import base64
import csv
import hmac
import json
import sys
from collections import defaultdict
from copy import copy
from datetime import datetime, timedelta
from pathlib import Path
from threading import Lock
from time import sleep, time
from typing import Any, Dict, List, Union
from urllib.parse import urlencode

from vnpy.api.rest import Request, RestClient
from vnpy.api.websocket import WebsocketClient
from vnpy.event import Event
from vnpy.trader.constant import (
    Direction,
    Exchange,
    Interval,
    Offset,
    OrderType,
    Product,
    Status,
)
from vnpy.trader.database import database_manager
from vnpy.trader.event import EVENT_TIMER
from vnpy.trader.gateway import BaseGateway
from vnpy.trader.object import (
    AccountData,
    BarData,
    CancelRequest,
    ContractData,
    HistoryRequest,
    OrderData,
    OrderRequest,
    PositionData,
    SubscribeRequest,
    TickData,
    TradeData,
)
from vnpy.trader.setting import bitget_account_main  # 导入账户字典
from vnpy.trader.utility import (
    TZ_INFO,
    GetFilePath,
    extract_vt_symbol,
    get_local_datetime,
    is_target_contract,
)

REST_HOST = "https://api.bitget.com"
WEBSOCKET_DATA_HOST = "wss://ws.bitget.com/v3/ws/public"  # UTA ws公共频道
WEBSOCKET_TRADE_HOST = "wss://ws.bitget.com/v3/ws/private"  # UTA ws私有频道

STATUS_BITGETONE2VT: Dict[str, Status] = {
    "new": Status.NOTTRADED,
    "live": Status.NOTTRADED,
    "partially_filled": Status.PARTTRADED,
    "cancelled": Status.CANCELLED,
    "filled": Status.ALLTRADED,
}

ORDERTYPE_VT2BITGETONE: Dict[OrderType, Any] = {
    OrderType.LIMIT: "limit",
    OrderType.MARKET: "market",
    OrderType.FAK: "limit",
    OrderType.FOK: "limit",
}
ORDERTYPE_BITGETONE2VT: Dict[Any, OrderType] = {"limit": OrderType.LIMIT, "market": OrderType.MARKET}
TIMEINFORCE_VT2BITGETONE: Dict[OrderType, str] = {
    OrderType.LIMIT: "gtc",
    OrderType.MARKET: "ioc",
    OrderType.FAK: "ioc",
    OrderType.FOK: "fok",
}

DIRECTION_VT2BITGETONE: Dict[Direction, str] = {
    Direction.LONG: "buy",
    Direction.SHORT: "sell",
}
DIRECTION_BITGETONE2VT: Dict[str, Direction] = {v: k for k, v in DIRECTION_VT2BITGETONE.items()}

HOLDSIDE_BITGETONE2VT: Dict[str, Direction] = {"long": Direction.LONG, "short": Direction.SHORT}
OPPOSITE_DIRECTION = {
    Direction.LONG: Direction.SHORT,
    Direction.SHORT: Direction.LONG,
}
CLOSE_OFFSETS = {Offset.CLOSE, Offset.CLOSETODAY, Offset.CLOSEYESTERDAY}

INTERVAL_VT2BITGETONE: Dict[Interval, str] = {
    Interval.MINUTE: "1m",
    Interval.HOUR: "1H",
    Interval.DAILY: "1D",
    Interval.WEEKLY: "1W",
}

MARGIN_SYMBOL_SUFFIX = "_MARGIN"
UTA_CATEGORIES: List[str] = ["MARGIN", "USDT-FUTURES", "USDC-FUTURES", "COIN-FUTURES"]
FUTURES_CATEGORIES = {"USDT-FUTURES", "USDC-FUTURES", "COIN-FUTURES"}
CATEGORY_EXCHANGE_MAP: Dict[str, Exchange] = {
    "SPOT": Exchange.BITGETSPOT,
    "MARGIN": Exchange.BITGETSPOT,
    "USDT-FUTURES": Exchange.BITGET,
    "USDC-FUTURES": Exchange.BITGET,
    "COIN-FUTURES": Exchange.BITGET,
}
CATEGORY_PRODUCT_MAP: Dict[str, Product] = {
    "SPOT": Product.SPOT,
    "MARGIN": Product.SPOT,
    "USDT-FUTURES": Product.FUTURES,
    "USDC-FUTURES": Product.FUTURES,
    "COIN-FUTURES": Product.FUTURES,
}
MIN_VOLUME_MAP = {

}
MARGIN_TYPE = "USDT_MARGIN"

TIMEDELTA_MAP: Dict[Interval, timedelta] = {
    Interval.MINUTE: timedelta(minutes=1),
    Interval.HOUR: timedelta(hours=1),
    Interval.DAILY: timedelta(days=1),
    Interval.WEEKLY: timedelta(weeks=1),
}
OPPOSITE_DIRECTION = {
    Direction.LONG: Direction.SHORT,
    Direction.SHORT: Direction.LONG,
}

def to_float(value: Any) -> float:
    """
    将Bitget返回的数字字符串转换为浮点数，兼容空字符串/None。
    """
    if value in (None, ""):
        return 0
    return float(value)


def to_int(value: Any) -> int:
    """
    将Bitget返回的整数字符串转换为整数，兼容空字符串/None。
    """
    if value in (None, ""):
        return 0
    return int(float(value))


def get_precision_tick(precision: Any) -> float:
    """
    根据精度位数生成最小变动单位。
    """
    if precision in (None, ""):
        return 0
    return float(f"1e-{int(precision)}")


def normalize_bitget_symbol(symbol: str) -> str:
    """
    将本地为避免MARGIN/USDT-FUTURES重名而添加的后缀还原成交易所symbol。
    """
    if symbol.endswith(MARGIN_SYMBOL_SUFFIX):
        return symbol[: -len(MARGIN_SYMBOL_SUFFIX)]
    return symbol


def make_bitget_symbol(symbol: str, category: str) -> str:
    """
    生成vn.py本地symbol。MARGIN与USDT永续存在BTCUSDT这类重名，使用本地后缀区分。
    """
    category = normalize_category(category)
    if category == "MARGIN" and not symbol.endswith(MARGIN_SYMBOL_SUFFIX):
        return f"{symbol}{MARGIN_SYMBOL_SUFFIX}"
    return symbol


def normalize_category(category: Any) -> str:
    """
    统一Bitget UTA产品类型大小写，兼容WebSocket中出现的小写写法。
    """
    if category in (None, ""):
        return ""
    return str(category).upper()


def infer_futures_category(symbol: str) -> str:
    """
    根据Bitget合约symbol推断期货产品类型，用于UTA持仓推送缺少category字段的兜底解析。
    """
    if symbol.endswith("PERP"):
        return "USDC-FUTURES"
    if symbol.endswith("USDT"):
        return "USDT-FUTURES"
    return "COIN-FUTURES"


def is_reduce_only(value: Any) -> bool:
    """
    解析Bitget reduceOnly字段，REST请求使用yes/no，部分回报使用YES/NO。
    """
    return str(value).lower() == "yes"

def get_bitget_orderid(data: dict) -> str:
    """
    优先使用本地clientOid，兼容外部委托没有clientOid的情况。
    """
    return data["clientOid"] or data["orderId"]


def parse_bitget_order_type(data: dict) -> OrderType:
    """
    根据Bitget UTA的orderType/timeInForce解析vn.py委托类型。
    """
    order_type = data["orderType"]
    time_in_force = data["timeInForce"]
    if order_type == "market":
        return OrderType.MARKET
    if time_in_force == "ioc":
        return OrderType.FAK
    if time_in_force == "fok":
        return OrderType.FOK
    return ORDERTYPE_BITGETONE2VT[order_type]


class BitGetOneGateway(BaseGateway):
    """
    * bitget统一账户接口
    * 现货，杠杆必须和合约分开交易
    * 单向持仓模式
    """
    # default_setting由vnpy.trader.ui.widget调用
    default_setting: Dict[str, Any] = {
        "key": "",
        "secret": "",
        "会话数": 3,
        "host": "",
        "port": "",
    }

    exchanges = [Exchange.BITGET,Exchange.BITGETSPOT]  # 由main_engine add_gateway调用
    get_file_path = GetFilePath()
    # ----------------------------------------------------------------------------------------------------
    def __init__(self, event_engine):
        """ """
        super(BitGetOneGateway, self).__init__(event_engine, "BITGETONE")
        self.orders: Dict[str, OrderData] = {}
        self.rest_api = BitGetOneRestApi(self)
        self.trade_ws_api = BitGetOneTradeWebsocketApi(self)
        self.market_ws_api = BitGetOneDataWebsocketApi(self)
        self.count = 0  # 轮询计时:秒
        # 所有合约列表
        self.recording_list = self.get_file_path.recording_list
        self.recording_list = [vt_symbol for vt_symbol in self.recording_list if is_target_contract(vt_symbol, self.gateway_name)]
        # 查询历史数据合约列表
        self.history_contracts = copy(self.recording_list)
        self.leverage_contracts = [vt_symbol for vt_symbol in self.get_file_path.all_trading_vt_symbols if is_target_contract(vt_symbol, self.gateway_name)]
        # 下载历史数据状态
        self.history_status: bool = True
        # 订阅逐笔成交数据状态
        self.book_trade_status: bool = False
        self.query_categories = copy(UTA_CATEGORIES)
    # ----------------------------------------------------------------------------------------------------
    def connect(self, log_account: dict = {}):
        """ """
        if not log_account:
            log_account = bitget_account_main
        key = log_account["key"]
        secret = log_account["secret"]
        passphrase = log_account["passphrase"]
        proxy_host = log_account["host"]
        proxy_port = log_account["port"]
        self.account_file_name = log_account["account_file_name"]
        self.rest_api.connect(key, secret, passphrase, proxy_host, proxy_port)
        self.trade_ws_api.connect(key, secret, passphrase, proxy_host, proxy_port)
        self.market_ws_api.connect(key, secret, passphrase, proxy_host, proxy_port)

        self.init_query()
    # ----------------------------------------------------------------------------------------------------
    def subscribe(self, req: SubscribeRequest) -> None:
        """
        订阅合约
        """
        self.market_ws_api.subscribe(req)
    # ----------------------------------------------------------------------------------------------------
    def send_order(self, req: OrderRequest) -> str:
        """
        发送委托单
        """
        #return self.rest_api.send_order(req)
        return self.trade_ws_api.send_order(req)
    # ----------------------------------------------------------------------------------------------------
    def cancel_order(self, req: CancelRequest) -> Request:
        """
        取消委托单
        """
        #self.rest_api.cancel_order(req)
        self.trade_ws_api.cancel_order(req)
    # ----------------------------------------------------------------------------------------------------
    def query_account(self) -> Request:
        """
        查询账户
        """
        self.rest_api.query_account()
    # ----------------------------------------------------------------------------------------------------
    def query_order(self, symbol: str):
        """
        查询活动委托单
        """
        self.rest_api.query_order(symbol)
    # ----------------------------------------------------------------------------------------------------
    def query_position(self, symbol: str):
        """
        查询持仓
        """
        self.rest_api.query_position(symbol)
    # ----------------------------------------------------------------------------------------------------
    def query_history(self, event: Event):
        """
        查询合约历史数据
        """
        if len(self.history_contracts) > 0:
            symbol, exchange, gateway_name = extract_vt_symbol(self.history_contracts.pop(0))
            req = HistoryRequest(
                symbol=symbol,
                exchange=exchange,
                interval=Interval.MINUTE,
                start=datetime.now(TZ_INFO) - timedelta(minutes=1440),
                end=datetime.now(TZ_INFO),
                gateway_name=self.gateway_name,
            )
            self.rest_api.query_history(req)
    # -------------------------------------------------------------------------------------------------------
    def on_order(self, order: OrderData) -> None:
        """
        收到委托单推送，BaseGateway推送数据
        """
        self.orders[order.vt_orderid] = copy(order)
        super().on_order(order)
    # -------------------------------------------------------------------------------------------------------
    def get_order(self, vt_orderid: str) -> OrderData:
        """
        用vt_orderid获取委托单数据
        """
        return self.orders.get(vt_orderid, None)
    # ----------------------------------------------------------------------------------------------------
    def close(self) -> None:
        """
        关闭接口
        """
        self.rest_api.stop()
        self.trade_ws_api.stop()
        self.market_ws_api.stop()
    # ----------------------------------------------------------------------------------------------------
    def process_timer_event(self, event: Event):
        """
        处理定时任务
        """
        self.count += 1
        if self.count < 3:
            return
        self.count = 0
        #self.query_account()
        if self.query_categories:
            category = self.query_categories.pop(0)
            self.rest_api.query_order(category)
            self.rest_api.query_position(category)
            self.query_categories.append(category)

        if self.leverage_contracts:
            vt_symbol = self.leverage_contracts.pop(0)
            self.rest_api.set_leverage(vt_symbol)
    # ----------------------------------------------------------------------------------------------------
    def init_query(self):
        """
        初始化定时查询
        """
        if self.history_status:
            self.event_engine.register(EVENT_TIMER, self.query_history)
        self.event_engine.register(EVENT_TIMER, self.process_timer_event)
# ----------------------------------------------------------------------------------------------------
class BitGetOneRestApi(RestClient):
    """
    BITGET REST API
    """

    def __init__(self, gateway: BitGetOneGateway):
        """ """
        super().__init__()

        self.gateway = gateway
        self.gateway_name: str = gateway.gateway_name

        self.host: str = ""
        self.key: str = ""
        self.secret: str = ""

        self.order_count: int = 0
        self.order_count_lock: Lock = Lock()
        self.count_datetime: int = 0

        self.account_date = None  # 账户日期
        self.accounts_info: Dict[str, dict] = {}
        self.product_types = UTA_CATEGORIES
        self.contract_inited: bool = False
        self.futures_symbol_category_map: Dict[str, str] = {}
    # ----------------------------------------------------------------------------------------------------
    def sign(self, request) -> Request:
        """
        生成签名
        """
        timestamp = str(int(time() * 1000))
        path = request.path
        method = request.method
        body = ""

        if method == "GET":
            if request.params:
                params = sorted(request.params.items())
                path += "?" + urlencode(params)
            # path需签名
            #if "/instruments" not in path and "/candles" not in path:
                #request.path = path
                
        elif method == "POST":
            if request.data:
                body = json.dumps(request.data, separators=(",", ":"))
                request.data = body

        message = f"{timestamp}{method}{path}{body}"
        signature = create_signature(self.secret, message)

        if not request.headers:
            request.headers = {}
            request.headers["ACCESS-KEY"] = self.key
            request.headers["ACCESS-SIGN"] = signature
            request.headers["ACCESS-TIMESTAMP"] = timestamp
            request.headers["ACCESS-PASSPHRASE"] = self.passphrase
            request.headers["Content-Type"] = "application/json"
            request.headers["locale"] = "zh-CN"
        return request
    # ----------------------------------------------------------------------------------------------------
    def connect(self, key: str, secret: str, passphrase: str, proxy_host: str, proxy_port: int) -> None:
        """
        连接REST服务
        """
        self.key = key
        self.secret = secret
        self.passphrase = passphrase

        self.init(REST_HOST, proxy_host, proxy_port, gateway_name=self.gateway_name)
        self.start()

        self.gateway.write_log(f"交易接口：{self.gateway_name}，REST API启动成功")

        self.query_contract()
        self.set_hold_mode()
    # ----------------------------------------------------------------------------------------------------
    def get_category(self, vt_symbol: str) -> str:
        """
        通过vt_symbol获取UTA产品类型。
        """
        symbol, exchange, gateway_name = extract_vt_symbol(vt_symbol)

        if exchange == Exchange.BITGETSPOT:
            if symbol.endswith(MARGIN_SYMBOL_SUFFIX):
                return "MARGIN"
            return "SPOT"
        
        if symbol.endswith("PERP"):
            return "USDC-FUTURES"
        if symbol.endswith("USDT"):
            return "USDT-FUTURES"
        return "COIN-FUTURES"
    # ----------------------------------------------------------------------------------------------------
    def get_symbol_category(self, symbol: str, exchange: Exchange) -> tuple[str,str]:
        """
        根据symbol/exchange返回交易所symbol和UTA产品类型。
        """
        vt_symbol = f"{symbol}_{exchange.value}/{self.gateway_name}"
        return normalize_bitget_symbol(symbol), self.get_category(vt_symbol)
    # ----------------------------------------------------------------------------------------------------
    def get_position_category(self, symbol: str) -> str:
        """
        解析UTA私有持仓推送的合约产品类型。

        Bitget持仓推送的arg.instType固定为UTA，data里没有category，无法直接区分产品线。
        这里优先使用REST合约查询建立的symbol->category缓存，缓存缺失时再按期货命名规则兜底。
        """
        return self.futures_symbol_category_map.get(symbol) or infer_futures_category(symbol)
    # ----------------------------------------------------------------------------------------------------
    def set_leverage(self, vt_symbol: str):
        """
        设置杠杆，现货不支持。
        """
        symbol, exchange, gateway_name = extract_vt_symbol(vt_symbol)
        raw_symbol, category = self.get_symbol_category(symbol, exchange)
        if category == "SPOT":
            return
        data = {
            "category": category,
            "symbol": raw_symbol,
            "leverage": "10",
        }
        if category == "MARGIN":
            data["coin"] = symbol.split("USD")[0]
        self.add_request(method="POST", path="/api/v3/account/set-leverage", callback=self.on_leverage, data=data, extra=vt_symbol)
    # ----------------------------------------------------------------------------------------------------
    def on_leverage(self, data: dict, request: Request):
        self.check_error(data, "设置杠杆")
    # ----------------------------------------------------------------------------------------------------
    def set_hold_mode(self):
        """
        设置单向持仓模式
        """
        data = {"holdMode": "one_way_mode"}
        self.add_request(method="POST", path="/api/v3/account/set-hold-mode", callback=self.on_hold_mode, data=data)
    # ----------------------------------------------------------------------------------------------------
    def on_hold_mode(self,data: dict, request: Request):
        self.check_error(data, "设置持仓模式")
    # ----------------------------------------------------------------------------------------------------
    def query_account(self) -> Request:
        """
        查询账户数据
        """
        self.add_request(method="GET", path="/api/v3/account/assets", callback=self.on_query_account)
    # ----------------------------------------------------------------------------------------------------
    def query_order(self, category: str, cursor: str = ""):
        """
        查询活动委托单
        """
        params = {"category": category, "limit": "100"}
        if cursor:
            params["cursor"] = cursor
        self.add_request(method="GET", path="/api/v3/trade/unfilled-orders", callback=self.on_query_order, params=params)
    # ----------------------------------------------------------------------------------------------------
    def query_position(self, category: str):
        """
        查询持仓数据，只支持期货合约
        """
        if category not in FUTURES_CATEGORIES:
            return
        params = {"category": category}
        self.add_request(method="GET", path="/api/v3/position/current-position", callback=self.on_query_position, params=params)
    # ----------------------------------------------------------------------------------------------------
    def query_repayable(self):
        """
        获取杠杆可还款币种
        """
        self.add_request(method="GET", path="/api/v3/account/repayable-coins", callback=self.on_query_repayable,)
    # ----------------------------------------------------------------------------------------------------
    def on_query_repayable(self, data: dict, request: Request) -> None:
        payment_coinlist = []
        for raw in data["data"]["repayableCoinList"]:
            symbol = raw["coin"]
            symbol =f"{symbol}{MARGIN_TYPE}"
            if symbol not in MIN_VOLUME_MAP:
                continue
            min_volume = MIN_VOLUME_MAP[symbol]
            volume = to_float(raw["size"])

            # 当杠杆借款数量小于杠杆现货最小委托量时自动还款
            if volume < min_volume:
                payment_coinlist.append(raw["coin"])
        if payment_coinlist:
            self.auto_repay(payment_coinlist)
    # ----------------------------------------------------------------------------------------------------
    def auto_repay(self,coinlist:list):
        """
        还款
        """
        # repayableCoinList要还款的币种，paymentCoinList支付的币种
        payment_coin = MARGIN_TYPE.split("_")[0]
        data = {"repayableCoinList": coinlist, "paymentCoinList": [payment_coin]}
        self.add_request(method="POST", path="/api/v3/account/repay",data = data, callback=self.on_auto_repay,)
    # ----------------------------------------------------------------------------------------------------
    def on_auto_repay(self, data: dict, request: Request) -> None:
        """
        收到还款回报
        """
        result = data["data"]["result"]
        if result != "YES":
            self.gateway.write_log(f"交易接口：{self.gateway_name}，杠杆现货自动还款失败")
    # ----------------------------------------------------------------------------------------------------
    def query_contract(self) -> Request:
        """
        获取合约信息
        """
        for product in self.product_types:
            params = {"category": product}
            self.add_request(
                method="GET",
                path="/api/v3/market/instruments",
                params=params,
                callback=self.on_query_contract,
            )
    # ----------------------------------------------------------------------------------------------------
    def query_history(self, req: HistoryRequest) -> List[BarData]:
        """
        查询历史数据
        """
        history = []
        count = 1000
        start = req.start
        time_delta = TIMEDELTA_MAP[req.interval]
        time_consuming_start = time()
        symbol = normalize_bitget_symbol(req.symbol)
        category = self.get_category(req.vt_symbol)
        while True:
            end = start + time_delta * count
            if req.end:
                end = min(end, req.end)

            # 构建查询参数
            params = {
                "category": category,
                "symbol": symbol,
                "interval": INTERVAL_VT2BITGETONE[req.interval],
                "type": "MARKET",
                "startTime": str(int(start.timestamp() * 1000)),
                "endTime": str(int(end.timestamp() * 1000)),
                "limit": str(count),
            }
            resp = self.request("GET", "/api/v3/market/candles", params=params)
            if not resp or resp.status_code // 100 != 2:
                msg = f"获取历史数据失败，状态码：{getattr(resp, 'status_code', '未知')}, 信息：{getattr(resp, 'text', '')}"
                self.gateway.write_log(msg)
                break

            json_data = resp.json()
            if self.check_error(json_data, "查询历史数据"):
                break
            rawdata = json_data.get("data") or []
            buf = [BarData(
                symbol=req.symbol,
                exchange=req.exchange,
                datetime=get_local_datetime(int(data[0])),
                interval=req.interval,
                volume=float(data[5]),
                open_price=float(data[1]),
                high_price=float(data[2]),
                low_price=float(data[3]),
                close_price=float(data[4]),
                gateway_name=self.gateway_name,
            ) for data in rawdata]

            history.extend(buf)
            if buf:
                start = buf[-1].datetime + time_delta

            # 结束条件检查
            if len(buf) < count or start >= req.end:
                break

        if history:
            try:
                database_manager.save_bar_data(history, False)
            except Exception as err:
                self.gateway.write_log(f"保存数据库出错：{err}")
            time_consuming_end = time()
            query_time = round(time_consuming_end - time_consuming_start, 3)
            msg = f"载入{req.vt_symbol}:bar数据，开始时间：{history[0].datetime}，结束时间：{history[-1].datetime}，数据量：{len(history)}，耗时:{query_time}秒"
            self.gateway.write_log(msg)
        else:
            msg = f"未查询到合约：{req.vt_symbol}历史数据，请核实行情连接"
            self.gateway.write_log(msg)
    # ----------------------------------------------------------------------------------------------------
    def new_order_id(self) -> int:
        """
        生成本地委托号
        """
        with self.order_count_lock:
            self.order_count += 1
            return self.order_count
    # ----------------------------------------------------------------------------------------------------
    def send_order(self, req: OrderRequest) -> str:
        """
        发送委托单
        """
        self.count_datetime = int(datetime.now(TZ_INFO).strftime("%Y%m%d%H%M%S"))

        orderid: str = req.symbol + "-" + str(self.count_datetime) + str(self.new_order_id()).rjust(8,"0")
        order = req.create_order_data(orderid, self.gateway_name)
        order.datetime = datetime.now(TZ_INFO)
        req_symbol, category = self.get_symbol_category(req.symbol, req.exchange)
        order_type = ORDERTYPE_VT2BITGETONE[req.type]
        data = {
            "category": category,
            "symbol": req_symbol,
            "clientOid": orderid,
            "qty": str(req.volume),
            "side": DIRECTION_VT2BITGETONE.get(req.direction),
            "orderType": order_type,
            "timeInForce": TIMEINFORCE_VT2BITGETONE[req.type],
        }
        if order_type == "limit":
            data["price"] = str(req.price)
        if category in FUTURES_CATEGORIES:
            # UTA单向持仓模式下平仓由reduceOnly控制。
            data["reduceOnly"] = "yes" if req.offset in CLOSE_OFFSETS else "no"
        else:
            data["reduceOnly"] = "no"

        self.add_request(
            method="POST",
            path="/api/v3/trade/place-order",
            callback=self.on_send_order,
            data=data,
            extra=order,
            on_error=self.on_send_order_error,
            on_failed=self.on_send_order_failed,
        )

        self.gateway.on_order(order)
        return order.vt_orderid
    # ----------------------------------------------------------------------------------------------------
    def cancel_order(self, req: CancelRequest) -> Request:
        """
        取消委托单
        """
        order = self.gateway.get_order(req.vt_orderid)
        orderid = req.orderid
        raw_symbol, category = self.get_symbol_category(req.symbol, req.exchange)
        data = {"category": category}
        if str(orderid).startswith(f"{req.symbol}-"):
            data["clientOid"] = orderid
        else:
            data["orderId"] = orderid
        self.add_request(
            method="POST", path="/api/v3/trade/cancel-order", callback=self.on_cancel_order, on_failed=self.on_cancel_order_failed, data=data, extra=order
        )
    # ----------------------------------------------------------------------------------------------------
    def on_query_account(self, data: dict, request: Request) -> None:
        """
        收到账户数据回报
        """
        if self.check_error(data, "查询账户"):
            return
        account_result = data["data"]
        for account_data in account_result["assets"]:
            coin = account_data["coin"]
            account = AccountData(
                accountid=coin + "_" + self.gateway_name,
                balance=to_float(account_data["balance"]),
                available=to_float(account_data["available"]),
                position_profit=to_float(account_result["unrealisedPnl"]),
                frozen=to_float(account_data["locked"]),
                datetime=datetime.now(TZ_INFO),
                file_name=self.gateway.account_file_name,
                gateway_name=self.gateway_name,
            )
            if account.balance:
                self.gateway.on_account(account)
                # 保存账户资金信息
                self.accounts_info[account.accountid] = account.__dict__
        if not self.accounts_info:
            return
        accounts_info = list(self.accounts_info.values())
        account_date = accounts_info[-1]["datetime"].date()
        account_path = self.gateway.get_file_path.account_path(self.gateway.account_file_name)
        write_header = not Path(account_path).exists()
        additional_writing = self.account_date and self.account_date != account_date
        self.account_date = account_date
        # 文件不存在则写入文件头，否则只在日期变更后追加写入文件
        if not write_header and not additional_writing:
            return
        write_mode = "w" if write_header else "a"
        for account_data in accounts_info:
            with open(account_path, write_mode, newline="") as f1:
                w1 = csv.DictWriter(f1, list(account_data))
                if write_header:
                    w1.writeheader()
                w1.writerow(account_data)
    # ----------------------------------------------------------------------------------------------------
    def on_query_order(self, data: dict, request: Request) -> None:
        """
        收到委托回报
        """
        if self.check_error(data, "查询活动委托"):
            return
        result = data["data"]
        order_list = result["list"]
        if not order_list:
            return
        order_ids = set()
        for order_data in order_list:
            order_ids.add(int(order_data["orderId"]))
            category = normalize_category(order_data["category"])
            exchange = CATEGORY_EXCHANGE_MAP[category]
            symbol = make_bitget_symbol(order_data["symbol"], category)
            order = OrderData(
                orderid=get_bitget_orderid(order_data),
                symbol=symbol,
                exchange=exchange,
                price=to_float(order_data["price"]),
                volume=to_float(order_data["qty"]),
                type=parse_bitget_order_type(order_data),
                direction=DIRECTION_BITGETONE2VT[order_data["side"]],
                traded=to_float(order_data["cumExecQty"]),
                status=STATUS_BITGETONE2VT[order_data["orderStatus"]],
                datetime=get_local_datetime(to_int(order_data["createdTime"])),
                gateway_name=self.gateway_name,
            )
            if is_reduce_only(order_data.get("reduceOnly")):
                order.offset = Offset.CLOSE

            self.gateway.on_order(order)

        if len(order_list) == 100:
            # 查询到达上限后使用本次响应的分页游标继续查询。
            # Bitget要求第二页及后续请求传入上一次响应的最小orderId，
            current_cursor = request.params.get("cursor","")
            next_cursor = str(min(order_ids))
            if next_cursor != current_cursor:
                category = request.params["category"]
                self.query_order(category, next_cursor)
    # ----------------------------------------------------------------------------------------------------
    def on_query_position(self, data: dict, request: Request) -> None:
        """
        收到持仓回报。
        """
        if self.check_error(data, "查询持仓"):
            return
        result = data.get("data") or {}
        position_list = result["list"] if result["list"] else []
        for pos_data in position_list:
            category = normalize_category(pos_data["category"])
            exchange = CATEGORY_EXCHANGE_MAP[category]
            volume = to_float(pos_data["total"])
            direction = HOLDSIDE_BITGETONE2VT[pos_data["posSide"]]
            position = PositionData(
                symbol=make_bitget_symbol(pos_data["symbol"], category),
                exchange=exchange,
                direction=direction,
                volume=abs(volume),
                frozen=to_float(pos_data["frozen"]),
                price=to_float(pos_data["avgPrice"]),
                pnl=to_float(pos_data["unrealisedPnl"]),
                gateway_name=self.gateway_name,
            )
            self.gateway.on_position(position)
    # ----------------------------------------------------------------------------------------------------
    def on_query_contract(self, data: dict, request: Request) -> None:
        """
        收到合约参数回报
        """
        if self.check_error(data, "查询合约"):
            return
        for contract_data in data["data"]:
            if contract_data["status"] != "online":
                continue
            category = contract_data["category"]
            raw_symbol = contract_data["symbol"]
            if category in FUTURES_CATEGORIES:
                self.futures_symbol_category_map[raw_symbol] = category
            symbol = make_bitget_symbol(raw_symbol, category)
            exchange = CATEGORY_EXCHANGE_MAP[category]
            product = CATEGORY_PRODUCT_MAP[category]
            price_tick = to_float(contract_data.get("priceMultiplier"))
            if not price_tick:
                price_tick = get_precision_tick(contract_data.get("pricePrecision"))
            size = 1 if product == Product.SPOT else to_float(contract_data.get("maxLeverage"))
            min_volume = to_float(contract_data["minOrderQty"])
            contract = ContractData(
                symbol=symbol,
                exchange=exchange,
                name=raw_symbol,
                price_tick=price_tick,
                size=size,
                min_volume=min_volume,
                max_volume=to_float(contract_data["maxOrderQty"]),
                product=product,
                gateway_name=self.gateway_name,
            )
            delivery_time = contract_data.get("deliveryTime")
            if delivery_time:
                delivery_datetime = get_local_datetime(to_int(delivery_time))
                # 过滤过期交割合约推送
                if delivery_datetime <= datetime.now(TZ_INFO):
                    continue
                if product == Product.FUTURES:
                    contract.name = contract_data.get("baseCoin", "") + contract_data.get("quoteCoin", "") + "_" + datetime.strftime(delivery_datetime, "%Y%m%d")
            MIN_VOLUME_MAP[symbol] = min_volume
            self.gateway.on_contract(contract)
        self.gateway.write_log(f"交易接口：{self.gateway_name}，{category}合约信息查询成功")
        self.contract_inited = True
    # ----------------------------------------------------------------------------------------------------
    def on_send_order(self, data: dict, request: Request) -> None:
        """ """
        order = request.extra
        if self.check_error(data, "委托"):
            order.status = Status.REJECTED
            self.gateway.on_order(order)
    # ----------------------------------------------------------------------------------------------------
    def on_send_order_failed(self, status_code, request: Request) -> None:
        """
        收到委托失败回报
        """
        order = request.extra
        order.status = Status.REJECTED
        self.gateway.on_order(order)

        msg = f"委托失败，状态码：{status_code}，信息：{request.response.text}"
        self.gateway.write_log(msg)
    # ----------------------------------------------------------------------------------------------------
    def on_send_order_error(self, exception_type: type, exception_value: Exception, tb, request: Request):
        """
        Callback when sending order caused exception.
        """
        order = request.extra
        order.status = Status.REJECTED
        self.gateway.on_order(order)

        # Record exception if not ConnectionError
        if not issubclass(exception_type, ConnectionError):
            self.on_error(exception_type, exception_value, tb, request)
    # ----------------------------------------------------------------------------------------------------
    def on_cancel_order(self, data: dict, request: Request) -> None:
        """
        """
        if self.check_error(data, "撤单"):
            order = request.extra
            order.status = Status.REJECTED
            self.gateway.on_order(order)
    # ----------------------------------------------------------------------------------------------------
    def on_cancel_order_failed(self, status_code, request: Request) -> None:
        """
        收到撤单失败回报
        """
        if request.extra:
            order = request.extra
            order.status = Status.REJECTED
            self.gateway.on_order(order)
        msg = f"撤单失败，状态码：{status_code}，信息：{request.response.text}"
        self.gateway.write_log(msg)
    # ----------------------------------------------------------------------------------------------------
    def on_error(self, exception_type: type, exception_value: Exception, tb, request: Request) -> None:
        """
        Callback to handler request exception.
        """
        msg = f"触发异常，状态码：{exception_type}，信息：{exception_value}"
        self.gateway.write_log(msg)

        sys.stderr.write(self.exception_detail(exception_type, exception_value, tb, request))
    # ----------------------------------------------------------------------------------------------------
    def check_error(self, data: dict, func: str = "") -> bool:
        """ """
        if data.get("msg") == "success":
            return False

        error_code = data.get("code")
        error_msg = data.get("msg")
        self.gateway.write_log(f"{func}请求出错，代码：{error_code}，信息：{error_msg}")
        return True
# ----------------------------------------------------------------------------------------------------
class BitGetOneWebsocketApiBase(WebsocketClient):
    """ """

    def __init__(self, gateway):
        """ """
        super(BitGetOneWebsocketApiBase, self).__init__()

        self.gateway: BitGetOneGateway = gateway
        self.gateway_name: str = gateway.gateway_name

        self.key: str = ""
        self.secret: str = ""
        self.passphrase: str = ""
        self.count = 0
    # ----------------------------------------------------------------------------------------------------
    def connect(self, key: str, secret: str, passphrase: str, url: str, proxy_host: str, proxy_port: int) -> None:
        """ """
        self.key = key
        self.secret = secret
        self.passphrase = passphrase

        self.init(url, proxy_host, proxy_port, gateway_name=self.gateway_name)
        self.start()
        self.gateway.event_engine.register(EVENT_TIMER, self.send_ping)
    # ----------------------------------------------------------------------------------------------------
    def send_ping(self, event):
        self.count += 1
        if self.count < 20:
            return
        self.count = 0
        self.send_packet("ping")
    # ----------------------------------------------------------------------------------------------------
    def login(self) -> int:
        """ """
        timestamp = str(int(time()))
        message = timestamp + "GET" + "/user/verify"
        signature = create_signature(self.secret, message)
        params = {"op": "login", "args": [{"apiKey": self.key, "passphrase": self.passphrase, "timestamp": timestamp, "sign": signature}]}
        return self.send_packet(params)
    # ----------------------------------------------------------------------------------------------------
    def on_login(self) -> None:
        """ """
        pass
    # ----------------------------------------------------------------------------------------------------
    def on_data(self, packet):
        pass
    # ----------------------------------------------------------------------------------------------------
    def on_packet(self, packet: Union[str, dict]) -> None:
        """ """
        if packet == "pong":
            return
        if "event" in packet:
            if packet["event"] == "login" and str(packet.get("code")) == "0":
                self.on_login()
            elif packet["event"] == "error":
                self.on_error_msg(packet)
        else:
            self.on_data(packet)
    # ----------------------------------------------------------------------------------------------------
    def on_error_msg(self, packet) -> None:
        """ """
        code = packet["code"]
        msg = packet["msg"]
        orderid = packet.get("id")
        if orderid:
            order = self.gateway.get_order(f"{self.gateway_name}_{orderid}")
            if order:
                order.status = Status.REJECTED
                self.gateway.on_order(order)
        self.gateway.write_log(f"交易接口：{self.gateway_name} WebSocket API收到错误回报，状态码：{code}，回报信息：{msg}")
# ----------------------------------------------------------------------------------------------------
class BitGetOneDataWebsocketApi(BitGetOneWebsocketApiBase):
    """ """

    def __init__(self, gateway: BitGetOneGateway):
        """ """
        super().__init__(gateway)
        self.ticks: Dict[str, TickData] = {}
        self.topic_map = {
            "ticker":self.on_tick,
            "books":self.on_depth,
            "trade": self.on_public_trade,
            "publicTrade": self.on_public_trade,
        }
        self.order_book_bids = defaultdict(dict)  # 订单簿买单字典
        self.order_book_asks = defaultdict(dict)  # 订单簿卖单字典
        self.books_seq:Dict[str,int] = defaultdict(int)  # books seq
    # ----------------------------------------------------------------------------------------------------
    def connect(self, key: str, secret: str, passphrase: str, proxy_host: str, proxy_port: int) -> None:
        """ """
        super().connect(key, secret, passphrase, WEBSOCKET_DATA_HOST, proxy_host, proxy_port)
    # ----------------------------------------------------------------------------------------------------
    def on_connected(self) -> None:
        """ """
        self.gateway.write_log(f"交易接口：{self.gateway_name}，行情Websocket API连接成功")

        for symbol in list(self.ticks):
            self.subscribe_data(symbol)
    # ----------------------------------------------------------------------------------------------------
    def on_disconnected(self):
        """
        ws行情断开回调
        """
        self.gateway.write_log(f"交易接口：{self.gateway_name}，行情Websocket API连接断开")
    # ----------------------------------------------------------------------------------------------------
    def subscribe(self, req: SubscribeRequest) -> None:
        """
        订阅合约
        """
        # 等待rest合约数据推送完成再订阅
        while not self.gateway.rest_api.contract_inited and self._active:
            sleep(1)

        tick = TickData(
            symbol=req.symbol,
            name=req.symbol,
            exchange=req.exchange,
            datetime=datetime.now(TZ_INFO),
            gateway_name=self.gateway_name,
        )
        symbol = tick.symbol
        self.ticks[symbol] = tick
        self.subscribe_data(symbol)
    # ----------------------------------------------------------------------------------------------------
    def topic_subscribe(self, symbol:str,channel: str, product_type: str):
        """
        主题订阅
        """
        req = {"op": "subscribe", "args": [{"instType": product_type, "topic": channel, "symbol": symbol}]}
        self.send_packet(req)
    # ----------------------------------------------------------------------------------------------------
    def subscribe_data(self, symbol: str) -> None:
        """
        订阅市场深度主题
        """
        # 订阅tick，行情深度
        channels = ["ticker", "books"]     # books推送间隔50ms
        if self.gateway.book_trade_status:
            # 订阅逐笔成交
            channels.append("trade")
        vt_symbol = self.ticks[symbol].vt_symbol
        raw_symbol = normalize_bitget_symbol(symbol)

        # ws接口的category小写
        product_type = self.gateway.rest_api.get_category(vt_symbol).lower()
        # ws没有margin类型
        if product_type == "margin":
            product_type = "spot"
        for channel in channels:
            if channel == "trade":
                # UTA逐笔成交频道文档使用topic=publicTrade/symbol格式，普通v3频道使用channel/instId格式。
                req = {"op": "subscribe", "args": [{"instType": product_type, "topic": "publicTrade", "symbol": raw_symbol}]}
                self.send_packet(req)
            else:
                self.topic_subscribe(raw_symbol, channel, product_type)
    # ----------------------------------------------------------------------------------------------------
    def on_data(self, packet) -> None:
        """ """
        arg = packet["arg"]
        channel = arg["topic"]  # UTA publicTrade使用topic字段
        handler = self.topic_map.get(channel)
        if handler:
            handler(packet)
    # ----------------------------------------------------------------------------------------------------
    def on_tick(self, packet: dict) -> None:
        """
        收到tick数据推送
        """
        data = packet["data"]
        arg = packet["arg"]
        category = arg["instType"]
        # 现货只交易杠杆
        if category == "spot":
            category = "margin"

        symbol = arg["symbol"]
        for tick_data in data:
            symbol = make_bitget_symbol(symbol, category)
            tick = self.ticks[symbol]
            tick.datetime = get_local_datetime(to_int(packet["ts"]))
            tick.pre_close = tick.open_price = to_float(tick_data["openPrice24h"])
            tick.high_price = to_float(tick_data["highPrice24h"])
            tick.low_price = to_float(tick_data["lowPrice24h"])
            tick.last_price = to_float(tick_data["lastPrice"])
            tick.open_interest = to_float(tick_data.get("openInterest",0))
            tick.volume = to_float(tick_data["volume24h"])
            tick.bid_price_1 = to_float(tick_data["bid1Price"])
            tick.bid_volume_1 = to_float(tick_data["bid1Size"])
            tick.ask_price_1 = to_float(tick_data["ask1Price"])
            tick.ask_volume_1 = to_float(tick_data["ask1Size"])
            self.gateway.on_tick(copy(tick))
    # ----------------------------------------------------------------------------------------------------
    def on_depth(self, packet: dict) -> None:
        """
        行情深度推送
        """
        arg = packet["arg"]
        category = arg["instType"]
        action = packet["action"]
        # 现货只交易杠杆
        if category == "spot":
            category = "margin"
        symbol = make_bitget_symbol(arg["symbol"], category)

        order_books = packet["data"][0]
        last_seq = order_books["seq"]
        # 过滤乱序books推送
        if last_seq < self.books_seq[symbol]:
            return
        self.books_seq[symbol] = last_seq

        tick = self.ticks[symbol]
        tick.datetime = get_local_datetime(to_int(order_books["ts"]))
        
        bids = order_books["b"]
        asks = order_books["a"]

        # 定义更新order book的函数
        def update_order_book(order_book_dict, order_book_data, prefix):
            order_book_dict.clear() if action == "snapshot" else None
            for price, volume in order_book_data:
                if float(volume) > 0:
                    order_book_dict[price] = volume
                else:
                    order_book_dict.pop(price, None)
            # 排序并更新TickData
            sorted_data = sorted(order_book_dict.items(), key=lambda x: float(x[0]), reverse=(prefix == "bid"))[:5]
            for index, (price, volume) in enumerate(sorted_data,start=1):
                setattr(tick, f"{prefix}_price_{index}", float(price))
                setattr(tick, f"{prefix}_volume_{index}", float(volume))

        # 更新买单和卖单数据
        update_order_book(self.order_book_bids[tick.vt_symbol], bids, "bid")
        update_order_book(self.order_book_asks[tick.vt_symbol], asks, "ask")

        self.gateway.on_tick(copy(tick))
    # ----------------------------------------------------------------------------------------------------
    def on_public_trade(self, packet):
        """
        收到逐笔成交回报
        """
        data = packet["data"][0]
        arg = packet["arg"]
        category = arg["instType"]
        symbol = make_bitget_symbol(arg.get("instId") or arg.get("symbol") or data.get("instId") or data.get("symbol"), category)
        if symbol not in self.ticks:
            return
        tick = self.ticks[symbol]
        tick.last_price = to_float(data.get("price") or data.get("p"))
        tick.last_volume = to_float(data.get("size") or data.get("qty") or data.get("v"))
        tick.datetime = get_local_datetime(to_int(data.get("ts") or data.get("T") or packet.get("ts")))
        self.gateway.on_tick(copy(tick))
# ----------------------------------------------------------------------------------------------------
class BitGetOneTradeWebsocketApi(BitGetOneWebsocketApiBase):
    """ """

    def __init__(self, gateway: BitGetOneGateway):
        """ """
        super().__init__(gateway)
        self.topic_map = {
            "account":self.on_account,
            "order":self.on_order,
            "position":self.on_position,
            "fill":self.on_trade,
        }
        self.account_date = None  # 账户日期
        self.accounts_info: Dict[str, dict] = {}
    # ----------------------------------------------------------------------------------------------------
    def connect(self, key: str, secret: str, passphrase: str, proxy_host: str, proxy_port: int) -> None:
        """ """
        super().connect(key, secret, passphrase, WEBSOCKET_TRADE_HOST, proxy_host, proxy_port)
    # ----------------------------------------------------------------------------------------------------
    def subscribe_private(self) -> int:
        """
        订阅私有频道
        """
        # 统一账户级别推送
        self.send_packet({"op": "subscribe", "args": [{"instType": "UTA", "topic": "account"}]})
        self.send_packet({"op": "subscribe", "args": [{"instType": "UTA", "topic": "order"}]})
        self.send_packet({"op": "subscribe", "args": [{"instType": "UTA", "topic": "position"}]})
        self.send_packet({"op": "subscribe", "args": [{"instType": "UTA", "topic": "fill"}]})
    # ----------------------------------------------------------------------------------------------------
    def on_connected(self) -> None:
        """ """
        self.gateway.write_log(f"交易接口：{self.gateway_name}，交易Websocket API连接成功")
        self.login()
    # ----------------------------------------------------------------------------------------------------
    def on_disconnected(self):
        """
        ws交易断开回调
        """
        self.gateway.write_log(f"交易接口：{self.gateway_name}，交易Websocket API连接断开")
    # ----------------------------------------------------------------------------------------------------
    def on_login(self) -> None:
        """ """
        self.gateway.write_log(f"交易接口：{self.gateway_name}，交易Websocket API登录成功")
        # 等待rest合约数据推送完成再订阅
        while not self.gateway.rest_api.contract_inited and self._active:
            sleep(1)
        self.subscribe_private()
    # ----------------------------------------------------------------------------------------------------
    def send_order(self,req:OrderRequest) -> str:
        """
        ws发送委托单
        """
        rest_api = self.gateway.rest_api
        count_datetime = int(datetime.now(TZ_INFO).strftime("%Y%m%d%H%M%S"))

        orderid: str = req.symbol + "-" + str(count_datetime) + str(rest_api.new_order_id()).rjust(8,"0")
        order = req.create_order_data(orderid, self.gateway_name)
        order.datetime = datetime.now(TZ_INFO)
        req_symbol, category = rest_api.get_symbol_category(req.symbol, req.exchange)
        order_type = ORDERTYPE_VT2BITGETONE[req.type]
        req_data = {
                    "symbol":req_symbol,
                    "orderType":order_type,
                    "clientOid": orderid,
                    "qty":str(req.volume),
                    "side":DIRECTION_VT2BITGETONE.get(req.direction),
                    "timeInForce":TIMEINFORCE_VT2BITGETONE[req.type],
                }
        if order_type == "limit":
            req_data["price"] = str(req.price)
        if (category in FUTURES_CATEGORIES and req.offset in CLOSE_OFFSETS):
            # UTA单向持仓模式下平仓由reduceOnly控制。
            req_data["reduceOnly"] = "YES"
        else:
            req_data["reduceOnly"] = "NO"
        data = {
            "op":"trade",
            "id":orderid,
            "topic":"place-order",
            "category":category.lower(),
            "args":[req_data],
        }
        self.gateway.on_order(order)
        self.send_packet(data)
    # ----------------------------------------------------------------------------------------------------
    def cancel_order(self,req:CancelRequest) -> str:
        """
        ws撤单
        """
        req_data = {}
        orderid = req.orderid
        if str(orderid).startswith(f"{req.symbol}-"):
            req_data["clientOid"] = orderid
        else:
            req_data["orderId"] = orderid
        data = {
            "args": [req_data],
            "id": orderid,
            "op": "trade",
            "topic": "cancel-order"
        }
        self.send_packet(data)
    # ----------------------------------------------------------------------------------------------------
    def on_data(self, packet) -> None:
        """ """
        arg = packet["arg"]
        channel = arg["topic"]
        data = packet["data"]
        self.topic_map[channel](data)
    # ----------------------------------------------------------------------------------------------------
    def on_account(self,data):
        """
        收到账户资金回报
        处理杠杆现货持仓推送
        """
        raw = data[0]["coin"]
        unrealised_pnl = data[0]["unrealisedPnL"]
        for account_data in raw:
            coin = account_data["coin"]
            account = AccountData(
                accountid=coin + "_" + self.gateway_name,
                balance=to_float(account_data["balance"]),
                available=to_float(account_data["available"]),
                position_profit=to_float(unrealised_pnl),
                frozen=to_float(account_data["locked"]),
                datetime=datetime.now(TZ_INFO),
                file_name=self.gateway.account_file_name,
                gateway_name=self.gateway_name,
            )
            if account.balance:
                self.gateway.on_account(account)
                # 保存账户资金信息
                self.accounts_info[account.accountid] = account.__dict__
            if coin not in ["USDT","USDC"]:
                volume = to_float(account_data["equity"])
                if volume >=0:
                    direction = Direction.LONG
                else:
                    direction = Direction.SHORT
                # 杠杆现货持仓推送
                position_1 = PositionData(
                    symbol=f"{coin}{MARGIN_TYPE}",
                    exchange=Exchange.BITGETSPOT,
                    direction=direction,
                    volume=abs(volume),
                    frozen=to_float(account_data["locked"]),
                    gateway_name=self.gateway_name,
                )
                position_2 = PositionData(
                    symbol = position_1.symbol,
                    exchange=position_1.exchange,
                    direction=OPPOSITE_DIRECTION[position_1.direction],
                    volume=0,
                    price=0,
                    frozen=0,
                    gateway_name=self.gateway_name
                )
                self.gateway.on_position(position_1)
                self.gateway.on_position(position_2)
                # 持仓变动后立即查询可杠杆现货可还款币种
                self.gateway.rest_api.query_repayable()

        if not self.accounts_info:
            return
        accounts_info = list(self.accounts_info.values())
        account_date = accounts_info[-1]["datetime"].date()
        account_path = self.gateway.get_file_path.account_path(self.gateway.account_file_name)
        write_header = not Path(account_path).exists()
        additional_writing = self.account_date and self.account_date != account_date
        self.account_date = account_date
        # 文件不存在则写入文件头，否则只在日期变更后追加写入文件
        if not write_header and not additional_writing:
            return
        write_mode = "w" if write_header else "a"
        for account_data in accounts_info:
            with open(account_path, write_mode, newline="") as f1:
                w1 = csv.DictWriter(f1, list(account_data))
                if write_header:
                    w1.writeheader()
                w1.writerow(account_data)
    # ----------------------------------------------------------------------------------------------------
    def on_order(self, data: dict) -> None:
        """
        收到委托回报
        """
        for order_data in data:
            category = normalize_category(order_data["category"])
            exchange = CATEGORY_EXCHANGE_MAP[category]
            order = OrderData(
                symbol=make_bitget_symbol(order_data["symbol"], category),
                exchange=exchange,
                orderid=get_bitget_orderid(order_data),
                type=parse_bitget_order_type(order_data),
                direction=DIRECTION_BITGETONE2VT[order_data["side"]],
                price=to_float(order_data["price"]),
                volume=to_float(order_data["qty"]),
                traded=to_float(order_data["cumExecQty"]),
                status=STATUS_BITGETONE2VT[order_data["orderStatus"]],
                datetime=get_local_datetime(to_int(order_data["createdTime"])),
                gateway_name=self.gateway_name,
            )
            if is_reduce_only(order_data.get("reduceOnly")):
                order.offset = Offset.CLOSE
            self.gateway.on_order(order)

    def on_trade(self, data: dict) -> None:
        """
        收到成交回报
        """
        for trade_data in data:
            category = normalize_category(trade_data["category"])
            exchange = CATEGORY_EXCHANGE_MAP[category]
            trade = TradeData(
                symbol=make_bitget_symbol(trade_data["symbol"], category),
                exchange=exchange,
                orderid=get_bitget_orderid(trade_data),
                tradeid=trade_data["execId"],
                direction=DIRECTION_BITGETONE2VT[trade_data["side"]],
                price=to_float(trade_data["execPrice"]),
                volume=to_float(trade_data["execQty"]),
                datetime=get_local_datetime(to_int(trade_data["execTime"])),
                gateway_name=self.gateway_name,
            )
            self.gateway.on_trade(trade)
    # ----------------------------------------------------------------------------------------------------
    def on_position(self, data: dict):
        """
        收到持仓回报
        """
        for pos_data in data:
            raw_symbol = pos_data["symbol"]
            category = self.gateway.rest_api.get_position_category(raw_symbol)
            exchange = CATEGORY_EXCHANGE_MAP.get(category, Exchange.BITGET)
            position = PositionData(
                symbol=make_bitget_symbol(raw_symbol, category),
                exchange=exchange,
                direction=HOLDSIDE_BITGETONE2VT[pos_data["posSide"]],
                volume=abs(to_float(pos_data["size"])),
                frozen=to_float(pos_data["frozen"]),
                price=to_float(pos_data["avgPrice"]),
                pnl=to_float(pos_data["unrealisedPnl"]),
                gateway_name=self.gateway_name,
            )
            self.gateway.on_position(position)
# ----------------------------------------------------------------------------------------------------
def create_signature(secret: str, message: str):
    mac = hmac.new(bytes(secret, encoding="utf8"), bytes(message, encoding="utf-8"), digestmod="sha256").digest()
    sign_str = base64.b64encode(mac).decode()
    return sign_str
