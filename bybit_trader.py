import os
import time
import json
import hmac
import hashlib
import logging
import asyncio
import numpy as np
import websockets
import ccxt
from datetime import datetime, timezone, timedelta
from dotenv import load_dotenv
import sys
from collections import defaultdict

sys.setrecursionlimit(10000)

# Загрузка переменных окружения
load_dotenv()
API_KEY = os.getenv('BYBIT_API_KEY')
SECRET_KEY = os.getenv('BYBIT_SECRET_KEY')

if not API_KEY or not SECRET_KEY:
    print("Error: Bybit API keys not loaded. Check .env file.")
    sys.exit(1)

# Bybit WebSocket URLs для фьючерсов
WS_PUBLIC_URL = 'wss://stream.bybit.com/v5/public/linear'  # Linear futures
WS_PRIVATE_URL = 'wss://stream.bybit.com/v5/private'

class BybitFuturesTrader:
    def __init__(
        self,
        api_key,
        secret_key,
        symbols=['ADAUSDT'],
        amounts=None,
        leverage=10,           # Плечо 10x согласно запросу
        rsi_high_threshold=70, # Верхний порог RSI 70
        rsi_low_threshold=30,  # Нижний порог RSI 30
        stop_loss_percent=0.015,
        trailing_stop=False,
        trailing_distance=0.01,
        activation_percent=0.005,
        # Параметры для уровней поддержки/сопротивления
        use_support_resistance=True,      # Использовать уровни поддержки/сопротивления
        sr_lookback_periods=100,          # Сколько свечей анализировать для поиска уровней
        sr_bounces_needed=2,              # Сколько касаний нужно для подтверждения уровня
        sr_threshold_percent=0.003,       # Порог для группировки уровней (0.3%)
        sr_zone_width_percent=0.004,      # Ширина зоны уровня (0.4%)
        sr_min_level_distance=0.01,       # Минимальная дистанция между уровнями (1%)
        sr_relevance_period=48,           # Как долго (в часах) уровень остается актуальным
        watch_only=False,
        hybrid_mode=True,
        debug_mode=False,
        username="edikua"
    ):
        self.api_key = api_key
        self.secret_key = secret_key
        self.symbols = symbols if isinstance(symbols, list) else [symbols]
        self.amounts = amounts or {symbol: 1 for symbol in self.symbols}
        self.leverage = leverage
        self.rsi_high_threshold = rsi_high_threshold
        self.rsi_low_threshold = rsi_low_threshold
        self.stop_loss_percent = stop_loss_percent
        self.trailing_stop = trailing_stop
        self.trailing_distance = trailing_distance
        self.activation_percent = activation_percent
        self.watch_only = watch_only
        self.hybrid_mode = hybrid_mode
        self.debug_mode = debug_mode
        self.username = username
        
        # Параметры поддержки/сопротивления
        self.use_support_resistance = use_support_resistance
        self.sr_lookback_periods = sr_lookback_periods
        self.sr_bounces_needed = sr_bounces_needed
        self.sr_threshold_percent = sr_threshold_percent
        self.sr_zone_width_percent = sr_zone_width_percent
        self.sr_min_level_distance = sr_min_level_distance
        self.sr_relevance_period = sr_relevance_period

        # Exchange setup - специально для фьючерсов
        self.exchange = ccxt.bybit({
            'apiKey': self.api_key,
            'secret': self.secret_key,
            'enableRateLimit': True,
            'options': {
                'defaultType': 'linear',  # Линейные контракты USDT
                'market_type': 'linear',
                'test': False             # Основная сеть
            }
        })

        # Data structures
        self.candle_history_1m = {symbol: [] for symbol in self.symbols}
        self.ohlcv_data_1m = {symbol: [] for symbol in self.symbols}
        self.last_candle_timestamp_1m = {symbol: 0 for symbol in self.symbols}
        self.candle_history_5m = {symbol: [] for symbol in self.symbols}
        self.ohlcv_data_5m = {symbol: [] for symbol in self.symbols}
        self.last_candle_timestamp_5m = {symbol: 0 for symbol in self.symbols}
        
        # История для уровней поддержки/сопротивления
        self.candle_history_1h = {symbol: [] for symbol in self.symbols}
        self.last_candle_timestamp_1h = {symbol: 0 for symbol in self.symbols}
        
        # Структуры для уровней поддержки/сопротивления
        self.support_levels = {symbol: [] for symbol in self.symbols}      # [{'level': price, 'strength': int, 'timestamp': int, 'touches': int}]
        self.resistance_levels = {symbol: [] for symbol in self.symbols}   # [{'level': price, 'strength': int, 'timestamp': int, 'touches': int}]
        
        self.positions = {symbol: None for symbol in self.symbols}
        self.available_margin = 0
        self.login_successful = False
        self.websocket_ready = False
        self.private_websocket = None
        self.public_websocket = None
        self.websocket = None  # Для общих операций
        self.last_trade_time = {symbol: 0 for symbol in self.symbols}
        self.trade_cooldown = 60  # seconds
        
        # Для трейлинг стопа
        self.trailing_activated = {symbol: False for symbol in self.symbols}
        self.highest_price = {symbol: 0 for symbol in self.symbols}
        self.lowest_price = {symbol: float('inf') for symbol in self.symbols}
        
        # Блокировка для предотвращения дублирования ордеров
        self.order_lock = {symbol: False for symbol in self.symbols}
        
        # Минимальные размеры ордеров - для фьючерсов
        self.min_order_sizes = {'ADAUSDT': 1, 'default': 0.01}
        
        # Setup logger
        self.log_filename = f"bybit_trader_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
        self.setup_logger()
        
        # Log startup info
        utc_time = datetime.now(timezone.utc)
        self.logger.info(f"Скрипт запущен пользователем {self.username}: UTC {utc_time.strftime('%Y-%m-%d %H:%M:%S')}")
        self.logger.info(f"Параметры: Плечо={leverage}x, RSI={rsi_low_threshold}-{rsi_high_threshold}, StopLoss={stop_loss_percent:.1%}")
        
        if self.use_support_resistance:
            self.logger.info(f"Уровни поддержки/сопротивления: Включены, Порог={sr_threshold_percent:.2%}, Зона={sr_zone_width_percent:.2%}")
        
        self.logger.info(f"Режим наблюдения: {watch_only}, Гибридный режим: {hybrid_mode}, Трейлинг стоп: {trailing_stop}, Режим отладки: {debug_mode}")
        
        if trailing_stop and not watch_only:
            self.logger.info(f"Трейлинг стоп настройки: дистанция={trailing_distance:.1%}, активация={activation_percent:.1%}")
            
        if not watch_only:
            self.logger.warning("ВНИМАНИЕ! ВКЛЮЧЕН РЕЖИМ РЕАЛЬНОЙ ТОРГОВЛИ. ВОЗМОЖНЫ ФИНАНСОВЫЕ ПОТЕРИ.")

    def setup_logger(self):
        """Настройка логгера"""
        self.logger = logging.getLogger('BybitTrader')
        self.logger.setLevel(logging.DEBUG if self.debug_mode else logging.INFO)
        formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s', datefmt='%Y-%m-%d %H:%M:%S')

        # Файловый логгер
        file_handler = logging.FileHandler(self.log_filename, encoding='utf-8')
        file_handler.setFormatter(formatter)
        self.logger.addHandler(file_handler)

        # Консольный логгер - используем ascii символы
        console_handler = logging.StreamHandler()
        console_handler.setFormatter(formatter)
        self.logger.addHandler(console_handler)

    def fetch_initial_data(self):
        """Получение начальных данных о балансе, исторических свечах и уровнях поддержки/сопротивления"""
        try:
            # Установка плеча
            if not self.watch_only:
                for symbol in self.symbols:
                    try:
                        self.exchange.set_leverage(self.leverage, symbol)
                        self.logger.info(f"Установлено плечо {self.leverage}x для {symbol}")
                    except Exception as e:
                        self.logger.warning(f"Не удалось установить плечо для {symbol}: {e}")
            
            # Получаем баланс
            balance = self.exchange.fetch_balance()
            if 'USDT' in balance['total']:
                self.available_margin = float(balance['free'].get('USDT', 0))
                self.logger.info(f"Баланс: {balance['total']['USDT']} USDT, доступная маржа: {self.available_margin} USDT")
            
            # Загружаем исторические данные
            for symbol in self.symbols:
                # 1-минутные свечи
                ohlcv_1m = self.exchange.fetch_ohlcv(symbol, timeframe='1m', limit=100)
                for candle in ohlcv_1m:
                    timestamp, o, h, l, c, _ = candle
                    self.candle_history_1m[symbol].append({
                        'timestamp': timestamp, 'open': float(o), 
                        'high': float(h), 'low': float(l), 'close': float(c)
                    })
                    self.ohlcv_data_1m[symbol].append(float(c))
                if ohlcv_1m:
                    self.last_candle_timestamp_1m[symbol] = ohlcv_1m[-1][0]
                self.logger.info(f"Загружено {len(ohlcv_1m)} 1m свечей для {symbol}")

                # 5-минутные свечи
                ohlcv_5m = self.exchange.fetch_ohlcv(symbol, timeframe='5m', limit=100)
                for candle in ohlcv_5m:
                    timestamp, o, h, l, c, _ = candle
                    self.candle_history_5m[symbol].append({
                        'timestamp': timestamp, 'open': float(o), 
                        'high': float(h), 'low': float(l), 'close': float(c)
                    })
                    self.ohlcv_data_5m[symbol].append(float(c))
                if ohlcv_5m:
                    self.last_candle_timestamp_5m[symbol] = ohlcv_5m[-1][0]
                self.logger.info(f"Загружено {len(ohlcv_5m)} 5m свечей для {symbol}")
                
                # 1-часовые свечи для уровней поддержки/сопротивления
                if self.use_support_resistance:
                    ohlcv_1h = self.exchange.fetch_ohlcv(symbol, timeframe='1h', limit=self.sr_lookback_periods)
                    for candle in ohlcv_1h:
                        timestamp, o, h, l, c, _ = candle
                        self.candle_history_1h[symbol].append({
                            'timestamp': timestamp, 'open': float(o), 
                            'high': float(h), 'low': float(l), 'close': float(c)
                        })
                    if ohlcv_1h:
                        self.last_candle_timestamp_1h[symbol] = ohlcv_1h[-1][0]
                    self.logger.info(f"Загружено {len(ohlcv_1h)} 1h свечей для {symbol}")
                    
                    # Рассчитываем начальные уровни поддержки/сопротивления
                    self.calculate_support_resistance_levels(symbol)
                
            # Проверка существующих позиций
            try:
                positions = self.exchange.fetch_positions(self.symbols)
                for position in positions:
                    if float(position.get('contracts', 0)) > 0:
                        symbol = position['symbol']
                        if symbol in self.symbols:
                            side = position['side']
                            entry_price = float(position['entryPrice'])
                            
                            self.positions[symbol] = {
                                "symbol": symbol,
                                "side": side,
                                "entry_price": entry_price,
                                "stop_loss_price": entry_price * (
                                    1 - self.stop_loss_percent if side == "long" else 
                                    1 + self.stop_loss_percent
                                )
                            }
                            self.logger.info(f"Обнаружена позиция: {symbol} {side} @ {entry_price}")
                            
                            # Инициализируем данные для трейлинга при существующей позиции
                            if self.trailing_stop:
                                if side == "long" or side == "Buy":
                                    self.highest_price[symbol] = entry_price
                                else:
                                    self.lowest_price[symbol] = entry_price
            except Exception as e:
                self.logger.warning(f"Не удалось проверить позиции: {e}")
                
        except Exception as e:
            self.logger.error(f"Ошибка загрузки начальных данных: {e}")

    def calculate_rsi(self, prices, period=14):
        """Безопасный расчет RSI индикатора"""
        if len(prices) < period + 1:
            return None
            
        deltas = np.diff(prices)
        ups = np.maximum(deltas, 0)
        downs = np.maximum(-deltas, 0)
        
        # Первоначальное сглаживание
        avg_gain = np.mean(ups[:period])
        avg_loss = np.mean(downs[:period])
        
        if avg_loss == 0:  # Избегаем деления на ноль
            return 100.0
            
        # Рекурсивное сглаживание
        for i in range(period, len(deltas)):
            avg_gain = ((avg_gain * (period - 1)) + ups[i]) / period
            avg_loss = ((avg_loss * (period - 1)) + downs[i]) / period
            
        # Расчет RS и RSI
        if avg_loss == 0:  # Избегаем деления на ноль
            return 100.0
            
        rs = avg_gain / avg_loss
        rsi = 100 - (100 / (1 + rs))
        
        return rsi

    def detect_pattern(self, candle_history, pattern_type='bullish'):
        """Определение свечных паттернов - оставляем для совместимости, но не используем"""
        if len(candle_history) < 2:
            return False
            
        try:
            current = candle_history[-1]
            previous = candle_history[-2]
            
            candle_range = current['high'] - current['low']
            if candle_range == 0:  # Избегаем деления на ноль
                return False
                
            real_body = abs(current['close'] - current['open'])
            
            if pattern_type == 'bullish':
                # Бычьи паттерны: молот или поглощение
                lower_shadow = min(current['open'], current['close']) - current['low']
                hammer = (
                    real_body <= 0.3 * candle_range and
                    lower_shadow >= 0.6 * candle_range and
                    current['close'] > current['open']
                )
                
                bullish_engulfing = (
                    current['close'] > previous['open'] and
                    current['open'] < previous['close'] and
                    current['close'] > current['open'] and
                    previous['close'] < previous['open'] and
                    (current['close'] - current['open']) > (previous['open'] - previous['close'])
                )
                
                return hammer or bullish_engulfing
            else:
                # Медвежьи паттерны: звезда или поглощение
                upper_shadow = current['high'] - max(current['open'], current['close'])
                shooting_star = (
                    real_body <= 0.3 * candle_range and
                    upper_shadow >= 0.6 * candle_range and
                    current['close'] < current['open']
                )
                
                bearish_engulfing = (
                    current['close'] < previous['open'] and
                    current['open'] > previous['close'] and
                    current['close'] < current['open'] and
                    previous['close'] > previous['open'] and
                    (current['open'] - current['close']) > (previous['close'] - previous['open'])
                )
                
                return shooting_star or bearish_engulfing
        except Exception as e:
            if self.debug_mode:
                self.logger.error(f"Ошибка определения паттерна: {e}")
            return False

    def calculate_support_resistance_levels(self, symbol):
        """Расчет уровней поддержки и сопротивления на основе исторических данных"""
        if not self.use_support_resistance:
            return
            
        if len(self.candle_history_1h[symbol]) < 30:  # Минимум 30 часовых свечей
            self.logger.warning(f"Недостаточно данных для расчета уровней S/R для {symbol}")
            return
            
        self.logger.info(f"Расчет уровней поддержки и сопротивления для {symbol}...")
        
        # Очищаем устаревшие уровни (старше sr_relevance_period часов)
        current_time = int(time.time() * 1000)
        relevance_ms = self.sr_relevance_period * 60 * 60 * 1000
        
        self.support_levels[symbol] = [level for level in self.support_levels[symbol] 
                                    if current_time - level['timestamp'] < relevance_ms]
        self.resistance_levels[symbol] = [level for level in self.resistance_levels[symbol] 
                                       if current_time - level['timestamp'] < relevance_ms]
        
        # Извлекаем максимумы и минимумы из часовых свечей
        highs = [candle['high'] for candle in self.candle_history_1h[symbol]]
        lows = [candle['low'] for candle in self.candle_history_1h[symbol]]
        
        # Находим локальные максимумы и минимумы для уровней
        pivots_high, pivots_low = self.find_pivot_points(highs, lows)
        current_price = self.candle_history_1h[symbol][-1]['close']
        
        # Группировка близких уровней сопротивления
        resistance_groups = self.group_price_levels(pivots_high, current_price)
        # Группировка близких уровней поддержки
        support_groups = self.group_price_levels(pivots_low, current_price)
        
        # Обновляем текущие уровни или добавляем новые
        for level_price, count in resistance_groups.items():
            if count >= self.sr_bounces_needed:
                # Проверяем, есть ли уже такой уровень
                found = False
                for level in self.resistance_levels[symbol]:
                    # Если уровень примерно такой же (в пределах порога)
                    if abs(level['level'] - level_price) / level_price < self.sr_threshold_percent:
                        level['touches'] += 1
                        level['strength'] = level['touches'] * (1 + count / 10)  # Увеличиваем силу уровня
                        level['level'] = (level['level'] * 0.7 + level_price * 0.3)  # Скользящее среднее для корректировки
                        found = True
                        break
                
                # Если это новый уровень
                if not found:
                    # Проверяем, не слишком ли близок к существующим уровням
                    too_close = False
                    for level in self.resistance_levels[symbol]:
                        if abs(level['level'] - level_price) / level_price < self.sr_min_level_distance:
                            too_close = True
                            break
                    
                    if not too_close:
                        self.resistance_levels[symbol].append({
                            'level': level_price,
                            'strength': count,
                            'timestamp': current_time,
                            'touches': 1
                        })
        
        # Аналогично для уровней поддержки
        for level_price, count in support_groups.items():
            if count >= self.sr_bounces_needed:
                found = False
                for level in self.support_levels[symbol]:
                    if abs(level['level'] - level_price) / level_price < self.sr_threshold_percent:
                        level['touches'] += 1
                        level['strength'] = level['touches'] * (1 + count / 10)
                        level['level'] = (level['level'] * 0.7 + level_price * 0.3)
                        found = True
                        break
                
                if not found:
                    too_close = False
                    for level in self.support_levels[symbol]:
                        if abs(level['level'] - level_price) / level_price < self.sr_min_level_distance:
                            too_close = True
                            break
                    
                    if not too_close:
                        self.support_levels[symbol].append({
                            'level': level_price,
                            'strength': count,
                            'timestamp': current_time,
                            'touches': 1
                        })
        
        # Сортируем уровни по цене (сопротивление - по убыванию, поддержка - по возрастанию)
        self.resistance_levels[symbol] = sorted(self.resistance_levels[symbol], 
                                             key=lambda x: x['level'], reverse=True)
        self.support_levels[symbol] = sorted(self.support_levels[symbol], 
                                          key=lambda x: x['level'])
        
        # Выводим текущие основные уровни
        if self.resistance_levels[symbol]:
            self.logger.info(f"{symbol} Уровни сопротивления: " + 
                          ", ".join([f"{level['level']:.6f} (сила:{level['strength']:.1f})" 
                                  for level in self.resistance_levels[symbol][:3]]))
        
        if self.support_levels[symbol]:
            self.logger.info(f"{symbol} Уровни поддержки: " + 
                          ", ".join([f"{level['level']:.6f} (сила:{level['strength']:.1f})" 
                                  for level in self.support_levels[symbol][:3]]))

    def find_pivot_points(self, highs, lows, window=5):
        """Находит локальные максимумы и минимумы (точки разворота)"""
        pivot_high, pivot_low = [], []
        
        # Находим локальные максимумы (уровни сопротивления)
        for i in range(window, len(highs) - window):
            if highs[i] == max(highs[i-window:i+window+1]):
                pivot_high.append(highs[i])
        
        # Находим локальные минимумы (уровни поддержки)
        for i in range(window, len(lows) - window):
            if lows[i] == min(lows[i-window:i+window+1]):
                pivot_low.append(lows[i])
                
        return pivot_high, pivot_low

    def group_price_levels(self, prices, current_price):
        """Группирует близкие ценовые уровни для нахождения зон поддержки/сопротивления"""
        groups = defaultdict(int)
        
        for price in prices:
            # Игнорируем слишком старые уровни, которые слишком далеко от текущей цены
            max_deviation = 0.2  # 20%
            if abs(price - current_price) / current_price > max_deviation:
                continue
                
            # Проверяем, подходит ли цена под существующую группу
            found_group = False
            for group_price in list(groups.keys()):
                if abs(group_price - price) / group_price < self.sr_threshold_percent:
                    # Обновляем центр группы как взвешенное среднее
                    new_group = (group_price * groups[group_price] + price) / (groups[group_price] + 1)
                    groups[new_group] = groups.pop(group_price) + 1
                    found_group = True
                    break
            
            # Если не нашли подходящую группу, создаем новую
            if not found_group:
                groups[price] = 1
                
        return dict(groups)

    def is_near_resistance(self, symbol, price, margin_percent=None):
        """Проверяет, находится ли цена вблизи уровня сопротивления"""
        if not self.use_support_resistance or not self.resistance_levels[symbol]:
            return None, 0
            
        margin = margin_percent or self.sr_zone_width_percent
        
        # Проверяем все уровни сопротивления
        for level in self.resistance_levels[symbol]:
            level_price = level['level']
            # Если цена в зоне уровня сопротивления
            if price >= level_price * (1 - margin) and price <= level_price * (1 + margin):
                return level, 1 - (abs(price - level_price) / (level_price * margin))
                
        return None, 0

    def is_near_support(self, symbol, price, margin_percent=None):
        """Проверяет, находится ли цена вблизи уровня поддержки"""
        if not self.use_support_resistance or not self.support_levels[symbol]:
            return None, 0
            
        margin = margin_percent or self.sr_zone_width_percent
        
        # Проверяем все уровни поддержки
        for level in self.support_levels[symbol]:
            level_price = level['level']
            # Если цена в зоне уровня поддержки
            if price >= level_price * (1 - margin) and price <= level_price * (1 + margin):
                return level, 1 - (abs(price - level_price) / (level_price * margin))
                
        return None, 0

    # Размещение ордеров через REST API с защитой от дублирования
    async def place_order(self, symbol, side, amount):
        """Размещение ордера через REST API с защитой от дублирования"""
        if self.watch_only:
            self.logger.info(f"[СИГНАЛ] {symbol} - {side.upper()}: Размер={amount} (режим наблюдения)")
            return
        
        # ВАЖНО: Проверяем наличие открытой позиции перед размещением ордера
        try:
            # Запрашиваем текущие позиции прямо перед размещением ордера
            positions = self.exchange.fetch_positions([symbol])
            for position in positions:
                if symbol == position['symbol'] and float(position.get('contracts', 0)) > 0:
                    self.logger.warning(f"Ордер не размещен: уже существует открытая позиция по {symbol}")
                    
                    # Обновляем информацию о позиции
                    self.positions[symbol] = {
                        "symbol": symbol,
                        "side": position['side'],
                        "entry_price": float(position['entryPrice']),
                        "stop_loss_price": float(position['entryPrice']) * (
                            1 - self.stop_loss_percent if position['side'] == 'long' else 
                            1 + self.stop_loss_percent
                        )
                    }
                    return False
        except Exception as e:
            self.logger.error(f"Ошибка проверки позиций: {e}")
            
        # Проверка минимального размера
        min_size = self.min_order_sizes.get(symbol, self.min_order_sizes['default'])
        if amount < min_size:
            amount = min_size
            
        # Округление для определенных монет
        if symbol in ['ADAUSDT', 'XRPUSDT', 'DOGEUSDT']:
            amount = int(amount)
        
        # Сторона ордера
        position_side = "buy" if side.lower() == "buy" else "sell"
        current_price = self.candle_history_1m[symbol][-1]['close']
        
        try:
            self.logger.info(f"Отправка ордера через REST API: {position_side.upper()} {amount} {symbol} по цене ~{current_price}")
            
            # Используем CCXT для размещения рыночного ордера
            order = self.exchange.create_market_order(
                symbol,
                position_side,
                amount,
                params={'category': 'linear'}  # Указываем линейные фьючерсы
            )
            
            self.last_trade_time[symbol] = time.time()
            order_id = order.get('id', 'unknown')
            self.logger.info(f"Ордер успешно размещен: ID={order_id}")
            
            # ВАЖНО: Немедленно обновляем информацию о позиции в локальной памяти
            if position_side == "buy":
                self.positions[symbol] = {
                    "symbol": symbol,
                    "side": "long",
                    "entry_price": current_price,
                    "stop_loss_price": current_price * (1 - self.stop_loss_percent)
                }
                
                # Для трейлинга
                if self.trailing_stop:
                    self.trailing_activated[symbol] = False
                    self.highest_price[symbol] = current_price
                
            else:  # sell
                self.positions[symbol] = {
                    "symbol": symbol,
                    "side": "short",
                    "entry_price": current_price,
                    "stop_loss_price": current_price * (1 + self.stop_loss_percent)
                }
                
                # Для трейлинга
                if self.trailing_stop:
                    self.trailing_activated[symbol] = False
                    self.lowest_price[symbol] = current_price
            
            return True
        except Exception as e:
            self.logger.error(f"Ошибка отправки ордера: {e}")
            return False

    def stop_loss_triggered(self, position):
        """Проверка срабатывания стоп-лосса"""
        if not position:
            return False
            
        symbol = position.get('symbol')
        if not symbol or symbol not in self.symbols:
            return False
            
        current_price = self.candle_history_1m[symbol][-1]['close']
        side = position['side']
        stop_loss_price = position['stop_loss_price']
        
        if side == "Buy" or side == "long":
            return current_price <= stop_loss_price
        else:
            return current_price >= stop_loss_price

    async def handle_message(self, message):
        """Обработка сообщений WebSocket"""
        try:
            data = json.loads(message)
            
            # Обработка пинг-понг
            if "op" in data and data["op"] == "ping":
                if self.websocket:
                    await self.websocket.send(json.dumps({"op": "pong"}))
                return
                
            # Обработка подписки
            if "op" in data and data["op"] == "subscribe":
                if data.get("success") and self.debug_mode:
                    self.logger.debug(f"Подписка успешна: {data.get('args', [])}")
                return
                
            # Обработка тикера
            if "topic" in data and data["topic"].startswith("tickers."):
                symbol = data["topic"].split(".")[1]
                ticker_data = data["data"]
                
                price = None
                if 'lastPrice' in ticker_data:
                    price = float(ticker_data['lastPrice'])
                elif 'last' in ticker_data:
                    price = float(ticker_data['last'])
                
                if price and symbol in self.symbols:
                    timestamp = int(time.time() * 1000)
                    current_minute = (timestamp // 60000) * 60000
                    
                    if current_minute > self.last_candle_timestamp_1m[symbol]:
                        candle = {
                            'timestamp': current_minute,
                            'open': price, 'high': price,
                            'low': price, 'close': price
                        }
                        self.candle_history_1m[symbol].append(candle)
                        self.ohlcv_data_1m[symbol].append(price)
                        self.last_candle_timestamp_1m[symbol] = current_minute
                        
                        if len(self.candle_history_1m[symbol]) > 200:
                            self.candle_history_1m[symbol] = self.candle_history_1m[symbol][-200:]
                        if len(self.ohlcv_data_1m[symbol]) > 200:
                            self.ohlcv_data_1m[symbol] = self.ohlcv_data_1m[symbol][-200:]
                return
                
            # Обработка свечей
            if "topic" in data and data["topic"].startswith("kline."):
                parts = data["topic"].split(".")
                interval, symbol = parts[1], parts[2]
                
                if "data" in data and len(data["data"]) > 0 and symbol in self.symbols:
                    kline = data["data"][0]
                    start_time = int(kline.get('start', 0))
                    open_price = float(kline.get('open', 0))
                    high_price = float(kline.get('high', 0))
                    low_price = float(kline.get('low', 0))
                    close_price = float(kline.get('close', 0))
                    
                    candle = {
                        'timestamp': start_time, 'open': open_price,
                        'high': high_price, 'low': low_price, 'close': close_price
                    }
                    
                    if interval == "1":
                        # Обработка 1m свечи
                        if len(self.candle_history_1m[symbol]) > 0 and self.candle_history_1m[symbol][-1]['timestamp'] == start_time:
                            # Обновление существующей свечи
                            self.candle_history_1m[symbol][-1] = candle
                            self.ohlcv_data_1m[symbol][-1] = close_price
                        else:
                            # Добавление новой свечи
                            self.candle_history_1m[symbol].append(candle)
                            self.ohlcv_data_1m[symbol].append(close_price)
                            
                            # Ограничение размера массивов
                            if len(self.candle_history_1m[symbol]) > 200:
                                self.candle_history_1m[symbol] = self.candle_history_1m[symbol][-200:]
                            if len(self.ohlcv_data_1m[symbol]) > 200:
                                self.ohlcv_data_1m[symbol] = self.ohlcv_data_1m[symbol][-200:]
                                
                        self.last_candle_timestamp_1m[symbol] = start_time
                        self.logger.info(f"Обработана свеча 1m для {symbol}: C={close_price}")
                        
                    elif interval == "5":
                        # Обработка 5m свечи
                        if len(self.candle_history_5m[symbol]) > 0 and self.candle_history_5m[symbol][-1]['timestamp'] == start_time:
                            # Обновление существующей свечи
                            self.candle_history_5m[symbol][-1] = candle
                            self.ohlcv_data_5m[symbol][-1] = close_price
                        else:
                            # Добавление новой свечи
                            self.candle_history_5m[symbol].append(candle)
                            self.ohlcv_data_5m[symbol].append(close_price)
                            
                            # Ограничение размера массивов
                            if len(self.candle_history_5m[symbol]) > 200:
                                self.candle_history_5m[symbol] = self.candle_history_5m[symbol][-200:]
                            if len(self.ohlcv_data_5m[symbol]) > 200:
                                self.ohlcv_data_5m[symbol] = self.ohlcv_data_5m[symbol][-200:]
                                
                        self.last_candle_timestamp_5m[symbol] = start_time
                        self.logger.info(f"Обработана свеча 5m для {symbol}: C={close_price}")
                    elif interval == "60" and self.use_support_resistance:
                        # Обработка часовых свечей для уровней поддержки/сопротивления
                        if len(self.candle_history_1h[symbol]) > 0 and self.candle_history_1h[symbol][-1]['timestamp'] == start_time:
                            # Обновление существующей свечи
                            self.candle_history_1h[symbol][-1] = candle
                        else:
                            # Добавление новой свечи
                            self.candle_history_1h[symbol].append(candle)
                            
                            # Ограничение размера массивов
                            if len(self.candle_history_1h[symbol]) > self.sr_lookback_periods:
                                self.candle_history_1h[symbol] = self.candle_history_1h[symbol][-self.sr_lookback_periods:]
                                
                            # Пересчитываем уровни поддержки/сопротивления
                            self.calculate_support_resistance_levels(symbol)
                                
                        self.last_candle_timestamp_1h[symbol] = start_time
                return

        except Exception as e:
            self.logger.error(f"Ошибка обработки сообщения: {e}")
            if self.debug_mode:
                self.logger.error(f"Текст сообщения: {message[:100]}...")

    async def update_trailing_stop(self):
        """Обновление трейлинг стоп-лосса"""
        if not self.trailing_stop or self.watch_only:
            return
            
        while True:
            for symbol in self.symbols:
                position = self.positions.get(symbol)
                if not position:
                    # Сбрасываем трейлинг если нет позиции
                    self.trailing_activated[symbol] = False
                    self.highest_price[symbol] = 0
                    self.lowest_price[symbol] = float('inf')
                    continue
                    
                current_price = self.candle_history_1m[symbol][-1]['close']
                entry_price = position['entry_price']
                side = position['side']
                
                if side == "Buy" or side == "long":
                    # Для длинных позиций
                    profit_percent = (current_price - entry_price) / entry_price
                    
                    # Проверяем активацию трейлинга
                    if not self.trailing_activated[symbol] and profit_percent >= self.activation_percent:
                        self.trailing_activated[symbol] = True
                        self.highest_price[symbol] = current_price
                        self.logger.info(f"[{symbol}] Трейлинг стоп активирован: цена={current_price}, прибыль={profit_percent:.2%}")
                    
                    # Обновляем трейлинг стоп
                    if self.trailing_activated[symbol]:
                        if current_price > self.highest_price[symbol]:
                            self.highest_price[symbol] = current_price
                            new_stop_loss = current_price * (1 - self.trailing_distance)
                            if new_stop_loss > position['stop_loss_price']:
                                old_stop = position['stop_loss_price']
                                position['stop_loss_price'] = new_stop_loss
                                self.logger.info(f"[{symbol}] Трейлинг стоп обновлен: {old_stop:.6f} -> {new_stop_loss:.6f}")
                else:
                    # Для коротких позиций
                    profit_percent = (entry_price - current_price) / entry_price
                    
                    # Проверяем активацию трейлинга
                    if not self.trailing_activated[symbol] and profit_percent >= self.activation_percent:
                        self.trailing_activated[symbol] = True
                        self.lowest_price[symbol] = current_price
                        self.logger.info(f"[{symbol}] Трейлинг стоп активирован: цена={current_price}, прибыль={profit_percent:.2%}")
                    
                    # Обновляем трейлинг стоп
                    if self.trailing_activated[symbol]:
                        if current_price < self.lowest_price[symbol]:
                            self.lowest_price[symbol] = current_price
                            new_stop_loss = current_price * (1 + self.trailing_distance)
                            if new_stop_loss < position['stop_loss_price']:
                                old_stop = position['stop_loss_price']
                                position['stop_loss_price'] = new_stop_loss
                                self.logger.info(f"[{symbol}] Трейлинг стоп обновлен: {old_stop:.6f} -> {new_stop_loss:.6f}")
            
            # Проверяем каждые 2 секунды
            await asyncio.sleep(2)

    async def calculate_indicators(self):
        """Расчет индикаторов и торговая логика с упрощенными условиями входа - только RSI"""
        while not self.websocket_ready:
            await asyncio.sleep(1)

        self.logger.info("Расчёт индикаторов начат (только RSI, без паттернов)")
        last_log_time = {symbol: 0 for symbol in self.symbols}

        while True:
            current_time = time.time()
            
            for symbol in self.symbols:
                # Проверка минимума данных
                if (len(self.ohlcv_data_1m[symbol]) <= 14 or 
                    len(self.candle_history_1m[symbol]) <= 1 or
                    len(self.ohlcv_data_5m[symbol]) <= 14 or
                    len(self.candle_history_5m[symbol]) <= 1):
                    continue
                    
                # Пропускаем если ордер уже в процессе размещения
                if self.order_lock[symbol]:
                    continue
                    
                # Расчет индикаторов
                try:
                    # Рассчитываем только RSI для обоих таймфреймов
                    rsi_1m = self.calculate_rsi(self.ohlcv_data_1m[symbol])
                    rsi_5m = self.calculate_rsi(self.ohlcv_data_5m[symbol])
                    
                    current_price = self.candle_history_1m[symbol][-1]['close']
                    
                    # Проверка уровней поддержки/сопротивления
                    near_resistance, resist_strength = self.is_near_resistance(symbol, current_price)
                    near_support, support_strength = self.is_near_support(symbol, current_price)
                    
                    # Дополнительная информация для логирования
                    sr_info = ""
                    if near_resistance:
                        sr_info += f", Сопр: {near_resistance['level']:.6f} ({resist_strength:.2f})"
                    if near_support:
                        sr_info += f", Подд: {near_support['level']:.6f} ({support_strength:.2f})"

                    # Логируем индикаторы каждые 10 секунд
                    if current_time - last_log_time[symbol] >= 10:
                        self.logger.info(f"{symbol} - RSI 1m: {rsi_1m:.2f}, RSI 5m: {rsi_5m:.2f}{sr_info}")
                        last_log_time[symbol] = current_time

                    # Проверяем торговые условия
                    if (rsi_1m is not None and rsi_5m is not None and 
                        current_time - self.last_trade_time[symbol] >= self.trade_cooldown):
                        
                        # Проверка стоп-лосса
                        if self.positions[symbol] and self.stop_loss_triggered(self.positions[symbol]):
                            pos = self.positions[symbol]
                            close_side = "sell" if pos["side"] == "Buy" or pos["side"] == "long" else "buy"
                            self.logger.info(f"[{symbol}] Стоп-лосс сработал: закрытие {pos['side']}, цена={current_price}")
                            
                            self.order_lock[symbol] = True
                            await self.place_order(symbol, close_side, self.amounts[symbol])
                            self.order_lock[symbol] = False
                            continue
                            
                        # УПРОЩЕННАЯ ТОРГОВАЯ ЛОГИКА - только если нет позиции
                        if not self.positions[symbol]:
                            # ПОКУПКА: только RSI на обоих таймфреймах < 30
                            buy_signal = (rsi_1m < self.rsi_low_threshold and rsi_5m < self.rsi_low_threshold)
                            
                            # Усиление сигнала при наличии уровня поддержки
                            if buy_signal:
                                buy_strength = 1.0  # Базовая сила сигнала
                                if near_support and support_strength > 0.5:
                                    buy_strength += 0.5  # Усиление при наличии поддержки
                                    self.logger.info(f"[{symbol}] Усиление сигнала ПОКУПКИ у уровня поддержки {near_support['level']:.6f}")
                                    
                                # Ослабление при наличии сопротивления рядом
                                if near_resistance and resist_strength > 0.7:
                                    buy_strength -= 0.7
                                    self.logger.info(f"[{symbol}] Ослабление сигнала ПОКУПКИ у уровня сопротивления {near_resistance['level']:.6f}")
                                    
                                # Если сигнал всё еще положительный
                                if buy_strength > 0:
                                    self.logger.info(f"[{symbol}] ПОКУПКА: RSI 1m={rsi_1m:.2f}, RSI 5m={rsi_5m:.2f}, Price={current_price}{sr_info}")
                                    
                                    self.order_lock[symbol] = True
                                    await self.place_order(symbol, "buy", self.amounts[symbol])
                                    self.order_lock[symbol] = False
                            
                            # ПРОДАЖА: только RSI на обоих таймфреймах > 70
                            sell_signal = (rsi_1m > self.rsi_high_threshold and rsi_5m > self.rsi_high_threshold)
                            
                            # Усиление сигнала при наличии уровня сопротивления
                            if sell_signal:
                                sell_strength = 1.0  # Базовая сила сигнала
                                if near_resistance and resist_strength > 0.5:
                                    sell_strength += 0.5  # Усиление при наличии сопротивления
                                    self.logger.info(f"[{symbol}] Усиление сигнала ПРОДАЖИ у уровня сопротивления {near_resistance['level']:.6f}")
                                    
                                # Ослабление при наличии поддержки рядом
                                if near_support and support_strength > 0.7:
                                    sell_strength -= 0.7
                                    self.logger.info(f"[{symbol}] Ослабление сигнала ПРОДАЖИ у уровня поддержки {near_support['level']:.6f}")
                                    
                                # Если сигнал всё еще положительный
                                if sell_strength > 0:
                                    self.logger.info(f"[{symbol}] ПРОДАЖА: RSI 1m={rsi_1m:.2f}, RSI 5m={rsi_5m:.2f}, Price={current_price}{sr_info}")
                                    
                                    self.order_lock[symbol] = True
                                    await self.place_order(symbol, "sell", self.amounts[symbol])
                                    self.order_lock[symbol] = False
                except Exception as e:
                    self.logger.error(f"Ошибка расчёта индикаторов для {symbol}: {e}")
                    self.order_lock[symbol] = False  # Снимаем блокировку при ошибке

            await asyncio.sleep(2)
            
    # Периодическое обновление позиций через REST API
    async def update_positions(self):
        """Обновление информации о позициях через REST API"""
        if self.watch_only:
            return
            
        while True:
            try:
                positions = self.exchange.fetch_positions(self.symbols)
                for position in positions:
                    symbol = position['symbol']
                    if symbol in self.symbols:
                        size = float(position.get('contracts', 0))
                        
                        if size > 0:
                            side = position['side']
                            entry_price = float(position['entryPrice'])
                            
                            # Обновляем существующую позицию или создаем новую
                            if self.positions[symbol] is None:
                                # Новая позиция - устанавливаем стоп-лосс
                                self.positions[symbol] = {
                                    "symbol": symbol,
                                    "side": side,
                                    "entry_price": entry_price,
                                    "stop_loss_price": entry_price * (
                                        1 - self.stop_loss_percent if side == "long" else 
                                        1 + self.stop_loss_percent
                                    )
                                }
                                self.logger.info(f"Новая позиция найдена: {symbol} {side} {size} @ {entry_price}")
                                
                                # Для трейлинга
                                if self.trailing_stop:
                                    if side == "long" or side == "Buy":
                                        self.highest_price[symbol] = entry_price
                                    else:
                                        self.lowest_price[symbol] = entry_price
                            
                        elif size == 0 and self.positions[symbol] is not None:
                            # Позиция закрыта
                            self.logger.info(f"Позиция по {symbol} закрыта")
                            self.positions[symbol] = None
                            
                            # Сбрасываем трейлинг
                            if self.trailing_stop:
                                self.trailing_activated[symbol] = False
                
            except Exception as e:
                self.logger.error(f"Ошибка при обновлении позиций: {e}")
                
            await asyncio.sleep(30)  # Обновляем каждые 30 секунд

    async def subscribe_channels(self, websocket):
        """Подписка на публичные WebSocket каналы"""
        # Публичные каналы
        for symbol in self.symbols:
            # Тикеры
            await websocket.send(json.dumps({
                "op": "subscribe",
                "args": [f"tickers.{symbol}"]
            }))
            await asyncio.sleep(0.3)
            
            # 1m свечи
            await websocket.send(json.dumps({
                "op": "subscribe", 
                "args": [f"kline.1.{symbol}"]
            }))
            await asyncio.sleep(0.3)
            
            # 5m свечи
            await websocket.send(json.dumps({
                "op": "subscribe", 
                "args": [f"kline.5.{symbol}"]
            }))
            await asyncio.sleep(0.3)
            
            # 1h свечи для уровней поддержки/сопротивления
            if self.use_support_resistance:
                await websocket.send(json.dumps({
                    "op": "subscribe", 
                    "args": [f"kline.60.{symbol}"]
                }))
                await asyncio.sleep(0.3)
        
        self.logger.info("Подписка на публичные каналы выполнена")

    async def run_public_websocket(self):
        """Подключение к публичному WebSocket"""
        while True:
            try:
                async with websockets.connect(WS_PUBLIC_URL) as websocket:
                    self.public_websocket = websocket
                    self.websocket = websocket  # Для пинг-понга
                    
                    self.logger.info(f"Подключен к публичному WebSocket")
                    await self.subscribe_channels(websocket)
                    self.websocket_ready = True
                    
                    async for message in websocket:
                        await self.handle_message(message)
                        
            except websockets.exceptions.ConnectionClosed as e:
                self.logger.error(f"Соединение с публичным WebSocket закрыто: {e}")
                self.websocket_ready = False
                await asyncio.sleep(5)
            except Exception as e:
                self.logger.error(f"Ошибка публичного WebSocket: {e}")
                self.websocket_ready = False
                await asyncio.sleep(5)

    async def run(self):
        """Основной метод запуска"""
        self.logger.info("Запуск Bybit Futures трейдера (с уровнями поддержки/сопротивления)...")
        self.fetch_initial_data()
        self.logger.info(f"Торговля активирована для символов: {self.symbols}")
        
        # Запуск задач
        tasks = [
            self.run_public_websocket(),
            self.calculate_indicators()
        ]
        
        # Добавляем задачу обновления позиций через REST API, если не в режиме наблюдения
        if not self.watch_only and self.hybrid_mode:
            tasks.append(self.update_positions())
            
        # Добавляем трейлинг стоп если включен
        if self.trailing_stop and not self.watch_only:
            tasks.append(self.update_trailing_stop())
            
        await asyncio.gather(*tasks)

async def main():
    """Основная функция"""
    # Получение параметров из .env файла
    leverage = int(os.getenv('LEVERAGE', '10'))        # Плечо 10x как запросил пользователь
    rsi_low = float(os.getenv('RSI_LOW', '30'))        # RSI нижний порог 30
    rsi_high = float(os.getenv('RSI_HIGH', '70'))      # RSI верхний порог 70
    stop_loss = float(os.getenv('STOP_LOSS', '0.015'))
    position_size = float(os.getenv('POSITION_SIZE', '1'))
    watch_only = os.getenv('WATCH_ONLY', 'false').lower() == 'true'
    hybrid_mode = os.getenv('HYBRID_MODE', 'true').lower() == 'true'
    debug_mode = os.getenv('DEBUG_MODE', 'false').lower() == 'true'
    trailing_stop = os.getenv('TRAILING_STOP', 'false').lower() == 'true'
    trailing_distance = float(os.getenv('TRAILING_DISTANCE', '0.01'))
    activation_percent = float(os.getenv('ACTIVATION_PERCENT', '0.005'))
    
    # Параметры для уровней поддержки/сопротивления
    use_sr = os.getenv('USE_SUPPORT_RESISTANCE', 'true').lower() == 'true'
    sr_threshold = float(os.getenv('SR_THRESHOLD', '0.003'))
    sr_zone_width = float(os.getenv('SR_ZONE_WIDTH', '0.004'))
    sr_bounces = int(os.getenv('SR_BOUNCES', '2'))
    
    # Текущая дата: 2025-04-03
    trader = BybitFuturesTrader(
        api_key=API_KEY,
        secret_key=SECRET_KEY,
        symbols=['ADAUSDT'],  # USDT-M фьючерсы
        amounts={'ADAUSDT': position_size},
        leverage=leverage,                # Используем плечо 10
        rsi_low_threshold=rsi_low,        # Нижний порог RSI (30)
        rsi_high_threshold=rsi_high,      # Верхний порог RSI (70)
        stop_loss_percent=stop_loss,
        trailing_stop=trailing_stop,
        trailing_distance=trailing_distance,
        activation_percent=activation_percent,
        use_support_resistance=use_sr,
        sr_threshold_percent=sr_threshold,
        sr_zone_width_percent=sr_zone_width,
        sr_bounces_needed=sr_bounces,
        watch_only=watch_only,
        hybrid_mode=hybrid_mode,
        debug_mode=debug_mode,
        username="edikua"
    )
    
    await trader.run()

if __name__ == "__main__":
    asyncio.run(main())
