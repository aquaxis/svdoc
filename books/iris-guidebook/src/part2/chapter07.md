# 第7章 インターフェース

## 本章のゴール

- `interface`を理解する
- ビューを使用できる
- 再利用可能な設計ができる

---

## 7.1 インターフェースの基本

インターフェースは、関連する信号をグループ化して管理する仕組みです。

### 基本定義

```rust
interface Handshake {
    valid: bit,
    ready: bit,
    data:  bit[8],

    // ビュー定義
    view initiator {
        out: valid, data,
        in:  ready
    }

    view target {
        in:  valid, data,
        out: ready
    }
}
```

---

## 7.2 ビュー

ビューは、インターフェースを使用する側の視点を定義します。

### 標準ビュー名

| ビュー名 | 説明 | 用途 |
|----------|------|------|
| `initiator` | トランザクション開始側 | マスターデバイス |
| `target` | トランザクション応答側 | スレーブデバイス |
| `monitor` | 観測専用 | 検証用 |

### ビューの定義

```rust
interface Handshake {
    valid: bit,
    ready: bit,
    data:  bit[8],

    // initiatorはvalidとdataを駆動
    view initiator {
        out: valid, data,
        in:  ready
    }

    // targetはreadyを駆動
    view target {
        in:  valid, data,
        out: ready
    }

    // monitorは全信号を観測
    view monitor {
        in: valid, ready, data
    }
}
```

---

## 7.3 インターフェースの使用

### ポート宣言

```rust
mod Producer(
    in  clk: clock,
    in  rst: reset,
    initiator out_if: Handshake,  // initiatorビューで接続
) {
    comb {
        out_if.valid = valid_signal;
        out_if.data = output_data;
    }
}

mod Consumer(
    in  clk: clock,
    in  rst: reset,
    target in_if: Handshake,  // targetビューで接続
) {
    comb {
        in_if.ready = ready_signal;
    }
}
```

### 接続

```rust
mod Top(
    in clk: clock,
    in rst: reset,
) {
    // インターフェース信号
    let bus: Handshake;

    // モジュール接続
    inst producer = Producer {
        clk: clk,
        rst: rst,
        out_if: bus
    };

    inst consumer = Consumer {
        clk: clk,
        rst: rst,
        in_if: bus
    };
}
```

---

## 7.4 パラメータ付きインターフェース

```rust
interface AxiLite[AddrWidth: uint = 32, DataWidth: uint = 32] {
    awaddr:  bit[AddrWidth],
    awvalid: bit,
    awready: bit,
    wdata:   bit[DataWidth],
    wvalid:  bit,
    wready:  bit,
    // ...

    view initiator {
        out: awaddr, awvalid, wdata, wvalid,
        in:  awready, wready
    }

    view target {
        in:  awaddr, awvalid, wdata, wvalid,
        out: awready, wready
    }
}
```

---

## 7.5 接続規則

### 有効な接続

| 接続パターン | 有効性 |
|--------------|--------|
| initiator ↔ target | 有効 |
| monitor ↔ any | 有効 |

### エラーになる接続

| 接続パターン | 結果 |
|--------------|------|
| initiator ↔ initiator | エラー（駆動競合） |
| target ↔ target | エラー（駆動なし） |

---

## 練習：UARTインターフェース設計

UART通信用のインターフェースを定義してください。

```rust
/// UARTインターフェース
interface Uart {
    // ここに信号とビューを定義
}
```

<details>
<summary>解答例</summary>

```rust
interface Uart {
    tx: bit,    // 送信データ
    rx: bit,    // 受信データ

    view initiator {
        out: tx,
        in:  rx
    }

    view target {
        in:  tx,
        out: rx
    }
}
```

</details>

---

## まとめ

- インターフェースは信号をグループ化
- ビューで使用側の視点を定義
- `initiator` と `target` のペアで接続
- パラメータ化で再利用性向上

---

## 参考リンク

- [IRIS言語仕様書 第8章 インターフェース](../../../spec/08_interface.md)