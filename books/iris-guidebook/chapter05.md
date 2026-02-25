---
title: "第5章 モジュールの構築"
---

---
title: "第5章 モジュールの構築"
---

# 第5章 モジュールの構築

## 本章のゴール

- モジュールをインスタンス化できる
- 階層構造を構築できる
- パラメータを使用できる

---

## 5.1 モジュールのインスタンス化

作成したモジュールを他のモジュール内で使用するには、`inst` キーワードを使います。

### 基本構文

```rust
inst インスタンス名 = モジュール名 {
    ポート名: 接続信号,
    ...
};
```

### 基本例

```rust
mod Top(
    in  clk: clock,
    in  rst: reset,
    in  btn: bit,
    out led: bit[8],
) {
    // Counterモジュールをインスタンス化
    inst counter = Counter {
        clk: clk,
        rst: rst,
        enable: btn,
        count: led
    };
}
```

### ポート接続

```rust
inst counter = Counter {
    clk: sys_clk,          // 入力ポート
    rst: sys_rst,
    enable: button,
    count: led,            // 出力ポート
    overflow: _            // '_' で未使用を明示
};
```

> **ポイント**: `_` を使うと、未使用のポートを明示的に無視できます。

---

## 5.2 階層設計

モジュールを入れ子にして階層構造を作成できます。

### 例：2段カウンタ

```rust
/// 8ビットカウンタ（再利用）
mod Counter8(
    in  clk: clock,
    in  rst: reset,
    in  enable: bit,
    out count: bit[8],
) {
    var counter: bit[8] = 0;

    sync(clk.posedge, rst.async) {
        if enable {
            counter = counter + 1;
        }
    }

    comb {
        count = counter;
    }
}

/// 16ビットカウンタ（2つの8ビットカウンタで構成）
mod Counter16(
    in  clk: clock,
    in  rst: reset,
    in  enable: bit,
    out count: bit[16],
) {
    let low_overflow: bit;

    // 下位8ビット
    inst low = Counter8 {
        clk: clk,
        rst: rst,
        enable: enable,
        count: count[7:0]
    };

    // 上位8ビット（下位がオーバーフローした時だけカウント）
    inst high = Counter8 {
        clk: clk,
        rst: rst,
        enable: low_overflow,
        count: count[15:8]
    };

    // オーバーフロー検出
    comb {
        low_overflow = enable && (count[7:0] == 8'hFF);
    }
}
```

---

## 5.3 パラメータ化

モジュールにパラメータを持たせて、再利用性を高めます。

### パラメータ化カウンタ

```rust
/// パラメータ化カウンタ
mod Counter[Width: uint = 8]  // デフォルト8ビット
where
    Width >= 1,               // 制約条件
    Width <= 32
(
    in  clk: clock,
    in  rst: reset,
    in  enable: bit,
    out count: bit[Width],    // Widthビット幅
) {
    var counter: bit[Width] = 0;

    sync(clk.posedge, rst.async) {
        if enable {
            counter = counter + 1;
        }
    }

    comb {
        count = counter;
    }
}
```

### パラメータの指定

```rust
mod Top(
    in  clk: clock,
    in  rst: reset,
    out count8: bit[8],
    out count16: bit[16],
) {
    // デフォルトパラメータ使用
    inst cnt8 = Counter {
        clk: clk,
        rst: rst,
        enable: 1'b1,
        count: count8
    };

    // パラメータ指定
    inst cnt16 = Counter[Width: 16] {
        clk: clk,
        rst: rst,
        enable: 1'b1,
        count: count16
    };
}
```

### 制約条件

`where` 句でパラメータの制約を指定できます：

```rust
mod Memory[DataWidth: uint, Depth: uint]
where
    DataWidth >= 8,
    DataWidth <= 256,
    Depth > 0,
    Depth <= 65536
{
    // ...
}
```

---

## 5.4 配列インスタンス

同じモジュールを複数インスタンス化できます。

```rust
mod MultiCounter(
    in  clk: clock,
    in  rst: reset,
    in  enables: bit[4],
    out counts: bit[8][4],
) {
    // 4つのカウンタをインスタンス化
    inst counters[4] = Counter[Width: 8] {
        clk: clk,
        rst: rst,
        enable: enables[..],      // 配列展開
        count: counts[..]         // 配列展開
    };
}
```

---

## 5.5 外部モジュール連携

既存のSystemVerilogモジュールを使用できます。

### 外部モジュール宣言

```rust
// 既存のVerilogモジュールを宣言
extern mod legacy_uart(
    in  clk: clock,
    in  rst_n: reset(active_low: true),
    in  tx_data: bit[8],
    in  tx_valid: bit,
    out tx_ready: bit,
    out tx: bit,
);
```

### 使用例

```rust
mod Top(
    in clk: clock,
    in rst: reset,
) {
    inst uart0 = legacy_uart {
        clk: clk,
        rst_n: ~rst,      // 極性変換
        tx_data: data,
        tx_valid: valid,
        tx_ready: ready,
        tx: tx_out
    };
}
```

---

## 練習：パラメータ化カウンタ

パラメータ化されたカウンタを使用して、8ビットと16ビットのカウンタを作成してください。

```rust
mod Top(
    in  clk: clock,
    in  rst: reset,
    in  enable: bit,
    out count8: bit[8],
    out count16: bit[16],
) {
    // Counterモジュールをインスタンス化
    // ここにコードを記述
}
```

<details>
<summary>解答例</summary>

```rust
mod Top(
    in  clk: clock,
    in  rst: reset,
    in  enable: bit,
    out count8: bit[8],
    out count16: bit[16],
) {
    // 8ビットカウンタ（デフォルト）
    inst cnt8 = Counter {
        clk: clk,
        rst: rst,
        enable: enable,
        count: count8
    };

    // 16ビットカウンタ
    inst cnt16 = Counter[Width: 16] {
        clk: clk,
        rst: rst,
        enable: enable,
        count: count16
    };
}
```

</details>

---

## まとめ

- モジュールは `inst` でインスタンス化
- ポートは名前で接続
- 階層構造で複雑な設計を管理
- パラメータで再利用性を向上
- `extern mod` で外部モジュールと連携

---

## 参考リンク

- [IRIS言語仕様書 第4章 モジュール定義](../../../spec/04_module_definition.md)