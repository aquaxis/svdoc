---
title: "第8章 パラメータ化とジェネリクス"
---

---
title: "第8章 パラメータ化とジェネリクス"
---

# 第8章 パラメータ化とジェネリクス

## 本章のゴール

- ジェネリクスを深く理解する
- 再利用可能なモジュールを設計できる
- 制約条件を使用できる

---

## 8.1 ジェネリクスの基本

モジュールにパラメータを持たせることで、再利用性を高めます。

### 基本構文

```rust
mod ModuleName[パラメータ名: 型 = デフォルト値]
where
    制約条件
(
    ポート宣言
) {
    モジュール本体
}
```

### 基本例

```rust
mod Counter[Width: uint = 8]
where
    Width >= 1,
    Width <= 32
(
    in  clk: clock,
    in  rst: reset,
    in  enable: bit,
    out count: bit[Width],
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

---

## 8.2 パラメータの種類

### 型パラメータ

```rust
mod Fifo[T, Depth: uint = 16]
where
    Depth > 0,
    Depth.is_power_of_two()
{
    in  clk: clock,
    in  rst: reset,
    in  push: bit,
    in  pop: bit,
    in  din: T,
    out dout: T,
    // ...
}
```

### 複数パラメータ

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

## 8.3 制約条件

`where` 句でパラメータの有効範囲を指定します。

### 比較演算子

```rust
where
    Width >= 1,        // 最小値
    Width <= 32,       // 最大値
    Depth > 0,         // 正の値
    Depth != 0         // ゼロ以外
```

### 組み込み関数

| 関数 | 説明 |
|------|------|
| `$clog2(N)` | 天井log2 |
| `$bits(T)` | 型のビット幅 |
| `.is_power_of_two()` | 2の累乗かどうか |

```rust
mod Fifo[Depth: uint]
where
    Depth.is_power_of_two()  // 2の累乗のみ
{
    let ptr_width: uint = $clog2(Depth);
    // ...
}
```

---

## 8.4 パラメータの指定

### デフォルト値の使用

```rust
// デフォルトパラメータ（Width = 8）
inst cnt8 = Counter {
    clk: clk,
    rst: rst,
    enable: btn,
    count: led
};
```

### 明示的な指定

```rust
// パラメータ指定
inst cnt16 = Counter[Width: 16] {
    clk: clk,
    rst: rst,
    enable: btn,
    count: led
};

inst cnt32 = Counter[Width: 32] {
    clk: clk,
    rst: rst,
    enable: btn,
    count: led
};
```

---

## 8.5 デザインパターン

### パラメータ化FIFO

```rust
mod SyncFifo[Width: uint = 8, Depth: uint = 16]
where
    Depth.is_power_of_two()
(
    in  clk: clock,
    in  rst: reset,
    in  push: bit,
    in  pop: bit,
    in  din: bit[Width],
    out dout: bit[Width],
    out full: bit,
    out empty: bit,
) {
    const ADDR_WIDTH: uint = $clog2(Depth);

    mem buffer: bit[Width][Depth];
    var wr_ptr: bit[ADDR_WIDTH] = 0;
    var rd_ptr: bit[ADDR_WIDTH] = 0;
    var count: bit[ADDR_WIDTH + 1] = 0;

    sync(clk.posedge, rst.async) {
        // 書き込み
        if push && !full {
            buffer[wr_ptr] = din;
            wr_ptr = wr_ptr + 1;
        }

        // 読み出し
        if pop && !empty {
            rd_ptr = rd_ptr + 1;
        }

        // カウント更新
        if push && !pop && !full {
            count = count + 1;
        } else if !push && pop && !empty {
            count = count - 1;
        }
    }

    comb {
        dout = buffer[rd_ptr];
        full = (count == Depth);
        empty = (count == 0);
    }
}
```

---

## 練習：パラメータ化FIFO

指定された幅と深さのFIFOを作成してください。

```rust
/// パラメータ化FIFO
mod MyFifo[Width: uint = 8, Depth: uint = 16](
    in  clk: clock,
    in  rst: reset,
    in  push: bit,
    in  pop: bit,
    in  din: bit[Width],
    out dout: bit[Width],
    out full: bit,
    out empty: bit,
) {
    // ここにコードを記述
}
```

<details>
<summary>解答例</summary>

上記の `SyncFifo` 例を参照してください。

</details>

---

## まとめ

- ジェネリクスでモジュールの再利用性を向上
- `where` 句でパラメータの制約を指定
- 型パラメータと値パラメータの両方をサポート
- 組み込み関数で柔軟な設計が可能

---

## 参考リンク

- [IRIS言語仕様書 第3章 型システム（ジェネリクス）](../../../spec/03_type_system.md)
- [IRIS言語仕様書 第4章 モジュール定義](../../../spec/04_module_definition.md)