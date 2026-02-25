# 第4章 順序論理

## 本章のゴール

- `sync`ブロックを理解する
- クロックとリセットを扱える
- レジスタを設計できる

---

## 4.1 syncブロックの基本

順序論理は、クロック信号に同期して状態を更新する回路です。

### 基本構文

```rust
sync(クロック指定, リセット指定) {
    // 順序回路の記述
}
```

### 基本例

```rust
// クロック立ち上がりで動作
sync(clk.posedge) {
    q = d;
}

// クロック立ち下がりで動作
sync(clk.negedge) {
    q = d;
}
```

---

## 4.2 var宣言

順序回路用の信号は `var` で宣言します。

```rust
var counter: bit[8] = 0;  // 初期値 = リセット値
```

### 宣言と初期値

| 宣言 | リセット値 |
|------|-----------|
| `var x: bit[8];` | なし（未定義） |
| `var x: bit[8] = 0;` | 0 |
| `var x: bit[8] = 8'hFF;` | 0xFF |

> **重要**: `var` は `sync` または `fsm` ブロック内でのみ使用可能です。

---

## 4.3 リセット

### 同期リセット

クロックエッジでリセットを評価します。

```rust
var count: bit[8] = 0;

sync(clk.posedge, rst.sync) {
    if enable {
        count = count + 1;
    }
}
```

### 非同期リセット

クロックに依存せず即座にリセットします。

```rust
var count: bit[8] = 0;

sync(clk.posedge, rst.async) {
    if enable {
        count = count + 1;
    }
    // リセット時は宣言時の初期値（0）に戻る
}
```

### リセット極性

```rust
// Active High（デフォルト）
in rst: reset,

// Active Low
in rst_n: reset(active_low: true),
```

---

## 4.4 代入の統一

IRISでは、代入演算子が `=` に統一されています。

### SystemVerilogとの比較

| SystemVerilog | IRIS |
|---------------|------|
| `q <= d;`（ノンブロッキング） | `q = d;` |
| `q = d;`（ブロッキング） | `q = d;` |

IRISでは、`sync` ブロック内の代入は自動的にレジスタ更新として扱われます。

---

## 4.5 暗黙の保持

`sync` ブロックでは、条件分岐で代入されなかった信号は**自動的に保持**されます。

```rust
sync(clk.posedge, rst.async) {
    if enable {
        count = count + 1;
    }
    // enable=0の場合、countは保持される
}
```

これは `comb` ブロックとは異なる動作です（`comb` では完全割り当てが必須）。

---

## 4.6 実践：カウンタ設計

### 基本カウンタ

```rust
/// 基本カウンタ
mod Counter(
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
```

### ロード機能付きカウンタ

```rust
/// ロード機能付きカウンタ
mod LoadableCounter(
    in  clk: clock,
    in  rst: reset,
    in  enable: bit,
    in  load: bit,
    in  load_value: bit[8],
    out count: bit[8],
    out overflow: bit,
) {
    var counter: bit[8] = 0;

    sync(clk.posedge, rst.async) {
        if load {
            counter = load_value;
        } else if enable {
            counter = counter + 1;
        }
    }

    comb {
        count = counter;
        overflow = enable && (counter == 8'hFF);
    }
}
```

---

## 4.7 クロックドメイン

複数のクロックを使用する場合、ドメインを指定できます。

```rust
// ドメインA
sync(clk_a.posedge) @domain_a {
    reg_a = data_a;
}

// ドメインB
sync(clk_b.posedge) @domain_b {
    reg_b = data_b;
}
```

### CDC（クロックドメイン交差）

異なるドメイン間の信号転送には注意が必要です。

```rust
// 2段FFシンクロナイザ
sync(clk_b.posedge) @domain_b {
    reg_b = sync_ff(async_signal, stages: 2);
}
```

---

## 練習：シフトレジスタ

8ビットシフトレジスタを作成してください。

```rust
/// シフトレジスタ
mod ShiftRegister(
    in  clk: clock,
    in  rst: reset,
    in  shift: bit,
    in  din: bit,
    out dout: bit[8],
) {
    // ここにコードを記述
}
```

<details>
<summary>解答例</summary>

```rust
mod ShiftRegister(
    in  clk: clock,
    in  rst: reset,
    in  shift: bit,
    in  din: bit,
    out dout: bit[8],
) {
    var reg: bit[8] = 0;

    sync(clk.posedge, rst.async) {
        if shift {
            reg = {reg[6:0], din};  // 左シフト
        }
    }

    comb {
        dout = reg;
    }
}
```

</details>

---

## まとめ

- 順序論理は `sync` ブロックで記述
- 信号は `var` で宣言（初期値がリセット値）
- 代入演算子は `=` に統一
- 暗黙の保持により条件分岐が簡潔に
- CDCにはシンクロナイザを使用

---

## 参考リンク

- [IRIS言語仕様書 第6章 順序論理](../../../spec/06_sequential_logic.md)