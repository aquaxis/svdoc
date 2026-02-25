---
title: "第2章 型と演算子"
---

# 第2章 型と演算子

## 本章のゴール

- プリミティブ型を理解する
- 演算子を使用できる
- 型安全性の重要性を理解する

---

## 2.1 プリミティブ型

IRISでよく使う基本的な型を紹介します。

### ビット型

| 型 | ビット幅 | 説明 |
|----|----------|------|
| `bit` | 1 | 単一ビット（0または1） |
| `bit[N]` | N | Nビットベクトル |
| `bool` | 1 | ブール値（true/false） |

```rust
let single: bit;           // 1ビット
let byte_val: bit[8];      // 8ビット
let word_val: bit[32];     // 32ビット
let flag: bool;            // true または false
```

### 特殊信号型

| 型 | 説明 |
|----|------|
| `clock` | クロック信号 |
| `reset` | リセット信号 |

```rust
in clk: clock,              // クロック入力
in rst: reset,              // リセット入力（active high）
in rst_n: reset(active_low: true),  // active lowリセット
```

---

## 2.2 リテラル

IRISでは、2進数、8進数、10進数、16進数のリテラルを記述できます。

### 数値リテラルの形式

```
幅 ' 基数 値
```

| 基数 | 記号 | 例 |
|------|------|-----|
| 2進数 | `b` | `4'b1010` |
| 8進数 | `o` | `8'o377` |
| 10進数 | `d` | `8'd255` |
| 16進数 | `h` | `8'hFF` |

```rust
// 8ビット値の様々な表現
let a = 8'b1010_1010;    // 2進数（アンダースコアで区切り可）
let b = 8'd170;          // 10進数
let c = 8'hAA;           // 16進数
let d = 8'o252;          // 8進数

// 型推論
let x = 8'hFF;           // 型: bit[8]
let y = 16'hFFFF;        // 型: bit[16]
```

---

## 2.3 演算子

### 算術演算子

| 演算子 | 説明 | 例 |
|--------|------|-----|
| `+` | 加算 | `a + b` |
| `-` | 減算 | `a - b` |
| `*` | 乗算 | `a * b` |
| `/` | 除算 | `a / b` |
| `%` | 剰余 | `a % b` |

```rust
let a: bit[8] = 8'd100;
let b: bit[8] = 8'd50;

let sum = a + b;         // 150
let diff = a - b;        // 50
let prod = a * b;        // 5000（bit[16]）
```

> **注意**: 乗算の結果幅は `width(a) + width(b)` になります。

### ビット演算子

| 演算子 | 説明 | 例 |
|--------|------|-----|
| `~` | ビット反転 | `~a` |
| `&` | ビットAND | `a & b` |
| `\|` | ビットOR | `a \| b` |
| `^` | ビットXOR | `a ^ b` |

```rust
let a: bit[4] = 4'b1100;
let b: bit[4] = 4'b1010;

let not_a = ~a;          // 4'b0011
let and_ab = a & b;      // 4'b1000
let or_ab = a | b;       // 4'b1110
let xor_ab = a ^ b;      // 4'b0110
```

### シフト演算子

| 演算子 | 説明 | 例 |
|--------|------|-----|
| `<<` | 論理左シフト | `a << 2` |
| `>>` | 論理右シフト | `a >> 2` |
| `>>>` | 算術右シフト | `a >>> 2` |

```rust
let a: bit[8] = 8'b0000_1000;

let left = a << 2;       // 8'b0010_0000
let right = a >> 2;      // 8'b0000_0010
```

### 比較演算子

| 演算子 | 説明 | 結果型 |
|--------|------|--------|
| `==` | 等価 | `bool` |
| `!=` | 不等価 | `bool` |
| `<` | 未満 | `bool` |
| `<=` | 以下 | `bool` |
| `>` | より大きい | `bool` |
| `>=` | 以上 | `bool` |

```rust
let a: bit[8] = 8'd10;
let b: bit[8] = 8'd20;

let eq = (a == b);       // false
let lt = (a < b);        // true
let gt = (a > b);        // false
```

### 論理演算子

| 演算子 | 説明 | 例 |
|--------|------|-----|
| `!` | 論理NOT | `!a` |
| `&&` | 論理AND | `a && b` |
| `\|\|` | 論理OR | `a \|\| b` |

```rust
let valid: bit = 1'b1;
let ready: bit = 1'b0;

let can_proceed = valid && ready;  // false
let alert = !valid || !ready;      // true
```

---

## 2.4 型安全性

IRISでは**暗黙の型変換を禁止**しています。これにより、多くのバグをコンパイル時に検出できます。

### エラー例

```rust
// エラー: ビット幅が一致しない
let a: bit[16] = 8'hFF;  // コンパイルエラー

// エラー: 異なる型の代入
let b: bit[8] = 1'b1;    // コンパイルエラー
```

### 明示的な型変換

```rust
// ゼロ拡張
let a: bit[16] = (8'hFF).extend[16];  // 0x00FF

// 符号拡張
let b: bit[16] = (8'hFF).sign_extend[16];  // 0xFFFF（-1として解釈）

// 切り詰め
let c: bit[4] = (8'hFF).truncate[4];  // 0xF
```

### 型変換メソッド

| メソッド | 説明 |
|----------|------|
| `.extend[N]` | ゼロ拡張してNビットに |
| `.sign_extend[N]` | 符号拡張してNビットに |
| `.truncate[N]` | 上位を切り詰めてNビットに |
| `.signed()` | 符号付きとして解釈 |
| `.unsigned()` | 符号なしとして解釈 |

---

## 2.5 ビット選択とスライス

### 単一ビット選択

```rust
let data: bit[8] = 8'b1010_0101;

let bit0 = data[0];      // 1（LSB）
let bit7 = data[7];      // 1（MSB）
let bit_n = data[idx];   // 変数インデックス
```

### ビットスライス

```rust
let data: bit[32] = 32'hDEAD_BEEF;

// 固定範囲
let byte0 = data[7:0];     // 下位8ビット: 0xEF
let byte1 = data[15:8];    // 次の8ビット: 0xBE
let byte2 = data[23:16];   // 0xAD
let byte3 = data[31:24];   // 上位8ビット: 0xDE

// 動的スライス
let byte_n = data[byte_idx * 8 +: 8];
```

---

## 2.6 連結とレプリケーション

### 連結

```rust
let high: bit[8] = 8'hAB;
let low: bit[8] = 8'hCD;

let combined: bit[16] = {high, low};  // 0xABCD

// 複数要素
let word: bit[32] = {8'h11, 8'h22, 8'h33, 8'h44};
```

### レプリケーション

```rust
let zeros: bit[8] = {8{1'b0}};   // 8'b0000_0000
let ones: bit[8] = {8{1'b1}};    // 8'b1111_1111
let pattern = {4{2'b10}};        // 8'b10101010
```

---

## 練習：加算器とMUX

### 練習1：8ビット加算器

キャリー出力付きの8ビット加算器を作成してください。

```rust
/// 8ビット加算器
mod Adder8(
    in  a: bit[8],
    in  b: bit[8],
    out sum: bit[8],
    out carry: bit,
) {
    // ここにコードを記述
}
```

<details>
<summary>解答例</summary>

```rust
mod Adder8(
    in  a: bit[8],
    in  b: bit[8],
    out sum: bit[8],
    out carry: bit,
) {
    // 9ビットで計算してオーバーフローを検出
    let result = a.extend[9] + b.extend[9];

    comb {
        sum = result[7:0];
        carry = result[8];
    }
}
```

</details>

### 練習2：2入力MUX

選択信号で入力を切り替えるMUXを作成してください。

```rust
/// 2入力MUX
mod Mux2(
    in  sel: bit,
    in  d0: bit[8],
    in  d1: bit[8],
    out y: bit[8],
) {
    // ここにコードを記述
}
```

<details>
<summary>解答例</summary>

```rust
mod Mux2(
    in  sel: bit,
    in  d0: bit[8],
    in  d1: bit[8],
    out y: bit[8],
) {
    comb {
        y = if sel { d1 } else { d0 };
    }
}
```

</details>

---

## まとめ

- プリミティブ型：`bit`, `bit[N]`, `bool`, `clock`, `reset`
- リテラル：`幅'基数値` 形式
- 演算子：算術、ビット、比較、論理
- 型安全性：暗黙の型変換禁止
- 型変換：`.extend[]`, `.truncate[]` など

---

## 参考リンク

- [IRIS言語仕様書 第3章 型システム](../../../spec/03_type_system.md)
- [IRIS言語仕様書 第9章 演算子](../../../spec/09_operators.md)