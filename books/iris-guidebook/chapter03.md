# 第3章 組み合わせ論理

## 本章のゴール

- `comb`ブロックを深く理解する
- 条件分岐を記述できる
- 意図しないラッチを防ぐ

---

## 3.1 combブロックの基本

組み合わせ論理は、入力から出力を即座に計算する回路です。

### let宣言とcombブロック

IRISでは2つの方法で組み合わせ論理を記述できます：

```rust
// 方法1: let宣言による直接代入（単純な場合）
let sum = a + b;

// 方法2: combブロック（複雑な場合）
comb {
    result = a + b;
}
```

### どちらを使うべきか

| 方法 | 適したケース |
|------|--------------|
| `let`直接代入 | 単純な式、1行で記述できる場合 |
| `comb`ブロック | 条件分岐がある、複数の代入がある場合 |

---

## 3.2 完全割り当てチェック

IRISでは、`comb`ブロック内のすべての信号が**すべての実行パスで値を持つこと**が保証されます。

### エラー例

```rust
// エラー: else節がない
comb {
    out = if sel {
        in0
    };  // コンパイルエラー: selがfalseの場合の値がない
}
```

### 正しい記述

```rust
// 正しい: 完全なif-else
comb {
    out = if sel {
        in0
    } else {
        in1
    };
}
```

> **重要**: これはSystemVerilogでよくある「意図しないラッチ生成」を防ぐ重要な機能です。

---

## 3.3 条件分岐

### if-else式

```rust
comb {
    result = if sel == 2'b00 {
        in0
    } else if sel == 2'b01 {
        in1
    } else {
        in2
    };
}
```

> **注意**: `else`は必須です。省略するとコンパイルエラーになります。

### match式

```rust
comb {
    result = match sel {
        2'b00 => in0,
        2'b01 => in1,
        2'b10 => in2,
        2'b11 => in3,
        // すべてのパターンを網羅必須
    };
}
```

### ワイルドカード

```rust
comb {
    result = match opcode {
        OpCode::Add => a + b,
        OpCode::Sub => a - b,
        _ => 32'h0,  // その他すべてのケース
    };
}
```

---

## 3.4 ビット操作

### ビット選択

```rust
let data: bit[8] = 8'b1010_0101;

let bit0 = data[0];      // 1（LSB）
let bit7 = data[7];      // 1（MSB）
```

### ビットスライス

```rust
let data: bit[16] = 16'hABCD;

let lower = data[7:0];   // 0xCD（下位8ビット）
let upper = data[15:8];  // 0xAB（上位8ビット）
```

### 連結

```rust
let high: bit[8] = 8'hAB;
let low: bit[8] = 8'hCD;

let combined: bit[16] = {high, low};  // 0xABCD
```

### レプリケーション

```rust
let zeros: bit[8] = {8{1'b0}};  // 8'b0000_0000
let ones: bit[8] = {8{1'b1}};   // 8'b1111_1111
```

---

## 3.5 よくある間違い

### Multi Drive（複数ドライバ）

同一信号に複数の場所から代入することはできません。

```rust
// エラー: resultへの複数ドライバ
comb {
    if sel { result = a; }
}

comb {
    if !sel { result = b; }  // コンパイルエラー
}
```

```rust
// 正しい: 単一のcombブロック
comb {
    result = if sel { a } else { b };
}
```

### 組み合わせループ

組み合わせ論理で循環依存があるとエラーになります。

```rust
// エラー: 組み合わせループ
comb {
    a = b + 1;
    b = a + 1;  // エラー: aに依存するbがaに代入される
}
```

---

## 練習：ALU設計

4つの演算ができるALUを作成してください。

```rust
/// 4機能ALU
mod Alu(
    in  a: bit[8],
    in  b: bit[8],
    in  op: bit[2],      // 00:加算, 01:減算, 10:AND, 11:OR
    out result: bit[8],
) {
    // ここにコードを記述
}
```

<details>
<summary>解答例</summary>

```rust
mod Alu(
    in  a: bit[8],
    in  b: bit[8],
    in  op: bit[2],
    out result: bit[8],
) {
    comb {
        result = match op {
            2'b00 => a + b,
            2'b01 => a - b,
            2'b10 => a & b,
            2'b11 => a | b,
        };
    }
}
```

</details>

---

## まとめ

- 組み合わせ論理は `let` または `comb` で記述
- 完全割り当てチェックでラッチ生成を防止
- 条件分岐は `if-else` または `match`
- Multi Driveは禁止
- 組み合わせループはエラー

---

## 参考リンク

- [IRIS言語仕様書 第5章 組み合わせ論理](../../../spec/05_combinational_logic.md)