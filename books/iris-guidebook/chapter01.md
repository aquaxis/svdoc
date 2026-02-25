---
title: "第1章 最初のモジュール"
---

# 第1章 最初のモジュール

## 本章のゴール

- モジュールの基本構文を理解する
- ポート宣言（入力/出力）を記述できる
- 組み合わせ論理の基礎を理解する

---

## 1.1 モジュールの構造

IRISでは、`mod`キーワードを使ってモジュールを定義します。

### 基本構文

```rust
mod モジュール名(
    ポート宣言
) {
    モジュール本体
}
```

### 最もシンプルなモジュール

何もしないモジュールを作ってみましょう。

```rust
/// 何もしないモジュール
mod EmptyModule() {
    // 空のモジュール
}
```

> **用語解説**: `///` で始まる行はドキュメンテーションコメントです。モジュールや関数の説明を記述します。

---

## 1.2 ポート宣言

モジュールと外部とのインターフェースを定義します。

### ポート方向

| キーワード | 説明 | 使用例 |
|------------|------|--------|
| `in` | 入力ポート | `in clk: clock` |
| `out` | 出力ポート | `out led: bit` |
| `inout` | 双方向ポート | `inout bus: bit[8]` |

### 基本的なポート宣言

```rust
mod LedSwitch(
    in  sw: bit,     // 1ビット入力
    out led: bit,    // 1ビット出力
) {
    // モジュール本体
}
```

### 型の基本

IRISでよく使う基本的な型：

| 型 | 説明 | 使用例 |
|----|------|--------|
| `bit` | 1ビット | `in enable: bit` |
| `bit[N]` | Nビット | `out count: bit[8]` |
| `clock` | クロック信号 | `in clk: clock` |
| `reset` | リセット信号 | `in rst: reset` |
| `bool` | ブール値 | `let flag: bool` |

---

## 1.3 組み合わせ論理の基礎

組み合わせ論理は、入力から出力を即座に計算する回路です。

### let宣言による直接代入

最もシンプルな方法は、`let`を使った直接代入です。

```rust
mod LedSwitch(
    in  sw: bit,
    out led: bit,
) {
    // スイッチの状態をそのままLEDに出力
    let led = sw;
}
```

### combブロック

複雑な論理を記述する場合は`comb`ブロックを使います。

```rust
mod AndGate(
    in  a: bit,
    in  b: bit,
    out y: bit,
) {
    comb {
        y = a & b;  // AND演算
    }
}
```

---

## 1.4 実践：LED制御モジュール

スイッチでLEDを制御するモジュールを作成します。

### ステップ1：単純な接続

スイッチの状態をそのままLEDに出力します。

```rust
/// スイッチでLED制御
mod LedSwitch(
    in  sw: bit,     // 入力スイッチ
    out led: bit,    // 出力LED
) {
    comb {
        led = sw;    // スイッチの状態をそのまま出力
    }
}
```

### ステップ2：NOTゲート

入力を反転して出力します。

```rust
/// NOTゲート
mod NotGate(
    in  a: bit,
    out y: bit,
) {
    comb {
        y = !a;      // 論理NOT
    }
}
```

### ステップ3：AND/ORゲート

複数入力の論理演算です。

```rust
/// 2入力ANDゲート
mod AndGate(
    in  a: bit,
    in  b: bit,
    out y: bit,
) {
    comb {
        y = a & b;
    }
}

/// 2入力ORゲート
mod OrGate(
    in  a: bit,
    in  b: bit,
    out y: bit,
) {
    comb {
        y = a | b;
    }
}
```

---

## 1.5 Multi Drive禁止

IRISでは、同一信号への複数箇所からの代入（Multi Drive）は禁止されています。

### エラー例

```rust
// エラー: resultへの複数ドライバ
mod MultiDriveError(
    in  sel: bit,
    in  a: bit[8],
    in  b: bit[8],
    out result: bit[8],
) {
    comb {
        if sel {
            result = a;  // ドライバ1
        }
    }

    comb {
        if !sel {
            result = b;  // ドライバ2 → コンパイルエラー
        }
    }
}
```

### 正しい記述

```rust
// 正しい: 単一のcombブロックで完結
mod SingleDriver(
    in  sel: bit,
    in  a: bit[8],
    in  b: bit[8],
    out result: bit[8],
) {
    comb {
        result = if sel { a } else { b };
    }
}
```

---

## 1.6 SystemVerilogとの対比

SystemVerilog経験者向けの対比表です。

| 機能 | SystemVerilog | IRIS |
|------|---------------|------|
| モジュール定義 | `module ... endmodule` | `mod ... { }` |
| 入力ポート | `input logic [7:0] data` | `in data: bit[8]` |
| 出力ポート | `output logic [7:0] data` | `out data: bit[8]` |
| 組み合わせ論理 | `assign y = a & b;` | `let y = a & b;` または `comb { y = a & b; }` |
| 括弧 | `begin ... end` | `{ ... }` |

---

## 練習問題

### 練習1：XORゲート

2入力XORゲートを作成してください。

```rust
/// XORゲート
mod XorGate(
    in  a: bit,
    in  b: bit,
    out y: bit,
) {
    // ここにコードを記述
}
```

<details>
<summary>解答例</summary>

```rust
/// XORゲート
mod XorGate(
    in  a: bit,
    in  b: bit,
    out y: bit,
) {
    comb {
        y = a ^ b;
    }
}
```

</details>

### 練習2：3入力ANDゲート

3入力ANDゲートを作成してください。

<details>
<summary>解答例</summary>

```rust
/// 3入力ANDゲート
mod And3Gate(
    in  a: bit,
    in  b: bit,
    in  c: bit,
    out y: bit,
) {
    comb {
        y = a & b & c;
    }
}
```

</details>

---

## まとめ

- モジュールは `mod` キーワードで定義
- ポートは `in` / `out` で宣言
- 組み合わせ論理は `let` または `comb` ブロックで記述
- Multi Drive（複数ドライバ）は禁止

---

## 参考リンク

- [IRIS言語仕様書 第4章 モジュール定義](../../../spec/04_module_definition.md)
- [IRIS言語仕様書 第5章 組み合わせ論理](../../../spec/05_combinational_logic.md)