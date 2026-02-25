---
title: "第6章 FSM（有限状態機械）"
---

---
title: "第6章 FSM（有限状態機械）"
---

# 第6章 FSM（有限状態機械）

## 本章のゴール

- `fsm`ブロックを理解する
- 状態遷移を記述できる
- エンコーディングを指定できる

---

## 6.1 FSMの基本

有限状態機械（FSM）は、状態と遷移によって動作を記述する設計パターンです。

### fsmブロックの構造

```rust
fsm StateMachineName(clk.posedge, rst.async) {
    // 1. 状態定義
    state enum {
        Idle,
        Running,
        Done
    }

    // 2. 初期状態
    initial: Idle

    // 3. 状態遷移
    transitions {
        Idle => {
            // 出力と遷移条件
        }
        Running => {
            // ...
        }
        Done => {
            // ...
        }
    }
}
```

---

## 6.2 状態遷移の記述

### 基本的な遷移

```rust
fsm Controller(clk.posedge, rst.async) {
    state enum {
        Idle,
        Active,
        Complete
    }

    initial: Idle

    transitions {
        Idle => {
            busy = 0;
            when start {
                goto Active;
            }
        }

        Active => {
            busy = 1;
            when done {
                goto Complete;
            }
        }

        Complete => {
            busy = 0;
            when ack {
                goto Idle;
            }
        }
    }
}
```

### 遷移の優先順位

```rust
transitions {
    Idle => {
        // 上から順に評価
        when error {
            goto Error;      // 最優先
        }
        when urgent {
            goto UrgentProc; // 2番目
        }
        when normal {
            goto NormalProc; // 3番目
        }
        // いずれも満たさない場合はIdleを維持
    }
}
```

---

## 6.3 状態エンコーディング

### エンコーディングの種類

| エンコーディング | 説明 | 用途 |
|------------------|------|------|
| `binary` | 2進エンコーディング | 状態数が多い場合 |
| `onehot` | ワンホットエンコーディング | 高速デコード（FPGA推奨） |
| `gray` | グレイコード | CDC用途 |

### 指定方法

```rust
fsm MyFSM(clk.posedge, rst.async) {
    state enum { A, B, C }
    initial: A
    transitions { ... }

    // エンコーディング指定
    output encoding: onehot
}
```

---

## 6.4 Moore型出力の簡略記法

状態に直接紐づく出力を簡潔に記述できます。

```rust
fsm Controller(clk.posedge, rst.async) {
    state enum {
        Idle   [busy = 0, done = 0],  // Moore出力
        Run    [busy = 1, done = 0],
        Done   [busy = 0, done = 1]
    }

    initial: Idle

    transitions {
        Idle => { when start { goto Run; } }
        Run  => { when complete { goto Done; } }
        Done => { when ack { goto Idle; } }
    }
}
```

---

## 6.5 タイマー付きFSM

```rust
fsm TrafficLight(clk.posedge, rst.async) {
    state enum { Red, Yellow, Green }
    initial: Red

    let timer: bit[8] = 0;

    transitions {
        Red => {
            red_light = 1;
            timer = timer + 1;
            when timer >= 100 {
                timer = 0;
                goto Green;
            }
        }

        Green => {
            green_light = 1;
            timer = timer + 1;
            when timer >= 80 {
                timer = 0;
                goto Yellow;
            }
        }

        Yellow => {
            yellow_light = 1;
            timer = timer + 1;
            when timer >= 20 {
                timer = 0;
                goto Red;
            }
        }
    }

    output encoding: onehot
}
```

---

## 練習：LEDコントローラーFSM

3状態のLED制御FSMを作成してください。

```rust
/// LED制御FSM
/// ボタンを押すと状態が遷移：
/// Idle → Active → Done → Idle
mod LedController(
    in  clk: clock,
    in  rst: reset,
    in  btn: bit,
    out led: bit[3],
) {
    // ここにコードを記述
}
```

<details>
<summary>解答例</summary>

```rust
mod LedController(
    in  clk: clock,
    in  rst: reset,
    in  btn: bit,
    out led: bit[3],
) {
    fsm Controller(clk.posedge, rst.async) {
        state enum {
            Idle   [led = 3'b001],
            Active [led = 3'b010],
            Done   [led = 3'b100]
        }

        initial: Idle

        transitions {
            Idle => {
                when btn { goto Active; }
            }
            Active => {
                when !btn { goto Done; }
            }
            Done => {
                when btn { goto Idle; }
            }
        }
    }
}
```

</details>

---

## まとめ

- FSMは `fsm` ブロックで記述
- 状態は `state enum` で定義
- 遷移は `when ... goto` で記述
- エンコーディングは用途に応じて選択
- Moore出力は `[...]` で簡潔に記述

---

## 参考リンク

- [IRIS言語仕様書 第7章 FSM](../../../spec/07_fsm.md)