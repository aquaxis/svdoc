---
title: "第13章 SystemVerilogからの移行"
---

---
title: "第13章 SystemVerilogからの移行"
---

# 第13章 SystemVerilogからの移行

## 本章のゴール

- SystemVerilogコードをIRISに変換できる
- 移行時の注意点を理解する

---

## 13.1 モジュール宣言の変換

### SystemVerilog

```systemverilog
module Counter #(
    parameter WIDTH = 8
) (
    input  logic clk,
    input  logic rst_n,
    input  logic en,
    output logic [WIDTH-1:0] count
);
```

### IRIS

```rust
mod Counter[Width: uint = 8] {
    in  clk: clock,
    in  rst_n: reset(active_low: true),
    in  en: bit,
    out count: bit[Width],
}
```

---

## 13.2 データ型の対応

| SystemVerilog | IRIS |
|---------------|------|
| `logic [N-1:0]` | `bit[N]` |
| `reg [N-1:0]` | `var x: bit[N] = 0` |
| `wire [N-1:0]` | `let x: bit[N]` |
| `integer` | `i32` |
| `logic signed [N-1:0]` | `iN` |

---

## 13.3 組み合わせ論理の変換

### SystemVerilog

```systemverilog
always_comb begin
    case (sel)
        2'b00: out = in0;
        2'b01: out = in1;
        2'b10: out = in2;
        default: out = in3;
    endcase
end
```

### IRIS

```rust
comb {
    out = match sel {
        2'b00 => in0,
        2'b01 => in1,
        2'b10 => in2,
        _ => in3,
    };
}
```

---

## 13.4 順序論理の変換

### SystemVerilog

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        count <= '0;
    else if (en)
        count <= count + 1;
end
```

### IRIS

```rust
var count: bit[8] = 0;  // リセット値

sync(clk.posedge, rst_n.async) {
    if en {
        count = count + 1;
    }
}
```

---

## 13.5 FSMの変換

### SystemVerilog

```systemverilog
typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
state_t state, next_state;

always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) state <= IDLE;
    else state <= next_state;

always_comb begin
    next_state = state;
    case (state)
        IDLE: if (start) next_state = RUN;
        RUN:  if (complete) next_state = DONE;
        DONE: next_state = IDLE;
    endcase
end
```

### IRIS

```rust
fsm Controller(clk.posedge, rst_n.async) {
    state enum { Idle, Run, Done }

    transitions {
        Idle => { when start { goto Run; } }
        Run  => { when complete { goto Done; } }
        Done => { goto Idle; }
    }
}
```

---

## 13.6 移行チェックリスト

- [ ] モジュール宣言を `mod` に変換
- [ ] ポート宣言を `in`/`out` に変換
- [ ] データ型を `bit[N]` 形式に変換
- [ ] `always_comb` を `comb` ブロックに変換
- [ ] `always_ff` を `sync` ブロックに変換
- [ ] 代入演算子を `=` に統一
- [ ] `begin/end` を `{}` に変換
- [ ] `case` 文を `match` 式に変換

---

## まとめ

- モジュール宣言は `mod` キーワードに変換
- 型は `bit[N]` 形式に統一
- 代入演算子は `=` に統一
- FSMは `fsm` ブロックで簡潔に記述

---

## 参考リンク

- [IRIS言語仕様書 第15章 移行ガイド](../../../spec/15_migration_guide.md)