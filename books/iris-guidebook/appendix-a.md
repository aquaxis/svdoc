# 付録A クイックリファレンス

## A.1 モジュール定義

### 基本構文

```rust
// モジュール宣言
mod ModuleName[Param: uint = Default] {
    // ポート宣言
    in  clk: clock,
    in  rst: reset,
    in  input_signal: bit[Width],
    out output_signal: bit[Width],

    // 内部信号宣言
    let internal_signal: bit[Width];
    var register_signal: bit[Width] = 0;

    // 組み合わせ論理
    comb {
        output_signal = internal_signal;
    }

    // 順序論理
    sync(clk.posedge, rst.async) {
        // ...
    }
}
```

### パラメータ制約

```rust
mod Counter[Width: uint = 8]
    where Width >= 1, Width <= 32
{
    // ...
}
```

---

## A.2 型一覧

### プリミティブ型

| 型 | 説明 | 例 |
|----|------|-----|
| `bit` | 1ビット信号 | `let x: bit;` |
| `bit[N]` | Nビット幅信号 | `let data: bit[8];` |
| `bool` | 論理型 | `let flag: bool;` |
| `clock` | クロック型 | `in clk: clock;` |
| `reset` | リセット型 | `in rst: reset;` |
| `iN` | 符号付き整数（Nビット） | `let val: i8;` |
| `uN` | 符号なし整数（Nビット） | `let val: u8;` |
| `int` | 符号付き整数（パラメータ用） | `const N: int = 8;` |
| `uint` | 符号なし整数（パラメータ用） | `const N: uint = 8;` |

### 複合型

```rust
// 列挙型
enum State {
    Idle,
    Running,
    Done
}

// 構造体
struct Packet {
    valid: bit,
    data: bit[32],
    last: bit
}

// ユニオン
union Data {
    word: bit[32],
    bytes: bit[8][4]
}
```

---

## A.3 信号宣言

| 宣言 | 用途 | 合成結果 |
|------|------|----------|
| `let x: bit[8];` | 組み合わせ信号 | Wire |
| `let x = expr;` | 直接代入（組み合わせ） | Wire |
| `var x: bit[8] = 0;` | 順序回路信号（推奨） | Flip-flop |
| `let mut x: bit[8] = 0;` | 順序回路信号 | Flip-flop |
| `mem x: bit[8][256];` | メモリ宣言 | RAM/ROM |
| `const WIDTH: uint = 8;` | 定数 | Parameter |

---

## A.4 論理ブロック

### 組み合わせ論理（comb）

```rust
comb {
    // デフォルト値（オプション）
    default output = 0;

    // 条件分岐
    if condition {
        output = a;
    } else {
        output = b;
    }

    // パターンマッチ
    result = match sel {
        2'b00 => in0,
        2'b01 => in1,
        2'b10 => in2,
        _ => in3,
    };
}
```

### 順序論理（sync）

```rust
// 基本形
sync(clk.posedge) {
    reg = next_value;
}

// リセット付き
sync(clk.posedge, rst.async) {
    // rstがアサート時は初期値に戻る
    counter = counter + 1;
}

// 同期リセット
sync(clk.posedge, rst.sync) {
    if rst {
        counter = 0;
    } else {
        counter = counter + 1;
    }
}
```

### FSM

```rust
fsm Controller(clk.posedge, rst.async) {
    state enum { Idle, Run, Done }
    initial Idle;

    transitions {
        Idle => {
            when start { goto Run; }
        }
        Run => {
            when complete { goto Done; }
        }
        Done => {
            goto Idle;
        }
    }
}
```

---

## A.5 演算子

### 優先順位（高い順）

| 優先度 | 演算子 | 説明 |
|--------|--------|------|
| 1 | `()` `[]` `.` `::` | グループ化、添字、メンバ、スコープ |
| 2 | `~` `!` | ビットNOT、論理NOT |
| 3 | `*` `/` `%` | 乗算、除算、剰余 |
| 4 | `+` `-` | 加算、減算 |
| 5 | `<<` `>>` `>>>` | シフト |
| 6 | `<` `<=` `>` `>=` | 比較 |
| 7 | `==` `!=` | 等価 |
| 8 | `&` | ビットAND |
| 9 | `^` `~^` | ビットXOR、XNOR |
| 10 | `\|` | ビットOR |
| 11 | `&&` | 論理AND |
| 12 | `\|\|` | 論理OR |
| 13 | `?:` | 三項条件 |
| 14 | `=` | 代入 |

### ビット操作

```rust
// ビット選択
let bit_val = data[3];       // 1ビット選択

// スライス
let slice = data[7:0];       // 8ビットスライス

// 連結
let concat = {a, b, c};      // 信号の連結

// レプリケーション
let repeat = {4{bit_val}};   // 4回繰り返し

// ゼロ拡張
let extended = data.zero_extend[16]();

// 符号拡張
let signed_ext = data.sign_extend[16]();

// 切り捨て
let truncated = data.truncate[8]();
```

---

## A.6 リテラル

| 種類 | 構文 | 例 |
|------|------|-----|
| 2進数 | `N'b値` | `8'b1010_1100` |
| 8進数 | `N'o値` | `8'o254` |
| 10進数 | `N'd値` | `32'd123456` |
| 16進数 | `N'h値` | `16'hABCD` |
| 不定値 | `x` | `8'bxxxx_xxxx` |
| ハイインピーダンス | `z` | `8'bzzzz_zzzz` |
| 文字列 | `"..."` | `"Hello"` |
| 配列 | `[要素; 数]` | `[0; 16]` |

---

## A.7 インターフェース

```rust
// インターフェース定義
interface Bus[Width: uint = 32] {
    addr: bit[Width],
    data: bit[Width],
    valid: bit,
    ready: bit,

    view initiator {
        out: addr, valid,
        in: data, ready
    }

    view target {
        in: addr, valid,
        out: data, ready
    }
}

// 使用例
mod Master {
    out bus: Bus.initiator
}

mod Slave {
    in bus: Bus.target
}
```

---

## A.8 メモリ

```rust
// RAM宣言
mem ram: bit[32][1024];  // 32ビットx1024エントリ

// RAMアクセス
sync(clk.posedge) {
    // 書き込み
    if write_en {
        ram[addr] = wdata;
    }
}

comb {
    // 読み出し
    rdata = ram[addr];
}

// ROM宣言
#[synthesis(rom)]
mem rom: bit[8][256] = [
    8'h00, 8'h01, 8'h02, /* ... */
];

// アトリビュート
#[synthesis(ram_style = "block")]
mem large_ram: bit[64][8192];

#[synthesis(ram_style = "distributed")]
mem small_ram: bit[32][32];
```

---

## A.9 テスト・検証

```rust
#[test]
test counter_test() {
    // DUTインスタンス化
    let dut = Counter[Width: 8].create();

    // クロック生成
    let clk = Clock.new(period: 10.ns);
    dut.clk = clk;

    // リセット
    dut.rst.assert();
    await clk.cycles(5);
    dut.rst.deassert();

    // 検証
    assert dut.count == 0;

    // テスト刺激
    dut.enable.set(1);
    await clk.cycles(10);
    assert dut.count.value() == 10;
}

// テストアトリビュート
#[test]
#[timeout(100.us)]
test long_test() { /* ... */ }

#[test]
#[should_fail]
test error_case() { /* ... */ }
```

---

## A.10 アトリビュート一覧

### 合成制御

| アトリビュート | 説明 |
|---------------|------|
| `#[synthesis(ram_style = "block")]` | ブロックRAM使用 |
| `#[synthesis(ram_style = "distributed")]` | 分散RAM使用 |
| `#[synthesis(rom)]` | ROMとして推論 |
| `#[synthesis(use_dsp)]` | DSPブロック使用 |

### デバッグ

| アトリビュート | 説明 |
|---------------|------|
| `#[debug]` | デバッグ信号としてマーク |
| `#[keep]` | 最適化で削除されないように保持 |
| `#[mark_debug]` | ILA/VIO用デバッグマーク |

### 警告制御

| アトリビュート | 説明 |
|---------------|------|
| `#[allow(W0001)]` | 特定警告を抑制 |
| `#![allow(W0001)]` | ファイル全体で警告抑制 |
| `#![deny(warnings)]` | 全警告をエラーに |

---

## A.11 予約語一覧（55語）

### モジュール構造（11語）
```
mod     extern  inst    in      out     inout
const   type    import  export  pub
```

### 制御構造（8語）
```
if      else    match   for     while
break   continue return
```

### 型関連（13語）
```
bit     int     uint    bool    enum
struct  union   clock   reset   let
var     mut     mem
```

### 論理ブロック（9語）
```
comb    sync    fsm     state   when
goto    initial transitions default
```

### 検証（8語）
```
test    assert  expect  cover   assume
constraint await  seq
```

### インターフェース（4語）
```
interface   initiator  target   view
```

### その他（2語）
```
where   fn
```

---

## A.12 よく使うコードスニペット

### カウンタ

```rust
mod Counter[Width: uint = 8] {
    in  clk: clock,
    in  rst: reset,
    in  en: bit,
    out count: bit[Width],

    var counter: bit[Width] = 0;

    sync(clk.posedge, rst.async) {
        if en {
            counter = counter + 1;
        }
    }

    comb {
        count = counter;
    }
}
```

### パルス検出

```rust
mod PulseDetector(
    in  clk: clock,
    in  rst: reset,
    in  signal: bit,
    out pulse: bit,
) {
    var delay: bit = 0;

    sync(clk.posedge, rst.async) {
        delay = signal;
    }

    comb {
        pulse = signal && !delay;
    }
}
```

### パラメータ化MUX

```rust
mod Mux[Width: uint = 8, Sel: uint = 2] {
    in  sel: bit[Sel],
    in  inputs: bit[Width][1 << Sel],
    out out: bit[Width],

    comb {
        out = inputs[sel];
    }
}
```

---

## 参考リンク

- [IRIS言語仕様書 第2章 字句構造](../../../spec/02_lexical_structure.md)
- [IRIS言語仕様書 第16章 文法定義](../../../spec/16_grammar.md)