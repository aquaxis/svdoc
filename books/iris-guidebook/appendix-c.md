# 付録C トラブルシューティング

IRIS開発中によく遭遇するエラーと解決方法をまとめています。

---

## C.1 エラーメッセージの読み方

IRISのエラーメッセージは以下の構造で表示されます：

```text
error[CODE]: エラーの概要
  --> ファイルパス:行番号:列番号
   |
行 | ソースコード
   |     ^^^^^^^^^ 問題の詳細
   |
   = help: 修正方法の提案
   = note: 追加情報
```

| 要素 | 説明 |
| ------ | ------ |
| `error` / `warning` | メッセージの種類 |
| `[CODE]` | エラーコード（ドキュメント検索用） |
| 概要 | エラーの簡潔な説明 |
| ファイルパス | 問題のあるファイル |
| 行番号:列番号 | 問題の位置 |
| `^^^^^` | 問題の箇所を示すマーカー |
| `help` | 修正方法の提案 |
| `note` | 追加の説明や背景情報 |

---

## C.2 よくあるエラーと解決方法

### 組み合わせ論理の不完全な代入

**エラーコード:** O0001

```
error[O0001]: incomplete signal assignment in combinational block
  --> src/alu.iris:42:5
   |
42 | comb {
43 |     if sel == 2'b00 {
44 |         out = in0;
45 |     }
   |     ^ 'out' is not assigned when sel != 2'b00
   |
   = help: add 'else' clause or use 'comb default(out = 0)'
   = note: incomplete assignments infer latches
```

**原因:** combブロック内ですべてのパスで信号に値が割り当てられていない。これによりラッチが推論される。

**解決方法:**

```rust
// 方法1: else句を追加
comb {
    if sel == 2'b00 {
        out = in0;
    } else {
        out = in1;  // 他のケースをカバー
    }
}

// 方法2: デフォルト値を設定
comb {
    default out = 0;  // デフォルト値
    if sel == 2'b00 {
        out = in0;
    }
}

// 方法3: match式で全ケースを網羅
comb {
    out = match sel {
        2'b00 => in0,
        2'b01 => in1,
        2'b10 => in2,
        _ => in3,      // デフォルトケース
    };
}
```

---

### varの使用場所エラー

**エラーコード:** O0002

```
error[O0002]: 'var' declaration used outside sync/fsm block
  --> src/counter.iris:8:5
   |
8  |     var counter: bit[8] = 0;
9  |     comb {
10 |         counter = counter + 1;
   |         ^^^^^^^ 'var' signal assigned in comb block
   |
   = help: use 'let' for combinational logic, or move to sync/fsm block
   = note: 'var' declarations are only allowed in sync or fsm blocks
```

**原因:** `var`で宣言した信号を`sync`/`fsm`ブロック外で使用している。`var`は順序回路専用。

**解決方法:**

```rust
// 組み合わせ論理の場合はletを使用
let counter_next: bit[8];  // OK

// 順序論理の場合はsyncブロック内で使用
var counter: bit[8] = 0;   // OK

sync(clk.posedge, rst.async) {
    counter = counter + 1;  // OK
}
```

---

### 型の不一致

**エラーコード:** O1001

```
error[O1001]: type mismatch
  --> src/counter.iris:15:12
   |
15 |     count = count + 1;
   |             ^^^^^^^^^ expected `bit[8]`, found `bit[9]`
   |
   = help: use explicit truncation: `(count + 1).truncate[8]()`
   = note: IRIS does not allow implicit narrowing conversions
```

**原因:** 右辺の式の型が左辺の型より広い。加算でビット幅が増えることを防ぐ。

**解決方法:**

```rust
// 方法1: 明示的な切り捨て
count = (count + 1).truncate[8]();

// 方法2: キャスト
count = (count + 1) as bit[8];

// 方法3: ゼロ拡張付きリサイズ
count = (count + 1).resize[8]();

// 方法4: オーバーフローを考慮した設計
var count: bit[8] = 0;
var overflow: bit = 0;

sync(clk.posedge, rst.async) {
    if count == 8'hFF {
        count = 0;
        overflow = 1;
    } else {
        count = count + 1;
    }
}
```

---

### 符号付き/符号なしの混在

**エラーコード:** O1002

```
error[O1002]: signed/unsigned mismatch in comparison
  --> src/calc.iris:23:8
   |
23 |     if signed_val > unsigned_val {
   |        ^^^^^^^^^^^^^^^^^^^^^^^^^ comparing `i8` with `u8`
   |
   = help: cast one operand: `signed_val > unsigned_val as i8`
```

**原因:** 符号付きと符号なしの値を直接比較している。意図しない結果になる可能性がある。

**解決方法:**

```rust
// 方法1: 符号なしにキャスト
if signed_val.as_unsigned() > unsigned_val {
    // ...
}

// 方法2: 符号付きにキャスト
if signed_val > unsigned_val.as_signed() {
    // ...
}

// 方法3: 明示的な型変換
if signed_val > (unsigned_val as i8) {
    // ...
}
```

---

### 組み合わせ回路ループ

**エラーコード:** O2001

```
error[O2001]: combinational loop detected
  --> src/logic.iris:10:5
   |
10 |     a = b & c;
11 |     b = a | d;
   |     ^^^^^^^^^ 'b' depends on 'a' which depends on 'b'
   |
   = help: break the loop by inserting a register
   = note: combinational loops cause simulation non-convergence
```

**原因:** 組み合わせ論理内で循環依存が発生している。シミュレーションが収束しない。

**解決方法:**

```rust
// 悪い例: 組み合わせループ
comb {
    a = b & c;
    b = a | d;  // b -> a -> b のループ
}

// 良い例: レジスタを挿入
var b_reg: bit = 0;

sync(clk.posedge, rst.async) {
    b_reg = b_next;
}

comb {
    a = b_reg & c;
    b_next = a | d;  // ループを断つ
}
```

---

### 複数ドライバエラー

**エラーコード:** O2003

```
error[O2003]: multiple drivers for signal
  --> src/mux.iris:15:9
   |
12 |     comb {
13 |         if sel { result = a; }
14 |     }
15 |     comb {
16 |         if !sel { result = b; }
   |                   ^^^^^^ 'result' is also driven at line 13
   |
   = help: combine into a single comb block with complete if-else
   = note: each signal must have exactly one driver
```

**原因:** 同一信号が複数のブロックから駆動されている。バス競合が発生する。

**解決方法:**

```rust
// 悪い例: 複数のcombブロック
comb {
    if sel { result = a; }
}
comb {
    if !sel { result = b; }  // エラー
}

// 良い例: 単一のcombブロック
comb {
    if sel {
        result = a;
    } else {
        result = b;
    }
}

// または三項演算子
comb {
    result = sel ? a : b;
}
```

---

### クロックドメイン交差の警告

**エラーコード:** O2005

```
warning[O2005]: clock domain crossing detected
  --> src/cdc.iris:18:14
   |
18 |     sync(clk_b.posedge) {
19 |         data_b = data_a;
   |                  ^^^^^^ 'data_a' is in clock domain 'clk_a'
   |
   = help: use synchronizer: `sync_ff(data_a, stages: 2)`
```

**原因:** 異なるクロックドメイン間で直接信号を渡している。メタステーブル状態になる可能性がある。

**解決方法:**

```rust
// 単一ビットの同期化
mod SyncBit(
    in  clk: clock,
    in  rst: reset,
    in  async_in: bit,
    out sync_out: bit,
) {
    var stage1: bit = 0;
    var stage2: bit = 0;

    sync(clk.posedge, rst.async) {
        stage1 = async_in;
        stage2 = stage1;
    }

    comb {
        sync_out = stage2;
    }
}

// データバスの同期化（FIFOを使用）
// 非同期FIFOまたはハンドシェイクを使用
```

---

### FSM到達不能状態

**エラーコード:** O3001

```
warning[O3001]: unreachable state in FSM
  --> src/ctrl.iris:25:9
   |
25 |         Unused,
   |         ^^^^^^ state 'Unused' is never reached from initial state
   |
   = help: remove unused state or add transition to it
```

**原因:** 初期状態から到達できない状態が定義されている。リソースの無駄。

**解決方法:**

```rust
// 悪い例: 到達不能な状態
fsm Controller(clk.posedge, rst.async) {
    state enum { Idle, Run, Unused }
    initial Idle;

    transitions {
        Idle => { when start { goto Run; } }
        Run => { when done { goto Idle; } }
        // Unusedへの遷移がない
    }
}

// 良い例1: 未使用状態を削除
fsm Controller(clk.posedge, rst.async) {
    state enum { Idle, Run }
    // ...

// 良い例2: 遷移を追加
fsm Controller(clk.posedge, rst.async) {
    state enum { Idle, Run, Unused }
    initial Idle;

    transitions {
        Idle => { when start { goto Run; } }
        Run => { when error { goto Unused; } }
        Unused => { goto Idle; }  // 遷移を追加
    }
}
```

---

### FSM遷移の非網羅性

**エラーコード:** O3002

```
error[O3002]: non-exhaustive transitions
  --> src/fsm.iris:30:5
   |
30 | transitions {
31 |     Idle => { when start { goto Run; } }
32 | }
   | ^ no transition defined for state 'Run'
   |
   = help: add transition for 'Run' or use '_ => { ... }' for default
```

**原因:** 全ての状態に対して遷移が定義されていない。

**解決方法:**

```rust
// 悪い例: Run状態の遷移がない
fsm Controller(clk.posedge, rst.async) {
    state enum { Idle, Run, Done }
    initial Idle;

    transitions {
        Idle => { when start { goto Run; } }
        // Runの遷移がない
    }
}

// 良い例: 全状態に遷移を定義
fsm Controller(clk.posedge, rst.async) {
    state enum { Idle, Run, Done }
    initial Idle;

    transitions {
        Idle => { when start { goto Run; } }
        Run => { when complete { goto Done; } }
        Done => { goto Idle; }
    }
}

// デフォルト遷移を使用
fsm Controller(clk.posedge, rst.async) {
    state enum { Idle, Run }
    initial Idle;

    transitions {
        Idle => { when start { goto Run; } }
        Run => { goto Idle; }
        _ => { goto Idle; }  // デフォルト
    }
}
```

---

### インターフェース方向不一致

**エラーコード:** O4001

```
error[O4001]: interface view direction mismatch
  --> src/top.iris:45:5
   |
45 |     inst slave = AxiSlave { axi: bus.initiator };
   |                                   ^^^^^^^^^^^^^ expected 'target' view, found 'initiator'
   |
   = help: use `bus.target` for slave modules
```

**原因:** インターフェースのビュー方向が一致していない。マスターはinitiator、スレーブはtargetを使用。

**解決方法:**

```rust
// 悪い例: スレーブにinitiatorを接続
inst slave = AxiSlave { axi: bus.initiator };  // エラー

// 良い例: スレーブにはtargetを使用
inst slave = AxiSlave { axi: bus.target };     // OK
```

---

### 合成不可能な構文

**エラーコード:** O5001

```
error[O5001]: non-synthesizable construct
  --> src/div.iris:12:12
   |
12 |     result = a / b;
   |              ^^^^^ division is not directly synthesizable
   |
   = help: use `#[synthesis(use_dsp)]` or implement iterative divider
```

**原因:** ハードウェアに直接合成できない構文を使用している。

**解決方法:**

```rust
// 方法1: DSPブロックを使用
#[synthesis(use_dsp)]
comb {
    result = a / b;
}

// 方法2: 2の累乗の場合はシフトを使用
comb {
    result = a >> 2;  // a / 4 と同等
}

// 方法3: 反復型除算器を実装（複数サイクル）
// 専用モジュールとして実装
```

---

### モジュール未定義

**エラーコード:** O6001

```
error[O6001]: module not found
  --> src/top.iris:8:16
   |
8  |     inst cpu = RiscvCore { ... };
   |                ^^^^^^^^^ module 'RiscvCore' not found
   |
   = help: check spelling or add: `import riscv::RiscvCore;`
```

**原因:** 指定されたモジュールが見つからない。

**解決方法:**

1. スペルを確認
2. 必要な`import`文を追加
3. モジュールが存在するパッケージを確認
4. 外部モジュールの場合は`extern mod`を宣言

```rust
// インポートを追加
import riscv::RiscvCore;

// または外部モジュールとして宣言
extern mod RiscvCore(
    in  clk: clock,
    // ...
);
```

---

## C.3 seqブロック関連のエラー

### seqブロックのtestモジュール外での使用

**エラーコード:** O7001

```
error[O7001]: seq block used outside test module
  --> src/counter.iris:15:5
   |
15 |     seq main {
   |     ^^^ seq blocks are only allowed in test modules
   |
   = help: move seq block inside a 'test' module or use 'initial' for synthesis
```

**原因:** `seq`ブロックを`test`モジュール以外で使用している。`seq`はシミュレーション専用。

**解決方法:**

```rust
// 悪い例: 通常モジュールでseqを使用
mod Counter {
    // ...
    seq main {  // エラー
        // ...
    }
}

// 良い例: テストモジュールで使用
test CounterTest {
    seq main {
        let dut = Counter.create();
        // ...
    }
}
```

---

### seqブロック内での信号アクセスエラー

**エラーコード:** O7005

```
error[O7005]: synthesizable signal operation in seq block
  --> test/counter_test.iris:12:9
   |
12 |         counter = counter + 1;
   |         ^^^^^^^^ direct signal assignment in seq block
   |
   = help: use signal API: counter.set(counter.value() + 1)
```

**原因:** `seq`ブロック内で通常の代入構文を使用している。seqブロックでは信号アクセスAPIを使用する必要がある。

**解決方法:**

```rust
// 悪い例: 直接代入
seq main {
    counter = counter + 1;  // エラー
}

// 良い例: 信号アクセスAPIを使用
seq main {
    counter.set(counter.value() + 1);  // OK
}

// 読み取り: .value()
// 書き込み: .set(value)
```

---

### 外部Rust関数が見つからない

**エラーコード:** O7002

```
error[O7002]: external Rust function not found
  --> test/counter_test.iris:3:5
   |
3  | use rust::test_utils::verify_count;
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ function 'verify_count' not found
   |
   = help: check function name spelling and ensure it is 'pub'
```

**原因:** インポートしようとしたRust関数が見つからない。

**解決方法:**

1. 関数名のスペルを確認
2. Rust側で関数が`pub`で宣言されていることを確認
3. `rust/`ディレクトリのパスを確認
4. `rust/mod.rs`でモジュールが宣言されていることを確認

```rust
// rust/test_utils.rs
pub fn verify_count(actual: u64, expected: u64) {
    // ...
}

// rust/mod.rs
pub mod test_utils;
```

---

## C.4 警告の対処

### 未使用信号の警告

**警告コード:** W0001

```
warning[W0001]: unused signal
  --> src/debug.iris:10:9
   |
10 |     let _debug_signal: bit[32];
   |         ^^^^^^^^^^^^^ 'debug_signal' is declared but never used
```

**解決方法:**

```rust
// 方法1: _プレフィックスで意図的未使用を示す
let _debug_signal: bit[32];

// 方法2: アトリビュートで抑制
#[allow(W0001)]
let debug_signal: bit[32];

// 方法3: ファイルレベルで抑制
#![allow(W0001)]
```

---

### 高ファンアウトの警告

**警告コード:** W0007

```
warning[W0007]: high fanout signal
  --> src/top.iris:25:5
   |
25 |     out clk: clock;
   |     ^^^ 'clk' has high fanout (32 loads)
   |
   = note: consider using a clock buffer or restructuring the design
```

**解決方法:**

1. クロックバッファ（BUFG等）の使用を検討
2. 階層を再構成してファンアウトを減らす
3. 意図的であれば警告を抑制

```rust
// クロックバッファの使用
#[synthesis(clock_buffer = "BUFG")]
out clk: clock;
```

---

## C.5 デバッグのヒント

### シミュレーションが進まない

**症状:** シミュレーションがハングアップする、または進行しない。

**確認事項:**

1. クロックが正しく生成されているか
2. リセットが適切に解除されているか
3. 組み合わせループがないか
4. `await`文が正しく使用されているか

```rust
// クロック生成の確認
let clk = Clock.new(period: 10.ns);
dut.clk = clk;

// リセットシーケンス
dut.rst.assert();
await clk.cycles(5);
dut.rst.deassert();
await clk.cycles(1);  // リセット解除後1サイクル待つ
```

---

### 合成結果が期待と異なる

**症状:** シミュレーションは通るが、合成結果が異なる。

**確認事項:**

1. `x`（不定値）を使用していないか
2. ラッチが推論されていないか
3. 非合成可能な構文を使用していないか

```rust
// 悪い例: xを使用
comb {
    result = sel ? a : 8'bxxxxxxxx;  // 合成結果が不定
}

// 良い例: デフォルト値を明示
comb {
    default result = 0;
    if sel {
        result = a;
    }
}
```

---

### 型エラーが頻発する

**症状:** 型関連のエラーが多数発生する。

**確認事項:**

1. ビット幅が一致しているか
2. 符号付き/符号なしの混在がないか
3. 明示的な型変換を追加する必要があるか

```rust
// 明示的な型変換を追加
let a: bit[8] = 8'hFF;
let b: bit[16] = a.zero_extend[16]();  // ゼロ拡張
let c: i16 = a.sign_extend[16]();       // 符号拡張
let d: bit[4] = a.truncate[4]();        // 切り捨て
```

---

## C.6 パフォーマンス最適化

### 合成後のリソース使用量が多い

**対策:**

1. ブロックRAMの使用
2. DSPブロックの活用
3. パイプラインの最適化

```rust
// ブロックRAMの使用
#[synthesis(ram_style = "block")]
mem large_mem: bit[64][8192];

// DSPブロックの使用
#[synthesis(use_dsp)]
comb {
    product = a * b;
}
```

---

### タイミング制約を満たさない

**対策:**

1. パイプライン段数の増加
2. クリティカルパスの分割
3. リタイミングの活用

```rust
// パイプラインの追加
var stage1: bit[32] = 0;
var stage2: bit[32] = 0;
var stage3: bit[32] = 0;

sync(clk.posedge, rst.async) {
    stage1 = input;
    stage2 = stage1 + constant;  // 段1
    stage3 = stage2 * factor;     // 段2
}
```

---

## 参考リンク

- [IRIS言語仕様書 第14章 エラーメッセージ](../../../spec/14_error_messages.md)
- [IRIS言語仕様書 第19章 よくある質問（FAQ）](../../../spec/19_faq.md)