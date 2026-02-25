---
title: "付録B 用語集"
---

# 付録B 用語集

本書で使用するIRIS関連の用語を解説します。

---

## A

### ALU（Arithmetic Logic Unit）
算術論理演算ユニット。加算、減算、論理演算などの基本演算を実行するハードウェアユニット。

### アサーション（assertion）
設計の正しさを検証するための文。シミュレーション時に条件が満たされない場合にエラーを報告する。IRISでは`assert`キーワードで記述。

### async（非同期リセット）
クロックエッジに依存せず、即座に効果を発揮するリセット方式。`rst.async`で指定。同期リセットと比較してリセット回路が簡潔になる利点がある。

### アトリビュート（attribute）
コード要素に付加するメタデータ。`#[...]`形式で記述。合成ツールへの指示やコンパイラ制御に使用する。

### await
テストモジュールのseqブロック内で使用する時間制御構文。クロックエッジ待機（`await clk.posedge`）、条件待機（`await until(expr)`）、サイクル待機（`await clk.cycles(n)`）などの形式がある。

### AXI（Advanced eXtensible Interface）
ARM社が策定したオンチップバスプロトコル。AXI4、AXI4-Lite、AXI4-Streamなどのバリエーションがある。

---

## B

### バレルシフタ（barrel shifter）
任意のビット数のシフトを1クロックで実行できる回路。シフト量に応じて複数段のマルチプレクサで構成される。

### ビットスライス（bit slice）
信号の一部ビットを抽出する操作。`signal[7:0]`のように範囲指定する。

### bit
IRISの基本ビット型。`bit[N]`でNビット幅を表す。例：`bit[8]`は8ビット信号。

### ブロックRAM（block RAM）
FPGAに内蔵された専用メモリリソース。大容量メモリの実装に使用。分散RAM（distributed RAM）より容量が大きいが、レイテンシがある。

---

## C

### CDC（Clock Domain Crossing）
クロックドメイン交差。異なるクロックドメイン間での信号転送。同期化が必要で、メタステーブル状態を防ぐためにシンクロナイザを使用する。

### clock
クロック型。タイミング信号を表すIRIS専用型。`posedge`（立ち上がりエッジ）と`negedge`（立ち下がりエッジ）を指定できる。

### comb
組み合わせ論理ブロック。クロックに依存しない論理を記述。SystemVerilogの`always_comb`に相当。

### 連結（concatenation）
複数の信号を結合する操作。`{a, b, c}`形式で記述。

### const
定数宣言。コンパイル時に値が確定する不変の値。SystemVerilogの`parameter`、`localparam`に相当。

### コンテキストベース合成（context-based synthesis）
IRISの特徴で、信号の使用場所（comb/sync/fsm）により組み合わせ回路か順序回路かを自動判定する仕組み。`var`はsync/fsm内でのみ使用可能。

---

## D

### delay
遅延。seqブロック内でシミュレーション時間を進める構文。`#10ns;`（10ナノ秒遅延）の形式。

### ドライバ（driver）
信号に値を供給する回路。IRISでは一つの信号に対して一つのドライバのみ許可（multi drive禁止）。

### 分散RAM（distributed RAM）
FPGAのLUT（Look-Up Table）を使用して実装されるメモリ。小容量・高速アクセス向け。ブロックRAMより小容量だが高速。

### DSP
Digital Signal Processor。FPGAに内蔵された乗算・加算専用ハードウェアブロック。演算回路の効率的な実装に使用。

---

## E

### EBNF（Extended Backus-Naur Form）
拡張バッカス・ナウア記法。文法を形式的に定義するための記法。IRIS仕様書で言語構文を定義するのに使用。

### enum
列挙型。有限個の名前付き値を持つ型。FSMの状態定義などで使用。

### extend（ビット幅拡張）
`.extend[N]()`でNビットに拡張。ゼロ拡張または符号拡張。

### extern mod
外部モジュール宣言。既存のVerilog/SystemVerilogモジュールをIRISから使用するための宣言。ブラックボックスとして扱われる。

### extern rust
外部Rust関数宣言ブロック。testモジュールのseqブロックから呼び出す外部Rust関数のシグネチャを明示的に宣言する。

---

## F

### ファンアウト（fanout）
一つの出力が駆動する入力の数。高ファンアウトはタイミング問題の原因になりうる。

### フリップフロップ（flip-flop）
クロックエッジで値を保持する基本的な順序回路素子。D-FF（D型フリップフロップ）が最も一般的。

### FIFO（First-In First-Out）
先入れ先出しバッファ。データを格納順に取り出すキュー構造。クロックドメイン間のデータ転送などで使用。

### FSM（Finite State Machine）
有限状態機械。状態と遷移で動作を記述するモデル。IRISでは`fsm`ブロックで宣言。ムーア型とミーリ型がある。

---

## G

### ジェネリクス（generic）
パラメータ化。モジュールや型を汎用化する機能。`mod Name[P: uint = 8]`形式で記述。`where`で制約を追加できる。

### goto
FSM内での状態遷移命令。`goto State;`で指定状態に遷移。

### グレイコード（gray code）
隣接する値が1ビットのみ異なるエンコーディング。CDCやFSMで使用。非同期FIFOのポインタでよく使われる。

---

## H

### ハンドシェイク（handshake）
valid/ready信号によるデータ転送プロトコル。AXIなどで採用されている。

### HDL（Hardware Description Language）
ハードウェア記述言語。デジタル回路を記述するための言語。Verilog、VHDL、SystemVerilog、IRISなどがある。

---

## I

### ILA（Integrated Logic Analyzer）
統合ロジックアナライザ。FPGA内部信号をリアルタイムで観測するデバッグツール。Xilinx Vivadoなどで提供。

### initial
FSMの初期状態を指定するキーワード。`initial Idle;`のように使用。

### initiator
インターフェースのビュー。トランザクションを開始する側（マスター）。targetの対義語。

### interface
インターフェース。関連する信号をグループ化し、方向（ビュー）を定義する構造。SystemVerilogのinterface/modportに相当。

### inst
インスタンス化宣言。モジュールのインスタンスを作成。`inst name = Module { ... };`形式で記述。

---

## L

### ラッチ（latch）
レベルセンシティブな記憶素子。意図しないラッチはバグの原因。IRISでは組み合わせ論理の不完全な代入を検出してエラー報告。

### let
信号宣言。`let x: bit[8];`で信号を宣言。直接代入（`let x = expr;`）は組み合わせ回路。sync/fsm内で代入すると順序回路（非推奨、varを使用）。

### let mut
可変信号宣言。初期値を指定してsync/fsmで使用すると、初期値がリセット値となる。`var`の使用が推奨される。

### リテラル（literal）
ソースコード中の定数値。`8'hFF`（8ビット16進数）、`4'b1010`（4ビット2進数）など。

---

## M

### メタステーブル（metastability）
フリップフロップのセットアップ/ホールド時間違反により発生する不安定状態。CDC対策が必要。

### マルチドライブ（multi drive）
同一信号への複数箇所からの駆動。IRISではコンパイルエラーとして検出。意図しないバス競合を防止。

### match
パターンマッチ式。複数の条件分岐を記述。SystemVerilogの`case`に相当。全ケースの網羅が推奨。

### ミーリ型（Mealy）
ミーリ型FSM。出力が現在の状態と入力に依存。出力が入力の変化に即座に反応。

### mem
メモリ宣言。RAM/ROMを宣言。`mem storage: bit[32][1024];`形式。

### mod
モジュール宣言キーワード。ハードウェアモジュールを定義。SystemVerilogの`module`に相当。

### ムーア型（Moore）
ムーア型FSM。出力が現在の状態のみに依存。出力が安定しているため設計が容易。

### マルチサイクルパス（multicycle path）
複数クロックサイクルで安定すればよい信号パス。タイミング解析で特別な制約が必要。

---

## N

### negedge
クロックの立ち下がりエッジ。`clk.negedge`で指定。`posedge`の対義語。

---

## O

### ワンホット（one-hot）
1ビットのみが1となる状態エンコード方式。FSMの状態表現で使用。デコードが高速だがビット数が多くなる。

---

## P

### パッケージ（package）
関連する型、関数、モジュールをグループ化する名前空間。再利用性と管理性を向上。

### パイプライン（pipeline）
処理を複数段階に分割し、スループットを向上させる技術。各段をレジスタで区切る。

### ポート（port）
モジュールの外部接続点。`in`（入力）、`out`（出力）、`inout`（双方向）の3種類。

### posedge
クロックの立ち上がりエッジ。`clk.posedge`で指定。`negedge`の対義語。

### pub
公開修飾子。パッケージ外からアクセス可能にする。カプセル化の制御に使用。

---

## R

### RAM（Random Access Memory）
ランダムアクセスメモリ。読み書き可能なメモリ。ブロックRAMと分散RAMの2種類がある。

### reset
リセット型。回路の初期化信号を表すIRIS専用型。`active_low: true/false`で極性を指定。

### ROM（Read-Only Memory）
読み取り専用メモリ。書き換え不可のメモリ。初期化データから推論。

---

## S

### seq
シーケンシャル処理ブロック。testモジュール内でのみ使用可能な手続き的記述ブロック。Rustの制御構文（for、while、if等）を直接使用でき、信号アクセスAPIと時間制御構文でDUTと連携する。

### 信号アクセスAPI（signal access API）
seqブロック内でDUTの信号を読み書きするためのメソッド。`.value()`で信号値を読み取り、`.set(value)`で信号に値を設定する。

### sync
順序論理ブロック。クロック同期の回路を記述。SystemVerilogの`always_ff`に相当。

### シンクロナイザ（synchronizer）
同期化器。CDCで使用される複数段フリップフロップ回路。メタステーブル状態を緩和。

### struct
構造体。複数のフィールドをグループ化した複合型。パケット構造などで使用。

### sync_ff
同期化フリップフロップ。CDC対策のための複数段FFシンクロナイザ。`sync_ff(signal, stages: 2)`形式。

### SystemVerilog
IEEE 1800規格のハードウェア記述言語。IRISのトランスパイル先。Verilogの上位互換。

---

## T

### タイミング制約（timing constraint）
クロック周期やセットアップ/ホールド時間の要件を定義。合成ツールに指示する。

### トランスパイル（transpile）
あるプログラミング言語から別の言語への変換。IRISはSystemVerilogにトランスパイルされる。

### target
インターフェースのビュー。トランザクションに応答する側（スレーブ）。initiatorの対義語。

### test
テストブロック。検証コードを記述。`#[test]`アトリビュートで宣言。

### テストモジュール（test module）
`test identifier { ... }`形式で宣言されるテストベンチ専用のモジュール。ポートを持たず、シミュレーション専用（合成対象外）。seqブロック、initial、inst等を含む。

### 時間制御（time control）
seqブロック内でシミュレーション時間を制御する構文の総称。`await clk.posedge`（クロックエッジ待機）、`#10ns;`（遅延）、`await until(condition)`（条件待機）などがある。

### transitions
FSMの遷移定義ブロック。各状態からの遷移条件と遷移先を記述。

### truncate
ビット幅切り捨て。`.truncate[N]()`でNビットに切り詰め。上位ビットが破棄される。

---

## U

### UltraRAM
Xilinx UltraScale+デバイスの大容量内蔵メモリ。ブロックRAMより大容量。

### use rust::
Rust関数インポート構文。testモジュールのseqブロックで使用する外部Rust関数をインポートする。`use rust::module::func;`（単一関数）、`use rust::module::{f1, f2};`（複数関数）、`use rust::module::*;`（ワイルドカード）の形式がある。

---

## V

### union
ユニオン型。複数のバリアントのいずれかを保持する型。タグ付きunionはenumに類似。メモリの再解釈に使用。

### var
順序回路専用の信号宣言。sync/fsmブロック内でのみ使用可能。comb/直接代入で使用するとコンパイルエラー。初期値がリセット値となる。

### view
インターフェースのビュー定義。信号の方向を指定。`initiator`、`target`、`monitor`などがある。

### VIO（Virtual I/O）
仮想I/O。デバッグ時にFPGA内部信号を操作・観測するツール。Xilinx Vivadoなどで提供。

---

## W

### when
FSM遷移条件。`when condition { goto State; }`形式で記述。

---

## 記号・数字

### `=`
代入演算子。IRISでは組み合わせ論理・順序論理ともに`=`を使用（統一）。SystemVerilogの`=`と`<=`の使い分けが不要。

### `#[...]`
アトリビュート記法。メタデータをコード要素に付加。合成指示や警告制御に使用。

### `$clog2`
2を底とする対数の天井関数。必要なビット幅の計算に使用。`$clog2(N)`はNを表現するのに必要なビット数。

### `::`
スコープ解決演算子。パッケージパスやジェネリクス引数で使用。`Package::Module`や`Type::constant`など。

### `#`
遅延演算子（seqブロック内）。シミュレーション時間を進める。`#10ns;`（10ナノ秒遅延）。

---

## 参考リンク

- [IRIS言語仕様書 第18章 用語集](../../../spec/18_glossary.md)