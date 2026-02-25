# 第10章 パッケージシステム

## 本章のゴール

- パッケージを定義・使用できる
- 公開制御を理解する
- プロジェクト構成を管理できる

---

## 10.1 パッケージの基本

パッケージは、関連する型、定数、モジュールをまとめて管理する仕組みです。

### パッケージ定義

```rust
// src/common/mod.iris
package common;

/// 8ビットデータ型
pub type Byte = bit[8];

/// 32ビットワード型
pub type Word = bit[32];

/// 演算コード列挙型
pub enum OpCode: bit[4] {
    Add  = 4'h0,
    Sub  = 4'h1,
    And  = 4'h2,
    Or   = 4'h3,
    Nop  = 4'hF,
}

/// パリティ計算関数
pub fn parity(data: Byte) -> bit {
    return data.xor_reduce();
}
```

---

## 10.2 可視性制御

### 公開範囲

| 修飾子 | 可視範囲 |
|--------|----------|
| なし | 同一パッケージ内のみ |
| `pub` | どこからでもアクセス可能 |

```rust
package mylib;

// 公開
pub struct PublicConfig { ... }

// プライベート（デフォルト）
fn private_function() { ... }
```

---

## 10.3 インポート

### 基本的なインポート

```rust
// 単一アイテム
import common::Word;
import common::OpCode;

// 複数アイテム
import common::{Word, OpCode, Byte};

// エイリアス付き
import common::Word as DataWord;
```

### 完全修飾名

```rust
import common;

let data: common::Word = 32'h0;
```

---

## 10.4 プロジェクト構成

### 標準ディレクトリ構造

```
project/
├── iris.toml           # プロジェクト設定
├── src/
│   ├── lib.iris        # ライブラリルート
│   ├── main.iris       # 合成トップ
│   └── rtl/
│       ├── mod.iris
│       └── cpu.iris
├── test/               # テストファイル
└── build/              # ビルド出力
```

### iris.toml 設定

```toml
[package]
name = "my_soc"
version = "1.0.0"
edition = "2025"

[dependencies]
iris_std = "1.0"
iris_axi = { version = "2.0", features = ["lite"] }

[synthesis]
target = "xilinx_ultrascale_plus"
top_module = "SocTop"
```

---

## 10.5 依存関係管理

### 依存関係の種類

```toml
[dependencies]
# バージョン指定
iris_std = "1.0"

# Gitリポジトリから
riscv_core = { git = "https://github.com/example/riscv", tag = "v1.0" }

# ローカルパスから
vendor_ip = { path = "../vendor_ip" }
```

---

## 練習：パッケージ化されたプロジェクト

共通型を定義するパッケージを作成してください。

```rust
// src/types.iris
package types;

// ここに共通型を定義
```

<details>
<summary>解答例</summary>

```rust
package types;

/// 汎用データ型
pub type Byte = bit[8];
pub type Word = bit[32];
pub type Address = bit[16];

/// ステータス列挙型
pub enum Status: bit[2] {
    Idle   = 2'b00,
    Busy   = 2'b01,
    Done   = 2'b10,
    Error  = 2'b11,
}
```

</details>

---

## まとめ

- パッケージでコードを整理
- `pub` で公開制御
- `import` で他パッケージを使用
- `iris.toml` でプロジェクト設定

---

## 参考リンク

- [IRIS言語仕様書 第12章 パッケージシステム](../../../spec/12_package_system.md)