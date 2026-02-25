# 第14章 開発環境構築

## 本章のゴール

- IRIS開発環境を構築できる
- IDE/エディタを設定できる

---

## 14.1 ツールチェーンのインストール

### インストール方法

```bash
# cargoを使用
cargo install iris-lsp iris-fmt iris-lint

# または、プリビルドバイナリをダウンロード
curl -L https://github.com/iris-lang/iris/releases/latest/download/iris-lsp-linux-x64 -o iris-lsp
chmod +x iris-lsp
sudo mv iris-lsp /usr/local/bin/
```

### 主なツール

| ツール | 説明 |
|--------|------|
| `iris-lsp` | Language Server |
| `iris-fmt` | フォーマッタ |
| `iris-lint` | リンター |
| `iris-sim` | シミュレータ |

---

## 14.2 VS Code設定

### 拡張機能のインストール

1. VS Codeを開く
2. 拡張機能パネル（Ctrl+Shift+X）を開く
3. 「IRIS HDL」を検索
4. インストールをクリック

### settings.json

```json
{
    "files.associations": {
        "*.iris": "iris",
        "*.irs": "iris"
    },
    "iris.lsp.enable": true,
    "iris.format.onSave": true,
    "editor.tabSize": 4,
    "[iris]": {
        "editor.defaultFormatter": "iris-lang.iris-vscode"
    }
}
```

### キーバインド

| キー | 機能 |
|------|------|
| F12 | 定義へジャンプ |
| Shift+F12 | 参照を検索 |
| F2 | シンボル名変更 |
| Ctrl+Shift+F | フォーマット |

---

## 14.3 プロジェクト構成

### 標準ディレクトリ構造

```
project/
├── iris.toml           # プロジェクト設定
├── src/
│   ├── lib.iris        # ライブラリルート
│   └── rtl/
│       └── *.iris      # RTLモジュール
├── test/               # テストファイル
└── build/              # ビルド出力
```

### iris.toml

```toml
[package]
name = "my_project"
version = "1.0.0"
edition = "2025"

[synthesis]
top_module = "Top"
```

---

## 14.4 ビルドとシミュレーション

### ビルド

```bash
# SystemVerilog生成
iris build --output systemverilog

# 合成
iris synth --target fpga
```

### シミュレーション

```bash
# テスト実行
iris test

# 特定のテスト
iris test test_counter

# 波形出力
iris test --waveform
```

---

## 14.5 フォーマットとリント

### フォーマット

```bash
# ファイルをフォーマット
iris-fmt src/counter.iris

# インプレースで上書き
iris-fmt -i src/

# チェックのみ（CI用）
iris-fmt --check src/
```

### リント

```bash
# ファイルをリント
iris-lint src/counter.iris

# 警告レベルを指定
iris-lint --level error src/
```

---

## まとめ

- VS Code拡張機能で開発環境を構築
- `iris.toml` でプロジェクト設定
- コマンドラインでビルド・テスト実行
- フォーマッタとリンターで品質維持

---

## 参考リンク

- [IRIS言語仕様書 第21章 IDE連携ガイド](../../../spec/21_ide_guide.md)