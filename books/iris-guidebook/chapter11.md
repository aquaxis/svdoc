---
title: "第11章 検証機能"
---

---
title: "第11章 検証機能"
---

# 第11章 検証機能

## 本章のゴール

- テストベンチを記述できる
- アサーションを使用できる
- シミュレーション制御を理解する

---

## 11.1 テストの基本

### テストブロック

```rust
#[test]
test check_counter() {
    // DUTのインスタンス化
    let dut = Counter[Width: 8].create();

    // クロック生成
    let clk = Clock.new(period: 10.ns);
    dut.clk = clk;

    // リセットシーケンス
    dut.rst.assert();
    await clk.cycles(5);
    dut.rst.deassert();
    await clk.cycles(1);

    // テスト刺激
    dut.enable = 1;
    await clk.cycles(10);

    // 検証
    assert dut.count == 8'h0A;
}
```

### テストアトリビュート

| アトリビュート | 説明 |
|----------------|------|
| `#[test]` | テストブロック宣言 |
| `#[timeout(1.ms)]` | タイムアウト指定 |
| `#[should_fail]` | 失敗を期待 |
| `#[ignore]` | テストをスキップ |

```rust
#[test]
#[timeout(100.us)]
test long_running_test() {
    await some_long_operation();
}

#[test]
#[should_fail]
test invalid_input_should_fail() {
    dut.invalid_data = 8'hFF;
    await clk.cycles(1);
    assert dut.error == 1;
}
```

---

## 11.2 シミュレーション制御

### クロック生成

```rust
// クロック生成
let clk = Clock.new(period: 10.ns);

// クロックサイクル待機
await clk.cycles(10);       // 10サイクル待機
await clk.posedge();        // 次の立ち上がりまで待機
await clk.negedge();        // 次の立ち下がりまで待機
```

### 時間待機

```rust
await delay(100.ns);        // 100ns待機
await delay(1.us);          // 1マイクロ秒待機
```

### 条件待機

```rust
await until(dut.ready == 1);                    // 条件成立まで待機
await until(dut.done == 1, timeout: 1.ms);     // タイムアウト付き
```

---

## 11.3 アサーション

### 即時アサーション

```rust
// 即時アサーション
assert dut.count == expected;

// エラーメッセージ付き
assert dut.valid == 1, "valid should be asserted";
```

### 遅延アサーション

```rust
// クロックサイクル後の検証
assert_after(5, dut.done == 1);

// 条件成立を待って検証
assert_eventually(dut.ready == 1);
```

---

## 11.4 並列実行

```rust
// 並列実行
fork {
    await send_data(dut, data);
}
join {
    await receive_response(dut);
}

// いずれか1つが完了したら続行
fork {
    task1();
    task2();
}
join_any;
```

---

## 練習：カウンタのテストベンチ

8ビットカウンターのテストベンチを作成してください。

```rust
#[test]
test counter_test() {
    // ここにテストコードを記述
}
```

<details>
<summary>解答例</summary>

```rust
#[test]
test counter_test() {
    let dut = Counter[Width: 8].create();
    let clk = Clock.new(period: 10.ns);

    dut.clk = clk;
    dut.rst.assert();
    await clk.cycles(5);
    dut.rst.deassert();
    await clk.cycles(1);

    // カウントテスト
    dut.enable = 1;
    await clk.cycles(10);
    assert dut.count == 8'h0A;

    // 停止テスト
    dut.enable = 0;
    await clk.cycles(5);
    assert dut.count == 8'h0A;

    // 再開テスト
    dut.enable = 1;
    await clk.cycles(5);
    assert dut.count == 8'h0F;
}
```

</details>

---

## まとめ

- テストは `#[test]` アトリビュートで宣言
- クロック生成とシミュレーション制御が可能
- アサーションで動作を検証
- `fork/join` で並列実行

---

## 参考リンク

- [IRIS言語仕様書 第11章 検証機能](../../../spec/11_verification.md)