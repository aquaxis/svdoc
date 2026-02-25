# 第12章 デザインパターン

## 本章のゴール

- IRIS特有の設計パターンを理解する
- 実践的な設計ができる
- アトリビュートを活用できる

---

## 12.1 ワンショットパルス生成

```rust
/// ワンショットパルス生成
mod OneShot(
    in  clk: clock,
    in  rst: reset,
    in  trigger: bit,
    out pulse: bit,
) {
    var delay: bit = 0;

    sync(clk.posedge, rst.async) {
        delay = trigger;
    }

    comb {
        pulse = trigger && !delay;
    }
}
```

---

## 12.2 クロックドメイン交差（CDC）

### 2段FFシンクロナイザ

```rust
/// 2段FFシンクロナイザ
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
```

### パルス同期

```rust
/// パルス同期器
mod PulseSync(
    in  src_clk: clock,
    in  dst_clk: clock,
    in  rst: reset,
    in  src_pulse: bit,
    out dst_pulse: bit,
) {
    // 送信側
    var src_toggle: bit = 0;
    sync(src_clk.posedge, rst.async) @src_domain {
        if src_pulse {
            src_toggle = !src_toggle;
        }
    }

    // 受信側
    var dst_sync1: bit = 0;
    var dst_sync2: bit = 0;
    var dst_sync3: bit = 0;

    sync(dst_clk.posedge, rst.async) @dst_domain {
        dst_sync1 = src_toggle;
        dst_sync2 = dst_sync1;
        dst_sync3 = dst_sync2;
    }

    comb {
        dst_pulse = dst_sync2 ^ dst_sync3;
    }
}
```

---

## 12.3 パイプライン設計

```rust
/// 3段パイプライン
mod Pipeline(
    in  clk: clock,
    in  rst: reset,
    in  din: bit[32],
    out dout: bit[32],
) {
    var stage1: bit[32] = 0;
    var stage2: bit[32] = 0;
    var stage3: bit[32] = 0;

    sync(clk.posedge, rst.async) {
        stage1 = din;
        stage2 = stage1;
        stage3 = stage2;
    }

    comb {
        dout = stage3;
    }
}
```

---

## 12.4 アトリビュート活用

### RAMスタイル指定

```rust
#[synthesis(ram_style = "block")]
mem large_buffer: bit[64][8192];

#[synthesis(ram_style = "distributed")]
mem small_fifo: bit[32][32];
```

### タイミング制御

```rust
#[synthesis(ram_output_register)]
mem pipelined_ram: bit[64][4096];
```

---

## 12.5 簡易バスプロトコル

```rust
/// 簡易バスインターフェース
interface SimpleBus[AddrWidth: uint, DataWidth: uint] {
    addr:   bit[AddrWidth],
    wdata:  bit[DataWidth],
    rdata:  bit[DataWidth],
    valid:  bit,
    ready:  bit,
    write:  bit,

    view initiator {
        out: addr, wdata, valid, write,
        in:  rdata, ready
    }

    view target {
        in:  addr, wdata, valid, write,
        out: rdata, ready
    }
}
```

---

## まとめ

- ワンショットパルスでエッジ検出
- CDCにはシンクロナイザを使用
- パイプラインでスループット向上
- アトリビュートで合成結果を制御

---

## 参考リンク

- [IRIS言語仕様書 第13章 アトリビュート](../../../spec/13_attributes.md)
- [IRIS言語仕様書 第17章 サンプルコード集](../../../spec/17_examples.md)