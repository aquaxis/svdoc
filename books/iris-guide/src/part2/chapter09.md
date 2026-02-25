# 第9章 メモリ

## 本章のゴール

- `mem`キーワードを使用できる
- RAM/ROMを推論できる
- メモリ初期化を理解する

---

## 9.1 メモリ宣言

### 基本構文

```rust
mem メモリ名: 要素型[深さ];
```

### 基本例

```rust
// シンプルなメモリ
mem storage: bit[32][1024];       // 1024ワード × 32ビット

// 構造体配列
mem packet_buffer: PacketHeader[256];

// 多次元メモリ
mem cache: bit[64][4][256];       // 4ウェイ × 256エントリ × 64ビット
```

---

## 9.2 RAM（読み書き可能）

### シングルポートRAM

```rust
mod Ram[DataWidth: uint = 32, Depth: uint = 1024] {
    in  clk: clock,
    in  we: bit,
    in  addr: bit[$clog2(Depth)],
    in  wdata: bit[DataWidth],
    out rdata: bit[DataWidth],

    mem storage: bit[DataWidth][Depth];

    sync(clk.posedge) {
        if we {
            storage[addr] = wdata;
        }
        rdata = storage[addr];
    }
}
```

### デュアルポートRAM

```rust
mod DualPortRam[Width: uint, Depth: uint] {
    in  clk: clock,
    // ポートA
    in  a_we: bit,
    in  a_addr: bit[$clog2(Depth)],
    in  a_wdata: bit[Width],
    out a_rdata: bit[Width],
    // ポートB
    in  b_we: bit,
    in  b_addr: bit[$clog2(Depth)],
    in  b_wdata: bit[Width],
    out b_rdata: bit[Width],

    mem storage: bit[Width][Depth] {
        ports: 2,
        type: true_dual_port
    };

    sync(clk.posedge) {
        if a_we {
            storage[a_addr] = a_wdata;
        }
        a_rdata = storage[a_addr];

        if b_we {
            storage[b_addr] = b_wdata;
        }
        b_rdata = storage[b_addr];
    }
}
```

---

## 9.3 ROM（読み取り専用）

### インライン初期化

```rust
mod SineTable(
    in  addr: bit[4],
    out data: bit[8],
) {
    const sine: bit[8][16] = [
        8'd128, 8'd177, 8'd218, 8'd246,
        8'd255, 8'd246, 8'd218, 8'd177,
        8'd128, 8'd79,  8'd38,  8'd10,
        8'd0,   8'd10,  8'd38,  8'd79
    ];

    comb {
        data = sine[addr];
    }
}
```

### ファイルからの初期化

```rust
mod RomFromFile(
    in  clk: clock,
    in  addr: bit[10],
    out data: bit[32],
) {
    const rom_data: bit[32][1024] {
        init_file: "rom_contents.hex",
        format: hex
    };

    sync(clk.posedge) {
        data = rom_data[addr];
    }
}
```

---

## 9.4 読み出しモード

| モード | 説明 | 動作 |
|--------|------|------|
| `read_first` | 読み出し優先（デフォルト） | 書き込み前の値を読み出し |
| `write_first` | 書き込み優先 | 書き込み後の値を読み出し |
| `no_change` | 変更なし | 書き込み時は読み出し値を保持 |

```rust
mem ram: bit[32][1024] {
    read_mode: read_first
};
```

---

## 9.5 合成アトリビュート

### RAMスタイル

| スタイル | 説明 | 用途 |
|----------|------|------|
| `block` | ブロックRAM | 大容量メモリ |
| `distributed` | 分散RAM | 小容量・高速 |
| `auto` | 自動選択 | デフォルト |

```rust
#[synthesis(ram_style = "block")]
mem large_buffer: bit[64][8192];

#[synthesis(ram_style = "distributed")]
mem small_fifo: bit[32][32];
```

---

## 練習：メモリ付きFIFO

メモリを使用したFIFOを作成してください。

```rust
/// メモリ付きFIFO
mod MemFifo[Width: uint = 8, Depth: uint = 16](
    in  clk: clock,
    in  rst: reset,
    in  push: bit,
    in  pop: bit,
    in  din: bit[Width],
    out dout: bit[Width],
    out full: bit,
    out empty: bit,
) {
    // ここにコードを記述
}
```

<details>
<summary>解答例</summary>

```rust
mod MemFifo[Width: uint = 8, Depth: uint = 16](
    in  clk: clock,
    in  rst: reset,
    in  push: bit,
    in  pop: bit,
    in  din: bit[Width],
    out dout: bit[Width],
    out full: bit,
    out empty: bit,
) {
    const ADDR_WIDTH: uint = $clog2(Depth);

    mem buffer: bit[Width][Depth];
    var wr_ptr: bit[ADDR_WIDTH] = 0;
    var rd_ptr: bit[ADDR_WIDTH] = 0;
    var count: bit[ADDR_WIDTH + 1] = 0;

    sync(clk.posedge, rst.async) {
        if push && !full {
            buffer[wr_ptr] = din;
            wr_ptr = wr_ptr + 1;
        }

        if pop && !empty {
            rd_ptr = rd_ptr + 1;
        }

        // カウント更新
        if push && !pop && !full {
            count = count + 1;
        } else if !push && pop && !empty {
            count = count - 1;
        }
    }

    comb {
        dout = buffer[rd_ptr];
        full = (count == Depth);
        empty = (count == 0);
    }
}
```

</details>

---

## まとめ

- メモリは `mem` キーワードで宣言
- RAMは `sync` ブロック内で読み書き
- ROMは `const` と初期化で実現
- アトリビュートでRAMスタイルを制御

---

## 参考リンク

- [IRIS言語仕様書 第10章 メモリ](../../../spec/10_memory.md)