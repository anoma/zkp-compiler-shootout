# Benchmarks

## Table of Contents

- [Benchmark Results](#benchmark-results)
    - [Sudoku: compile](#sudoku:-compile)
    - [Sudoku: prove](#sudoku:-prove)
    - [Sudoku: verify](#sudoku:-verify)
    - [Sudoku:](#sudoku:)
    - [fibonacci: compile](#fibonacci:-compile)
    - [fibonacci: prove](#fibonacci:-prove)
    - [fibonacci: verify](#fibonacci:-verify)
    - [fibonacci:](#fibonacci:)
    - [fibonacci large: compile](#fibonacci-large:-compile)
    - [fibonacci large: prove](#fibonacci-large:-prove)
    - [fibonacci large: verify](#fibonacci-large:-verify)
    - [fibonacci large:](#fibonacci-large:)
    - [Blake: compile](#blake:-compile)
    - [Blake: prove](#blake:-prove)
    - [Blake: verify](#blake:-verify)
    - [Blake:](#blake:)
    - [Blake3: compile](#blake3:-compile)
    - [Blake3: prove](#blake3:-prove)
    - [Blake3: verify](#blake3:-verify)
    - [Blake3:](#blake3:)

## Benchmark Results

### Sudoku: compile

|        | `Miden`                 | `Plonk: 3 by 3`                  | `Risc`                         | `Halo: 3 by 3`                      |
|:-------|:------------------------|:---------------------------------|:-------------------------------|:----------------------------------- |
|        | `1.52 ms` (✅ **1.00x**) | `99.92 ms` (❌ *65.80x slower*)   | `1.86 ms` (❌ *1.22x slower*)   | `329.15 ms` (❌ *216.76x slower*)    |

### Sudoku: prove

|        | `Miden`                   | `Plonk: 3 by 3`                  | `Risc`                        | `Halo: 3 by 3`                    |
|:-------|:--------------------------|:---------------------------------|:------------------------------|:--------------------------------- |
|        | `477.41 ms` (✅ **1.00x**) | `100.52 ms` (🚀 **4.75x faster**) | `1.67 s` (❌ *3.49x slower*)   | `116.74 ms` (🚀 **4.09x faster**)  |

### Sudoku: verify

|        | `Miden`                 | `Plonk: 3 by 3`                | `Risc`                         | `Halo: 3 by 3`                  |
|:-------|:------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `2.41 ms` (✅ **1.00x**) | `7.28 ms` (❌ *3.02x slower*)   | `2.79 ms` (❌ *1.15x slower*)   | `4.39 ms` (❌ *1.82x slower*)    |

### Sudoku:

|        | `Miden`                   | `Plonk: 3 by 3`                  | `Risc`                        | `Halo: 3 by 3`                    |
|:-------|:--------------------------|:---------------------------------|:------------------------------|:--------------------------------- |
|        | `475.69 ms` (✅ **1.00x**) | `205.22 ms` (🚀 **2.32x faster**) | `1.67 s` (❌ *3.52x slower*)   | `450.98 ms` (✅ **1.05x faster**)  |

### fibonacci: compile

|        | `Miden: iter-93`          | `Miden: fixed-92`               | `Miden: fixed-50`               | `Risc0: iter-93`                 | `Risc0: iter-50`                 | `Risc0: fixed-50`                | `Risc0: fixed-92`                 |
|:-------|:--------------------------|:--------------------------------|:--------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `64.89 us` (✅ **1.00x**)  | `55.92 us` (✅ **1.16x faster**) | `45.01 us` (✅ **1.44x faster**) | `387.69 us` (❌ *5.97x slower*)   | `388.34 us` (❌ *5.98x slower*)   | `391.42 us` (❌ *6.03x slower*)   | `390.26 us` (❌ *6.01x slower*)    |

### fibonacci: prove

|        | `Miden: iter-93`          | `Miden: fixed-92`                | `Miden: fixed-50`                | `Risc0: iter-93`                 | `Risc0: iter-50`                 | `Risc0: fixed-50`                | `Risc0: fixed-92`                 |
|:-------|:--------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `472.51 ms` (✅ **1.00x**) | `231.76 ms` (🚀 **2.04x faster**) | `233.25 ms` (🚀 **2.03x faster**) | `417.66 ms` (✅ **1.13x faster**) | `413.46 ms` (✅ **1.14x faster**) | `410.38 ms` (✅ **1.15x faster**) | `412.02 ms` (✅ **1.15x faster**)  |

### fibonacci: verify

|        | `Miden: iter-93`          | `Miden: fixed-92`              | `Miden: fixed-50`              | `Risc0: iter-93`               | `Risc0: iter-50`               | `Risc0: fixed-50`              | `Risc0: fixed-92`               |
|:-------|:--------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `2.41 ms` (✅ **1.00x**)   | `2.36 ms` (✅ **1.02x faster**) | `2.36 ms` (✅ **1.02x faster**) | `2.55 ms` (✅ **1.06x slower**) | `2.55 ms` (✅ **1.06x slower**) | `2.55 ms` (✅ **1.06x slower**) | `2.55 ms` (✅ **1.06x slower**)  |

### fibonacci:

|        | `Miden: iter-93`          | `Miden: fixed-92`                | `Miden: fixed-50`                | `Risc0: iter-93`                 | `Risc0: iter-50`                 | `Risc0: fixed-50`                | `Risc0: fixed-92`                 |
|:-------|:--------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `475.43 ms` (✅ **1.00x**) | `234.39 ms` (🚀 **2.03x faster**) | `235.84 ms` (🚀 **2.02x faster**) | `421.28 ms` (✅ **1.13x faster**) | `417.20 ms` (✅ **1.14x faster**) | `413.70 ms` (✅ **1.15x faster**) | `415.58 ms` (✅ **1.14x faster**)  |

### fibonacci large: compile

|        | `Miden: iter-1000`          | `Risc0: iter-1000`                |
|:-------|:----------------------------|:--------------------------------- |
|        | `64.91 us` (✅ **1.00x**)    | `387.43 us` (❌ *5.97x slower*)    |

### fibonacci large: prove

|        | `Miden: iter-1000`          | `Risc0: iter-1000`             |
|:-------|:----------------------------|:------------------------------ |
|        | `4.07 s` (✅ **1.00x**)      | `3.39 s` (✅ **1.20x faster**)  |

### fibonacci large: verify

|        | `Miden: iter-1000`          | `Risc0: iter-1000`              |
|:-------|:----------------------------|:------------------------------- |
|        | `2.66 ms` (✅ **1.00x**)     | `2.96 ms` (✅ **1.11x slower**)  |

### fibonacci large:

|        | `Miden: iter-1000`          | `Risc0: iter-1000`             |
|:-------|:----------------------------|:------------------------------ |
|        | `4.07 s` (✅ **1.00x**)      | `3.40 s` (✅ **1.20x faster**)  |

### Blake: compile

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `466.84 us` (✅ **1.00x**)                                              |

### Blake: prove

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `3.40 s` (✅ **1.00x**)                                                 |

### Blake: verify

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `4.24 ms` (✅ **1.00x**)                                                |

### Blake:

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `3.40 s` (✅ **1.00x**)                                                 |

### Blake3: compile

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `7.38 ms` (✅ **1.00x**)                    |

### Blake3: prove

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `1.99 s` (✅ **1.00x**)                     |

### Blake3: verify

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `3.12 ms` (✅ **1.00x**)                    |

### Blake3:

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `2.01 s` (✅ **1.00x**)                     |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

