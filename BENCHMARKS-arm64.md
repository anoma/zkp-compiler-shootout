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
|        | `1.22 ms` (✅ **1.00x**) | `67.96 ms` (❌ *55.63x slower*)   | `1.20 ms` (✅ **1.02x faster**) | `361.19 ms` (❌ *295.71x slower*)    |

### Sudoku: prove

|        | `Miden`                   | `Plonk: 3 by 3`                 | `Risc`                           | `Halo: 3 by 3`                    |
|:-------|:--------------------------|:--------------------------------|:---------------------------------|:--------------------------------- |
|        | `348.11 ms` (✅ **1.00x**) | `74.05 ms` (🚀 **4.70x faster**) | `941.61 ms` (❌ *2.70x slower*)   | `116.39 ms` (🚀 **2.99x faster**)  |

### Sudoku: verify

|        | `Miden`                 | `Plonk: 3 by 3`                | `Risc`                         | `Halo: 3 by 3`                  |
|:-------|:------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `2.77 ms` (✅ **1.00x**) | `8.47 ms` (❌ *3.06x slower*)   | `2.24 ms` (✅ **1.23x faster**) | `3.85 ms` (❌ *1.39x slower*)    |

### Sudoku:

|        | `Miden`                   | `Plonk: 3 by 3`                  | `Risc`                           | `Halo: 3 by 3`                    |
|:-------|:--------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `346.00 ms` (✅ **1.00x**) | `150.56 ms` (🚀 **2.30x faster**) | `943.85 ms` (❌ *2.73x slower*)   | `478.72 ms` (❌ *1.38x slower*)    |

### fibonacci: compile

|        | `Miden: iter-93`          | `Miden: fixed-92`               | `Miden: fixed-50`               | `Risc0: iter-93`                 | `Risc0: iter-50`                 | `Risc0: fixed-50`                | `Risc0: fixed-92`                 |
|:-------|:--------------------------|:--------------------------------|:--------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `59.20 us` (✅ **1.00x**)  | `51.31 us` (✅ **1.15x faster**) | `41.34 us` (✅ **1.43x faster**) | `217.66 us` (❌ *3.68x slower*)   | `225.05 us` (❌ *3.80x slower*)   | `234.23 us` (❌ *3.96x slower*)   | `241.48 us` (❌ *4.08x slower*)    |

### fibonacci: prove

|        | `Miden: iter-93`          | `Miden: fixed-92`                | `Miden: fixed-50`                | `Risc0: iter-93`                 | `Risc0: iter-50`                 | `Risc0: fixed-50`                | `Risc0: fixed-92`                 |
|:-------|:--------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `345.29 ms` (✅ **1.00x**) | `172.68 ms` (🚀 **2.00x faster**) | `174.90 ms` (🚀 **1.97x faster**) | `230.49 ms` (✅ **1.50x faster**) | `227.52 ms` (✅ **1.52x faster**) | `225.30 ms` (✅ **1.53x faster**) | `226.36 ms` (✅ **1.53x faster**)  |

### fibonacci: verify

|        | `Miden: iter-93`          | `Miden: fixed-92`              | `Miden: fixed-50`              | `Risc0: iter-93`               | `Risc0: iter-50`               | `Risc0: fixed-50`              | `Risc0: fixed-92`               |
|:-------|:--------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `2.76 ms` (✅ **1.00x**)   | `2.70 ms` (✅ **1.02x faster**) | `2.71 ms` (✅ **1.02x faster**) | `2.05 ms` (✅ **1.35x faster**) | `2.04 ms` (✅ **1.35x faster**) | `2.05 ms` (✅ **1.35x faster**) | `2.04 ms` (✅ **1.35x faster**)  |

### fibonacci:

|        | `Miden: iter-93`          | `Miden: fixed-92`                | `Miden: fixed-50`                | `Risc0: iter-93`                 | `Risc0: iter-50`                 | `Risc0: fixed-50`                | `Risc0: fixed-92`                 |
|:-------|:--------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `348.39 ms` (✅ **1.00x**) | `175.68 ms` (🚀 **1.98x faster**) | `177.95 ms` (🚀 **1.96x faster**) | `233.00 ms` (✅ **1.50x faster**) | `230.14 ms` (✅ **1.51x faster**) | `227.91 ms` (✅ **1.53x faster**) | `229.04 ms` (✅ **1.52x faster**)  |

### fibonacci large: compile

|        | `Miden: iter-1000`          | `Risc0: iter-1000`                |
|:-------|:----------------------------|:--------------------------------- |
|        | `59.27 us` (✅ **1.00x**)    | `219.38 us` (❌ *3.70x slower*)    |

### fibonacci large: prove

|        | `Miden: iter-1000`          | `Risc0: iter-1000`             |
|:-------|:----------------------------|:------------------------------ |
|        | `2.94 s` (✅ **1.00x**)      | `1.90 s` (✅ **1.54x faster**)  |

### fibonacci large: verify

|        | `Miden: iter-1000`          | `Risc0: iter-1000`              |
|:-------|:----------------------------|:------------------------------- |
|        | `3.03 ms` (✅ **1.00x**)     | `2.67 ms` (✅ **1.13x faster**)  |

### fibonacci large:

|        | `Miden: iter-1000`          | `Risc0: iter-1000`             |
|:-------|:----------------------------|:------------------------------ |
|        | `2.94 s` (✅ **1.00x**)      | `1.91 s` (✅ **1.54x faster**)  |

### Blake: compile

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `297.81 us` (✅ **1.00x**)                                              |

### Blake: prove

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `1.91 s` (✅ **1.00x**)                                                 |

### Blake: verify

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `3.26 ms` (✅ **1.00x**)                                                |

### Blake:

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `1.91 s` (✅ **1.00x**)                                                 |

### Blake3: compile

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `5.93 ms` (✅ **1.00x**)                    |

### Blake3: prove

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `1.40 s` (✅ **1.00x**)                     |

### Blake3: verify

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `3.18 ms` (✅ **1.00x**)                    |

### Blake3:

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `1.41 s` (✅ **1.00x**)                     |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

