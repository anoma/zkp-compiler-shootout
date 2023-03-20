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
|        | `1.37 ms` (✅ **1.00x**) | `95.98 ms` (❌ *69.91x slower*)   | `1.04 ms` (✅ **1.32x faster**) | `331.53 ms` (❌ *241.48x slower*)    |

### Sudoku: prove

|        | `Miden`                   | `Plonk: 3 by 3`                 | `Risc`                         | `Halo: 3 by 3`                    |
|:-------|:--------------------------|:--------------------------------|:-------------------------------|:--------------------------------- |
|        | `349.33 ms` (✅ **1.00x**) | `94.90 ms` (🚀 **3.68x faster**) | `8.36 s` (❌ *23.93x slower*)   | `115.77 ms` (🚀 **3.02x faster**)  |

### Sudoku: verify

|        | `Miden`                 | `Plonk: 3 by 3`                | `Risc`                         | `Halo: 3 by 3`                  |
|:-------|:------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `2.37 ms` (✅ **1.00x**) | `7.13 ms` (❌ *3.01x slower*)   | `5.51 ms` (❌ *2.32x slower*)   | `4.38 ms` (❌ *1.85x slower*)    |

### Sudoku:

|        | `Miden`                   | `Plonk: 3 by 3`                  | `Risc`                         | `Halo: 3 by 3`                    |
|:-------|:--------------------------|:---------------------------------|:-------------------------------|:--------------------------------- |
|        | `346.23 ms` (✅ **1.00x**) | `197.72 ms` (✅ **1.75x faster**) | `8.37 s` (❌ *24.16x slower*)   | `442.56 ms` (❌ *1.28x slower*)    |

### fibonacci: compile

|        | `Miden: iter-93`          | `Miden: fixed-92`               | `Miden: fixed-50`               | `Risc0: iter-93`                  | `Risc0: iter-50`                  | `Risc0: fixed-50`                 | `Risc0: fixed-92`                  |
|:-------|:--------------------------|:--------------------------------|:--------------------------------|:----------------------------------|:----------------------------------|:----------------------------------|:---------------------------------- |
|        | `67.22 us` (✅ **1.00x**)  | `57.50 us` (✅ **1.17x faster**) | `46.51 us` (✅ **1.45x faster**) | `959.07 us` (❌ *14.27x slower*)   | `957.27 us` (❌ *14.24x slower*)   | `980.19 us` (❌ *14.58x slower*)   | `989.62 us` (❌ *14.72x slower*)    |

### fibonacci: prove

|        | `Miden: iter-93`          | `Miden: fixed-92`                | `Miden: fixed-50`                | `Risc0: iter-93`               | `Risc0: iter-50`               | `Risc0: fixed-50`              | `Risc0: fixed-92`               |
|:-------|:--------------------------|:---------------------------------|:---------------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `343.26 ms` (✅ **1.00x**) | `165.62 ms` (🚀 **2.07x faster**) | `167.57 ms` (🚀 **2.05x faster**) | `4.66 s` (❌ *13.57x slower*)   | `4.66 s` (❌ *13.57x slower*)   | `4.66 s` (❌ *13.58x slower*)   | `4.66 s` (❌ *13.58x slower*)    |

### fibonacci: verify

|        | `Miden: iter-93`          | `Miden: fixed-92`              | `Miden: fixed-50`              | `Risc0: iter-93`               | `Risc0: iter-50`               | `Risc0: fixed-50`              | `Risc0: fixed-92`               |
|:-------|:--------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `2.38 ms` (✅ **1.00x**)   | `2.32 ms` (✅ **1.03x faster**) | `2.32 ms` (✅ **1.02x faster**) | `4.66 ms` (❌ *1.96x slower*)   | `4.66 ms` (❌ *1.96x slower*)   | `4.67 ms` (❌ *1.96x slower*)   | `4.66 ms` (❌ *1.96x slower*)    |

### fibonacci:

|        | `Miden: iter-93`          | `Miden: fixed-92`                | `Miden: fixed-50`                | `Risc0: iter-93`               | `Risc0: iter-50`               | `Risc0: fixed-50`              | `Risc0: fixed-92`               |
|:-------|:--------------------------|:---------------------------------|:---------------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `345.83 ms` (✅ **1.00x**) | `168.16 ms` (🚀 **2.06x faster**) | `170.35 ms` (🚀 **2.03x faster**) | `4.66 s` (❌ *13.49x slower*)   | `4.67 s` (❌ *13.50x slower*)   | `4.67 s` (❌ *13.50x slower*)   | `4.67 s` (❌ *13.50x slower*)    |

### fibonacci large: compile

|        | `Miden: iter-1000`          | `Risc0: iter-1000`                 |
|:-------|:----------------------------|:---------------------------------- |
|        | `67.31 us` (✅ **1.00x**)    | `956.13 us` (❌ *14.20x slower*)    |

### fibonacci large: prove

|        | `Miden: iter-1000`          | `Risc0: iter-1000`             |
|:-------|:----------------------------|:------------------------------ |
|        | `3.06 s` (✅ **1.00x**)      | `8.32 s` (❌ *2.72x slower*)    |

### fibonacci large: verify

|        | `Miden: iter-1000`          | `Risc0: iter-1000`              |
|:-------|:----------------------------|:------------------------------- |
|        | `2.62 ms` (✅ **1.00x**)     | `5.51 ms` (❌ *2.10x slower*)    |

### fibonacci large:

|        | `Miden: iter-1000`          | `Risc0: iter-1000`             |
|:-------|:----------------------------|:------------------------------ |
|        | `3.06 s` (✅ **1.00x**)      | `8.33 s` (❌ *2.73x slower*)    |

### Blake: compile

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `1.58 ms` (✅ **1.00x**)                                                |

### Blake: prove

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `15.92 s` (✅ **1.00x**)                                                |

### Blake: verify

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `4.68 ms` (✅ **1.00x**)                                                |

### Blake:

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `15.93 s` (✅ **1.00x**)                                                |

### Blake3: compile

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `6.64 ms` (✅ **1.00x**)                    |

### Blake3: prove

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `1.48 s` (✅ **1.00x**)                     |

### Blake3: verify

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `2.76 ms` (✅ **1.00x**)                    |

### Blake3:

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `1.50 s` (✅ **1.00x**)                     |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

