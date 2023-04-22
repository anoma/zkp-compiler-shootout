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

|        | `Triton`                  | `Miden`                        | `Plonk: 3 by 3`                   | `Risc`                         | `Halo: 3 by 3`                       |
|:-------|:--------------------------|:-------------------------------|:----------------------------------|:-------------------------------|:------------------------------------ |
|        | `204.86 us` (✅ **1.00x**) | `1.37 ms` (❌ *6.70x slower*)   | `97.55 ms` (❌ *476.17x slower*)   | `1.13 ms` (❌ *5.50x slower*)   | `330.26 ms` (❌ *1612.07x slower*)    |

### Sudoku: prove

|        | `Triton`                | `Miden`                           | `Plonk: 3 by 3`                   | `Risc`                        | `Halo: 3 by 3`                      |
|:-------|:------------------------|:----------------------------------|:----------------------------------|:------------------------------|:----------------------------------- |
|        | `14.37 s` (✅ **1.00x**) | `340.62 ms` (🚀 **42.18x faster**) | `96.09 ms` (🚀 **149.53x faster**) | `8.38 s` (✅ **1.71x faster**) | `116.45 ms` (🚀 **123.39x faster**)  |

### Sudoku: verify

|        | `Triton`                  | `Miden`                         | `Plonk: 3 by 3`                 | `Risc`                          | `Halo: 3 by 3`                   |
|:-------|:--------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:-------------------------------- |
|        | `118.64 ms` (✅ **1.00x**) | `2.38 ms` (🚀 **49.75x faster**) | `7.22 ms` (🚀 **16.43x faster**) | `5.57 ms` (🚀 **21.31x faster**) | `4.40 ms` (🚀 **26.99x faster**)  |

### Sudoku:

|        | `Triton`               | `Miden`                           | `Plonk: 3 by 3`                   | `Risc`                        | `Halo: 3 by 3`                     |
|:-------|:-----------------------|:----------------------------------|:----------------------------------|:------------------------------|:---------------------------------- |
|        | `8.06 s` (✅ **1.00x**) | `344.99 ms` (🚀 **23.37x faster**) | `200.19 ms` (🚀 **40.27x faster**) | `8.39 s` (✅ **1.04x slower**) | `449.40 ms` (🚀 **17.94x faster**)  |

### fibonacci: compile

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`                | `Miden: fixed-92`               | `Miden: fixed-50`               | `Risc0: iter-93`                | `Risc0: iter-50`                | `Risc0: fixed-50`               | `Risc0: fixed-92`                |
|:-------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:-------------------------------- |
|        | `19.48 us` (✅ **1.00x**)        | `19.80 us` (✅ **1.02x slower**) | `67.02 us` (❌ *3.44x slower*)   | `57.51 us` (❌ *2.95x slower*)   | `46.50 us` (❌ *2.39x slower*)   | `1.03 ms` (❌ *52.77x slower*)   | `1.03 ms` (❌ *52.84x slower*)   | `1.05 ms` (❌ *53.80x slower*)   | `1.06 ms` (❌ *54.58x slower*)    |

### fibonacci: prove

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`                 | `Miden: fixed-92`                | `Miden: fixed-50`                | `Risc0: iter-93`              | `Risc0: iter-50`              | `Risc0: fixed-50`             | `Risc0: fixed-92`              |
|:-------|:--------------------------------|:--------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:------------------------------|:------------------------------|:------------------------------|:------------------------------ |
|        | `1.09 s` (✅ **1.00x**)          | `2.17 s` (❌ *1.99x slower*)     | `342.71 ms` (🚀 **3.17x faster**) | `165.82 ms` (🚀 **6.56x faster**) | `167.25 ms` (🚀 **6.50x faster**) | `4.66 s` (❌ *4.29x slower*)   | `4.66 s` (❌ *4.29x slower*)   | `4.66 s` (❌ *4.29x slower*)   | `4.67 s` (❌ *4.29x slower*)    |

### fibonacci: verify

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`                | `Miden: fixed-92`               | `Miden: fixed-50`               | `Risc0: iter-93`                | `Risc0: iter-50`                | `Risc0: fixed-50`               | `Risc0: fixed-92`                |
|:-------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:-------------------------------- |
|        | `83.93 ms` (✅ **1.00x**)        | `94.19 ms` (❌ *1.12x slower*)   | `2.38 ms` (🚀 **35.31x faster**) | `2.33 ms` (🚀 **35.97x faster**) | `2.34 ms` (🚀 **35.88x faster**) | `4.72 ms` (🚀 **17.79x faster**) | `4.72 ms` (🚀 **17.78x faster**) | `4.72 ms` (🚀 **17.80x faster**) | `4.71 ms` (🚀 **17.81x faster**)  |

### fibonacci:

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`                 | `Miden: fixed-92`                | `Miden: fixed-50`                | `Risc0: iter-93`              | `Risc0: iter-50`              | `Risc0: fixed-50`             | `Risc0: fixed-92`              |
|:-------|:--------------------------------|:--------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:------------------------------|:------------------------------|:------------------------------|:------------------------------ |
|        | `1.07 s` (✅ **1.00x**)          | `2.04 s` (❌ *1.92x slower*)     | `344.02 ms` (🚀 **3.10x faster**) | `167.61 ms` (🚀 **6.36x faster**) | `169.99 ms` (🚀 **6.27x faster**) | `4.66 s` (❌ *4.38x slower*)   | `4.67 s` (❌ *4.38x slower*)   | `4.67 s` (❌ *4.38x slower*)   | `4.67 s` (❌ *4.38x slower*)    |

### fibonacci large: compile

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`              | `Risc0: iter-1000`               |
|:-------|:----------------------------------|:--------------------------------|:-------------------------------- |
|        | `19.68 us` (✅ **1.00x**)          | `67.12 us` (❌ *3.41x slower*)   | `1.02 ms` (❌ *52.05x slower*)    |

### fibonacci large: prove

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`             | `Risc0: iter-1000`             |
|:-------|:----------------------------------|:-------------------------------|:------------------------------ |
|        | `31.99 s` (✅ **1.00x**)           | `3.07 s` (🚀 **10.41x faster**) | `8.35 s` (🚀 **3.83x faster**)  |

### fibonacci large: verify

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`              | `Risc0: iter-1000`               |
|:-------|:----------------------------------|:--------------------------------|:-------------------------------- |
|        | `139.55 ms` (✅ **1.00x**)         | `2.64 ms` (🚀 **52.94x faster**) | `5.58 ms` (🚀 **25.01x faster**)  |

### fibonacci large:

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`             | `Risc0: iter-1000`             |
|:-------|:----------------------------------|:-------------------------------|:------------------------------ |
|        | `31.59 s` (✅ **1.00x**)           | `3.08 s` (🚀 **10.27x faster**) | `8.35 s` (🚀 **3.78x faster**)  |

### Blake: compile

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `1.73 ms` (✅ **1.00x**)                                                |

### Blake: prove

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `15.96 s` (✅ **1.00x**)                                                |

### Blake: verify

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `4.72 ms` (✅ **1.00x**)                                                |

### Blake:

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `15.98 s` (✅ **1.00x**)                                                |

### Blake3: compile

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `6.65 ms` (✅ **1.00x**)                    |

### Blake3: prove

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `1.48 s` (✅ **1.00x**)                     |

### Blake3: verify

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `4.30 ms` (✅ **1.00x**)                    |

### Blake3:

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `1.50 s` (✅ **1.00x**)                     |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

