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

|        | `Triton`                  | `Miden`                        | `Plonk: 3 by 3`                    | `Risc`                         | `Halo: 3 by 3`                       |
|:-------|:--------------------------|:-------------------------------|:-----------------------------------|:-------------------------------|:------------------------------------ |
|        | `227.02 us` (✅ **1.00x**) | `1.47 ms` (❌ *6.45x slower*)   | `101.70 ms` (❌ *447.97x slower*)   | `1.23 ms` (❌ *5.41x slower*)   | `345.36 ms` (❌ *1521.26x slower*)    |

### Sudoku: prove

|        | `Triton`                | `Miden`                           | `Plonk: 3 by 3`                    | `Risc`                        | `Halo: 3 by 3`                      |
|:-------|:------------------------|:----------------------------------|:-----------------------------------|:------------------------------|:----------------------------------- |
|        | `12.31 s` (✅ **1.00x**) | `363.43 ms` (🚀 **33.87x faster**) | `100.67 ms` (🚀 **122.27x faster**) | `8.90 s` (✅ **1.38x faster**) | `122.58 ms` (🚀 **100.41x faster**)  |

### Sudoku: verify

|        | `Triton`                 | `Miden`                         | `Plonk: 3 by 3`                 | `Risc`                          | `Halo: 3 by 3`                   |
|:-------|:-------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:-------------------------------- |
|        | `86.12 ms` (✅ **1.00x**) | `2.54 ms` (🚀 **33.93x faster**) | `7.70 ms` (🚀 **11.18x faster**) | `5.91 ms` (🚀 **14.57x faster**) | `4.68 ms` (🚀 **18.42x faster**)  |

### Sudoku:

|        | `Triton`               | `Miden`                           | `Plonk: 3 by 3`                   | `Risc`                        | `Halo: 3 by 3`                     |
|:-------|:-----------------------|:----------------------------------|:----------------------------------|:------------------------------|:---------------------------------- |
|        | `9.16 s` (✅ **1.00x**) | `368.40 ms` (🚀 **24.87x faster**) | `210.74 ms` (🚀 **43.47x faster**) | `8.94 s` (✅ **1.02x faster**) | `474.34 ms` (🚀 **19.31x faster**)  |

### fibonacci: compile

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`                | `Miden: fixed-92`               | `Miden: fixed-50`               | `Risc0: iter-93`                | `Risc0: iter-50`                | `Risc0: fixed-50`               | `Risc0: fixed-92`                |
|:-------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:-------------------------------- |
|        | `22.05 us` (✅ **1.00x**)        | `22.43 us` (✅ **1.02x slower**) | `71.07 us` (❌ *3.22x slower*)   | `60.81 us` (❌ *2.76x slower*)   | `49.09 us` (❌ *2.23x slower*)   | `1.12 ms` (❌ *50.62x slower*)   | `1.15 ms` (❌ *52.03x slower*)   | `1.14 ms` (❌ *51.86x slower*)   | `1.15 ms` (❌ *52.35x slower*)    |

### fibonacci: prove

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`                 | `Miden: fixed-92`                | `Miden: fixed-50`                | `Risc0: iter-93`              | `Risc0: iter-50`              | `Risc0: fixed-50`             | `Risc0: fixed-92`              |
|:-------|:--------------------------------|:--------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:------------------------------|:------------------------------|:------------------------------|:------------------------------ |
|        | `1.11 s` (✅ **1.00x**)          | `2.24 s` (❌ *2.02x slower*)     | `365.69 ms` (🚀 **3.03x faster**) | `176.90 ms` (🚀 **6.27x faster**) | `178.66 ms` (🚀 **6.20x faster**) | `4.96 s` (❌ *4.47x slower*)   | `4.96 s` (❌ *4.47x slower*)   | `4.96 s` (❌ *4.47x slower*)   | `4.96 s` (❌ *4.47x slower*)    |

### fibonacci: verify

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`                | `Miden: fixed-92`               | `Miden: fixed-50`               | `Risc0: iter-93`               | `Risc0: iter-50`               | `Risc0: fixed-50`              | `Risc0: fixed-92`               |
|:-------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:-------------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `53.25 ms` (✅ **1.00x**)        | `66.77 ms` (❌ *1.25x slower*)   | `2.54 ms` (🚀 **21.00x faster**) | `2.47 ms` (🚀 **21.53x faster**) | `2.48 ms` (🚀 **21.44x faster**) | `6.65 ms` (🚀 **8.00x faster**) | `7.21 ms` (🚀 **7.38x faster**) | `8.33 ms` (🚀 **6.39x faster**) | `6.68 ms` (🚀 **7.97x faster**)  |

### fibonacci:

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`                 | `Miden: fixed-92`                | `Miden: fixed-50`                | `Risc0: iter-93`              | `Risc0: iter-50`              | `Risc0: fixed-50`             | `Risc0: fixed-92`              |
|:-------|:--------------------------------|:--------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:------------------------------|:------------------------------|:------------------------------|:------------------------------ |
|        | `1.09 s` (✅ **1.00x**)          | `2.25 s` (❌ *2.06x slower*)     | `367.52 ms` (🚀 **2.97x faster**) | `180.10 ms` (🚀 **6.06x faster**) | `181.23 ms` (🚀 **6.02x faster**) | `4.96 s` (❌ *4.55x slower*)   | `4.96 s` (❌ *4.55x slower*)   | `4.97 s` (❌ *4.55x slower*)   | `4.97 s` (❌ *4.55x slower*)    |

### fibonacci large: compile

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`              | `Risc0: iter-1000`               |
|:-------|:----------------------------------|:--------------------------------|:-------------------------------- |
|        | `22.47 us` (✅ **1.00x**)          | `71.12 us` (❌ *3.16x slower*)   | `1.11 ms` (❌ *49.52x slower*)    |

### fibonacci large: prove

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`             | `Risc0: iter-1000`             |
|:-------|:----------------------------------|:-------------------------------|:------------------------------ |
|        | `34.91 s` (✅ **1.00x**)           | `3.29 s` (🚀 **10.62x faster**) | `8.88 s` (🚀 **3.93x faster**)  |

### fibonacci large: verify

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`              | `Risc0: iter-1000`               |
|:-------|:----------------------------------|:--------------------------------|:-------------------------------- |
|        | `107.72 ms` (✅ **1.00x**)         | `2.79 ms` (🚀 **38.58x faster**) | `14.28 ms` (🚀 **7.54x faster**)  |

### fibonacci large:

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`             | `Risc0: iter-1000`             |
|:-------|:----------------------------------|:-------------------------------|:------------------------------ |
|        | `35.71 s` (✅ **1.00x**)           | `3.29 s` (🚀 **10.85x faster**) | `8.90 s` (🚀 **4.01x faster**)  |

### Blake: compile

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `1.89 ms` (✅ **1.00x**)                                                |

### Blake: prove

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `16.98 s` (✅ **1.00x**)                                                |

### Blake: verify

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `5.00 ms` (✅ **1.00x**)                                                |

### Blake:

|        | `Risc0: Library-The quick brown fox jumps over the lazy dog`           |
|:-------|:---------------------------------------------------------------------- |
|        | `17.00 s` (✅ **1.00x**)                                                |

### Blake3: compile

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `7.05 ms` (✅ **1.00x**)                    |

### Blake3: prove

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `1.58 s` (✅ **1.00x**)                     |

### Blake3: verify

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `3.17 ms` (✅ **1.00x**)                    |

### Blake3:

|        | `Miden: Library-quick brown fox`           |
|:-------|:------------------------------------------ |
|        | `1.60 s` (✅ **1.00x**)                     |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

