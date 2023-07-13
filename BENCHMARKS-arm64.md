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

## Benchmark Results

### Sudoku: compile

|        | `Triton`                  | `Miden`                        | `Plonk: 3 by 3`                   | `Halo: 3 by 3`                      | `Vamp-IR zk-garage plonk: sudoku`          | `Vamp-IR halo2: sudoku`              |
|:-------|:--------------------------|:-------------------------------|:----------------------------------|:------------------------------------|:-------------------------------------------|:------------------------------------ |
|        | `223.85 us` (✅ **1.00x**) | `1.24 ms` (❌ *5.54x slower*)   | `64.79 ms` (❌ *289.43x slower*)   | `317.25 ms` (❌ *1417.25x slower*)   | `591.76 ms` (❌ *2643.57x slower*)          | `578.46 ms` (❌ *2584.15x slower*)    |

### Sudoku: prove

|        | `Triton`               | `Miden`                          | `Plonk: 3 by 3`                  | `Halo: 3 by 3`                    | `Vamp-IR zk-garage plonk: sudoku`          | `Vamp-IR halo2: sudoku`            |
|:-------|:-----------------------|:---------------------------------|:---------------------------------|:----------------------------------|:-------------------------------------------|:---------------------------------- |
|        | `2.85 s` (✅ **1.00x**) | `293.32 ms` (🚀 **9.70x faster**) | `70.62 ms` (🚀 **40.30x faster**) | `106.91 ms` (🚀 **26.62x faster**) | `10.03 ms` (🚀 **283.88x faster**)          | `14.09 ms` (🚀 **202.01x faster**)  |

### Sudoku: verify

|        | `Triton`                 | `Miden`                         | `Plonk: 3 by 3`                | `Halo: 3 by 3`                  | `Vamp-IR zk-garage plonk: sudoku`          | `Vamp-IR halo2: sudoku`           |
|:-------|:-------------------------|:--------------------------------|:-------------------------------|:--------------------------------|:-------------------------------------------|:--------------------------------- |
|        | `37.25 ms` (✅ **1.00x**) | `3.03 ms` (🚀 **12.31x faster**) | `7.72 ms` (🚀 **4.82x faster**) | `3.56 ms` (🚀 **10.45x faster**) | `7.39 ms` (🚀 **5.04x faster**)             | `1.17 ms` (🚀 **31.71x faster**)   |

### Sudoku:

|        | `Triton`               | `Miden`                          | `Plonk: 3 by 3`                   | `Halo: 3 by 3`                   | `Vamp-IR zk-garage plonk: sudoku`          | `Vamp-IR halo2: sudoku`           |
|:-------|:-----------------------|:---------------------------------|:----------------------------------|:---------------------------------|:-------------------------------------------|:--------------------------------- |
|        | `2.42 s` (✅ **1.00x**) | `297.18 ms` (🚀 **8.14x faster**) | `142.19 ms` (🚀 **17.00x faster**) | `432.98 ms` (🚀 **5.58x faster**) | `609.16 ms` (🚀 **3.97x faster**)           | `594.97 ms` (🚀 **4.06x faster**)  |

### fibonacci: compile

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`                | `Miden: fixed-92`               | `Miden: fixed-50`                |
|:-------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:-------------------------------- |
|        | `22.74 us` (✅ **1.00x**)        | `22.74 us` (✅ **1.00x faster**) | `59.59 us` (❌ *2.62x slower*)   | `51.55 us` (❌ *2.27x slower*)   | `41.43 us` (❌ *1.82x slower*)    |

### fibonacci: prove

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`           | `Miden: iter-93`                 | `Miden: fixed-92`                | `Miden: fixed-50`                 |
|:-------|:--------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `321.30 ms` (✅ **1.00x**)       | `634.68 ms` (❌ *1.98x slower*)   | `300.72 ms` (✅ **1.07x faster**) | `151.88 ms` (🚀 **2.12x faster**) | `157.30 ms` (🚀 **2.04x faster**)  |

### fibonacci: verify

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`               | `Miden: fixed-92`              | `Miden: fixed-50`               |
|:-------|:--------------------------------|:--------------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `19.49 ms` (✅ **1.00x**)        | `24.74 ms` (❌ *1.27x slower*)   | `3.02 ms` (🚀 **6.46x faster**) | `2.94 ms` (🚀 **6.64x faster**) | `2.94 ms` (🚀 **6.62x faster**)  |

### fibonacci:

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`           | `Miden: iter-93`                 | `Miden: fixed-92`                | `Miden: fixed-50`                 |
|:-------|:--------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `319.92 ms` (✅ **1.00x**)       | `614.63 ms` (❌ *1.92x slower*)   | `303.57 ms` (✅ **1.05x faster**) | `154.65 ms` (🚀 **2.07x faster**) | `160.05 ms` (🚀 **2.00x faster**)  |

### fibonacci large: compile

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`               |
|:-------|:----------------------------------|:-------------------------------- |
|        | `23.64 us` (✅ **1.00x**)          | `59.56 us` (❌ *2.52x slower*)    |

### fibonacci large: prove

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`             |
|:-------|:----------------------------------|:------------------------------ |
|        | `9.49 s` (✅ **1.00x**)            | `2.52 s` (🚀 **3.76x faster**)  |

### fibonacci large: verify

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`               |
|:-------|:----------------------------------|:-------------------------------- |
|        | `60.00 ms` (✅ **1.00x**)          | `3.37 ms` (🚀 **17.78x faster**)  |

### fibonacci large:

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`             |
|:-------|:----------------------------------|:------------------------------ |
|        | `9.56 s` (✅ **1.00x**)            | `2.55 s` (🚀 **3.74x faster**)  |

### Blake: compile

|        | `Vamp-IR zk-garage plonk: Blake2s`          | `Vamp-IR halo2: Blake2s`           |
|:-------|:--------------------------------------------|:---------------------------------- |
|        | `35.49 s` (✅ **1.00x**)                     | `193.45 s` (❌ *5.45x slower*)      |

### Blake: prove

|        | `Vamp-IR zk-garage plonk: Blake2s`          | `Vamp-IR halo2: Blake2s`           |
|:-------|:--------------------------------------------|:---------------------------------- |
|        | `48.56 s` (✅ **1.00x**)                     | `19.93 s` (🚀 **2.44x faster**)     |

### Blake: verify

|        | `Vamp-IR zk-garage plonk: Blake2s`          | `Vamp-IR halo2: Blake2s`           |
|:-------|:--------------------------------------------|:---------------------------------- |
|        | `282.42 ms` (✅ **1.00x**)                   | `615.47 ms` (❌ *2.18x slower*)     |

### Blake:

|        | `Vamp-IR zk-garage plonk: Blake2s`          | `Vamp-IR halo2: Blake2s`           |
|:-------|:--------------------------------------------|:---------------------------------- |
|        | `83.88 s` (✅ **1.00x**)                     | `218.47 s` (❌ *2.60x slower*)      |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

