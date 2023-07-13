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
|        | `205.74 us` (✅ **1.00x**) | `1.37 ms` (❌ *6.65x slower*)   | `98.20 ms` (❌ *477.31x slower*)   | `333.02 ms` (❌ *1618.65x slower*)   | `671.45 ms` (❌ *3263.56x slower*)          | `668.92 ms` (❌ *3251.26x slower*)    |

### Sudoku: prove

|        | `Triton`               | `Miden`                           | `Plonk: 3 by 3`                  | `Halo: 3 by 3`                    | `Vamp-IR zk-garage plonk: sudoku`          | `Vamp-IR halo2: sudoku`           |
|:-------|:-----------------------|:----------------------------------|:---------------------------------|:----------------------------------|:-------------------------------------------|:--------------------------------- |
|        | `4.33 s` (✅ **1.00x**) | `281.03 ms` (🚀 **15.42x faster**) | `96.56 ms` (🚀 **44.88x faster**) | `118.78 ms` (🚀 **36.48x faster**) | `73.67 ms` (🚀 **58.83x faster**)           | `84.74 ms` (🚀 **51.14x faster**)  |

### Sudoku: verify

|        | `Triton`                 | `Miden`                         | `Plonk: 3 by 3`                | `Halo: 3 by 3`                 | `Vamp-IR zk-garage plonk: sudoku`          | `Vamp-IR halo2: sudoku`           |
|:-------|:-------------------------|:--------------------------------|:-------------------------------|:-------------------------------|:-------------------------------------------|:--------------------------------- |
|        | `43.14 ms` (✅ **1.00x**) | `2.43 ms` (🚀 **17.78x faster**) | `7.20 ms` (🚀 **5.99x faster**) | `4.42 ms` (🚀 **9.77x faster**) | `7.77 ms` (🚀 **5.55x faster**)             | `3.99 ms` (🚀 **10.81x faster**)   |

### Sudoku:

|        | `Triton`               | `Miden`                           | `Plonk: 3 by 3`                   | `Halo: 3 by 3`                   | `Vamp-IR zk-garage plonk: sudoku`          | `Vamp-IR halo2: sudoku`           |
|:-------|:-----------------------|:----------------------------------|:----------------------------------|:---------------------------------|:-------------------------------------------|:--------------------------------- |
|        | `3.74 s` (✅ **1.00x**) | `285.03 ms` (🚀 **13.11x faster**) | `203.30 ms` (🚀 **18.39x faster**) | `461.41 ms` (🚀 **8.10x faster**) | `750.65 ms` (🚀 **4.98x faster**)           | `756.46 ms` (🚀 **4.94x faster**)  |

### fibonacci: compile

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`                | `Miden: fixed-92`               | `Miden: fixed-50`                |
|:-------|:--------------------------------|:--------------------------------|:--------------------------------|:--------------------------------|:-------------------------------- |
|        | `19.83 us` (✅ **1.00x**)        | `19.81 us` (✅ **1.00x faster**) | `66.05 us` (❌ *3.33x slower*)   | `56.78 us` (❌ *2.86x slower*)   | `45.71 us` (❌ *2.30x slower*)    |

### fibonacci: prove

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`           | `Miden: iter-93`                 | `Miden: fixed-92`                | `Miden: fixed-50`                 |
|:-------|:--------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `468.15 ms` (✅ **1.00x**)       | `958.73 ms` (❌ *2.05x slower*)   | `282.52 ms` (✅ **1.66x faster**) | `136.05 ms` (🚀 **3.44x faster**) | `137.18 ms` (🚀 **3.41x faster**)  |

### fibonacci: verify

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`          | `Miden: iter-93`               | `Miden: fixed-92`              | `Miden: fixed-50`               |
|:-------|:--------------------------------|:--------------------------------|:-------------------------------|:-------------------------------|:------------------------------- |
|        | `23.20 ms` (✅ **1.00x**)        | `28.89 ms` (❌ *1.25x slower*)   | `2.44 ms` (🚀 **9.51x faster**) | `2.38 ms` (🚀 **9.74x faster**) | `2.38 ms` (🚀 **9.73x faster**)  |

### fibonacci:

|        | `Triton: fibonacci-50`          | `Triton: fibonacci-93`           | `Miden: iter-93`                 | `Miden: fixed-92`                | `Miden: fixed-50`                 |
|:-------|:--------------------------------|:---------------------------------|:---------------------------------|:---------------------------------|:--------------------------------- |
|        | `462.22 ms` (✅ **1.00x**)       | `917.38 ms` (❌ *1.98x slower*)   | `284.82 ms` (✅ **1.62x faster**) | `138.46 ms` (🚀 **3.34x faster**) | `139.64 ms` (🚀 **3.31x faster**)  |

### fibonacci large: compile

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`               |
|:-------|:----------------------------------|:-------------------------------- |
|        | `19.93 us` (✅ **1.00x**)          | `65.96 us` (❌ *3.31x slower*)    |

### fibonacci large: prove

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`             |
|:-------|:----------------------------------|:------------------------------ |
|        | `14.66 s` (✅ **1.00x**)           | `2.59 s` (🚀 **5.66x faster**)  |

### fibonacci large: verify

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`               |
|:-------|:----------------------------------|:-------------------------------- |
|        | `74.79 ms` (✅ **1.00x**)          | `2.71 ms` (🚀 **27.58x faster**)  |

### fibonacci large:

|        | `Triton: fibonacci-1000`          | `Miden: iter-1000`             |
|:-------|:----------------------------------|:------------------------------ |
|        | `14.39 s` (✅ **1.00x**)           | `2.59 s` (🚀 **5.55x faster**)  |

### Blake: compile

|        | `Vamp-IR zk-garage plonk: Blake2s`          | `Vamp-IR halo2: Blake2s`           |
|:-------|:--------------------------------------------|:---------------------------------- |
|        | `46.79 s` (✅ **1.00x**)                     | `205.72 s` (❌ *4.40x slower*)      |

### Blake: prove

|        | `Vamp-IR zk-garage plonk: Blake2s`          | `Vamp-IR halo2: Blake2s`           |
|:-------|:--------------------------------------------|:---------------------------------- |
|        | `54.54 s` (✅ **1.00x**)                     | `27.90 s` (🚀 **1.95x faster**)     |

### Blake: verify

|        | `Vamp-IR zk-garage plonk: Blake2s`          | `Vamp-IR halo2: Blake2s`           |
|:-------|:--------------------------------------------|:---------------------------------- |
|        | `398.57 ms` (✅ **1.00x**)                   | `939.26 ms` (❌ *2.36x slower*)     |

### Blake:

|        | `Vamp-IR zk-garage plonk: Blake2s`          | `Vamp-IR halo2: Blake2s`           |
|:-------|:--------------------------------------------|:---------------------------------- |
|        | `101.01 s` (✅ **1.00x**)                    | `234.49 s` (❌ *2.32x slower*)      |

---
Made with [criterion-table](https://github.com/nu11ptr/criterion-table)

