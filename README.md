# Lean Playground

Messing around with [Lean](https://github.com/leanprover/lean4).

Below are some highlights of each of the files.

## [`misc/Misc/Fibonacci.lean`](./misc/Misc/Fibonacci.lean)
- Standard definition of the Fibonacci sequence
  ```lean
  def fib_rec : ℕ → ℕ := fun
  | 0 => 0
  | 1 => 1
  | n + 2 => fib_rec (n + 1) + fib_rec (n)
  ```
- Alternative definitions of the Fibonacci sequence
  - `fib_rec_mat` and `fib_pow_mat` using matrix `Q` multiplication recursively or powers, respectively, where:
    ```math
    Q = \begin{bmatrix}
      1 & 1\\
      1 & 0
    \end{bmatrix}
    ```
- Equating these multiple definitions

## [`misc/Misc/FibMod.lean`](./misc/Misc/FibMod.lean)
- Modular definition of the Fibonacci sequence:
  ```lean
  def fib [mod : Mod] (n : ℕ) : ↑mod :=
    ((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst
  ```
- Showing relations between the entries of powers of the matrix $Q$ above:
  ```lean
  structure Q_entries [Mod] (n : ℕ) where
    Q_11_10 : (Q ^ (n + 1)) 1 1 = (Q ^ n) 1 0
    Q_11_01 : (Q ^ (n + 1)) 1 1 = (Q ^ n) 0 1
    Q_11_00 : (Q ^ (n + 2)) 1 1 = (Q ^ n) 0 0
    Q_10_01 : (Q ^ n) 1 0 = (Q ^ n) 0 1
  ```
- Showing that the modular Fibonacci sequence is periodic ([Pisano Period]):
  ```lean
  theorem fib_period_even [Mod] [hm : Fact (Mod.n > 2)] (p : ℕ) (hp : Function.Periodic fib p) : Even p := ...
  ```

### To Do
- Show that the Pisano Period is bounded by 6 times the modulus:
  ```lean
  theorem fib_period_bound [Mod] [hm : Fact (Mod.n ≥ 1)] (p : ℕ) (hp : Function.Periodic fib p) : p ≤ 6 * Mod.n := ...
  ```

[Lean]: https://github.com/leanprover/lean4
[Pisano Period]: https://en.wikipedia.org/wiki/Pisano_period
