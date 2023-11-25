# Lean Playground

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
- Modular definition of the Fibonacci sequence:
  ```lean
  def fib {m : ℕ} (n : ℕ) : (ZMod m) :=
    Fib.fib_fast n
  ```
- Showing that the modular Fibonacci sequence is periodic ([Pisano Period]):
  ```lean
  theorem fib_periodic {m : ℕ} [hm : Fact (m > 1)] :
    ∃ c > 0, Function.Periodic (@fib m) c := ...
  ```

### To Do
- Show that the Pisano Period is bounded by 6 times the modulus:
  ```lean
  theorem fib_periodic {m : ℕ} [hm : Fact (m > 1)] :
    ∃ 0 < c, c ≤ 6 * m ∧ Function.Periodic (@fib m) c := ...
  ```

[Pisano Period]: https://en.wikipedia.org/wiki/Pisano_period
