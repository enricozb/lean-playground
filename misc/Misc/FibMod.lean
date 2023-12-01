import Mathlib.Algebra.Periodic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Init.Function
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.Order.WellFoundedSet

/-!
# Fibonacci Sequence Mod `m` and Pisano Periods

Contains a definition of the Fibonacci sequence modulo `m`. Also
provides proofs around the periodicity `p(m)` of `fib (mod m ≥ 1)` and properties
of those periods.

The `Mod` typeclass is used to provide the modulus of these definitions and theorems
implicitly.
-/

namespace FibMod

/-- Wrapper class for adding modulus to the type class system.
This is used so the modulus can be inferred in the following `theorem`s and `def`s. -/
class Mod : Type where
  n : ℕ

/-- Coerce `Mod` into its inner value. -/
instance : Coe Mod ℕ := ⟨fun mod => mod.n⟩

/-- Coerce `mod : Mod` into `ZMod mod.n`. -/
instance : Coe Mod Type := ⟨fun mod => ZMod mod.n⟩

/-- `Mod` from a `Nat`. -/
instance : OfNat Mod n where
  ofNat := ⟨n⟩

/-- Matrix used in the Fibonacci sequence. -/
def Q [mod : Mod] : Matrix (Fin 2) (Fin 2) ↑mod := ![
  ![1, 1],
  ![1, 0]
]

@[simp]
lemma Q_00 [Mod] : Q 0 0 = 1 := rfl
@[simp]
lemma Q_01 [Mod] : Q 0 1 = 1 := rfl
@[simp]
lemma Q_10 [Mod] : Q 1 0 = 1 := rfl
@[simp]
lemma Q_11 [Mod] : Q 1 1 = 0 := rfl

@[simp]
lemma Q_pow_two [Mod] : Q ^ 2 = Q + 1 := by
  apply funext; intro i; apply funext; intro j
  fin_cases i
  all_goals fin_cases j
  all_goals simp only [
    pow_two, zero_add, ne_eq,
    Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
    Q_00, Q_01, Q_10, Q_11,
    Fin.mk_one, Fin.zero_eta, Fin.sum_univ_two
  ]
  all_goals ring

@[simp]
lemma Q_pow_succ [Mod] (n : ℕ) : Q ^ (n + 2) = Q ^ (n + 1) + Q ^ n := by
  rw [pow_add, Q_pow_two, mul_add, mul_one, add_left_inj, pow_add, pow_one]

@[simp]
lemma Q_det_eq_neg_one [Mod] : Q.det = -1 := by
  rw [Matrix.det_fin_two, Q_00, Q_01, Q_10, Q_11]
  ring_nf

lemma isUnit_Q_det [Mod] : IsUnit Q.det := by
  rw [Q_det_eq_neg_one, IsUnit.neg_iff]
  exact isUnit_one

lemma Q_exists_pow_eq [Mod] [h_mod_ge_one : Fact (Mod.n ≥ 1)] : ∃ a b, a > b ∧ Q ^ a = Q ^ b := by
  by_cases Mod.n = 1

  -- case Mod.n = 1
  · have h : Q ^ 2 = Q ^ 1 := by
      simp only [Q_pow_two, pow_one, add_right_eq_self]
      apply funext; intro i; apply funext; intro j
      all_goals fin_cases i
      all_goals fin_cases j
      all_goals { rw [h]; simp only }
      
    exact ⟨2, 1, (by simp only : 2 > 1), h⟩

  -- case Mod.n ≠ 1
  · have : Fact (Mod.n > 1) := by
      apply Fact.mk
      have h_mod_ne_one : Mod.n ≠ 1 := by rw [ne_eq]; exact h
      exact lt_iff_le_and_ne.mpr ⟨h_mod_ge_one.1, h_mod_ne_one.symm⟩

    have hQ_pow_not_inj : ¬Function.Injective (fun n => Q ^ n) := not_injective_infinite_finite _
    simp only [Function.Injective, not_forall, exists_prop] at hQ_pow_not_inj
    have ⟨a, b, hQ_pow_a_eq_Q_pow_b, ha_ne_b⟩ := hQ_pow_not_inj
    have ha_b_order : b > a ∨ a > b := Nat.lt_or_gt_of_ne ha_ne_b    
    cases ha_b_order with
    | inl hb_gt_a => exact ⟨b, a, hb_gt_a, hQ_pow_a_eq_Q_pow_b.symm⟩
    | inr ha_gt_b => exact ⟨a, b, ha_gt_b, hQ_pow_a_eq_Q_pow_b⟩

/-- `Q` has finite order. -/
theorem Q_order_finite [Mod] [Fact (Mod.n ≥ 1)] : ∃ p > 0, Q ^ p = 1 := by
  have ⟨a, b, ha_gt_b, hQ_pow_a_eq_Q_pow_b⟩ := Q_exists_pow_eq
  have a_ge_b : a ≥ b := Nat.le_of_lt ha_gt_b 
  have ha_sub_b_gt_zero : a - b > 0 := by simp only [ge_iff_le, gt_iff_lt, tsub_pos_iff_lt, ha_gt_b]
  have hQ_pow_c_eq_one : Q ^ (a - b) = 1 := by
    simp only [
      ge_iff_le, ne_eq, le_refl, tsub_eq_zero_of_le, pow_zero,
      Matrix.pow_sub' Q isUnit_Q_det a_ge_b, ←hQ_pow_a_eq_Q_pow_b,
      Matrix.det_pow, ←Matrix.pow_sub' Q isUnit_Q_det (by rfl)
    ]
    
  exact ⟨a - b, ha_sub_b_gt_zero, hQ_pow_c_eq_one⟩

/-- Equivalences between entries of powers `Q`. -/
structure Q_entries [Mod] (n : ℕ) where
  Q_11_10 : (Q ^ (n + 1)) 1 1 = (Q ^ n) 1 0
  Q_11_01 : (Q ^ (n + 1)) 1 1 = (Q ^ n) 0 1
  Q_11_00 : (Q ^ (n + 2)) 1 1 = (Q ^ n) 0 0
  Q_10_01 : (Q ^ n) 1 0 = (Q ^ n) 0 1

lemma Q_entries_eq [Mod] (n : ℕ) : Q_entries n := by
  apply Q_entries.mk
  all_goals {
    induction' n using Nat.strong_induction_on with n nih
    match n with
    | 0 => simp
    | 1 => simp
    | (n + 2) =>
      conv => rhs; simp [Q_pow_succ, ←(nih n), ←(nih (n + 1))]
      simp only [Q_pow_succ, Matrix.add_apply]
  }

/-- If `f(n) := (Q ^ n) 1 1` has period `p`, then `Q` has order `p`.
This is useful when showing that `fib (mod m ≥ 1)` has period `p(m)`, then `Q` has order `p(m)`.
-/
lemma Q_entry_period_is_order [Mod] (h : ∀ (n : ℕ), (Q ^ (n + p + 1)) 1 1 = (Q ^ (n + 1)) 1 1) : Q ^ p = 1 := by
  apply funext; intro i; apply funext; intro j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp
  · rw [←(Q_entries_eq p).Q_11_00, (by ring : p + 2 = 1 + p + 1), h 1]
    simp only [Q_pow_succ, zero_add, pow_one, pow_zero, Matrix.add_apply, Q_11, Matrix.one_apply_eq]
  · rw [←(Q_entries_eq p).Q_11_01, (by ring : p + 1 = 0 + p + 1), h 0]
    simp only [Q_pow_succ, zero_add, pow_one, pow_zero, Matrix.add_apply, Q_11]
  · rw [←(Q_entries_eq p).Q_11_10, (by ring : p + 1 = 0 + p + 1), h 0]
    simp only [Q_pow_succ, zero_add, pow_one, pow_zero, Matrix.add_apply, Q_11]
  · have hp : ((Q ^ (p + 2)) 1 1) = ((Q ^ 2 : Matrix _ _ _) 1 1) := by
      rw [(by ring : p + 2 = 1 + p + 1), h 1]
    rw [Q_pow_succ, Matrix.add_apply, (by ring : p + 1 = 0 + p + 1), h 0] at hp
    simp only [zero_add, pow_one, Q_11, Q_pow_succ, pow_zero, Matrix.add_apply, Matrix.one_apply_eq] at hp
    exact hp

/-- The Fibonacci sequence modulo `m`. -/
def fib [mod : Mod] (n : ℕ) : ↑mod := ((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst

/-- The Fibonacci sequence defined from powers of `Q`. -/
def fib_pow_mat [mod : Mod] (n : ℕ) : ↑mod := (Q ^ (n + 1)) 1 1

/-- Whether a function is the Fibonacci sequence. -/
def is_fib [mod : Mod] (f : ℕ → ↑mod) : Prop :=
  f 0 = 0 ∧
  f 1 = 1 ∧
  ∀ n, f (n + 2) = f (n + 1) + f n

/-- Any two functions `f₁` and `f₂` that are fib are equal. -/
lemma is_fib_eq [mod : Mod] (f₁ : ℕ → ↑mod) (f₂ : ℕ → ↑mod) {hf₁ : is_fib f₁} {hf₂ : is_fib f₂} : f₁ = f₂ := by
  have ⟨h0f₁, h1f₁, hnf₁⟩ := hf₁
  have ⟨h0f₂, h1f₂, hnf₂⟩ := hf₂
  apply funext; intro n
  induction' n using Nat.strong_induction_on with n nih
  match n with
  | 0 => rw [h0f₁, h0f₂]
  | 1 => rw [h1f₁, h1f₂]
  | (n + 2) =>
    rw [hnf₁ n, hnf₂ n, nih n, nih (n+1)]
    · simp only [add_lt_add_iff_left]
    · simp only [lt_add_iff_pos_right]

/-- `fib` definition satisfies the Fibonacci recurrence relation. -/
theorem fib_is_fib [Mod] : is_fib fib := by
  have h0 : fib 0 = 0 := by simp [fib]
  have h1 : fib 1 = 1 := by simp [fib]
  have hn n : fib (n + 2) = fib (n + 1) + fib n := by
    simp only [fib, Function.iterate_succ_apply', Nat.cast_add, add_comm]

  exact ⟨h0, h1, hn⟩

/-- `fib_pow_mat` definition satisfies the Fibonacci recurrence relation. -/
theorem fib_pow_mat_is_fib [Mod] : is_fib fib_pow_mat := by
  have h0 : fib_pow_mat 0 = 0 := by simp [fib_pow_mat]
  have h1 : fib_pow_mat 1 = 1 := by simp [fib_pow_mat]
  have hn n : fib_pow_mat (n + 2) = fib_pow_mat (n + 1) + fib_pow_mat n := by
    simp only [fib_pow_mat, Q_pow_succ, Matrix.add_apply]

  exact ⟨h0, h1, hn⟩

theorem fib_eq_fib_pow_mat [mod : Mod] : fib = fib_pow_mat :=
  @is_fib_eq mod fib fib_pow_mat fib_is_fib fib_pow_mat_is_fib

/-- `fib (mod n ≥ 1)` has period `p(n)` iff `Q ^ p(n) = 1`. -/
lemma fib_period_iff_Q_order [Mod] (p : ℕ): Function.Periodic fib p ↔ Q ^ p = 1 := by
  have mp : Function.Periodic fib p → Q ^ p = 1 := by
    intro h_period
    simp only [Function.Periodic, fib_eq_fib_pow_mat, fib_pow_mat] at h_period
    exact Q_entry_period_is_order h_period

  have mpr : Q ^ p = 1 → Function.Periodic fib p := by
    intro h_order
    simp only [Function.Periodic, fib_eq_fib_pow_mat, fib_pow_mat, pow_add, h_order]
    intro n; ring_nf

  exact ⟨mp, mpr⟩

/-- `fib (mod m ≥ 1)` is periodic for some period `p(m) > 0`.
While this theorem does not prove this, the period is bounded by `p(m) ≤ 6 * m`. -/
theorem fib_periodic [Mod] [Fact (Mod.n ≥ 1)] : ∃ p > 0, Function.Periodic fib p := by
  simp [fib_eq_fib_pow_mat, fib_pow_mat]
  have ⟨p, h_p_gt_zero, h_Q_pow_p_eq_one⟩ := Q_order_finite
  apply Exists.intro p
  apply And.intro h_p_gt_zero
  simp only [h_Q_pow_p_eq_one, pow_add, mul_one, pow_one, forall_const]

/-- Periods `p(m)` of `fib (mod m > 2)` are even. -/
theorem fib_period_even [Mod] [hm : Fact (Mod.n > 2)] (p : ℕ) (hp : Function.Periodic fib p) : Even p := by
  have h_order : Q ^ p = 1 := (fib_period_iff_Q_order p).mp hp
  have h_det_pow : Q.det ^ p = 1 := by rw [←Matrix.det_pow Q p, h_order, Matrix.det_one]
  rw [Q_det_eq_neg_one] at h_det_pow
  rw [neg_one_pow_eq_one_iff_even] at h_det_pow
  exact h_det_pow
  exact @ZMod.neg_one_ne_one Mod.n hm

/-- Pisano periods for `m ≥ 1`.
These are defined as the minimum non-zero period of `fib`. -/
noncomputable def pisano_ge_one (m : ℕ) {hm : m ≥ 1} : ℕ :=
    Set.IsWf.min wellFounded_lt (@fib_periodic (Mod.mk m) (Fact.mk hm))

theorem pisano_ge_one_min (m : ℕ) {hm : m ≥ 1} (p : ℕ) :
  @pisano_ge_one m hm = p ↔
    p > 0 ∧
    Function.Periodic (@fib (Mod.mk m)) p ∧
    ∀ p' < p, p' > 0 → ¬Function.Periodic (@fib (Mod.mk m)) p'
  := by
  sorry

/-- The [Pisano Period](https://en.wikipedia.org/wiki/Pisano_period).
This is the period of the Fibonacci sequence mod `m ≥ 1`, or `0` if `m = 0`. -/
noncomputable def pisano (m : ℕ) : ℕ := 
  if h : m ≥ 1 then
    @pisano_ge_one m h
  else
    0

def pisano_ge_one_eq (m : ℕ) {hm : m ≥ 1} : pisano m = @pisano_ge_one m hm := by
  rw [pisano, dif_pos hm]

theorem pisano_is_period [Mod] [hm : Fact (Mod.n ≥ 1)] : (pisano Mod.n > 0) ∧ Function.Periodic fib (pisano Mod.n) := by
  have hmem : pisano Mod.n ∈ { p : ℕ | p > 0 ∧ Function.Periodic fib p } := by
    rw [pisano, dif_pos hm.out, pisano_ge_one]
    apply Set.IsWf.min_mem
  rw [Set.mem_setOf_eq] at hmem
  exact hmem

theorem pisano_one : pisano 1 = 1 := by
  rw [pisano, dif_pos (by rfl), pisano_ge_one_min]
  apply And.intro Nat.one_pos
  apply And.intro
  swap
  intro p' hp'_lt_one hp'_gt_zero
  have hp'_le_zero : p' ≤ 0 := Nat.lt_succ.1 hp'_lt_one
  have contradiction := hp'_le_zero.not_lt hp'_gt_zero
  contradiction

  rw [Function.Periodic]
  intro n
  simp only [Fin.eq_zero]

theorem pisano_two : pisano 2 = 3 := sorry

theorem pisano_even (m : ℕ) {hm : m > 2}: Even (pisano m) := by
  let mod : Mod := Mod.mk m
  let hm : Fact (mod.n > 2) := Fact.mk hm

  have : Fact (Mod.n ≥ 1) := Fact.mk (Nat.one_le_of_lt hm.out)
  exact fib_period_even (pisano m) pisano_is_period

end FibMod

example (a b : ZMod 1) : a = b := by exact?