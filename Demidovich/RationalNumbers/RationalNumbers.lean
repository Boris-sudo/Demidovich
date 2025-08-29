import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic


open Real
open scoped BigOperators

-- # Task 5
-- `TODO`

-- # Task 6
-- `TODO`

-- # Task 7
theorem bernoulli (x : ℝ) (n : ℕ) (hx : x ≥ -1) : (1 + x) ^ n ≥ 1 + n * x := by
  induction' n with k hk
  · norm_num
  · have hge : (1+x)^(k+1) ≥ (1+x) * (1+k*x) := by
      rw [pow_succ]
      apply mul_le_mul_of_nonneg_left
      · exact hk
      · linarith [hx]
    have heq : (1+x) * (1+k*x) = (1 + (k+1)*x) + (k*x^2) := by ring
    have hge₂ : (1 + (k+1)*x) + (k*x^2) ≥ (1 + (k+1)*x) := by
      nth_rw 2 [← add_zero (1 + (k+1)*x)]
      apply add_le_add_left
      apply mul_nonneg
      exact Nat.cast_nonneg k
      exact sq_nonneg x
    rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    rw [heq] at hge
    exact ge_trans hge hge₂

-- # Task 8
theorem factorial_pow (n : ℕ) (hn : 1 ≤ n) : Nat.factorial n < (n+1)^n := by
  induction n with
  | zero => cases hn
  | succ n ih =>
    by_cases hn_eq_zero : n = 0
    · -- case n = 0
      subst hn_eq_zero
      simp [Nat.factorial]
    · -- case n ≥ 1
      rw [Nat.succ_eq_add_one] at *
      specialize ih (Nat.pos_of_ne_zero hn_eq_zero)
      -- adding new theorem for (0 < n+1)
      have h_zero_lt : 0 < n+1 := Nat.succ_le_iff.mp hn
      -- final theorem proving steps
      calc
      Nat.factorial (n+1) = (n+1) * Nat.factorial n := by rw [Nat.factorial_succ]
      _ < (n+1) * (n+1) ^ n := by
        apply (mul_lt_mul_left h_zero_lt).2 ih
      _ = (n+1) ^ (n+1) := by rw [← pow_succ]
      _ < (n+1+1) ^ (n+1) := by
        apply Nat.pow_lt_pow_of_lt_left
        · exact Nat.lt_succ_self (n + 1)
        · exact h_zero_lt

-- # Task 9
@[simp]
def doubleFactorialProduct (n : ℕ) : ℕ :=
  (Finset.range n).prod (fun k => Nat.factorial (2 * (k + 1)))

#eval doubleFactorialProduct 3  -- evaluating `2!*4!*6! = 2*24*720 = 34560`

example (n : ℕ) (hn : 1 < n) : doubleFactorialProduct n > (Nat.factorial (n+1))^n := by
  induction n with
  | zero => cases hn
  | succ n ih =>
    by_cases hn_eq_zero_or_one : n = 0 ∨ n = 1
    · -- case `n = 0 ∨ n = 1`
      rcases hn_eq_zero_or_one with (hn_eq_zero | hn_eq_one)
      · --case `n = 0`
        subst hn_eq_zero
        simp at hn
      · -- case `n = 1`
        subst hn_eq_one
        rw [Nat.succ_eq_add_one] at *
        norm_num
    · -- case `n ≥ 1`
      rw [Nat.succ_eq_add_one] at *
      push_neg at hn_eq_zero_or_one
      rcases hn_eq_zero_or_one with ⟨hn_not_zero, hn_not_one⟩
      -- new theorems
      have hn_ge_zero : 0 < n + 1 := by
        exact Nat.zero_lt_succ n
      have hn_ge_one : 1 < n := by
        by_contra
        interval_cases n <;> contradiction
      have h_lt : (n+1) < 2*(n+1) := by linarith
      have h_zero_lt : 0 < Nat.factorial (2 * (n + 1)) := by
        exact Nat.factorial_pos (2*(n+1))
      -- specialize
      specialize ih hn_ge_one
      simp only [doubleFactorialProduct] at *
      -- calculating final solution
      calc
      (Finset.prod (Finset.range (n + 1)) fun k ↦ Nat.factorial (2 * (k + 1))) = (Finset.prod (Finset.range n) fun x ↦ Nat.factorial (2 * (x + 1))) * Nat.factorial (2 * (n + 1)) := by
        rw [Finset.prod_range_succ]
      _ > Nat.factorial (n + 1) ^ n * Nat.factorial (2 * (n + 1)) := by
        apply (mul_lt_mul_right h_zero_lt).2 ih
      _ > Nat.factorial (n + 1 + 1) ^ (n + 1) := by
        rw [Nat.factorial_succ (n+1)]
        rw [Nat.mul_pow]
        rw [pow_succ (Nat.factorial (n + 1)), ← mul_assoc, mul_comm _ (Nat.factorial (n+1) ^ n)]
        -- removing Nat.factorial (n+1) ^ n
        apply (mul_lt_mul_left (pow_pos (Nat.factorial_pos (n+1)) n)).2
        -- normalizing view
        rw [pow_succ, mul_comm (n+1+1), mul_assoc, ← Nat.factorial_succ (n+1), Nat.succ_eq_add_one]
        ring
        rw [mul_two, ← add_assoc,]
        --
        calc
        Nat.factorial (2 + n) * (2 + n) ^ n < Nat.factorial (2 + n) * Nat.succ (2 + n) ^ n := by
          apply (mul_lt_mul_left (Nat.factorial_pos (2+n))).2
          apply Nat.pow_lt_pow_of_lt_left
          · linarith
          · linarith
        _ ≤ Nat.factorial ((2 + n) + n) := by
          exact Nat.factorial_mul_pow_le_factorial
        _ = Nat.factorial (2 + n + n) := by ring

-- # Task 10
@[simp]
def odd_over_even_prod (n : ℕ) : ℚ :=
  (Finset.range n).prod (fun i => ((2*i+1 : ℚ)/(2*i+2 : ℚ)))

#eval odd_over_even_prod 2

example (n : ℕ) (hn : 1 ≤ n) : odd_over_even_prod n < 1 / ((2*n+1) : ℚ)^(1/2) := by
  induction n with
  | zero => cases hn
  | succ n ih =>
    by_cases hn_eq_zero : n = 0
    · -- case `n = 0`
      subst hn_eq_zero
      norm_num
    · -- case `n ≥ 1`
      push_neg at hn_eq_zero
      rw [Nat.succ_eq_add_one] at *
      -- additional theorems
      have hn_ge_one : 1 ≤ n := Nat.pos_of_ne_zero hn_eq_zero
      -- working with other theorems
      specialize ih hn_ge_one
      simp only [odd_over_even_prod] at *
      -- solution
      rw [Finset.prod_range_succ]
      sorry

-- # Task 10.1.a

theorem sq_le_sq'' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 → a < b := by
  intro hsq
  have h' := sq_lt_sq.mp hsq
  rw [abs_of_nonneg ha, abs_of_nonneg hb] at h'
  exact h'

theorem h_sqrt (n : ℝ) : sqrt n = n / sqrt n := by
  simp only [div_sqrt]

example (n : ℕ) (hn : n ≥ 2) : ∑ i in Finset.range n, 1 / Real.sqrt (i + 1) > Real.sqrt n := by
  induction n with
  | zero => cases hn
  | succ n ih =>
    by_cases hn_eq : n = 0 ∨ n = 1
    · -- case `n = 0 ∨ n = 1`
      rcases hn_eq with (rfl | rfl)
      · -- case `n = 0`
        contradiction
      · -- case `n = 1`
        rw [Nat.succ_eq_add_one] at *
        repeat rw [Finset.sum_range_succ]
        simp; norm_num
        -- square both parts
        apply sq_le_sq''
        · exact sqrt_nonneg 2
        · exact add_nonneg (by norm_num) (inv_nonneg.mpr (sqrt_nonneg 2))
        -- solving for squared
        ring
        field_simp [ne_of_gt (by norm_num : (0 : ℝ) < sqrt 2)]
        rw [add_mul, mul_two]
        ring; norm_num
        rw [← sub_lt_iff_lt_add']
        norm_num
        -- square both parts
        apply sq_le_sq''
        · norm_num
        · exact sqrt_nonneg 2
        ring; norm_num
    · -- case `n > 1`
      rw [Nat.succ_eq_add_one]
      push_neg at hn_eq
      rcases hn_eq with ⟨hn_not_zero, hn_not_one⟩
      -- additional theorems
      have hn_ge_two : n ≥ 2 := by
        by_contra
        interval_cases n <;> contradiction
      have hn_le_zero : (n : ℝ) > 0 := by
        apply Nat.cast_pos.mpr
        linarith [hn]
      have hn_le_zero₁ : ((n : ℝ) + 1) > 0 := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        apply Nat.cast_pos.mpr
        exact Nat.succ_pos n
      -- specializing other theorems
      specialize ih hn_ge_two
      -- solution
      calc
      ∑ i in Finset.range (n + 1), 1 / sqrt (i + 1) = ∑ x in Finset.range n, 1 / sqrt (x + 1) + 1 / sqrt (n + 1) := by
        rw [Finset.sum_range_succ]
      _ > sqrt n + 1 / sqrt (n + 1) := by
        apply add_lt_add_right ih
      _ > sqrt ↑(n + 1) := by
        -- sqrt n = n / sqrt n
        rw [h_sqrt, h_sqrt ↑(n+1)]
        apply sub_pos.mp
        have : 1 / sqrt (↑n + 1) - ↑(n + 1) / sqrt ↑(n + 1) = (1 - (n+1)) / sqrt (n+1) := by
          rw [sub_div]
          repeat rw [Nat.cast_add, Nat.cast_one]
        rw [← add_sub, this, sub_add_cancel'', neg_div, ← sub_eq_add_neg]
        -- moving n / sqrt(n+1) to the left
        rw [lt_sub_iff_add_lt, zero_add]
        -- transforming to mul
        rw [div_eq_inv_mul, div_eq_inv_mul]
        -- removing n
        apply (mul_lt_mul_right hn_le_zero).mpr
        -- removing inv
        apply (inv_lt_inv (sqrt_pos.mpr hn_le_zero₁) (sqrt_pos.mpr hn_le_zero)).mpr
        -- removing sqrt
        apply sqrt_lt_sqrt
        · exact Nat.cast_nonneg n
        · linarith

#check sqrt_pos.mpr
#check inv_lt_inv
