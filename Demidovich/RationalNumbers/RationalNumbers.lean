import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic


open Real

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
-- making a function for even factorials prod
def doubleFactorialProduct (n : ℕ) : ℕ :=
  (Finset.range n).prod (fun k => Nat.factorial (2 * (k + 1)))

#eval doubleFactorialProduct 3  -- evaluating `2!*4!*6! = 2*24*720 = 34560`

example (n : ℕ) :
