import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic


section

open scoped BigOperators

-- # Task 1
theorem sum_power_one (n : ℕ) : ∑ i in Finset.range n, i = n * (n - 1) / 2 := by
  -- proving with induction
  induction' n with k hk
  · rw [Finset.range_zero, Finset.sum_empty]
    norm_num
  · rw [Finset.sum_range_succ, hk, Nat.succ_eq_add_one]
    rw [Nat.triangle_succ]

-- # Task 2
theorem sum_power_two (n : ℕ) : ∑ i in Finset.range (n+1), i^2 = n * (n + 1) * (2 * n + 1) / 6 := by
  -- adding new theorem to get out of division
  have mul6 (a b c : ℕ) (h : a + 6 * c = b) : a / 6 + c = b / 6 := by
    rw [h.symm, Nat.mul_comm]
    have h' : 0 < 6 := by norm_num
    rw [Nat.add_mul_div_right a c h']
  -- solving by induction
  induction' n with k hk
  · rw [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  rw [Finset.sum_range_succ, hk, Nat.succ_eq_add_one]
  apply mul6; ring

-- # Task 3
theorem sum_power_three (n : ℕ) : ∑ i in Finset.range (n + 1), i^3 = (∑ i in Finset.range (n+1), i)^2 := by
  -- adding new theorem to get out of division
  have hsq (k : ℕ) : (2 * k) ^ 2 = k ^ 2 * 4 := by
    ring
  have hmul (a b c : ℕ) (ha : Even a) (hb : Even b)
    (h : a^2 + c^3*4 = b^2) :
    (a/2)^2 + c^3 = (b/2)^2 := by
    -- (x : ℕ) Even x → x = 2 * x'
    rcases ha.two_dvd with ⟨a', rfl⟩
    rcases hb.two_dvd with ⟨b', rfl⟩
    -- reducing by 2
    rw [Nat.mul_div_cancel_left, Nat.mul_div_cancel_left]
    rw [hsq a', hsq b'] at h
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 4)
    rw [Nat.add_mul]
    exact h; linarith; linarith
  -- solving by induction
  induction' n with k hk
  · repeat rw [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  rw [Finset.sum_range_succ, hk, Nat.succ_eq_add_one]
  repeat rw [sum_power_one]
  simp
  apply hmul ((k+1)*k) ((k+1+1)*(k+1)) (k+1)
  · rw [Nat.mul_comm]
    exact Nat.even_mul_succ_self k
  · rw [Nat.mul_comm]
    exact Nat.even_mul_succ_self (k+1)
  ring

-- # Task 4
theorem sum_two_powers (n : ℕ) : ∑ i in Finset.range n, 2^i = 2^n - 1 := by
  have hle (k : ℕ) : 1 ≤ 2^k := by
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [Nat.pow_succ, Nat.mul_comm]
      have h2 : 2 ≤ 2 * 2^k := Nat.mul_le_mul_left 2 ih
      have : 1 ≤ 2 := by decide
      exact Nat.le_trans this h2
  -- solving by induction
  induction' n with d hd
  · rw [Finset.range_zero, Finset.sum_empty]
    norm_num
  rw [Finset.sum_range_succ, hd, Nat.succ_eq_add_one]
  rw [Nat.pow_succ, mul_comm, two_mul]
  rw [add_comm (2 ^ d - 1) (2 ^ d)]
  rw [← Nat.add_sub_assoc]; exact hle d

end
