import OMAStatements.S_oeis_a284005
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
Binomial proof for OEIS A284005: binary digit sums satisfy weight (2*x) = weight x
and weight (2*x + 1) = weight x + 1, yielding a (2^k * x) = (1 + weight x)^k * a x
and turning the RHS into the binomial expansion of (2 + weight n)^(m + 1) * a n.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a284005.main := by
  intro m n
  let w := OMA.S_oeis_a284005.weight
  let a := OMA.S_oeis_a284005.a
  have hw0 : w 0 = 0 := rfl
  have hw2 : ∀ x : ℕ, w (2 * x) = w x := by
    intro x
    by_cases hx : x = 0
    · subst hx; rfl
    · dsimp [w, OMA.S_oeis_a284005.weight]
      rw [show 2 * x = 0 + 2 * x by omega, Nat.digits_add 2 (by omega) 0 x (by omega) (Or.inr hx)]
      simp
  have hw21 : ∀ x : ℕ, w (2 * x + 1) = w x + 1 := by
    intro x
    dsimp [w, OMA.S_oeis_a284005.weight]
    rw [show 2 * x + 1 = 1 + 2 * x by omega,
      Nat.digits_add 2 (by omega) 1 x (by omega) (Or.inl (by omega))]
    simp [Nat.add_comm]
  have hw_pow2 : ∀ k x : ℕ, w (2 ^ k * x) = w x := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, hw2, ih]
  have ha0 : a 0 = 1 := by
    dsimp [a]
    unfold OMA.S_oeis_a284005.a
    simp
  have ha_step : ∀ z : ℕ, z ≠ 0 → a z = (1 + w z) * a (z / 2) := by
    intro z hz
    dsimp [a, w]
    conv_lhs => unfold OMA.S_oeis_a284005.a
    simp [hz]
  have ha_pow2 : ∀ k x : ℕ, a (2 ^ k * x) = (1 + w x) ^ k * a x := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih =>
      by_cases hx : x = 0
      · subst hx
        simp [ha0, hw0]
      · have hy : 2 ^ k * x ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ (by omega)) hx
        have h2y : 2 ^ (k + 1) * x = 2 * (2 ^ k * x) := by ring
        rw [h2y, ha_step (2 * (2 ^ k * x)) (by omega), hw2, hw_pow2,
          show (2 * (2 ^ k * x)) / 2 = 2 ^ k * x by omega, ih]
        ring
  have ha_odd : a (2 ^ m * (2 * n + 1)) = (2 + w n) ^ (m + 1) * a n := by
    rw [ha_pow2 m (2 * n + 1), ha_step (2 * n + 1) (by omega), hw21,
      show (2 * n + 1) / 2 = n by omega]
    ring
  have hrhs : ∑ k ∈ Finset.range (m + 2), Nat.choose (m + 1) k * a (2 ^ k * n) =
      (2 + w n) ^ (m + 1) * a n := by
    calc ∑ k ∈ Finset.range (m + 2), Nat.choose (m + 1) k * a (2 ^ k * n)
        = ∑ k ∈ Finset.range (m + 2),
            ((1 + w n) ^ k * 1 ^ (m + 1 - k) * Nat.choose (m + 1) k) * a n := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ha_pow2 k n, one_pow, mul_one]
          ring
      _ = (∑ k ∈ Finset.range (m + 2),
            (1 + w n) ^ k * 1 ^ (m + 1 - k) * Nat.choose (m + 1) k) * a n := by
          rw [Finset.sum_mul]
      _ = ((1 + w n) + 1) ^ (m + 1) * a n := by
          rw [add_pow (1 + w n) 1 (m + 1), show m + 1 + 1 = m + 2 by omega]
          simp
      _ = (2 + w n) ^ (m + 1) * a n := by ring
  exact ha_odd.trans hrhs.symm
