import OMAStatements.S_oeis_a059158
import Mathlib

/-!
Credit: @ivillar
Proof: the k-th collapsed element is 4 * 2^(4v) + 16 * 2^(4v) + 4 * 2^(4v) = 24 * 16^v(k),
where v is the 2-adic valuation. Splitting 1..2^(m+1)-1 into odd and even numbers shows that
W(m) = sum of 16^v(k) over 1 <= k < 2^m satisfies W(m+1) = 2^m + 16 W(m), so
W(m) = (16^m - 2^m)/14. Hence a(n) = 24 W(n+1) = 24/7 (8 * 16^n - 2^n). The recurrence and the
generating function follow from this closed form by direct computation.
-/

namespace OMAA059158Helpers
open OMA.S_oeis_a059158 PowerSeries

theorem split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ Finset.range (2 * N + 1), f (k + 1) =
      ∑ j ∈ Finset.range (N + 1), f (2 * j + 1) + ∑ j ∈ Finset.range N, f (2 * j + 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have l1 : ∑ k ∈ Finset.range (2 * (N + 1) + 1), f (k + 1) =
        ∑ k ∈ Finset.range (2 * N + 1), f (k + 1) + f (2 * N + 2) + f (2 * N + 3) := by
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
    have l2 : ∑ j ∈ Finset.range (N + 1 + 1), f (2 * j + 1) =
        ∑ j ∈ Finset.range (N + 1), f (2 * j + 1) + f (2 * N + 3) := Finset.sum_range_succ _ _
    have l3 : ∑ j ∈ Finset.range (N + 1), f (2 * j + 2) =
        ∑ j ∈ Finset.range N, f (2 * j + 2) + f (2 * N + 2) := Finset.sum_range_succ _ _
    rw [l1, l2, l3, ih]
    abel

theorem W (m : ℕ) :
    ∑ k ∈ Finset.range (2 ^ m - 1), (16 : ℚ) ^ (padicValNat 2 (k + 1)) = (16 ^ m - 2 ^ m) / 14 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by
      have := Nat.one_le_two_pow (n := m)
      rw [pow_succ]
      omega
    have e1 : ∀ j : ℕ, padicValNat 2 (2 * j + 1) = 0 := fun j =>
      padicValNat.eq_zero_of_not_dvd (by omega)
    have e2 : ∀ j : ℕ, padicValNat 2 (2 * j + 2) = padicValNat 2 (j + 1) + 1 := by
      intro j
      rw [show 2 * j + 2 = 2 * (j + 1) by ring, padicValNat.mul (by norm_num) (by omega),
        padicValNat_self]
      ring
    rw [h2, split (fun k => (16 : ℚ) ^ (padicValNat 2 k))]
    simp only [e1, e2, pow_zero, pow_succ, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, ← Finset.sum_mul, ih]
    rw [Nat.cast_add, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring

theorem closed (n : ℕ) : (a n : ℚ) = 24 / 7 * (8 * 16 ^ n - 2 ^ n) := by
  have hc : ∀ k, collapsed2 k = 24 * 16 ^ (padicValNat 2 k) := by
    intro k
    have hb : 4 * (padicValNat 2 k + 1 - 1) + 1 = 4 * padicValNat 2 k + 1 := by omega
    have h0 : 4 * padicValNat 2 k + 1 - 1 = 4 * padicValNat 2 k := by omega
    have ht : ∀ t : ℕ, 4 * padicValNat 2 k + 1 + t - 1 = 4 * padicValNat 2 k + t := by
      intro t
      omega
    simp only [collapsed2, element', element, ruler, hb, h0, ht, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    ring
  unfold a
  rw [Nat.cast_sum]
  simp only [hc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.mul_sum, W]
  ring

theorem coeff_mk_mul_X_pow (f : ℕ → ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (f : ℕ → ℚ) (r : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

end OMAA059158Helpers

open OMAA059158Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a059158.main := by
  refine ⟨closed, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
    have key : ((OMA.S_oeis_a059158.a (m + 2) : ℤ) : ℚ) =
        ((18 * OMA.S_oeis_a059158.a (m + 1) - 32 * OMA.S_oeis_a059158.a m : ℤ) : ℚ) := by
      push_cast
      rw [closed (m + 2), closed (m + 1), closed m]
      ring
    exact_mod_cast key
  · ext n
    have hD : ((2 * X - 1) * (16 * X - 1) : PowerSeries ℚ) =
        C 32 * X ^ 2 - C 18 * X ^ 1 + X ^ 0 := by
      rw [map_ofNat C 32, map_ofNat C 18]; ring
    have hN : (24 : PowerSeries ℚ) = C 24 * X ^ 0 := by
      rw [map_ofNat C 24]; ring
    rw [hD, hN]
    simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
      coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> norm_num [closed]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
        show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega,
        show m + 2 - 0 = m + 2 by omega, closed, closed, closed]
      ring
