import OMAStatements.S_oeis_a127751
import Mathlib

/-!
# A127751: row sums of the inverse triangle, and their parity

The row sums of `(triangle N)⁻¹` form the vector `a` with `triangle N *ᵥ a = 1`, i.e.
`∑_{⌈n/2⌉ ≤ k ≤ n} a k = 3n + 1`. Differencing two consecutive rows gives `a 0 = 1`, `a n = 3` for
even `n > 0`, and `a n = 3 + a ((n-1)/2)` for odd `n` (`b`, `window`). The triangle is lower
triangular with nonzero diagonal, so it is invertible and `a = b`. By induction `b n` is odd
exactly when `v_2(2(n+1))` is odd (`parity`).
-/

namespace OMA.A127751Proof
open OMA.S_oeis_a127751 Matrix

/-- The row sums: `b 0 = 1`, `b n = 3` for even `n > 0`, `b n = 3 + b ((n - 1) / 2)` for odd `n`. -/
def b : ℕ → ℤ
  | 0 => 1
  | n + 1 => if (n + 1) % 2 = 0 then 3 else 3 + b (n / 2)
decreasing_by omega

/-- `∑_{⌈n/2⌉ ≤ k ≤ n} b k = 3n + 1`, i.e. `b` solves `triangle · b = 1`. -/
lemma window (n : ℕ) : ∑ k ∈ Finset.Icc ((n + 1) / 2) n, b k = 3 * n + 1 := by
  induction n with
  | zero => simp [b]
  | succ n ih =>
    rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · -- n = 2j even: n + 1 odd, the window loses `b j` and gains `b (n+1)`
      have hb : b (j + j + 1) = 3 + b j := by
        rw [b, if_neg (by omega), show (j + j) / 2 = j by omega]
      rw [show (j + j + 1 + 1) / 2 = j + 1 by omega]
      rw [show (j + j + 1) / 2 = j by omega] at ih
      have h1 := Finset.sum_Icc_succ_top (show j ≤ j + j + 1 by omega) b
      have h2 := Finset.add_sum_Ioc_eq_sum_Icc (f := b) (show j ≤ j + j + 1 by omega)
      rw [← Finset.Icc_add_one_left_eq_Ioc] at h2
      push_cast at ih ⊢
      linarith
    · -- n = 2j+1 odd: n + 1 even, the window gains `b (n+1) = 3`
      have hb : b (2 * j + 1 + 1) = 3 := by rw [b, if_pos (by omega)]
      rw [show (2 * j + 1 + 1 + 1) / 2 = j + 1 by omega]
      rw [show (2 * j + 1 + 1) / 2 = j + 1 by omega] at ih
      rw [Finset.sum_Icc_succ_top (by omega), ih, hb]
      push_cast
      ring

lemma parity : ∀ n : ℕ, b n % 2 = (A035263 (n + 1) : ℤ)
  | 0 => by
    have h : padicValNat 2 (2 * (0 + 1)) = 1 := by simp
    have h0 : b 0 = 1 := by rw [b]
    rw [A035263, h, h0]; rfl
  | n + 1 => by
    rcases Nat.even_or_odd (n + 1) with he | ho
    · have he' := Nat.even_iff.mp he
      have hb : b (n + 1) = 3 := by rw [b, if_pos he']
      have hv : padicValNat 2 (2 * (n + 1 + 1)) = 1 := by
        rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
          padicValNat.eq_zero_of_not_dvd (by omega)]
      rw [hb, A035263, hv]; rfl
    · have ho' := Nat.odd_iff.mp ho
      have hb : b (n + 1) = 3 + b (n / 2) := by rw [b, if_neg (by omega)]
      have ih := parity (n / 2)
      have hv : padicValNat 2 (2 * (n + 1 + 1)) = 1 + padicValNat 2 (2 * (n / 2 + 1)) := by
        rw [show 2 * (n + 1 + 1) = 2 * (2 * (n / 2 + 1)) by omega,
          padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
      rw [hb, A035263, hv]
      rw [A035263] at ih
      generalize padicValNat 2 (2 * (n / 2 + 1)) = v at ih ⊢
      push_cast at ih ⊢
      omega

lemma det_ne (N : ℕ) : (triangle N).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular (triangle N) (fun i j hij => by
    simp only [triangle]
    rw [if_neg]
    intro h
    have : (j : ℕ) ≤ i := h.1
    exact absurd hij (not_lt.mpr (by exact_mod_cast this)))]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  simp only [triangle, le_refl, true_and]
  rw [if_pos (by omega)]
  positivity

lemma mul_b (N : ℕ) : triangle N *ᵥ (fun k : Fin N => (b k : ℚ)) = fun _ => 1 := by
  funext n
  simp only [mulVec, dotProduct, triangle]
  have hw := window n
  have hset : (Finset.range N).filter (fun k => k ≤ (n : ℕ) ∧ (n : ℕ) ≤ 2 * k) =
      Finset.Icc (((n : ℕ) + 1) / 2) n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    have := n.2
    omega
  have hs : ∑ k : Fin N, (if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 / (3 * (n : ℚ) + 1) else 0) *
      (b k : ℚ) = (1 / (3 * (n : ℚ) + 1)) * ∑ k ∈ Finset.Icc (((n : ℕ) + 1) / 2) n, (b k : ℚ) := by
    rw [Finset.mul_sum, ← hset, Finset.sum_filter]
    rw [Fin.sum_univ_eq_sum_range (fun k => (if k ≤ (n : ℕ) ∧ (n : ℕ) ≤ 2 * k then
      1 / (3 * (n : ℚ) + 1) else 0) * (b k : ℚ)) N]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [hs]
  have hq : ∑ k ∈ Finset.Icc (((n : ℕ) + 1) / 2) n, (b k : ℚ) = 3 * (n : ℚ) + 1 := by
    exact_mod_cast hw
  rw [hq]
  field_simp

theorem main' : ∀ (N : ℕ) (n : Fin N),
    ∃ m : ℤ, a N n = m ∧ m % 2 = (A035263 ((n : ℕ) + 1) : ℤ) := by
  intro N n
  refine ⟨b n, ?_, parity n⟩
  have hu : IsUnit (triangle N).det := isUnit_iff_ne_zero.mpr (det_ne N)
  have h1 : (triangle N)⁻¹ *ᵥ (fun _ : Fin N => (1 : ℚ)) = fun k : Fin N => (b k : ℚ) := by
    rw [← mul_b N, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have h2 := congrFun h1 n
  simp only [mulVec, dotProduct, mul_one] at h2
  exact h2

end OMA.A127751Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a127751.main := OMA.A127751Proof.main'
