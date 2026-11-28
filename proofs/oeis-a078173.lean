import OMAStatements.S_oeis_a078173
import Mathlib

/-!
# OEIS A078173: extreme solutions of `r s t = n (r + s + t)` with `r ≤ s ≤ t`

Rewrite the equation as `t (r s - n) = n (r + s)`. The right side is positive, so
`d = r s - n ≥ 1`.

* **Largest `t`.** Since `(r - 1)(s - 1) ≥ 0` we have `r + s ≤ r s + 1 = n + d + 1`, hence
  `t d ≤ n (n + d + 1) ≤ n (n + 2) d` (the last step is `n (n + 1)(d - 1) ≥ 0`), so
  `t ≤ n (n + 2)`. Equality holds for `(r, s, t) = (1, n + 1, n (n + 2))`.
* **Largest `s`.** From `s ≤ t` we get `s (r s - n) ≤ n (r + s)`. If `s ≥ 2n + 1` then
  `r s - 2n ≥ r`, so `s (r s - 2n) ≥ r s ≥ (2n + 1) r > n r`, contradicting the previous
  inequality. Equality `s = 2n` holds for `(r, s, t) = (1, 2n, 2n + 1)`.
-/

open OMA.S_oeis_a078173

namespace OMA.A078173

/-- Both bounds, over the integers. -/
lemma bounds (N R S T : ℤ) (hN : 1 ≤ N) (hR : 1 ≤ R) (hRS : R ≤ S) (hST : S ≤ T)
    (h : R * S * T = N * (R + S + T)) : T ≤ N * (N + 2) ∧ S ≤ 2 * N := by
  have hS : 1 ≤ S := le_trans hR hRS
  have hT : 1 ≤ T := le_trans hS hST
  have hTD : T * (R * S - N) = N * (R + S) := by linear_combination h
  -- `d = r s - n` is positive
  have hD : 0 < R * S - N := by
    by_contra hcon
    have hle : R * S - N ≤ 0 := not_lt.mp hcon
    have h1 : 0 < N * (R + S) := mul_pos (by linarith) (by linarith)
    nlinarith
  constructor
  · -- `t ≤ n (n + 2)`
    have h1 : 0 ≤ N * (R * S + 1 - (R + S)) := by
      have : 0 ≤ (R - 1) * (S - 1) := mul_nonneg (by linarith) (by linarith)
      exact mul_nonneg (by linarith) (by nlinarith)
    have h2 : 0 ≤ N * (N + 1) * (R * S - N - 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have h3 : T * (R * S - N) ≤ N * (N + 2) * (R * S - N) := by
      rw [hTD]
      nlinarith
    exact le_of_mul_le_mul_right h3 hD
  · -- `s ≤ 2n`
    by_contra hcon
    have hS2 : 2 * N + 1 ≤ S := by omega
    have h1 : S * (R * S - N) ≤ N * (R + S) := by
      rw [← hTD]
      exact mul_le_mul_of_nonneg_right hST hD.le
    have h2 : (2 * N + 1) * R ≤ S * R := mul_le_mul_of_nonneg_right hS2 (by linarith)
    have h3 : R ≤ R * S - 2 * N := by
      have : 0 ≤ N * (R - 1) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have h4 : S * R ≤ S * (R * S - 2 * N) := mul_le_mul_of_nonneg_left h3 (by linarith)
    have h5 : 0 < N * R := mul_pos (by linarith) (by linarith)
    nlinarith

end OMA.A078173

open OMA.A078173 in
theorem OMA.solution : type_of% @OMA.S_oeis_a078173.main := by
  intro n hn
  constructor
  · constructor
    · exact ⟨1, n + 1, by norm_num, by omega, by nlinarith, by ring⟩
    · rintro t ⟨r, s, hr, hrs, hst, h⟩
      have hb := (bounds (n : ℤ) r s t (by exact_mod_cast hn) (by exact_mod_cast hr)
        (by exact_mod_cast hrs) (by exact_mod_cast hst) (by exact_mod_cast h)).1
      exact_mod_cast hb
  · constructor
    · exact ⟨1, 2 * n + 1, by norm_num, by omega, by omega, by ring⟩
    · rintro s ⟨r, t, hr, hrs, hst, h⟩
      have hb := (bounds (n : ℤ) r s t (by exact_mod_cast hn) (by exact_mod_cast hr)
        (by exact_mod_cast hrs) (by exact_mod_cast hst) (by exact_mod_cast h)).2
      exact_mod_cast hb
