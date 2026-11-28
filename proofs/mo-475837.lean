import OMAStatements.S_mo_475837
import Mathlib

/-!
MathOverflow 475837: following Zach Hunter's comment, take a long progression in the range of
`s`; its last two terms `x = s i < y = s j` satisfy `y < L x` once the progression is long, and
`s (i + 1) ≤ s j`, so `k = i` works.
-/

namespace OMA.P475837

theorem proof_aux : ∀ s : ℕ → ℕ, StrictMono s →
    (∀ m : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ j < m, a + j * d ∈ Set.range s) →
    ∀ L : ℝ, 1 < L → ∃ k : ℕ, (s (k + 1) : ℝ) < L * s k := by
  intro s hs hap L hL
  set M : ℕ := ⌈1 / (L - 1)⌉₊ + 1 with hM
  obtain ⟨a, d, hd, h⟩ := hap (M + 2)
  obtain ⟨i, hi⟩ := h M (by omega)
  obtain ⟨j, hj⟩ := h (M + 1) (by omega)
  have hij : i < j := by
    rw [← hs.lt_iff_lt, hi, hj]; nlinarith
  refine ⟨i, ?_⟩
  have h1 : (s (i + 1) : ℝ) ≤ s j := by exact_mod_cast hs.monotone hij
  rw [hi]; rw [hj] at h1
  have hL1 : 0 < L - 1 := by linarith
  have hc : 1 / (L - 1) ≤ (⌈1 / (L - 1)⌉₊ : ℝ) := Nat.le_ceil _
  have hMr : (M : ℝ) = ⌈1 / (L - 1)⌉₊ + 1 := by rw [hM]; push_cast; ring
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have key : 1 < (L - 1) * M := by
    rw [hMr]
    have : (L - 1) * (1 / (L - 1)) = 1 := by field_simp
    nlinarith
  push_cast at h1 ⊢
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith

end OMA.P475837

theorem OMA.solution : type_of% @OMA.S_mo_475837.main := OMA.P475837.proof_aux
