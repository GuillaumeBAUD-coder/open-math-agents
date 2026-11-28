import OMAStatements.S_mo_450392
import Mathlib

-- Problem: mo-450392, the floor of sqrt(n^2) + sqrt(n^2+1) + ... + sqrt((n+1)^2) is the
-- hexagonal number H(n+1) = 2n^2 + 3n + 1.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Lower bound: by concavity sqrt(n^2 + h) >= n + h / (2n + 1) for 0 <= h <= 2n + 1, and these
-- chords sum to exactly 2n^2 + 3n + 1. Upper bound: sqrt(n^2 + h) <= n + h / (2n) for
-- h <= 2n, the last term is n + 1, and the total is 2n^2 + 3n + 3/2 < 2n^2 + 3n + 2.

namespace MO450392

open OMA.S_mo_450392

lemma gauss (m : ℕ) : (∑ h ∈ Finset.range (m + 1), (h : ℝ)) = (m : ℝ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma lower_term (x y : ℝ) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ 2 * x + 1) :
    x + y / (2 * x + 1) ≤ Real.sqrt (x ^ 2 + y) := by
  have hd : (0 : ℝ) < 2 * x + 1 := by linarith
  have hz0 : 0 ≤ y / (2 * x + 1) := div_nonneg hy0 hd.le
  have hz1 : y / (2 * x + 1) ≤ 1 := (div_le_one hd).mpr hy
  have hyz : y = y / (2 * x + 1) * (2 * x + 1) := by field_simp
  have h1 : (x + y / (2 * x + 1)) ^ 2 ≤ x ^ 2 + y := by
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1), hyz]
  calc x + y / (2 * x + 1) = Real.sqrt ((x + y / (2 * x + 1)) ^ 2) :=
        (Real.sqrt_sq (add_nonneg hx hz0)).symm
    _ ≤ Real.sqrt (x ^ 2 + y) := Real.sqrt_le_sqrt h1

lemma upper_term (x y : ℝ) (hx : 0 < x) (hy0 : 0 ≤ y) :
    Real.sqrt (x ^ 2 + y) ≤ x + y / (2 * x) := by
  have hw0 : 0 ≤ y / (2 * x) := div_nonneg hy0 (by linarith)
  have hyw : y = y / (2 * x) * (2 * x) := by field_simp
  have h1 : x ^ 2 + y ≤ (x + y / (2 * x)) ^ 2 := by
    nlinarith [mul_nonneg hw0 hw0, hyw]
  calc Real.sqrt (x ^ 2 + y) ≤ Real.sqrt ((x + y / (2 * x)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = x + y / (2 * x) := Real.sqrt_sq (add_nonneg hx.le hw0)

theorem main_proof : ∀ n : ℕ, 1 ≤ n →
    ⌊∑ h ∈ Finset.range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ))⌋₊
      = hexagonal (n + 1) := by
  intro n hn
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hhex : hexagonal (n + 1) = 2 * n ^ 2 + 3 * n + 1 := by
    unfold hexagonal
    have h : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [h]
    ring
  have hlow : 2 * (n : ℝ) ^ 2 + 3 * n + 1
      ≤ ∑ h ∈ Finset.range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ)) := by
    have h1 : ∑ h ∈ Finset.range (2 * n + 2), ((n : ℝ) + (h : ℝ) / (2 * (n : ℝ) + 1))
        ≤ ∑ h ∈ Finset.range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ)) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [Finset.mem_range] at hh
      apply lower_term _ _ (by linarith) (Nat.cast_nonneg h)
      have h3 : (h : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : h ≤ 2 * n + 1)
      push_cast at h3
      linarith
    have hg : ∑ h ∈ Finset.range (2 * n + 2), (h : ℝ)
        = ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 1) / 2 := gauss (2 * n + 1)
    have h2 : ∑ h ∈ Finset.range (2 * n + 2), ((n : ℝ) + (h : ℝ) / (2 * (n : ℝ) + 1))
        = 2 * (n : ℝ) ^ 2 + 3 * n + 1 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range, hg,
        nsmul_eq_mul]
      have hd : (2 * (n : ℝ) + 1) ≠ 0 := by linarith
      push_cast
      field_simp
      ring
    linarith
  have hup : ∑ h ∈ Finset.range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ))
      < 2 * (n : ℝ) ^ 2 + 3 * n + 1 + 1 := by
    rw [Finset.sum_range_succ]
    have hlast : Real.sqrt ((n : ℝ) ^ 2 + ((2 * n + 1 : ℕ) : ℝ)) = n + 1 := by
      have h : (n : ℝ) ^ 2 + ((2 * n + 1 : ℕ) : ℝ) = ((n : ℝ) + 1) ^ 2 := by
        push_cast
        ring
      rw [h, Real.sqrt_sq (by linarith)]
    have h1 : ∑ h ∈ Finset.range (2 * n + 1), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ))
        ≤ ∑ h ∈ Finset.range (2 * n + 1), ((n : ℝ) + (h : ℝ) / (2 * (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro h _
      exact upper_term _ _ (by linarith) (Nat.cast_nonneg h)
    have h2 : ∑ h ∈ Finset.range (2 * n + 1), ((n : ℝ) + (h : ℝ) / (2 * (n : ℝ)))
        = 2 * (n : ℝ) ^ 2 + 2 * n + 1 / 2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range,
        gauss (2 * n), nsmul_eq_mul]
      have hd : (n : ℝ) ≠ 0 := by linarith
      push_cast
      field_simp
      ring
    rw [hlast]
    linarith
  have hnonneg : 0 ≤ ∑ h ∈ Finset.range (2 * n + 2), Real.sqrt ((n : ℝ) ^ 2 + (h : ℝ)) :=
    Finset.sum_nonneg fun h _ => Real.sqrt_nonneg _
  rw [hhex, Nat.floor_eq_iff hnonneg]
  push_cast
  exact ⟨hlow, hup⟩

end MO450392

theorem OMA.solution : type_of% @OMA.S_mo_450392.main := MO450392.main_proof
