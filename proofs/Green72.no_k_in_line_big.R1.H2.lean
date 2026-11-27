import OMAReductions.R_Green72_no_k_in_line_big_R1
import Mathlib

-- Step Green72.no_k_in_line_big.R1.H2: hypothesis H2 of reduction Green72.no_k_in_line_big.R1
-- Credit: @ivillar

/-!
# Line counts with small integer coefficients certify an allowed set

If `k ≥ 2` points of the grid are collinear, take two of them, `p ≠ q`. All of the points lie on
the integer line `a x + b y = c` with `a = q.2 - p.2` and `b = p.1 - q.1`, whose coefficients are
smaller than `N` in absolute value and not both zero, so that line would carry `k` points of `s`.
-/

namespace Green72CertifyStep

open Finset Green72

theorem certify : ∀ (k N : ℕ) (s : Finset (ℕ × ℕ)), 2 ≤ k →
  s ⊆ (range N ×ˢ range N) → (∀ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0) → -(N : ℤ) < a → a < N → -(N : ℤ) < b → b < N →
    (s.filter (fun i ↦ a * i.1 + b * i.2 = c)).card ≤ k - 1) → AllowedSet k N s := by
  intro k N s hk hs hline
  have hbd : ∀ i ∈ s, i.1 < N ∧ i.2 < N := by
    intro i hi
    have h := mem_product.mp (hs hi)
    exact ⟨mem_range.mp h.1, mem_range.mp h.2⟩
  refine ⟨hbd, ?_⟩
  intro t hts htk hcol
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < t.card)
  have hPmem : (((p.1 : ℝ), (p.2 : ℝ)) : ℝ × ℝ) ∈
      ({r | ∃ i ∈ t, r = ((↑i.1 : ℝ), (↑i.2 : ℝ))} : Set (ℝ × ℝ)) := ⟨p, hp, rfl⟩
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem hPmem).mp hcol
  have hcoord : ∀ i ∈ t, ∃ r : ℝ, (i.1 : ℝ) = r * v.1 + p.1 ∧ (i.2 : ℝ) = r * v.2 + p.2 := by
    intro i hi
    obtain ⟨r, hr⟩ := hv _ ⟨i, hi, rfl⟩
    refine ⟨r, ?_, ?_⟩
    · have h := congrArg Prod.fst hr
      simpa using h
    · have h := congrArg Prod.snd hr
      simpa using h
  obtain ⟨rq, hq1, hq2⟩ := hcoord q hq
  have hall : ∀ i ∈ t, ((q.2 : ℤ) - (p.2 : ℤ)) * (i.1 : ℤ) + ((p.1 : ℤ) - (q.1 : ℤ)) * (i.2 : ℤ) =
      ((q.2 : ℤ) - (p.2 : ℤ)) * (p.1 : ℤ) + ((p.1 : ℤ) - (q.1 : ℤ)) * (p.2 : ℤ) := by
    intro i hi
    obtain ⟨r, hi1, hi2⟩ := hcoord i hi
    have h : ((q.2 : ℝ) - (p.2 : ℝ)) * (i.1 : ℝ) + ((p.1 : ℝ) - (q.1 : ℝ)) * (i.2 : ℝ) =
        ((q.2 : ℝ) - (p.2 : ℝ)) * (p.1 : ℝ) + ((p.1 : ℝ) - (q.1 : ℝ)) * (p.2 : ℝ) := by
      rw [hi1, hi2, hq1, hq2]
      ring
    exact_mod_cast h
  have hpb := hbd p (hts hp)
  have hqb := hbd q (hts hq)
  have hne : ((q.2 : ℤ) - (p.2 : ℤ)) ≠ 0 ∨ ((p.1 : ℤ) - (q.1 : ℤ)) ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hpq (Prod.ext (by omega) (by omega))
  have hcard := hline ((q.2 : ℤ) - (p.2 : ℤ)) ((p.1 : ℤ) - (q.1 : ℤ))
    (((q.2 : ℤ) - (p.2 : ℤ)) * (p.1 : ℤ) + ((p.1 : ℤ) - (q.1 : ℤ)) * (p.2 : ℤ)) hne
    (by omega) (by omega) (by omega) (by omega)
  have hsub : t ⊆ s.filter (fun i ↦ ((q.2 : ℤ) - (p.2 : ℤ)) * (i.1 : ℤ) +
      ((p.1 : ℤ) - (q.1 : ℤ)) * (i.2 : ℤ) =
      ((q.2 : ℤ) - (p.2 : ℤ)) * (p.1 : ℤ) + ((p.1 : ℤ) - (q.1 : ℤ)) * (p.2 : ℤ)) :=
    fun i hi => mem_filter.mpr ⟨hts hi, hall i hi⟩
  have h2 := Finset.card_le_card hsub
  omega

end Green72CertifyStep

theorem OMA.solution : OMA.R_Green72_no_k_in_line_big_R1.H2 :=
  Green72CertifyStep.certify
