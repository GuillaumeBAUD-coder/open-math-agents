import OMAReductions.R_LittlewoodConjecture_padic_littlewood_conjecture_R1

-- If n * dist(n alpha, Z) is arbitrarily small for infinitely many n, then liminf n |n|_p dist(n alpha, Z) = 0.
-- Original Lean proof of the classical remark that the p-adic Littlewood conjecture is only open for badly
-- approximable numbers: the p-adic absolute value of an integer is at most 1, so the terms are below epsilon
-- infinitely often for every epsilon > 0, and they are nonnegative.
-- An elementary case, not progress on the conjecture.

namespace OMA.Padic2

open Filter

theorem well_approximable (α : ℝ) (p : ℕ) (hp : p.Prime)
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, n * distToNearestInt (n * α) < ε) :
    atTop.liminf (fun (n : ℕ) ↦ n * padicNorm p n * distToNearestInt (n * α)) = 0 := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hd0 : ∀ x : ℝ, 0 ≤ distToNearestInt x := fun x => abs_nonneg _
  have hn0 : ∀ q : ℕ, (0 : ℝ) ≤ ((padicNorm p (q : ℚ) : ℚ) : ℝ) := fun q => by
    exact_mod_cast padicNorm.nonneg (q : ℚ)
  have hn1 : ∀ q : ℕ, ((padicNorm p (q : ℚ) : ℚ) : ℝ) ≤ 1 := fun q => by
    exact_mod_cast padicNorm.of_nat (p := p) q
  have hnonneg : ∀ n : ℕ,
      0 ≤ (n : ℝ) * padicNorm p n * distToNearestInt (n * α) := fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (hn0 n)) (hd0 _)
  have hle : ∀ n : ℕ, (n : ℝ) * padicNorm p n * distToNearestInt (n * α) ≤
      (n : ℝ) * distToNearestInt (n * α) := by
    intro n
    have e : (n : ℝ) * padicNorm p n * distToNearestInt (n * α) =
        ((n : ℝ) * distToNearestInt (n * α)) * padicNorm p n := by ring
    rw [e]
    exact mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg n) (hd0 _)) (hn1 n)
  have hfreq : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      (n : ℝ) * padicNorm p n * distToNearestInt (n * α) ≤ ε := fun ε hε =>
    (h ε hε).mono fun n hn => le_trans (hle n) hn.le
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun (n : ℕ) ↦ (n : ℝ) * padicNorm p n * distToNearestInt (n * α)) :=
    isBoundedUnder_of ⟨0, hnonneg⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop
      (fun (n : ℕ) ↦ (n : ℝ) * padicNorm p n * distToNearestInt (n * α)) :=
    IsCoboundedUnder.of_frequently_le (hfreq 1 one_pos)
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    rw [zero_add]
    exact liminf_le_of_frequently_le (hfreq ε hε) hbdd
  · exact le_liminf_of_le hcobdd (Eventually.of_forall hnonneg)

end OMA.Padic2

theorem OMA.solution : OMA.R_LittlewoodConjecture_padic_littlewood_conjecture_R1.H1 := by
  intro α p hp h
  exact OMA.Padic2.well_approximable α p hp h
