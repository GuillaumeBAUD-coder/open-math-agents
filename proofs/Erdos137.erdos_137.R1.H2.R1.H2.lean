import OMAReductions.R_Erdos137_erdos_137_R1_H2_R1
import Mathlib

/-! In four consecutive terms, only 2 and 3 can divide more than one term. -/

open Finset

namespace E137FourPowerful

private theorem extract_square {s : Finset ℕ} {p x : ℕ} (hp : p.Prime) (hx : x ∈ s)
    (hother : ∀ y ∈ s, y ≠ x → ¬ p ∣ y)
    (h : p^2 ∣ ∏ y ∈ s, y) : p^2 ∣ x := by
  have hc : p.Coprime (∏ y ∈ s.erase x, y) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro y hy
    exact (hp.coprime_iff_not_dvd).mpr (hother y (mem_erase.mp hy).2 (mem_erase.mp hy).1)
  have hprod : ∏ y ∈ s, y = x * ∏ y ∈ s.erase x, y := (mul_prod_erase s id hx).symm
  rw [hprod] at h
  exact (hc.pow_left 2).dvd_of_dvd_mul_right h

private theorem from_two {s : Finset ℕ} {p x y : ℕ} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y)
    (hp : p ∣ x) (hq : p ∣ y) : p^2 ∣ ∏ z ∈ s, z := by
  have hsub : {x,y} ⊆ s := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hprod := prod_dvd_prod_of_subset {x,y} s id hsub
  rw [prod_pair hne] at hprod
  rw [pow_two]
  exact (mul_dvd_mul hp hq).trans hprod

private theorem unique_large {a p x y : ℕ} (hp : 3 < p)
    (hx : x ∈ Ico a (a+4)) (hy : y ∈ Ico a (a+4)) (hpX : p ∣ x) (hpY : p ∣ y) :
    x = y := by
  have h1 := mem_Ico.mp hx
  have h2 := mem_Ico.mp hy
  rcases lt_trichotomy x y with h | h | h
  · have hdist := Nat.le_of_dvd (by omega : 0 < y - x) (Nat.dvd_sub hpY hpX)
    omega
  · exact h
  · have hdist := Nat.le_of_dvd (by omega : 0 < x - y) (Nat.dvd_sub hpX hpY)
    omega

theorem main : ∀ a : ℕ, 0 < a →
    ((∏ x ∈ Ico a (a+4), x).Powerful ↔
      (∀ x ∈ Ico a (a+4), ∀ p : ℕ, p.Prime → 3 < p → p ∣ x → p^2 ∣ x) ∧
      (a%3 = 0 ∨ 9 ∣ a+3-a%3)) := by
  intro a ha
  let s := Ico a (a+4)
  let z := a+3-a%3
  have hP : (∏ y ∈ s, y) ≠ 0 := by
    apply ne_of_gt
    exact prod_pos fun y hy => ha.trans_le (mem_Ico.mp hy).1
  have hz (hn : a%3 ≠ 0) : z ∈ s := mem_Ico.mpr (by dsimp [z]; omega)
  have hdvz : 3 ∣ z := by dsimp [z]; omega
  have huniq (hn : a%3 ≠ 0) {x : ℕ} (hx : x ∈ s) (hdx : 3 ∣ x) : x = z := by
    have := mem_Ico.mp hx
    dsimp [z]
    omega
  constructor
  · intro hpow
    constructor
    · intro x hx p hp hlarge hpx
      have hsq : p^2 ∣ ∏ y ∈ s, y := hpow p (Nat.mem_primeFactors.mpr ⟨hp, hpx.trans (dvd_prod_of_mem id hx), hP⟩)
      exact extract_square hp hx (fun y hy hne hd => hne (unique_large hlarge hy hx hd hpx)) hsq
    · by_cases h : a%3 = 0
      · exact Or.inl h
      · refine Or.inr ?_
        exact extract_square Nat.prime_three (hz h)
          (fun y hy hne hdy => hne (huniq h hy hdy))
          (hpow 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hdvz.trans (dvd_prod_of_mem id (hz h)), hP⟩))
  · rintro ⟨hlarge, h3⟩ p hpmem
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hpmem
    change p^2 ∣ ∏ y ∈ s, y
    have h2 : (2 : ℕ)^2 ∣ ∏ y ∈ s, y := by
      by_cases he : 2 ∣ a
      · exact from_two (x := a) (y := a+2) (mem_Ico.mpr (by omega)) (mem_Ico.mpr (by omega))
          (by omega) he (by omega)
      · exact from_two (x := a+1) (y := a+3) (mem_Ico.mpr (by omega)) (mem_Ico.mpr (by omega))
          (by omega) (by omega) (by omega)
    have h3sq : (3 : ℕ)^2 ∣ ∏ y ∈ s, y := by
      by_cases hm : a%3 = 0
      · exact from_two (x := a) (y := a+3) (mem_Ico.mpr (by omega)) (mem_Ico.mpr (by omega))
          (by omega) (by omega) (by omega)
      · exact (h3.resolve_left hm).trans (dvd_prod_of_mem id (hz hm))
    rcases (show p = 2 ∨ p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | rfl | hp'
    · exact h2
    · exact h3sq
    · obtain ⟨x,hx,hpx⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
      exact (hlarge x hx p hp hp' hpx).trans (dvd_prod_of_mem id hx)

end E137FourPowerful

theorem OMA.solution : OMA.R_Erdos137_erdos_137_R1_H2_R1.H2 :=
  E137FourPowerful.main