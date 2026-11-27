import OMAReductions.R_Erdos137_erdos_137_R1_H2_R1
import Mathlib

/-!
# Characterization of powerful length-four consecutive products

Proves `OMA.R_Erdos137_erdos_137_R1_H2_R1.H2`: a product of four consecutive positive integers
`a * (a + 1) * (a + 2) * (a + 3)` is powerful if and only if every prime `p > 3` dividing one of
the four terms divides it to the second power, and `a % 3 = 0 ∨ 9 ∣ a + 3 - a % 3`.
-/

open Finset

namespace OMA.R_Erdos137_erdos_137_R1_H2_R1

private lemma prod_Ico_four (a : ℕ) :
    (∏ x ∈ Ico a (a + 4), x) = a * (a + 1) * (a + 2) * (a + 3) := by
  have h : Ico a (a + 4) = {a, a + 1, a + 2, a + 3} := by
    ext x
    simp only [mem_Ico, mem_insert, mem_singleton]
    omega
  rw [h]
  rw [prod_insert (by simp), prod_insert (by simp),
      prod_insert (by simp), prod_singleton]
  ring

private lemma four_dvd_prod_four (a : ℕ) :
    2 ^ 2 ∣ a * (a + 1) * (a + 2) * (a + 3) := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · have h1 : 2 ∣ a := Nat.dvd_of_mod_eq_zero h
    have h2 : 2 ∣ a + 2 := Nat.dvd_of_mod_eq_zero (by omega)
    have h4 : 2 * 2 ∣ a * (a + 2) := mul_dvd_mul h1 h2
    have heq : a * (a + 1) * (a + 2) * (a + 3) = (a * (a + 2)) * ((a + 1) * (a + 3)) := by ring
    rw [heq]
    exact dvd_mul_of_dvd_left (by simpa [pow_two] using h4) _
  · have h1 : 2 ∣ a + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have h2 : 2 ∣ a + 3 := Nat.dvd_of_mod_eq_zero (by omega)
    have h4 : 2 * 2 ∣ (a + 1) * (a + 3) := mul_dvd_mul h1 h2
    have heq : a * (a + 1) * (a + 2) * (a + 3) = ((a + 1) * (a + 3)) * (a * (a + 2)) := by ring
    rw [heq]
    exact dvd_mul_of_dvd_left (by simpa [pow_two] using h4) _

private lemma nine_dvd_prod_four_iff (a : ℕ) :
    3 ^ 2 ∣ a * (a + 1) * (a + 2) * (a + 3) ↔ a % 3 = 0 ∨ 9 ∣ a + 3 - a % 3 := by
  have hmod : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · constructor
    · intro _; exact Or.inl h0
    · intro _
      have ha : 3 ∣ a := Nat.dvd_of_mod_eq_zero h0
      have ha3 : 3 ∣ a + 3 := Nat.dvd_of_mod_eq_zero (by omega)
      have h9 : 3 * 3 ∣ a * (a + 3) := mul_dvd_mul ha ha3
      have heq : a * (a + 1) * (a + 2) * (a + 3) = (a * (a + 3)) * ((a + 1) * (a + 2)) := by ring
      rw [heq]
      exact dvd_mul_of_dvd_left (by simpa [pow_two] using h9) _
  · have hsub : a + 3 - a % 3 = a + 2 := by omega
    rw [hsub]
    have hcop : Nat.Coprime 9 (a * (a + 1) * (a + 3)) := by
      have hc3 : ∀ k : ℕ, k % 3 ≠ 0 → Nat.Coprime 3 k := fun k hk =>
        (Nat.prime_three.coprime_iff_not_dvd).mpr fun hd => hk (Nat.mod_eq_zero_of_dvd hd)
      have h1' : Nat.Coprime 3 (a * (a + 1) * (a + 3)) :=
        ((hc3 a (by omega)).mul_right (hc3 (a + 1) (by omega))).mul_right (hc3 (a + 3) (by omega))
      simpa using h1'.pow_left 2
    have heq : a * (a + 1) * (a + 2) * (a + 3) = (a * (a + 1) * (a + 3)) * (a + 2) := by ring
    rw [heq]
    have hiff : (9 : ℕ) ∣ (a * (a + 1) * (a + 3)) * (a + 2) ↔ 9 ∣ a + 2 :=
      hcop.dvd_mul_left
    have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [h9, hiff]
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · omega
      · exact h
  · have hsub : a + 3 - a % 3 = a + 1 := by omega
    rw [hsub]
    have hcop : Nat.Coprime 9 (a * (a + 2) * (a + 3)) := by
      have hc3 : ∀ k : ℕ, k % 3 ≠ 0 → Nat.Coprime 3 k := fun k hk =>
        (Nat.prime_three.coprime_iff_not_dvd).mpr fun hd => hk (Nat.mod_eq_zero_of_dvd hd)
      have h1' : Nat.Coprime 3 (a * (a + 2) * (a + 3)) :=
        ((hc3 a (by omega)).mul_right (hc3 (a + 2) (by omega))).mul_right (hc3 (a + 3) (by omega))
      simpa using h1'.pow_left 2
    have heq : a * (a + 1) * (a + 2) * (a + 3) = (a * (a + 2) * (a + 3)) * (a + 1) := by ring
    rw [heq]
    have hiff : (9 : ℕ) ∣ (a * (a + 2) * (a + 3)) * (a + 1) ↔ 9 ∣ a + 1 :=
      hcop.dvd_mul_left
    have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [h9, hiff]
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · omega
      · exact h

private lemma prime_gt_three_dvd_unique {a x y p : ℕ} (hp3 : 3 < p)
    (hx : x ∈ Ico a (a + 4)) (hy : y ∈ Ico a (a + 4)) (hxy : x ≠ y)
    (hpx : p ∣ x) (hpy : p ∣ y) : False := by
  simp only [mem_Ico] at hx hy
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have hd : p ∣ y - x := Nat.dvd_sub hpy hpx
    have hle : p ≤ y - x := Nat.le_of_dvd (by omega) hd
    omega
  · have hd : p ∣ x - y := Nat.dvd_sub hpx hpy
    have hle : p ≤ x - y := Nat.le_of_dvd (by omega) hd
    omega

private lemma H2_proof : H2 := by
  intro a ha
  have hPpos : 0 < ∏ x ∈ Ico a (a + 4), x := by
    rw [prod_Ico_four]
    positivity
  have hPne : (∏ x ∈ Ico a (a + 4), x) ≠ 0 := hPpos.ne'
  constructor
  · intro hPow
    refine ⟨?_, ?_⟩
    · intro x hx p hp hp3 hpx
      have hpP : p ∣ ∏ y ∈ Ico a (a + 4), y := dvd_trans hpx (Finset.dvd_prod_of_mem _ hx)
      have hp2P : p ^ 2 ∣ ∏ y ∈ Ico a (a + 4), y :=
        hPow p (Nat.mem_primeFactors.mpr ⟨hp, hpP, hPne⟩)
      rw [← Finset.mul_prod_erase _ _ hx] at hp2P
      have hcop : Nat.Coprime (p ^ 2) (∏ y ∈ (Ico a (a + 4)).erase x, y) := by
        apply Nat.Coprime.pow_left
        refine Nat.Coprime.prod_right fun y hy => ?_
        rw [hp.coprime_iff_not_dvd]
        intro hpy
        exact prime_gt_three_dvd_unique hp3 hx (mem_erase.mp hy).2 (mem_erase.mp hy).1.symm hpx hpy
      exact hcop.dvd_of_dvd_mul_right hp2P
    · have h3P : 3 ∣ ∏ y ∈ Ico a (a + 4), y := by
        rw [prod_Ico_four]
        rcases (show a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 by omega) with h | h | h
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero h) _) _) _
        · have h2 : 3 ∣ a + 2 := Nat.dvd_of_mod_eq_zero (by omega)
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2 _) _
        · have h1 : 3 ∣ a + 1 := Nat.dvd_of_mod_eq_zero (by omega)
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1 _) _) _
      have h9P : 3 ^ 2 ∣ ∏ y ∈ Ico a (a + 4), y :=
        hPow 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3P, hPne⟩)
      rw [prod_Ico_four] at h9P
      exact (nine_dvd_prod_four_iff a).mp h9P
  · rintro ⟨hgt3, h3⟩ p hp
    obtain ⟨hPrime, hpP, _⟩ := Nat.mem_primeFactors.mp hp
    change p ^ 2 ∣ ∏ x ∈ Ico a (a + 4), x
    have hcases : p = 2 ∨ p = 3 ∨ 3 < p := by
      have hp2 := hPrime.two_le
      omega
    rcases hcases with rfl | rfl | hp3
    · rw [prod_Ico_four]
      exact four_dvd_prod_four a
    · rw [prod_Ico_four]
      exact (nine_dvd_prod_four_iff a).mpr h3
    · obtain ⟨x, hx, hpx⟩ := Prime.exists_mem_finset_dvd hPrime.prime hpP
      exact dvd_trans (hgt3 x hx p hPrime hp3 hpx) (Finset.dvd_prod_of_mem _ hx)

end OMA.R_Erdos137_erdos_137_R1_H2_R1

theorem OMA.solution : OMA.R_Erdos137_erdos_137_R1_H2_R1.H2 :=
  OMA.R_Erdos137_erdos_137_R1_H2_R1.H2_proof
