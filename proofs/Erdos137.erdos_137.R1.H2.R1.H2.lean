import OMAReductions.R_Erdos137_erdos_137_R1_H2_R1
import Mathlib

/-! Isolate each prime above 3 in its unique multiple in the interval. -/

open Finset

namespace OMA.PowerfulFour
private theorem same_multiple {a x y p : ℕ}
    (hx : x ∈ Ico a (a+4)) (hy : y ∈ Ico a (a+4)) (hp : 3 < p)
    (hpx : p ∣ x) (hpy : p ∣ y) : x=y := by
  obtain ⟨hxa,hxb⟩ := mem_Ico.mp hx
  obtain ⟨hya,hyb⟩ := mem_Ico.mp hy
  rcases lt_trichotomy x y with h|h|h
  · have hh := Nat.le_of_dvd (Nat.sub_pos_of_lt h) (Nat.dvd_sub hpy hpx)
    omega
  · exact h
  · have hh := Nat.le_of_dvd (Nat.sub_pos_of_lt h) (Nat.dvd_sub hpx hpy)
    omega

private theorem one_three_multiple {a : ℕ} (ha : a%3 ≠ 0) :
    (a+3-a%3 ∈ Ico a (a+4) ∧ 3 ∣ a+3-a%3) ∧
    ∀ x ∈ Ico a (a+4), 3 ∣ x → x=a+3-a%3 := by
  have hr := Nat.mod_lt a (by decide : 0<3)
  have ha' : a = a/3*3 + a%3 := by omega
  have heq : a+3-a%3 = (a/3+1)*3 := by omega
  refine ⟨⟨mem_Ico.mpr ⟨by omega,by omega⟩,⟨a/3+1,by omega⟩⟩,?_⟩
  intro x hx hp
  obtain ⟨hl,hu⟩ := mem_Ico.mp hx
  obtain ⟨q,hq⟩ := hp
  omega

private theorem square_dvd_of_distinct {S : Finset ℕ} {x y p : ℕ}
    (hx : x∈S) (hy : y∈S) (hne : x ≠ y) (hpx : p ∣ x) (hpy : p ∣ y) :
    p^2 ∣ ∏ z ∈ S,z := by
  have hy' : y ∈ S.erase x := mem_erase.mpr ⟨hne.symm,hy⟩
  rw [← mul_prod_erase S (fun z : ℕ => z) hx,
    ← mul_prod_erase (S.erase x) (fun z : ℕ => z) hy',← mul_assoc,pow_two]
  exact dvd_mul_of_dvd_left (mul_dvd_mul hpx hpy) _

private theorem isolate_square {S : Finset ℕ} {x p : ℕ} (hx : x∈S)
    (hp : p.Prime) (hUnique : ∀ y∈S, p ∣ y → y = x)
    (h : p^2 ∣ ∏ z ∈ S,z) : p^2 ∣ x := by
  have hNo : ¬ p ∣ ∏ z ∈ S.erase x,z := by
    intro hd
    obtain ⟨z,hz,hdz⟩ := (hp.prime.dvd_finsetProd_iff (fun z : ℕ => z)).mp hd
    obtain ⟨hneq,hzS⟩ := mem_erase.mp hz
    exact hneq (hUnique z hzS hdz)
  rw [← mul_prod_erase S (fun z : ℕ => z) hx] at h
  exact ((hp.coprime_iff_not_dvd.mpr hNo).pow_left 2).dvd_of_dvd_mul_right h

/-- The primes 2 and 3 are the only primes that can appear in more than
one term of a block of length four. The contribution of 2 is automatic. -/
theorem four_criterion (a : ℕ) (ha : 0 < a) :
    (∏ x ∈ Ico a (a+4), x).Powerful ↔
      (∀ x ∈ Ico a (a+4), ∀ p : ℕ, p.Prime → 3 < p → p ∣ x → p^2 ∣ x) ∧
      (a%3 = 0 ∨ 9 ∣ a+3-a%3) := by
  let S := Ico a (a+4)
  let P := ∏ x ∈ S,x
  have hP : 0 < P := prod_pos (fun x hx => by
    have hh := (mem_Ico.mp hx).1
    omega)
  have h₁ : a ∈ S := mem_Ico.mpr ⟨le_rfl,by omega⟩
  have h₂ : a+1 ∈ S := mem_Ico.mpr ⟨by omega,by omega⟩
  have h₃ : a+2 ∈ S := mem_Ico.mpr ⟨by omega,by omega⟩
  have h₄ : a+3 ∈ S := mem_Ico.mpr ⟨by omega,by omega⟩
  change P.Powerful ↔ _
  constructor
  · intro h
    constructor
    · intro x hx p hp hlarge hd
      have hpP := dvd_trans hd (dvd_prod_of_mem (fun y : ℕ => y) hx)
      have hpp := h p (Nat.mem_primeFactors.mpr ⟨hp,hpP,hP.ne'⟩)
      exact isolate_square hx hp (fun y hy hdy => same_multiple hy hx hlarge hdy hd) hpp
    · by_cases hm : a%3 = 0
      · exact Or.inl hm
      right
      obtain ⟨⟨hx,hd⟩,hOnly⟩ := one_three_multiple hm
      have hpP := dvd_trans hd (dvd_prod_of_mem (fun y : ℕ => y) hx)
      have hpp := h 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three,hpP,hP.ne'⟩)
      exact isolate_square hx Nat.prime_three hOnly hpp
  · rintro ⟨h,h3⟩ p hp
    obtain ⟨hp',hd,_⟩ := Nat.mem_primeFactors.mp hp
    by_cases hlarge : 3 < p
    · obtain ⟨x,hx,hdx⟩ := (hp'.prime.dvd_finsetProd_iff (fun z : ℕ => z)).mp hd
      exact (h x hx p hp' hlarge hdx).trans (dvd_prod_of_mem (fun y : ℕ => y) hx)
    have hCases : p=2 ∨ p=3 := by have := hp'.two_le; omega
    rcases hCases with rfl|rfl
    · by_cases he : 2 ∣ a
      · exact square_dvd_of_distinct h₁ h₃ (by omega) he (by omega)
      · exact square_dvd_of_distinct h₂ h₄ (by omega) (by omega) (by omega)
    · rcases h3 with hzero|h9
      · exact square_dvd_of_distinct h₁ h₄ (by omega) (by omega) (by omega)
      · have hM : a+3-a%3 ∈ S := by
          have := Nat.mod_lt a (by decide : 0 < 3)
          exact mem_Ico.mpr ⟨by omega,by omega⟩
        exact h9.trans (dvd_prod_of_mem (fun y : ℕ => y) hM)

end OMA.PowerfulFour

theorem OMA.solution : OMA.R_Erdos137_erdos_137_R1_H2_R1.H2 :=
  OMA.PowerfulFour.four_criterion
