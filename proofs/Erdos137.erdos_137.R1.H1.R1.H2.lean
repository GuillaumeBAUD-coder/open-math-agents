import OMAReductions.R_Erdos137_erdos_137_R1_H1_R1
import Mathlib

/-! The only prime which can divide two terms in a block of width three is 2.
Moving a factor 2 from the endpoint of valuation one to the endpoint
divisible by four gives three pairwise coprime factors. -/

namespace OMA.PowerfulTriple

open Nat

private theorem powerful_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.Coprime b) : (a*b).Powerful ↔ a.Powerful ∧ b.Powerful := by
  constructor
  · intro hm
    constructor
    · intro p hp
      obtain ⟨hp',hpA,_⟩ := Nat.mem_primeFactors.mp hp
      have hP : p^2 ∣ a*b := hm p (Nat.mem_primeFactors.mpr
        ⟨hp',dvd_mul_of_dvd_left hpA b,mul_ne_zero ha hb⟩)
      exact ((h.coprime_dvd_left hpA).pow_left 2).dvd_of_dvd_mul_right hP
    · intro p hp
      obtain ⟨hp',hpB,_⟩ := Nat.mem_primeFactors.mp hp
      have hP : p^2 ∣ a*b := hm p (Nat.mem_primeFactors.mpr
        ⟨hp',dvd_mul_of_dvd_right hpB a,mul_ne_zero ha hb⟩)
      exact ((h.symm.coprime_dvd_left hpB).pow_left 2).dvd_of_dvd_mul_left hP
  · rintro ⟨hA,hB⟩ p hp
    obtain ⟨hp',hM,_⟩ := Nat.mem_primeFactors.mp hp
    rcases hp'.dvd_mul.mp hM with hpa|hpb
    · exact dvd_mul_of_dvd_left (hA p (Nat.mem_primeFactors.mpr ⟨hp',hpa,ha⟩)) b
    · exact dvd_mul_of_dvd_right (hB p (Nat.mem_primeFactors.mpr ⟨hp',hpb,hb⟩)) a

private theorem powerful_product {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c) :
    (a*b*c).Powerful ↔ a.Powerful ∧ b.Powerful ∧ c.Powerful := by
  rw [powerful_mul (mul_ne_zero ha hb) hc (Nat.coprime_mul_iff_left.mpr ⟨hac,hbc⟩),
    powerful_mul ha hb hab, and_assoc]

private theorem coprime_next (a : ℕ) : a.Coprime (a+1) := by
  rw [add_comm a 1,Nat.coprime_add_self_right]
  simp

private theorem coprime_two_of_not_even {a : ℕ} (h : ¬ 2 ∣ a) : a.Coprime 2 :=
  (Nat.prime_two.coprime_iff_not_dvd.mpr h).symm

private theorem odd_prime_coprime_two {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    p.Coprime 2 := by
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  have eq : p = 2 := (Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one
  exact hne eq

private theorem powerful_double_iff {a : ℕ} (ha : a ≠ 0) (h4 : 4 ∣ a) :
    (2*a).Powerful ↔ a.Powerful := by
  constructor
  · intro h p hp
    obtain ⟨hp',hpA,_⟩ := Nat.mem_primeFactors.mp hp
    by_cases eq : p=2
    · simpa [eq] using h4
    have hD : p^2 ∣ 2*a := h p (Nat.mem_primeFactors.mpr
      ⟨hp',dvd_mul_of_dvd_right hpA 2,by positivity⟩)
    exact ((odd_prime_coprime_two hp' eq).pow_left 2).dvd_of_dvd_mul_left hD
  · intro h p hp
    obtain ⟨hp',hM,_⟩ := Nat.mem_primeFactors.mp hp
    by_cases eq : p=2
    · subst p
      exact dvd_mul_of_dvd_right h4 2
    have hpa := (odd_prime_coprime_two hp' eq).dvd_of_dvd_mul_left hM
    exact dvd_mul_of_dvd_right (h p (Nat.mem_primeFactors.mpr ⟨hp',hpa,ha⟩)) 2

private theorem odd_start {a : ℕ} (ha : 0 < a) (h : ¬ 2 ∣ a) :
    (a*(a+1)*(a+2)).Powerful ↔ a.Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful := by
  apply powerful_product ha.ne' (by omega) (by omega) (coprime_next a) _ (coprime_next (a+1))
  rw [add_comm a 2,Nat.coprime_add_self_right]
  exact coprime_two_of_not_even h

private theorem first_div_four {a : ℕ} (ha : 0 < a) (h4 : 4 ∣ a) :
    (a*(a+1)*(a+2)).Powerful ↔ a.Powerful ∧ (a+1).Powerful ∧ ((a+2)/2).Powerful := by
  let u := (a+2)/2
  have h2u : a+2=2*u := by dsimp [u]; omega
  have hu : 0 < u := by omega
  have hUodd : ¬ 2 ∣ u := by omega
  have hU2 := coprime_two_of_not_even hUodd
  have hB2 : (a+1).Coprime 2 := coprime_two_of_not_even (by omega)
  have hA : (2*a).Coprime (a+1) := Nat.coprime_mul_iff_left.mpr ⟨hB2.symm,coprime_next a⟩
  have hPrev : a = 2*(u-1) := by omega
  have hUPrev : (u-1).Coprime u := by
    have h := coprime_next (u-1)
    rwa [Nat.sub_add_cancel hu] at h
  have hQ : (2*a).Coprime u := by
    rw [hPrev,Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_left]
    exact ⟨hU2.symm,hU2.symm,hUPrev⟩
  have hBU : (a+1).Coprime u := (coprime_next (a+1)).coprime_dvd_right
    (show u ∣ (a+1)+1 from ⟨2,by omega⟩)
  have hprod : a*(a+1)*(a+2)=(2*a)*(a+1)*u := by rw [h2u]; ring
  rw [hprod,powerful_product (by positivity) (by omega) hu.ne' hA hQ hBU,
    powerful_double_iff ha.ne' h4]

private theorem last_div_four {a : ℕ} (ha : 0 < a) (h4 : 4 ∣ a+2) :
    (a*(a+1)*(a+2)).Powerful ↔ (a/2).Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful := by
  let u := a/2
  have h2u : a=2*u := by dsimp [u]; omega
  have hu : 0 < u := by omega
  have hUodd : ¬ 2 ∣ u := by omega
  have hU2 := coprime_two_of_not_even hUodd
  have hB2 : (a+1).Coprime 2 := coprime_two_of_not_even (by omega)
  have hUB : u.Coprime (a+1) := by
    rw [h2u,add_comm (2*u) 1,Nat.coprime_add_mul_right_right]
    simp
  have hUC : u.Coprime (2*(a+2)) := by
    have hLast : a+2=2*(u+1) := by omega
    rw [hLast,Nat.coprime_mul_iff_right,Nat.coprime_mul_iff_right]
    exact ⟨hU2,hU2,coprime_next u⟩
  have hBC : (a+1).Coprime (2*(a+2)) :=
    Nat.coprime_mul_iff_right.mpr ⟨hB2,coprime_next (a+1)⟩
  have hprod : a*(a+1)*(a+2)=u*(a+1)*(2*(a+2)) := by rw [h2u]; ring
  rw [hprod,powerful_product hu.ne' (by omega) (by positivity) hUB hUC hBC,
    powerful_double_iff (by omega : a+2 ≠ 0) h4]

/-- At width three, a powerful product is either a powerful triple or a
consecutive powerful pair with the third term twice an odd powerful number. -/
theorem triple_criterion (a : ℕ) (ha : 0 < a) :
    (a*(a+1)*(a+2)).Powerful ↔
      (a.Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful) ∨
      (4 ∣ a ∧ a.Powerful ∧ (a+1).Powerful ∧ ((a+2)/2).Powerful) ∨
      (4 ∣ a+2 ∧ (a/2).Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful) := by
  constructor
  · intro h
    by_cases hEven : 2 ∣ a
    · by_cases h4 : 4 ∣ a
      · exact Or.inr (Or.inl ⟨h4,(first_div_four ha h4).mp h⟩)
      · have hLast : 4 ∣ a+2 := by omega
        exact Or.inr (Or.inr ⟨hLast,(last_div_four ha hLast).mp h⟩)
    · exact Or.inl ((odd_start ha hEven).mp h)
  · rintro (h|⟨h4,h⟩|⟨h4,h⟩)
    · intro p hp
      obtain ⟨hP,hd,_⟩ := Nat.mem_primeFactors.mp hp
      rcases hP.dvd_mul.mp hd with h12|h3
      · rcases hP.dvd_mul.mp h12 with h1|h2
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
            (h.1 p (Nat.mem_primeFactors.mpr ⟨hP,h1,ha.ne'⟩)) _) _
        · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
            (h.2.1 p (Nat.mem_primeFactors.mpr ⟨hP,h2,by omega⟩)) _) _
      · exact dvd_mul_of_dvd_right
          (h.2.2 p (Nat.mem_primeFactors.mpr ⟨hP,h3,by omega⟩)) _
    · exact (first_div_four ha h4).mpr h
    · exact (last_div_four ha h4).mpr h

end OMA.PowerfulTriple


theorem OMA.solution : OMA.R_Erdos137_erdos_137_R1_H1_R1.H2 :=
  OMA.PowerfulTriple.triple_criterion
