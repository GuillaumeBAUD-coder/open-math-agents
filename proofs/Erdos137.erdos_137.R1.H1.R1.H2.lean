import OMAReductions.R_Erdos137_erdos_137_R1_H1_R1
import Mathlib

/-! Only the prime 2 can divide two members of a three-term interval. -/

open Finset

namespace E137ThreePowerful

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

private theorem three_prod (a : ℕ) :
    (∏ x ∈ Ico a (a+3), x) = a*(a+1)*(a+2) := by
  rw [show a+3 = (a+2)+1 by omega, prod_Ico_succ_top (by omega : a ≤ a+2),
    show a+2 = (a+1)+1 by omega, prod_Ico_succ_top (by omega : a ≤ a+1)]
  simp

private def OddSquares (x : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → 2 < p → p ∣ x → p^2 ∣ x

private theorem squares_of_powerful {x p : ℕ} (hx : x ≠ 0) (h : x.Powerful)
    (hp : p.Prime) (hd : p ∣ x) : p^2 ∣ x :=
  h p (Nat.mem_primeFactors.mpr ⟨hp,hd,hx⟩)

private theorem make_powerful {x : ℕ} (ho : OddSquares x) (h2 : 2 ∣ x → 4 ∣ x) : x.Powerful := by
  intro p hpm
  obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp hpm
  rcases eq_or_lt_of_le hp.two_le with rfl | hp'
  · exact h2 hd
  · exact ho p hp hp' hd

private theorem half_powerful {x : ℕ} (he : 2 ∣ x) (he' : ¬4 ∣ x) (h : OddSquares x) :
    (x/2).Powerful := by
  have hx : x/2*2 = x := Nat.div_mul_cancel he
  apply make_powerful
  · intro p hp hp' hd
    have hp2 : p.Coprime 2 := (hp.coprime_iff_not_dvd).mpr fun h =>
      (not_le_of_gt hp') (Nat.le_of_dvd (by decide) h)
    have hd' : p ∣ x := dvd_trans hd ⟨2,hx.symm⟩
    have hs := h p hp hp' hd'
    rw [← hx] at hs
    exact (hp2.pow_left 2).dvd_of_dvd_mul_right hs
  · intro hd
    exfalso
    apply he'
    have hs := mul_dvd_mul hd (dvd_rfl (a := (2:ℕ)))
    rwa [hx] at hs

theorem three : ∀ a : ℕ, 0 < a →
    ((a*(a+1)*(a+2)).Powerful ↔
      (a.Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful) ∨
      (4 ∣ a ∧ a.Powerful ∧ (a+1).Powerful ∧ ((a+2)/2).Powerful) ∨
      (4 ∣ a+2 ∧ (a/2).Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful)) := by
  intro a ha
  rw [← three_prod]
  let s := Ico a (a+3)
  have hz : (∏ x ∈ s, x) ≠ 0 := ne_of_gt (prod_pos fun _ hx => ha.trans_le (mem_Ico.mp hx).1)
  have ha0 : a ∈ s := mem_Ico.mpr (by omega)
  have ha1 : a+1 ∈ s := mem_Ico.mpr (by omega)
  have ha2 : a+2 ∈ s := mem_Ico.mpr (by omega)
  have hlabel {x : ℕ} (hx : x ∈ s) : x=a ∨ x=a+1 ∨ x=a+2 := by
    have := mem_Ico.mp hx
    omega
  have huniq {p x y : ℕ} (hx : x ∈ s) (hy : y ∈ s) (hp : 2 < p) (hdx : p ∣ x) (hdy : p ∣ y) : x = y := by
    have := mem_Ico.mp hx
    have := mem_Ico.mp hy
    rcases lt_trichotomy x y with h | h | h
    · have := Nat.le_of_dvd (by omega : 0 < y-x) (Nat.dvd_sub hdy hdx)
      omega
    · exact h
    · have := Nat.le_of_dvd (by omega : 0 < x-y) (Nat.dvd_sub hdx hdy)
      omega
  constructor
  · intro h
    have ho {x : ℕ} (hx : x ∈ s) : OddSquares x := by
      intro p hp hp' hd
      apply extract_square hp hx (fun y hy hne hdy => hne (huniq hy hx hp' hdy hd))
      exact squares_of_powerful hz h hp (hd.trans (dvd_prod_of_mem id hx))
    by_cases he : 2 ∣ a
    · have hmid : (a+1).Powerful := make_powerful (ho ha1) (by omega)
      by_cases h4 : 4 ∣ a
      · exact Or.inr (Or.inl ⟨h4, make_powerful (ho ha0) (fun _ => h4), hmid,
          half_powerful (by omega) (by omega) (ho ha2)⟩)
      · have h4' : 4 ∣ a+2 := by omega
        exact Or.inr (Or.inr ⟨h4', half_powerful he h4 (ho ha0), hmid,
          make_powerful (ho ha2) (fun _ => h4')⟩)
    · have hmid : (a+1).Powerful := make_powerful (ho ha1) fun h2 => by
        exact extract_square Nat.prime_two ha1 (fun y hy hne hdy => by
          have := hlabel hy
          omega) (squares_of_powerful hz h Nat.prime_two (h2.trans (dvd_prod_of_mem id ha1)))
      exact Or.inl ⟨make_powerful (ho ha0) (by omega), hmid, make_powerful (ho ha2) (by omega)⟩
  · intro h p hpm
    obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp hpm
    obtain ⟨x,hx,hdx⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
    have hn : x ≠ 0 := (ha.trans_le (mem_Ico.mp hx).1).ne'
    have lift {y : ℕ} (h2 : 2 ∣ y) (hh : (y/2).Powerful) (hp' : 2 < p) (hy : p ∣ y) : p^2 ∣ y := by
      have he : y/2*2 = y := Nat.div_mul_cancel h2
      by_cases hy0 : y = 0
      · simp [hy0]
      have hn : y/2 ≠ 0 := by
        intro h
        apply hy0
        simpa [h] using he.symm
      have hd' : p ∣ y/2 := by
        rw [← he] at hy
        exact (hp.dvd_mul.mp hy).resolve_right fun hd =>
          (not_le_of_gt hp') (Nat.le_of_dvd (by decide) hd)
      exact (squares_of_powerful hn hh hp hd').trans ⟨2,he.symm⟩
    rcases h with ⟨ha',hb',hc'⟩ | ⟨h4,ha',hb',hc'⟩ | ⟨h4,ha',hb',hc'⟩
    · suffices hpow : x.Powerful from (squares_of_powerful hn hpow hp hdx).trans (dvd_prod_of_mem id hx)
      rcases hlabel hx with rfl | rfl | rfl
      · exact ha'
      · exact hb'
      · exact hc'
    · rcases eq_or_lt_of_le hp.two_le with rfl | hp'
      · exact h4.trans (dvd_prod_of_mem id ha0)
      · apply dvd_trans _ (dvd_prod_of_mem id hx)
        change p^2 ∣ x
        rcases hlabel hx with rfl | rfl | rfl
        · exact squares_of_powerful hn ha' hp hdx
        · exact squares_of_powerful hn hb' hp hdx
        · exact lift (by omega) hc' hp' hdx
    · rcases eq_or_lt_of_le hp.two_le with rfl | hp'
      · exact h4.trans (dvd_prod_of_mem id ha2)
      · apply dvd_trans _ (dvd_prod_of_mem id hx)
        change p^2 ∣ x
        rcases hlabel hx with rfl | rfl | rfl
        · exact lift (by omega) ha' hp' hdx
        · exact squares_of_powerful hn hb' hp hdx
        · exact squares_of_powerful hn hc' hp hdx

end E137ThreePowerful

theorem OMA.solution : OMA.R_Erdos137_erdos_137_R1_H1_R1.H2 := E137ThreePowerful.three