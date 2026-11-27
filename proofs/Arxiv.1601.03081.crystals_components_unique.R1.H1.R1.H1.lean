import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1
import Mathlib

/-!
# Crystal uniqueness at cross multiplier three

With the smaller components ordered, the second quotient lies strictly
between 3 and 6. Reduction modulo 3 excludes 4, so that quotient is 5.
The first quotient is between 5 and 11. Subtracting nine times the
second quadratic equation from the first eliminates the square of the
larger component. For each candidate quotient from 6 to 11, the ensuing
univariate identity has strictly negative constant term and nonpositive
remaining coefficients after shifting the smaller component by 3.
Thus the first quotient is also 5.
-/

namespace CrystalMultiplierThree

open Arxiv.«1601.03081»

theorem multiplier_three_parameter {a c q : ℕ}
    (ha : 3 ≤ a) (hc : 5 ≤ c) (hac : a ≤ c) (hca : c ≤ 3 * a)
    (he : (c + 3 * a)^2 = q * ((c + 1) * (3 * a + 1))) :
    q = 5 := by
  have ha' : (3 : ℤ) ≤ a := by exact_mod_cast ha
  have hc' : (5 : ℤ) ≤ c := by exact_mod_cast hc
  have hac' : (a : ℤ) ≤ c := by exact_mod_cast hac
  have hca' : (c : ℤ) ≤ 3 * a := by exact_mod_cast hca
  have he' : ((c : ℤ) + 3 * a)^2 = q * ((c + 1) * (3 * a + 1)) := by exact_mod_cast he
  have hlo : 3 * (((c : ℤ) + 1) * (3 * a + 1)) < (c + 3 * a)^2 := by
    have hprod := mul_nonneg (show 0 ≤ (c : ℤ) - 5 by omega)
      (show 0 ≤ 3 * (a : ℤ) - 3 by omega)
    have hprod' := mul_nonneg (show 0 ≤ (2 : ℤ) by norm_num)
      (show 0 ≤ 3 * (a : ℤ) - 9 by omega)
    by_cases h : (c : ℤ) = 3 * a
    · rw [h] at hc' ⊢
      nlinarith
    · have hs := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
      nlinarith
  have hhi : ((c : ℤ) + 3 * a)^2 < 6 * ((c + 1) * (3 * a + 1)) := by
    have hp := mul_nonneg (sub_nonneg.mpr hac') (sub_nonneg.mpr hca')
    have hq := mul_nonneg (show 0 ≤ (a : ℤ) by omega) (sub_nonneg.mpr hac')
    nlinarith
  have hpos : 0 < ((c : ℤ) + 1) * (3 * a + 1) := by positivity
  have hqlo : 3 < q := by
    rw [he'] at hlo
    exact_mod_cast lt_of_mul_lt_mul_right hlo hpos.le
  have hqhi : q < 6 := by
    rw [he'] at hhi
    exact_mod_cast lt_of_mul_lt_mul_right hhi hpos.le
  have hne : q ≠ 4 := by
    intro h4
    subst q
    have hz := congrArg (fun x : ℕ => (x : ZMod 3)) he
    push_cast at hz
    have hzero : (3 : ZMod 3) = 0 := by decide
    have hone : (4 : ZMod 3) = 1 := by decide
    rw [hzero, hone] at hz
    simp only [zero_mul, add_zero, zero_add, mul_one, one_mul] at hz
    generalize (c : ZMod 3) = z at hz
    fin_cases z <;> exact (by decide : ¬ (_ : ZMod 3) = _) hz
  omega

theorem coprime_crystal_multiplier_three_parameter {a c : ℕ}
    (hac : a ≤ c) (hca : c ≤ a * 3) (hcop : a.Coprime c)
    (hab : IsCrystalWithComponents (a * (c * 3)) a (c * 3))
    (hcd : IsCrystalWithComponents (a * (c * 3)) c (a * 3)) :
    (c + a * 3)^2 / ((c + 1) * (a * 3 + 1)) = 5 := by
  have haodd : Odd a := Nat.Odd.of_mul_left hab.1
  have hcodd : Odd c := Nat.Odd.of_mul_left (Nat.Odd.of_mul_right hab.1)
  have ha : 3 ≤ a := by
    obtain ⟨i, hi⟩ := haodd
    have := hab.2.1
    omega
  have hc : 5 ≤ c := by
    obtain ⟨i, hi⟩ := hcodd
    by_contra! h
    have he : a = c := by omega
    rw [← he] at hcop
    change Nat.gcd a a = 1 at hcop
    rw [Nat.gcd_self] at hcop
    omega
  have hd := ((isCrystalWithComponents_iff_sum_sq_dvd _ _ _).mp hcd).2.2.2.2
  have he := (Nat.div_mul_cancel hd).symm
  rw [mul_comm a 3] at hca he ⊢
  exact multiplier_three_parameter ha hc hac hca he

theorem first_parameter_eq_five {a c q : ℕ} (ha : 3 ≤ a)
    (hac : a ≤ c) (hca : c ≤ 3 * a)
    (hf : (a + 3*c)^2 = q * ((a+1)*(3*c+1)))
    (hg : (c + 3*a)^2 = 5 * ((c+1)*(3*a+1))) : q = 5 := by
  have ha' : (3 : ℤ) ≤ a := by exact_mod_cast ha
  have hac' : (a : ℤ) ≤ c := by exact_mod_cast hac
  have hca' : (c : ℤ) ≤ 3 * a := by exact_mod_cast hca
  have hf' : ((a : ℤ) + 3*c)^2 = q * ((a+1)*(3*c+1)) := by exact_mod_cast hf
  have hg' : ((c : ℤ) + 3*a)^2 = 5 * ((c+1)*(3*a+1)) := by exact_mod_cast hg
  have hqhi : q < 12 := by
    have hx := mul_nonneg (show 0 ≤ (a : ℤ) by omega) (sub_nonneg.mpr hac')
    have hy := mul_nonneg (show 0 ≤ (c : ℤ) by omega) (sub_nonneg.mpr hca')
    have hz := mul_pos (show 0 < (a : ℤ) by omega) (show 0 < (c : ℤ) by omega)
    have hh : ((a : ℤ) + 3*c)^2 < 12 * ((a+1)*(3*c+1)) := by nlinarith
    rw [hf'] at hh
    exact_mod_cast lt_of_mul_lt_mul_right hh (by positivity)
  have hqlo : 5 ≤ q := by
    let x : ℤ := a + 3*c
    let y : ℤ := c + 3*a
    let z : ℤ := 3*a*c + 1
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hy : 0 ≤ y := by dsimp [y]; positivity
    have hz : 0 < z := by dsimp [z]; positivity
    have hxy : y ≤ x := by dsimp [x,y]; omega
    have h1 : x^2 = (q : ℤ) * (z+x) := by dsimp [x,z]; linear_combination hf'
    have h2 : y^2 = 5 * (z+y) := by dsimp [y,z]; linear_combination hg'
    have h : 0 ≤ x^2*(z+y) - y^2*(z+x) := by
      rw [show x^2*(z+y) - y^2*(z+x) = (x-y)*((x+y)*z+x*y) by ring]
      positivity
    rw [h1, h2] at h
    have h' : (5 : ℤ) * ((z+x)*(z+y)) ≤ q * ((z+x)*(z+y)) := by
      calc
        _ = 5*(z+y)*(z+x) := by ring
        _ ≤ (q : ℤ)*(z+x)*(z+y) := sub_nonneg.mp h
        _ = _ := by ring
    exact_mod_cast (le_of_mul_le_mul_right h' (by positivity) : (5 : ℤ) ≤ q)
  by_contra hq
  have hq6 : 6 ≤ q := by omega
  let l : ℤ := -3*a*q + 87*a - 3*q + 45
  let m : ℤ := -80*(a:ℤ)^2 - a*q + 135*a - q + 45
  have hlin : l*c+m=0 := by dsimp [l,m]; linear_combination hf' - 9*hg'
  have hm : m = -(l*c) := by linarith
  have hr : m^2 + (9*(a:ℤ)+5)*m*l + (9*(a:ℤ)^2-15*a-5)*l^2 = 0 := by
    rw [hm]
    linear_combination l^2 * hg'
  let t : ℤ := a - 3
  have ht : 0 ≤ t := by dsimp [t]; omega
  have hat : (a : ℤ) = t + 3 := by dsimp [t]; ring
  have ht2 := sq_nonneg t
  have ht3 : 0 ≤ t^3 := pow_nonneg ht _
  have ht4 : 0 ≤ t^4 := pow_nonneg ht _
  dsimp [l,m] at hr
  rw [hat] at hr
  interval_cases q <;> ring_nf at hr <;> nlinarith only [hr, ht, ht2, ht3, ht4]

theorem multiplier_three_coprime {a c : ℕ} (h1 : a.Coprime c)
    (h2 : a ≤ c*3) (h3 : c ≤ a*3)
    (hab : IsCrystalWithComponents (a*(c*3)) a (c*3))
    (hcd : IsCrystalWithComponents (a*(c*3)) c (a*3)) :
    (a+c*3)^2/((a+1)*(c*3+1)) = (c+a*3)^2/((c+1)*(a*3+1)) := by
  have aux : ∀ a c : ℕ, a ≤ c → c ≤ a*3 → a.Coprime c →
      IsCrystalWithComponents (a*(c*3)) a (c*3) →
      IsCrystalWithComponents (a*(c*3)) c (a*3) →
      (a+c*3)^2/((a+1)*(c*3+1)) = (c+a*3)^2/((c+1)*(a*3+1)) := by
    intro a c hac hca hcop hab hcd
    have he := coprime_crystal_multiplier_three_parameter hac hca hcop hab hcd
    have ha : 3 ≤ a := by
      obtain ⟨k, hk⟩ := Nat.Odd.of_mul_left hab.1
      have := hab.2.1
      omega
    have hf := (Nat.div_mul_cancel
      ((isCrystalWithComponents_iff_sum_sq_dvd _ _ _).mp hab).2.2.2.2).symm
    have hg := (Nat.div_mul_cancel
      ((isCrystalWithComponents_iff_sum_sq_dvd _ _ _).mp hcd).2.2.2.2).symm
    rw [he] at hg
    have hq := first_parameter_eq_five ha hac (by simpa only [mul_comm a 3] using hca)
      (by simpa only [mul_comm c 3] using hf) (by simpa only [mul_comm a 3] using hg)
    simpa only [mul_comm c 3] using hq.trans he.symm
  rcases le_total a c with h | h
  · exact aux a c h h3 h1 hab hcd
  · have eq : a*(c*3) = c*(a*3) := by ac_rfl
    exact (aux c a h h2 h1.symm (eq ▸ hcd) (eq ▸ hab)).symm

end CrystalMultiplierThree

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1.H1 := by
  intro a c hcop hab hcd ha hc
  exact CrystalMultiplierThree.multiplier_three_coprime hcop hab hcd ha hc
