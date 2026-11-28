import OMAReductions.R_mo_342353_R1
import Mathlib

theorem OMA.solution : OMA.R_mo_342353_R1.H1 := by
  intro n hn ho h p hp hd i
  haveI : Fact p.Prime := ⟨hp⟩
  have hd' : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hd
  have hm := h.of_dvd (hd'.trans (dvd_pow_self (n : ℤ) (by decide : 3 ≠ 0)))
  have hz := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hm
  push_cast at hz
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro he
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using he)
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv
    subst p
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)
  have hfour : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2*2 by norm_num]
    exact mul_ne_zero htwo htwo
  by_contra! bad
  have hzero : (∏ j ∈ Finset.range (i+1), Nat.choose ((n-1)/p^j%p) (((n-1)/2)/p^j%p)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self i)) (Nat.choose_eq_zero_of_lt bad)
  have hl := Choose.choose_modEq_choose_mul_prod_range_choose (p := p) (n := n-1) (k := (n-1)/2) (i+1)
  rw [hzero] at hl
  have he := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hl
  push_cast at he
  simp at he
  rw [he] at hz
  exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hfour)) hz.symm
