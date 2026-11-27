import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1
import Mathlib

/-! H2: N % p = 1 and N % 4 = 3, so Jacobi reciprocity gives (p | N) = -1; but N | M gives p ^ q = 1 mod N, so (p | N) = 1. -/

namespace OMA.FeitThompsonH2

lemma cast_one_of_mod {n m : ℕ} (hm : 2 ≤ m) (h : n % m = 1) : (n : ZMod m) = 1 := by
  rw [show (1 : ZMod m) = ((1 : ℕ) : ZMod m) by simp, ZMod.natCast_eq_natCast_iff', h,
    Nat.one_mod_eq_one.mpr (by omega)]

end OMA.FeitThompsonH2

open OMA.FeitThompsonH2 in
theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H2 := by
  intro p q hp hq hpq hmod hp4 hq4 hdvd
  have := Fact.mk hp
  rw [← Nat.geomSum_eq hq.two_le, ← Nat.geomSum_eq hp.two_le] at hdvd
  set N := ∑ k ∈ Finset.range p, q ^ k with hNdef
  set M := ∑ k ∈ Finset.range q, p ^ k with hMdef
  have hN4 : N % 4 = 3 := by
    have hq1 : (q : ZMod 4) = 1 := cast_one_of_mod (by norm_num) hq4
    have : (N : ZMod 4) = (p : ZMod 4) := by
      rw [hNdef]; push_cast; simp [hq1]
    rw [ZMod.natCast_eq_natCast_iff'] at this
    omega
  have hNp : N % p = 1 := by
    have hq1 : (q : ZMod p) ≠ 1 := by
      intro h
      rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by simp, ZMod.natCast_eq_natCast_iff',
        Nat.one_mod_eq_one.mpr hp.one_lt.ne'] at h
      exact hmod h
    have hg := geom_sum_mul (q : ZMod p) p
    rw [ZMod.pow_card] at hg
    have hne : (q : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr hq1
    have hN1 : (N : ZMod p) = 1 := by
      rw [hNdef]; push_cast
      have := mul_right_cancel₀ hne (hg.trans (one_mul _).symm)
      exact this
    rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by simp, ZMod.natCast_eq_natCast_iff',
        Nat.one_mod_eq_one.mpr hp.one_lt.ne'] at hN1
    exact hN1
  have hdvdZ : (N : ℤ) ∣ (p : ℤ) ^ q - 1 := by
    rw [← geom_sum_mul (p : ℤ) q]
    have : ((M : ℕ) : ℤ) = ∑ i ∈ Finset.range q, (p : ℤ) ^ i := by rw [hMdef]; push_cast; rfl
    rw [← this]
    exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hdvd) _
  have hJ1 : jacobiSym ((p : ℤ) ^ q) N = 1 := by
    rw [← jacobiSym.one_left N]
    apply jacobiSym.mod_left'
    exact (Int.modEq_iff_dvd.mpr hdvdZ).symm
  have hJp : jacobiSym p N = -1 := by
    rw [jacobiSym.quadratic_reciprocity_three_mod_four hp4 hN4, jacobiSym.mod_left]
    have : ((N : ℤ) % (p : ℤ)) = 1 := by
      rw [← Int.natCast_mod, hNp]; rfl
    rw [this, jacobiSym.one_left]
  rw [jacobiSym.pow_left, hJp] at hJ1
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [hqodd.neg_one_pow] at hJ1
  norm_num at hJ1
