import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1
import Mathlib.FieldTheory.Finite.Basic

-- Step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H3.R1.H1: hypothesis H1 of reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H3.R1
-- Credit: @DeepDuke
-- H1 := ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p ≠ 1 → ¬ (p % 4 = 3 ∧ q % 4 = 1) →     (∃ r : ℕ, r.Prime ∧ r ∣ (q ^ p - 1) / (q - 1) ∧ ¬ q ∣ r - 1) →     ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)  /-- The rest: every prime factor r of N has q | r - 1. -/

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1.H1 := by
  intro p q hp hq hpq hmod hclasses hex hdiv
  obtain ⟨r,hr,hrN,hqr⟩ := hex
  have : Fact r.Prime := ⟨hr⟩
  rw [← Nat.geomSum_eq hq.two_le] at hrN hdiv
  rw [← Nat.geomSum_eq hp.two_le] at hdiv
  let N := ∑ i ∈ Finset.range p, q^i
  let M := ∑ i ∈ Finset.range q, p^i
  change r ∣ N at hrN
  change N ∣ M at hdiv
  have hMzero : (M : ZMod r)=0 := (ZMod.natCast_eq_zero_iff M r).mpr (hrN.trans hdiv)
  have hgeom : M*(p-1)+1=p^q := by
    simpa only [Nat.sub_add_cancel hp.one_lt.le] using geom_sum_mul_add (p-1) q
  have hpow : (p : ZMod r)^q=1 := by
    have hh := congrArg (fun n : ℕ => (n : ZMod r)) hgeom
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_pow,hMzero,
      zero_mul,zero_add] using hh.symm
  have hpnz : (p : ZMod r) ≠ 0 := by
    intro hz
    rw [hz,zero_pow hq.ne_zero] at hpow
    exact zero_ne_one hpow
  have hd1 : orderOf (p : ZMod r) ∣ q := orderOf_dvd_of_pow_eq_one hpow
  have hd2 : orderOf (p : ZMod r) ∣ r-1 := ZMod.orderOf_dvd_card_sub_one hpnz
  have hcop : q.Coprime (r-1) := hq.coprime_iff_not_dvd.mpr hqr
  have hord : orderOf (p : ZMod r)=1 := by
    have hh := Nat.dvd_gcd hd1 hd2
    rw [hcop.gcd_eq_one] at hh
    exact Nat.dvd_one.mp hh
  have hpone : (p : ZMod r)=1 := orderOf_eq_one_iff.mp hord
  have hM : (M : ZMod r)=q := by
    simp only [M,Nat.cast_sum,Nat.cast_pow,hpone,one_pow,
      Finset.sum_const,Finset.card_range,nsmul_one]
  have hrdq : r ∣ q := (ZMod.natCast_eq_zero_iff q r).mp (by rw [← hM]; exact hMzero)
  have heq : r=q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrdq
  subst r
  have hNzero : (N : ZMod q)=0 := (ZMod.natCast_eq_zero_iff N q).mpr hrN
  have hNone : (N : ZMod q)=1 := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    simp only [N,Nat.cast_sum,Nat.cast_pow]
    rw [hk,Finset.sum_range_succ']
    simp [ZMod.natCast_self,pow_succ]
  rw [hNone] at hNzero
  exact one_ne_zero hNzero

