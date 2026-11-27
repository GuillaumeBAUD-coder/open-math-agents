import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

-- Step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H2: hypothesis H2 of reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1
-- Credit: @DeepDuke
-- H2 := ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p ≠ 1 → p % 4 = 3 → q % 4 = 1 →     ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)  /-- All remaining pairs of primes p < q. -/

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H2 := by
  intro p q hp hq hpq hmod hp4 hq4 hdiv
  have : Fact p.Prime := ⟨hp⟩
  let N := ∑ i ∈ Finset.range p, q^i
  rw [← Nat.geomSum_eq hq.two_le, ← Nat.geomSum_eq hp.two_le] at hdiv
  change N ∣ ∑ i ∈ Finset.range q, p^i at hdiv
  have hN4 : N % 4 = 3 := by
    have hm (n : ℕ) : (∑ i ∈ Finset.range n, q^i) % 4 = n % 4 := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hq4]
        simp [Nat.add_mod]
    exact (hm p).trans hp4
  have hqne : (q : ZMod p) ≠ 1 := by
    intro he
    have hh := (ZMod.natCast_eq_natCast_iff' q 1 p).mp (by simpa using he)
    rw [Nat.mod_eq_of_lt hp.one_lt] at hh
    exact hmod hh
  have hfermat : (q : ZMod p)^p = q := by
    simpa only [ZMod.card] using FiniteField.pow_card (q : ZMod p)
  have hNp : (N : ZMod p) = 1 := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hqne)
    rw [one_mul]
    calc
      _ = (q : ZMod p)^p - 1 := by
        simpa only [N, Nat.cast_sum, Nat.cast_pow] using geom_sum_mul (q : ZMod p) p
      _ = _ := by rw [hfermat]
  have hNpmod : N % p = 1 % p :=
    (ZMod.natCast_eq_natCast_iff' N 1 p).mp (by simpa using hNp)
  have hrec : jacobiSym (p : ℤ) N = -1 := by
    rw [jacobiSym.quadratic_reciprocity_three_mod_four hp4 hN4]
    have hm : (N : ℤ) % p = (1 : ℤ) % p := by exact_mod_cast hNpmod
    rw [jacobiSym.mod_left' hm, jacobiSym.one_left]
  have hd : N ∣ p^q-1 := by
    have hmul := dvd_mul_of_dvd_left hdiv (p-1)
    rwa [geom_sum_mul_of_one_le (show 1 ≤ p by omega) q] at hmul
  have hdZ : (N : ℤ) ∣ (p : ℤ)^q - 1 := by
    have hb : 1 ≤ p^q := Nat.one_le_pow q p (by omega)
    have hh : (N : ℤ) ∣ ((p^q-1 : ℕ) : ℤ) := by exact_mod_cast hd
    simpa only [Int.natCast_sub hb, Nat.cast_pow, Nat.cast_one] using hh
  have hpowmod : ((p : ℤ)^q) % N = (1 : ℤ) % N := by
    apply Int.ModEq.symm
    exact Int.modEq_iff_dvd.mpr hdZ
  have hj : jacobiSym ((p : ℤ)^q) N = 1 := by
    rw [jacobiSym.mod_left' hpowmod, jacobiSym.one_left]
  rw [jacobiSym.pow_left, hrec] at hj
  have hodd : Odd q := hq.odd_of_ne_two (by omega)
  rw [hodd.neg_one_pow] at hj
  norm_num at hj

