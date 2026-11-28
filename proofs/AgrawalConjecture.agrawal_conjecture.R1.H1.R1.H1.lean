import OMAReductions.R_AgrawalConjecture_agrawal_conjecture_R1_H1_R1
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! Applying the polynomial identity to two inverse generators forces
the exponent to be odd in every coefficient modulus greater than two. -/

open Polynomial

private theorem reciprocal_odd {n p m : ℕ} (hm : 2 < m)
    (hp : p.Prime) (hc : n.Coprime p)
    (h : (X ^ p - 1 : Polynomial (ZMod m)) ∣
      (X - 1) ^ n - (X ^ n - 1)) : Odd n := by
  let R := AddMonoidAlgebra (ZMod m) (ZMod p)
  let a : R := AddMonoidAlgebra.single 1 1
  let b : R := AddMonoidAlgebra.single (-1) 1
  have ab : a * b = 1 := by
    change AddMonoidAlgebra.single (1 : ZMod p) (1 : ZMod m) *
      AddMonoidAlgebra.single (-1 : ZMod p) (1 : ZMod m) = 1
    rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
    rfl
  have ap : a ^ p = 1 := by
    change AddMonoidAlgebra.single (1 : ZMod p) (1 : ZMod m) ^ p = 1
    rw [AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rfl
  have bp : b ^ p = 1 := by
    change AddMonoidAlgebra.single (-1 : ZMod p) (1 : ZMod m) ^ p = 1
    rw [AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rfl
  have eval (u : R) (hu : u ^ p = 1) : (u - 1) ^ n = u ^ n - 1 := by
    have hv := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
      (algebraMap (ZMod m) R) u h (by simp [Polynomial.eval₂_pow, hu])
    simpa [Polynomial.eval₂_pow, sub_eq_zero] using hv
  apply Nat.not_even_iff_odd.mp
  intro he
  have hx : a * (b - 1) = -(a - 1) := by rw [mul_sub, ab, mul_one, neg_sub]
  have habn : a ^ n * b ^ n = 1 := by rw [← mul_pow, ab, one_pow]
  have hrecip : a ^ n - 1 = 1 - a ^ n := calc
    a ^ n - 1 = (a - 1) ^ n := (eval a ap).symm
    _ = (-(a - 1)) ^ n := (he.neg_pow _).symm
    _ = a ^ n * (b - 1) ^ n := by rw [← hx, mul_pow]
    _ = 1 - a ^ n := by rw [eval b bp, mul_sub, habn, mul_one]
  have hn_cast : (n : ZMod p) ≠ 0 := by
    intro hz
    have hg := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff n p).mp hz) (dvd_refl p)
    rw [hc.gcd_eq_one] at hg
    exact hp.not_dvd_one hg
  have hcoeff : (a ^ n).coeff 0 = 0 := by
    change (AddMonoidAlgebra.single (1 : ZMod p) (1 : ZMod m) ^ n).coeff 0 = 0
    rw [AddMonoidAlgebra.single_pow, nsmul_eq_mul, mul_one, AddMonoidAlgebra.coeff_single]
    simp [Ne.symm hn_cast]
  have hdouble : a ^ n + a ^ n = (1 : R) + 1 := by linear_combination hrecip
  have htwo := congrArg (fun z : R => z.coeff 0) hdouble
  change ((a^n + a^n) : AddMonoidAlgebra (ZMod m) (ZMod p)).coeff 0 =
    ((1 : AddMonoidAlgebra (ZMod m) (ZMod p)) + 1).coeff 0 at htwo
  rw [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add] at htwo
  simp only [Finsupp.add_apply, hcoeff, AddMonoidAlgebra.coeff_one_zero, zero_add,
    one_add_one_eq_two] at htwo
  have hzero : (2 : ZMod m) = 0 := htwo.symm
  have hle := Nat.le_of_dvd (by decide : (0 : ℕ) < 2)
    ((ZMod.natCast_eq_zero_iff 2 m).mp hzero)
  omega


theorem OMA.solution : OMA.R_AgrawalConjecture_agrawal_conjecture_R1_H1_R1.H1 := by
  intro n p hn hnp even hp _ hc _ _
  have hn2 : n ≠ 2 := fun h => hnp (h ▸ Nat.prime_two)
  have hf : ∃ m : ℕ, IsPrimePow m ∧ m ∣ n ∧ 2 < m := by
    by_cases h4 : 4 ∣ n
    · exact ⟨4, (isPrimePow_nat_iff 4).mpr ⟨2, 2, Nat.prime_two, by decide, by decide⟩,
        h4, by decide⟩
    obtain ⟨k, hk⟩ := even
    have hnot : ¬ 2 ∣ k := by
      rintro ⟨d, hd⟩
      exact h4 ⟨d, by omega⟩
    have hl : k ≠ 1 := by omega
    have prime : k.minFac.Prime := Nat.minFac_prime hl
    have gt : 2 < k.minFac := by
      have low := prime.two_le
      by_contra! hle
      have e : k.minFac = 2 := by omega
      exact hnot (e ▸ Nat.minFac_dvd k)
    have divides : k.minFac ∣ n := by
      rw [hk]
      exact dvd_add (Nat.minFac_dvd k) (Nat.minFac_dvd k)
    exact ⟨k.minFac, (isPrimePow_nat_iff _).mpr
      ⟨k.minFac, 1, prime, Nat.one_pos, pow_one _⟩, divides, gt⟩
  obtain ⟨m, hm, hmn, hg⟩ := hf
  refine ⟨m, hm, hmn, ?_⟩
  intro h
  exact (Nat.not_even_iff_odd.mpr (reciprocal_odd hg hp hc h)) even
