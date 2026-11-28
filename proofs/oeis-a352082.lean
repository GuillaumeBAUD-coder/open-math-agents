import OMAStatements.S_oeis_a352082

/-!
# Proof of the Hurwitz zeta conjecture of OEIS A352082

Source: https://oeis.org/A352082
Credit: @bmendonca3

For `n > 0`, `a(n) = (1 - 2^n) ζ(-n) - 2^n ζ(-n, n/2 + 1)`.

Outline. At `s = -n` the classical Hurwitz zeta function of the statement is Mathlib's periodic
one minus the finite sum `∑_{k=1}^{M} (q - k)^n`, with `q = n/2 + 1` and `M = ⌈q⌉ - 1`.
* `n = 2(m + 1)`: `q = m + 2` is the zero point of the circle, so the periodic value is `ζ(-n)`,
  which is `0` (trivial zero). The finite sum times `2^n` is `∑_{k=0}^{m} (n - 2k)^n`, and the
  last term of `a(n)` is `0^n = 0`.
* `n = 2m + 1`: `q = 1/2 + (m + 1)`, so the periodic value is `ζ(-n, 1/2)`, and
  `2^n ζ(-n, 1/2) = (1 - 2^n) ζ(-n)` (the `L`-function of the trivial character mod 2). The
  finite sum times `2^n` is `∑_{k=0}^{m} (n - 2k)^n = a(n)`.
-/

namespace OMA.A352082Proof

open OMA.S_oeis_a352082

/-- A natural number is the zero point of the circle `ℝ / ℤ`. -/
lemma coe_nat_eq_zero (k : ℕ) : ((k : ℝ) : UnitAddCircle) = 0 :=
  (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨(k : ℤ), by simp⟩

/-- Reindexing of a sum over `1..M`. -/
lemma sum_Icc_one (f : ℕ → ℂ) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, f k = ∑ k ∈ Finset.range M, f (k + 1) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- The classical Hurwitz zeta function at a negative integer. -/
lemma classical_neg_nat (n : ℕ) (q : ℝ) :
    hurwitzZetaClassical (-(n : ℂ)) q = HurwitzZeta.hurwitzZeta (q : UnitAddCircle) (-(n : ℂ))
      - ∑ k ∈ Finset.Icc 1 (⌈q⌉₊ - 1), ((q - (k : ℝ) : ℝ) : ℂ) ^ n := by
  simp only [hurwitzZetaClassical, neg_neg, Complex.cpow_natCast]

lemma neg_nat_ne_one (n : ℕ) : -(n : ℂ) ≠ 1 := by
  intro h
  exact Nat.cast_add_one_ne_zero (R := ℂ) n (by linear_combination (-1 : ℂ) * h)

/-- `2^n ζ(-n, 1/2) = (1 - 2^n) ζ(-n)`, from the `L`-function of the trivial character mod 2. -/
lemma two_pow_mul_hurwitz_half (n : ℕ) :
    (2 : ℂ) ^ n * HurwitzZeta.hurwitzZeta (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) (-(n : ℂ))
      = (1 - 2 ^ n) * riemannZeta (-(n : ℂ)) := by
  have h := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) (neg_nat_ne_one n)
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have hc : ZMod.toAddCircle (1 : ZMod 2) = (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) := by
    have := ZMod.toAddCircle_natCast (N := 2) 1
    simpa using this
  have hχ : (1 : DirichletCharacter ℂ 2) 0 = 0 := by
    have : Fact (1 < 2) := ⟨by norm_num⟩
    exact MulChar.map_zero _
  rw [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction, ZMod.LFunction, huniv,
    Finset.sum_pair h01, hc, Nat.prime_two.primeFactors, Finset.prod_singleton, hχ] at h
  simpa using h

end OMA.A352082Proof

open OMA.S_oeis_a352082 OMA.A352082Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a352082.main := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
  · -- `n = 2 * m` with `m ≥ 1`: here `n / 2 + 1 = m + 1` is an integer and `ζ(-n) = 0`.
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have hmC : (n : ℂ) = 2 * ((m : ℂ) + 1) := by rw [hm]; push_cast; ring
    have hq : (n : ℝ) / 2 + 1 = ((m + 2 : ℕ) : ℝ) := by rw [hm]; push_cast; ring
    have hζ : riemannZeta (-(n : ℂ)) = 0 := by
      rw [hmC, show -(2 * ((m : ℂ) + 1)) = -2 * ((m : ℂ) + 1) by ring]
      exact riemannZeta_neg_two_mul_nat_add_one m
    have ha : a n = ∑ k ∈ Finset.range (m + 2), (n - 2 * k) ^ n := by
      unfold a
      rw [show n / 2 + 1 = m + 2 by omega]
    rw [classical_neg_nat, hq, Nat.ceil_natCast, coe_nat_eq_zero, HurwitzZeta.hurwitzZeta_zero,
      hζ, show m + 2 - 1 = m + 1 by omega, sum_Icc_one, ha, Finset.sum_range_succ,
      show n - 2 * (m + 1) = 0 by omega, zero_pow (by omega), add_zero, mul_zero, zero_sub,
      zero_sub, mul_neg, neg_neg, Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < m + 1 := Finset.mem_range.mp hk
    rw [Nat.cast_pow, ← mul_pow, Nat.cast_sub (by omega)]
    congr 1
    push_cast
    linear_combination hmC
  · -- `n = 2 * m + 1`: here `n / 2 + 1 = 1 / 2 + (m + 1)` and `2^n ζ(-n, 1/2) = (1 - 2^n) ζ(-n)`.
    have hmC : (n : ℂ) = 2 * (m : ℂ) + 1 := by rw [hm]; push_cast; ring
    have hq : (n : ℝ) / 2 + 1 = (1 : ℝ) / 2 + ((m + 1 : ℕ) : ℝ) := by rw [hm]; push_cast; ring
    have hceil : ⌈(1 : ℝ) / 2 + ((m + 1 : ℕ) : ℝ)⌉₊ = m + 2 := by
      rw [Nat.ceil_eq_iff (by omega)]
      constructor
      · rw [show m + 2 - 1 = m + 1 by omega]; linarith
      · push_cast; linarith
    have hcirc : (((1 : ℝ) / 2 + ((m + 1 : ℕ) : ℝ) : ℝ) : UnitAddCircle)
        = (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) := by
      rw [AddCircle.coe_add, coe_nat_eq_zero, add_zero]
    have ha : a n = ∑ k ∈ Finset.range (m + 1), (n - 2 * k) ^ n := by
      unfold a
      rw [show n / 2 + 1 = m + 1 by omega]
    rw [classical_neg_nat, hq, hceil, hcirc, mul_sub, two_pow_mul_hurwitz_half, sub_sub_cancel,
      show m + 2 - 1 = m + 1 by omega, sum_Icc_one, ha, Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < m + 1 := Finset.mem_range.mp hk
    rw [Nat.cast_pow, ← mul_pow, Nat.cast_sub (by omega)]
    congr 1
    push_cast
    linear_combination hmC
