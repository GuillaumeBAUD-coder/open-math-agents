import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1_H1_R1
-- Step Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction
-- Erdos78.erdos_78.variants.strongly_explicit.R1.H1.R1.H1.R1
-- Credit: @adammcarter
-- H2: in F_13[x]/(x^(3^j) - 2), x times a non-square is a square.
-- Proof: the polynomial is irreducible (2 is not a cube mod 13), so the quotient is a finite
-- field of odd characteristic, where a product of two non-squares is a square. And x is a
-- non-square: if x = r^2 then 2 = x^(3^j) = (r^(3^j))^2, and taking norms down to F_13 would
-- make 2^(3^j) a square mod 13, which it is not because 3^j is odd and 2 is a non-residue.
open Polynomial

namespace Erdos78Cliq

theorem no_cube : ∀ b : ZMod 13, b ^ 3 ≠ 2 := by decide

theorem two_ne_zero13 : (2 : ZMod 13) ≠ 0 := by decide

theorem no_sqrt_two : ∀ s : ZMod 13, s * s ≠ 2 := by decide

theorem irr (j : ℕ) : Irreducible (X ^ 3 ^ j - C 2 : (ZMod 13)[X]) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact X_pow_sub_C_irreducible_of_prime_pow Nat.prime_three (by norm_num) j no_cube

theorem two_pow_odd_not_sq (n : ℕ) (hn : Odd n) : ¬ IsSquare ((2 : ZMod 13) ^ n) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨t, rfl⟩ := hn
  rintro ⟨s, hs⟩
  have h2 : (2 : ZMod 13) ^ t ≠ 0 := pow_ne_zero _ two_ne_zero13
  refine no_sqrt_two (s * ((2 : ZMod 13) ^ t)⁻¹) ?_
  calc s * ((2 : ZMod 13) ^ t)⁻¹ * (s * ((2 : ZMod 13) ^ t)⁻¹)
      = (s * s) * (((2 : ZMod 13) ^ t)⁻¹ * ((2 : ZMod 13) ^ t)⁻¹) := by ring
    _ = (2 : ZMod 13) ^ (2 * t + 1) * (((2 : ZMod 13) ^ t)⁻¹ * ((2 : ZMod 13) ^ t)⁻¹) := by rw [hs]
    _ = 2 * (((2 : ZMod 13) ^ t * ((2 : ZMod 13) ^ t)⁻¹) * ((2 : ZMod 13) ^ t * ((2 : ZMod 13) ^ t)⁻¹)) := by ring
    _ = 2 := by rw [mul_inv_cancel₀ h2]; ring

theorem root_not_sq (j : ℕ) :
    ¬ IsSquare (AdjoinRoot.root (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hm : 0 < 3 ^ j := by positivity
  have hmon : (X ^ 3 ^ j - C 2 : (ZMod 13)[X]).Monic := monic_X_pow_sub_C 2 hm.ne'
  have := hmon.finite_adjoinRoot
  rintro ⟨r, hr⟩
  have hx : (AdjoinRoot.root (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) ^ 3 ^ j =
      algebraMap (ZMod 13) (AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) 2 := by
    have h0 := AdjoinRoot.mk_self (f := (X ^ 3 ^ j - C 2 : (ZMod 13)[X]))
    rw [map_sub, map_pow, sub_eq_zero, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h0
    rw [h0, AdjoinRoot.algebraMap_eq]
  have hfin : Module.finrank (ZMod 13) (AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) = 3 ^ j :=
    (finrank_quotient_span_eq_natDegree (f := (X ^ 3 ^ j - C 2 : (ZMod 13)[X]))).trans
      natDegree_X_pow_sub_C
  have hN := congrArg (Algebra.norm (ZMod 13)) hx
  rw [Algebra.norm_algebraMap, hfin, hr, mul_pow, map_mul] at hN
  exact two_pow_odd_not_sq (3 ^ j) (Odd.pow (by decide)) ⟨_, hN.symm⟩

theorem root_mul_sq (j : ℕ) (y : AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X]))
    (hy : ¬ IsSquare y) :
    IsSquare (AdjoinRoot.root (X ^ 3 ^ j - C 2 : (ZMod 13)[X]) * y) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Fact (Irreducible (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) := ⟨irr j⟩
  have hm : 0 < 3 ^ j := by positivity
  have hmon : (X ^ 3 ^ j - C 2 : (ZMod 13)[X]).Monic := monic_X_pow_sub_C 2 hm.ne'
  have := hmon.finite_adjoinRoot
  have : Finite (AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X])) := Module.finite_of_finite (ZMod 13)
  let := Fintype.ofFinite (AdjoinRoot (X ^ 3 ^ j - C 2 : (ZMod 13)[X]))
  have hx := root_not_sq j
  have hx0 : AdjoinRoot.root (X ^ 3 ^ j - C 2 : (ZMod 13)[X]) ≠ 0 := by
    intro h
    rw [h] at hx
    exact hx IsSquare.zero
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hy
    exact hy IsSquare.zero
  have h1 := quadraticChar_neg_one_iff_not_isSquare.2 hx
  have h2 := quadraticChar_neg_one_iff_not_isSquare.2 hy
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hx0 hy0), map_mul, h1, h2]
  norm_num

end Erdos78Cliq

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1_H1_R1_H1_R1.H2 :=
  fun j y hy => Erdos78Cliq.root_mul_sq j y hy
