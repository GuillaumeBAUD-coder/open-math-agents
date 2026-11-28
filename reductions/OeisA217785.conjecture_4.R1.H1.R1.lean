import OMAReductions.R_OeisA217785_conjecture_4_R1
import Mathlib

/-!
The rational splitting field criterion for irreducible reduction.

At good primes, Frobenius cycle lengths give the degrees of the finite-field
factors. The primes dividing the leading coefficient are handled separately.
-/

namespace OMA.R_OeisA217785_conjecture_4_R1_H1_R1

open Finset Polynomial OeisA217785

private theorem closed_form {R : Type*} [CommRing R] (n : ℕ) :
    (1-X)^2 * (∑ k ∈ range (n+1), C ((k+1 : ℕ) : R) * X^k) =
      1 - C ((n+2 : ℕ) : R) * X^(n+1) + C ((n+1 : ℕ) : R) * X^(n+2) := by
  induction n with
  | zero =>
    simp [pow_succ, C_ofNat]
    ring
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add,
      map_one, map_ofNat, pow_succ]
    ring

private theorem rational_form (n : ℕ) :
    (OeisA217785.polyS n).map (Int.castRingHom ℚ) =
    ∑ k ∈ range (n+1), C ((k+1 : ℕ) : ℚ) * X^k := by
  simp [OeisA217785.polyS, Polynomial.map_sum]

private theorem top_coefficient (n : ℕ) : (OeisA217785.polyS n).coeff n = (n+1 : ℤ) := by
  rw [OeisA217785.polyS, Polynomial.finsetSum_coeff, Finset.sum_eq_single n]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [Ne.symm hb]
  · intro hn
    exact (hn (mem_range.mpr n.lt_succ_self)).elim

private theorem exact_degree (n : ℕ) : (OeisA217785.polyS n).natDegree = n := by
  apply le_antisymm
  · rw [OeisA217785.polyS]
    exact natDegree_sum_le_of_forall_le _ _ fun k hk =>
      (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (mem_range.mp hk))
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [top_coefficient]
    positivity

private theorem nonzero_at_zero (n : ℕ) :
    aeval (0 : ℂ) ((OeisA217785.polyS n).map (Int.castRingHom ℚ)) ≠ 0 := by
  rw [rational_form, map_sum, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    simp [zero_pow hb]
  · intro hn
    exact (hn (mem_range.mpr (by omega))).elim

private theorem nonzero_at_one (n : ℕ) :
    aeval (1 : ℂ) ((OeisA217785.polyS n).map (Int.castRingHom ℚ)) ≠ 0 := by
  rw [rational_form, map_sum]
  simp only [map_mul, aeval_C, map_pow, aeval_X, one_pow, mul_one]
  have h : 0 < ∑ k ∈ range (n+1), (k+1 : ℕ) := by
    exact Finset.sum_pos (fun k _ => Nat.succ_pos k) ⟨0,mem_range.mpr (by omega)⟩
  exact_mod_cast h.ne'

/-- No common root with the derivative over the rational algebraic closure. -/
private theorem separable (n : ℕ) : ((OeisA217785.polyS n).map (Int.castRingHom ℚ)).Separable := by
  let p := (OeisA217785.polyS n).map (Int.castRingHom ℚ)
  have h := closed_form (R := ℚ) n
  rw [← rational_form] at h
  change (1-X)^2*p = 1-C ((n+2 : ℕ) : ℚ)*X^(n+1)+C ((n+1 : ℕ):ℚ)*X^(n+2) at h
  have hd : derivative ((1-X)^2*p) =
      C ((n+1 : ℕ) : ℚ) * C ((n+2 : ℕ) : ℚ) * X^n * (X-1) := by
    rw [h, derivative_add, derivative_sub, derivative_one, derivative_C_mul, derivative_C_mul,
      derivative_X_pow_succ, show n+2 = (n+1)+1 by omega, derivative_X_pow_succ]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one, pow_succ]
    ring
  rw [Polynomial.separable_def]
  change IsCoprime p (derivative p)
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ p (derivative p)).mpr
  intro z
  by_contra! hz
  have hzP : aeval z p = 0 := hz.1
  have hzD : aeval z (derivative p) = 0 := hz.2
  have he := congrArg (fun f : ℚ[X] => aeval z f) hd
  rw [derivative_mul] at he
  simp only [map_add, map_mul, hzP, hzD, mul_zero, add_zero,
    aeval_C, map_pow, aeval_X, map_sub, map_one] at he
  have hn1 : algebraMap ℚ ℂ ((n+1 : ℕ) : ℚ) ≠ 0 := by
    simpa only [map_zero] using (algebraMap ℚ ℂ).injective.ne (show ((n+1 : ℕ) : ℚ) ≠ 0 by positivity)
  have hn2 : algebraMap ℚ ℂ ((n+2 : ℕ) : ℚ) ≠ 0 := by
    simpa only [map_zero] using (algebraMap ℚ ℂ).injective.ne (show ((n+2 : ℕ) : ℚ) ≠ 0 by positivity)
  rcases (mul_eq_zero.mp he.symm) with hpow | hOne
  · have hzn : z^n = 0 := (mul_eq_zero.mp hpow).resolve_left (mul_ne_zero hn1 hn2)
    have hz0 : z = 0 := eq_zero_of_pow_eq_zero hzn
    exact nonzero_at_zero n (hz0 ▸ hzP)
  · exact nonzero_at_one n (sub_eq_zero.mp hOne ▸ hzP)

/-- Outside the exceptional indices, either one of the finitely many primes
dividing the leading coefficient already works, or an automorphism acts on
the rational roots as one cycle. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → (¬ ∃ k : ℕ, 0 < k ∧ n = 8 * k * (k + 1)) →
    (∃ p : ℕ, p.Prime ∧ p ∣ n+1 ∧
      Irreducible ((polyS n).map (Int.castRingHom (ZMod p)))) ∨
    (let f := (polyS n).map (Int.castRingHom ℚ)
     ∃ σ : f.Gal, ∀ x y : f.rootSet f.SplittingField, ∃ j : ℕ, (σ ^ j) • x = y)

/-- Chebotarev and the polynomial Frobenius factorization rule give a prime
of irreducible reduction from a full cycle in the Galois group. -/
def H2 : Prop :=
  ∀ P : ℤ[X], 0 < P.natDegree →
    let f := P.map (Int.castRingHom ℚ)
    f.Separable →
    (∃ σ : f.Gal, ∀ x y : f.rootSet f.SplittingField, ∃ j : ℕ, (σ ^ j) • x = y) →
    ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ P.leadingCoeff ∧
      Irreducible (P.map (Int.castRingHom (ZMod p)))

theorem main : H1 → H2 → OMA.R_OeisA217785_conjecture_4_R1.H1 := by
  intro hcycle hfrob n hn hall
  by_contra hexception
  rcases hcycle n hn hexception with ⟨p, hp, _, hirr⟩ | htrans
  · exact hall p hp hirr
  · obtain ⟨p, hp, _, hirr⟩ := hfrob (polyS n) (by rw [exact_degree]; omega) (separable n) htrans
    exact hall p hp hirr

end OMA.R_OeisA217785_conjecture_4_R1_H1_R1
