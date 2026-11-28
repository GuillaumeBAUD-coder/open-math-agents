import OMAStatements.S_oeis_a091817
import Mathlib

/-
A091817: for a prime p >= 3, p divides 2 num(H(p-3)) - 3 den(H(p-3)), where H is the harmonic
number.

Work in ZMod p and write T for the sum of the inverses of 1, ..., p - 3.
- full: the sum of the inverses of 1, ..., p - 1 is 0, because j -> p - j negates each term
  and 2 is invertible.
- Removing the last two terms, 1/(p-2) = -1/2 and 1/(p-1) = -1, gives T = 1 + 1/2, so 2 T = 3.
- With n = p - 3 and N the sum of the integers n!/(i+1), H(n) n! = N, hence
  num * n! = N * den as integers, and N = n! T in ZMod p. Since n! is invertible, num = T den,
  so 2 num - 3 den = (2 T - 3) den = 0 in ZMod p.
-/

namespace OMA.P091817

open Finset

lemma two_ne (p : ℕ) (hp3 : 3 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).1 h')
  omega

lemma cast_ne (p j : ℕ) (h0 : 0 < j) (hj : j < p) : ((j : ℕ) : ZMod p) ≠ 0 := by
  intro h
  have := Nat.le_of_dvd h0 ((ZMod.natCast_eq_zero_iff j p).1 h)
  omega

lemma full (p : ℕ) (hp3 : 3 ≤ p) [Fact p.Prime] :
    ∑ i ∈ range (p - 1), (((i + 1 : ℕ) : ZMod p))⁻¹ = 0 := by
  have h := Finset.sum_range_reflect (fun i => (((i + 1 : ℕ) : ZMod p))⁻¹) (p - 1)
  beta_reduce at h
  have h2 : ∑ j ∈ range (p - 1), (((p - 1 - 1 - j + 1 : ℕ) : ZMod p))⁻¹ =
      ∑ j ∈ range (p - 1), -(((j + 1 : ℕ) : ZMod p))⁻¹ := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have e : ((p - 1 - 1 - j + 1 : ℕ) : ZMod p) = -((j + 1 : ℕ) : ZMod p) := by
      have : ((p - 1 - 1 - j + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
        rw [show p - 1 - 1 - j + 1 + (j + 1) = p by omega]
        exact ZMod.natCast_self p
      rw [Nat.cast_add] at this
      linear_combination this
    rw [e, inv_neg]
  rw [h2, Finset.sum_neg_distrib] at h
  have h3 : (2 : ZMod p) * ∑ i ∈ range (p - 1), (((i + 1 : ℕ) : ZMod p))⁻¹ = 0 := by
    linear_combination (-1 : ZMod p) * h
  exact (mul_eq_zero.1 h3).resolve_left (two_ne p hp3)

lemma main' : ∀ p : ℕ, p.Prime → 3 ≤ p →
      (p : ℤ) ∣ 2 * (harmonic (p - 3)).num - 3 * ((harmonic (p - 3)).den : ℤ) := by
  intro p hp hp3
  have := Fact.mk hp
  generalize hn : p - 3 = n
  obtain ⟨T, hT⟩ : ∃ T : ZMod p, T = ∑ i ∈ range n, (((i + 1 : ℕ) : ZMod p))⁻¹ := ⟨_, rfl⟩
  have h2 := two_ne p hp3
  have hT2 : 2 * T = 3 := by
    have hf := full p hp3
    rw [show p - 1 = n + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, ← hT] at hf
    have e1 : ((n + 1 : ℕ) : ZMod p) = -2 := by
      have : ((n + 1 + 2 : ℕ) : ZMod p) = 0 := by
        rw [show n + 1 + 2 = p by omega]
        exact ZMod.natCast_self p
      rw [Nat.cast_add] at this
      push_cast at this ⊢
      linear_combination this
    have e2 : ((n + 1 + 1 : ℕ) : ZMod p) = -1 := by
      have : ((n + 1 + 1 + 1 : ℕ) : ZMod p) = 0 := by
        rw [show n + 1 + 1 + 1 = p by omega]
        exact ZMod.natCast_self p
      rw [Nat.cast_add] at this
      push_cast at this ⊢
      linear_combination this
    rw [e1, e2, inv_neg, inv_neg, inv_one] at hf
    have hT' : T = 1 + 2⁻¹ := by linear_combination hf
    rw [hT', mul_add, mul_one, mul_inv_cancel₀ h2]
    norm_num
  have hdvd : ∀ i ∈ range n, (i + 1) ∣ n.factorial := fun i hi =>
    Nat.dvd_factorial (Nat.succ_pos i) (by have := mem_range.1 hi; omega)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ∑ i ∈ range n, n.factorial / (i + 1) := ⟨_, rfl⟩
  have hrep : (harmonic n : ℚ) * n.factorial = N := by
    unfold harmonic
    rw [Finset.sum_mul, hN, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.cast_div (hdvd i hi) (by positivity), div_eq_inv_mul]
  have hint : (harmonic n).num * (n.factorial : ℤ) = (N : ℤ) * ((harmonic n).den : ℤ) := by
    have h1 : ((harmonic n).num : ℚ) / ((harmonic n).den : ℚ) * n.factorial = N := by
      rw [Rat.num_div_den]
      exact hrep
    have hden : ((harmonic n).den : ℚ) ≠ 0 := by exact_mod_cast (harmonic n).den_ne_zero
    rw [div_mul_eq_mul_div, div_eq_iff hden] at h1
    exact_mod_cast h1
  have hNp : (N : ZMod p) = (n.factorial : ZMod p) * T := by
    rw [hN, hT, Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    have hne : ((i + 1 : ℕ) : ZMod p) ≠ 0 := cast_ne p (i + 1) (Nat.succ_pos i) (by omega)
    rw [eq_mul_inv_iff_mul_eq₀ hne, ← Nat.cast_mul, Nat.div_mul_cancel (hdvd i hi)]
  have hfac : (n.factorial : ZMod p) ≠ 0 := by
    intro h
    have := hp.dvd_factorial.1 ((ZMod.natCast_eq_zero_iff _ _).1 h)
    omega
  have hz : ((2 * (harmonic n).num - 3 * ((harmonic n).den : ℤ) : ℤ) : ZMod p) = 0 := by
    have h1 := congrArg (Int.cast : ℤ → ZMod p) hint
    push_cast at h1
    rw [hNp] at h1
    have h3 : ((harmonic n).num : ZMod p) = T * ((harmonic n).den : ZMod p) := by
      apply mul_right_cancel₀ hfac
      linear_combination h1
    push_cast
    rw [h3]
    linear_combination ((harmonic n).den : ZMod p) * hT2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hz

end OMA.P091817

theorem OMA.solution : type_of% @OMA.S_oeis_a091817.main := OMA.P091817.main'
