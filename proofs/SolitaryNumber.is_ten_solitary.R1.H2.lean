import OMAReductions.R_SolitaryNumber_is_ten_solitary_R1
import Mathlib

-- Step SolitaryNumber.is_ten_solitary.R1.H2: hypothesis H2 of reduction SolitaryNumber.is_ten_solitary.R1
-- Credit: @ivillar

/-!
An odd number whose sum of divisors is odd is a perfect square: `σ` is multiplicative and
`σ(p ^ n) = 1 + p + ... + p ^ n` has the parity of `n + 1` for odd `p`. If `10 σ(m) = 18 m` with
`m` odd then `σ(m)` is odd.
-/
namespace F2Sol

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem sq_of_odd_sigma (m : ℕ) : Odd m → Odd (σ 1 m) → IsSquare m := by
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ m
  · intro p n hp hn hodd hs
    have hpodd : Odd p := by
      by_contra hne
      have hev : Even p := Nat.not_odd_iff_even.mp hne
      exact (Nat.not_odd_iff_even.mpr (hev.pow_of_ne_zero hn.ne')) hodd
    rw [sigma_one_apply_prime_pow hp, Finset.odd_sum_iff_odd_card_odd] at hs
    have hall : (Finset.range (n + 1)).filter (fun k => Odd (p ^ k)) = Finset.range (n + 1) :=
      Finset.filter_true_of_mem (fun k _ => hpodd.pow)
    rw [hall, Finset.card_range] at hs
    have h2 : n % 2 = 0 := by
      have := Nat.odd_iff.mp hs
      omega
    refine ⟨p ^ (n / 2), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  · intro h
    exact absurd h (by decide)
  · intro _ _
    exact ⟨1, rfl⟩
  · intro a b _ _ hab iha ihb hodd hs
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at hs
    have ha : Odd a := (Nat.odd_mul.mp hodd).1
    have hb : Odd b := (Nat.odd_mul.mp hodd).2
    have hsa : Odd (σ 1 a) := (Nat.odd_mul.mp hs).1
    have hsb : Odd (σ 1 b) := (Nat.odd_mul.mp hs).2
    exact (iha ha hsa).mul (ihb hb hsb)

theorem odd_friend : ∀ m : ℕ, Odd m → σ 1 m * 10 = 18 * m → IsSquare m := by
  intro m hm h
  apply sq_of_odd_sigma m hm
  rw [Nat.odd_iff] at hm ⊢
  omega

end F2Sol

theorem OMA.solution : OMA.R_SolitaryNumber_is_ten_solitary_R1.H2 :=
  F2Sol.odd_friend
