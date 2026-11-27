import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
For primes at least five, the elementary bound from successive central
extensions of prime order gives a sufficient cubic coefficient. Only at three
is a sharper prime-power bound needed. The prescribed-Sylow estimate costs
a quadratic term. All estimates are in natural numbers to avoid rounding
logarithms, with 2^9 < 5^4 and 2^11 < 3^7 giving strict cubic slack.
-/
open Finset Erdos1160
namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1

/-- Count presentations by successive central extensions of prime order. -/
def H1 : Prop := ∀ p a : ℕ, p.Prime → g (p^a)^6 * p^a ≤ p^(a^3)

/-- A weak form of the Higman-Sims upper bound at the single prime three. -/
def H2 : Prop := ∃ B : ℕ, ∀ a : ℕ, g (3^a)^12 ≤ 3^(a^3+B*(a+1)^2)

/-- Prescribing Sylow types in odd order costs a quadratic term in the logarithm. -/
def H3 : Prop := ∃ E : ℕ, ∀ q r : ℕ, Odd q → q < 2^r →
  g q ≤ 2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p)

private theorem log_gap {p a r A B : ℕ} (h : 2^A ≤ p^B) (hp : p^a ≤ 2^r) :
    A*a ≤ B*r := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    2^(A*a) = (2^A)^a := pow_mul .. 
    _ ≤ (p^B)^a := Nat.pow_le_pow_left h _
    _ = (p^a)^B := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
    _ ≤ (2^r)^B := Nat.pow_le_pow_left hp _
    _ = 2^(B*r) := by rw [← pow_mul,Nat.mul_comm]

theorem odd_cubic_of_sylow (f : ℕ → ℕ) {B E : ℕ}
    (pc : ∀ p a : ℕ, p.Prime → f (p^a)^6 * p^a ≤ p^(a^3))
    (ternary : ∀ a : ℕ, f (3^a)^12 ≤ 3^(a^3+B*(a+1)^2))
    (profiles : ∀ q r : ℕ, Odd q → q < 2^r →
      f q ≤ 2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, f (p^q.factorization p)) :
    ∃ D : ℕ, ∀ q r : ℕ, Odd q → q < 2^r → f q^27 ≤ 2^(r^3+D) := by
  classical
  let K := 432*E+72*B
  let D := K*(4*K+1)^2
  refine ⟨D,fun q r ho hqr => ?_⟩
  have hqn : 0 < q := by obtain ⟨u,hu⟩ := ho; omega
  let T := 72*B*(r+1)^2
  have local_bound (p : ℕ) (hp : p ∈ q.primeFactors) :
      f (p^q.factorization p)^432 ≤ (p^q.factorization p)^(15*r^2) *
        (if p=3 then 2^T else 1) := by
    let a := q.factorization p
    have prime := Nat.prime_of_mem_primeFactors hp
    have hr : p^a ≤ 2^r := (Nat.le_of_dvd hqn (Nat.ordProj_dvd q p)).trans hqr.le
    have hn2 : p ≠ 2 := fun h => ho.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors hp)
    by_cases h : p=3
    · subst p
      rw [if_pos rfl]
      have hx : 11*a ≤ 7*r := log_gap (by decide : 2^11 ≤ 3^7) hr
      have hs : 36*a^2 ≤ 15*r^2 := by nlinarith only [Nat.pow_le_pow_left hx 2,Nat.zero_le (r^2)]
      have ha : a ≤ r := by omega
      calc
        f (3^a)^432 = (f (3^a)^12)^36 := pow_mul _ 12 36
        _ ≤ (3^(a^3+B*(a+1)^2))^36 := Nat.pow_le_pow_left (ternary a) _
        _ = (3^a)^(36*a^2) * 3^(36*B*(a+1)^2) := by
          rw [← pow_mul,← pow_mul,← pow_add]; congr 1; ring
        _ ≤ (3^a)^(15*r^2) * (2^2)^(36*B*(r+1)^2) := Nat.mul_le_mul
          (Nat.pow_le_pow_right (by positivity) hs)
          ((Nat.pow_le_pow_left (by decide : 3 ≤ 2^2) _).trans (Nat.pow_le_pow_right (by decide)
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : a+1 ≤ r+1) 2))))
        _ = _ := by
          rw [← pow_mul (2:ℕ) 2,show 2*(36*B*(r+1)^2) = T by dsimp [T]; ring]
    · rw [if_neg h,mul_one]
      have hp5 : 5 ≤ p := by
        have hp2 := prime.two_le
        have hn4 : p ≠ 4 := fun he => (by decide : ¬ Nat.Prime 4) (he ▸ prime)
        omega
      have hx : 9*a ≤ 4*r := log_gap ((by decide : 2^9 ≤ 5^4).trans (Nat.pow_le_pow_left hp5 4)) hr
      have hs : 72*a^2 ≤ 15*r^2 := by nlinarith only [Nat.pow_le_pow_left hx 2,Nat.zero_le (r^2)]
      have hb := (Nat.le_mul_of_pos_right _ (Nat.pow_pos prime.pos)).trans (pc p a prime)
      calc
        f (p^a)^432 = (f (p^a)^6)^72 := pow_mul _ 6 72
        _ ≤ (p^(a^3))^72 := Nat.pow_le_pow_left hb _
        _ = (p^a)^(72*a^2) := by rw [← pow_mul,← pow_mul]; congr 1; ring
        _ ≤ _ := Nat.pow_le_pow_right (Nat.pow_pos prime.pos) hs
  have hcost : (∏ p ∈ q.primeFactors, if p=3 then (2:ℕ)^T else 1) ≤ 2^T := by
    rw [Finset.prod_ite_eq']
    split <;> first | exact le_rfl | exact Nat.two_pow_pos _
  have hprod : (∏ p ∈ q.primeFactors, f (p^q.factorization p))^432 ≤ q^(15*r^2) * 2^T := by
    calc
      _ = ∏ p ∈ q.primeFactors, f (p^q.factorization p)^432 := (Finset.prod_pow ..).symm
      _ ≤ ∏ p ∈ q.primeFactors, ((p^q.factorization p)^(15*r^2) * (if p=3 then 2^T else 1)) :=
        Finset.prod_le_prod' local_bound
      _ ≤ _ := by
        rw [Finset.prod_mul_distrib,Finset.prod_pow]
        have he : (∏ p ∈ q.primeFactors, p^q.factorization p) = q := Nat.prod_factorization_pow_eq_self hqn.ne'
        rw [he]
        exact Nat.mul_le_mul_left _ hcost
  have hbudget : K*(r+1)^2 ≤ r^3+16*D := by
    by_cases hb : 4*K ≤ r
    · by_cases hr : r = 0
      · subst r; simp_all [D]
      · have hh := Nat.pow_le_pow_left (by omega : r+1 ≤ 2*r) 2
        nlinarith only [Nat.mul_le_mul_left K hh,Nat.mul_le_mul_right (r^2) hb,Nat.zero_le D]
    · have hh : K*(r+1)^2 ≤ D := Nat.mul_le_mul_left K (Nat.pow_le_pow_left (by omega : r+1 ≤ 4*K+1) 2)
      omega
  have hf : (f q^27)^16 ≤ (2^(r^3+D))^16 := calc
    _ = f q^432 := (pow_mul _ 27 16).symm
    _ ≤ (2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, f (p^q.factorization p))^432 :=
      Nat.pow_le_pow_left (profiles q r ho hqr) _
    _ ≤ (2^(E*(r+1)^2))^432 * ((2^r)^(15*r^2) * 2^T) := by
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ (hprod.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hqr.le _)))
    _ = 2^(15*r^3 + K*(r+1)^2) := by
      rw [← pow_mul,← pow_mul,← pow_add,← pow_add]; dsimp [K,T]; congr 1; ring
    _ ≤ _ := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by decide) (by nlinarith only [hbudget])
  exact (Nat.pow_le_pow_iff_left (by decide : 16 ≠ 0)).mp hf

theorem main : H1 → H2 → H3 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1.H2 := by
  rintro h1 ⟨B,h2⟩ ⟨E,h3⟩
  exact odd_cubic_of_sylow g h1 h2 h3

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1