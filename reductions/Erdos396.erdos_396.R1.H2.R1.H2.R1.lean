import OMAReductions.R_Erdos396_erdos_396_R1_H2_R1
import Mathlib

/-!
Write the endpoint as M(t+1)-1. Each of its eighteen descending factors
has the form (i+1)qᵢ. The modulus makes every qᵢ coprime to 18!, so two
different qᵢ cannot share a prime: it would divide a nonzero difference
of at most seventeen. Meanwhile 18! divides the endpoint plus one, hence
the central binomial coefficient by Catalan integrality.

This leaves a search along one arithmetic progression. Only primes of
the separate linear forms need carry certificates. Existence on this
progression is a sufficient condition; a witness elsewhere can be missed.
-/

namespace OMA.R_Erdos396_erdos_396_R1_H2_R1_H2_R1

open Finset

/-- On the progression, the fixed factorial is paid and all remaining
factors have disjoint prime supports. -/
def H1 : Prop := ∀ t : ℕ,
    let M := 2431 * Nat.factorial 18
    let n := M * (t+1) - 1
    let q := fun i : ℕ => M / (i+1) * (t+1) - 1
    Nat.factorial 18 ∣ n.centralBinom ∧
    (∀ i ∈ range 18, Nat.Coprime (Nat.factorial 18) (q i)) ∧
    Set.Pairwise (↑(range 18) : Set ℕ) (Nat.Coprime.onFun q)

/-- Find a parameter where every prime of each residual linear form gives
at least its multiplicity in carries on doubling the endpoint. -/
def H2 : Prop := ∃ t : ℕ,
    let M := 2431 * Nat.factorial 18
    let n := M * (t+1) - 1
    ∀ i ∈ range 18, let q := M / (i+1) * (t+1) - 1
                     ∀ p ∈ q.primeFactors, q.factorization p ≤
                       ((Ico 1 (Nat.log p (n+n) + 1)).filter fun a =>
                         p ^ a ≤ n % p ^ a + n % p ^ a).card

/-- The multiplier 2431 = 11·13·17 provides the extra copy of each prime
occurring just once in 18!. The primorial up to 18 is 510510. -/
theorem coefficients : ∀ i ∈ range 18,
    let M := 2431 * Nat.factorial 18
    (i+1) * (M / (i+1)) = M ∧ 2 ≤ M / (i+1) ∧ 510510 ∣ M / (i+1) := by
  decide +kernel

/-- No finite set of primes obstructs the residual search: take t+1 = B!.
Then every residual is minus one modulo each prime at most B. -/
theorem avoid_initial_primes (B : ℕ) : ∃ t : ℕ, ∀ i ∈ range 18,
    let q := (2431 * Nat.factorial 18) / (i+1) * (t+1) - 1
    ∀ p ∈ q.primeFactors, B < p := by
  refine ⟨B.factorial - 1, ?_⟩
  intro i hi
  rw [Nat.sub_add_cancel (Nat.factorial_pos B)]
  let c := (2431 * Nat.factorial 18) / (i+1)
  change ∀ p ∈ (c * B.factorial - 1).primeFactors, B < p
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd : p ∣ c * B.factorial - 1 := Nat.dvd_of_mem_primeFactors hp
  by_contra! hB
  have hf := Nat.dvd_factorial hprime.pos hB
  have hpos : 0 < c * B.factorial :=
    Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 2) (coefficients i hi).2.1) (Nat.factorial_pos _)
  have hs : p ∣ (c * B.factorial - 1) + 1 := by
    rw [Nat.sub_add_cancel hpos]
    exact dvd_mul_of_dvd_right hf _
  exact hprime.not_dvd_one ((Nat.dvd_add_right hd).mp hs)

theorem term_decomposition {M t i : ℕ} (ht : 0 < t) (hc : (i+1) * (M / (i+1)) = M)
    (hq : 2 ≤ M / (i+1)) :
    M*t - 1 - i = (i+1) * (M / (i+1) * t - 1) := by
  have hpos : 0 < M / (i+1) * t := Nat.mul_pos (by omega) ht
  have h := congrArg (· * t) hc
  rw [mul_assoc] at h
  have he : (i+1) * (M / (i+1) * t - 1) + (i+1) = M*t := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos, h]
  omega

theorem fixed_coprime {c t : ℕ} (hc : 2 ≤ c) (hprim : 510510 ∣ c) (ht : 0 < t) :
    Nat.Coprime (Nat.factorial 18) (c*t - 1) := by
  by_contra bad
  obtain ⟨p,hp,hf,hq⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  have hpow : Nat.factorial 18 ∣ 510510 ^ 16 := by decide
  have hr := hp.dvd_of_dvd_pow (hf.trans hpow)
  have hct : p ∣ c*t := dvd_mul_of_dvd_left (hr.trans hprim) _
  have hpos : 0 < c*t := Nat.mul_pos (by omega) ht
  have hs : p ∣ (c*t - 1) + 1 := by rwa [Nat.sub_add_cancel hpos]
  exact hp.not_dvd_one ((Nat.dvd_add_right hq).mp hs)

/-- A shared prime in two residuals divides the difference of their offsets. -/
theorem separate_residuals {n : ℕ} {q : ℕ → ℕ} (hn : 18 ≤ n)
    (terms : ∀ i ∈ range 18, n-i = (i+1) * q i)
    (cop : ∀ i ∈ range 18, Nat.Coprime (Nat.factorial 18) (q i)) :
    Set.Pairwise (↑(range 18) : Set ℕ) (Nat.Coprime.onFun q) := by
  suffices h : ∀ a ∈ range 18, ∀ b ∈ range 18, a < b → Nat.Coprime (q a) (q b) by
    intro i hi j hj hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h i hi j hj hlt
    · exact (h j hj i hi hgt).symm
  intro a ha b hb hab
  by_contra bad
  obtain ⟨p,hp,hu,hv⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  have hu' : p ∣ n-a := by rw [terms a ha]; exact dvd_mul_of_dvd_right hu _
  have hv' : p ∣ n-b := by rw [terms b hb]; exact dvd_mul_of_dvd_right hv _
  have hb' := mem_range.mp hb
  have sub := Nat.dvd_sub hu' hv'
  rw [show n-a-(n-b) = b-a by omega] at sub
  have pf := sub.trans (Nat.dvd_factorial (show 0 < b-a by omega) (show b-a ≤ 18 by omega))
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,pf,hu⟩) (cop a ha)

/-- Unconditional verification of the fixed and pairwise parts of the sieve. -/
theorem separation : H1 := by
  intro t
  let M := 2431 * Nat.factorial 18
  let n := M * (t+1) - 1
  let q := fun i : ℕ => M / (i+1) * (t+1) - 1
  have cop (i : ℕ) (hi : i ∈ range 18) : Nat.Coprime (Nat.factorial 18) (q i) :=
    fixed_coprime (coefficients i hi).2.1 (coefficients i hi).2.2 (Nat.succ_pos t)
  have hm : 19 ≤ M := by decide
  have hmt : M ≤ M * (t+1) := Nat.le_mul_of_pos_right M (Nat.succ_pos t)
  refine ⟨?_, cop, separate_residuals (n := n) (by dsimp [n]; omega) ?_ cop⟩
  · apply Dvd.dvd.trans _ (Nat.succ_dvd_centralBinom n)
    change Nat.factorial 18 ∣ (M * (t+1) - 1) + 1
    rw [Nat.sub_add_cancel (by omega)]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · intro i hi
    exact term_decomposition (Nat.succ_pos t) (coefficients i hi).1 (coefficients i hi).2.1

theorem main : H1 → H2 → OMA.R_Erdos396_erdos_396_R1_H2_R1.H2 := by
  rintro sep ⟨t, carry⟩
  let M := 2431 * Nat.factorial 18
  let n := M * (t+1) - 1
  let q := fun i : ℕ => M / (i+1) * (t+1) - 1
  obtain ⟨fixed, cop, pairs⟩ := sep t
  have terms (i : ℕ) (hi : i ∈ range 18) : n-i = (i+1) * q i :=
    term_decomposition (Nat.succ_pos t) (coefficients i hi).1 (coefficients i hi).2.1
  refine ⟨n, ?_⟩
  rw [Nat.descFactorial_eq_prod_range, prod_congr rfl terms, prod_mul_distrib,
    prod_range_add_one_eq_factorial]
  apply (Nat.coprime_prod_right_iff.mpr cop).mul_dvd_of_dvd_of_dvd fixed
  rw [← lcm_eq_prod (f := q) pairs]
  apply Finset.lcm_dvd
  intro i hi
  have hq : q i ≠ 0 := by
    have h := (coefficients i hi).2.1
    change 2 ≤ M / (i+1) at h
    have : M / (i+1) ≤ M / (i+1) * (t+1) := Nat.le_mul_of_pos_right (M / (i+1)) (Nat.succ_pos t)
    dsimp only [q]
    omega
  apply (Nat.factorization_le_iff_dvd hq (Nat.centralBinom_pos n).ne').mp
  intro p
  by_cases hp : p ∈ (q i).primeFactors
  · rw [Nat.centralBinom_eq_two_mul_choose, two_mul,
        Nat.factorization_choose' (Nat.prime_of_mem_primeFactors hp) (Nat.lt_succ_self _)]
    exact carry i hi p hp
  · have hz : (q i).factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    simp [hz]

end OMA.R_Erdos396_erdos_396_R1_H2_R1_H2_R1
