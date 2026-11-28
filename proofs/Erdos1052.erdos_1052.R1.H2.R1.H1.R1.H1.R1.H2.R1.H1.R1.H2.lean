import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1

/-! A unitary-perfect number with 3 as its only repeated odd prime and
three-adic exponent eleven cannot have a two-adic exponent congruent to 2 modulo 4.
The six forced primes and stripped balance come from studer's PR 35627.
This proof refines the prime-path inequality from the earlier Erdős 1052 reductions.
It charges the leaf at 5 only once and uses the eight remaining factors of 3. -/

namespace E1052Strip

open scoped BigOperators

/-- Prime divisors of the kernel and their successors force six fixed primes. -/
theorem forced_fixed {P : Finset ℕ}
    (step : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({3} : Finset ℕ) →
      ∀ p ∈ P, c ∣ p+1 → c ∈ P)
    (seed : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({3} : Finset ℕ) →
      c ∣ 1+3^11 → c ∈ P) :
    ({7,17,67,83,331,661} : Finset ℕ) ⊆ P := by
  have h67 := seed 67 (by norm_num) (by decide) (by decide) (by decide)
  have h661 := seed 661 (by norm_num) (by decide) (by decide) (by decide)
  have h331 := step 331 (by norm_num) (by decide) (by decide) 661 h661 (by decide)
  have h83 := step 83 (by norm_num) (by decide) (by decide) 331 h331 (by decide)
  have h7 := step 7 (by norm_num) (by decide) (by decide) 83 h83 (by decide)
  have h17 := step 17 (by norm_num) (by decide) (by decide) 67 h67 (by decide)
  simp [Finset.insert_subset_iff, h7, h17, h67, h83, h331, h661]

/-- Strip the arithmetic contribution of the six forced primes from the balance. -/
theorem strip_eleven {a : ℕ} {P : Finset ℕ}
    (hF : ({7,17,67,83,331,661} : Finset ℕ) ⊆ P)
    (hbal : (2^a+1)*(1+3^11)*(∏ p ∈ P, (p+1)) =
      2^(a+1)*3^11*(∏ p ∈ P,p)) :
    (2^a+1)*8192*(∏ p ∈ P \ {7,17,67,83,331,661}, (p+1)) =
      2^(a+1)*6561*(∏ p ∈ P \ {7,17,67,83,331,661},p) := by
  rw [← Finset.prod_sdiff (f := fun p : ℕ => p+1) hF,
      ← Finset.prod_sdiff (f := fun p : ℕ => p) hF] at hbal
  have hnum : (∏ p ∈ ({7,17,67,83,331,661} : Finset ℕ), (p+1)) = 180778493952 := by decide
  have hden : (∏ p ∈ ({7,17,67,83,331,661} : Finset ℕ), p) = 144786913369 := by decide
  rw [hnum,hden] at hbal
  nlinarith only [hbal]

end E1052Strip
namespace ElevenLeaves
open Finset OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1
theorem twelve_after_strip {a : ℕ} {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 2)
    (E : (2^a+1)*8192*∏ p ∈ Q,(p+1) = 2^(a+1)*6561*∏ p ∈ Q,p) : 12 ≤ a := by
  have dn : 8192 ∣ 2^(a+1)*6561*∏ p ∈ Q,p := by
    rw [← E]
    exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  have hnq : ∀ p ∈ Q, p ≠ 0 := fun p hp => (hQ p hp).1.ne_zero
  have hnp : (∏ p ∈ Q, p) ≠ 0 := prod_ne_zero_iff.mpr hnq
  have v := (Nat.factorization_le_iff_dvd (by decide : 8192 ≠ 0) (by positivity)).mpr dn 2
  have hq0 (q : ℕ) (hq : q ∈ Q) : q.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => (hQ q hq).2
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hQ q hq).1).mp h).symm)
  have hz : ∑ q ∈ Q, q.factorization 2 = 0 := sum_eq_zero hq0
  have hu : Nat.factorization 8192 2 = 13 := by decide +kernel
  have hv : Nat.factorization 6561 2 = 0 := by decide +kernel
  rw [hu,Nat.factorization_mul (by positivity) hnp,Nat.factorization_mul (by positivity)
    (by decide),Finsupp.add_apply,Finsupp.add_apply,Nat.factorization_pow_self Nat.prime_two,
    hv,Nat.factorization_prod_apply hnq,hz] at v
  omega
end ElevenLeaves

/- Rational bounds for the incoming prime paths of the exponent-eleven balance. -/

namespace OMA.E1052.Eleven

/-- Rational path weights for the stripped three-adic exponent eleven balance. -/
def pathWeight (p : ℕ) : ℚ :=
  if p = 3 then 1 else if p = 7 then 1 else
  if p = 5 then 6/5 else
  if p = 11 then 1728/1541 else
  if p = 23 then 96/91 else
  if p = 31 then 3072/2921 else
  if p = 43 then 1584/1541 else
  if p = 47 then 192/187 else
  if p = 53 then 2592/2525 else
  if p = 61 then 2976/2921 else
  if p = 71 then 48/47 else
  if p = 127 then 96/95 else
  if p = 137 then 92/91 else
  if p = 191 then 176/175 else
  if p = 211 then 2544/2525 else
  if p = 257 then 1548/1541 else
  if p = 281 then 188/187 else
  if p = 421 then 2532/2525 else
  if p = 487 then 2928/2921 else
  ((p : ℚ)+1)/(p-1)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem path_bounds {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) (h7 : p ≠ 7) :
    1+1/(p:ℚ) ≤ pathWeight p ∧ pathWeight p ≤ ((p:ℚ)+1)/(p-1) := by
  have lower := OMA.R_Erdos1052_erdos_1052_R1_H2_R1.one_add_le_B hp.two_le
  by_cases small : p < 488
  · exact (by decide +kernel : ∀ x : Fin 488, x.val.Prime → x.val ≠ 3 → x.val ≠ 7 →
      1+1/(x.val:ℚ) ≤ pathWeight x.val ∧ pathWeight x.val ≤ ((x.val:ℚ)+1)/(x.val-1)) ⟨p,small⟩ hp h3 h7
  have eq : pathWeight p = ((p:ℚ)+1)/(p-1) := by simp [pathWeight, show ∀ t < 488, p ≠ t from fun t ht => by omega, *]
  rw [eq]
  exact ⟨lower, le_rfl⟩

private theorem standard_decreasing {p k : ℕ} (hk : 2 ≤ k) (hkp : k ≤ p) :
    ((p:ℚ)+1)/(p-1) ≤ ((k:ℚ)+1)/(k-1) := by
  have h₁ : (2:ℚ) ≤ k := by exact_mod_cast hk
  have h₂ : (k:ℚ) ≤ p := by exact_mod_cast hkp
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

/- For each distinct odd prime c, its successor factor may be charged to at most
one prime p. Here 5 already occurs in the component of 2, so it has no such p. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem path_step {p c : ℕ} (hp : p.Prime) (h3p : p ≠ 3) (h7p : p ≠ 7)
    (h3c : c ≠ 3) (h7c : c ≠ 7) (hd : c ∣ p+1) (h5 : ¬5 ∣ p+1)
    (changed : pathWeight c ≠ ((c:ℚ)+1)/(c-1)) :
    (1+1/(c:ℚ))*pathWeight p ≤ pathWeight c := by
  have upper := (path_bounds hp h3p h7p).2
  by_cases hc5 : c = 5
  · exact False.elim (h5 (hc5 ▸ hd))
  by_cases hc11 : c = 11
  · subst c
    by_cases large : 109 ≤ p
    · calc (1+1/(11:ℚ))*pathWeight p ≤ (1+1/(11:ℚ))*(((109:ℚ)+1)/(109-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 11 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 10 := by omega
      have e : p = 11*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 10, Nat.Prime (11*j.val-1) →
        (1+1/(11:ℚ))*pathWeight (11*j.val-1) ≤ pathWeight 11) ⟨j,jbound⟩ hp
  by_cases hc23 : c = 23
  · subst c
    by_cases large : 229 ≤ p
    · calc (1+1/(23:ℚ))*pathWeight p ≤ (1+1/(23:ℚ))*(((229:ℚ)+1)/(229-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 23 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 10 := by omega
      have e : p = 23*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 10, Nat.Prime (23*j.val-1) →
        (1+1/(23:ℚ))*pathWeight (23*j.val-1) ≤ pathWeight 23) ⟨j,jbound⟩ hp
  by_cases hc31 : c = 31
  · subst c
    by_cases large : 433 ≤ p
    · calc (1+1/(31:ℚ))*pathWeight p ≤ (1+1/(31:ℚ))*(((433:ℚ)+1)/(433-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 31 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 14 := by omega
      have e : p = 31*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 14, Nat.Prime (31*j.val-1) →
        (1+1/(31:ℚ))*pathWeight (31*j.val-1) ≤ pathWeight 31) ⟨j,jbound⟩ hp
  by_cases hc43 : c = 43
  · subst c
    by_cases large : 601 ≤ p
    · calc (1+1/(43:ℚ))*pathWeight p ≤ (1+1/(43:ℚ))*(((601:ℚ)+1)/(601-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 43 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 14 := by omega
      have e : p = 43*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 14, Nat.Prime (43*j.val-1) →
        (1+1/(43:ℚ))*pathWeight (43*j.val-1) ≤ pathWeight 43) ⟨j,jbound⟩ hp
  by_cases hc47 : c = 47
  · subst c
    by_cases large : 563 ≤ p
    · calc (1+1/(47:ℚ))*pathWeight p ≤ (1+1/(47:ℚ))*(((563:ℚ)+1)/(563-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 47 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 12 := by omega
      have e : p = 47*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 12, Nat.Prime (47*j.val-1) →
        (1+1/(47:ℚ))*pathWeight (47*j.val-1) ≤ pathWeight 47) ⟨j,jbound⟩ hp
  by_cases hc53 : c = 53
  · subst c
    by_cases large : 317 ≤ p
    · calc (1+1/(53:ℚ))*pathWeight p ≤ (1+1/(53:ℚ))*(((317:ℚ)+1)/(317-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 53 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 6 := by omega
      have e : p = 53*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 6, Nat.Prime (53*j.val-1) →
        (1+1/(53:ℚ))*pathWeight (53*j.val-1) ≤ pathWeight 53) ⟨j,jbound⟩ hp
  by_cases hc61 : c = 61
  · subst c
    by_cases large : 853 ≤ p
    · calc (1+1/(61:ℚ))*pathWeight p ≤ (1+1/(61:ℚ))*(((853:ℚ)+1)/(853-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 61 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 14 := by omega
      have e : p = 61*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 14, Nat.Prime (61*j.val-1) →
        (1+1/(61:ℚ))*pathWeight (61*j.val-1) ≤ pathWeight 61) ⟨j,jbound⟩ hp
  by_cases hc71 : c = 71
  · subst c
    by_cases large : 283 ≤ p
    · calc (1+1/(71:ℚ))*pathWeight p ≤ (1+1/(71:ℚ))*(((283:ℚ)+1)/(283-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 71 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 4 := by omega
      have e : p = 71*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 4, Nat.Prime (71*j.val-1) →
        (1+1/(71:ℚ))*pathWeight (71*j.val-1) ≤ pathWeight 71) ⟨j,jbound⟩ hp
  by_cases hc127 : c = 127
  · subst c
    by_cases large : 761 ≤ p
    · calc (1+1/(127:ℚ))*pathWeight p ≤ (1+1/(127:ℚ))*(((761:ℚ)+1)/(761-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 127 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 6 := by omega
      have e : p = 127*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 6, Nat.Prime (127*j.val-1) →
        (1+1/(127:ℚ))*pathWeight (127*j.val-1) ≤ pathWeight 127) ⟨j,jbound⟩ hp
  by_cases hc137 : c = 137
  · subst c
    by_cases large : 547 ≤ p
    · calc (1+1/(137:ℚ))*pathWeight p ≤ (1+1/(137:ℚ))*(((547:ℚ)+1)/(547-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 137 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 4 := by omega
      have e : p = 137*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 4, Nat.Prime (137*j.val-1) →
        (1+1/(137:ℚ))*pathWeight (137*j.val-1) ≤ pathWeight 137) ⟨j,jbound⟩ hp
  by_cases hc191 : c = 191
  · subst c
    by_cases large : 4201 ≤ p
    · calc (1+1/(191:ℚ))*pathWeight p ≤ (1+1/(191:ℚ))*(((4201:ℚ)+1)/(4201-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 191 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 22 := by omega
      have e : p = 191*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 22, Nat.Prime (191*j.val-1) →
        (1+1/(191:ℚ))*pathWeight (191*j.val-1) ≤ pathWeight 191) ⟨j,jbound⟩ hp
  by_cases hc211 : c = 211
  · subst c
    by_cases large : 2531 ≤ p
    · calc (1+1/(211:ℚ))*pathWeight p ≤ (1+1/(211:ℚ))*(((2531:ℚ)+1)/(2531-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 211 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 12 := by omega
      have e : p = 211*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 12, Nat.Prime (211*j.val-1) →
        (1+1/(211:ℚ))*pathWeight (211*j.val-1) ≤ pathWeight 211) ⟨j,jbound⟩ hp
  by_cases hc257 : c = 257
  · subst c
    by_cases large : 3083 ≤ p
    · calc (1+1/(257:ℚ))*pathWeight p ≤ (1+1/(257:ℚ))*(((3083:ℚ)+1)/(3083-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 257 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 12 := by omega
      have e : p = 257*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 12, Nat.Prime (257*j.val-1) →
        (1+1/(257:ℚ))*pathWeight (257*j.val-1) ≤ pathWeight 257) ⟨j,jbound⟩ hp
  by_cases hc281 : c = 281
  · subst c
    by_cases large : 1123 ≤ p
    · calc (1+1/(281:ℚ))*pathWeight p ≤ (1+1/(281:ℚ))*(((1123:ℚ)+1)/(1123-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 281 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 4 := by omega
      have e : p = 281*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 4, Nat.Prime (281*j.val-1) →
        (1+1/(281:ℚ))*pathWeight (281*j.val-1) ≤ pathWeight 281) ⟨j,jbound⟩ hp
  by_cases hc421 : c = 421
  · subst c
    by_cases large : 5051 ≤ p
    · calc (1+1/(421:ℚ))*pathWeight p ≤ (1+1/(421:ℚ))*(((5051:ℚ)+1)/(5051-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 421 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 12 := by omega
      have e : p = 421*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 12, Nat.Prime (421*j.val-1) →
        (1+1/(421:ℚ))*pathWeight (421*j.val-1) ≤ pathWeight 421) ⟨j,jbound⟩ hp
  by_cases hc487 : c = 487
  · subst c
    by_cases large : 5843 ≤ p
    · calc (1+1/(487:ℚ))*pathWeight p ≤ (1+1/(487:ℚ))*(((5843:ℚ)+1)/(5843-1)) := by
             exact mul_le_mul_of_nonneg_left (upper.trans (standard_decreasing (by decide) large)) (by norm_num)
           _ ≤ pathWeight 487 := by decide +kernel
    · obtain ⟨j,hj⟩ := hd
      have jbound : j < 12 := by omega
      have e : p = 487*j-1 := by omega
      rw [e] at hp ⊢
      exact (by decide +kernel : ∀ j : Fin 12, Nat.Prime (487*j.val-1) →
        (1+1/(487:ℚ))*pathWeight (487*j.val-1) ≤ pathWeight 487) ⟨j,jbound⟩ hp
  exact False.elim (changed (by simp [pathWeight, h3c, h7c, hc5, hc11, hc23, hc31, hc43, hc47, hc53, hc61, hc71, hc127, hc137, hc191, hc211, hc257, hc281, hc421, hc487]))

end OMA.E1052.Eleven

/- A finite weighted bound for leaves whose successor is supported on 2 and 3. -/

namespace OMA.E1052.Eleven

def leafCandidates : Finset ℕ := {5, 11, 23, 47, 53, 71, 107, 191, 383}

def leafWeight : ℕ → ℚ
  | 5 => 6/5
  | 11 => 1728/1541
  | 23 => 96/91
  | 47 => 192/187
  | 53 => 2592/2525
  | 71 => 48/47
  | 107 => 54/53
  | 191 => 176/175
  | 383 => 192/191
  | _ => 1

private def leafCost : ℕ → ℕ
  | 53 | 107 => 3
  | 71 => 2
  | _ => 1

theorem small_leaves {q : ℕ} (h : q ≤ 400) (hp : q.Prime) (h2 : q ≠ 2)
    (h17 : q ≠ 17) (hd : 3 ∣ q+1)
    (hfac : ∀ r ∈ (q+1).primeFactors, r=2 ∨ r=3) : q ∈ leafCandidates := by
  have test : ∀ q : Fin 401, q.val.Prime → q.val ≠ 2 → q.val ≠ 17 → 3 ∣ q.val+1 →
      (∀ r ∈ (q.val+1).primeFactors, r=2 ∨ r=3) → q.val ∈ leafCandidates := by decide +kernel
  exact test ⟨q,by omega⟩ hp h2 h17 hd hfac

private theorem cost_eq {q : ℕ} (h : q ∈ leafCandidates) : leafCost q = (q+1).factorization 3 := by
  have test : ∀ i ∈ leafCandidates, leafCost i = (i+1).factorization 3 := by decide +kernel
  exact test q h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem small_product {S : Finset ℕ} (hS : S ⊆ leafCandidates)
    (hc : ∑ q ∈ S, leafCost q ≤ 8) :
    (∏ q ∈ S, leafWeight q) * (201/200 : ℚ)^(8 - ∑ q ∈ S, leafCost q)
      ≤ 28179280429056/18725448594125 := by
  have test : ∀ P ∈ leafCandidates.powerset, (∑ q ∈ P, leafCost q ≤ 8) →
      (∏ q ∈ P, leafWeight q) * (201/200 : ℚ)^(8 - ∑ q ∈ P, leafCost q)
        ≤ 28179280429056/18725448594125 := by decide +kernel
  exact test S (Finset.mem_powerset.mpr hS) hc

theorem leaf_bound {T : Finset ℕ} {w : ℕ → ℚ} (hnonneg : ∀ q ∈ T, 0 ≤ w q)
    (hsmall : ∀ q ∈ T, q ≤ 400 → q ∈ leafCandidates)
    (hcap : ∀ q ∈ T, q ∈ leafCandidates → w q ≤ leafWeight q)
    (hlarge : ∀ q ∈ T, 400 < q → w q ≤ 201/200)
    (hd : ∀ q ∈ T, 3 ∣ q+1) (hcost : ∑ q ∈ T, (q+1).factorization 3 ≤ 8) :
    ∏ q ∈ T, w q ≤ 28179280429056/18725448594125 := by
  let S := T.filter (· ≤ 400)
  let R := T \ S
  have sub : S ⊆ T := Finset.filter_subset _ _
  have small : S ⊆ leafCandidates := fun q h =>
    hsmall q (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h).2
  have rest {q} (h : q ∈ R) : q ∈ T ∧ 400 < q := by
    obtain ⟨ht,hn⟩ := Finset.mem_sdiff.mp h
    exact ⟨ht, lt_of_not_ge fun hle => hn (Finset.mem_filter.mpr ⟨ht,hle⟩)⟩
  have sumeq : ∑ q ∈ S, leafCost q = ∑ q ∈ S, (q+1).factorization 3 :=
    Finset.sum_congr rfl fun i hi => cost_eq (small hi)
  have rc : R.card ≤ ∑ q ∈ R, (q+1).factorization 3 := by
    simpa using Finset.sum_le_sum (s := R) (f := fun _ => 1) (g := fun q => (q+1).factorization 3)
      (fun q h => Nat.prime_three.factorization_pos_of_dvd (by omega) (hd q (rest h).1))
  have sumsplit := Finset.sum_sdiff (f := fun q => (q+1).factorization 3) sub
  change (∑ q ∈ R, _) + _ = _ at sumsplit
  have sumcost : R.card + (∑ q ∈ S, leafCost q) ≤ 8 := by omega
  have lhs : (∏ q ∈ R, w q) ≤ (201/200 : ℚ)^R.card := by
    simpa only [Finset.prod_const] using Finset.prod_le_prod (s := R) (f := w) (g := fun _ => 201/200)
      (fun q h => hnonneg _ (rest h).1) (fun q h => hlarge _ (rest h).1 (rest h).2)
  have rhs : (∏ q ∈ S, w q) ≤ ∏ q ∈ S, leafWeight q :=
    Finset.prod_le_prod (fun q h => hnonneg _ (sub h)) (fun q h => hcap _ (sub h) (small h))
  have large := (pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 201/200)
    (show R.card ≤ 8 - ∑ q ∈ S, leafCost q by omega))
  rw [← Finset.prod_sdiff (f := w) sub, mul_comm]
  exact (mul_le_mul rhs (lhs.trans large) (Finset.prod_nonneg fun q h => hnonneg _ (rest h).1)
    ((Finset.prod_nonneg fun q h => hnonneg _ (sub h)).trans rhs)).trans (small_product small (by omega))

end OMA.E1052.Eleven

/- Exclusivity, factorization budget, and the leaf-product contradiction for the
stripped Graham balance at three-adic exponent eleven. -/

namespace OMA.E1052.Eleven

open Finset OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

theorem stripped_no_five {a : ℕ} {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime ∧ p ≠ 2)
    (E : (2^a+1)*8192*∏ p ∈ Q,(p+1) = 2^(a+1)*6561*∏ p ∈ Q,p)
    (ha : 5 ∣ 2^a+1) : ∀ p ∈ Q, ¬5 ∣ p+1 := by
  have bk := prime_dvd_prime_pow (e:=8) (show Nat.Prime 3 by decide)
  change ∀ c, c.Prime → c ∣ 6561 → c ∈ ({3} : Finset ℕ) at bk
  obtain ⟨_,_,_,consumed,_,_,_,_⟩ := facts hQ bk E
  exact consumed 5 (by decide) (by decide) (by decide) ha

theorem five_dvd_two_pow_add_one_of_mod_four {a : ℕ} (ha : a%4=2) : 5 ∣ 2^a+1 := by
  have hd := one_add_pow_dvd_of_odd_mul (z:=2) (e0:=2) ha
  norm_num [Nat.add_comm 1] at hd
  exact hd

/- The factorization budget and the partition into two types of leaves
   below adapt the exponent-eleven reduction in PR #35627. The general
   Graham leaf inequality is the one proved by @Dugongue and @adammcarter. -/
theorem stripped_three_budget {a : ℕ} {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 3)
    (E : (2^a+1)*8192*∏ p ∈ Q,(p+1) = 2^(a+1)*6561*∏ p ∈ Q,p) :
    ∑ q ∈ Q,(q+1).factorization 3 ≤ 8 := by
  have dn : (∏ p ∈ Q, (p+1)) ∣ 2^(a+1)*6561*∏ p ∈ Q,p := E ▸ dvd_mul_left _ _
  have hnq : ∀ p ∈ Q, p ≠ 0 := fun p hp => (hQ p hp).1.ne_zero
  have hnp : (∏ p ∈ Q, p) ≠ 0 := prod_ne_zero_iff.mpr hnq
  have hd : ∀ p ∈ Q, p+1 ≠ 0 := fun p _ => by omega
  have v := (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr hd) (by positivity)).mpr dn 3
  have hq0 (q : ℕ) (hq : q ∈ Q) : q.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => (hQ q hq).2 ((Nat.prime_dvd_prime_iff_eq
      (show Nat.Prime 3 by decide) (hQ q hq).1).mp h).symm)
  have htwo : (2^(a+1)).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd
    (fun h => (by decide : ¬3 ∣ 2) ((show Nat.Prime 3 by decide).dvd_of_dvd_pow h))
  have hkernel : Nat.factorization 6561 3 = 8 := by decide +kernel
  rw [Nat.factorization_prod_apply hd,Nat.factorization_mul (by positivity) hnp,
      Nat.factorization_mul (by positivity) (by decide), Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_prod_apply hnq, htwo, hkernel] at v
  have hz : ∑ q ∈ Q, q.factorization 3 = 0 := sum_eq_zero hq0
  simpa [hz] using v

theorem stripped_weight_contradiction {a : ℕ} {Q : Finset ℕ} (ha : 12 ≤ a)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 7 ∧ q ≠ 17)
    (E : (2^a+1)*8192*∏ p ∈ Q,(p+1) = 2^(a+1)*6561*∏ p ∈ Q,p)
    (w : ℕ → ℚ)
    (hb : ∀ p ∈ Q, 1 + 1/(p : ℚ) ≤ w p ∧ w p ≤ ((p : ℚ)+1)/((p : ℚ)-1))
    (hstep : ∀ p ∈ Q, ∀ c ∈ Q, c ∣ p+1 →
      (∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ ({3} : Finset ℕ) → r ∣ p+1 → c ≤ r) →
      w c ≠ ((c : ℚ)+1)/((c : ℚ)-1) → (1+1/(c : ℚ))*w p ≤ w c)
    (s3 : w 3 = 1) (s7 : w 7 = 1) (s31 : w 31 = 3072/2921) (s127 : w 127 = 96/95)
    (bound : ∀ T ⊆ Q, (∀ q ∈ T, q.Prime ∧ q ≠ 2 ∧ q ≠ 17 ∧ 3 ∣ q+1 ∧
      ∀ r ∈ (q+1).primeFactors, r = 2 ∨ r = 3) → (∑ q ∈ T,(q+1).factorization 3) ≤ 8 →
      ∏ q ∈ T,w q ≤ (28179280429056/18725448594125 : ℚ)) : False := by
  classical
  have bk := prime_dvd_prime_pow (e:=8) (show Nat.Prime 3 by decide)
  change ∀ c, c.Prime → c ∣ 6561 → c ∈ ({3} : Finset ℕ) at bk
  obtain ⟨L,hL,leaf,main⟩ := master_gen (fun p hp => ⟨(hQ p hp).1,(hQ p hp).2.1⟩)
    bk (by decide) E w hb hstep
  let T := L.filter (fun q => 3 ∣ q+1)
  let M := L.filter (fun q => ¬3 ∣ q+1)
  have hm (q : ℕ) (hq : q ∈ M) : ∃ i, q+1=2^i := by
    obtain ⟨hql,hnd⟩ := mem_filter.mp hq
    apply two_pow_of_no_odd_prime
    intro c hcp hc2 hc
    exact hnd ((mem_singleton.mp (leaf q hql c hcp hc2 hc)) ▸ hc)
  have mB := mersenne_bound w M (fun q h => (hQ q (hL (mem_filter.mp h).1)).1) hm
    (fun q h => by
      have hq := hL (mem_filter.mp h).1
      have pos : (0:ℚ) ≤ 1 / (q:ℚ) := by positivity
      exact ⟨lt_of_lt_of_le (by linarith) (hb q hq).1, (hb q hq).2⟩)
    (by norm_num [s3,s7,s31,s127])
  have sub : T ⊆ Q := (filter_subset _ _).trans hL
  have tb := stripped_three_budget (fun q h => ⟨(hQ q h).1,(hQ q h).2.2.1⟩) E
  have sm : ∑ q ∈ T, (q+1).factorization 3 ≤ 8 :=
    (sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)).trans tb
  have tB := bound T sub (fun q h => by
    have p := hQ q (sub h)
    exact ⟨p.1,p.2.1,p.2.2.2.2,(mem_filter.mp h).2,
      fun t ht => or_iff_not_imp_left.mpr (fun ht2 => mem_singleton.mp
        (leaf q (mem_filter.mp h).1 t (Nat.prime_of_mem_primeFactors ht) ht2
          (Nat.dvd_of_mem_primeFactors ht)))⟩) sm
  have eq : (∏ q ∈ T, w q)*(∏ q ∈ M, w q) = ∏ q ∈ L, w q :=
    prod_filter_mul_prod_filter_not _ _ _
  rw [← eq] at main
  have mpos : 0 ≤ ∏ q ∈ M, w q := prod_nonneg (fun q h =>
    (by positivity : (0:ℚ) ≤ 1+1/(q:ℚ)).trans (hb q (hL (mem_filter.mp h).1)).1)
  have tpos : 0 ≤ ∏ q ∈ T, w q := prod_nonneg (fun q h =>
    (by positivity : (0:ℚ) ≤ 1+1/(q:ℚ)).trans (hb q (sub h)).1)
  have powlb : (2:ℚ)^12 ≤ (2:ℚ)^a := pow_le_pow_right₀ (by norm_num) ha
  have ap : 1+1/(2:ℚ)^a ≤ 4097/4096 := by
    norm_num at powlb
    rw [le_div_iff₀ (by norm_num)]
    field_simp
    linarith
  have upper := calc
    (1+1/(2:ℚ)^a)*(8192/6561)*((∏ q ∈ T, w q)*(∏ q ∈ M, w q)) ≤
        (4097/4096)*(8192/6561)*((28179280429056/18725448594125)*
          ((w 3*w 7*w 31*w 127)*(2048/2047))) := by gcongr
    _ < 2 := by norm_num [s3,s7,s31,s127]
  exact (not_lt_of_ge main) upper

end OMA.E1052.Eleven

namespace OMA.E1052.Eleven

theorem path_leaf_bound {T : Finset ℕ}
    (hT : ∀ q ∈ T, q.Prime ∧ q ≠ 2 ∧ q ≠ 17 ∧ 3 ∣ q+1 ∧
      ∀ r ∈ (q+1).primeFactors, r=2 ∨ r=3)
    (hc : ∑ q ∈ T, (q+1).factorization 3 ≤ 8) :
    ∏ q ∈ T, pathWeight q ≤ 28179280429056/18725448594125 := by
  apply leaf_bound _ _ _ _ _ hc
  · intro q hq
    obtain ⟨hp,_,_,hd,_⟩ := hT q hq
    exact le_trans (by positivity) (path_bounds hp (by omega) (by omega)).1
  · intro q hq hs
    obtain ⟨hp,hn2,hn17,hd,hfac⟩ := hT q hq
    exact small_leaves hs hp hn2 hn17 hd hfac
  · have cap : ∀ q ∈ leafCandidates, pathWeight q = leafWeight q := by decide +kernel
    exact fun q _ hq => (cap q hq).le
  · intro q hq hl
    obtain ⟨hp,_,_,hd,_⟩ := hT q hq
    have lo : (401:ℚ) ≤ q := by exact_mod_cast (show 401 ≤ q by omega)
    exact (path_bounds hp (by omega) (by omega)).2.trans ((div_le_iff₀ (by linarith)).2 (by linarith))
  · intro q hq
    exact (hT q hq).2.2.2.1

theorem stripped_obstruction {a : ℕ} {Q : Finset ℕ} (ha : 12 ≤ a)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 7 ∧ q ≠ 17)
    (E : (2^a+1)*8192*∏ p ∈ Q,(p+1) = 2^(a+1)*6561*∏ p ∈ Q,p)
    (hfive : 5 ∣ 2^a+1) : False := by
  have consumed := stripped_no_five (fun q h => ⟨(hQ q h).1,(hQ q h).2.1⟩) E hfive
  refine stripped_weight_contradiction ha hQ E pathWeight ?_ ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun _ _ hT hc => path_leaf_bound hT hc)
  · intro p hp
    obtain ⟨prime,_,h3,h7,_⟩ := hQ p hp
    exact path_bounds prime h3 h7
  · intro p hp c hc hd _ hchange
    obtain ⟨prime,_,h3,h7,_⟩ := hQ p hp
    obtain ⟨_,_,hc3,hc7,_⟩ := hQ c hc
    exact path_step prime h3 h7 hc3 hc7 hd (consumed p hp) hchange

end OMA.E1052.Eleven

/- Unitary-perfect inputs yield the precise stripped balance for applying the
weighted Graham inequality. The normalization and stripping lemmas come from
the antecedent reductions and PR #35627. -/

namespace OMA.E1052.Eleven

open Finset OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

theorem excludes_two_mod_four_of
    (obstruction : ∀ {a : ℕ} {Q : Finset ℕ}, 12 ≤ a →
      (∀ q ∈ Q, q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 7 ∧ q ≠ 17) →
      (2^a+1)*8192*∏ p ∈ Q,(p+1) = 2^(a+1)*6561*∏ p ∈ Q,p →
      5 ∣ 2^a+1 → False)
    {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (unique : ∀ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p = 3)
    (he : n.factorization 3 = 11) : padicValNat 2 n % 4 ≠ 2 := by
  classical
  intro hmod
  have hn : n ≠ 0 := h.2.ne'
  have simple : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have prime := Nat.prime_of_mem_primeFactors hr
    have pos := prime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hr)
    have small : ¬ 2 ≤ n.factorization r := fun h2 =>
      hr3 ((unique r).mp ⟨prime, hr2, (prime.pow_dvd_iff_le_factorization hn).mpr h2⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3 : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three,h3n,hn⟩
  obtain ⟨hP, bal⟩ := kernel_balance_one h h3 (by norm_num) simple
  rw [he, Nat.factorization_def n Nat.prime_two] at bal
  obtain ⟨force,_,_,_,_,_,seed,_⟩ := facts hP
    (prime_dvd_prime_pow (e:=11) (by decide : Nat.Prime 3)) bal
  have E := E1052Strip.strip_eleven (E1052Strip.forced_fixed force seed) bal
  have lower := ElevenLeaves.twelve_after_strip (fun q hq => hP q (sdiff_subset hq)) E
  let P := (n.primeFactors.erase 2).filter (fun r => r ∉ ({3} : Finset ℕ))
  let Q := P \ {7,17,67,83,331,661}
  have hQ (q : ℕ) (h : q ∈ Q) : q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 7 ∧ q ≠ 17 := by
    obtain ⟨mem, rem⟩ := mem_sdiff.mp h
    exact ⟨(hP q mem).1,(hP q mem).2,fun eq => (mem_filter.mp mem).2 (by simp [eq]),
      fun eq => rem (by simp [eq]),fun eq => rem (by simp [eq])⟩
  have powFive := one_add_pow_dvd_of_odd_mul (z:=2) (e0:=2) hmod
  norm_num [Nat.add_comm 1] at powFive
  exact obstruction lower hQ E powFive

theorem excludes_two_mod_four {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (unique : ∀ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p^2 ∣ n ↔ p = 3)
    (he : n.factorization 3 = 11) : padicValNat 2 n % 4 ≠ 2 :=
  excludes_two_mod_four_of (@stripped_obstruction) h unique he

end OMA.E1052.Eleven

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.H2 := by
  refine ⟨0, ?_⟩
  intro n perfect unique eleven two _ _
  exact (OMA.E1052.Eleven.excludes_two_mod_four perfect unique eleven two).elim
