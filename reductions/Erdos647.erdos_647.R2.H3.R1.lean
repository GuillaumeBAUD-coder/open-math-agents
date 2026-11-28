import OMAReductions.R_Erdos647_erdos_647_R2
import Mathlib

/-!
# Sharp divisor-count bounds with coprimality restrictions for Erdős 647

For each factorization M = A B of the unrestricted sixth-power maximizer
with coprime factors, B maximizes τ(m)⁶/m among positive integers coprime
to A. Multiplying m by A proves the assertion and equality occurs at m = B.
Every such bound screens shifts in the progression n = 720720t before their
divisors need to be counted. In particular, the sharp sixth-root constant
for m coprime to 30030 is 4096 / 3905707004975257109^(1/6).

The unrestricted prime-by-prime sixth-power calculation is adapted from
`proofs/Erdos647.erdos_647.R1.H1.lean` (merged work of @sbassibot).
The unitary-factor argument, sharp restricted bounds and search reduction
are formalized by @KoaOkano.
-/

open ArithmeticFunction.sigma
open scoped BigOperators

namespace OMA.R_Erdos647_erdos_647_R2_H3_R1

private theorem tailStep (a : ℕ) (ha : 8 ≤ a) :
    (a + 2) ^ 6 ≤ (a + 1) ^ 6 * 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  ring_nf
  omega

private theorem extendProduct {s t : Finset ℕ} (hst : s ⊆ t) {e : ℕ → ℕ}
    (he : ∀ p ∈ t, p ∉ s → e p = 0) (g : ℕ → ℕ → ℕ) (hg : ∀ p, g p 0 = 1) :
    (∏ p ∈ t, g p (e p)) = ∏ p ∈ s, g p (e p) :=
  (Finset.prod_subset hst (fun p hp hps => by rw [he p hp hps, hg])).symm

private theorem peakFacts : σ 0 780296143507862696557498656000 = 13271040 ∧
    ∀ m : ℕ, (σ 0 m)^6 * 780296143507862696557498656000 ≤ 13271040^6 * m := by
  let peak : ℕ → ℕ := fun p =>
    if p < 64 then
      match p with
      | 2 => 8
      | 3 => 4
      | 5 => 3
      | 7 | 11 => 2
      | _ => 1
    else 0
  let smallPrimes : Finset ℕ := (Finset.range 64).filter Nat.Prime
  have smallExponents :
      ∀ p : Fin 64, p.val.Prime → ∀ a : Fin 9,
        (a.val + 1) ^ 6 * p.val ^ peak p.val ≤
          (peak p.val + 1) ^ 6 * p.val ^ a.val := by
    dsimp only [peak]
    decide
  have localBound {p : ℕ} (hp : p.Prime) (a : ℕ) :
      (a + 1) ^ 6 * p ^ peak p ≤ (peak p + 1) ^ 6 * p ^ a := by
    by_cases hsmall : p < 64
    · induction a with
      | zero => exact smallExponents ⟨p, hsmall⟩ hp 0
      | succ a ih =>
        by_cases ha : a < 8
        · exact smallExponents ⟨p, hsmall⟩ hp ⟨a + 1, by omega⟩
        · calc
            (a + 2) ^ 6 * p ^ peak p
                ≤ ((a + 1) ^ 6 * 2) * p ^ peak p :=
                  Nat.mul_le_mul_right _ (tailStep a (by omega))
            _ = ((a + 1) ^ 6 * p ^ peak p) * 2 := mul_right_comm _ _ _
            _ ≤ ((a + 1) ^ 6 * p ^ peak p) * p := Nat.mul_le_mul_left _ hp.two_le
            _ ≤ _ := by simpa only [pow_succ, mul_assoc] using Nat.mul_le_mul_right p ih
    · have hlarge : 2 ^ 6 ≤ p := by omega
      simp only [peak, if_neg hsmall, pow_zero, zero_add, one_pow, one_mul, mul_one]
      calc
        (a + 1) ^ 6 ≤ (2 ^ a) ^ 6 := Nat.pow_le_pow_left a.lt_two_pow_self 6
        _ = (2 ^ 6) ^ a := by rw [← pow_mul, Nat.mul_comm, pow_mul]
        _ ≤ p ^ a := Nat.pow_le_pow_left hlarge a
  have peakDivisors : (∏ p ∈ smallPrimes, (peak p + 1)) = 13271040 := by
    dsimp only [peak, smallPrimes]
    decide
  have peakNumber : (∏ p ∈ smallPrimes, p ^ peak p) = 780296143507862696557498656000 := by
    dsimp only [peak, smallPrimes]
    decide
  have hpr {p : ℕ} (hp : p ∈ smallPrimes) : p.Prime := (Finset.mem_filter.mp hp).2
  constructor
  · rw [← peakNumber, ← peakDivisors]
    rw [ArithmeticFunction.isMultiplicative_sigma.map_prod (fun p => p ^ peak p)]
    · exact Finset.prod_congr rfl (fun p hp =>
        ArithmeticFunction.sigma_zero_apply_prime_pow (hpr hp))
    · intro p hp q hq hpq
      exact (((Nat.coprime_primes (hpr hp) (hpr hq)).2 hpq).pow_left _).pow_right _
  · intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    let s := m.primeFactors ∪ smallPrimes
    have hs {p : ℕ} (hp : p ∈ s) : p.Prime := by
      rcases Finset.mem_union.mp hp with h | h
      · exact Nat.prime_of_mem_primeFactors h
      · exact (Finset.mem_filter.mp h).2
    have hfactor {p : ℕ} (_ : p ∈ s) (hp : p ∉ m.primeFactors) : m.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp hp
    have hpeak {p : ℕ} (hp : p ∈ s) (hn : p ∉ smallPrimes) : peak p = 0 := by
      have h64 : ¬ p < 64 := fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hs hp⟩)
      simp [peak, h64]
    have em := extendProduct (e := m.factorization) (t := s) Finset.subset_union_left
      (fun _ => hfactor)
    have ep := extendProduct (e := peak) (t := s) Finset.subset_union_right (fun _ => hpeak)
    have h := Finset.prod_le_prod' (s := s)
      (fun p hp => localBound (hs hp) (m.factorization p))
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow] at h
    rw [em (fun _ a => a + 1) (fun _ => rfl), ep (· ^ ·) (fun _ => pow_zero _),
      ep (fun _ a => a + 1) (fun _ => rfl), em (· ^ ·) (fun _ => pow_zero _)] at h
    simpa only [← Nat.card_divisors hm, ← ArithmeticFunction.sigma_zero_apply,
      ← Nat.prod_primeFactors_pow_factorization hm, peakNumber, peakDivisors] using h

/-- Each coprime split of the unrestricted extremizer gives a sharp bound
on the integers avoiding the primes in its first factor. -/
def H1 : Prop :=
  ∀ A B m : ℕ, A*B = 780296143507862696557498656000 → A.Coprime B → A.Coprime m →
    (σ 0 m)^6 * B ≤ (σ 0 B)^6 * m

/-- A candidate only requires a direct calculation at shifts that pass the
original cutoff and all restricted bounds. The small divisor C of 720720
can record complete prime-power factors of the shifted integer. -/
def H2 : Prop :=
  ∃ t : ℕ, 0 < t ∧
    (∀ k ∈ ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24} : Finset ℕ),
      Nat.Prime ((720720 / k) * t - 1)) ∧
    ∀ k : ℕ, 0 < k → k ≤ 720720*t →
      k ∉ ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24} : Finset ℕ) →
      (k+3)^8 ≤ 45197^8*(720720*t-k) →
      (∀ A B C u : ℕ, A*B = 780296143507862696557498656000 → C ∣ 720720 →
        C*u = 720720*t-k → A.Coprime B → A.Coprime u → C.Coprime B → C.Coprime u →
        (k+3)^6 * (C*B) ≤ (σ 0 (C*B))^6 * (720720*t-k)) →
      σ 0 (720720*t-k) ≤ k+2

theorem sharpCoprime : H1 := by
  intro A B m hAB hab ham
  have posA : 0 < A := by by_contra! h; simp [show A = 0 by omega] at hAB
  have posTau : 0 < σ 0 A := by
    rw [ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr posA.ne'⟩
  obtain ⟨peakCount, peakBound⟩ := peakFacts
  have h := peakBound (A*m)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ham,
    ← peakCount, ← hAB, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab,
    mul_pow, mul_pow] at h
  have aux : ((σ 0 A)^6*A) * ((σ 0 m)^6*B) ≤ ((σ 0 A)^6*A) * ((σ 0 B)^6*m) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  exact le_of_mul_le_mul_left aux (Nat.mul_pos (pow_pos posTau _) posA)

/-- For coprime factors the right-hand factor actually attains the bound. -/
theorem maximizer {A B : ℕ} (product : A*B = 780296143507862696557498656000)
    (coprime : A.Coprime B) : A.Coprime B ∧ 0 < B ∧
    ∀ m : ℕ, A.Coprime m → (σ 0 m)^6 * B ≤ (σ 0 B)^6 * m := by
  refine ⟨coprime, ?_, fun m hm => sharpCoprime A B m product coprime hm⟩
  by_contra! h
  simp [show B = 0 by omega] at product

/-- After fixing a complete coprime factor C, the corresponding sharp
bound is attained at C*B. The maximizer for the remaining part is B. -/
theorem sharpWithFactor (bounds : H1) {A B C u : ℕ}
    (product : A*B = 780296143507862696557498656000)
    (ab : A.Coprime B) (au : A.Coprime u) (cb : C.Coprime B) (cu : C.Coprime u) :
    (σ 0 (C*u))^6*(C*B) ≤ (σ 0 (C*B))^6*(C*u) := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cu,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cb, mul_pow, mul_pow]
  calc
    _ = ((σ 0 C)^6*C) * ((σ 0 u)^6*B) := by ring
    _ ≤ ((σ 0 C)^6*C) * ((σ 0 B)^6*u) :=
      Nat.mul_le_mul_left _ (bounds A B u product ab au)
    _ = _ := by ring

private theorem remainingCount : σ 0 3905707004975257109 = 4096 := by
  let P : Finset ℕ := {17,19,23,29,31,37,41,43,47,53,59,61}
  have prime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have value : ∏ p ∈ P, p = 3905707004975257109 := by decide
  rw [← value, ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime P prime]
  calc
    (∏ p ∈ P, σ 0 p) = ∏ _p ∈ P, (2:ℕ) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      simpa using (ArithmeticFunction.sigma_zero_apply_prime_pow (i := 1) (prime p hp))
    _ = 4096 := by decide

/-- The exact sixth-power inequality when 2, 3, 5, 7, 11 and 13 are absent. -/
theorem coprimePrimorial {m : ℕ} (hm : Nat.Coprime 30030 m) :
    (σ 0 m)^6 * 3905707004975257109 ≤ 4096^6 * m := by
  have ha : Nat.Coprime 199783584000 m :=
    (hm.pow_left 8).coprime_dvd_left (by decide : 199783584000 ∣ (30030:ℕ)^8)
  simpa only [remainingCount] using
    (sharpCoprime 199783584000 3905707004975257109 m (by decide) (by decide) ha)

/-- The constant is attained by the product of the twelve primes from 17 to 61. -/
theorem primorialEquality : Nat.Coprime 30030 3905707004975257109 ∧
    (σ 0 3905707004975257109)^6 * 3905707004975257109 =
      4096^6 * 3905707004975257109 := ⟨by decide, by rw [remainingCount]⟩

/-- A modular test on the shift alone certifies the smaller cutoff. -/
theorem screenedShift {t k : ℕ} (hk : k ≤ 720720*t) (coprime : Nat.Coprime 30030 k)
    (cut : 4096^6*(720720*t-k) < (k+3)^6 * 3905707004975257109) :
    σ 0 (720720*t-k) ≤ k+2 := by
  let g := Nat.gcd 30030 (720720*t-k)
  have gbase : g ∣ 30030 := Nat.gcd_dvd_left ..
  have gtotal : g ∣ 720720*t :=
    gbase.trans (dvd_mul_of_dvd_left (by decide : 30030 ∣ 720720) _)
  have gk : g ∣ k := by
    have h := Nat.dvd_sub gtotal (Nat.gcd_dvd_right 30030 (720720*t-k))
    rwa [Nat.sub_sub_self hk] at h
  have common := Nat.dvd_gcd gbase gk
  rw [coprime.gcd_eq_one] at common
  have hcop : Nat.Coprime 30030 (720720*t-k) := Nat.dvd_one.mp common
  by_contra! fail
  have big : k+3 ≤ σ 0 (720720*t-k) := by omega
  exact (Nat.not_lt_of_ge ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_left big 6)).trans
    (coprimePrimorial hcop))) cut

theorem main : H1 → H2 → OMA.R_Erdos647_erdos_647_R2.H3 := by
  intro localBounds hx
  obtain ⟨t, ht, primes, checks⟩ := hx
  refine ⟨t, ht, primes, ?_⟩
  intro k pos le outside old
  by_contra! fail
  have big : k+3 ≤ σ 0 (720720*t-k) := by omega
  apply (Nat.not_lt_of_ge (checks k pos le outside old ?_)) fail
  intro A B C u product _hsmall split ab au cb cu
  have h := sharpWithFactor localBounds product ab au cb cu
  rw [split] at h
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left big 6)).trans h

/-- Passing only the sharp cutoffs is equivalent to the original search. -/
theorem exactSearch : H2 ↔ OMA.R_Erdos647_erdos_647_R2.H3 := by
  refine ⟨main sharpCoprime, ?_⟩
  rintro ⟨t, ht, primes, checks⟩
  exact ⟨t, ht, primes, fun k pos le outside old _ => checks k pos le outside old⟩

end OMA.R_Erdos647_erdos_647_R2_H3_R1
