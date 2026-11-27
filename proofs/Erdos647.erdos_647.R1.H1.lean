import OMAReductions.R_Erdos647_erdos_647_R1

namespace OMA.DivisorSixthBound

def peak (p : ℕ) : ℕ :=
  if p=2 then 8 else if p=3 then 4 else if p=5 then 3 else
    if p=7 ∨ p=11 then 2 else if p<64 then 1 else 0

lemma ratio_step (p K a : ℕ) (hK : K ≤ a)
    (hstep : (K+2)^6 ≤ p*(K+1)^6) : (a+2)^6 ≤ p*(a+1)^6 := by
  have hc : (a+2)*(K+1) ≤ (a+1)*(K+2) := by nlinarith
  have hp := Nat.pow_le_pow_left hc 6
  rw [mul_pow, mul_pow] at hp
  have hs := Nat.mul_le_mul_left ((a+1)^6) hstep
  have he : (a+2)^6*(K+1)^6 ≤ (p*(a+1)^6)*(K+1)^6 := by nlinarith only [hp,hs]
  exact (mul_le_mul_iff_left₀ (show 0 < (K+1)^6 by positivity)).mp he

lemma peak_bound (p K : ℕ) (_hp : 0 < p)
    (hstep : (K+2)^6 ≤ p*(K+1)^6)
    (hsmall : ∀ a ≤ K, (a+1)^6*p^K ≤ (K+1)^6*p^a) :
    ∀ a : ℕ, (a+1)^6*p^K ≤ (K+1)^6*p^a := by
  intro a
  by_cases ha : a ≤ K
  · exact hsmall a ha
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (by omega : K ≤ a)
  clear ha
  induction t with
  | zero => simp
  | succ t ih =>
    have hs := ratio_step p K (K+t) (by omega) hstep
    have hm := Nat.mul_le_mul_right (p^K) hs
    have hi := Nat.mul_le_mul_left p ih
    rw [show K+(t+1)=K+t+1 by omega, pow_succ p (K+t)]
    nlinarith only [hm,hi]

lemma certificates (p : ℕ) (hp : p.Prime) :
    (peak p+2)^6 ≤ p*(peak p+1)^6 ∧
      ∀ a ≤ peak p, (a+1)^6*p^(peak p) ≤ (peak p+1)^6*p^a := by
  by_cases hlarge : 64 ≤ p
  · have hk : peak p = 0 := by
      simp only [peak]
      split_ifs <;> omega
    rw [hk]
    constructor
    · norm_num
      exact hlarge
    · intro a ha
      have : a=0 := by omega
      subst a
      simp
  · have hlt : p < 64 := by omega
    interval_cases p <;> first
      | solve | norm_num at hp
      | constructor
        · norm_num [peak]
        · intro a ha
          norm_num [peak] at ha
          interval_cases a <;> norm_num [peak]

def ratio (p : ℕ) : ℚ := (peak p+1)^6/(p : ℚ)^(peak p)

lemma bound (p a : ℕ) (hp : p.Prime) :
    ((a+1 : ℕ) : ℚ)^6 ≤ ratio p*(p : ℚ)^a := by
  have hc := certificates p hp
  have hb := peak_bound p (peak p) hp.pos hc.1 hc.2 a
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hpos : (0 : ℚ) < (p : ℚ)^(peak p) := by positivity
  dsimp [ratio]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpos).mpr
  exact_mod_cast hb

def smallPrimes : Finset ℕ := {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61}

lemma ratio_one (p : ℕ) (hp : p.Prime) (hnot : p ∉ smallPrimes) : ratio p = 1 := by
  have hlarge : 64 ≤ p := by
    by_contra! h
    interval_cases p <;> first
      | solve | norm_num at hp
      | solve | norm_num [smallPrimes] at hnot
  have hk : peak p = 0 := by
    simp only [peak]
    split_ifs <;> omega
  simp [ratio, hk]

lemma ratio_ge_one (p : ℕ) (hp : p.Prime) : 1 ≤ ratio p := by
  simpa using bound p 0 hp

lemma small_prime (p : ℕ) (hp : p ∈ smallPrimes) : p.Prime := by
  simp only [smallPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma constant : (∏ p ∈ smallPrimes, ratio p) ≤ (139 : ℚ)^6 := by
  norm_num [smallPrimes, ratio, peak]

lemma product_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, ratio p) ≤ (139 : ℚ)^6 := by
  have he : (∏ p ∈ S ∩ smallPrimes, ratio p) = ∏ p ∈ S, ratio p := by
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hp hn
    have hnot : p ∉ smallPrimes := fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)
    exact ratio_one p (hS p hp) hnot
  rw [← he]
  apply le_trans ?_ constant
  apply Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
  · intro p hp
    exact le_trans (by norm_num : (0 : ℚ) ≤ 1)
      (ratio_ge_one p (small_prime p (Finset.mem_inter.mp hp).2))
  · intro p hp hn
    exact ratio_ge_one p (small_prime p hp)

end OMA.DivisorSixthBound

-- Step Erdos647.erdos_647.R1.H1: hypothesis H1 of reduction Erdos647.erdos_647.R1
-- Credit: @DeepDuke
-- H1 := ∀ m : ℕ, (σ 0 m) ^ 6 ≤ 139 ^ 6 * m  -- A candidate needs divisor counts only for the final O(n^(1/6)) shifts.

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R1.H1 := by
  intro m
  by_cases hm : m=0
  · subst m
    norm_num
  have hS : ∀ p ∈ m.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hp := Finset.prod_le_prod (s := m.primeFactors)
    (f := fun p => (((m.factorization p+1 : ℕ) : ℚ)^6))
    (g := fun p => OMA.DivisorSixthBound.ratio p*(p : ℚ)^(m.factorization p))
    (fun p _ => by positivity)
    (fun p hp => OMA.DivisorSixthBound.bound p (m.factorization p) (hS p hp))
  rw [Finset.prod_pow, Finset.prod_mul_distrib] at hp
  have htau : (ArithmeticFunction.sigma 0 m : ℚ) =
      ∏ p ∈ m.primeFactors, ((m.factorization p+1 : ℕ) : ℚ) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm, Nat.cast_prod]
  have hmprod : (∏ p ∈ m.primeFactors, (p : ℚ)^(m.factorization p)) = m := by
    have hh := congrArg (fun n : ℕ => (n : ℚ)) (Nat.prod_primeFactors_pow_factorization hm)
    simpa only [Nat.cast_prod, Nat.cast_pow] using hh.symm
  rw [← htau, hmprod] at hp
  have hc := mul_le_mul_of_nonneg_right (OMA.DivisorSixthBound.product_bound m.primeFactors hS)
    (show (0 : ℚ) ≤ m by positivity)
  exact_mod_cast hp.trans hc

