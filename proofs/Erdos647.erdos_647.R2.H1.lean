import OMAReductions.R_Erdos647_erdos_647_R2

/-!
# Proof of `Erdos647.erdos_647.R2.H1`

Proves that `(σ 0 m) ^ 8 ≤ 45197 ^ 8 * m` for all `m : ℕ`.

For `m = 0`, `σ 0 0 = 0`. For `m > 0`, `σ 0 m = ∏ p ∈ m.primeFactors, (m.factorization p + 1)`
and `m = ∏ p ∈ m.primeFactors, p ^ (m.factorization p)`. For every prime `p ≥ 256`,
`(e + 1) ^ 8 ≤ p ^ e` holds for all `e : ℕ`. For each of the 54 primes `p ≤ 251`, an explicit
peak exponent `peakExp p` satisfies `(e + 1) ^ 8 * p ^ (peakExp p) ≤ (peakExp p + 1) ^ 8 * p ^ e`
for all `e : ℕ`, and direct integer arithmetic shows
`∏ (peakExp p + 1) ^ 8 ≤ 45197 ^ 8 * ∏ p ^ (peakExp p)` over the 54 primes `≤ 251`.
-/

open ArithmeticFunction.sigma Finset

namespace Erdos647R2H1Proof

private lemma succ_le_two_pow (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => decide
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

private lemma pow_eight_le_of_ge_256 {p : ℕ} (hp : 256 ≤ p) (e : ℕ) : (e + 1) ^ 8 ≤ p ^ e := by
  calc (e + 1) ^ 8 ≤ (2 ^ e) ^ 8 := Nat.pow_le_pow_left (succ_le_two_pow e) 8
    _ = (2 ^ 8) ^ e := by rw [← pow_mul, mul_comm, pow_mul]
    _ = 256 ^ e := by norm_num
    _ ≤ p ^ e := Nat.pow_le_pow_left hp e

private lemma pow_eight_bound_of_peak {p e₀ : ℕ}
    (hsmall : ∀ e ≤ e₀ + 12, (e + 1) ^ 8 * p ^ e₀ ≤ (e₀ + 1) ^ 8 * p ^ e)
    (hstep : ∀ e ≥ e₀ + 12, (e + 2) ^ 8 ≤ p * (e + 1) ^ 8) :
    ∀ e : ℕ, (e + 1) ^ 8 * p ^ e₀ ≤ (e₀ + 1) ^ 8 * p ^ e := by
  intro e
  by_cases hle : e ≤ e₀ + 12
  · exact hsmall e hle
  · have hge : e₀ + 12 ≤ e := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
    clear hle hge
    induction k with
    | zero => simpa using hsmall (e₀ + 12) le_rfl
    | succ k ih =>
      have h1 : (e₀ + 12 + k + 2) ^ 8 ≤ p * (e₀ + 12 + k + 1) ^ 8 :=
        hstep (e₀ + 12 + k) (by omega)
      have h2 := Nat.mul_le_mul_right (p ^ e₀) h1
      have h3 : p * ((e₀ + 12 + k + 1) ^ 8 * p ^ e₀) ≤
          p * ((e₀ + 1) ^ 8 * p ^ (e₀ + 12 + k)) := Nat.mul_le_mul_left p ih
      calc (e₀ + 12 + (k + 1) + 1) ^ 8 * p ^ e₀
          = (e₀ + 12 + k + 2) ^ 8 * p ^ e₀ := by ring_nf
        _ ≤ p * (e₀ + 12 + k + 1) ^ 8 * p ^ e₀ := h2
        _ = p * ((e₀ + 12 + k + 1) ^ 8 * p ^ e₀) := by ring
        _ ≤ p * ((e₀ + 1) ^ 8 * p ^ (e₀ + 12 + k)) := h3
        _ = (e₀ + 1) ^ 8 * p ^ (e₀ + 12 + (k + 1)) := by rw [pow_succ]; ring

private lemma step_ge_12 {p e : ℕ} (hp : 2 ≤ p) (he : 12 ≤ e) :
    (e + 2) ^ 8 ≤ p * (e + 1) ^ 8 := by
  have h1 : (e + 2) ^ 8 ≤ 2 * (e + 1) ^ 8 := by
    set t := e + 1
    have h13 : 13 ≤ t := by omega
    have ha : 13 * t ^ 7 ≤ t ^ 8 := by
      calc 13 * t ^ 7 ≤ t * t ^ 7 := Nat.mul_le_mul_right _ h13
        _ = t ^ 8 := (pow_succ' t 7).symm
    have hb : 13 * t ^ 6 ≤ t ^ 7 := by
      calc 13 * t ^ 6 ≤ t * t ^ 6 := Nat.mul_le_mul_right _ h13
        _ = t ^ 7 := (pow_succ' t 6).symm
    have hc : 13 * t ^ 5 ≤ t ^ 6 := by
      calc 13 * t ^ 5 ≤ t * t ^ 5 := Nat.mul_le_mul_right _ h13
        _ = t ^ 6 := (pow_succ' t 5).symm
    have hd : 13 * t ^ 4 ≤ t ^ 5 := by
      calc 13 * t ^ 4 ≤ t * t ^ 4 := Nat.mul_le_mul_right _ h13
        _ = t ^ 5 := (pow_succ' t 4).symm
    have hf : 13 * t ^ 3 ≤ t ^ 4 := by
      calc 13 * t ^ 3 ≤ t * t ^ 3 := Nat.mul_le_mul_right _ h13
        _ = t ^ 4 := (pow_succ' t 3).symm
    have hg : 13 * t ^ 2 ≤ t ^ 3 := by
      calc 13 * t ^ 2 ≤ t * t ^ 2 := Nat.mul_le_mul_right _ h13
        _ = t ^ 3 := (pow_succ' t 2).symm
    have hh : 13 * t ≤ t ^ 2 := by
      calc 13 * t ≤ t * t := Nat.mul_le_mul_right _ h13
        _ = t ^ 2 := (sq t).symm
    have hexp : (t + 1) ^ 8 = t ^ 8 + 8 * t ^ 7 + 28 * t ^ 6 + 56 * t ^ 5 + 70 * t ^ 4 +
        56 * t ^ 3 + 28 * t ^ 2 + 8 * t + 1 := by ring
    have he2 : e + 2 = t + 1 := by omega
    rw [he2, hexp]
    omega
  exact h1.trans (Nat.mul_le_mul_right _ hp)

private def peakExp (p : ℕ) : ℕ :=
  if p = 2 then 11
  else if p = 3 then 6
  else if p = 5 then 4
  else if p ≤ 7 then 3
  else if p ≤ 23 then 2
  else if p ≤ 251 then 1
  else 0

private def smallPrimesList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251]

private lemma smallPrimesList_nodup : smallPrimesList.Nodup := by decide +kernel

private lemma smallPrimesList_all_prime : ∀ p ∈ smallPrimesList, p.Prime := by decide +kernel

private lemma mem_smallPrimesList_of_prime_lt {p : ℕ} (hp : p.Prime) (hlt : p < 256) :
    p ∈ smallPrimesList := by
  have hall : ∀ n : Fin 256, n.val.Prime → n.val ∈ smallPrimesList := by decide +kernel
  exact hall ⟨p, hlt⟩ hp

private lemma peakExp_eq_zero_of_ge_256 {p : ℕ} (hp : 256 ≤ p) : peakExp p = 0 := by
  unfold peakExp
  split_ifs <;> omega

private def smallPrimes : Finset ℕ := smallPrimesList.toFinset

private lemma prime_peak_bound_small :
    ∀ p ∈ smallPrimesList,
      ∀ e : Fin (peakExp p + 13),
        (e.val + 1) ^ 8 * p ^ (peakExp p) ≤ (peakExp p + 1) ^ 8 * p ^ e.val := by
  decide +kernel

private lemma prime_peak_bound (p : ℕ) (hp : p.Prime) (e : ℕ) :
    (e + 1) ^ 8 * p ^ (peakExp p) ≤ (peakExp p + 1) ^ 8 * p ^ e := by
  by_cases hp256 : p < 256
  · have hmem : p ∈ smallPrimesList := mem_smallPrimesList_of_prime_lt hp hp256
    refine pow_eight_bound_of_peak ?_ (fun e' he' => step_ge_12 hp.two_le (by omega)) e
    intro e' he'
    exact prime_peak_bound_small p hmem ⟨e', by omega⟩
  · have h0 : peakExp p = 0 := by
      unfold peakExp
      split_ifs <;> omega
    rw [h0, pow_zero, mul_one, zero_add, one_pow, one_mul]
    exact pow_eight_le_of_ge_256 (by omega) e

private lemma prod_peak_list_le :
    (smallPrimesList.map (fun p => (peakExp p + 1) ^ 8)).prod ≤
      45197 ^ 8 * (smallPrimesList.map (fun p => p ^ (peakExp p))).prod := by
  decide +kernel

private lemma prod_peak_le :
    (∏ p ∈ smallPrimes, (peakExp p + 1) ^ 8) ≤
      45197 ^ 8 * (∏ p ∈ smallPrimes, p ^ (peakExp p)) := by
  unfold smallPrimes
  rw [List.prod_toFinset _ smallPrimesList_nodup, List.prod_toFinset _ smallPrimesList_nodup]
  exact prod_peak_list_le

private lemma peak_num_ge_den (p : ℕ) (hp : p ∈ smallPrimes) :
    p ^ (peakExp p) ≤ (peakExp p + 1) ^ 8 := by
  have hp_prime : p.Prime := smallPrimesList_all_prime p (List.mem_toFinset.mp hp)
  have h := prime_peak_bound p hp_prime 0
  simpa using h

end Erdos647R2H1Proof

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R2.H1 := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hsig : σ 0 m = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm.ne']
  have hfac : ∏ p ∈ m.primeFactors, p ^ (m.factorization p) = m :=
    Nat.prod_factorization_pow_eq_self hm.ne'
  rw [hsig, ← Finset.prod_pow]
  have h1 : (∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ 8) *
      (∏ p ∈ m.primeFactors, p ^ (Erdos647R2H1Proof.peakExp p)) ≤
      (∏ p ∈ m.primeFactors, (Erdos647R2H1Proof.peakExp p + 1) ^ 8) *
      (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' fun p hp =>
      Erdos647R2H1Proof.prime_peak_bound p (Nat.prime_of_mem_primeFactors hp) (m.factorization p)
  rw [hfac] at h1
  set A := m.primeFactors ∩ Erdos647R2H1Proof.smallPrimes
  set B := m.primeFactors \ Erdos647R2H1Proof.smallPrimes
  have hdisjAB : Disjoint A B :=
    Finset.disjoint_left.mpr fun p hpA hpB => (Finset.mem_sdiff.mp hpB).2 (Finset.mem_inter.mp hpA).2
  have hunionAB : A ∪ B = m.primeFactors := by
    ext p; simp only [A, B, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hB_zero : ∀ p ∈ B, Erdos647R2H1Proof.peakExp p = 0 := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
    have hp_not : p ∉ Erdos647R2H1Proof.smallPrimes := (Finset.mem_sdiff.mp hp).2
    have hge256 : 256 ≤ p := by
      by_contra hlt
      exact hp_not (List.mem_toFinset.mpr
        (Erdos647R2H1Proof.mem_smallPrimesList_of_prime_lt hp_prime (by omega)))
    exact Erdos647R2H1Proof.peakExp_eq_zero_of_ge_256 hge256
  have hden_eq : (∏ p ∈ m.primeFactors, p ^ (Erdos647R2H1Proof.peakExp p)) =
      ∏ p ∈ A, p ^ (Erdos647R2H1Proof.peakExp p) := by
    rw [← hunionAB, Finset.prod_union hdisjAB]
    have hB1 : ∏ p ∈ B, p ^ (Erdos647R2H1Proof.peakExp p) = 1 :=
      Finset.prod_eq_one fun p hp => by rw [hB_zero p hp, pow_zero]
    rw [hB1, mul_one]
  have hnum_eq : (∏ p ∈ m.primeFactors, (Erdos647R2H1Proof.peakExp p + 1) ^ 8) =
      ∏ p ∈ A, (Erdos647R2H1Proof.peakExp p + 1) ^ 8 := by
    rw [← hunionAB, Finset.prod_union hdisjAB]
    have hB1 : ∏ p ∈ B, (Erdos647R2H1Proof.peakExp p + 1) ^ 8 = 1 :=
      Finset.prod_eq_one fun p hp => by rw [hB_zero p hp]; norm_num
    rw [hB1, mul_one]
  rw [hden_eq, hnum_eq] at h1
  set C := Erdos647R2H1Proof.smallPrimes \ A
  have hAsub : A ⊆ Erdos647R2H1Proof.smallPrimes := Finset.inter_subset_right
  have hdisjAC : Disjoint A C := Finset.disjoint_sdiff
  have hunionAC : A ∪ C = Erdos647R2H1Proof.smallPrimes := Finset.union_sdiff_of_subset hAsub
  have hC_le : (∏ p ∈ C, p ^ (Erdos647R2H1Proof.peakExp p)) ≤
      ∏ p ∈ C, (Erdos647R2H1Proof.peakExp p + 1) ^ 8 :=
    Finset.prod_le_prod' fun p hp =>
      Erdos647R2H1Proof.peak_num_ge_den p (Finset.mem_sdiff.mp hp).1
  have hden_pos : 0 < ∏ p ∈ Erdos647R2H1Proof.smallPrimes, p ^ (Erdos647R2H1Proof.peakExp p) := by
    refine Finset.prod_pos fun p hp =>
      pow_pos (Erdos647R2H1Proof.smallPrimesList_all_prime p (List.mem_toFinset.mp hp)).pos _
  have hmul : (∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ 8) *
      (∏ p ∈ Erdos647R2H1Proof.smallPrimes, p ^ (Erdos647R2H1Proof.peakExp p)) ≤
      (∏ p ∈ Erdos647R2H1Proof.smallPrimes, (Erdos647R2H1Proof.peakExp p + 1) ^ 8) * m := by
    calc (∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ 8) *
          (∏ p ∈ Erdos647R2H1Proof.smallPrimes, p ^ (Erdos647R2H1Proof.peakExp p))
        = ((∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ 8) *
            (∏ p ∈ A, p ^ (Erdos647R2H1Proof.peakExp p))) *
            (∏ p ∈ C, p ^ (Erdos647R2H1Proof.peakExp p)) := by
          rw [← hunionAC, Finset.prod_union hdisjAC, mul_assoc]
      _ ≤ ((∏ p ∈ A, (Erdos647R2H1Proof.peakExp p + 1) ^ 8) * m) *
            (∏ p ∈ C, (Erdos647R2H1Proof.peakExp p + 1) ^ 8) :=
          Nat.mul_le_mul h1 hC_le
      _ = ((∏ p ∈ A, (Erdos647R2H1Proof.peakExp p + 1) ^ 8) *
            (∏ p ∈ C, (Erdos647R2H1Proof.peakExp p + 1) ^ 8)) * m := by ring
      _ = (∏ p ∈ Erdos647R2H1Proof.smallPrimes, (Erdos647R2H1Proof.peakExp p + 1) ^ 8) * m := by
          rw [← Finset.prod_union hdisjAC, hunionAC]
  have hfin : (∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ 8) *
      (∏ p ∈ Erdos647R2H1Proof.smallPrimes, p ^ (Erdos647R2H1Proof.peakExp p)) ≤
      (45197 ^ 8 * m) *
      (∏ p ∈ Erdos647R2H1Proof.smallPrimes, p ^ (Erdos647R2H1Proof.peakExp p)) := by
    calc (∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ 8) *
          (∏ p ∈ Erdos647R2H1Proof.smallPrimes, p ^ (Erdos647R2H1Proof.peakExp p))
        ≤ (∏ p ∈ Erdos647R2H1Proof.smallPrimes, (Erdos647R2H1Proof.peakExp p + 1) ^ 8) * m := hmul
      _ ≤ (45197 ^ 8 * ∏ p ∈ Erdos647R2H1Proof.smallPrimes, p ^ (Erdos647R2H1Proof.peakExp p)) * m :=
          Nat.mul_le_mul_right m Erdos647R2H1Proof.prod_peak_le
      _ = (45197 ^ 8 * m) *
            (∏ p ∈ Erdos647R2H1Proof.smallPrimes, p ^ (Erdos647R2H1Proof.peakExp p)) := by ring
  exact Nat.le_of_mul_le_mul_right hfin hden_pos
