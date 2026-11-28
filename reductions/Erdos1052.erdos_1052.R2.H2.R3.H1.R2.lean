import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R3
import Mathlib

/-!
# Mersenne-Fermat Exclusion and Shift Valuation Split for Simple Mersenne Primes

To bound the count of simple Mersenne primes in a completion of a fixed odd
powerful core, we first prove unconditionally that no number above three of the
form `2 ^ k - 1` can divide `2 ^ a + 1`. Factoring the unitary divisor sum of
`2 ^ a * c` shows that every simple Mersenne prime in `S` is either equal to `3`,
a prime factor of the fixed odd core divisor sum, or a divisor of `1 + p` for
some `p ∈ S`. Splitting the shift divisors according to whether `32` divides
`1 + p` reduces the bound to `H1` and `H2`.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R2

/-- Uniform bound on simple Mersenne primes in `S` dividing a low-2-adic shift `1 + p`. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      (S.filter (fun q => ordCompl[2] (1 + q) = 1 ∧ ∃ p ∈ S, q ∣ 1 + p ∧ ¬ 32 ∣ 1 + p)).card ≤ K

/-- Uniform bound on simple Mersenne primes in `S` dividing a high-2-adic shift `1 + p`. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      (S.filter (fun q => ordCompl[2] (1 + q) = 1 ∧ ∃ p ∈ S, q ∣ 1 + p ∧ 32 ∣ 1 + p)).card ≤ K

lemma sigma_power_two_times {a c : ℕ} (ha : 0 < a) (hc : Odd c) :
    (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) =
      (2 ^ a + 1) * (∏ p ∈ c.primeFactors, (1 + p ^ c.factorization p)) := by
  have hb : (2 : ℕ) ^ a ≠ 0 := pow_ne_zero _ (by decide)
  have hc0 : c ≠ 0 := hc.pos.ne'
  have h2c : ¬ 2 ∣ c := by obtain ⟨i, hi⟩ := hc; omega
  have h2 : 2 ∉ c.primeFactors := fun h => h2c (Nat.dvd_of_mem_primeFactors h)
  have hfac (p : ℕ) : (2 ^ a * c).factorization p =
      (if 2 = p then a else 0) + c.factorization p := by
    rw [Nat.factorization_mul hb hc0, Nat.prime_two.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.single_apply, eq_comm]
  have h2val : c.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2c
  rw [Nat.primeFactors_mul hb hc0, Nat.primeFactors_prime_pow ha.ne' Nat.prime_two,
    Finset.singleton_union, Finset.prod_insert h2, hfac]
  simp only [if_true, h2val, add_zero, Nat.add_comm 1 (2 ^ a)]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have he : 2 ≠ p := fun e => h2 (e ▸ hp)
  rw [hfac, if_neg he, zero_add]

lemma mersenne_not_dvd_two_pow_add_one {q k a : ℕ} (hq3 : 3 < q) (hk : q + 1 = 2 ^ k) :
    ¬ q ∣ 2 ^ a + 1 := by
  intro hd
  have hk3 : 3 ≤ k := by
    by_contra! hlt
    have hle : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  let r := a % k
  let m := a / k
  have hr : r < k := Nat.mod_lt a (by omega)
  have ha_eq : k * m + r = a := Nat.div_add_mod a k
  have h2k : (2 : ZMod q) ^ k = 1 := by
    have hcast : ((q + 1 : ℕ) : ZMod q) = ((2 ^ k : ℕ) : ZMod q) := congrArg Nat.cast hk
    simpa [ZMod.natCast_self] using hcast.symm
  have h2a : (2 : ZMod q) ^ a = (2 : ZMod q) ^ r := by
    rw [← ha_eq, pow_add, pow_mul, h2k, one_pow, one_mul]
  have hza : (2 : ZMod q) ^ a + 1 = 0 := by
    have hz : ((2 ^ a + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff (2 ^ a + 1) q).mpr hd
    simpa using hz
  have hzr : ((2 ^ r + 1 : ℕ) : ZMod q) = 0 := by
    push_cast
    rw [← h2a]
    exact hza
  have hdr : q ∣ 2 ^ r + 1 := (ZMod.natCast_eq_zero_iff (2 ^ r + 1) q).mp hzr
  have hq_le : q ≤ 2 ^ r + 1 := Nat.le_of_dvd (by positivity) hdr
  have hr_pow : 2 ^ r ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hk_split : 2 ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  have hk_ge : 4 ≤ 2 ^ (k - 1) := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ k - 1 by omega))
  omega

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R3.H1 := by
  classical
  intro h1 h2 c hc powerful
  obtain ⟨K1, hK1⟩ := h1 c hc powerful
  obtain ⟨K2, hK2⟩ := h2 c hc powerful
  let σ := ∏ r ∈ c.primeFactors, (1 + r ^ c.factorization r)
  have hσ0 : σ ≠ 0 := (Finset.prod_pos fun _ _ => by positivity).ne'
  refine ⟨1 + σ.primeFactors.card + K1 + K2, ?_⟩
  intro a S b u ha hScard hSsub hp hbal
  have h1' := hK1 a S ha hScard hSsub hp hbal
  have h2' := hK2 a S ha hScard hSsub hp hbal
  let M := S.filter (fun q => ordCompl[2] (1 + q) = 1)
  let M1 := S.filter (fun q => ordCompl[2] (1 + q) = 1 ∧ ∃ p ∈ S, q ∣ 1 + p ∧ ¬ 32 ∣ 1 + p)
  let M2 := S.filter (fun q => ordCompl[2] (1 + q) = 1 ∧ ∃ p ∈ S, q ∣ 1 + p ∧ 32 ∣ 1 + p)
  have hu : u = (2 ^ a + 1) * σ := sigma_power_two_times (by omega : 0 < a) hc
  have hcov : M ⊆ ({3} : Finset ℕ) ∪ σ.primeFactors ∪ M1 ∪ M2 := by
    intro q hqM
    obtain ⟨hqS, hq1⟩ := Finset.mem_filter.mp hqM
    have hqp : q.Prime := (hp q hqS).1
    have hq3_ge : 3 ≤ q := (Finset.mem_Icc.mp (hSsub hqS)).1
    have hd : q ∣ ((2 ^ a + 1) * σ) * (∏ p ∈ S, (1 + p)) := by
      rw [← hu, hbal]
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hqS) (2 * b)
    rcases hqp.dvd_mul.mp hd with hleft | hright
    · rcases hqp.dvd_mul.mp hleft with hseed | hsig
      · have hk : q + 1 = 2 ^ (1 + q).factorization 2 := by
          have hpow := Nat.ordProj_mul_ordCompl_eq_self (1 + q) 2
          rw [hq1, mul_one] at hpow
          omega
        have hq_eq3 : q = 3 := by
          by_contra hne
          exact mersenne_not_dvd_two_pow_add_one (by omega : 3 < q) hk hseed
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_singleton.mpr hq_eq3)))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hqp, hsig, hσ0⟩)))
    · obtain ⟨p, hpS, hqp1⟩ := (hqp.prime.dvd_finsetProd_iff _).mp hright
      by_cases h32 : 32 ∣ 1 + p
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hqS, hq1, p, hpS, hqp1, h32⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hqS, hq1, p, hpS, hqp1, h32⟩))
  have hc1 : M.card ≤ (({3} : Finset ℕ) ∪ σ.primeFactors ∪ M1 ∪ M2).card :=
    Finset.card_le_card hcov
  have hc2 : (({3} : Finset ℕ) ∪ σ.primeFactors ∪ M1 ∪ M2).card ≤
      (({3} : Finset ℕ) ∪ σ.primeFactors ∪ M1).card + M2.card :=
    Finset.card_union_le _ _
  have hc3 : (({3} : Finset ℕ) ∪ σ.primeFactors ∪ M1).card ≤
      (({3} : Finset ℕ) ∪ σ.primeFactors).card + M1.card :=
    Finset.card_union_le _ _
  have hc4 : (({3} : Finset ℕ) ∪ σ.primeFactors).card ≤
      ({3} : Finset ℕ).card + σ.primeFactors.card :=
    Finset.card_union_le _ _
  have hc5 : ({3} : Finset ℕ).card = 1 := Finset.card_singleton 3
  change M.card ≤ 1 + σ.primeFactors.card + K1 + K2
  change M1.card ≤ K1 at h1'
  change M2.card ≤ K2 at h2'
  omega

end OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R2
