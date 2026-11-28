import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1

/-!
# Pairwise-disjoint shift children and binary versus higher-order shift branching

Reduction of `Erdos1052.erdos_1052.R2.H2.R3.H1.R1.H2` (uniform bound on total shift branching
`sum_{p in S} ((S.filter (fun r => r | 1 + p)).card - 1)` for a fixed odd powerful core `c`).

For every `p in S`, let `C(p) = S.filter (fun r => r | 1 + p)` be the set of simple primes in `S`
dividing `1 + p`. Using `odd_balance_eq` from the parent reduction we prove:
1. Pairwise disjointness (`children_pairwise_disjoint`): every `r in S` divides `c * prod_{q in S} q`
   to the exact first power, so `r` divides `1 + p` for at most one `p in S`.
2. Exact set-cardinality reformulation (`branching_sum_eq_nonmax_children_card`): removing the
   maximum element from each nonempty `C(p)` yields pairwise-disjoint subsets of `S` whose union
   is `{r in S | exists p in S, exists r' in S, r < r' and r * r' | 1 + p}` (each element satisfying
   `2 * r^2 < 1 + p`), with cardinality identically equal to the target branching sum.
3. Exact multiplicity decomposition: every branching vertex `p in S` with `2 <= (C p).card` has
   `2 <= cardFactors (ordCompl[2] (1 + p))`. Those with `cardFactors (ordCompl[2] (1 + p)) = 2`
   are precisely the pure binary shifts `ordCompl[2] (1 + p) = r * r'` (`r, r' in S`, `r < r'`),
   each contributing exactly `1` to the sum, while all remaining terms have
   `3 <= cardFactors (ordCompl[2] (1 + p))`.

This splits total shift branching into two independent subproblems:
- `H1`: uniform bound on the count of pure binary-branching vertices `p in S` satisfying
  `exists r in S, exists r' in S, r < r' and ordCompl[2] (1 + p) = r * r'`.
- `H2`: uniform bound on the higher-order shift branching sum restricted to vertices `p in S`
  with `3 <= ArithmeticFunction.cardFactors (ordCompl[2] (1 + p))`.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1_H2_R1

open scoped BigOperators
open ArithmeticFunction
open OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1

/-- Uniform bound on pure binary-branching vertices `p in S` whose shifted odd part is a
product of two distinct primes in `S`. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      (S.filter (fun p => ∃ r ∈ S, ∃ r' ∈ S, r < r' ∧ ordCompl[2] (1 + p) = r * r')).card ≤ K

/-- Uniform bound on total shift branching summed over vertices `p in S` whose shifted odd part
has at least three prime factors with multiplicity. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      (∑ p ∈ S.filter (fun p => 3 ≤ cardFactors (ordCompl[2] (1 + p))),
        ((S.filter (fun r => r ∣ 1 + p)).card - 1)) ≤ K

/-- Valuation of a product of distinct primes at any prime `q`. -/
theorem factorization_prime_prod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (∏ p ∈ S, p).factorization q = if q ∈ S then 1 else 0 := by
  classical
  rw [Nat.factorization_prod (fun p hp => (hS p hp).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by rw [(hS p hp).factorization, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S q _

/-- Each `r in S` divides `1 + p` for at most one `p in S`, so the child sets
`S.filter (fun r => r | 1 + p)` are pairwise disjoint across `p in S`. -/
theorem unique_shift_parent {a c r p₁ p₂ : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p))
    (hrS : r ∈ S) (hp₁ : p₁ ∈ S) (hp₂ : p₂ ∈ S)
    (hd₁ : r ∣ 1 + p₁) (hd₂ : r ∣ 1 + p₂) : p₁ = p₂ := by
  classical
  by_contra hne
  have hp2 : ∀ p ∈ S, p.Prime ∧ p ≠ 2 := fun p h =>
    ⟨(hp p h).1, fun h2 => (hp p h).2 (h2 ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 ha.ne') c)⟩
  have hodd := odd_balance_eq ha hc hp2 hbal
  have hprod_dvd : (∏ p ∈ S, ordCompl[2] (1 + p)) ∣ c * ∏ p ∈ S, p := by
    rw [← hodd]
    exact dvd_mul_left _ _
  have hr2 : ¬ 2 ∣ r := by
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hp r hrS).1).mp h2
    exact (hp2 r hrS).2 this.symm
  have ho₁ : r ∣ ordCompl[2] (1 + p₁) := Nat.dvd_ordCompl_of_dvd_not_dvd hd₁ hr2
  have ho₂ : r ∣ ordCompl[2] (1 + p₂) := Nat.dvd_ordCompl_of_dvd_not_dvd hd₂ hr2
  have hpair_sub : ({p₁, p₂} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hsq_dvd : r ^ 2 ∣ c * ∏ p ∈ S, p := by
    have h1 : r ^ 2 ∣ ordCompl[2] (1 + p₁) * ordCompl[2] (1 + p₂) := by
      rw [sq]; exact Nat.mul_dvd_mul ho₁ ho₂
    have h2 : ordCompl[2] (1 + p₁) * ordCompl[2] (1 + p₂) =
        ∏ p ∈ ({p₁, p₂} : Finset ℕ), ordCompl[2] (1 + p) :=
      (Finset.prod_pair (f := fun p => ordCompl[2] (1 + p)) hne).symm
    rw [h2] at h1
    exact h1.trans ((Finset.prod_dvd_prod_of_subset _ _ _ hpair_sub).trans hprod_dvd)
  have hSprod : (∏ p ∈ S, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p h => (hp p h).1.ne_zero
  have hval := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 (hp r hrS).1.ne_zero)
    (mul_ne_zero hc.pos.ne' hSprod)).mpr hsq_dvd r
  rw [(hp r hrS).1.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_mul hc.pos.ne' hSprod, Finsupp.add_apply,
    factorization_prime_prod (fun p h => (hp p h).1), if_pos hrS,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (hp r hrS).2 (dvd_mul_of_dvd_right h _)),
    zero_add] at hval
  omega

/-- Exact reformulation: total shift branching equals the number of simple primes `r in S`
that occur as a non-maximal `S`-divisor of `1 + p` for some `p in S` (each with `2 * r^2 < 1 + p`). -/
theorem branching_sum_eq_nonmax_children_card {a c : ℕ} {S : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p)) :
    (∑ p ∈ S, ((S.filter (fun r => r ∣ 1 + p)).card - 1)) =
      (S.filter (fun r => ∃ p ∈ S, ∃ r' ∈ S, r < r' ∧ r * r' ∣ 1 + p)).card := by
  classical
  let C (p : ℕ) := S.filter (fun r => r ∣ 1 + p)
  let E (p : ℕ) := (C p).filter (fun r => ∃ r' ∈ C p, r < r')
  have hE_card (p : ℕ) : (E p).card = (C p).card - 1 := by
    by_cases hne : (C p).Nonempty
    · let m := (C p).max' hne
      have hm : m ∈ C p := Finset.max'_mem (C p) hne
      have hEq : E p = (C p).erase m := by
        ext r
        simp only [E, Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hrC, r', hr'C, hlt⟩
          have hle : r' ≤ m := Finset.le_max' (C p) r' hr'C
          exact ⟨by omega, hrC⟩
        · rintro ⟨hrne, hrC⟩
          have hle : r ≤ m := Finset.le_max' (C p) r hrC
          exact ⟨hrC, m, hm, by omega⟩
      rw [hEq, Finset.card_erase_of_mem hm]
    · have hempty : C p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [E, hempty]
  have hdisj : (S : Set ℕ).PairwiseDisjoint E := by
    intro p₁ hp₁ p₂ hp₂ hne
    refine Finset.disjoint_left.mpr fun r hr₁ hr₂ => ?_
    have hC₁ := (Finset.mem_filter.mp hr₁).1
    have hC₂ := (Finset.mem_filter.mp hr₂).1
    obtain ⟨hrS, hd₁⟩ := Finset.mem_filter.mp hC₁
    obtain ⟨_, hd₂⟩ := Finset.mem_filter.mp hC₂
    exact hne (unique_shift_parent ha hc hp hbal hrS hp₁ hp₂ hd₁ hd₂)
  have hunion : S.biUnion E =
      S.filter (fun r => ∃ p ∈ S, ∃ r' ∈ S, r < r' ∧ r * r' ∣ 1 + p) := by
    ext r
    simp only [Finset.mem_biUnion, Finset.mem_filter, E, C]
    constructor
    · rintro ⟨p, hpS, ⟨hrS, hrp⟩, r', ⟨hr'S, hr'p⟩, hlt⟩
      have hcop : r.Coprime r' :=
        ((Nat.coprime_primes (hp r hrS).1 (hp r' hr'S).1).mpr (by omega))
      exact ⟨hrS, p, hpS, r', hr'S, hlt, hcop.mul_dvd_of_dvd_of_dvd hrp hr'p⟩
    · rintro ⟨hrS, p, hpS, r', hr'S, hlt, hmul⟩
      exact ⟨p, hpS, ⟨hrS, (dvd_mul_right r r').trans hmul⟩,
        r', ⟨hr'S, (dvd_mul_left r' r).trans hmul⟩, hlt⟩
  rw [← hunion, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl fun p _ => (hE_card p).symm

/-- If a prime `p in S` has at least two distinct `S`-divisors of `1 + p`, then
`2 <= cardFactors (ordCompl[2] (1 + p))`; equality holds if and only if `ordCompl[2] (1 + p)`
is the product of two distinct primes in `S`, in which case `(S.filter (· | 1 + p)).card = 2`. -/
theorem binary_branching_iff {p : ℕ} {S : Finset ℕ}
    (hp : ∀ q ∈ S, q.Prime ∧ q ≠ 2)
    (hge2 : 2 ≤ (S.filter (fun r => r ∣ 1 + p)).card)
    (hlt3 : cardFactors (ordCompl[2] (1 + p)) < 3) :
    (S.filter (fun r => r ∣ 1 + p)).card = 2 ∧
      ∃ r ∈ S, ∃ r' ∈ S, r < r' ∧ ordCompl[2] (1 + p) = r * r' := by
  let C := S.filter (fun r => r ∣ 1 + p)
  have h1lt : 1 < C.card := by change 2 ≤ C.card at hge2; omega
  obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := Finset.one_lt_card.mp h1lt
  obtain ⟨r, r', hrC, hr'C, hlt⟩ : ∃ r r', r ∈ C ∧ r' ∈ C ∧ r < r' := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨r₁, r₂, hr₁, hr₂, h⟩
    · exact ⟨r₂, r₁, hr₂, hr₁, h⟩
  obtain ⟨hrS, hrdvd⟩ := Finset.mem_filter.mp hrC
  obtain ⟨hr'S, hr'dvd⟩ := Finset.mem_filter.mp hr'C
  have hrp := (hp r hrS).1
  have hr'p := (hp r' hr'S).1
  have hr2 : ¬ 2 ∣ r := fun h => (hp r hrS).2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hrp).mp h).symm
  have hr'2 : ¬ 2 ∣ r' := fun h => (hp r' hr'S).2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr'p).mp h).symm
  have hro : r ∣ ordCompl[2] (1 + p) := Nat.dvd_ordCompl_of_dvd_not_dvd hrdvd hr2
  have hr'o : r' ∣ ordCompl[2] (1 + p) := Nat.dvd_ordCompl_of_dvd_not_dvd hr'dvd hr'2
  have hcop : r.Coprime r' := (Nat.coprime_primes hrp hr'p).mpr (by omega)
  have hmul : r * r' ∣ ordCompl[2] (1 + p) := hcop.mul_dvd_of_dvd_of_dvd hro hr'o
  obtain ⟨k, hk⟩ := hmul
  have hd_pos : 0 < ordCompl[2] (1 + p) := Nat.ordCompl_pos 2 (by omega)
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hk
    omega
  have hcf : cardFactors (ordCompl[2] (1 + p)) = 2 + cardFactors k := by
    rw [hk, cardFactors_mul (mul_ne_zero hrp.ne_zero hr'p.ne_zero) hk0,
      cardFactors_mul hrp.ne_zero hr'p.ne_zero,
      cardFactors_apply_prime hrp, cardFactors_apply_prime hr'p]
  have hcfk : cardFactors k = 0 := by omega
  have hk1 : k = 1 := by
    rcases (@cardFactors_eq_zero_iff_eq_zero_or_one k).mp hcfk with h0 | h1
    · exact absurd h0 hk0
    · exact h1
  rw [hk1, mul_one] at hk
  have hCeq : C = {r, r'} := by
    ext q
    simp only [C, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hqS, hqdvd⟩
      have hqp := (hp q hqS).1
      have hq2 : ¬ 2 ∣ q := fun h =>
        (hp q hqS).2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp).mp h).symm
      have hqo : q ∣ r * r' := hk ▸ Nat.dvd_ordCompl_of_dvd_not_dvd hqdvd hq2
      rcases hqp.dvd_mul.mp hqo with hqr | hqr'
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hqp hrp).mp hqr)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hqp hr'p).mp hqr')
    · rintro (rfl | rfl)
      · exact ⟨hrS, hrdvd⟩
      · exact ⟨hr'S, hr'dvd⟩
  refine ⟨?_, r, hrS, r', hr'S, hlt, hk⟩
  change C.card = 2
  rw [hCeq, Finset.card_pair (by omega)]

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1.H2 := by
  classical
  intro h1 h2 c hc hpow
  obtain ⟨K1, hK1⟩ := h1 c hc hpow
  obtain ⟨K2, hK2⟩ := h2 c hc hpow
  refine ⟨K1 + K2, ?_⟩
  intro a S b u ha hS hsub hp hbal
  have hp2 : ∀ p ∈ S, p.Prime ∧ p ≠ 2 := fun p h =>
    ⟨(hp p h).1, fun h2 => (hp p h).2 (h2 ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) c)⟩
  let High := S.filter (fun p => 3 ≤ cardFactors (ordCompl[2] (1 + p)))
  let Low := S.filter (fun p => ¬ 3 ≤ cardFactors (ordCompl[2] (1 + p)))
  let Bin := S.filter (fun p => ∃ r ∈ S, ∃ r' ∈ S, r < r' ∧ ordCompl[2] (1 + p) = r * r')
  have hsplit : (∑ p ∈ S, ((S.filter (fun r => r ∣ 1 + p)).card - 1)) =
      (∑ p ∈ High, ((S.filter (fun r => r ∣ 1 + p)).card - 1)) +
      (∑ p ∈ Low, ((S.filter (fun r => r ∣ 1 + p)).card - 1)) := by
    exact (Finset.sum_filter_add_sum_filter_not S
      (fun p => 3 ≤ cardFactors (ordCompl[2] (1 + p))) _).symm
  have hLow_le : (∑ p ∈ Low, ((S.filter (fun r => r ∣ 1 + p)).card - 1)) ≤ Bin.card := by
    calc (∑ p ∈ Low, ((S.filter (fun r => r ∣ 1 + p)).card - 1))
        ≤ ∑ p ∈ Low, (if p ∈ Bin then 1 else 0) := by
          apply Finset.sum_le_sum
          intro p hpLow
          have hpS := (Finset.mem_filter.mp hpLow).1
          have hlt3 : cardFactors (ordCompl[2] (1 + p)) < 3 := by
            have := (Finset.mem_filter.mp hpLow).2
            omega
          by_cases hge2 : 2 ≤ (S.filter (fun r => r ∣ 1 + p)).card
          · obtain ⟨heq2, hex⟩ := binary_branching_iff hp2 hge2 hlt3
            have hpBin : p ∈ Bin := Finset.mem_filter.mpr ⟨hpS, hex⟩
            rw [if_pos hpBin, heq2]
          · split_ifs <;> omega
      _ = (Low.filter (fun p => p ∈ Bin)).card := by rw [← Finset.card_filter]
      _ ≤ Bin.card := Finset.card_le_card (fun p h => (Finset.mem_filter.mp h).2)
  have hBin_le : Bin.card ≤ K1 := hK1 a S ha hS hsub hp hbal
  have hHigh_le : (∑ p ∈ High, ((S.filter (fun r => r ∣ 1 + p)).card - 1)) ≤ K2 :=
    hK2 a S ha hS hsub hp hbal
  omega

end OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H1_R1_H2_R1
