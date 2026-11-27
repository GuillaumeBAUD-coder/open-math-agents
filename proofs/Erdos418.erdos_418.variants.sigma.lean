import FormalConjectures.ErdosProblems.«418»
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.PSeries

/-! Finite sieve estimates followed by the count of aliquot values. -/

open Filter Finset
open scoped BigOperators Topology

namespace OMA.Nonaliquot

private theorem totientReal (n : ℕ) :
    (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  exact h

-- A finite set of primes outside any prescribed set can have arbitrarily small
-- product of the factors 1 - 1/p, by divergence of the prime reciprocal sum.
private theorem smallTotient (excluded : Finset ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ q : ℕ, 0 < q ∧ (∀ p ∈ q.primeFactors, p ∉ excluded) ∧
      (q.totient : ℝ) < c * q := by
  classical
  let primeRecip (p : ℕ) : ℝ := if p.Prime then (p : ℝ)⁻¹ else 0
  let remaining (p : ℕ) : ℝ := if p.Prime ∧ p ∉ excluded then (p : ℝ)⁻¹ else 0
  let discarded (p : ℕ) : ℝ := if p ∈ excluded then primeRecip p else 0
  have hdiscard : Summable discarded :=
    summable_of_ne_finset_zero (s := excluded) fun p hp => by simp [discarded, hp]
  have hnot : ¬ Summable remaining := by
    intro h
    apply not_summable_one_div_on_primes
    convert h.add hdiscard using 1
    funext p
    by_cases hpr : p.Prime <;> by_cases hp : p ∈ excluded <;>
      simp [remaining, discarded, primeRecip, Set.indicator, hpr, hp, one_div]
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, -Real.log c < ∑ p ∈ s, remaining p := by
    by_contra! h
    exact hnot (summable_of_sum_le (fun p => by
      dsimp [remaining]
      split <;> positivity) h)
  let primes := s.filter fun p => p.Prime ∧ p ∉ excluded
  have hprime (p : ℕ) (hp : p ∈ primes) : p.Prime := (mem_filter.mp hp).2.1
  have hsum : -Real.log c < ∑ p ∈ primes, (p : ℝ)⁻¹ := by
    simpa only [primes, sum_filter, remaining] using hs
  let q := ∏ p ∈ primes, p
  have hq : 0 < q := prod_pos (fun p hp => (hprime p hp).pos)
  have hqf : q.primeFactors = primes := Nat.primeFactors_prod hprime
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hqf]
    exact fun p hp => (mem_filter.mp hp).2.2
  · have bound : ∏ p ∈ primes, (1 - (p : ℝ)⁻¹) < c := by
      calc
        _ ≤ ∏ p ∈ primes, Real.exp (-(p : ℝ)⁻¹) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_lt.le
            exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp')
          · intro p hp
            simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(p : ℝ)⁻¹)
        _ = Real.exp (-(∑ p ∈ primes, (p : ℝ)⁻¹)) := by
          rw [← Real.exp_sum, Finset.sum_neg_distrib]
        _ < c := by
          rw [← Real.exp_log hc]
          exact Real.exp_lt_exp.mpr (by linarith)
    rw [totientReal, hqf, mul_comm c]
    exact mul_lt_mul_of_pos_left bound (by exact_mod_cast hq)

private def coprimeUpTo (q x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n => q.Coprime n

private theorem cardCoprimeUpTo {q : ℕ} (hq : 0 < q) (x : ℕ) :
    (coprimeUpTo q x).card ≤ (x / q + 1) * q.totient := by
  let residues := (range q).filter fun r => q.Coprime r
  have hres : residues.card = q.totient := (Nat.totient_eq_card_coprime q).symm
  rw [← hres, ← card_range (x / q + 1), ← card_product]
  apply card_le_card_of_injOn (fun n => (n / q, n % q))
  · intro n hn
    have hn' := mem_filter.mp (show n ∈ coprimeUpTo q x from hn)
    have hx : n ≤ x := (mem_Icc.mp hn'.1).2
    have hr : q.Coprime (n % q) := by
      change q.gcd (n % q) = 1
      rw [Nat.gcd_comm q (n % q), ← Nat.gcd_rec q n]
      exact hn'.2
    exact mem_product.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hx)),
       mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hq), hr⟩⟩
  · intro a ha b hb e
    have e₁ := congrArg Prod.fst e
    have e₂ := congrArg Prod.snd e
    change a / q = b / q at e₁
    change a % q = b % q at e₂
    simpa only [Nat.mod_add_div] using congrArg₂ (fun d r => r + q * d) e₁ e₂

private theorem eventuallyCoprime {q : ℕ} (hq : 0 < q) {c : ℝ} (hc : 0 < c)
    (ht : (q.totient : ℝ) ≤ (c / 2) * q) :
    ∀ᶠ x : ℕ in atTop, ((coprimeUpTo q x).card : ℝ) ≤ c * x := by
  filter_upwards [eventually_ge_atTop q] with x hx
  have hbound : (x / q + 1) * q ≤ 2 * x := by
    rw [add_mul, one_mul, two_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self x q) hx
  calc
    _ ≤ ((x / q + 1 : ℕ) : ℝ) * (q.totient : ℝ) := by
      exact_mod_cast cardCoprimeUpTo hq x
    _ ≤ ((x / q + 1 : ℕ) : ℝ) * ((c / 2) * q) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (c / 2) * (((x / q + 1 : ℕ) : ℝ) * q) := by ring
    _ ≤ (c / 2) * (2 * x) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hbound) (by positivity)
    _ = c * x := by ring

private def fewPrimeFactors (k : ℕ) (excluded : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n => (n.primeFactors \ excluded).card ≤ k

private theorem commonPrime {q n : ℕ} (hq : q ≠ 0) (hn : n ≠ 0) (h : ¬ q.Coprime n) :
    ∃ p ∈ q.primeFactors, p ∈ n.primeFactors := by
  obtain ⟨p, hp, hpq, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, hq⟩, Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩⟩

-- In each induction step the coprime numbers are sparse. The remaining numbers
-- use at least one prime of q, which can be added to the excluded set.
private theorem eventuallyFewPrimeFactors (k : ℕ) (excluded : Finset ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ((fewPrimeFactors k excluded x).card : ℝ) ≤ c * x := by
  induction k generalizing excluded c with
  | zero =>
    obtain ⟨q, hq, hdis, ht⟩ := smallTotient excluded (half_pos hc)
    filter_upwards [eventuallyCoprime hq hc ht.le] with x hx
    apply le_trans _ hx
    apply Nat.cast_le.mpr
    apply card_le_card
    intro n hn
    have hn' := mem_filter.mp (show n ∈ fewPrimeFactors 0 excluded x from hn)
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn'.1).1; omega
    refine mem_filter.mpr ⟨hn'.1, ?_⟩
    by_contra hcop
    obtain ⟨p, hpq, hpn⟩ := commonPrime hq.ne' hn0 hcop
    have hp : p ∈ n.primeFactors \ excluded := mem_sdiff.mpr ⟨hpn, hdis p hpq⟩
    have := card_pos.mpr ⟨p, hp⟩
    omega
  | succ k ih =>
    obtain ⟨q, hq, hdis, ht⟩ := smallTotient excluded (half_pos (half_pos hc))
    filter_upwards [eventuallyCoprime hq (half_pos hc) ht.le,
      ih (excluded ∪ q.primeFactors) (half_pos hc)] with x hcop hfew
    have hsubset : fewPrimeFactors (k + 1) excluded x ⊆
        coprimeUpTo q x ∪ fewPrimeFactors k (excluded ∪ q.primeFactors) x := by
      intro n hn
      have hn' := mem_filter.mp (show n ∈ fewPrimeFactors (k + 1) excluded x from hn)
      by_cases h : q.Coprime n
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hn'.1, h⟩))
      · have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn'.1).1; omega
        obtain ⟨p, hpq, hpn⟩ := commonPrime hq.ne' hn0 h
        have hlt : (n.primeFactors \ (excluded ∪ q.primeFactors)).card <
            (n.primeFactors \ excluded).card := by
          apply card_lt_card
          apply ssubset_iff_subset_ne.mpr
          refine ⟨?_, ?_⟩
          · intro a ha
            rcases mem_sdiff.mp ha with ⟨ha₁, ha₂⟩
            exact mem_sdiff.mpr ⟨ha₁, fun ha₃ => ha₂ (mem_union_left _ ha₃)⟩
          · intro heq
            have hp : p ∈ n.primeFactors \ (excluded ∪ q.primeFactors) :=
              heq.symm ▸ mem_sdiff.mpr ⟨hpn, hdis p hpq⟩
            exact (mem_sdiff.mp hp).2 (mem_union_right _ hpq)
        exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hn'.1, by omega⟩))
    have hcard := (card_le_card hsubset).trans (card_union_le _ _)
    calc
      _ ≤ ((coprimeUpTo q x).card : ℝ) +
          ((fewPrimeFactors k (excluded ∪ q.primeFactors) x).card : ℝ) := by
        exact_mod_cast hcard
      _ ≤ (c / 2) * x + (c / 2) * x := add_le_add hcop hfew
      _ = c * x := by ring

private theorem cardMultiples {d : ℕ} (hd : 0 < d) (x : ℕ) :
    ((Icc 1 x).filter fun n => d ∣ n).card ≤ x / d := by
  have hquot : (Icc 1 (x / d)).card = x / d := by simp [Nat.card_Icc]
  rw [← hquot]
  apply card_le_card_of_injOn (fun n => n / d)
  · intro n hn
    obtain ⟨hnI, hnD⟩ := mem_filter.mp (show n ∈ (Icc 1 x).filter (fun j => d ∣ j) from hn)
    have hnP : 0 < n := (mem_Icc.mp hnI).1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hnP hnD) hd,
      Nat.div_le_div_right (mem_Icc.mp hnI).2⟩
  · intro a ha b hb h
    have haD := (mem_filter.mp (show a ∈ (Icc 1 x).filter (fun j => d ∣ j) from ha)).2
    have hbD := (mem_filter.mp (show b ∈ (Icc 1 x).filter (fun j => d ∣ j) from hb)).2
    simpa only [Nat.div_mul_cancel haD, Nat.div_mul_cancel hbD] using congrArg (· * d) h

open scoped ArithmeticFunction.sigma

private def squareMultiple (P x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n => ∃ p ∈ Icc P x, p ^ 2 ∣ n

-- A tail of the convergent p-series bounds the frequency of large square divisors.
private theorem largeSquareDivisors {c : ℝ} (hc : 0 < c) :
    ∃ P : ℕ, 3 ≤ P ∧ ∀ x : ℕ, ((squareMultiple P x).card : ℝ) ≤ c * x := by
  classical
  let f : ℕ → ℝ := fun p => 1 / (p : ℝ) ^ 2
  have hf : Summable f := Real.summable_one_div_nat_pow.mpr (by decide)
  have htail : Tendsto (fun P : ℕ => ∑' i : ℕ, f (i + P)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ∑' i, f i)).sub hf.hasSum.tendsto_sum_nat
    rw [sub_self] at h
    refine h.congr fun P => ?_
    linarith [hf.sum_add_tsum_nat_add P]
  obtain ⟨P, hP, hsmall⟩ := ((eventually_ge_atTop 3).and (htail.eventually_lt_const hc)).exists
  refine ⟨P, hP, fun x => ?_⟩
  let T := fun i : ℕ => (Icc 1 x).filter fun n => (i + P) ^ 2 ∣ n
  have hincl : squareMultiple P x ⊆ (range (x + 1)).biUnion T := by
    intro n hn
    obtain ⟨hn, p, hp, hd⟩ := mem_filter.mp hn
    obtain ⟨hp₁, hp₂⟩ := mem_Icc.mp hp
    refine mem_biUnion.mpr ⟨p - P, mem_range.mpr (by omega), mem_filter.mpr ⟨hn, ?_⟩⟩
    simpa only [Nat.sub_add_cancel hp₁] using hd
  have hcard : (squareMultiple P x).card ≤ ∑ i ∈ range (x + 1), (T i).card :=
    (card_le_card hincl).trans card_biUnion_le
  have hterm (i : ℕ) : ((T i).card : ℝ) ≤ (x : ℝ) * f (i + P) := by
    have hm : 0 < (i + P) ^ 2 := by positivity
    have hd : ((T i).card : ℝ) ≤ ((x / ((i + P) ^ 2) : ℕ) : ℝ) := by
      exact_mod_cast cardMultiples hm x
    refine hd.trans ?_
    dsimp [f]
    rw [mul_one_div]
    apply (le_div_iff₀ (by positivity)).mpr
    exact_mod_cast Nat.div_mul_le_self x ((i + P) ^ 2)
  calc
    _ ≤ ∑ i ∈ range (x + 1), ((T i).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ i ∈ range (x + 1), (x : ℝ) * f (i + P) := sum_le_sum fun i _ => hterm i
    _ = (x : ℝ) * (∑ i ∈ range (x + 1), f (i + P)) := by rw [mul_sum]
    _ ≤ (x : ℝ) * (∑' i : ℕ, f (i + P)) := by
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (summable_nat_add_iff P).2 hf |>.sum_le_tsum _ (fun _ _ => by positivity)
    _ ≤ c * x := by rw [mul_comm c]; gcongr

private theorem sigmaDvdOfMany {P n : ℕ} (hP : 3 ≤ P) (hn : n ≠ 0)
    (hmany : 4 ≤ (n.primeFactors \ range P).card)
    (hnsq : ∀ p ∈ n.primeFactors \ range P, ¬ p ^ 2 ∣ n) : 16 ∣ σ 1 n := by
  let s := n.primeFactors \ range P
  rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn]
  have hfactor (p : ℕ) (hp : p ∈ s) : 2 ∣ σ 1 (p ^ n.factorization p) := by
    have hp' := (mem_sdiff.mp hp).1
    have hprime := Nat.prime_of_mem_primeFactors hp'
    have hpd := Nat.dvd_of_mem_primeFactors hp'
    have h₁ := (hprime.dvd_iff_one_le_factorization hn).mp hpd
    have h₂ : ¬ 2 ≤ n.factorization p :=
      fun hh => hnsq p hp ((hprime.pow_dvd_iff_le_factorization hn).mpr hh)
    have he : n.factorization p = 1 := by omega
    have hge := Nat.le_of_not_gt (fun hlt => (mem_sdiff.mp hp).2 (mem_range.mpr hlt))
    have hodd := hprime.odd_of_ne_two (by omega : p ≠ 2)
    rw [he, ArithmeticFunction.sigma_one_apply_prime_pow hprime]
    norm_num [sum_range_succ]
    exact even_iff_two_dvd.mp ((show Odd 1 by decide).add_odd hodd)
  have hd : 2 ^ s.card ∣ ∏ p ∈ s, σ 1 (p ^ n.factorization p) := by
    rw [← prod_const]
    exact prod_dvd_prod_of_dvd _ _ hfactor
  exact (Nat.pow_dvd_pow 2 hmany).trans (hd.trans
    (prod_dvd_prod_of_subset _ _ _ sdiff_subset))

private def badSigma (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n => ¬ 16 ∣ σ 1 n

private theorem eventuallyBadSigma {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ((badSigma x).card : ℝ) ≤ c * x := by
  obtain ⟨P, hP, hsq⟩ := largeSquareDivisors (half_pos hc)
  filter_upwards [eventuallyFewPrimeFactors 3 (range P) (half_pos hc)] with x hfew
  have hsub : badSigma x ⊆ fewPrimeFactors 3 (range P) x ∪ squareMultiple P x := by
    intro n hn
    obtain ⟨hnI, hnS⟩ := mem_filter.mp hn
    have hn0 : 0 < n := (mem_Icc.mp hnI).1
    by_cases hm : (n.primeFactors \ range P).card ≤ 3
    · exact mem_union_left _ (mem_filter.mpr ⟨hnI, hm⟩)
    by_cases hs : n ∈ squareMultiple P x
    · exact mem_union_right _ hs
    exfalso
    apply hnS (sigmaDvdOfMany hP hn0.ne' (by omega) ?_)
    intro p hp hd
    apply hs (mem_filter.mpr ⟨hnI, p, ?_, hd⟩)
    refine mem_Icc.mpr ⟨Nat.le_of_not_gt (fun h => (mem_sdiff.mp hp).2 (mem_range.mpr h)), ?_⟩
    exact (Nat.le_of_dvd hn0 (Nat.dvd_of_mem_primeFactors (mem_sdiff.mp hp).1)).trans (mem_Icc.mp hnI).2
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  calc
    _ ≤ ((fewPrimeFactors 3 (range P) x).card : ℝ) + (squareMultiple P x).card := by exact_mod_cast hcard
    _ ≤ (c / 2) * x + (c / 2) * x := add_le_add hfew (hsq x)
    _ = c * x := by ring

private def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

private theorem sigmaEq (n : ℕ) : σ 1 n = aliquot n + n := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  rfl

private theorem scaleAliquot (k t : ℕ) (ht : 0 < t) : t * aliquot k ≤ aliquot (k * t) := by
  let f : ℕ → ℕ := fun d => d * t
  have hf : Function.Injective f := fun a b h => Nat.eq_of_mul_eq_mul_right ht h
  have hs : k.properDivisors.image f ⊆ (k * t).properDivisors := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hd
    obtain ⟨had, hal⟩ := Nat.mem_properDivisors.mp ha
    exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_right had t, Nat.mul_lt_mul_of_pos_right hal ht⟩
  calc
    _ = ∑ d ∈ k.properDivisors.image f, d := by
      rw [sum_image (fun a _ b _ h => hf h), aliquot, mul_sum]
      exact sum_congr rfl fun i _ => Nat.mul_comm t i
    _ ≤ aliquot (k * t) := sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)

private theorem factorizationEvenOfOddSigma {n : ℕ} (hn : Odd n) (hs : Odd (σ 1 n))
    (p : ℕ) (hp : p ∈ n.primeFactors) : Even (n.factorization p) := by
  have hn0 : n ≠ 0 := by rintro rfl; norm_num at hn
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := fun e => hn.not_two_dvd_nat (e ▸ Nat.dvd_of_mem_primeFactors hp)
  have hodd := hpr.odd_of_ne_two hp2
  let e := n.factorization p
  let f := fun q => σ 1 (q ^ n.factorization q)
  have hf : f p ∣ σ 1 n := by
    rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn0]
    exact dvd_prod_of_mem f hp
  have hos : Odd (f p) := Nat.not_even_iff_odd.mp fun he => hs.not_two_dvd_nat (he.two_dvd.trans hf)
  change Odd (σ 1 (p ^ e)) at hos
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hpr, odd_sum_iff_odd_card_odd] at hos
  have hall : (range (e + 1)).filter (fun i => Odd (p ^ i)) = range (e + 1) :=
    filter_true_of_mem fun i _ => hodd.pow
  rw [hall, card_range] at hos
  have hm := Nat.odd_iff.mp hos
  change Even e
  rw [Nat.even_iff]
  omega

private theorem oddPreimageSquare {n : ℕ} (hn : Odd n) (hs : 2 ∣ aliquot n) :
    ∃ r : ℕ, n = r ^ 2 := by
  have hsigma : Odd (σ 1 n) := by
    rw [sigmaEq]
    exact (even_iff_two_dvd.mpr hs).add_odd hn
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← prod_pow]
  have hn0 : n ≠ 0 := by rintro rfl; norm_num at hn
  calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := Nat.prod_primeFactors_pow_factorization hn0
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      have hp' := Nat.even_iff.mp (factorizationEvenOfOddSigma hn hsigma p hp)
      omega

private theorem primeSquareAliquot {p : ℕ} (hp : p.Prime) : aliquot (p ^ 2) = p + 1 := by
  have hs := sigmaEq (p ^ 2)
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp] at hs
  simp [sum_range_succ] at hs
  omega

private theorem compositeSquareAliquot {k r : ℕ} (hk : 2 ≤ k) (hr : k * k ≤ r)
    (hnp : ¬ r.Prime) : k * r ≤ aliquot (r ^ 2) := by
  have hr₂ : 2 ≤ r := (hk.trans (Nat.le_mul_of_pos_right _ (by omega))).trans hr
  obtain ⟨a, had, ha₂, hal⟩ := Nat.exists_dvd_of_not_prime2 hr₂ hnp
  obtain ⟨b, hb⟩ := had
  have hb₂ : 2 ≤ b := by
    by_contra! hh
    interval_cases b <;> simp_all
  let d := max a b
  have hd : d ∣ r := by
    rcases le_total a b with h | h
    · rw [show d = b from max_eq_right h, hb, mul_comm]
      exact dvd_mul_right _ _
    · rw [show d = a from max_eq_left h, hb]
      exact dvd_mul_right _ _
  have hdr : d < r := by
    apply max_lt hal
    rw [hb, mul_comm]
    exact lt_mul_of_one_lt_right (by omega) (by omega)
  have hkd : k ≤ d := by
    by_contra! hh
    have hab : a * b < k * k := Nat.mul_lt_mul_of_lt_of_lt (lt_of_le_of_lt (le_max_left ..) hh)
      (lt_of_le_of_lt (le_max_right ..) hh)
    omega
  have hmem : d * r ∈ (r ^ 2).properDivisors := by
    rw [pow_two]
    exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_right hd r,
      Nat.mul_lt_mul_of_pos_right hdr (by omega)⟩
  exact (Nat.mul_le_mul_right r hkd).trans (single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hmem)

private theorem cardNotThree (x : ℕ) :
    ((Icc 1 x).filter fun n => ¬ 3 ∣ n).card ≤ 2 * (x / 3 + 1) := by
  let residues : Finset ℕ := {1, 2}
  have hcard : ((range (x / 3 + 1)) ×ˢ residues).card = 2 * (x / 3 + 1) := by
    simp [residues, mul_comm]
  rw [← hcard]
  apply card_le_card_of_injOn (fun n => (n / 3, n % 3))
  · intro n hn
    obtain ⟨hi, hd⟩ := mem_filter.mp hn
    refine mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp hi).2)), ?_⟩
    have hm := Nat.mod_lt n (by decide : 0 < 3)
    have hz := Nat.dvd_iff_mod_eq_zero.not.mp hd
    simp only [residues, mem_insert, mem_singleton]
    omega
  · intro a _ b _ h
    simpa only [Nat.mod_add_div] using congrArg (fun z : ℕ × ℕ => z.2 + 3 * z.1) h

private theorem castDivLe (x : ℕ) {k : ℕ} (hk : 0 < k) : ((x / k : ℕ) : ℝ) ≤ (x : ℝ) / k := by
  rw [le_div_iff₀ (by exact_mod_cast hk)]
  exact_mod_cast Nat.div_mul_le_self x k

open scoped Classical in
private def multiples (x : ℕ) : Finset ℕ := (Icc 1 (x / 16)).image fun t => 16 * t

open scoped Classical in
private noncomputable def untouchableMultiples (x : ℕ) : Finset ℕ := (multiples x).filter Nat.IsUntouchable

-- Count the occupied multiples of sixteen by sorting their possible preimages.
-- The even preimages with sixteen dividing their divisor sums contribute at most
-- two residue classes of quotients by sixteen and one class of quotients by forty-eight.
set_option maxHeartbeats 1200000 in
private theorem manyUntouchable : ∀ᶠ x : ℕ in atTop,
    (x : ℝ) / 500 ≤ ((untouchableMultiples x).card : ℝ) := by
  classical
  have hscale : Tendsto (fun x : ℕ => 2 * x) atTop atTop :=
    tendsto_atTop_mono (fun x => by dsimp [id]; omega) tendsto_id
  filter_upwards [hscale.eventually (eventuallyBadSigma (c := 1 / 4000) (by norm_num)),
    eventuallyFewPrimeFactors 1 ∅ (c := 1 / 4000) (by norm_num),
    eventually_ge_atTop (1000000000 : ℕ)] with x hb hd hx
  let A := ((Icc 1 (x / 15)).filter fun t => ¬ 3 ∣ t).image fun t => aliquot (16 * t)
  let C := (Icc 1 (x / 76)).image fun t => aliquot (48 * t)
  let B := (badSigma (2 * x)).image aliquot
  let D := (fewPrimeFactors 1 ∅ x).image fun r => r + 1
  let E := (Icc 1 (x / 1000)).image fun r => aliquot (r ^ 2)
  have hsub : multiples x ⊆ untouchableMultiples x ∪ (A ∪ (C ∪ (B ∪ (D ∪ E)))) := by
    intro m hm
    by_cases hU : m.IsUntouchable
    · exact mem_union_left _ (mem_filter.mpr ⟨hm, hU⟩)
    apply mem_union_right
    obtain ⟨t, ht, hmt⟩ := mem_image.mp hm
    have hm0 : 0 < m := by
      have := (mem_Icc.mp ht).1
      omega
    have hmX : m ≤ x := by
      have := Nat.mul_le_mul_left 16 (mem_Icc.mp ht).2
      have := Nat.div_mul_le_self x 16
      omega
    have hmD : 16 ∣ m := ⟨t, hmt.symm⟩
    have hpre : ∃ n : ℕ, aliquot n = m := by
      simpa only [Nat.IsUntouchable, not_not, aliquot] using hU
    obtain ⟨n, hn⟩ := hpre
    have hn0 : 0 < n := by
      by_contra! h0
      have hnz : n = 0 := by omega
      subst n
      simp [aliquot] at hn
      omega
    by_cases hne : Even n
    · have hnX : n ≤ 2 * x := by
        obtain ⟨u, hu⟩ := hne.two_dvd
        have h := scaleAliquot 2 u (by omega)
        rw [← hu, show aliquot 2 = 1 by decide, mul_one, hn] at h
        omega
      by_cases hs : 16 ∣ σ 1 n
      · rw [sigmaEq, hn] at hs
        obtain ⟨u, hu⟩ : 16 ∣ n := by simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub hs hmD
        have hu0 : 0 < u := by omega
        by_cases h3 : 3 ∣ u
        · obtain ⟨v, hv⟩ := h3
          have hn48 : n = 48 * v := by omega
          have hh := scaleAliquot 48 v (by omega)
          rw [← hn48, show aliquot 48 = 76 by decide, hn] at hh
          exact mem_union_right _ (mem_union_left _ (mem_image.mpr ⟨v, mem_Icc.mpr ⟨by omega, by omega⟩,
            by simpa only [← hn48] using hn⟩))
        · have hh := scaleAliquot 16 u hu0
          rw [← hu, show aliquot 16 = 15 by decide, hn] at hh
          exact mem_union_left _ (mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_Icc.mpr ⟨hu0, by omega⟩, h3⟩,
            by simpa only [← hu] using hn⟩)
      · exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_image.mpr
          ⟨n, mem_filter.mpr ⟨mem_Icc.mpr ⟨hn0, hnX⟩, hs⟩, hn⟩)))
    · obtain ⟨r, hr⟩ := oddPreimageSquare (Nat.not_even_iff_odd.mp hne)
        (hn ▸ (show 2 ∣ 16 by decide).trans hmD)
      have hr0 : 0 < r := by by_contra! h; simp [show r = 0 by omega] at hr; omega
      rw [hr] at hn
      by_cases hpr : r.Prime
      · have hvalue := primeSquareAliquot hpr
        have hrX : r ≤ x := by omega
        have hcard : r.primeFactors.card ≤ 1 := by simp [hpr.primeFactors]
        exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_image.mpr
          ⟨r, mem_filter.mpr ⟨mem_Icc.mpr ⟨hr0, hrX⟩, by simpa using hcard⟩, hvalue.symm.trans hn⟩))))
      · have hrX : r ≤ x / 1000 := by
          by_cases he : 1000 * 1000 ≤ r
          · have hh := compositeSquareAliquot (by decide : 2 ≤ 1000) he hpr
            omega
          · omega
        exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_image.mpr
          ⟨r, mem_Icc.mpr ⟨hr0, hrX⟩, hn⟩))))
  have hM : (multiples x).card = x / 16 := by
    rw [multiples, card_image_of_injective _ (fun a b h => by omega)]
    simp [Nat.card_Icc]
  have hc : x / 16 ≤ (untouchableMultiples x).card + (A.card + (C.card + (B.card + (D.card + E.card)))) := by
    rw [← hM]
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left
      ((card_union_le _ _).trans (Nat.add_le_add_left
        ((card_union_le _ _).trans (Nat.add_le_add_left
          ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _)) _)) _)) _))
  have hfloor : (x : ℝ) / 16 - 1 ≤ ((x / 16 : ℕ) : ℝ) := by
    have hm : x ≤ 16 * (x / 16 + 1) := by omega
    have hh : (x : ℝ) ≤ 16 * ((x / 16 : ℕ) + (1 : ℝ)) := by exact_mod_cast hm
    linarith
  have hA : (A.card : ℝ) ≤ (2 / 45 : ℝ) * x + 2 := by
    have hl : A.card ≤ 2 * (x / 15 / 3 + 1) := card_image_le.trans (cardNotThree _)
    have hdiv := (castDivLe (x / 15) (by decide : 0 < 3)).trans
      (div_le_div_of_nonneg_right (castDivLe x (by decide : 0 < 15)) (by norm_num))
    have hcast : (A.card : ℝ) ≤ 2 * (((x / 15 / 3 : ℕ) : ℝ) + 1) := by exact_mod_cast hl
    linarith
  have hC : (C.card : ℝ) ≤ (1 / 76 : ℝ) * x := by
    have hl : C.card ≤ x / 76 := card_image_le.trans (by simp [Nat.card_Icc])
    calc
      _ ≤ ((x / 76 : ℕ) : ℝ) := by exact_mod_cast hl
      _ ≤ _ := by simpa [div_eq_mul_inv, mul_comm] using castDivLe x (by decide : 0 < 76)
  have hB : (B.card : ℝ) ≤ (1 / 2000 : ℝ) * x := by
    have h : (B.card : ℝ) ≤ (badSigma (2 * x)).card := by exact_mod_cast (card_image_le : B.card ≤ _)
    push_cast at hb
    linarith
  have hD : (D.card : ℝ) ≤ (1 / 4000 : ℝ) * x := by
    exact le_trans (by exact_mod_cast (card_image_le : D.card ≤ (fewPrimeFactors 1 ∅ x).card)) hd
  have hE : (E.card : ℝ) ≤ (1 / 1000 : ℝ) * x := by
    have hl : E.card ≤ x / 1000 := card_image_le.trans (by simp [Nat.card_Icc])
    calc
      _ ≤ ((x / 1000 : ℕ) : ℝ) := by exact_mod_cast hl
      _ ≤ _ := by simpa [div_eq_mul_inv, mul_comm] using castDivLe x (by decide : 0 < 1000)
  have hcount : ((x / 16 : ℕ) : ℝ) ≤ (untouchableMultiples x).card +
      ((A.card : ℝ) + ((C.card : ℝ) + ((B.card : ℝ) + ((D.card : ℝ) + (E.card : ℝ))))) := by
    exact_mod_cast hc
  have hx' : (1000000000 : ℝ) ≤ x := by exact_mod_cast hx
  linarith

private theorem countInIio (x : ℕ) : (untouchableMultiples x).card ≤
    ({n : ℕ | n.IsUntouchable} ∩ Set.Iio (x + 1)).ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (Set.finite_Iio _ |>.subset Set.inter_subset_right)
  intro m hm
  obtain ⟨hm, hU⟩ := mem_filter.mp hm
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hm
  have hh := Nat.mul_le_mul_left 16 (mem_Icc.mp ht).2
  have hdx := Nat.div_mul_le_self x 16
  exact ⟨hU, by change 16 * t < x + 1; omega⟩

end OMA.Nonaliquot

open OMA.Nonaliquot

theorem OMA.solution : type_of% @Erdos418.erdos_418.variants.sigma := by
  classical
  let S : Set ℕ := {n | n.IsUntouchable}
  change 0 < S.lowerDensity
  unfold Set.lowerDensity
  rw [Filter.liminf_eq]
  have hb : BddAbove {r : ℝ | ∀ᶠ n : ℕ in atTop, r ≤ S.partialDensity Set.univ n} := by
    refine ⟨1, fun r hr => ?_⟩
    obtain ⟨n, hn⟩ := (show ∀ᶠ n : ℕ in atTop, r ≤ S.partialDensity Set.univ n from hr).exists
    exact hn.trans (Set.partialDensity_le_one _ _ _)
  apply lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 1000)
  apply le_csSup hb
  obtain ⟨K, hK⟩ := eventually_atTop.mp manyUntouchable
  refine eventually_atTop.mpr ⟨max K 1 + 1, fun n hn => ?_⟩
  let x := n - 1
  have hnx : n = x + 1 := by dsimp [x]; omega
  have hx : x ≥ K := by dsimp [x]; omega
  have hx1 : 1 ≤ x := by dsimp [x]; omega
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hcard : (x : ℝ) / 500 ≤ ((S ∩ Set.Iio (x + 1)).ncard : ℝ) :=
    (hK x hx).trans (by exact_mod_cast countInIio x)
  have hden : (Set.Iio (x + 1)).ncard = x + 1 := by simp
  rw [hnx]
  change (1 : ℝ) / 1000 ≤ ((S ∩ Set.univ ∩ Set.Iio (x + 1)).ncard : ℝ) /
    ((Set.univ ∩ Set.Iio (x + 1)).ncard : ℝ)
  simp only [Set.inter_univ, Set.univ_inter, hden, Nat.cast_add, Nat.cast_one]
  rw [le_div_iff₀ (by positivity)]
  linarith
