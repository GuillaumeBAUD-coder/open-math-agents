import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R1

/-!
# Forced-prime closure and stripped residual equations for multi-prime cores

Reduction of `Erdos1052.erdos_1052.R2.H2.R1.H3` (finiteness of admissible 2-adic exponents
`a >= 5` for every odd powerful core `c` having at least two distinct prime factors).

Given a fixed odd powerful core `c` with `2 <= c.primeFactors.card`, let
`sigma = prod_{q | c} (1 + q^{v_q(c)})`. In any completion `(a, S)`, every odd prime dividing
`sigma` outside `c` is forced into `S`, and iterating this closure through shifts `1 + p`
produces a canonical finite subset `F subseteq S` depending only on `c`.

This reduction proves three unconditional elimination results for composite cores:
1. Closure divisibility obstruction: if `ordCompl[2] (sigma * prod_{p in F} (1 + p))` fails
   to divide `c * prod_{p in F} p` (capturing both repeated odd prime factors outside `c` and
   valuation overflows at primes of `c`), then no completion exists for any `a >= 5`.
2. Abundancy bounds: for every surviving core, cancelling `F` collapses the entire core factor
   `sigma` to a stripped residual ratio `2^k / d` with an odd divisor `d | c`, `1 < d`, and
   `d < 2^k < 2 * d` (uniquely determining `k` from `d`).
3. Generalized Graham elimination: whenever `2^k / d = prod_{q in A} (q + 1) / q` for some
   subset `A subseteq d.primeFactors` (including all Mersenne-prime residuals `d = 2^k - 1`,
   such as `c = 5^2 * 7^2 = 1225` and `c = 3^2 * 5^3 * 7^2 = 55125`), substituting
   `T = (S \ F) union A` reduces directly to `Graham1052.core`, forcing `a < 10`.

All remaining composite cores satisfy the stripped residual balance equation
`(2^a + 1) * prod_{p in T} (1 + p) = 2^(a + 1 - k) * d * prod_{p in T} p` with `sigma*(c)`
completely eliminated. We split these surviving residual equations by whether the stripped
denominator `d` is a single prime power (`H1`, e.g. `c = 3^2 * 5^3 -> d = 25, k = 5`) or still
has at least two distinct prime factors (`H2`, e.g. `c = 3^2 * 5^2 -> d = 45, k = 6`).
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R1_H3_R1

open scoped BigOperators

/-- Finiteness of exponents for stripped residual balance equations with a single-prime-power
odd denominator `d > 1`, `d < 2^k < 2 * d`, excluding Graham-reducible residuals. -/
def H1 : Prop :=
  ∀ d k : ℕ, Odd d → 1 < d → d < 2 ^ k → 2 ^ k < 2 * d →
    d.primeFactors.card = 1 →
    (¬ ∃ A : Finset ℕ, A ⊆ d.primeFactors ∧
      2 ^ k * (∏ q ∈ A, q) = d * (∏ q ∈ A, (q + 1))) →
    {a : ℕ | max 5 k ≤ a ∧ ∃ T : Finset ℕ,
      (∀ p ∈ T, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ d) ∧
      (2 ^ a + 1) * (∏ p ∈ T, (1 + p)) = 2 ^ (a + 1 - k) * d * (∏ p ∈ T, p)}.Finite

/-- Finiteness of exponents for stripped residual balance equations whose odd denominator `d`
still has at least two distinct prime factors, with `d < 2^k < 2 * d` and not Graham-reducible. -/
def H2 : Prop :=
  ∀ d k : ℕ, Odd d → 1 < d → d < 2 ^ k → 2 ^ k < 2 * d →
    2 ≤ d.primeFactors.card →
    (¬ ∃ A : Finset ℕ, A ⊆ d.primeFactors ∧
      2 ^ k * (∏ q ∈ A, q) = d * (∏ q ∈ A, (q + 1))) →
    {a : ℕ | max 5 k ≤ a ∧ ∃ T : Finset ℕ,
      (∀ p ∈ T, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ d) ∧
      (2 ^ a + 1) * (∏ p ∈ T, (1 + p)) = 2 ^ (a + 1 - k) * d * (∏ p ∈ T, p)}.Finite

/-- Factorization of `sigma*(2^a * c)` for positive `a` and odd `c`. -/
theorem sigma_power_two_times {a c : ℕ} (ha : 0 < a) (hc : Odd c) :
    (∏ q ∈ (2 ^ a * c).primeFactors, (1 + q ^ (2 ^ a * c).factorization q)) =
      (2 ^ a + 1) * (∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)) := by
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

/-- Every odd prime outside `c` dividing `sigma * prod_{p in F} (1 + p)` is forced into `S`
whenever `F subseteq S`. -/
theorem forced_step_subset {a c : ℕ} {S F : Finset ℕ} (ha : 0 < a) (hc : Odd c)
    (hS : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ q ∈ (2 ^ a * c).primeFactors, (1 + q ^ (2 ^ a * c).factorization q)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p))
    (hFS : F ⊆ S) :
    F ∪ (((∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)) *
      ∏ p ∈ F, (1 + p)).primeFactors.filter (fun r => r ≠ 2 ∧ ¬ r ∣ c)) ⊆ S := by
  let σ := ∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)
  rw [sigma_power_two_times ha hc] at hbal
  change ((2 ^ a + 1) * σ) * (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p) at hbal
  intro r hr
  rcases Finset.mem_union.mp hr with hrF | hrNew
  · exact hFS hrF
  · obtain ⟨hrpf, hr2, hrc⟩ := Finset.mem_filter.mp hrNew
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hrpf
    have hrdvdM : r ∣ σ * ∏ p ∈ F, (1 + p) := Nat.dvd_of_mem_primeFactors hrpf
    have hprodF : (∏ p ∈ F, (1 + p)) ∣ ∏ p ∈ S, (1 + p) :=
      Finset.prod_dvd_prod_of_subset F S (fun p => 1 + p) hFS
    have hrdvdLHS : r ∣ ((2 ^ a + 1) * σ) * (∏ p ∈ S, (1 + p)) := by
      have h1 : σ * (∏ p ∈ F, (1 + p)) ∣ ((2 ^ a + 1) * σ) * (∏ p ∈ S, (1 + p)) := by
        rw [mul_assoc (2 ^ a + 1) σ]
        exact dvd_mul_of_dvd_right (Nat.mul_dvd_mul_left σ hprodF) (2 ^ a + 1)
      exact hrdvdM.trans h1
    rw [hbal] at hrdvdLHS
    rcases hrp.dvd_mul.mp hrdvdLHS with hleft | hright
    · exfalso
      rcases hrp.dvd_mul.mp hleft with hr2' | hrest
      · exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp hr2')
      · rcases hrp.dvd_mul.mp hrest with hrpow | hrc'
        · exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp (hrp.dvd_of_dvd_pow hrpow))
        · exact hrc hrc'
    · obtain ⟨p, hpS, hrp'⟩ := (hrp.prime.dvd_finsetProd_iff _).mp hright
      have heq := (Nat.prime_dvd_prime_iff_eq hrp (hS p hpS).1).mp hrp'
      exact heq ▸ hpS

/-- A monotone inflationary operator on `Finset ℕ` bounded by `S₀` stabilizes by step `S₀.card`. -/
theorem iter_stabilizes {step : Finset ℕ → Finset ℕ} {S₀ : Finset ℕ}
    (hinc : ∀ F, F ⊆ step F)
    (hbdd : ∀ n, step^[n] ∅ ⊆ S₀) :
    step (step^[S₀.card] ∅) = step^[S₀.card] ∅ := by
  have hfix : ∀ k m, k ≤ m → step (step^[k] ∅) = step^[k] ∅ → step^[m] ∅ = step^[k] ∅ := by
    intro k m hkm hk
    induction m with
    | zero =>
      have hk0 : k = 0 := by omega
      subst hk0; rfl
    | succ m ih =>
      by_cases h : k = m + 1
      · subst h; rfl
      · rw [Function.iterate_succ_apply', ih (by omega), hk]
  by_contra hne
  have hne_all : ∀ k ≤ S₀.card, step (step^[k] ∅) ≠ step^[k] ∅ := by
    intro k hk heq
    apply hne
    have h1 := hfix k S₀.card hk heq
    rw [h1, heq]
  have hcard : ∀ k ≤ S₀.card + 1, k ≤ (step^[k] ∅).card := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hss : step^[k] ∅ ⊂ step^[k + 1] ∅ := by
        rw [Function.iterate_succ_apply']
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hinc _, (hne_all k (by omega)).symm⟩
      have hlt := Finset.card_lt_card hss
      have := ih (by omega)
      omega
  have hbig := hcard (S₀.card + 1) (le_refl _)
  have hle := Finset.card_le_card (hbdd (S₀.card + 1))
  omega

/-- Valuation of a product of distinct primes at any prime `q`. -/
theorem factorization_prime_prod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (∏ p ∈ S, p).factorization q = if q ∈ S then 1 else 0 := by
  classical
  rw [Nat.factorization_prod (fun p hp => (hS p hp).ne_zero), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by rw [(hS p hp).factorization, Finsupp.single_apply])]
  exact Finset.sum_ite_eq' S q _

/-- For every odd `c` with `1 < c` admitting at least one completion, the canonical forced-prime
closure `F` produces a fixed odd divisor `d | c` and exponent `k` with `1 < d`, `d < 2^k < 2 * d`,
and `d * (sigma * prod_{p in F} (1 + p)) = 2^k * (c * prod_{p in F} p)`, with `F subseteq S`
for every completion `(a, S)`. -/
theorem canonical_residual_of_nonempty {c : ℕ} (hc : Odd c) (hc1 : 1 < c)
    (a₀ : ℕ) (S₀ : Finset ℕ) (ha₀ : 0 < a₀)
    (hS₀ : ∀ p ∈ S₀, p.Prime ∧ ¬ p ∣ 2 ^ a₀ * c)
    (hbal₀ : (∏ q ∈ (2 ^ a₀ * c).primeFactors, (1 + q ^ (2 ^ a₀ * c).factorization q)) *
      (∏ p ∈ S₀, (1 + p)) = (2 * (2 ^ a₀ * c)) * (∏ p ∈ S₀, p)) :
    ∃ (F : Finset ℕ) (d k : ℕ),
      Odd d ∧ 1 < d ∧ d ∣ c ∧ d < 2 ^ k ∧ 2 ^ k < 2 * d ∧
      d * ((∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)) * ∏ p ∈ F, (1 + p)) =
        2 ^ k * (c * ∏ p ∈ F, p) ∧
      (∀ p ∈ F, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ c) ∧
      (∀ a : ℕ, ∀ S : Finset ℕ, 0 < a →
        (∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c) →
        (∏ q ∈ (2 ^ a * c).primeFactors, (1 + q ^ (2 ^ a * c).factorization q)) *
          (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p) → F ⊆ S) := by
  classical
  let σ := ∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)
  let step : Finset ℕ → Finset ℕ := fun F =>
    F ∪ ((σ * ∏ p ∈ F, (1 + p)).primeFactors.filter (fun r => r ≠ 2 ∧ ¬ r ∣ c))
  have hinc : ∀ F, F ⊆ step F := fun F => Finset.subset_union_left
  have hiter_sub : ∀ a S, 0 < a → (∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c) →
      (∏ q ∈ (2 ^ a * c).primeFactors, (1 + q ^ (2 ^ a * c).factorization q)) *
        (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p) →
      ∀ n, step^[n] ∅ ⊆ S := by
    intro a S ha hS hbal n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact forced_step_subset ha hc hS hbal ih
  have hiter_dvd : ∀ n, ∀ p ∈ step^[n] ∅, p ∣ σ * ∏ r ∈ step^[n] ∅, (1 + r) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro p hp
      rw [Function.iterate_succ_apply'] at hp ⊢
      have hsub : step^[n] ∅ ⊆ step (step^[n] ∅) := hinc _
      have hmul : (∏ r ∈ step^[n] ∅, (1 + r)) ∣ ∏ r ∈ step (step^[n] ∅), (1 + r) :=
        Finset.prod_dvd_prod_of_subset _ _ _ hsub
      rcases Finset.mem_union.mp hp with hpOld | hpNew
      · exact (ih p hpOld).trans (Nat.mul_dvd_mul_left σ hmul)
      · exact (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hpNew).1).trans
          (Nat.mul_dvd_mul_left σ hmul)
  let F := step^[S₀.card] ∅
  have hstab : step F = F := iter_stabilizes hinc (hiter_sub a₀ S₀ ha₀ hS₀ hbal₀)
  have hFall : ∀ a S, 0 < a → (∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c) →
      (∏ q ∈ (2 ^ a * c).primeFactors, (1 + q ^ (2 ^ a * c).factorization q)) *
        (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p) → F ⊆ S :=
    fun a S ha hS hbal => hiter_sub a S ha hS hbal S₀.card
  have hFS₀ : F ⊆ S₀ := hFall a₀ S₀ ha₀ hS₀ hbal₀
  have hFprops : ∀ p ∈ F, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ c := by
    intro p hp
    have hpS := hS₀ p (hFS₀ hp)
    refine ⟨hpS.1, fun h2 => hpS.2 (h2 ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 ha₀.ne') c),
      fun hpc => hpS.2 (dvd_mul_of_dvd_right hpc _)⟩
  let M := σ * ∏ p ∈ F, (1 + p)
  let D := c * ∏ p ∈ F, p
  have hσpos : 0 < σ := Finset.prod_pos fun _ _ => by omega
  have hMpos : 0 < M := Nat.mul_pos hσpos (Finset.prod_pos fun _ _ => by omega)
  have hFprodpos : 0 < ∏ p ∈ F, p := Finset.prod_pos fun p hp => (hFprops p hp).1.pos
  have hDpos : 0 < D := Nat.mul_pos hc.pos hFprodpos
  have hDodd : Odd D := hc.mul (Finset.prod_induction (fun p => p) Odd
    (fun _ _ => Odd.mul) odd_one (fun p hp => (hFprops p hp).1.odd_of_ne_two (hFprops p hp).2.1))
  have hM0 : M ≠ 0 := hMpos.ne'
  have hD0 : D ≠ 0 := hDpos.ne'
  have hM_odd_pos : 0 < ordCompl[2] M := Nat.ordCompl_pos 2 hM0
  have hM_odd_ne : ordCompl[2] M ≠ 0 := hM_odd_pos.ne'
  have hM_dvd_RHS : M ∣ (2 * (2 ^ a₀ * c)) * ∏ p ∈ S₀, p := by
    rw [← hbal₀, sigma_power_two_times ha₀ hc]
    have hprodF : (∏ p ∈ F, (1 + p)) ∣ ∏ p ∈ S₀, (1 + p) :=
      Finset.prod_dvd_prod_of_subset F S₀ _ hFS₀
    change σ * (∏ p ∈ F, (1 + p)) ∣ ((2 ^ a₀ + 1) * σ) * (∏ p ∈ S₀, (1 + p))
    rw [mul_assoc (2 ^ a₀ + 1) σ]
    exact dvd_mul_of_dvd_right (Nat.mul_dvd_mul_left σ hprodF) (2 ^ a₀ + 1)
  have hRHS_ne : (2 * (2 ^ a₀ * c)) * ∏ p ∈ S₀, p ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by decide) (mul_ne_zero (pow_ne_zero _ (by decide)) hc.pos.ne')
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => (hS₀ p hp).1.ne_zero
  have hord_dvd_M : ordCompl[2] M ∣ M := Nat.ordCompl_dvd M 2
  have hval_ord : ∀ q, (ordCompl[2] M).factorization q = if q = 2 then 0 else M.factorization q := by
    intro q
    have hfac := Nat.factorization_mul (pow_ne_zero (M.factorization 2) (by decide : (2 : ℕ) ≠ 0))
      hM_odd_ne
    rw [Nat.ordProj_mul_ordCompl_eq_self M 2] at hfac
    have hq := congrArg (fun f : ℕ →₀ ℕ => f q) hfac
    simp only [Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_apply] at hq
    by_cases hq2 : q = 2
    · subst hq2
      rw [if_pos rfl]
      exact Nat.factorization_eq_zero_of_not_dvd (Nat.not_dvd_ordCompl Nat.prime_two hM0)
    · rw [if_neg (Ne.symm hq2), zero_add] at hq
      rw [if_neg hq2]
      exact hq.symm
  have hS₀p : ∀ p ∈ S₀, p.Prime := fun p hp => (hS₀ p hp).1
  have hFp : ∀ p ∈ F, p.Prime := fun p hp => (hFprops p hp).1
  have hS₀prod_ne : (∏ p ∈ S₀, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hS₀p p hp).ne_zero
  have hFprod_ne : (∏ p ∈ F, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hFp p hp).ne_zero
  have hval_RHS (q : ℕ) (hq2 : q ≠ 2) :
      ((2 * (2 ^ a₀ * c)) * ∏ p ∈ S₀, p).factorization q =
        c.factorization q + (if q ∈ S₀ then 1 else 0) := by
    have h2pow : (2 : ℕ) * (2 ^ a₀ * c) = 2 ^ (a₀ + 1) * c := by rw [pow_succ]; ring
    rw [h2pow, Nat.factorization_mul (mul_ne_zero (pow_ne_zero _ (by decide)) hc.pos.ne') hS₀prod_ne,
      Nat.factorization_mul (pow_ne_zero _ (by decide)) hc.pos.ne',
      Finsupp.add_apply, Finsupp.add_apply, Nat.prime_two.factorization_pow,
      Finsupp.single_eq_of_ne hq2, zero_add, factorization_prime_prod hS₀p]
  have hval_D (q : ℕ) : D.factorization q = c.factorization q + (if q ∈ F then 1 else 0) := by
    dsimp [D]
    rw [Nat.factorization_mul hc.pos.ne' hFprod_ne, Finsupp.add_apply, factorization_prime_prod hFp]
  have hord_dvd_D : ordCompl[2] M ∣ D := by
    rw [← Nat.factorization_le_iff_dvd hM_odd_ne hD0]
    intro q
    rw [hval_ord q, hval_D q]
    by_cases hq2 : q = 2
    · rw [if_pos hq2]; omega
    · rw [if_neg hq2]
      by_cases hqM : M.factorization q = 0
      · omega
      · have hqpf : q ∈ M.primeFactors := by
          rw [← Nat.support_factorization, Finsupp.mem_support_iff]
          exact hqM
        have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqpf
        have hle_rhs : M.factorization q ≤ ((2 * (2 ^ a₀ * c)) * ∏ p ∈ S₀, p).factorization q :=
          (Nat.factorization_le_iff_dvd hM0 hRHS_ne).mpr hM_dvd_RHS q
        rw [hval_RHS q hq2] at hle_rhs
        by_cases hqc : q ∣ c
        · have hqnotS : q ∉ S₀ := fun h => (hS₀ q h).2 (dvd_mul_of_dvd_right hqc _)
          rw [if_neg hqnotS] at hle_rhs
          omega
        · have hqF : q ∈ F := by
            rw [← hstab]
            exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hqpf, hq2, hqc⟩)
          rw [if_pos (hFS₀ hqF)] at hle_rhs
          rw [if_pos hqF]
          exact hle_rhs
  let d := D / ordCompl[2] M
  let k := M.factorization 2
  have hd_mul : d * ordCompl[2] M = D := Nat.div_mul_cancel hord_dvd_D
  have hk_mul : 2 ^ k * ordCompl[2] M = M := Nat.ordProj_mul_ordCompl_eq_self M 2
  have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd hDpos hord_dvd_D) hM_odd_pos
  have hd_odd : Odd d := hDodd.of_dvd_nat ⟨ordCompl[2] M, hd_mul.symm⟩
  have hrel : d * M = 2 ^ k * D := by
    calc d * M = d * (2 ^ k * ordCompl[2] M) := by rw [hk_mul]
      _ = 2 ^ k * (d * ordCompl[2] M) := by ring
      _ = 2 ^ k * D := by rw [hd_mul]
  have hd_dvd_c : d ∣ c := by
    rw [← Nat.factorization_le_iff_dvd hd_pos.ne' hc.pos.ne']
    intro q
    have hfac_d : d.factorization q + (ordCompl[2] M).factorization q = D.factorization q := by
      have h := congrArg (fun f : ℕ →₀ ℕ => f q) (Nat.factorization_mul hd_pos.ne' hM_odd_ne)
      rw [hd_mul, Finsupp.add_apply] at h
      exact h.symm
    rw [hval_D q, hval_ord q] at hfac_d
    by_cases hqF : q ∈ F
    · have hq2 : q ≠ 2 := (hFprops q hqF).2.1
      have hqdvdM : q ∣ M := hiter_dvd S₀.card q hqF
      have hqpos : 1 ≤ M.factorization q := (hFprops q hqF).1.factorization_pos_of_dvd hM0 hqdvdM
      rw [if_pos hqF, if_neg hq2] at hfac_d
      omega
    · rw [if_neg hqF] at hfac_d
      omega
  have hσ_gt_c : c < σ := by
    have hne : c.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hc1
    have hlt : ∏ q ∈ c.primeFactors, q ^ c.factorization q <
        ∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q) :=
      Finset.prod_lt_prod_of_nonempty (fun q hq => pow_pos (Nat.prime_of_mem_primeFactors hq).pos _)
        (fun q _ => by omega) hne
    have hprod_c : ∏ q ∈ c.primeFactors, q ^ c.factorization q = c :=
      Nat.factorization_prod_pow_eq_self hc.pos.ne'
    simpa only [σ, hprod_c] using hlt
  have hM_gt_D : D < M := by
    have hF_le : ∏ p ∈ F, p ≤ ∏ p ∈ F, (1 + p) :=
      Finset.prod_le_prod' fun p _ => by omega
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hσ_gt_c hFprodpos)
      (Nat.mul_le_mul_left σ hF_le)
  have hd_lt_pow : d < 2 ^ k := by
    have h1 : d * D < 2 ^ k * D := by
      rw [← hrel]
      exact Nat.mul_lt_mul_of_pos_left hM_gt_D hd_pos
    exact Nat.lt_of_mul_lt_mul_right h1
  have hpow_lt_2d : 2 ^ k < 2 * d := by
    let T₀ := S₀ \ F
    have hT₀_prod1 : (∏ p ∈ F, (1 + p)) * (∏ p ∈ T₀, (1 + p)) = ∏ p ∈ S₀, (1 + p) := by
      rw [mul_comm]; exact Finset.prod_sdiff hFS₀
    have hT₀_prod2 : (∏ p ∈ F, p) * (∏ p ∈ T₀, p) = ∏ p ∈ S₀, p := by
      rw [mul_comm]; exact Finset.prod_sdiff hFS₀
    rw [sigma_power_two_times ha₀ hc] at hbal₀
    change ((2 ^ a₀ + 1) * σ) * (∏ p ∈ S₀, (1 + p)) = (2 * (2 ^ a₀ * c)) * (∏ p ∈ S₀, p) at hbal₀
    have hstrip0 : 2 ^ k * (2 ^ a₀ + 1) * (∏ p ∈ T₀, (1 + p)) =
        2 ^ (a₀ + 1) * d * (∏ p ∈ T₀, p) := by
      apply Nat.eq_of_mul_eq_mul_left hDpos
      calc D * (2 ^ k * (2 ^ a₀ + 1) * (∏ p ∈ T₀, (1 + p)))
          = (2 ^ k * D) * (2 ^ a₀ + 1) * (∏ p ∈ T₀, (1 + p)) := by ring
        _ = (d * M) * (2 ^ a₀ + 1) * (∏ p ∈ T₀, (1 + p)) := by rw [← hrel]
        _ = d * (((2 ^ a₀ + 1) * σ) * ((∏ p ∈ F, (1 + p)) * (∏ p ∈ T₀, (1 + p)))) := by
            dsimp [M]; ring
        _ = d * (((2 ^ a₀ + 1) * σ) * (∏ p ∈ S₀, (1 + p))) := by rw [hT₀_prod1]
        _ = d * ((2 * (2 ^ a₀ * c)) * (∏ p ∈ S₀, p)) := by rw [hbal₀]
        _ = d * ((2 * (2 ^ a₀ * c)) * ((∏ p ∈ F, p) * (∏ p ∈ T₀, p))) := by rw [hT₀_prod2]
        _ = D * (2 ^ (a₀ + 1) * d * (∏ p ∈ T₀, p)) := by dsimp [D]; rw [pow_succ]; ring
    have hT₀_pos : 0 < ∏ p ∈ T₀, p := Finset.prod_pos fun p hp => (hS₀ p (Finset.mem_sdiff.mp hp).1).1.pos
    have hT₀_le : ∏ p ∈ T₀, p ≤ ∏ p ∈ T₀, (1 + p) := Finset.prod_le_prod' fun p _ => by omega
    have hlt1 : 2 ^ k * 2 ^ a₀ * (∏ p ∈ T₀, p) < 2 ^ k * (2 ^ a₀ + 1) * (∏ p ∈ T₀, (1 + p)) := by
      have h1 : 2 ^ k * 2 ^ a₀ < 2 ^ k * (2 ^ a₀ + 1) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (Nat.two_pow_pos k)
      exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 hT₀_pos)
        (Nat.mul_le_mul_left _ hT₀_le)
    rw [hstrip0, pow_succ] at hlt1
    have hlt2 : 2 ^ k * (2 ^ a₀ * ∏ p ∈ T₀, p) < (2 * d) * (2 ^ a₀ * ∏ p ∈ T₀, p) := by
      linarith [hlt1]
    exact Nat.lt_of_mul_lt_mul_right hlt2
  have hd_gt_1 : 1 < d := by
    by_contra! hd1
    have hd_eq : d = 1 := by omega
    rw [hd_eq] at hd_lt_pow hpow_lt_2d
    omega
  exact ⟨F, d, k, hd_odd, hd_gt_1, hd_dvd_c, hd_lt_pow, hpow_lt_2d, hrel, hFprops, hFall⟩

/-- Generalized Graham elimination: whenever the residual ratio `2^k / d` matches
`prod_{q in A} (q + 1) / q` for a subset `A subseteq d.primeFactors`, substituting
`P = (S \ F) union A` yields Graham's balance equation, forcing `a < 10`. -/
theorem finite_of_graham_reducible {c d k : ℕ} {F : Finset ℕ} (hc : Odd c)
    (hd : 0 < d) (hdc : d ∣ c)
    (hrel : d * ((∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)) * ∏ p ∈ F, (1 + p)) =
      2 ^ k * (c * ∏ p ∈ F, p))
    (hFall : ∀ a : ℕ, ∀ S : Finset ℕ, 0 < a →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c) →
      (∏ q ∈ (2 ^ a * c).primeFactors, (1 + q ^ (2 ^ a * c).factorization q)) *
        (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p) → F ⊆ S)
    {A : Finset ℕ} (hAd : A ⊆ d.primeFactors)
    (hgraham : 2 ^ k * (∏ q ∈ A, q) = d * (∏ q ∈ A, (q + 1))) :
    {a : ℕ | let b := 2 ^ a * c
             let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
             5 ≤ a ∧ ∃ S : Finset ℕ, 4 ≤ S.card ∧ S ⊆ Finset.Icc 3 u ∧
               (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) ∧
               u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p}.Finite := by
  classical
  apply (Finset.range 10).finite_toSet.subset
  rintro a ⟨ha5, S, -, -, hS, hbal⟩
  have ha0 : 0 < a := by omega
  have hFS : F ⊆ S := hFall a S ha0 hS hbal
  let T := S \ F
  let P := T ∪ A
  have hDpos : 0 < c * ∏ p ∈ F, p := Nat.mul_pos hc.pos
    (Finset.prod_pos fun p hp => (hS p (hFS hp)).1.pos)
  have hT_prod1 : (∏ p ∈ F, (1 + p)) * (∏ p ∈ T, (1 + p)) = ∏ p ∈ S, (1 + p) := by
    rw [mul_comm]; exact Finset.prod_sdiff hFS
  have hT_prod2 : (∏ p ∈ F, p) * (∏ p ∈ T, p) = ∏ p ∈ S, p := by
    rw [mul_comm]; exact Finset.prod_sdiff hFS
  have hstrip : 2 ^ k * (2 ^ a + 1) * (∏ p ∈ T, (1 + p)) =
      2 ^ (a + 1) * d * (∏ p ∈ T, p) := by
    rw [sigma_power_two_times ha0 hc] at hbal
    apply Nat.eq_of_mul_eq_mul_left hDpos
    calc (c * ∏ p ∈ F, p) * (2 ^ k * (2 ^ a + 1) * (∏ p ∈ T, (1 + p)))
        = (2 ^ k * (c * ∏ p ∈ F, p)) * (2 ^ a + 1) * (∏ p ∈ T, (1 + p)) := by ring
      _ = (d * ((∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)) * ∏ p ∈ F, (1 + p))) *
            (2 ^ a + 1) * (∏ p ∈ T, (1 + p)) := by rw [← hrel]
      _ = d * (((2 ^ a + 1) * (∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q))) *
            ((∏ p ∈ F, (1 + p)) * (∏ p ∈ T, (1 + p)))) := by ring
      _ = d * (((2 ^ a + 1) * (∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q))) *
            (∏ p ∈ S, (1 + p))) := by rw [hT_prod1]
      _ = d * ((2 * (2 ^ a * c)) * (∏ p ∈ S, p)) := by rw [hbal]
      _ = d * ((2 * (2 ^ a * c)) * ((∏ p ∈ F, p) * (∏ p ∈ T, p))) := by rw [hT_prod2]
      _ = (c * ∏ p ∈ F, p) * (2 ^ (a + 1) * d * (∏ p ∈ T, p)) := by rw [pow_succ]; ring
  have hdisj : Disjoint T A := by
    refine Finset.disjoint_left.mpr fun p hpT hpA => ?_
    have hpS := (Finset.mem_sdiff.mp hpT).1
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors (hAd hpA)
    exact (hS p hpS).2 (dvd_mul_of_dvd_right (hpd.trans hdc) _)
  have hPprops : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpT | hpA
    · have hpS := hS p (Finset.mem_sdiff.mp hpT).1
      exact ⟨hpS.1, fun h2 => hpS.2 (h2 ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 ha0.ne') c)⟩
    · have hpf := hAd hpA
      have hpc : p ∣ c := (Nat.dvd_of_mem_primeFactors hpf).trans hdc
      have h2c : ¬ 2 ∣ c := by obtain ⟨i, hi⟩ := hc; omega
      exact ⟨Nat.prime_of_mem_primeFactors hpf, fun h2 => h2c (h2 ▸ hpc)⟩
  have hE : (2 ^ a + 1) * (∏ p ∈ P, (p + 1)) = 2 ^ (a + 1) * (∏ p ∈ P, p) := by
    have hP1 : ∏ p ∈ P, (p + 1) = (∏ p ∈ T, (1 + p)) * (∏ q ∈ A, (q + 1)) := by
      rw [Finset.prod_union hdisj]
      congr 1
      exact Finset.prod_congr rfl fun p _ => add_comm p 1
    have hP2 : ∏ p ∈ P, p = (∏ p ∈ T, p) * (∏ q ∈ A, q) := Finset.prod_union hdisj
    rw [hP1, hP2]
    have hkd : 0 < 2 ^ k * d := Nat.mul_pos (Nat.two_pow_pos k) hd
    apply Nat.eq_of_mul_eq_mul_left hkd
    calc (2 ^ k * d) * ((2 ^ a + 1) * ((∏ p ∈ T, (1 + p)) * (∏ q ∈ A, (q + 1))))
        = (2 ^ k * (2 ^ a + 1) * (∏ p ∈ T, (1 + p))) * (d * (∏ q ∈ A, (q + 1))) := by ring
      _ = (2 ^ (a + 1) * d * (∏ p ∈ T, p)) * (2 ^ k * (∏ q ∈ A, q)) := by rw [hstrip, ← hgraham]
      _ = (2 ^ k * d) * (2 ^ (a + 1) * ((∏ p ∈ T, p) * (∏ q ∈ A, q))) := by ring
  rcases OMA.R_Erdos1052_erdos_1052_R2_H2_R1.Graham1052.core hPprops hE (by omega) with
    ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R1.H3 := by
  classical
  intro h1 h2 c hc _ hcard
  let Target := {a : ℕ | let b := 2 ^ a * c
                         let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
                         5 ≤ a ∧ ∃ S : Finset ℕ, 4 ≤ S.card ∧ S ⊆ Finset.Icc 3 u ∧
                           (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) ∧
                           u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p}
  change Target.Finite
  by_cases hne : Target.Nonempty
  · obtain ⟨a₀, ha₀5, S₀, -, -, hS₀, hbal₀⟩ := hne
    have hc1 : 1 < c := by
      have hpos : 0 < c.primeFactors.card := by omega
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hle := Nat.le_of_dvd hc.pos (Nat.dvd_of_mem_primeFactors hq)
      have := hqp.two_le
      omega
    obtain ⟨F, d, k, hd_odd, hd1, hdc, hdk, hk2d, hrel, _, hFall⟩ :=
      canonical_residual_of_nonempty hc hc1 a₀ S₀ (by omega) hS₀ hbal₀
    by_cases hg : ∃ A : Finset ℕ, A ⊆ d.primeFactors ∧
        2 ^ k * (∏ q ∈ A, q) = d * (∏ q ∈ A, (q + 1))
    · obtain ⟨A, hAd, hgraham⟩ := hg
      exact finite_of_graham_reducible hc (by omega) hdc hrel hFall hAd hgraham
    · let Stripped := {a : ℕ | max 5 k ≤ a ∧ ∃ T : Finset ℕ,
        (∀ p ∈ T, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ d) ∧
        (2 ^ a + 1) * (∏ p ∈ T, (1 + p)) = 2 ^ (a + 1 - k) * d * (∏ p ∈ T, p)}
      have hStripped_fin : Stripped.Finite := by
        have hd_card_pos : 0 < d.primeFactors.card :=
          Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hd1)
        by_cases hsingle : d.primeFactors.card = 1
        · exact h1 d k hd_odd hd1 hdk hk2d hsingle hg
        · exact h2 d k hd_odd hd1 hdk hk2d (by omega) hg
      apply ((Finset.range (max 5 k)).finite_toSet.union hStripped_fin).subset
      intro a ha
      by_cases hsmall : a < max 5 k
      · exact Or.inl (Finset.mem_range.mpr hsmall)
      · right
        obtain ⟨ha5, S, -, -, hS, hbal⟩ := ha
        have ha0 : 0 < a := by omega
        have hka : k ≤ a := by omega
        have hFS : F ⊆ S := hFall a S ha0 hS hbal
        let T := S \ F
        refine ⟨by omega, T, ?_, ?_⟩
        · intro p hpT
          have hpS := hS p (Finset.mem_sdiff.mp hpT).1
          exact ⟨hpS.1, fun h2 => hpS.2 (h2 ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 ha0.ne') c),
            fun hpd => hpS.2 (dvd_mul_of_dvd_right (hpd.trans hdc) _)⟩
        · have hDpos : 0 < c * ∏ p ∈ F, p := Nat.mul_pos hc.pos
            (Finset.prod_pos fun p hp => (hS p (hFS hp)).1.pos)
          have hT_prod1 : (∏ p ∈ F, (1 + p)) * (∏ p ∈ T, (1 + p)) = ∏ p ∈ S, (1 + p) := by
            rw [mul_comm]; exact Finset.prod_sdiff hFS
          have hT_prod2 : (∏ p ∈ F, p) * (∏ p ∈ T, p) = ∏ p ∈ S, p := by
            rw [mul_comm]; exact Finset.prod_sdiff hFS
          rw [sigma_power_two_times ha0 hc] at hbal
          have hpow_split : (2 : ℕ) ^ (a + 1) = 2 ^ k * 2 ^ (a + 1 - k) := by
            rw [← pow_add]; congr 1; omega
          apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.two_pow_pos k) hDpos)
          calc (2 ^ k * (c * ∏ p ∈ F, p)) * ((2 ^ a + 1) * (∏ p ∈ T, (1 + p)))
              = (d * ((∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q)) * ∏ p ∈ F, (1 + p))) *
                  ((2 ^ a + 1) * (∏ p ∈ T, (1 + p))) := by rw [← hrel]
            _ = d * (((2 ^ a + 1) * (∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q))) *
                  ((∏ p ∈ F, (1 + p)) * (∏ p ∈ T, (1 + p)))) := by ring
            _ = d * (((2 ^ a + 1) * (∏ q ∈ c.primeFactors, (1 + q ^ c.factorization q))) *
                  (∏ p ∈ S, (1 + p))) := by rw [hT_prod1]
            _ = d * ((2 * (2 ^ a * c)) * (∏ p ∈ S, p)) := by rw [hbal]
            _ = d * ((2 ^ (a + 1) * c) * ((∏ p ∈ F, p) * (∏ p ∈ T, p))) := by
                rw [hT_prod2, pow_succ]; ring
            _ = d * ((2 ^ k * 2 ^ (a + 1 - k) * c) * ((∏ p ∈ F, p) * (∏ p ∈ T, p))) := by
                rw [hpow_split]
            _ = (2 ^ k * (c * ∏ p ∈ F, p)) * (2 ^ (a + 1 - k) * d * (∏ p ∈ T, p)) := by ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

end OMA.R_Erdos1052_erdos_1052_R2_H2_R1_H3_R1
