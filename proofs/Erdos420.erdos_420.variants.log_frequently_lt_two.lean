import FormalConjectures.ErdosProblems.«420»
import Mathlib.NumberTheory.Chebyshev

/-!
# Proof of Erdos420.erdos_420.variants.log_frequently_lt_two

For every `c > 0`, there are infinitely many `n` such that
`τ((n + ⌊c * log n⌋₊)!) / τ(n!) < 2`.

We combine:
1. A divisor-ratio upper bound via prime factorizations and `v_p(n!) + 1 > n / p`.
2. Chebyshev-only prime estimates from `Mathlib.NumberTheory.Chebyshev`.
3. Rankin's smooth-number bound and a greedy Chinese Remainder Theorem covering
   of `{1, ..., H}` by primes in `((log z)^26, z]`.
4. Selberg's upper bound sieve on arithmetic progressions, averaged over `k ∈ [1, P]`.
-/

namespace Erdos420Proof

open Filter Real Finset
open scoped ArithmeticFunction.sigma ArithmeticFunction.Moebius BigOperators Nat.Prime

/- ### Part 1: Divisor-ratio bound -/

private lemma padic_factorial_ge_div (n p : ℕ) (hp : p.Prime) :
    n / p ≤ n.factorial.factorization p := by
  have h1 : n / p ≤ ∑ i ∈ Ico 1 (Nat.log p n + 1), n / p ^ i := by
    by_cases hnp : n < p
    · rw [Nat.div_eq_of_lt hnp]; exact Nat.zero_le _
    · push Not at hnp
      have hlog : 1 ≤ Nat.log p n := Nat.le_log_of_pow_le hp.one_lt (by simpa using hnp)
      have hmem : 1 ∈ Ico 1 (Nat.log p n + 1) := mem_Ico.mpr ⟨le_rfl, by omega⟩
      have hle := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) hmem
      simpa using hle
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, padicValNat_factorial (Nat.lt_succ_self _)]
  exact h1

private lemma nat_lt_mul_div_add_one (n p : ℕ) (hp : 0 < p) :
    (n : ℝ) < (p : ℝ) * ((n / p : ℕ) + 1 : ℝ) := by
  have h : n < p * (n / p + 1) := by
    have hmod := Nat.div_add_mod n p
    have hlt := Nat.mod_lt n hp
    nlinarith
  exact_mod_cast h

private lemma sigma_zero_eq_prod_factorization (m : ℕ) (hm : m ≠ 0) :
    (σ 0 m : ℝ) = ∏ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1) := by
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm]
  push_cast
  rfl

private lemma factorial_primeFactors_subset (n h : ℕ) :
    n.factorial.primeFactors ⊆ (n + h).factorial.primeFactors := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, hp.2.1.trans (Nat.factorial_dvd_factorial (Nat.le_add_right n h)),
    Nat.factorial_ne_zero _⟩

private lemma factorization_factorial_add (n h p : ℕ) :
    (n + h).factorial.factorization p =
      n.factorial.factorization p + ∑ j ∈ range h, (n + j + 1).factorization p := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show n + (h + 1) = (n + h) + 1 by omega, Nat.factorial_succ,
      Nat.factorization_mul (by omega) (Nat.factorial_ne_zero _), Finsupp.coe_add, Pi.add_apply,
      ih, Finset.sum_range_succ]
    ring

private lemma ratio_le_exp_prime_cost (n h : ℕ) (hn : 0 < n) :
    (σ 0 (n + h).factorial : ℝ) / (σ 0 n.factorial : ℝ) ≤
      exp ((∑ j ∈ range h,
        ∑ p ∈ (n + j + 1).primeFactors, ((n + j + 1).factorization p : ℝ) * (p : ℝ)) / (n : ℝ)) := by
  rw [sigma_zero_eq_prod_factorization _ (Nat.factorial_ne_zero _),
      sigma_zero_eq_prod_factorization _ (Nat.factorial_ne_zero _)]
  have hsub := factorial_primeFactors_subset n h
  have hprod_eq : ∏ p ∈ n.factorial.primeFactors, ((n.factorial.factorization p : ℝ) + 1) =
      ∏ p ∈ (n + h).factorial.primeFactors, ((n.factorial.factorization p : ℝ) + 1) := by
    apply Finset.prod_subset hsub
    intro p _ hpnot
    have h0 : n.factorial.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hpnot)
    simp [h0]
  rw [hprod_eq, ← Finset.prod_div_distrib]
  calc
    ∏ p ∈ (n + h).factorial.primeFactors,
        (((n + h).factorial.factorization p : ℝ) + 1) / ((n.factorial.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ (n + h).factorial.primeFactors,
          exp ((∑ j ∈ range h, ((n + j + 1).factorization p : ℝ)) * (p : ℝ) / (n : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p _
          positivity
        · intro p hp
          have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hden_pos : (0 : ℝ) < (n.factorial.factorization p : ℝ) + 1 := by positivity
          have hfac := factorization_factorial_add n h p
          have hrat :
              (((n + h).factorial.factorization p : ℝ) + 1) / ((n.factorial.factorization p : ℝ) + 1) =
              1 + (∑ j ∈ range h, ((n + j + 1).factorization p : ℝ)) /
                ((n.factorial.factorization p : ℝ) + 1) := by
            rw [hfac]
            push_cast
            field_simp [hden_pos.ne']
            ring
          rw [hrat, add_comm 1]
          refine (add_one_le_exp _).trans (exp_le_exp.mpr ?_)
          have hge : (n / p : ℕ) ≤ n.factorial.factorization p :=
            padic_factorial_ge_div n p hp_prime
          have hgeR : ((n / p : ℕ) : ℝ) + 1 ≤ (n.factorial.factorization p : ℝ) + 1 := by
            have : ((n / p : ℕ) : ℝ) ≤ (n.factorial.factorization p : ℝ) := by exact_mod_cast hge
            linarith
          have hlt := nat_lt_mul_div_add_one n p hp_prime.pos
          have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
          have hinv : (1 : ℝ) / ((n.factorial.factorization p : ℝ) + 1) ≤ (p : ℝ) / (n : ℝ) := by
            rw [div_le_div_iff₀ hden_pos hnR, one_mul]
            nlinarith [show (0 : ℝ) < (p : ℝ) from by exact_mod_cast hp_prime.pos]
          have hsum_nn : 0 ≤ ∑ j ∈ range h, ((n + j + 1).factorization p : ℝ) :=
            sum_nonneg fun _ _ => by positivity
          calc
            (∑ j ∈ range h, ((n + j + 1).factorization p : ℝ)) /
                ((n.factorial.factorization p : ℝ) + 1)
              = (∑ j ∈ range h, ((n + j + 1).factorization p : ℝ)) *
                (1 / ((n.factorial.factorization p : ℝ) + 1)) := by ring
            _ ≤ (∑ j ∈ range h, ((n + j + 1).factorization p : ℝ)) * ((p : ℝ) / (n : ℝ)) :=
                mul_le_mul_of_nonneg_left hinv hsum_nn
            _ = _ := by ring
    _ = exp ((∑ p ∈ (n + h).factorial.primeFactors,
          (∑ j ∈ range h, ((n + j + 1).factorization p : ℝ)) * (p : ℝ)) / (n : ℝ)) := by
        rw [← Real.exp_sum, sum_div]
    _ = exp ((∑ j ∈ range h,
          ∑ p ∈ (n + j + 1).primeFactors, ((n + j + 1).factorization p : ℝ) * (p : ℝ)) / (n : ℝ)) := by
        congr 2
        trans ∑ p ∈ (n + h).factorial.primeFactors,
          ∑ j ∈ range h, ((n + j + 1).factorization p : ℝ) * (p : ℝ)
        · refine sum_congr rfl fun p _ => ?_
          rw [sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun j hj => ?_
        have hsub_j : (n + j + 1).primeFactors ⊆ (n + h).factorial.primeFactors := by
          intro p hp
          rw [Nat.mem_primeFactors] at hp ⊢
          have hj_lt : j < h := mem_range.mp hj
          exact ⟨hp.1, hp.2.1.trans (Nat.dvd_factorial (by omega) (by omega)),
            Nat.factorial_ne_zero _⟩
        symm
        apply Finset.sum_subset hsub_j
        intro p _ hpnot
        have h0 : (n + j + 1).factorization p = 0 :=
          Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hpnot)
        simp [h0]

private lemma sum_factorization_le_log2 (m : ℕ) (hm : 0 < m) :
    ((∑ p ∈ m.primeFactors, m.factorization p : ℕ) : ℝ) ≤ log m / log 2 := by
  have hpow : 2 ^ (∑ p ∈ m.primeFactors, m.factorization p) ≤ m := by
    have hprod : ∏ p ∈ m.primeFactors, p ^ m.factorization p = m :=
      Nat.prod_factorization_pow_eq_self hm.ne'
    rw [← Finset.prod_pow_eq_pow_sum]
    calc
      ∏ p ∈ m.primeFactors, 2 ^ m.factorization p
        ≤ ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
          apply Finset.prod_le_prod'
          intro p hp
          exact Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _
      _ = m := hprod
  have hpowR : (2 : ℝ) ^ (∑ p ∈ m.primeFactors, m.factorization p) ≤ (m : ℝ) := by
    exact_mod_cast hpow
  have hlog := log_le_log (by positivity) hpowR
  rw [log_pow] at hlog
  rw [le_div_iff₀ (log_pos (by norm_num))]
  exact hlog

/- ### Part 2: Selberg's Upper Bound Sieve on Arithmetic Progressions -/

private lemma card_ap_dvd_le (N a b L : ℕ) (hL : 0 < L) (hcop : Nat.Coprime b L) :
    ((range N).filter (fun t => L ∣ a + t * b)).card ≤ N / L + 1 := by
  have hblock : ∀ m : ℕ, ((Ico m (m + L)).filter (fun t => L ∣ a + t * b)).card ≤ 1 := by
    intro m
    rw [Finset.card_le_one]
    intro t₁ ht₁ t₂ ht₂
    rw [mem_filter, mem_Ico] at ht₁ ht₂
    have hdvd : L ∣ (a + t₁ * b) := ht₁.2
    have hdvd2 : L ∣ (a + t₂ * b) := ht₂.2
    wlog hle : t₁ ≤ t₂ generalizing t₁ t₂
    · exact (this t₂ ht₂ t₁ ht₁ hdvd2 hdvd (le_of_not_ge hle)).symm
    have hsub : L ∣ (t₂ - t₁) * b := by
      have heq : (a + t₂ * b) - (a + t₁ * b) = (t₂ - t₁) * b := by
        rw [Nat.sub_mul]
        omega
      rw [← heq]
      exact Nat.dvd_sub hdvd2 hdvd
    have hdvd_diff : L ∣ t₂ - t₁ := hcop.symm.dvd_of_dvd_mul_right hsub
    have hlt : t₂ - t₁ < L := by omega
    have h0 : t₂ - t₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_diff hlt
    omega
  have hsub : (range N).filter (fun t => L ∣ a + t * b) ⊆
      (range (N / L + 1)).biUnion
        (fun q => (Ico (q * L) (q * L + L)).filter (fun t => L ∣ a + t * b)) := by
    intro t ht
    rw [mem_filter, mem_range] at ht
    rw [mem_biUnion]
    refine ⟨t / L, mem_range.mpr ?_, mem_filter.mpr ⟨mem_Ico.mpr ?_, ht.2⟩⟩
    · exact Nat.lt_succ_of_le (Nat.div_le_div_right ht.1.le)
    · have hmod := Nat.div_add_mod t L
      have hlt := Nat.mod_lt t hL
      have hcomm : t / L * L = L * (t / L) := Nat.mul_comm _ _
      constructor <;> omega
  calc
    ((range N).filter (fun t => L ∣ a + t * b)).card
      ≤ ((range (N / L + 1)).biUnion
          (fun q => (Ico (q * L) (q * L + L)).filter (fun t => L ∣ a + t * b))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ q ∈ range (N / L + 1),
          ((Ico (q * L) (q * L + L)).filter (fun t => L ∣ a + t * b)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ range (N / L + 1), 1 := sum_le_sum fun q _ => hblock (q * L)
    _ = N / L + 1 := by simp

private lemma card_ap_dvd_ge (N a b L : ℕ) (hL : 0 < L) (hcop : Nat.Coprime b L) :
    N / L ≤ ((range N).filter (fun t => L ∣ a + t * b)).card := by
  have hex : ∀ m : ℕ, ∃ t ∈ Ico m (m + L), L ∣ a + t * b := by
    intro m
    have hunit : IsUnit (b : ZMod L) := (ZMod.isUnit_iff_coprime b L).mpr hcop
    let u := hunit.unit
    let r : ZMod L := -(a : ZMod L) * (u⁻¹ : (ZMod L)ˣ)
    let x : ℕ := r.val
    have hx_lt : x < L := by
      have : NeZero L := ⟨hL.ne'⟩
      exact ZMod.val_lt r
    let t := m + (x + L - m % L) % L
    have ht_mem : t ∈ Ico m (m + L) := by
      rw [mem_Ico]
      exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.mod_lt _ hL) m⟩
    refine ⟨t, ht_mem, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    have ht_mod : (t : ZMod L) = r := by
      have h1 : t % L = x := by
        have hltm : m % L < L := Nat.mod_lt m hL
        have hmod1 : (m + (x + L - m % L) % L) % L = (m % L + (x + L - m % L)) % L := by
          simp [Nat.add_mod]
        rw [show t = m + (x + L - m % L) % L from rfl, hmod1]
        have heq : m % L + (x + L - m % L) = x + L := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hx_lt]
      have : NeZero L := ⟨hL.ne'⟩
      rw [← ZMod.natCast_mod, h1]
      exact ZMod.natCast_zmod_val r
    rw [ht_mod]
    have hbu : (b : ZMod L) = (u : ZMod L) := rfl
    rw [hbu]
    simp [r, mul_assoc]
  have hsub : (range (N / L)).biUnion
      (fun q => (Ico (q * L) (q * L + L)).filter (fun t => L ∣ a + t * b)) ⊆
      (range N).filter (fun t => L ∣ a + t * b) := by
    intro t ht
    rw [mem_biUnion] at ht
    obtain ⟨q, hq, htq⟩ := ht
    rw [mem_range] at hq
    rw [mem_filter, mem_Ico] at htq
    rw [mem_filter, mem_range]
    have hqL : q * L + L ≤ N := by
      have : (q + 1) * L ≤ (N / L) * L := Nat.mul_le_mul_right L hq
      have := Nat.div_mul_le_self N L
      nlinarith
    exact ⟨by omega, htq.2⟩
  have hdisj : Set.PairwiseDisjoint (↑(range (N / L)) : Set ℕ)
      (fun q => (Ico (q * L) (q * L + L)).filter (fun t => L ∣ a + t * b)) := by
    intro q₁ _ q₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro t ht₁ ht₂
    rw [mem_filter, mem_Ico] at ht₁ ht₂
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : q₁ * L + L ≤ q₂ * L := by nlinarith
      omega
    · have : q₂ * L + L ≤ q₁ * L := by nlinarith
      omega
  calc
    N / L = ∑ _q ∈ range (N / L), 1 := by simp
    _ ≤ ∑ q ∈ range (N / L),
          ((Ico (q * L) (q * L + L)).filter (fun t => L ∣ a + t * b)).card := by
        apply sum_le_sum
        intro q _
        obtain ⟨t, ht1, ht2⟩ := hex (q * L)
        exact Finset.card_pos.mpr ⟨t, mem_filter.mpr ⟨ht1, ht2⟩⟩
    _ = ((range (N / L)).biUnion
          (fun q => (Ico (q * L) (q * L + L)).filter (fun t => L ∣ a + t * b))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ ((range N).filter (fun t => L ∣ a + t * b)).card := Finset.card_le_card hsub

private lemma abs_card_ap_dvd_sub_le (N a b L : ℕ) (hL : 0 < L) (hcop : Nat.Coprime b L) :
    |(((range N).filter (fun t => L ∣ a + t * b)).card : ℝ) - (N : ℝ) / (L : ℝ)| ≤ 1 := by
  have hle : (((range N).filter (fun t => L ∣ a + t * b)).card : ℝ) ≤ (N / L : ℕ) + 1 := by
    exact_mod_cast card_ap_dvd_le N a b L hL hcop
  have hge : ((N / L : ℕ) : ℝ) ≤ (((range N).filter (fun t => L ∣ a + t * b)).card : ℝ) := by
    exact_mod_cast card_ap_dvd_ge N a b L hL hcop
  have hdiv_le : ((N / L : ℕ) : ℝ) ≤ (N : ℝ) / (L : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hL)]
    exact_mod_cast Nat.div_mul_le_self N L
  have hdiv_gt : (N : ℝ) / (L : ℝ) < ((N / L : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ (by exact_mod_cast hL)]
    have hlt := nat_lt_mul_div_add_one N L hL
    linarith
  rw [abs_le]
  constructor <;> linarith

private lemma sum_inv_totient_divisors_of_squarefree (d : ℕ) (hd : Squarefree d) :
    ∑ u ∈ d.divisors, (1 : ℝ) / (u.totient : ℝ) = (d : ℝ) / (d.totient : ℝ) := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hphi_pos : ∀ u ∈ d.divisors, (0 : ℝ) < (u.totient : ℝ) := by
    intro u hu
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hu) hd_pos)
  have hd_phi_pos : (0 : ℝ) < (d.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hd_pos
  rw [eq_div_iff hd_phi_pos.ne', sum_mul]
  have hterm : ∀ u ∈ d.divisors,
      (1 : ℝ) / (u.totient : ℝ) * (d.totient : ℝ) = ((d / u).totient : ℝ) := by
    intro u hu
    have hud : u ∣ d := Nat.dvd_of_mem_divisors hu
    have hcop : Nat.Coprime u (d / u) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      have hgt : 1 < Nat.gcd u (d / u) := by
        have hpos : 0 < Nat.gcd u (d / u) :=
          Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos hud hd_pos)
        omega
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgt.ne'
      have hp1 : p ∣ u := hpd.trans (Nat.gcd_dvd_left _ _)
      have hp2 : p ∣ d / u := hpd.trans (Nat.gcd_dvd_right _ _)
      have hpp : p * p ∣ d := by
        have := Nat.mul_dvd_mul hp1 hp2
        rwa [Nat.mul_div_cancel' hud] at this
      exact hp.not_isUnit (hd p hpp)
    have hmul : (u.totient : ℝ) * ((d / u).totient : ℝ) = (d.totient : ℝ) := by
      exact_mod_cast (Nat.totient_mul hcop).symm.trans (by rw [Nat.mul_div_cancel' hud])
    have hu_ne : (u.totient : ℝ) ≠ 0 := (hphi_pos u hu).ne'
    rw [← hmul]
    field_simp [hu_ne]
  rw [sum_congr rfl hterm]
  have hbij : ∑ u ∈ d.divisors, ((d / u).totient : ℝ) = ∑ v ∈ d.divisors, (v.totient : ℝ) := by
    refine Finset.sum_bij (fun u _ => d / u) ?_ ?_ ?_ ?_
    · intro u hu
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hu), hd_pos.ne'⟩
    · intro u₁ hu₁ u₂ hu₂ heq
      have h1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hu₁)
      have h2 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hu₂)
      rw [heq] at h1
      have hpos : 0 < d / u₂ := Nat.div_pos (Nat.le_of_dvd hd_pos (Nat.dvd_of_mem_divisors hu₂))
        (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hu₂) hd_pos)
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    · intro v hv
      refine ⟨d / v, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hv), hd_pos.ne'⟩, ?_⟩
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hv) hd_pos.ne'
    · intro _ _; rfl
  rw [hbij]
  exact_mod_cast Nat.sum_totient d

private lemma selberg_sieve_ap (N Z a b : ℕ) (Q : Finset ℕ)
    (hZ : 1 ≤ Z)
    (_hQ_prime : ∀ q ∈ Q, q.Prime)
    (hQ_cop : ∀ q ∈ Q, ¬ q ∣ b) :
    let D := (Icc 1 Z).filter (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, p ∈ Q)
    let S := ∑ d ∈ D, (1 : ℝ) / (d.totient : ℝ)
    (((range N).filter (fun t => ∀ q ∈ Q, ¬ q ∣ a + t * b)).card : ℝ) ≤
      (N : ℝ) / S + (Z : ℝ) ^ 2 := by
  intro D S
  have h1D : 1 ∈ D := by
    simp [D, hZ]
  have hD_sqf : ∀ d ∈ D, Squarefree d := fun d hd => (mem_filter.mp hd).2.1
  have hD_pos : ∀ d ∈ D, 0 < d := fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).1
  have hD_le : ∀ d ∈ D, d ≤ Z := fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).2
  have hD_pf : ∀ d ∈ D, ∀ p ∈ d.primeFactors, p ∈ Q := fun d hd => (mem_filter.mp hd).2.2
  have hD_dvd : ∀ d ∈ D, ∀ e, e ∣ d → e ∈ D := by
    intro d hd e hed
    have he_pos : 0 < e := Nat.pos_of_dvd_of_pos hed (hD_pos d hd)
    have he_le : e ≤ Z := (Nat.le_of_dvd (hD_pos d hd) hed).trans (hD_le d hd)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨he_pos, he_le⟩,
      (hD_sqf d hd).squarefree_of_dvd hed, fun p hp => ?_⟩
    exact hD_pf d hd p (Nat.primeFactors_mono hed (hD_pos d hd).ne' hp)
  have hS_pos : 0 < S := by
    refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / ((1 : ℕ).totient : ℝ)) ?_
    exact Finset.single_le_sum (f := fun d => (1 : ℝ) / (d.totient : ℝ)) (fun d _ => by positivity) h1D
  -- Define Selberg weights
  let y : ℕ → ℝ := fun e => if e ∈ D then (μ e : ℝ) / ((e.totient : ℝ) * S) else 0
  let lam : ℕ → ℝ := fun d => (d : ℝ) * ∑ e ∈ D.filter (fun e => d ∣ e), (μ (e / d) : ℝ) * y e
  -- 1. lam 1 = 1
  have hlam1 : lam 1 = 1 := by
    simp only [lam, Nat.cast_one, one_mul, Nat.one_dvd, Finset.filter_true, Nat.div_one]
    have hterm : ∀ e ∈ D, (μ e : ℝ) * y e = (1 : ℝ) / ((e.totient : ℝ) * S) := by
      intro e he
      simp only [y, he, ↓reduceIte]
      have hsq : Squarefree e := hD_sqf e he
      have hmu2 : (μ e : ℝ) * (μ e : ℝ) = 1 := by
        have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
        exact_mod_cast (by rw [← sq]; exact h)
      calc
        (μ e : ℝ) * ((μ e : ℝ) / ((e.totient : ℝ) * S))
          = ((μ e : ℝ) * (μ e : ℝ)) / ((e.totient : ℝ) * S) := by ring
        _ = 1 / ((e.totient : ℝ) * S) := by rw [hmu2]
    rw [sum_congr rfl hterm]
    have : ∑ e ∈ D, (1 : ℝ) / ((e.totient : ℝ) * S) = S / S := by
      rw [show S = ∑ e ∈ D, (1 : ℝ) / (e.totient : ℝ) from rfl, sum_div]
      refine sum_congr rfl fun e _ => by ring
    rw [this, div_self hS_pos.ne']
  -- 2. Inversion: ∑_{d ∈ D, e ∣ d} lam d / d = y e for e ∈ D
  have hinv : ∀ e ∈ D, ∑ d ∈ D.filter (fun d => e ∣ d), lam d / (d : ℝ) = y e := by
    intro e he
    have hsimp : ∀ d ∈ D.filter (fun d => e ∣ d),
        lam d / (d : ℝ) = ∑ f ∈ D.filter (fun f => d ∣ f), (μ (f / d) : ℝ) * y f := by
      intro d hd
      have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hD_pos d (mem_filter.mp hd).1
      simp only [lam]
      field_simp [hd_pos.ne']
    rw [sum_congr rfl hsimp]
    -- Swap sums over (d, f) with e ∣ d ∣ f, f ∈ D
    have hswap :
        ∑ d ∈ D.filter (fun d => e ∣ d), ∑ f ∈ D.filter (fun f => d ∣ f), (μ (f / d) : ℝ) * y f =
        ∑ f ∈ D.filter (fun f => e ∣ f),
          (∑ d ∈ (f / e).divisors, (μ ((f / e) / d) : ℝ)) * y f := by
      -- First rewrite as sum over f ∈ D with e ∣ f of sum over d with e ∣ d ∧ d ∣ f
      trans ∑ f ∈ D.filter (fun f => e ∣ f),
          ∑ d ∈ D.filter (fun d => e ∣ d ∧ d ∣ f), (μ (f / d) : ℝ) * y f
      · rw [Finset.sum_sigma', Finset.sum_sigma']
        refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
        · intro ⟨d, f⟩ hp
          simp only [Finset.mem_sigma, mem_filter] at hp ⊢
          exact ⟨⟨hp.2.1, hp.1.2.trans hp.2.2⟩, hp.1.1, hp.1.2, hp.2.2⟩
        · intro ⟨d₁, f₁⟩ _ ⟨d₂, f₂⟩ _ h
          cases h; rfl
        · intro ⟨f, d⟩ hp
          simp only [Finset.mem_sigma, mem_filter] at hp
          exact ⟨⟨d, f⟩, by simp [hp.1.1, hp.2.1, hp.2.2.1, hp.2.2.2], rfl⟩
        · intro _ _; rfl
      · refine sum_congr rfl fun f hf => ?_
        rw [sum_mul]
        have hfD : f ∈ D := (mem_filter.mp hf).1
        have hef : e ∣ f := (mem_filter.mp hf).2
        have he_pos : 0 < e := hD_pos e he
        have hf_pos : 0 < f := hD_pos f hfD
        refine Finset.sum_bij (fun d _ => d / e) ?_ ?_ ?_ ?_
        · intro d hd
          simp only [mem_filter] at hd
          rw [Nat.mem_divisors]
          refine ⟨?_, (Nat.div_pos (Nat.le_of_dvd hf_pos hef) he_pos).ne'⟩
          exact Nat.div_dvd_div hd.2.1 hd.2.2
        · intro d₁ hd₁ d₂ hd₂ heq
          simp only [mem_filter] at hd₁ hd₂
          have h1 := Nat.mul_div_cancel' hd₁.2.1
          have h2 := Nat.mul_div_cancel' hd₂.2.1
          rw [← h1, ← h2, heq]
        · intro k hk
          rw [Nat.mem_divisors] at hk
          have hekf : e * k ∣ f := by
            have := Nat.mul_dvd_mul_left e hk.1
            rwa [Nat.mul_div_cancel' hef] at this
          refine ⟨e * k, mem_filter.mpr ⟨hD_dvd f hfD (e * k) hekf, dvd_mul_right e k, hekf⟩, ?_⟩
          exact Nat.mul_div_cancel_left k he_pos
        · intro d hd
          simp only [mem_filter] at hd
          have heq : f / d = (f / e) / (d / e) := by
            obtain ⟨q, rfl⟩ := hd.2.1
            rw [Nat.mul_div_cancel_left _ he_pos, Nat.div_div_eq_div_mul]
          rw [heq]
    rw [hswap]
    -- Now ∑ d ∈ (f / e).divisors, μ ((f / e) / d) = if f = e then 1 else 0
    have hmob : ∀ f ∈ D.filter (fun f => e ∣ f),
        (∑ d ∈ (f / e).divisors, (μ ((f / e) / d) : ℝ)) * y f =
          if f = e then y e else 0 := by
      intro f hf
      have hfD : f ∈ D := (mem_filter.mp hf).1
      have hef : e ∣ f := (mem_filter.mp hf).2
      have hq_pos : 0 < f / e := Nat.div_pos (Nat.le_of_dvd (hD_pos f hfD) hef) (hD_pos e he)
      have hsum_int : ∑ d ∈ (f / e).divisors, μ ((f / e) / d) = if f / e = 1 then 1 else 0 := by
        have hconv : ∑ d ∈ (f / e).divisors, μ ((f / e) / d) =
            (μ * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) (f / e) := by
          rw [ArithmeticFunction.mul_apply,
            Nat.sum_divisorsAntidiagonal' (f := fun x y => μ x * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) y)]
          refine sum_congr rfl fun d hd => ?_
          have hdne : d ≠ 0 := (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hq_pos).ne'
          simp [ArithmeticFunction.zeta_apply, hdne]
        rw [hconv, ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
      have hsum_real : (∑ d ∈ (f / e).divisors, (μ ((f / e) / d) : ℝ)) =
          if f / e = 1 then 1 else 0 := by
        have : (∑ d ∈ (f / e).divisors, (μ ((f / e) / d) : ℝ)) =
            ((∑ d ∈ (f / e).divisors, μ ((f / e) / d) : ℤ) : ℝ) := by push_cast; rfl
        rw [this, hsum_int]
        split_ifs <;> simp
      rw [hsum_real]
      have hfe_iff : f / e = 1 ↔ f = e := by
        constructor
        · intro h
          have := Nat.mul_div_cancel' hef
          rw [h, mul_one] at this
          exact this.symm
        · intro h
          rw [h]
          exact Nat.div_self (hD_pos e he)
      by_cases hfe : f = e
      · subst hfe
        rw [if_pos (hfe_iff.mpr rfl), if_pos rfl, one_mul]
      · rw [if_neg (mt hfe_iff.mp hfe), if_neg hfe, zero_mul]
    rw [sum_congr rfl hmob, Finset.sum_ite_eq']
    simp [he]
  -- 3. |lam d| ≤ 1 for all d ∈ D
  have hlam_bound : ∀ d ∈ D, |lam d| ≤ 1 := by
    intro d hd
    have hd_sqf : Squarefree d := hD_sqf d hd
    have hd_pos : 0 < d := hD_pos d hd
    have hcop_div : ∀ e ∈ D, d ∣ e → Nat.Coprime d (e / d) := by
      intro e heD hde
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      have hgt : 1 < Nat.gcd d (e / d) := by
        have := Nat.gcd_pos_of_pos_left (e / d) hd_pos; omega
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgt.ne'
      have hpp : p * p ∣ e := by
        have := Nat.mul_dvd_mul (hpd.trans (Nat.gcd_dvd_left _ _))
          (hpd.trans (Nat.gcd_dvd_right _ _))
        rwa [Nat.mul_div_cancel' hde] at this
      exact hp.not_isUnit (hD_sqf e heD p hpp)
    have hsign : ∀ e ∈ D.filter (fun e => d ∣ e),
        (μ (e / d) : ℝ) * y e = (μ d : ℝ) / ((d.totient : ℝ) * S) * (1 / ((e / d).totient : ℝ)) := by
      intro e he
      have heD : e ∈ D := (mem_filter.mp he).1
      have hde : d ∣ e := (mem_filter.mp he).2
      have hcop := hcop_div e heD hde
      have hmu_e : μ e = μ d * μ (e / d) := by
        have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
        rwa [Nat.mul_div_cancel' hde] at this
      have hmu_q2 : (μ (e / d) : ℝ) * (μ (e / d) : ℝ) = 1 := by
        have hsq : Squarefree (e / d) := (hD_sqf e heD).squarefree_of_dvd (Nat.div_dvd_of_dvd hde)
        exact_mod_cast (by rw [← sq]; exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq)
      have hphi_e : (e.totient : ℝ) = (d.totient : ℝ) * ((e / d).totient : ℝ) := by
        have := Nat.totient_mul hcop
        rw [Nat.mul_div_cancel' hde] at this
        exact_mod_cast this
      simp only [y, heD, ↓reduceIte, hmu_e, hphi_e]
      push_cast
      have hd_phi_ne : (d.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hd_pos).ne'
      have hq_phi_ne : ((e / d).totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (Nat.div_pos (Nat.le_of_dvd (hD_pos e heD) hde) hd_pos)).ne'
      calc
        (μ (e / d) : ℝ) * ((μ d : ℝ) * (μ (e / d) : ℝ) / ((d.totient : ℝ) * ((e / d).totient : ℝ) * S))
          = ((μ (e / d) : ℝ) * (μ (e / d) : ℝ)) * (μ d : ℝ) / ((d.totient : ℝ) * ((e / d).totient : ℝ) * S) := by ring
        _ = (μ d : ℝ) / ((d.totient : ℝ) * ((e / d).totient : ℝ) * S) := by rw [hmu_q2, one_mul]
        _ = (μ d : ℝ) / ((d.totient : ℝ) * S) * (1 / ((e / d).totient : ℝ)) := by ring
    have hlam_eq : lam d = (μ d : ℝ) * ((d : ℝ) / (d.totient : ℝ) *
        ∑ e ∈ D.filter (fun e => d ∣ e), (1 : ℝ) / ((e / d).totient : ℝ)) / S := by
      simp only [lam]
      rw [sum_congr rfl hsign, ← mul_sum]
      ring
    rw [hlam_eq, abs_div, abs_of_pos hS_pos, div_le_one hS_pos, abs_mul]
    have hmu_abs : |(μ d : ℝ)| ≤ 1 := by
      have hsq : (μ d : ℝ) * (μ d : ℝ) = 1 := by
        exact_mod_cast (by rw [← sq]; exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree hd_sqf)
      nlinarith [abs_mul_abs_self (μ d : ℝ)]
    have hnn : 0 ≤ (d : ℝ) / (d.totient : ℝ) *
        ∑ e ∈ D.filter (fun e => d ∣ e), (1 : ℝ) / ((e / d).totient : ℝ) := by
      apply mul_nonneg (by positivity)
      exact sum_nonneg fun _ _ => by positivity
    rw [abs_of_nonneg hnn]
    calc
      |(μ d : ℝ)| * ((d : ℝ) / (d.totient : ℝ) *
          ∑ e ∈ D.filter (fun e => d ∣ e), (1 : ℝ) / ((e / d).totient : ℝ))
        ≤ 1 * ((d : ℝ) / (d.totient : ℝ) *
          ∑ e ∈ D.filter (fun e => d ∣ e), (1 : ℝ) / ((e / d).totient : ℝ)) :=
        mul_le_mul_of_nonneg_right hmu_abs hnn
      _ = (∑ u ∈ d.divisors, (1 : ℝ) / (u.totient : ℝ)) *
          (∑ e ∈ D.filter (fun e => d ∣ e), (1 : ℝ) / ((e / d).totient : ℝ)) := by
        rw [one_mul, sum_inv_totient_divisors_of_squarefree d hd_sqf]
      _ ≤ S := by
        rw [sum_mul_sum]
        have hterm_eq : ∀ x ∈ d.divisors ×ˢ D.filter (fun e => d ∣ e),
            (1 : ℝ) / (x.1.totient : ℝ) * ((1 : ℝ) / ((x.2 / d).totient : ℝ)) =
              (1 : ℝ) / ((x.1 * (x.2 / d)).totient : ℝ) := by
          intro ⟨u, e⟩ hx
          simp only [mem_product, mem_filter, Nat.mem_divisors] at hx
          have hcop_u : Nat.Coprime u (e / d) := (hcop_div e hx.2.1 hx.2.2).coprime_dvd_left hx.1.1
          rw [Nat.totient_mul hcop_u]
          push_cast
          ring
        rw [← Finset.sum_product']
        rw [sum_congr rfl hterm_eq]
        have himg : ∑ w ∈ (d.divisors ×ˢ D.filter (fun e => d ∣ e)).image (fun x : ℕ × ℕ => x.1 * (x.2 / d)),
            (1 : ℝ) / (w.totient : ℝ) =
            ∑ x ∈ d.divisors ×ˢ D.filter (fun e => d ∣ e),
              (1 : ℝ) / ((x.1 * (x.2 / d)).totient : ℝ) := by
          apply sum_image
          intro ⟨u₁, e₁⟩ h₁ ⟨u₂, e₂⟩ h₂ heq
          simp only [mem_coe, mem_product, mem_filter, Nat.mem_divisors] at h₁ h₂
          have hg1 : Nat.gcd (u₁ * (e₁ / d)) d = u₁ := by
            rw [Nat.Coprime.gcd_mul_right_cancel u₁ (hcop_div e₁ h₁.2.1 h₁.2.2).symm]
            exact Nat.gcd_eq_left h₁.1.1
          have hg2 : Nat.gcd (u₂ * (e₂ / d)) d = u₂ := by
            rw [Nat.Coprime.gcd_mul_right_cancel u₂ (hcop_div e₂ h₂.2.1 h₂.2.2).symm]
            exact Nat.gcd_eq_left h₂.1.1
          dsimp only at heq
          have hu_eq : u₁ = u₂ := by rw [← hg1, ← hg2, heq]
          subst hu_eq
          have hu_pos : 0 < u₁ := Nat.pos_of_dvd_of_pos h₁.1.1 hd_pos
          have hq_eq : e₁ / d = e₂ / d := Nat.eq_of_mul_eq_mul_left hu_pos heq
          have he_eq : e₁ = e₂ := by
            rw [← Nat.mul_div_cancel' h₁.2.2, ← Nat.mul_div_cancel' h₂.2.2, hq_eq]
          exact Prod.ext rfl he_eq
        rw [← himg]
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro w hw
        rw [mem_image] at hw
        obtain ⟨⟨u, e⟩, hx, rfl⟩ := hw
        simp only [mem_product, mem_filter, Nat.mem_divisors] at hx
        have hdvd_e : u * (e / d) ∣ e := by
          have := Nat.mul_dvd_mul_right hx.1.1 (e / d)
          rwa [Nat.mul_div_cancel' hx.2.2] at this
        exact hD_dvd e hx.2.1 _ hdvd_e
  -- 4. Main quadratic form bound
  have hmain : ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ / ((Nat.lcm d₁ d₂ : ℕ) : ℝ) = 1 / S := by
    have hlcm : ∀ d₁ ∈ D, ∀ d₂ ∈ D,
        lam d₁ * lam d₂ / ((Nat.lcm d₁ d₂ : ℕ) : ℝ) =
          (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ)) *
            ∑ e ∈ D.filter (fun e => e ∣ d₁ ∧ e ∣ d₂), (e.totient : ℝ) := by
      intro d₁ hd₁ d₂ hd₂
      have h1 : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast hD_pos d₁ hd₁
      have h2 : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast hD_pos d₂ hd₂
      have hlcm_pos : (0 : ℝ) < (Nat.lcm d₁ d₂ : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hD_pos d₁ hd₁).ne' (hD_pos d₂ hd₂).ne')
      have hgl : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ) = (d₁ : ℝ) * (d₂ : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d₁ d₂
      have hsum_gcd : ∑ e ∈ D.filter (fun e => e ∣ d₁ ∧ e ∣ d₂), (e.totient : ℝ) =
          ((Nat.gcd d₁ d₂ : ℕ) : ℝ) := by
        have hfilt : D.filter (fun e => e ∣ d₁ ∧ e ∣ d₂) = (Nat.gcd d₁ d₂).divisors := by
          ext e
          simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
          constructor
          · intro h
            exact ⟨h.2, (Nat.gcd_pos_of_pos_left d₂ (hD_pos d₁ hd₁)).ne'⟩
          · intro h
            exact ⟨hD_dvd d₁ hd₁ e h.1.1, h.1⟩
        rw [hfilt]
        exact_mod_cast Nat.sum_totient (Nat.gcd d₁ d₂)
      rw [hsum_gcd]
      field_simp [h1.ne', h2.ne', hlcm_pos.ne']
      linear_combination (lam d₁ * lam d₂) * hgl.symm
    calc
      ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ / ((Nat.lcm d₁ d₂ : ℕ) : ℝ)
        = ∑ d₁ ∈ D, ∑ d₂ ∈ D, ∑ e ∈ D.filter (fun e => e ∣ d₁ ∧ e ∣ d₂),
            (e.totient : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ)) := by
          refine sum_congr rfl fun d₁ hd₁ => sum_congr rfl fun d₂ hd₂ => ?_
          rw [hlcm d₁ hd₁ d₂ hd₂, mul_sum]
          refine sum_congr rfl fun e _ => by ring
      _ = ∑ e ∈ D, (e.totient : ℝ) *
            (∑ d₁ ∈ D.filter (fun d => e ∣ d), lam d₁ / (d₁ : ℝ)) *
            (∑ d₂ ∈ D.filter (fun d => e ∣ d), lam d₂ / (d₂ : ℝ)) := by
          trans ∑ d₁ ∈ D, ∑ d₂ ∈ D, ∑ e ∈ D,
              if e ∣ d₁ ∧ e ∣ d₂ then (e.totient : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ)) else 0
          · refine sum_congr rfl fun d₁ _ => sum_congr rfl fun d₂ _ => ?_
            rw [sum_filter]
          trans ∑ d₁ ∈ D, ∑ e ∈ D, ∑ d₂ ∈ D,
              if e ∣ d₁ ∧ e ∣ d₂ then (e.totient : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ)) else 0
          · refine sum_congr rfl fun d₁ _ => sum_comm
          rw [sum_comm]
          refine sum_congr rfl fun e _ => ?_
          symm
          rw [mul_assoc, sum_mul, mul_sum]
          trans ∑ d₁ ∈ D, if e ∣ d₁ then
              (e.totient : ℝ) * (lam d₁ / (d₁ : ℝ) * ∑ d₂ ∈ D.filter (fun d => e ∣ d), lam d₂ / (d₂ : ℝ)) else 0
          · rw [← sum_filter]
          refine sum_congr rfl fun d₁ _ => ?_
          by_cases h1 : e ∣ d₁
          · rw [if_pos h1, mul_sum, mul_sum, sum_filter]
            refine sum_congr rfl fun d₂ _ => by
              by_cases h2 : e ∣ d₂
              · simp [h1, h2]; ring
              · simp [h1, h2]
          · rw [if_neg h1]
            symm
            exact sum_eq_zero fun d₂ _ => by simp [h1]
      _ = ∑ e ∈ D, (e.totient : ℝ) * y e * y e := by
          refine sum_congr rfl fun e he => by rw [hinv e he]
      _ = 1 / S := by
          have hterm : ∀ e ∈ D, (e.totient : ℝ) * y e * y e =
              (1 : ℝ) / (e.totient : ℝ) / S ^ 2 := by
            intro e he
            simp only [y, he, ↓reduceIte]
            have hmu2 : (μ e : ℝ) * (μ e : ℝ) = 1 := by
              exact_mod_cast (by rw [← sq]; exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hD_sqf e he))
            have hphi_ne : (e.totient : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.totient_pos.mpr (hD_pos e he)).ne'
            field_simp [hphi_ne, hS_pos.ne']
            nlinarith
          rw [sum_congr rfl hterm, ← sum_div]
          show S / S ^ 2 = 1 / S
          field_simp [hS_pos.ne']
  -- 5. Put it together: count ≤ ∑_{t < N} (∑_{d ∈ D, d ∣ a + t*b} lam d)^2
  have hcount :
      (((range N).filter (fun t => ∀ q ∈ Q, ¬ q ∣ a + t * b)).card : ℝ) ≤
        ∑ t ∈ range N, (∑ d ∈ D.filter (fun d => d ∣ a + t * b), lam d) ^ 2 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    rw [sum_filter]
    refine sum_le_sum fun t _ => ?_
    split_ifs with ht
    · have hfilt : D.filter (fun d => d ∣ a + t * b) = {1} := by
        ext d
        simp only [mem_filter, Finset.mem_singleton]
        constructor
        · intro ⟨hdD, hdvd⟩
          by_contra hd1
          have hgt : 1 < d := by have := hD_pos d hdD; omega
          obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgt.ne'
          have hpQ : p ∈ Q := hD_pf d hdD p (Nat.mem_primeFactors.mpr ⟨hp, hpd, (hD_pos d hdD).ne'⟩)
          exact ht p hpQ (hpd.trans hdvd)
        · rintro rfl
          exact ⟨h1D, one_dvd _⟩
      rw [hfilt, Finset.sum_singleton, hlam1]
      norm_num
    · exact sq_nonneg _
  have hexpand :
      ∑ t ∈ range N, (∑ d ∈ D.filter (fun d => d ∣ a + t * b), lam d) ^ 2 =
        ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ *
          (((range N).filter (fun t => Nat.lcm d₁ d₂ ∣ a + t * b)).card : ℝ) := by
    have hsq : ∀ t ∈ range N,
        (∑ d ∈ D.filter (fun d => d ∣ a + t * b), lam d) ^ 2 =
          ∑ d₁ ∈ D, ∑ d₂ ∈ D,
            if Nat.lcm d₁ d₂ ∣ a + t * b then lam d₁ * lam d₂ else 0 := by
      intro t _
      rw [sq, sum_mul]
      simp_rw [mul_sum, sum_filter]
      refine sum_congr rfl fun d₁ _ => ?_
      by_cases h1 : d₁ ∣ a + t * b
      · rw [if_pos h1]
        refine sum_congr rfl fun d₂ _ => ?_
        by_cases h2 : d₂ ∣ a + t * b <;> simp [h1, h2, Nat.lcm_dvd_iff]
      · rw [if_neg h1]
        symm
        exact sum_eq_zero fun d₂ _ => by simp [h1, Nat.lcm_dvd_iff]
    rw [sum_congr rfl hsq]
    rw [sum_comm]
    trans ∑ d₁ ∈ D, ∑ d₂ ∈ D, ∑ t ∈ range N,
        if Nat.lcm d₁ d₂ ∣ a + t * b then lam d₁ * lam d₂ else 0
    · refine sum_congr rfl fun d₁ _ => sum_comm
    refine sum_congr rfl fun d₁ _ => sum_congr rfl fun d₂ _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    ring
  calc
    (((range N).filter (fun t => ∀ q ∈ Q, ¬ q ∣ a + t * b)).card : ℝ)
      ≤ ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ *
          (((range N).filter (fun t => Nat.lcm d₁ d₂ ∣ a + t * b)).card : ℝ) :=
        hcount.trans_eq hexpand
    _ ≤ ∑ d₁ ∈ D, ∑ d₂ ∈ D, (lam d₁ * lam d₂ * ((N : ℝ) / ((Nat.lcm d₁ d₂ : ℕ) : ℝ)) + 1) := by
        refine sum_le_sum fun d₁ hd₁ => sum_le_sum fun d₂ hd₂ => ?_
        have hlcm_pos : 0 < Nat.lcm d₁ d₂ :=
          Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hD_pos d₁ hd₁).ne' (hD_pos d₂ hd₂).ne')
        have hcop_lcm : Nat.Coprime b (Nat.lcm d₁ d₂) := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          have hgt : 1 < Nat.gcd b (Nat.lcm d₁ d₂) := by
            have := Nat.gcd_pos_of_pos_right b hlcm_pos; omega
          obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgt.ne'
          have hpb : p ∣ b := hpd.trans (Nat.gcd_dvd_left _ _)
          have hpl : p ∣ Nat.lcm d₁ d₂ := hpd.trans (Nat.gcd_dvd_right _ _)
          have hp12 : p ∣ d₁ ∨ p ∣ d₂ := hp.prime.dvd_or_dvd (hpl.trans (Nat.lcm_dvd_mul d₁ d₂))
          rcases hp12 with h | h
          · exact hQ_cop p (hD_pf d₁ hd₁ p (Nat.mem_primeFactors.mpr ⟨hp, h, (hD_pos d₁ hd₁).ne'⟩)) hpb
          · exact hQ_cop p (hD_pf d₂ hd₂ p (Nat.mem_primeFactors.mpr ⟨hp, h, (hD_pos d₂ hd₂).ne'⟩)) hpb
        have herr := abs_card_ap_dvd_sub_le N a b (Nat.lcm d₁ d₂) hlcm_pos hcop_lcm
        have hl1 := hlam_bound d₁ hd₁
        have hl2 := hlam_bound d₂ hd₂
        have hdiff : |lam d₁ * lam d₂ *
            ((((range N).filter (fun t => Nat.lcm d₁ d₂ ∣ a + t * b)).card : ℝ) -
              (N : ℝ) / ((Nat.lcm d₁ d₂ : ℕ) : ℝ))| ≤ 1 := by
          rw [abs_mul, abs_mul]
          calc
            |lam d₁| * |lam d₂| *
                |(((range N).filter (fun t => Nat.lcm d₁ d₂ ∣ a + t * b)).card : ℝ) -
                  (N : ℝ) / ((Nat.lcm d₁ d₂ : ℕ) : ℝ)|
              ≤ 1 * 1 * 1 := by gcongr
            _ = 1 := by norm_num
        linarith [(le_abs_self _).trans hdiff]
    _ = (N : ℝ) / S + ((D.card : ℝ) ^ 2) := by
        simp_rw [Finset.sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
        have h1 : ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * ((N : ℝ) / ((Nat.lcm d₁ d₂ : ℕ) : ℝ)) =
            (N : ℝ) / S := by
          calc
            ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ * ((N : ℝ) / ((Nat.lcm d₁ d₂ : ℕ) : ℝ))
              = (N : ℝ) * ∑ d₁ ∈ D, ∑ d₂ ∈ D, lam d₁ * lam d₂ / ((Nat.lcm d₁ d₂ : ℕ) : ℝ) := by
                rw [mul_sum]
                refine sum_congr rfl fun d₁ _ => ?_
                rw [mul_sum]
                refine sum_congr rfl fun d₂ _ => by ring
            _ = (N : ℝ) * (1 / S) := by rw [hmain]
            _ = (N : ℝ) / S := by ring
        rw [h1]
        ring
    _ ≤ (N : ℝ) / S + (Z : ℝ) ^ 2 := by
        gcongr
        have hD_card : D.card ≤ Z := by
          calc D.card ≤ (Icc 1 Z).card := Finset.card_le_card (Finset.filter_subset _ _)
            _ = Z := by simp
        exact_mod_cast hD_card

/- ### Part 3: Chebyshev Prime Estimates -/

private lemma primorial_log_bounds :
    ∀ᶠ z : ℕ in atTop, (z : ℝ) / 2 ≤ log (primorial z) ∧ log (primorial z) ≤ 2 * (z : ℝ) := by
  have hlog2 : (0.69 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hlog4 : log 4 < 2 := by
    have : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; ring
    linarith [log_two_lt_d9]
  have hsqrt : ∀ᶠ z : ℕ in atTop, log ((z : ℝ) + 1) + 2 * sqrt z * log z ≤ 0.19 * (z : ℝ) := by
    have h1 : Tendsto (fun z : ℕ => (log ((z : ℝ) + 1) + 2 * sqrt z * log z) / (z : ℝ))
        atTop (nhds 0) := by
      have ha : Tendsto (fun z : ℕ => log ((z : ℝ) + 1) / (z : ℝ)) atTop (nhds 0) := by
        have h := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)
        have h' := h.tendsto_div_nhds_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
        have hratio : Tendsto (fun z : ℕ => ((z : ℝ) + 1) / (z : ℝ)) atTop (nhds 1) := by
          have := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
          simpa using this.congr' (by
            filter_upwards [eventually_gt_atTop 0] with z hz
            have hz' : (z : ℝ) ≠ 0 := by exact_mod_cast hz.ne'
            simp only [Function.comp_apply]
            field_simp [hz'])
        simpa using (h'.mul hratio).congr' (by
          filter_upwards [eventually_gt_atTop 0] with z hz
          have hz' : (z : ℝ) ≠ 0 := by exact_mod_cast hz.ne'
          have hz1 : (z : ℝ) + 1 ≠ 0 := by positivity
          simp only [Function.comp_apply, Real.rpow_one]
          field_simp [hz', hz1])
      have hb : Tendsto (fun z : ℕ => 2 * sqrt z * log z / (z : ℝ)) atTop (nhds 0) := by
        have h := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
        have h' := (h.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 2
        simpa using h'.congr' (by
          filter_upwards [eventually_gt_atTop 0] with z hz
          have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
          simp only [Function.comp_apply]
          rw [sqrt_eq_rpow]
          have hmul : ((z : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (z : ℝ) := by
            rw [sq, ← rpow_add hzR]; norm_num
          field_simp [hzR.ne', (Real.rpow_pos_of_pos hzR _).ne']
          rw [hmul])
      simpa [add_div] using ha.add hb
    filter_upwards [h1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.19)),
      eventually_gt_atTop 0] with z hz hzp
    have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hzp
    exact (div_lt_iff₀ hzR).mp hz |>.le
  filter_upwards [hsqrt, eventually_ge_atTop 2] with z hz hz2
  have htheta : Chebyshev.theta z = log (primorial z) := by
    simpa [Nat.floor_natCast] using Chebyshev.theta_eq_log_primorial (z : ℝ)
  rw [← htheta]
  constructor
  · have hge := Chebyshev.theta_ge z
    nlinarith
  · have hle := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ (z : ℝ) by positivity)
    nlinarith

private lemma eventually_pi_bounds :
    ∀ᶠ n : ℕ in atTop,
      0.65 * (n : ℝ) / log n ≤ (Nat.primeCounting n : ℝ) ∧
      (Nat.primeCounting n : ℝ) ≤ 1.5 * (n : ℝ) / log n := by
  have hlog2 : (0.69 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hlog4 : log 4 + 0.1 < 1.5 := by
    have : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; ring
    linarith [log_two_lt_d9]
  have hub := tendsto_natCast_atTop_atTop.eventually
    (Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 0.1 by norm_num))
  have hlog_small : ∀ᶠ n : ℕ in atTop, log ((n : ℝ) + 1) ≤ 0.04 * (n : ℝ) := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.02)),
      eventually_ge_atTop 2] with n hn hn2
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : log ((n : ℝ) + 1) < 0.02 * ((n : ℝ) + 1) := by
      simp only [Function.comp_apply, Real.rpow_one] at hn
      exact (div_lt_iff₀ hn1).mp hn
    have : (n : ℝ) ≥ 2 := by exact_mod_cast hn2
    linarith
  filter_upwards [hub, hlog_small, eventually_ge_atTop 3] with n hle hls hn3
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hlog_pos : 0 < log (n : ℝ) := log_pos (by linarith)
  constructor
  · have hge := Chebyshev.pi_ge n
    have hnum : 0.65 * (n : ℝ) ≤ (n : ℝ) * log 2 - log ((n : ℝ) + 1) := by nlinarith
    calc
      0.65 * (n : ℝ) / log n
        ≤ ((n : ℝ) * log 2 - log ((n : ℝ) + 1)) / log n :=
          div_le_div_of_nonneg_right hnum hlog_pos.le
      _ ≤ (Nat.primeCounting n : ℝ) := hge
  · simp only [Nat.floor_natCast] at hle
    calc
      (Nat.primeCounting n : ℝ)
        ≤ (log 4 + 0.1) * (n : ℝ) / log n := hle
      _ ≤ 1.5 * (n : ℝ) / log n := by
          gcongr

private lemma card_primes_Ioc_eq_sub (a b : ℕ) (hab : a ≤ b) :
    ((Ioc a b).filter Nat.Prime).card = Nat.primeCounting b - Nat.primeCounting a := by
  have hcc : ∀ m : ℕ, ((Icc 1 m).filter Nat.Prime).card = Nat.primeCounting m := by
    intro m
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    congr 1
    ext p
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · intro ⟨⟨_, hpm⟩, hp⟩; exact ⟨Nat.lt_succ_of_le hpm, hp⟩
    · intro ⟨hpm, hp⟩; exact ⟨⟨hp.one_le, Nat.lt_succ_iff.mp hpm⟩, hp⟩
  have hsub : (Icc 1 a).filter Nat.Prime ⊆ (Icc 1 b).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hab⟩, hp.2⟩
  have hsdiff : (Ioc a b).filter Nat.Prime =
      (Icc 1 b).filter Nat.Prime \ (Icc 1 a).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_Ioc, Finset.mem_sdiff, mem_Icc]
    constructor
    · intro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨⟨hp.one_le, h2⟩, hp⟩, fun h => by omega⟩
    · intro ⟨⟨⟨_, h2⟩, hp⟩, hnot⟩
      refine ⟨⟨?_, h2⟩, hp⟩
      by_contra hle
      exact hnot ⟨⟨hp.one_le, by omega⟩, hp⟩
  have hadd := Finset.card_sdiff_add_card_eq_card hsub
  rw [← hsdiff, hcc b, hcc a] at hadd
  omega

private lemma primes_in_quarter_ge :
    ∀ᶠ z : ℕ in atTop,
      (z : ℝ) / (10 * log z) ≤ (((Ioc (z / 4) z).filter Nat.Prime).card : ℝ) := by
  have hdiv4 : Tendsto (fun z : ℕ => z / 4) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨4 * b, fun z hz => by omega⟩
  filter_upwards [eventually_pi_bounds, hdiv4.eventually eventually_pi_bounds,
    eventually_ge_atTop 10000] with z ⟨hge_z, _⟩ ⟨_, hle_q⟩ hz10000
  have hq_le : z / 4 ≤ z := Nat.div_le_self z 4
  rw [card_primes_Ioc_eq_sub _ _ hq_le]
  have hmono : Nat.primeCounting (z / 4) ≤ Nat.primeCounting z := Nat.monotone_primeCounting hq_le
  rw [Nat.cast_sub hmono]
  have hzR : (10000 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz10000
  have hlogz : 7 < log (z : ℝ) := by
    have h1 : exp 7 < 10000 := by
      have he : exp 1 < 3 := by linarith [exp_one_lt_d9]
      have h7 : exp 7 = (exp 1) ^ 7 := by rw [← exp_nat_mul]; norm_num
      rw [h7]
      calc (exp 1) ^ 7 < 3 ^ 7 := pow_lt_pow_left₀ he (exp_pos 1).le (by norm_num)
        _ < 10000 := by norm_num
    exact (lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
  have hqR : ((z / 4 : ℕ) : ℝ) ≤ (z : ℝ) / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    exact_mod_cast Nat.div_mul_le_self z 4
  have hqR_ge : (z : ℝ) / 5 ≤ ((z / 4 : ℕ) : ℝ) := by
    have : z ≤ z / 4 * 5 := by omega
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5)]
    exact_mod_cast this
  have hlogq : 0.7 * log (z : ℝ) ≤ log ((z / 4 : ℕ) : ℝ) := by
    have h1 : log ((z : ℝ) / 5) ≤ log ((z / 4 : ℕ) : ℝ) :=
      log_le_log (by positivity) hqR_ge
    rw [log_div (by linarith) (by norm_num)] at h1
    have hlog5 : log 5 < 2.1 := by
      have h2 : log 5 < log 8 := log_lt_log (by norm_num) (by norm_num)
      have h8 : log 8 = 3 * log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; ring
      linarith [log_two_lt_d9]
    linarith
  have hlogq_pos : 0 < log ((z / 4 : ℕ) : ℝ) := by linarith
  have hsub_ub : 1.5 * ((z / 4 : ℕ) : ℝ) / log ((z / 4 : ℕ) : ℝ) ≤
      (1.5 / 2.8) * (z : ℝ) / log (z : ℝ) := by
    have hnum : 1.5 * ((z / 4 : ℕ) : ℝ) ≤ (1.5 / 4) * (z : ℝ) := by linarith
    calc
      1.5 * ((z / 4 : ℕ) : ℝ) / log ((z / 4 : ℕ) : ℝ)
        ≤ ((1.5 / 4) * (z : ℝ)) / (0.7 * log (z : ℝ)) := by
          exact div_le_div₀ (by positivity) hnum (by positivity) hlogq
      _ = (1.5 / 2.8) * (z : ℝ) / log (z : ℝ) := by ring
  have h2 : (z : ℝ) / (10 * log z) = 0.1 * (z : ℝ) / log z := by ring
  rw [h2]
  have hcoeff : (0.1 : ℝ) ≤ 0.65 - 1.5 / 2.8 := by norm_num
  have hpos_term : 0 ≤ (z : ℝ) / log z := by positivity
  calc
    0.1 * (z : ℝ) / log z = 0.1 * ((z : ℝ) / log z) := by ring
    _ ≤ (0.65 - 1.5 / 2.8) * ((z : ℝ) / log z) := mul_le_mul_of_nonneg_right hcoeff hpos_term
    _ = 0.65 * (z : ℝ) / log z - (1.5 / 2.8) * (z : ℝ) / log z := by ring
    _ ≤ (Nat.primeCounting z : ℝ) - (Nat.primeCounting (z / 4) : ℝ) := by linarith

private lemma harmonic_sum_le_one_add_log (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Icc 1 K, (1 : ℝ) / (k : ℝ) ≤ 1 + log (K : ℝ) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ log ((m + 1 : ℕ) : ℝ) - log (m : ℝ) := by
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      rw [← log_div hm1_pos.ne' hm_pos.ne']
      have h1 : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) = 1 - (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        push_cast; field_simp [hm1_pos.ne']; ring
      rw [h1]
      have h2 := add_one_le_exp (-((1 : ℝ) - (m : ℝ) / ((m + 1 : ℕ) : ℝ)))
      have h3 : -((1 : ℝ) - (m : ℝ) / ((m + 1 : ℕ) : ℝ)) + 1 = (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by ring
      rw [h3] at h2
      have h4 := log_le_log (by positivity) h2
      rw [log_exp, log_div hm_pos.ne' hm1_pos.ne'] at h4
      rw [log_div hm1_pos.ne' hm_pos.ne']
      linarith
    linarith

private lemma harmonic_sum_ge_log_ratio (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    log ((b : ℝ) / (a : ℝ)) ≤ ∑ k ∈ Ico a b, (1 : ℝ) / (k : ℝ) := by
  induction b, hab using Nat.le_induction with
  | base =>
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    simp [div_self ha_pos.ne']
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (ha.trans hm)
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hstep : log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ≤ (1 : ℝ) / (m : ℝ) := by
      have h1 : ((m + 1 : ℕ) : ℝ) / (m : ℝ) = 1 / (m : ℝ) + 1 := by
        push_cast; field_simp [hm_pos.ne']; ring
      rw [h1]
      have := log_le_log (by positivity) (add_one_le_exp ((1 : ℝ) / (m : ℝ)))
      rwa [log_exp] at this
    have hsplit : log (((m + 1 : ℕ) : ℝ) / (a : ℝ)) =
        log ((m : ℝ) / (a : ℝ)) + log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
      rw [← log_mul (by positivity) (by positivity)]
      congr 1
      field_simp [hm_pos.ne', ha_pos.ne']
    linarith

private lemma sum_inv_primes_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 4 ≤ z →
      ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
        5 * log (log (z : ℝ)) + C := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_pi_bounds
  let k₀ := max 2 (Nat.log 2 N₀ + 1)
  let C₀ := ∑ p ∈ (Icc 1 (2 ^ k₀)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
  refine ⟨C₀ + 20, by positivity, fun z hz => ?_⟩
  by_cases hzk : z ≤ 2 ^ k₀
  · have hsub : (Icc 1 z).filter Nat.Prime ⊆ (Icc 1 (2 ^ k₀)).filter Nat.Prime :=
      Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hzk)
    have h1 : ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ C₀ :=
      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    have hlogz : 1 ≤ log (z : ℝ) := by
      have h4 : exp 1 ≤ 4 := by linarith [exp_one_lt_d9]
      exact (Real.le_log_iff_exp_le (by positivity)).mpr (h4.trans (by exact_mod_cast hz))
    have hll : 0 ≤ log (log (z : ℝ)) := log_nonneg hlogz
    linarith
  · push Not at hzk
    let K := Nat.log 2 z + 1
    have hK_ge : k₀ ≤ K := by
      have : k₀ ≤ Nat.log 2 z := Nat.le_log_of_pow_le (by norm_num) hzk.le
      exact Nat.le_succ_of_le this
    have hcover : (Icc 1 z).filter Nat.Prime ⊆
        (Icc 1 (2 ^ k₀)).filter Nat.Prime ∪
          (Ico k₀ K).biUnion (fun k => (Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime) := by
      intro p hp
      simp only [mem_filter, mem_Icc] at hp
      by_cases hpk : p ≤ 2 ^ k₀
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.1.1, hpk⟩, hp.2⟩)
      · push Not at hpk
        refine mem_union_right _ (mem_biUnion.mpr ?_)
        let k := Nat.log 2 (p - 1)
        have hp_gt : 2 ^ k < p := by
          have hp2 : 2 ≤ p := hp.2.two_le
          have h1 : 2 ^ k ≤ p - 1 := Nat.pow_log_le_self 2 (by omega)
          omega
        have hp_le : p ≤ 2 ^ (k + 1) := by
          have h1 : p - 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (p - 1)
          omega
        have hk_ge : k₀ ≤ k := by
          have : 2 ^ k₀ ≤ p - 1 := by omega
          exact Nat.le_log_of_pow_le (by norm_num) this
        have hk_lt : k < K := by
          have hpm : p - 1 ≤ z := by omega
          have hlogm : k ≤ Nat.log 2 z := Nat.log_mono_right hpm
          exact Nat.lt_succ_of_le hlogm
        exact ⟨k, mem_Ico.mpr ⟨hk_ge, hk_lt⟩,
          mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp_gt, hp_le⟩, hp.2⟩⟩
    have hsum_union_le : ∀ s t : Finset ℕ,
        ∑ p ∈ s ∪ t, (1 : ℝ) / (p : ℝ) ≤ ∑ p ∈ s, (1 : ℝ) / (p : ℝ) + ∑ p ∈ t, (1 : ℝ) / (p : ℝ) := by
      intro s t
      have := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := fun p : ℕ => (1 : ℝ) / (p : ℝ))
      have hnn : 0 ≤ ∑ p ∈ s ∩ t, (1 : ℝ) / (p : ℝ) := sum_nonneg fun _ _ => by positivity
      linarith
    have hsum_biUnion_le : ∀ (s : Finset ℕ) (f : ℕ → Finset ℕ),
        ∑ p ∈ s.biUnion f, (1 : ℝ) / (p : ℝ) ≤ ∑ k ∈ s, ∑ p ∈ f k, (1 : ℝ) / (p : ℝ) := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.biUnion_insert, Finset.sum_insert ha]
        exact (hsum_union_le _ _).trans (add_le_add le_rfl ih)
    have hsum_le : ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
        C₀ + ∑ k ∈ Ico k₀ K,
          ∑ p ∈ (Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
      calc
        ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
          ≤ ∑ p ∈ (Icc 1 (2 ^ k₀)).filter Nat.Prime ∪
              (Ico k₀ K).biUnion (fun k => (Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime),
              (1 : ℝ) / (p : ℝ) :=
            sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by positivity
        _ ≤ C₀ + ∑ p ∈ (Ico k₀ K).biUnion
              (fun k => (Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime), (1 : ℝ) / (p : ℝ) :=
            hsum_union_le _ _
        _ ≤ C₀ + ∑ k ∈ Ico k₀ K,
              ∑ p ∈ (Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
            gcongr
            exact hsum_biUnion_le _ _
    have hblock : ∀ k ∈ Ico k₀ K,
        ∑ p ∈ (Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
          5 / ((k + 1 : ℕ) : ℝ) := by
      intro k hk
      rw [mem_Ico] at hk
      have hk_ge_N : N₀ ≤ 2 ^ (k + 1) := by
        have h1 : Nat.log 2 N₀ < k + 1 := by omega
        exact (Nat.lt_pow_succ_log_self (by norm_num) N₀).le.trans
          (Nat.pow_le_pow_right (by norm_num) h1)
      have hpi_ub := (hN₀ (2 ^ (k + 1)) hk_ge_N).2
      have hcard_le : (((Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime).card : ℝ) ≤
          (Nat.primeCounting (2 ^ (k + 1)) : ℝ) := by
        rw [card_primes_Ioc_eq_sub _ _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))]
        exact_mod_cast Nat.sub_le _ _
      have hterm : ∑ p ∈ (Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
          (((Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime).card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
        rw [div_eq_mul_inv, ← nsmul_eq_mul, ← sum_const]
        refine sum_le_sum fun p hp => ?_
        have hgt : 2 ^ k < p := (mem_Ioc.mp (mem_filter.mp hp).1).1
        rw [one_div]
        exact inv_anti₀ (by positivity) (by exact_mod_cast hgt.le)
      have hlog2 : (0.69 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
      calc
        ∑ p ∈ (Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
          ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) :=
            hterm.trans (div_le_div_of_nonneg_right hcard_le (by positivity))
        _ ≤ (1.5 * ((2 ^ (k + 1) : ℕ) : ℝ) / log ((2 ^ (k + 1) : ℕ) : ℝ)) / ((2 ^ k : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right hpi_ub (by positivity)
        _ = 3 / (((k + 1 : ℕ) : ℝ) * log 2) := by
            rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, log_pow, pow_succ]
            have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
            have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            field_simp [h2k, hk1, (show log 2 ≠ 0 by linarith)]
            ring
        _ ≤ 5 / ((k + 1 : ℕ) : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
            nlinarith
    have hsum_k : ∑ k ∈ Ico k₀ K, (5 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤
        5 * (1 + log (K : ℝ)) := by
      calc
        ∑ k ∈ Ico k₀ K, (5 : ℝ) / ((k + 1 : ℕ) : ℝ)
          = 5 * ∑ k ∈ Ico k₀ K, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
            rw [mul_sum]; refine sum_congr rfl fun _ _ => by ring
        _ = 5 * ∑ j ∈ Icc (k₀ + 1) K, (1 : ℝ) / (j : ℝ) := by
            congr 1
            refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
            · intro k hk; rw [mem_Ico] at hk; rw [mem_Icc]; omega
            · intro k₁ _ k₂ _ h; omega
            · intro j hj; rw [mem_Icc] at hj
              exact ⟨j - 1, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
            · intro _ _; rfl
        _ ≤ 5 * ∑ j ∈ Icc 1 K, (1 : ℝ) / (j : ℝ) := by
            exact mul_le_mul_of_nonneg_left
              (sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left (by omega))
                fun _ _ _ => by positivity) (by norm_num)
        _ ≤ 5 * (1 + log (K : ℝ)) := by
            exact mul_le_mul_of_nonneg_left (harmonic_sum_le_one_add_log K (by omega)) (by norm_num)
    have hlogK : log (K : ℝ) ≤ log (log (z : ℝ)) + 2 := by
      have hpow : (2 : ℝ) ^ (Nat.log 2 z) ≤ (z : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have hlog_pow := log_le_log (by positivity) hpow
      rw [log_pow] at hlog_pow
      have hlog2 : (0.69 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
      have hK_le : (K : ℝ) ≤ 3 * log (z : ℝ) := by
        have hlogz_ge : 1 ≤ log (z : ℝ) := by
          have h4 : exp 1 ≤ 4 := by linarith [exp_one_lt_d9]
          exact (Real.le_log_iff_exp_le (by positivity)).mpr (h4.trans (by exact_mod_cast hz))
        have hKeq : (K : ℝ) = (Nat.log 2 z : ℝ) + 1 := by simp [K]
        nlinarith
      have hlogz_pos : 0 < log (z : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < z))
      calc
        log (K : ℝ) ≤ log (3 * log (z : ℝ)) :=
          log_le_log (by positivity) hK_le
        _ = log 3 + log (log (z : ℝ)) :=
          log_mul (by norm_num) hlogz_pos.ne'
        _ ≤ log (log (z : ℝ)) + 2 := by
          have : log 3 < 2 := by
            have : log 3 < log 4 := log_lt_log (by norm_num) (by norm_num)
            have h4 : log 4 = 2 * log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; ring
            linarith [log_two_lt_d9]
          linarith
    have hsum_final := hsum_le.trans (add_le_add le_rfl ((sum_le_sum hblock).trans hsum_k))
    linarith

private lemma sum_inv_primes_Ioc_tendsto :
    Tendsto (fun z : ℕ =>
      ∑ p ∈ (Ioc ⌊(log (z : ℝ)) ^ 12⌋₊ ⌊exp (sqrt (log (z : ℝ)))⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) atTop atTop := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_pi_bounds
  let k₀ := max 4 (Nat.log 4 N₀ + 1)
  have hlog4_pos : 0 < log 4 := log_pos (by norm_num)
  have hlog4_ge1 : 1 ≤ log 4 := (le_log_iff_exp_le (by norm_num)).mpr (by linarith [exp_one_lt_d9])
  have hlog4_lt : log 4 < 1.45 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; linarith [log_two_lt_d9]
  have hblock : ∀ k : ℕ, k₀ ≤ k →
      (1 : ℝ) / (8 * ((k + 1 : ℕ) : ℝ)) ≤
        ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    intro k hk
    have hk1_ge : N₀ ≤ 4 ^ k :=
      (Nat.lt_pow_succ_log_self (by norm_num) N₀).le.trans
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hk2_ge : N₀ ≤ 4 ^ (k + 1) := hk1_ge.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
    have hge := (hN₀ (4 ^ (k + 1)) hk2_ge).1
    have hle := (hN₀ (4 ^ k) hk1_ge).2
    have hcard : (((Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime).card : ℝ) =
        (Nat.primeCounting (4 ^ (k + 1)) : ℝ) - (Nat.primeCounting (4 ^ k) : ℝ) := by
      rw [card_primes_Ioc_eq_sub _ _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))]
      exact Nat.cast_sub (Nat.monotone_primeCounting (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)))
    have hsum_ge :
        (((Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime).card : ℝ) / ((4 ^ (k + 1) : ℕ) : ℝ) ≤
          ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
      rw [div_eq_mul_inv, ← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum fun p hp => ?_
      rw [one_div]
      exact inv_anti₀ (by exact_mod_cast (mem_filter.mp hp).2.pos)
        (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2)
    have hdiff_ge : (0.5 : ℝ) * ((4 ^ k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) ≤
        (Nat.primeCounting (4 ^ (k + 1)) : ℝ) - (Nat.primeCounting (4 ^ k) : ℝ) := by
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hk_ge4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 4 ≤ k)
      have h1 : 0.65 * ((4 ^ (k + 1) : ℕ) : ℝ) / log ((4 ^ (k + 1) : ℕ) : ℝ) =
          2.6 * ((4 ^ k : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * log 4) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, log_pow, pow_succ]; ring
      have h2 : 1.5 * ((4 ^ k : ℕ) : ℝ) / log ((4 ^ k : ℕ) : ℝ) =
          (1.5 / (k : ℝ)) * (((4 ^ k : ℕ) : ℝ) / log 4) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, log_pow]; ring
      have h3 : 1.5 / (k : ℝ) ≤ 1.875 / ((k + 1 : ℕ) : ℝ) := by
        rw [div_le_div_iff₀ hk_pos hk1_pos]; push_cast; linarith
      have h4 : (1.5 / (k : ℝ)) * (((4 ^ k : ℕ) : ℝ) / log 4) ≤
          1.875 * ((4 ^ k : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * log 4) := by
        calc (1.5 / (k : ℝ)) * (((4 ^ k : ℕ) : ℝ) / log 4)
            ≤ (1.875 / ((k + 1 : ℕ) : ℝ)) * (((4 ^ k : ℕ) : ℝ) / log 4) :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = 1.875 * ((4 ^ k : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * log 4) := by ring
      have h5 : (0.5 : ℝ) * ((4 ^ k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) ≤
          0.725 * ((4 ^ k : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * log 4) := by
        rw [div_le_div_iff₀ hk1_pos (by positivity)]
        nlinarith [mul_pos (show (0 : ℝ) < ((4 ^ k : ℕ) : ℝ) by positivity) hk1_pos]
      have h6 : 2.6 * ((4 ^ k : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * log 4) -
          1.875 * ((4 ^ k : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * log 4) =
          0.725 * ((4 ^ k : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) * log 4) := by ring
      linarith
    calc (1 : ℝ) / (8 * ((k + 1 : ℕ) : ℝ))
        = (0.5 * ((4 ^ k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) / ((4 ^ (k + 1) : ℕ) : ℝ) := by
          push_cast; rw [pow_succ]; field_simp [pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0)]; ring
      _ ≤ (((Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime).card : ℝ) / ((4 ^ (k + 1) : ℕ) : ℝ) := by
          rw [hcard]; exact div_le_div_of_nonneg_right hdiff_ge (by positivity)
      _ ≤ _ := hsum_ge
  rw [tendsto_atTop_atTop]
  intro M
  have hratio : Tendsto (fun z : ℕ =>
      sqrt (log (z : ℝ)) / (12 * log (log (z : ℝ)) + 2)) atTop atTop := by
    have hcore : Tendsto (fun t : ℝ => sqrt t / (12 * log t + 2)) atTop atTop := by
      have hinv : Tendsto (fun t : ℝ => (12 * log t + 2) / sqrt t) atTop (nhds 0) := by
        have h1 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero.const_mul 12
        have h2 : Tendsto (fun t : ℝ => (2 : ℝ) / sqrt t) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop
            ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr fun t => by rw [sqrt_eq_rpow])
        simpa using (h1.add h2).congr' (by
          filter_upwards [eventually_gt_atTop 0] with t _; rw [sqrt_eq_rpow]; ring)
      have hpos : ∀ᶠ t : ℝ in atTop, 0 < (12 * log t + 2) / sqrt t := by
        filter_upwards [eventually_gt_atTop (exp 1)] with t ht
        have hlt : 1 < log t := (lt_log_iff_exp_lt (by linarith [exp_pos 1])).mpr ht
        have : 0 < sqrt t := sqrt_pos.mpr (by linarith [exp_pos 1])
        positivity
      exact (Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hinv hpos)).congr
        fun t => by simp [inv_div]
    exact hcore.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  let K := ((k₀ : ℝ) + 1) * exp (8 * max M 0 + 4) * (2 * log 4)
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp ((hratio.eventually_ge_atTop K).and (eventually_ge_atTop 100))
  refine ⟨Z₀, fun z hz => ?_⟩
  obtain ⟨hbig, hz100⟩ := hZ₀ z hz
  let A := ⌊(log (z : ℝ)) ^ 12⌋₊
  let y := ⌊exp (sqrt (log (z : ℝ)))⌋₊
  let J₁ := max k₀ (Nat.log 4 A + 1)
  let J₂ := Nat.log 4 y
  have hz100R : (100 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz100
  have hlogz_pos : 1 < log (z : ℝ) :=
    (lt_log_iff_exp_lt (by positivity)).mpr (by linarith [exp_one_lt_d9])
  have hll_nn : 0 ≤ log (log (z : ℝ)) := log_nonneg hlogz_pos.le
  have hden_pos : 0 < 12 * log (log (z : ℝ)) + 2 := by positivity
  have hsqrt_ge : K * (12 * log (log (z : ℝ)) + 2) ≤ sqrt (log (z : ℝ)) := (le_div_iff₀ hden_pos).mp hbig
  have hJ₁_le : ((J₁ + 1 : ℕ) : ℝ) ≤ max ((k₀ : ℝ) + 1) (12 * log (log (z : ℝ)) / log 4 + 2) := by
    have hlogA : (Nat.log 4 A : ℝ) ≤ 12 * log (log (z : ℝ)) / log 4 := by
      by_cases hA0 : A = 0
      · simp [hA0]; positivity
      · have h1 := log_le_log (by positivity)
          ((by exact_mod_cast Nat.pow_log_le_self 4 hA0 : (4 : ℝ) ^ Nat.log 4 A ≤ A).trans (Nat.floor_le (by positivity)))
        rw [log_pow, log_pow] at h1
        exact (le_div_iff₀ hlog4_pos).mpr h1
    dsimp [J₁]
    rcases le_total k₀ (Nat.log 4 A + 1) with h | h
    · rw [Nat.max_eq_right h]; push_cast; exact le_max_of_le_right (by linarith)
    · rw [Nat.max_eq_left h]; push_cast; exact le_max_left _ _
  have hJ₂_ge : sqrt (log (z : ℝ)) / log 4 - 2 ≤ (J₂ : ℝ) := by
    have h2sq : (2 : ℝ) ≤ exp (sqrt (log (z : ℝ))) :=
      (by linarith [add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ exp 1).trans
        (exp_le_exp.mpr ((le_sqrt (by norm_num) (by linarith)).mpr (by linarith)))
    have hy_pos : 1 ≤ y := Nat.le_floor (by push_cast; linarith)
    have hlog_lt := log_lt_log (by exact_mod_cast hy_pos)
      (by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) y : (y : ℝ) < 4 ^ (J₂ + 1))
    have hlog_ge := log_le_log (by positivity)
      (show exp (sqrt (log (z : ℝ))) / 2 ≤ (y : ℝ) by linarith [Nat.sub_one_lt_floor (exp (sqrt (log (z : ℝ))))])
    rw [log_pow] at hlog_lt
    rw [log_div (exp_pos _).ne' (by norm_num), log_exp] at hlog_ge
    have : log 2 < log 4 := log_lt_log (by norm_num) (by norm_num)
    have hlt2 : sqrt (log (z : ℝ)) - log 4 < ((J₂ + 1 : ℕ) : ℝ) * log 4 := by linarith
    push_cast at hlt2
    rw [sub_le_iff_le_add, div_le_iff₀ hlog4_pos]; nlinarith
  have he8_ge4 : (4 : ℝ) ≤ exp (8 * max M 0 + 4) := by
    have : (4 : ℝ) ≤ exp 4 := by linarith [add_one_le_exp (4 : ℝ)]
    exact this.trans (exp_le_exp.mpr (by linarith [le_max_right M 0]))
  have hJ2_half : sqrt (log (z : ℝ)) / (2 * log 4) ≤ (J₂ : ℝ) := by
    have hk01 : (1 : ℝ) ≤ (k₀ : ℝ) + 1 := by exact_mod_cast (by omega : 1 ≤ k₀ + 1)
    have hK_ge : 2 * log 4 * 2 ≤ K := by
      have h1 : 4 * (2 * log 4) ≤ ((k₀ : ℝ) + 1) * exp (8 * max M 0 + 4) * (2 * log 4) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      dsimp [K]; linarith
    have hsq2 : 2 * (2 * log 4) ≤ sqrt (log (z : ℝ)) := by nlinarith
    have h1 : sqrt (log (z : ℝ)) / log 4 = 2 * (sqrt (log (z : ℝ)) / (2 * log 4)) := by ring
    linarith [show 2 ≤ sqrt (log (z : ℝ)) / (2 * log 4) from (le_div_iff₀ (by positivity)).mpr (by linarith)]
  have hratio_ge : exp (8 * max M 0) ≤ ((J₂ + 1 : ℕ) : ℝ) / ((J₁ + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    have he_le : exp (8 * max M 0) ≤ exp (8 * max M 0 + 4) := exp_le_exp.mpr (by linarith)
    have hJ2_gt : sqrt (log (z : ℝ)) / (2 * log 4) ≤ ((J₂ + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hk01 : (1 : ℝ) ≤ (k₀ : ℝ) + 1 := by exact_mod_cast (by omega : 1 ≤ k₀ + 1)
    rcases max_choice ((k₀ : ℝ) + 1) (12 * log (log (z : ℝ)) / log 4 + 2) with hmax | hmax
    · rw [hmax] at hJ₁_le
      have h1 : ((k₀ : ℝ) + 1) * exp (8 * max M 0 + 4) ≤ sqrt (log (z : ℝ)) / (2 * log 4) := by
        rw [le_div_iff₀ (by positivity)]
        have h2 : (1 : ℝ) ≤ 12 * log (log (z : ℝ)) + 2 := by linarith
        have hmul : ((k₀ : ℝ) + 1) * exp (8 * max M 0 + 4) * (2 * log 4) ≤
            K * (12 * log (log (z : ℝ)) + 2) := by
          dsimp [K]; exact le_mul_of_one_le_right (by positivity) h2
        linarith
      nlinarith [exp_pos (8 * max M 0)]
    · rw [hmax] at hJ₁_le
      have hdiv : 12 * log (log (z : ℝ)) / log 4 + 2 ≤ 12 * log (log (z : ℝ)) + 2 := by
        linarith [div_le_self (by positivity : 0 ≤ 12 * log (log (z : ℝ))) hlog4_ge1]
      have h1 : (12 * log (log (z : ℝ)) + 2) * exp (8 * max M 0 + 4) ≤ sqrt (log (z : ℝ)) / (2 * log 4) := by
        rw [le_div_iff₀ (by positivity)]
        have hmul : (12 * log (log (z : ℝ)) + 2) * exp (8 * max M 0 + 4) * (2 * log 4) ≤
            K * (12 * log (log (z : ℝ)) + 2) := by
          dsimp [K]
          have : 0 ≤ exp (8 * max M 0 + 4) * (2 * log 4) * (12 * log (log (z : ℝ)) + 2) := by positivity
          nlinarith
        linarith
      nlinarith [exp_pos (8 * max M 0)]
  have hJ_lt : J₁ ≤ J₂ := by
    have h1 : (1 : ℝ) ≤ exp (8 * max M 0) := one_le_exp (by positivity)
    have h2 : ((J₁ + 1 : ℕ) : ℝ) ≤ ((J₂ + 1 : ℕ) : ℝ) := by
      nlinarith [(le_div_iff₀ (by positivity : (0 : ℝ) < ((J₁ + 1 : ℕ) : ℝ))).mp (h1.trans hratio_ge)]
    exact Nat.le_of_lt_succ (by exact_mod_cast h2)
  have hsub : (Ico J₁ J₂).biUnion (fun k => (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime) ⊆
      (Ioc A y).filter Nat.Prime := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := mem_biUnion.mp hp
    rw [mem_Ico] at hk; rw [mem_filter, mem_Ioc] at hpk ⊢
    refine ⟨⟨?_, ?_⟩, hpk.2⟩
    · exact ((Nat.lt_pow_succ_log_self (by norm_num) A).trans_le
        (Nat.pow_le_pow_right (by norm_num) (le_trans (le_max_right _ _) hk.1))).trans hpk.1.1
    · have hy_pos : 1 ≤ y := Nat.le_floor (by simp [one_le_exp (sqrt_nonneg (log (z : ℝ)))])
      have hy_ne : y ≠ 0 := by omega
      exact hpk.1.2.trans ((Nat.pow_le_pow_right (by norm_num) hk.2).trans (Nat.pow_log_le_self 4 hy_ne))
  have hdisj : Set.PairwiseDisjoint (↑(Ico J₁ J₂) : Set ℕ)
      (fun k => (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime) := by
    intro k₁ _ k₂ _ hne
    change Disjoint _ _; rw [disjoint_left]
    intro p hp1 hp2
    rw [mem_filter, mem_Ioc] at hp1 hp2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) hlt; omega
    · have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) hlt; omega
  have hsum_ge :
      ∑ k ∈ Ico J₁ J₂, (1 : ℝ) / (8 * ((k + 1 : ℕ) : ℝ)) ≤
        ∑ p ∈ (Ioc A y).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
    calc ∑ k ∈ Ico J₁ J₂, (1 : ℝ) / (8 * ((k + 1 : ℕ) : ℝ))
        ≤ ∑ k ∈ Ico J₁ J₂, ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
          sum_le_sum fun k hk => hblock k ((le_max_left _ _).trans (mem_Ico.mp hk).1)
      _ = ∑ p ∈ (Ico J₁ J₂).biUnion (fun k => (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime), (1 : ℝ) / (p : ℝ) :=
          (sum_biUnion hdisj).symm
      _ ≤ ∑ p ∈ (Ioc A y).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hharm : (1 : ℝ) / 8 * log (((J₂ + 1 : ℕ) : ℝ) / ((J₁ + 1 : ℕ) : ℝ)) ≤
      ∑ k ∈ Ico J₁ J₂, (1 : ℝ) / (8 * ((k + 1 : ℕ) : ℝ)) := by
    have hshift : ∑ k ∈ Ico J₁ J₂, (1 : ℝ) / (8 * ((k + 1 : ℕ) : ℝ)) =
        (1 : ℝ) / 8 * ∑ j ∈ Ico (J₁ + 1) (J₂ + 1), (1 : ℝ) / (j : ℝ) := by
      rw [mul_sum]
      refine sum_bij (fun k _ => k + 1) (fun k hk => by rw [mem_Ico] at hk ⊢; omega)
        (fun _ _ _ _ h => by omega) (fun j hj => by rw [mem_Ico] at hj; exact ⟨j - 1, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩)
        (fun _ _ => by ring)
    rw [hshift]; gcongr
    exact harmonic_sum_ge_log_ratio (J₁ + 1) (J₂ + 1) (by omega) (by omega)
  have hlog_ge : M ≤ (1 : ℝ) / 8 * log (((J₂ + 1 : ℕ) : ℝ) / ((J₁ + 1 : ℕ) : ℝ)) := by
    have hln := log_le_log (exp_pos _) hratio_ge
    rw [log_exp] at hln; linarith [le_max_left M 0]
  exact hlog_ge.trans (hharm.trans hsum_ge)

/- ### Part 4: Smooth Numbers, Selberg S Lower Bound, Greedy Sieving, and CRT -/

private lemma geom_sum_le_inv_one_sub (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (E : ℕ) :
    ∑ e ∈ range (E + 1), r ^ e ≤ (1 - r)⁻¹ := by
  have h1 : 1 - r ≠ 0 := by linarith
  have hpos : 0 < 1 - r := by linarith
  have hsum : (1 - r) * ∑ e ∈ range (E + 1), r ^ e = 1 - r ^ (E + 1) := by
    have := mul_geom_sum r (E + 1)
    linarith [show (r - 1) * ∑ e ∈ range (E + 1), r ^ e =
      -((1 - r) * ∑ e ∈ range (E + 1), r ^ e) by ring]
  rw [inv_eq_one_div, le_div_iff₀ hpos, mul_comm, hsum]
  have : 0 ≤ r ^ (E + 1) := pow_nonneg hr0 _
  linarith

private lemma sum_smooth_rpow_le (M : ℕ) (S : Finset ℕ) (α : ℝ)
    (hS : ∀ p ∈ S, p.Prime) (hα : 0 < α) :
    ∑ m ∈ (Icc 1 M).filter (fun m => ∀ p ∈ m.primeFactors, p ∈ S), (m : ℝ) ^ (-α) ≤
      ∏ p ∈ S, (1 - (p : ℝ) ^ (-α))⁻¹ := by
  let E := Nat.log 2 M + 1
  -- Induction on S: for any S' of primes, ∑_{m ∈ Icc 1 M, pf ⊆ S'} m^(-α) ≤ ∏_{p ∈ S'} ∑_{e ≤ E} p^(-α*e)
  have hmain : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) →
      ∑ m ∈ (Icc 1 M).filter (fun m => ∀ p ∈ m.primeFactors, p ∈ T), (m : ℝ) ^ (-α) ≤
        ∏ p ∈ T, ∑ e ∈ range (E + 1), ((p : ℝ) ^ (-α)) ^ e := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.prod_empty]
      have hsub : (Icc 1 M).filter (fun m => ∀ p ∈ m.primeFactors, p ∈ (∅ : Finset ℕ)) ⊆ {1} := by
        intro m hm
        simp only [mem_filter, mem_Icc, Finset.notMem_empty, imp_false] at hm
        rw [Finset.mem_singleton]
        by_contra hm1
        have hgt : 1 < m := by omega
        obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hgt.ne'
        exact hm.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpm, by omega⟩)
      calc
        ∑ m ∈ (Icc 1 M).filter (fun m => ∀ p ∈ m.primeFactors, p ∈ (∅ : Finset ℕ)), (m : ℝ) ^ (-α)
          ≤ ∑ m ∈ ({1} : Finset ℕ), (m : ℝ) ^ (-α) :=
            sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = 1 := by simp
    | insert q T hqT ih =>
      intro hT
      have hq_prime : q.Prime := hT q (mem_insert_self q T)
      have hT_prime : ∀ p ∈ T, p.Prime := fun p hp => hT p (mem_insert_of_mem hp)
      rw [Finset.prod_insert hqT]
      let A := (Icc 1 M).filter (fun m => ∀ p ∈ m.primeFactors, p ∈ insert q T)
      let B := (Icc 1 M).filter (fun m => ∀ p ∈ m.primeFactors, p ∈ T)
      -- Each m ∈ A factors uniquely as q^e * u where e = m.factorization q ≤ E and u ∈ B
      have hsub : A ⊆ (range (E + 1) ×ˢ B).image (fun x : ℕ × ℕ => q ^ x.1 * x.2) := by
        intro m hm
        simp only [A, mem_filter, mem_Icc] at hm
        let e := m.factorization q
        have hpow_dvd : q ^ e ∣ m := Nat.ordProj_dvd m q
        let u := m / q ^ e
        have hm_eq : q ^ e * u = m := Nat.mul_div_cancel' hpow_dvd
        have he_le : e ≤ E := by
          have h2 : 2 ^ e ≤ q ^ e := Nat.pow_le_pow_left hq_prime.two_le e
          have hqM : q ^ e ≤ M := (Nat.le_of_dvd (by omega) hpow_dvd).trans hm.1.2
          have h2M : 2 ^ e ≤ M := h2.trans hqM
          have : e ≤ Nat.log 2 M := Nat.le_log_of_pow_le (by norm_num) h2M
          omega
        have hu_mem : u ∈ B := by
          simp only [B, mem_filter, mem_Icc]
          have hu_pos : 0 < u := Nat.div_pos (Nat.le_of_dvd (by omega) hpow_dvd) (pow_pos hq_prime.pos e)
          have hu_le : u ≤ M := (Nat.div_le_self m _).trans hm.1.2
          refine ⟨⟨hu_pos, hu_le⟩, fun p hp => ?_⟩
          have hp_m : p ∈ m.primeFactors := Nat.primeFactors_mono (Nat.div_dvd_of_dvd hpow_dvd) (by omega) hp
          have hp_ins := hm.2 p hp_m
          rw [Finset.mem_insert] at hp_ins
          rcases hp_ins with hpq | hpT
          · exfalso
            have hqu : q ∣ u := hpq ▸ Nat.dvd_of_mem_primeFactors hp
            have hqe1 : q ^ (e + 1) ∣ m := by
              rw [pow_succ, ← hm_eq]
              exact Nat.mul_dvd_mul_left (q ^ e) hqu
            have hle_e := (hq_prime.pow_dvd_iff_le_factorization (by omega)).mp hqe1
            omega
          · exact hpT
        exact mem_image.mpr ⟨(e, u), mem_product.mpr ⟨mem_range.mpr (by omega), hu_mem⟩, hm_eq⟩
      have hsum_img :
          ∑ m ∈ (range (E + 1) ×ˢ B).image (fun x : ℕ × ℕ => q ^ x.1 * x.2), (m : ℝ) ^ (-α) ≤
            ∑ x ∈ range (E + 1) ×ˢ B, ((q ^ x.1 * x.2 : ℕ) : ℝ) ^ (-α) :=
        sum_image_le_of_nonneg fun _ _ => by positivity
      calc
        ∑ m ∈ A, (m : ℝ) ^ (-α)
          ≤ ∑ m ∈ (range (E + 1) ×ˢ B).image (fun x : ℕ × ℕ => q ^ x.1 * x.2), (m : ℝ) ^ (-α) :=
            sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ ≤ ∑ x ∈ range (E + 1) ×ˢ B, ((q ^ x.1 * x.2 : ℕ) : ℝ) ^ (-α) := hsum_img
        _ = (∑ e ∈ range (E + 1), ((q : ℝ) ^ (-α)) ^ e) * (∑ u ∈ B, (u : ℝ) ^ (-α)) := by
            rw [Finset.sum_product, sum_mul]
            refine sum_congr rfl fun e _ => ?_
            rw [mul_sum]
            refine sum_congr rfl fun u hu => ?_
            have hu_pos : (0 : ℝ) < (u : ℝ) := by
              exact_mod_cast (mem_Icc.mp (mem_filter.mp hu).1).1
            have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_prime.pos
            push_cast
            rw [Real.mul_rpow (pow_nonneg hq_pos.le e) hu_pos.le]
            congr 1
            rw [← rpow_natCast (q : ℝ) e, ← rpow_mul hq_pos.le,
                ← rpow_natCast ((q : ℝ) ^ (-α)) e, ← rpow_mul hq_pos.le, mul_comm]
        _ ≤ (∑ e ∈ range (E + 1), ((q : ℝ) ^ (-α)) ^ e) *
            ∏ p ∈ T, ∑ e ∈ range (E + 1), ((p : ℝ) ^ (-α)) ^ e := by
            exact mul_le_mul_of_nonneg_left (ih hT_prime) (sum_nonneg fun _ _ => by positivity)
  refine (hmain S hS).trans (Finset.prod_le_prod (fun p _ => sum_nonneg fun _ _ => by positivity) ?_)
  intro p hp
  have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
  have hr1 : (p : ℝ) ^ (-α) < 1 := by
    rw [Real.rpow_neg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by linarith) hα)
  exact geom_sum_le_inv_one_sub _ (by positivity) hr1 E

private lemma inv_one_sub_le_exp_two (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ exp (2 * x) := by
  have hpos : 0 < 1 - x := by linarith
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  have h1 : 1 + 2 * x ≤ exp (2 * x) := by linarith [add_one_le_exp (2 * x)]
  nlinarith

private lemma smooth_card_le (H y : ℕ) (hH : 1 ≤ H) (hy : 4 ≤ y) :
    let S_sm := (Icc 1 H).filter (fun j => ∀ p ∈ j.primeFactors, p ≤ y)
    (S_sm.card : ℝ) ≤
      (H : ℝ) * exp (-log (H : ℝ) / (2 * log (y : ℝ))) *
        16 * exp (4 * ∑ p ∈ (Icc 1 y).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) := by
  intro S_sm
  have hyR : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 1 ≤ log (y : ℝ) := by
    have : exp 1 ≤ 4 := by linarith [exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr (this.trans hyR)
  let α : ℝ := 1 - 1 / (2 * log (y : ℝ))
  have hα_ge : 1 / 2 ≤ α := by
    have : 1 / (2 * log (y : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    dsimp only [α]; linarith
  have hα_pos : 0 < α := by linarith
  have h1 : (S_sm.card : ℝ) ≤ (H : ℝ) ^ α * ∑ m ∈ S_sm, (m : ℝ) ^ (-α) := by
    rw [mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (mem_Icc.mp (mem_filter.mp hm).1).1
    have hmH : m ≤ H := (mem_Icc.mp (mem_filter.mp hm).1).2
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
    have hpow : (m : ℝ) ^ α ≤ (H : ℝ) ^ α := rpow_le_rpow hmR.le (by exact_mod_cast hmH) hα_pos.le
    rw [Real.rpow_neg hmR.le, ← div_eq_mul_inv, Nat.cast_one, one_le_div (Real.rpow_pos_of_pos hmR α)]
    exact hpow
  have hS_sm_eq : S_sm = (Icc 1 H).filter
      (fun m => ∀ p ∈ m.primeFactors, p ∈ (Icc 1 y).filter Nat.Prime) := by
    ext m
    simp only [S_sm, mem_filter, mem_Icc]
    refine and_congr_right fun _ => forall_congr' fun p => ⟨fun h hp => ?_, fun h hp => (h hp).1.2⟩
    exact ⟨⟨(Nat.prime_of_mem_primeFactors hp).one_le, h hp⟩, Nat.prime_of_mem_primeFactors hp⟩
  have h2 : ∑ m ∈ S_sm, (m : ℝ) ^ (-α) ≤
      ∏ p ∈ (Icc 1 y).filter Nat.Prime, (1 - (p : ℝ) ^ (-α))⁻¹ := by
    rw [hS_sm_eq]
    exact sum_smooth_rpow_le H _ α (fun p hp => (mem_filter.mp hp).2) hα_pos
  have h3 : ∏ p ∈ (Icc 1 y).filter Nat.Prime, (1 - (p : ℝ) ^ (-α))⁻¹ ≤
      16 * exp (4 * ∑ p ∈ (Icc 1 y).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) := by
    have hprod_le :
        ∏ p ∈ (Icc 1 y).filter Nat.Prime, (1 - (p : ℝ) ^ (-α))⁻¹ ≤
          ∏ p ∈ (Icc 1 y).filter Nat.Prime,
            ((if p ≤ 3 then (4 : ℝ) else 1) * exp (4 * (1 / (p : ℝ)))) := by
      refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
      · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
        have : (p : ℝ) ^ (-α) < 1 := by
          rw [Real.rpow_neg (by positivity)]
          exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by linarith) hα_pos)
        exact inv_nonneg.mpr (by linarith)
      · have hp_prime : p.Prime := (mem_filter.mp hp).2
        have hp_le_y : p ≤ y := (mem_Icc.mp (mem_filter.mp hp).1).2
        have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
        by_cases hp3 : p ≤ 3
        · rw [if_pos hp3]
          have hinv4 : (1 - (p : ℝ) ^ (-α))⁻¹ ≤ 4 := by
            have h2_le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (p : ℝ) ^ α := by
              calc
                (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα_ge
                _ ≤ (p : ℝ) ^ α := rpow_le_rpow (by norm_num) (by exact_mod_cast hp_prime.two_le) hα_pos.le
            have hsqrt2 : (4 : ℝ) / 3 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
              rw [← sqrt_eq_rpow, Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
            have hpa : (p : ℝ) ^ (-α) ≤ 3 / 4 := by
              rw [Real.rpow_neg hp_pos.le]
              have h1 : (4 : ℝ) / 3 ≤ (p : ℝ) ^ α := hsqrt2.trans h2_le
              rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
              linarith
            rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
            linarith
          have hexp1 : 1 ≤ exp (4 * (1 / (p : ℝ))) := one_le_exp (by positivity)
          nlinarith
        · push Not at hp3
          rw [if_neg (by omega), one_mul]
          have hp5 : (5 : ℝ) ≤ (p : ℝ) := by
            have : p ≠ 4 := fun h => by subst h; exact absurd hp_prime (by decide)
            exact_mod_cast (by omega : 5 ≤ p)
          have hp_pow : (p : ℝ) ^ (1 - α) ≤ 2 := by
            have h1 : 1 - α = 1 / (2 * log (y : ℝ)) := by dsimp only [α]; ring
            rw [h1]
            calc
              (p : ℝ) ^ (1 / (2 * log (y : ℝ)))
                ≤ (y : ℝ) ^ (1 / (2 * log (y : ℝ))) :=
                  rpow_le_rpow hp_pos.le (by exact_mod_cast hp_le_y) (by positivity)
              _ = exp (log (y : ℝ) * (1 / (2 * log (y : ℝ)))) := by
                  rw [rpow_def_of_pos (by positivity)]
              _ = exp (1 / 2) := by
                  congr 1; field_simp [(by linarith : log (y : ℝ) ≠ 0)]
              _ ≤ 2 := by
                  have hsq : (exp (1 / 2)) ^ 2 < 4 := by
                    rw [← exp_nat_mul]; norm_num; linarith [exp_one_lt_d9]
                  nlinarith [exp_pos (1 / 2)]
          have hpa_le : (p : ℝ) ^ (-α) ≤ 2 * (1 / (p : ℝ)) := by
            have heq : (p : ℝ) ^ (-α) = (p : ℝ) ^ (1 - α) * (1 / (p : ℝ)) := by
              rw [one_div, ← rpow_neg_one, ← rpow_add hp_pos]; congr 1; ring
            rw [heq]
            exact mul_le_mul_of_nonneg_right hp_pow (by positivity)
          have hpa_half : (p : ℝ) ^ (-α) ≤ 1 / 2 := by
            have : 2 * (1 / (p : ℝ)) ≤ 2 / 5 := by
              rw [mul_one_div, div_le_div_iff₀ hp_pos (by norm_num)]; linarith
            linarith
          calc
            (1 - (p : ℝ) ^ (-α))⁻¹ ≤ exp (2 * (p : ℝ) ^ (-α)) :=
              inv_one_sub_le_exp_two _ (by positivity) hpa_half
            _ ≤ exp (4 * (1 / (p : ℝ))) :=
              exp_le_exp.mpr (by linarith)
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← mul_sum] at hprod_le
    have h4prod : ∏ p ∈ (Icc 1 y).filter Nat.Prime, (if p ≤ 3 then (4 : ℝ) else 1) ≤ 16 := by
      have hsub : ((Icc 1 y).filter Nat.Prime).filter (fun p => p ≤ 3) ⊆ {2, 3} := by
        intro p hp
        simp only [mem_filter, mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
        have := hp.1.2.two_le
        omega
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      have hcard : (((Icc 1 y).filter Nat.Prime).filter (fun p => p ≤ 3)).card ≤ 2 :=
        (Finset.card_le_card hsub).trans (by decide)
      calc (4 : ℝ) ^ (((Icc 1 y).filter Nat.Prime).filter (fun p => p ≤ 3)).card
        ≤ (4 : ℝ) ^ 2 := pow_le_pow_right₀ (by norm_num) hcard
        _ = 16 := by norm_num
    exact hprod_le.trans (mul_le_mul_of_nonneg_right h4prod (exp_pos _).le)
  have hH_pow : (H : ℝ) ^ α = (H : ℝ) * exp (-log (H : ℝ) / (2 * log (y : ℝ))) := by
    have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
    rw [rpow_def_of_pos hHR]
    have : log (H : ℝ) * α = log (H : ℝ) + (-log (H : ℝ) / (2 * log (y : ℝ))) := by
      dsimp only [α]; ring
    rw [this, exp_add, exp_log hHR]
  calc
    (S_sm.card : ℝ)
      ≤ (H : ℝ) ^ α * ∑ m ∈ S_sm, (m : ℝ) ^ (-α) := h1
    _ ≤ (H : ℝ) ^ α * (16 * exp (4 * ∑ p ∈ (Icc 1 y).filter Nat.Prime, (1 : ℝ) / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
    _ = _ := by rw [hH_pow]; ring

private lemma selberg_S_ge (z Z : ℕ) (_hz : 4 ≤ z) (hZ : 2 ≤ Z) :
    let Q := (Ioc z Z).filter Nat.Prime
    let D := (Icc 1 Z).filter (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, p ∈ Q)
    log (Z : ℝ) /
        (4 * exp (2 * ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))) ≤
      ∑ d ∈ D, (1 : ℝ) / (d.totient : ℝ) := by
  intro Q D
  let U := (Icc 1 Z).filter (fun u => ∀ p ∈ u.primeFactors, p ≤ z)
  let V := (Icc 1 Z).filter (fun v => ∀ p ∈ v.primeFactors, p ∈ Q)
  -- Step 1: log Z ≤ ∑_{m ∈ Icc 1 Z} 1/m ≤ (∑_{u ∈ U} 1/u) * (∑_{v ∈ V} 1/v)
  have hlog_le : log (Z : ℝ) ≤ ∑ m ∈ Icc 1 Z, (1 : ℝ) / (m : ℝ) := by
    have h1 := harmonic_sum_ge_log_ratio 1 (Z + 1) le_rfl (by omega)
    have h2 : log (Z : ℝ) ≤ log (((Z + 1 : ℕ) : ℝ) / (1 : ℝ)) := by
      rw [div_one]; exact log_le_log (by positivity) (by push_cast; linarith)
    have h3 : ∑ k ∈ Ico 1 (Z + 1), (1 : ℝ) / (k : ℝ) = ∑ m ∈ Icc 1 Z, (1 : ℝ) / (m : ℝ) :=
      rfl
    linarith
  have hfactor : Icc 1 Z ⊆ (U ×ˢ V).image (fun x : ℕ × ℕ => x.1 * x.2) := by
    intro m hm
    rw [mem_Icc] at hm
    let u := ∏ p ∈ m.primeFactors.filter (fun p => p ≤ z), p ^ m.factorization p
    let v := ∏ p ∈ m.primeFactors.filter (fun p => z < p), p ^ m.factorization p
    have hmul : u * v = m := by
      have hdisj : Disjoint (m.primeFactors.filter (fun p => p ≤ z)) (m.primeFactors.filter (fun p => z < p)) := by
        rw [Finset.disjoint_left]; intro p hp1 hp2
        simp only [mem_filter] at hp1 hp2; omega
      have hunion : m.primeFactors.filter (fun p => p ≤ z) ∪ m.primeFactors.filter (fun p => z < p) = m.primeFactors := by
        ext p; simp only [Finset.mem_union, mem_filter]; constructor
        · rintro (h | h) <;> exact h.1
        · intro hp; by_cases h : p ≤ z; exact Or.inl ⟨hp, h⟩; exact Or.inr ⟨hp, by omega⟩
      rw [← Finset.prod_union hdisj, hunion]
      exact Nat.prod_factorization_pow_eq_self (by omega)
    have hu_pos : 0 < u := Finset.prod_pos fun p hp =>
      pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _
    have hv_pos : 0 < v := Finset.prod_pos fun p hp =>
      pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _
    have hu_mem : u ∈ U := by
      simp only [U, mem_filter, mem_Icc]
      refine ⟨⟨hu_pos, ?_⟩, fun p hp => ?_⟩
      · exact (Nat.le_of_dvd (by omega) ⟨v, hmul.symm⟩).trans hm.2
      · have hp_prime := Nat.prime_of_mem_primeFactors hp
        have hpdvd : p ∣ u := Nat.dvd_of_mem_primeFactors hp
        obtain ⟨q, hq, hpq⟩ := hp_prime.prime.exists_mem_finset_dvd hpdvd
        have hq_prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1
        have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow hpq)
        rw [hpeq]
        exact (mem_filter.mp hq).2
    have hv_mem : v ∈ V := by
      simp only [V, mem_filter, mem_Icc]
      have hv_le : v ≤ Z := (Nat.le_of_dvd (by omega) ⟨u, by rw [mul_comm, hmul]⟩).trans hm.2
      refine ⟨⟨hv_pos, hv_le⟩, fun p hp => ?_⟩
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ v := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨q, hq, hpq⟩ := hp_prime.prime.exists_mem_finset_dvd hpdvd
      have hq_prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1
      have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp (hp_prime.dvd_of_dvd_pow hpq)
      rw [hpeq]
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_filter.mp hq).2, ?_⟩, hq_prime⟩
      exact (Nat.le_of_dvd hv_pos (hpeq ▸ hpdvd)).trans hv_le
    exact mem_image.mpr ⟨(u, v), mem_product.mpr ⟨hu_mem, hv_mem⟩, hmul⟩
  have hprod_bound : log (Z : ℝ) ≤ (∑ u ∈ U, (1 : ℝ) / (u : ℝ)) * (∑ v ∈ V, (1 : ℝ) / (v : ℝ)) := by
    calc
      log (Z : ℝ) ≤ ∑ m ∈ Icc 1 Z, (1 : ℝ) / (m : ℝ) := hlog_le
      _ ≤ ∑ m ∈ (U ×ˢ V).image (fun x : ℕ × ℕ => x.1 * x.2), (1 : ℝ) / (m : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hfactor fun _ _ _ => by positivity
      _ ≤ ∑ x ∈ U ×ˢ V, (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ) :=
          sum_image_le_of_nonneg fun _ _ => by positivity
      _ = (∑ u ∈ U, (1 : ℝ) / (u : ℝ)) * (∑ v ∈ V, (1 : ℝ) / (v : ℝ)) := by
          rw [Finset.sum_product, sum_mul]
          refine sum_congr rfl fun u _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun v _ => by push_cast; ring
  -- Step 2: ∑_{u ∈ U} 1/u ≤ 4 * exp(2 * ∑_{p ≤ z} 1/p)
  have hU_le : ∑ u ∈ U, (1 : ℝ) / (u : ℝ) ≤
      4 * exp (2 * ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) := by
    have hU_eq : U = (Icc 1 Z).filter
        (fun m => ∀ p ∈ m.primeFactors, p ∈ (Icc 1 z).filter Nat.Prime) := by
      ext m; simp only [U, mem_filter, mem_Icc]
      refine and_congr_right fun _ => forall_congr' fun p => ⟨fun h hp => ?_, fun h hp => (h hp).1.2⟩
      exact ⟨⟨(Nat.prime_of_mem_primeFactors hp).one_le, h hp⟩, Nat.prime_of_mem_primeFactors hp⟩
    have h1 : ∑ u ∈ U, (1 : ℝ) / (u : ℝ) ≤
        ∏ p ∈ (Icc 1 z).filter Nat.Prime, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ := by
      have hrewrite : ∑ u ∈ U, (1 : ℝ) / (u : ℝ) = ∑ u ∈ U, (u : ℝ) ^ (-(1 : ℝ)) := by
        refine sum_congr rfl fun u _ => by rw [rpow_neg_one, one_div]
      rw [hrewrite, hU_eq]
      exact sum_smooth_rpow_le Z _ 1 (fun p hp => (mem_filter.mp hp).2) one_pos
    refine h1.trans ?_
    have hprod_le :
        ∏ p ∈ (Icc 1 z).filter Nat.Prime, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ ≤
          ∏ p ∈ (Icc 1 z).filter Nat.Prime,
            ((if p = 2 then (4 : ℝ) else 1) * exp (2 * (1 / (p : ℝ)))) := by
      refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
      · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
        rw [rpow_neg_one]
        have : (p : ℝ)⁻¹ ≤ 1 / 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
        exact inv_nonneg.mpr (by linarith)
      · have hp_prime := (mem_filter.mp hp).2
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
        rw [rpow_neg_one, ← one_div]
        have hx1 : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        by_cases h2 : p = 2
        · rw [if_pos h2]
          have hle4 : (1 - (1 : ℝ) / (p : ℝ))⁻¹ ≤ 4 := by
            rw [h2]; norm_num
          have hexp1 : 1 ≤ exp (2 * (1 / (p : ℝ))) := one_le_exp (by positivity)
          rw [one_div] at hle4 ⊢
          nlinarith
        · rw [if_neg h2, one_mul]
          have hle := inv_one_sub_le_exp_two ((1 : ℝ) / (p : ℝ)) (by positivity) hx1
          simpa [one_div] using hle
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← mul_sum] at hprod_le
    have h2prod : ∏ p ∈ (Icc 1 z).filter Nat.Prime, (if p = 2 then (4 : ℝ) else 1) ≤ 4 := by
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      have hcard : (((Icc 1 z).filter Nat.Prime).filter (fun p => p = 2)).card ≤ 1 := by
        refine (Finset.card_le_card (t := ({2} : Finset ℕ)) fun p hp => ?_).trans (by simp)
        simp only [mem_filter, Finset.mem_singleton] at hp ⊢
        exact hp.2
      calc (4 : ℝ) ^ (((Icc 1 z).filter Nat.Prime).filter (fun p => p = 2)).card
        ≤ (4 : ℝ) ^ 1 := pow_le_pow_right₀ (by norm_num) hcard
        _ = 4 := by norm_num
    exact hprod_le.trans (mul_le_mul_of_nonneg_right h2prod (exp_pos _).le)
  -- Step 3: ∑_{v ∈ V} 1/v ≤ ∑_{d ∈ D} 1 / d.totient
  have hV_le : ∑ v ∈ V, (1 : ℝ) / (v : ℝ) ≤ ∑ d ∈ D, (1 : ℝ) / (d.totient : ℝ) := by
    let rad : ℕ → ℕ := fun v => ∏ p ∈ v.primeFactors, p
    have hrad_mem : ∀ v ∈ V, rad v ∈ D := by
      intro v hv
      simp only [V, mem_filter, mem_Icc] at hv
      have hv_ne : v ≠ 0 := by omega
      have hrad_dvd : rad v ∣ v := Nat.prod_primeFactors_dvd v
      have hrad_pos : 0 < rad v := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
      have hrad_le : rad v ≤ Z := (Nat.le_of_dvd hv.1.1 hrad_dvd).trans hv.1.2
      have hrad_sqf : Squarefree (rad v) := by
        rw [Nat.squarefree_iff_prime_squarefree]
        intro p hp hpp
        have hpm : p ∈ v.primeFactors := by
          have := (dvd_mul_left p p).trans hpp |>.trans hrad_dvd
          exact Nat.mem_primeFactors.mpr ⟨hp, this, hv_ne⟩
        have hsplit : rad v = p * ∏ q ∈ v.primeFactors.erase p, q :=
          (Finset.mul_prod_erase _ _ hpm).symm
        rw [hsplit] at hpp
        have hpdvd : p ∣ ∏ q ∈ v.primeFactors.erase p, q := (Nat.mul_dvd_mul_iff_left hp.pos).mp hpp
        obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd hpdvd
        have hq_prime := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hq).2
        have heq := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq
        exact (Finset.mem_erase.mp hq).1 heq.symm
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hrad_pos, hrad_le⟩, hrad_sqf, fun p hp => ?_⟩
      exact hv.2 p (Nat.primeFactors_mono hrad_dvd hv_ne hp)
    have hgroup : ∑ v ∈ V, (1 : ℝ) / (v : ℝ) =
        ∑ d ∈ D, ∑ v ∈ V.filter (fun v => rad v = d), (1 : ℝ) / (v : ℝ) := by
      rw [← sum_fiberwise_of_maps_to hrad_mem]
    rw [hgroup]
    refine sum_le_sum fun d hd => ?_
    have hd_pos : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
    have hd_sqf : Squarefree d := (mem_filter.mp hd).2.1
    -- Every v ∈ V with rad v = d satisfies v = d * w with w ∈ Icc 1 Z and w.primeFactors ⊆ d.primeFactors
    let W := (Icc 1 Z).filter (fun w => ∀ p ∈ w.primeFactors, p ∈ d.primeFactors)
    have hfib_le : ∑ v ∈ V.filter (fun v => rad v = d), (1 : ℝ) / (v : ℝ) ≤
        (1 : ℝ) / (d : ℝ) * ∑ w ∈ W, (1 : ℝ) / (w : ℝ) := by
      have hsub : V.filter (fun v => rad v = d) ⊆ W.image (fun w => d * w) := by
        intro v hv
        simp only [mem_filter, V, mem_Icc] at hv
        have hv_ne : v ≠ 0 := by omega
        have hdvd : d ∣ v := hv.2 ▸ Nat.prod_primeFactors_dvd v
        let w := v / d
        have hw_eq : d * w = v := Nat.mul_div_cancel' hdvd
        have hw_pos : 0 < w := Nat.div_pos (Nat.le_of_dvd hv.1.1.1 hdvd) hd_pos
        have hw_le : w ≤ Z := (Nat.div_le_self v d).trans hv.1.1.2
        have hw_pf : ∀ p ∈ w.primeFactors, p ∈ d.primeFactors := by
          intro p hp
          have hpv : p ∈ v.primeFactors := Nat.primeFactors_mono (Nat.div_dvd_of_dvd hdvd) hv_ne hp
          have hpd : p ∣ d := hv.2 ▸ dvd_prod_of_mem _ hpv
          exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpd, hd_pos.ne'⟩
        exact mem_image.mpr ⟨w, mem_filter.mpr ⟨mem_Icc.mpr ⟨hw_pos, hw_le⟩, hw_pf⟩, hw_eq⟩
      calc
        ∑ v ∈ V.filter (fun v => rad v = d), (1 : ℝ) / (v : ℝ)
          ≤ ∑ v ∈ W.image (fun w => d * w), (1 : ℝ) / (v : ℝ) :=
            sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ ≤ ∑ w ∈ W, (1 : ℝ) / ((d * w : ℕ) : ℝ) :=
            sum_image_le_of_nonneg fun _ _ => by positivity
        _ = (1 : ℝ) / (d : ℝ) * ∑ w ∈ W, (1 : ℝ) / (w : ℝ) := by
            rw [mul_sum]; refine sum_congr rfl fun w _ => by push_cast; ring
    have hW_le : ∑ w ∈ W, (1 : ℝ) / (w : ℝ) ≤
        ∏ p ∈ d.primeFactors, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ := by
      have hrewrite : ∑ w ∈ W, (1 : ℝ) / (w : ℝ) = ∑ w ∈ W, (w : ℝ) ^ (-(1 : ℝ)) :=
        sum_congr rfl fun w _ => by rw [rpow_neg_one, one_div]
      rw [hrewrite]
      exact sum_smooth_rpow_le Z d.primeFactors 1 (fun p hp => Nat.prime_of_mem_primeFactors hp) one_pos
    have hphi_eq : (1 : ℝ) / (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ =
        (1 : ℝ) / (d.totient : ℝ) := by
      have htot := Nat.totient_eq_mul_prod_factors d
      have htotR : (d.totient : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
        have hq : ((d.totient : ℚ) : ℝ) = ((d * ∏ p ∈ d.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by
          exact_mod_cast htot
        simpa using hq
      have hprod_ne : ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) ≠ 0 := by
        rw [prod_ne_zero_iff]
        intro p hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have : (p : ℝ)⁻¹ ≤ 1 / 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
        linarith
      rw [htotR]
      have hprod_inv : ∏ p ∈ d.primeFactors, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ =
          (∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by
        rw [prod_inv_distrib]
        congr 1
        refine prod_congr rfl fun p _ => by rw [rpow_neg_one]
      rw [hprod_inv]
      have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast hd_pos.ne'
      field_simp [hd_ne, hprod_ne]
    calc
      ∑ v ∈ V.filter (fun v => rad v = d), (1 : ℝ) / (v : ℝ)
        ≤ (1 : ℝ) / (d : ℝ) * ∑ w ∈ W, (1 : ℝ) / (w : ℝ) := hfib_le
      _ ≤ (1 : ℝ) / (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ :=
          mul_le_mul_of_nonneg_left hW_le (by positivity)
      _ = (1 : ℝ) / (d.totient : ℝ) := hphi_eq
  rw [div_le_iff₀ (by positivity)]
  calc
    log (Z : ℝ)
      ≤ (∑ u ∈ U, (1 : ℝ) / (u : ℝ)) * (∑ v ∈ V, (1 : ℝ) / (v : ℝ)) := hprod_bound
    _ ≤ (4 * exp (2 * ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))) *
          (∑ d ∈ D, (1 : ℝ) / (d.totient : ℝ)) := by
        gcongr
    _ = (∑ d ∈ D, (1 : ℝ) / (d.totient : ℝ)) *
          (4 * exp (2 * ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))) := by ring

private lemma greedy_sieve_finset (U P₁ : Finset ℕ) (hP₁ : ∀ p ∈ P₁, p.Prime) :
    ∃ a : ℕ → ℕ,
      ((U.filter (fun j => ∀ p ∈ P₁, ¬ p ∣ j + a p)).card : ℝ) ≤
        (U.card : ℝ) * exp (-∑ p ∈ P₁, (1 : ℝ) / (p : ℝ)) := by
  induction P₁ using Finset.induction_on generalizing U with
  | empty =>
    exact ⟨fun _ => 0, by simp⟩
  | insert q P hqP ih =>
    have hq_prime : q.Prime := hP₁ q (mem_insert_self q P)
    have hP_prime : ∀ p ∈ P, p.Prime := fun p hp => hP₁ p (mem_insert_of_mem hp)
    -- Choose r < q maximizing #{j ∈ U : q ∣ j + r}
    have hex_r : ∃ r < q, (U.card : ℝ) / (q : ℝ) ≤ ((U.filter (fun j => q ∣ j + r)).card : ℝ) := by
      have hsum : ∑ r ∈ range q, (U.filter (fun j => q ∣ j + r)).card = U.card := by
        have hmap : ∀ j ∈ U, (q - j % q) % q ∈ range q := fun j _ =>
          mem_range.mpr (Nat.mod_lt _ hq_prime.pos)
        have hfib := sum_card_fiberwise_eq_card_filter (s := U) (t := range q)
          (g := fun j => (q - j % q) % q)
        have hfilt_eq : U.filter (fun j => (q - j % q) % q ∈ range q) = U :=
          filter_true_of_mem hmap
        rw [hfilt_eq] at hfib
        rw [← hfib]
        refine sum_congr rfl fun r hr => ?_
        congr 1
        ext j
        simp only [mem_filter]
        refine and_congr_right fun _ => ?_
        have hr_lt : r < q := mem_range.mp hr
        have hj_lt : j % q < q := Nat.mod_lt j hq_prime.pos
        constructor
        · intro hdvd
          have hmod0 : (j + r) % q = 0 := Nat.mod_eq_zero_of_dvd hdvd
          have : (j % q + r) % q = 0 := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hmod0]
          by_cases hj0 : j % q = 0
          · rw [hj0, Nat.sub_zero, Nat.mod_self]
            rw [hj0, zero_add, Nat.mod_eq_of_lt hr_lt] at this
            exact this.symm
          · have hlt : q - j % q < q := by omega
            rw [Nat.mod_eq_of_lt hlt]
            have hsum_eq : j % q + r = q := by
              have hlt2 : j % q + r < 2 * q := by omega
              have hge : q ≤ j % q + r := by
                by_contra hltq
                rw [Nat.mod_eq_of_lt (by omega)] at this
                omega
              have hsub : (j % q + r) % q = j % q + r - q := by
                rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
              omega
            omega
        · intro heq
          rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, ← heq]
          by_cases hj0 : j % q = 0
          · simp [hj0]
          · have hlt : q - j % q < q := by omega
            rw [Nat.mod_eq_of_lt hlt]
            have : j % q + (q - j % q) = q := by omega
            simp [this]
      by_contra hnot
      push Not at hnot
      have hlt : ∑ r ∈ range q, ((U.filter (fun j => q ∣ j + r)).card : ℝ) <
          ∑ _r ∈ range q, (U.card : ℝ) / (q : ℝ) := by
        apply sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hq_prime.ne_zero)
        intro r hr
        exact hnot r (mem_range.mp hr)
      rw [← Nat.cast_sum, hsum, sum_const, Finset.card_range, nsmul_eq_mul] at hlt
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq_prime.ne_zero
      field_simp [hqR] at hlt
      linarith
    obtain ⟨r, _, hr_ge⟩ := hex_r
    let U' := U.filter (fun j => ¬ q ∣ j + r)
    have hU'_card : (U'.card : ℝ) ≤ (U.card : ℝ) * exp (-((1 : ℝ) / (q : ℝ))) := by
      have hadd := Finset.card_filter_add_card_filter_not (s := U) (fun j => q ∣ j + r)
      have hU'_le : (U'.card : ℝ) ≤ (U.card : ℝ) * (1 - 1 / (q : ℝ)) := by
        have haddR : ((U.filter (fun j => q ∣ j + r)).card : ℝ) + (U'.card : ℝ) = (U.card : ℝ) := by
          exact_mod_cast hadd
        linarith [show (U.card : ℝ) * (1 - 1 / (q : ℝ)) = (U.card : ℝ) - (U.card : ℝ) / (q : ℝ) by ring]
      refine hU'_le.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      linarith [add_one_le_exp (-((1 : ℝ) / (q : ℝ)))]
    obtain ⟨a', ha'⟩ := ih U' hP_prime
    refine ⟨fun p => if p = q then r else a' p, ?_⟩
    have hfilt : U.filter (fun j => ∀ p ∈ insert q P, ¬ p ∣ j + (if p = q then r else a' p)) =
        U'.filter (fun j => ∀ p ∈ P, ¬ p ∣ j + a' p) := by
      ext j
      simp only [U', mem_filter, Finset.mem_insert]
      constructor
      · intro ⟨hjU, hall⟩
        refine ⟨⟨hjU, ?_⟩, fun p hp => ?_⟩
        · have := hall q (Or.inl rfl); simpa using this
        · have hpq : p ≠ q := fun h => hqP (h ▸ hp)
          have := hall p (Or.inr hp); simpa [hpq] using this
      · rintro ⟨⟨hjU, hnq⟩, hall⟩
        refine ⟨hjU, fun p hp => ?_⟩
        rcases hp with rfl | hpP
        · simpa using hnq
        · have hpq : p ≠ q := fun h => hqP (h ▸ hpP)
          simpa [hpq] using hall p hpP
    rw [hfilt, Finset.sum_insert hqP, neg_add, exp_add]
    calc
      ((U'.filter (fun j => ∀ p ∈ P, ¬ p ∣ j + a' p)).card : ℝ)
        ≤ (U'.card : ℝ) * exp (-∑ p ∈ P, (1 : ℝ) / (p : ℝ)) := ha'
      _ ≤ ((U.card : ℝ) * exp (-((1 : ℝ) / (q : ℝ)))) *
            exp (-∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right hU'_card (exp_pos _).le
      _ = _ := by ring

private lemma crt_finset_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (a : ℕ → ℕ) :
    ∃ r < ∏ p ∈ S, p, ∀ p ∈ S, r ≡ a p [MOD p] := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨0, by simp, fun _ hp => absurd hp (Finset.notMem_empty _)⟩
  | insert q T hqT ih =>
    have hq_prime : q.Prime := hS q (mem_insert_self q T)
    have hT_prime : ∀ p ∈ T, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    obtain ⟨r₀, hr₀_lt, hr₀_mod⟩ := ih hT_prime
    have hcop : Nat.Coprime q (∏ p ∈ T, p) := by
      rw [Nat.coprime_comm]
      exact Nat.Coprime.prod_left fun p hp =>
        (Nat.coprime_primes (hT_prime p hp) hq_prime).mpr (fun h => hqT (h ▸ hp))
    let crt := Nat.chineseRemainder hcop (a q) r₀
    have hprod_pos : 0 < q * ∏ p ∈ T, p :=
      mul_pos hq_prime.pos (Finset.prod_pos fun p hp => (hT_prime p hp).pos)
    refine ⟨crt.val % (q * ∏ p ∈ T, p), ?_, fun p hp => ?_⟩
    · rw [Finset.prod_insert hqT]
      exact Nat.mod_lt _ hprod_pos
    · rw [Finset.mem_insert] at hp
      rcases hp with hpq | hpT
      · rw [hpq]
        have h1 : crt.val % (q * ∏ p ∈ T, p) ≡ crt.val [MOD q] :=
          Nat.ModEq.of_dvd (dvd_mul_right q _) (Nat.mod_modEq _ _)
        exact h1.trans crt.property.1
      · have hdvd : p ∣ q * ∏ x ∈ T, x := (dvd_prod_of_mem id hpT).trans (dvd_mul_left _ _)
        have h1 : crt.val % (q * ∏ x ∈ T, x) ≡ crt.val [MOD p] :=
          Nat.ModEq.of_dvd hdvd (Nat.mod_modEq _ _)
        have h2 : crt.val ≡ r₀ [MOD p] :=
          Nat.ModEq.of_dvd (dvd_prod_of_mem id hpT) crt.property.2
        exact h1.trans (h2.trans (hr₀_mod p hpT))

/- ### Part 5: Final Assembly -/

private lemma primorial_eq_prod_Icc (z : ℕ) :
    primorial z = ∏ p ∈ (Icc 1 z).filter Nat.Prime, p := by
  rw [primorial]
  congr 1
  ext p
  simp only [mem_filter, mem_range, mem_Icc]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨⟨h2.one_le, Nat.lt_succ_iff.mp h1⟩, h2⟩
  · intro ⟨⟨_, h1⟩, h2⟩; exact ⟨Nat.lt_succ_of_le h1, h2⟩

/-- For fixed `j, d, m`, bound the number of `k ∈ Icc 1 P` such that `d * m ∣ r + k * P + j`
and `(r + k * P + j) / (d * m)` is prime, using `selberg_sieve_ap`. -/
private lemma count_prime_quot_le (z P Z r j d m : ℕ)
    (hZ : 1 ≤ Z)
    (hd_pos : 0 < d) (hm_pos : 0 < m)
    (hd_rj : d ∣ r + j) (hd_P : d ∣ P)
    (hP_cop : ∀ q ∈ (Ioc z Z).filter Nat.Prime, ¬ q ∣ P)
    (hquot_gt : Z < P / (d * m)) :
    let Q := (Ioc z Z).filter Nat.Prime
    let D := (Icc 1 Z).filter (fun e => Squarefree e ∧ ∀ p ∈ e.primeFactors, p ∈ Q)
    let S := ∑ e ∈ D, (1 : ℝ) / (e.totient : ℝ)
    (((Icc 1 P).filter (fun k =>
      d * m ∣ r + k * P + j ∧ ((r + k * P + j) / (d * m)).Prime)).card : ℝ) ≤
      ((P + 1 : ℕ) : ℝ) / S + (Z : ℝ) ^ 2 := by
  intro Q D S
  let u₀ := (r + j) / d
  let P' := P / d
  have hu₀_eq : d * u₀ = r + j := Nat.mul_div_cancel' hd_rj
  have hP'_eq : d * P' = P := Nat.mul_div_cancel' hd_P
  let g := Nat.gcd m P'
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left P' hm_pos
  by_cases hgu : ¬ g ∣ u₀
  · -- Zero solutions
    have hempty : (Icc 1 P).filter (fun k =>
        d * m ∣ r + k * P + j ∧ ((r + k * P + j) / (d * m)).Prime) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k _ ⟨hdvd, _⟩
      apply hgu
      have h1 : r + k * P + j = d * (u₀ + k * P') := by
        rw [mul_add, hu₀_eq, show d * (k * P') = k * (d * P') by ring, hP'_eq]; ring
      rw [h1] at hdvd
      have hm_dvd : m ∣ u₀ + k * P' := (Nat.mul_dvd_mul_iff_left hd_pos).mp hdvd
      have hg_sum : g ∣ u₀ + k * P' := (Nat.gcd_dvd_left m P').trans hm_dvd
      have hg_kP : g ∣ k * P' := (Nat.gcd_dvd_right m P').trans (dvd_mul_left P' k)
      exact (Nat.dvd_add_left hg_kP).mp hg_sum
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have hS_pos : 0 < S := by
      have h1D : 1 ∈ D := by simp [D, hZ]
      refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / ((1 : ℕ).totient : ℝ)) ?_
      exact Finset.single_le_sum (f := fun e => (1 : ℝ) / (e.totient : ℝ)) (fun _ _ => by positivity) h1D
    positivity
  · push Not at hgu
    let m' := m / g
    let P'' := P' / g
    let u₀' := u₀ / g
    have hm'_pos : 0 < m' := Nat.div_pos (Nat.le_of_dvd hm_pos (Nat.gcd_dvd_left _ _)) hg_pos
    have hm_eq : g * m' = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hP''_eq : g * P'' = P' := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have hu₀'_eq : g * u₀' = u₀ := Nat.mul_div_cancel' hgu
    have hcop_m'P'' : Nat.Coprime m' P'' := Nat.coprime_div_gcd_div_gcd hg_pos
    -- Unique residue k₀ < m' such that m' ∣ u₀' + k₀ * P''
    have hunit : IsUnit (P'' : ZMod m') := (ZMod.isUnit_iff_coprime P'' m').mpr hcop_m'P''.symm
    let k₀ : ℕ := (-(u₀' : ZMod m') * (hunit.unit⁻¹ : (ZMod m')ˣ)).val
    have hk₀_lt : k₀ < m' := by
      have : NeZero m' := ⟨hm'_pos.ne'⟩
      exact ZMod.val_lt _
    have hk₀_dvd : m' ∣ u₀' + k₀ * P'' := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      have : NeZero m' := ⟨hm'_pos.ne'⟩
      have hval : (k₀ : ZMod m') = -(u₀' : ZMod m') * (hunit.unit⁻¹ : (ZMod m')ˣ) :=
        ZMod.natCast_zmod_val _
      rw [hval]
      have hcancel : ((hunit.unit⁻¹ : (ZMod m')ˣ) : ZMod m') * (P'' : ZMod m') = 1 :=
        hunit.unit.inv_mul
      rw [mul_assoc, hcancel, mul_one, add_neg_cancel]
    let a₀ := (u₀' + k₀ * P'') / m'
    have ha₀_eq : m' * a₀ = u₀' + k₀ * P'' := Nat.mul_div_cancel' hk₀_dvd
    -- Map each valid k ∈ Icc 1 P to t = k / m' ∈ range (P + 1)
    let F_good := (Icc 1 P).filter (fun k =>
      d * m ∣ r + k * P + j ∧ ((r + k * P + j) / (d * m)).Prime)
    let T_sieve := (range (P + 1)).filter (fun t => ∀ q ∈ Q, ¬ q ∣ a₀ + t * P'')
    have hcard_le : F_good.card ≤ T_sieve.card := by
      refine Finset.card_le_card_of_injOn (fun k => k / m') ?_ ?_
      · intro k hk
        simp only [F_good, mem_coe, mem_filter, mem_Icc] at hk
        obtain ⟨⟨hk1, hkP⟩, hdvd, hprime⟩ := hk
        have h1 : r + k * P + j = d * (u₀ + k * P') := by
          rw [mul_add, hu₀_eq, show d * (k * P') = k * (d * P') by ring, hP'_eq]; ring
        rw [h1] at hdvd
        have hm_dvd : m ∣ u₀ + k * P' := (Nat.mul_dvd_mul_iff_left hd_pos).mp hdvd
        have h2 : u₀ + k * P' = g * (u₀' + k * P'') := by
          rw [mul_add, hu₀'_eq, show g * (k * P'') = k * (g * P'') by ring, hP''_eq]
        rw [← hm_eq, h2] at hm_dvd
        have hm'_dvd : m' ∣ u₀' + k * P'' := (Nat.mul_dvd_mul_iff_left hg_pos).mp hm_dvd
        have hk_mod : k % m' = k₀ := by
          have hz1 : ((u₀' + k * P'' : ℕ) : ZMod m') = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hm'_dvd
          have hz2 : ((u₀' + k₀ * P'' : ℕ) : ZMod m') = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hk₀_dvd
          push_cast at hz1 hz2
          have hdiff : ((k : ZMod m') - (k₀ : ZMod m')) * (P'' : ZMod m') = 0 := by
            linear_combination hz1 - hz2
          have hkeq : (k : ZMod m') = (k₀ : ZMod m') := by
            have hinv : ((k : ZMod m') - (k₀ : ZMod m')) = 0 := by
              have hcancel : (P'' : ZMod m') * ((hunit.unit⁻¹ : (ZMod m')ˣ) : ZMod m') = 1 :=
                hunit.unit.mul_inv
              have hmul := congrArg (fun x : ZMod m' => x * ((hunit.unit⁻¹ : (ZMod m')ˣ) : ZMod m')) hdiff
              simpa [mul_assoc, hcancel] using hmul
            exact sub_eq_zero.mp hinv
          have : NeZero m' := ⟨hm'_pos.ne'⟩
          have hv := congrArg ZMod.val hkeq
          rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk₀_lt] at hv
        have hk_eq : k = k₀ + (k / m') * m' := by
          have := Nat.div_add_mod k m'
          rw [hk_mod] at this
          linarith
        have hquot_eq : (r + k * P + j) / (d * m) = a₀ + (k / m') * P'' := by
          have hdm_pos : 0 < d * m := mul_pos hd_pos hm_pos
          apply Nat.div_eq_of_eq_mul_left hdm_pos
          calc
            r + k * P + j = d * (g * (u₀' + k * P'')) := by rw [h1, h2]
            _ = d * (g * (u₀' + k₀ * P'' + (k / m') * m' * P'')) := by
                conv_lhs => rw [hk_eq]
                ring
            _ = d * (g * (m' * a₀ + (k / m') * m' * P'')) := by rw [ha₀_eq]
            _ = (a₀ + (k / m') * P'') * (d * (g * m')) := by ring
            _ = (a₀ + (k / m') * P'') * (d * m) := by rw [hm_eq]
        have hquot_gt_Z : Z < a₀ + (k / m') * P'' := by
          rw [← hquot_eq]
          have hge : P ≤ r + k * P + j := by
            have : 1 * P ≤ k * P := Nat.mul_le_mul_right P hk1
            omega
          exact hquot_gt.trans_le (Nat.div_le_div_right hge)
        simp only [T_sieve, mem_coe, mem_filter, mem_range]
        refine ⟨Nat.lt_succ_of_le ((Nat.div_le_self k m').trans hkP), fun q hq hqdvd => ?_⟩
        rw [← hquot_eq] at hqdvd
        have hq_prime : q.Prime := (mem_filter.mp hq).2
        have hq_le_Z : q ≤ Z := (mem_Ioc.mp (mem_filter.mp hq).1).2
        have heq := (Nat.prime_dvd_prime_iff_eq hq_prime hprime).mp hqdvd
        rw [← hquot_eq] at hquot_gt_Z
        omega
      · intro k₁ hk₁ k₂ hk₂ heq
        simp only [F_good, mem_coe, mem_filter, mem_Icc] at hk₁ hk₂
        have hmod : ∀ k, d * m ∣ r + k * P + j → k % m' = k₀ := by
          intro k hdvd
          have h1 : r + k * P + j = d * (u₀ + k * P') := by
            rw [mul_add, hu₀_eq, show d * (k * P') = k * (d * P') by ring, hP'_eq]; ring
          rw [h1] at hdvd
          have hm_dvd : m ∣ u₀ + k * P' := (Nat.mul_dvd_mul_iff_left hd_pos).mp hdvd
          have h2 : u₀ + k * P' = g * (u₀' + k * P'') := by
            rw [mul_add, hu₀'_eq, show g * (k * P'') = k * (g * P'') by ring, hP''_eq]
          rw [← hm_eq, h2] at hm_dvd
          have hm'_dvd : m' ∣ u₀' + k * P'' := (Nat.mul_dvd_mul_iff_left hg_pos).mp hm_dvd
          have hz1 : ((u₀' + k * P'' : ℕ) : ZMod m') = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hm'_dvd
          have hz2 : ((u₀' + k₀ * P'' : ℕ) : ZMod m') = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hk₀_dvd
          push_cast at hz1 hz2
          have hdiff : ((k : ZMod m') - (k₀ : ZMod m')) * (P'' : ZMod m') = 0 := by
            linear_combination hz1 - hz2
          have hkeq : (k : ZMod m') = (k₀ : ZMod m') := by
            have hinv : ((k : ZMod m') - (k₀ : ZMod m')) = 0 := by
              have hcancel : (P'' : ZMod m') * ((hunit.unit⁻¹ : (ZMod m')ˣ) : ZMod m') = 1 :=
                hunit.unit.mul_inv
              have hmul := congrArg (fun x : ZMod m' => x * ((hunit.unit⁻¹ : (ZMod m')ˣ) : ZMod m')) hdiff
              simpa [mul_assoc, hcancel] using hmul
            exact sub_eq_zero.mp hinv
          have : NeZero m' := ⟨hm'_pos.ne'⟩
          have hv := congrArg ZMod.val hkeq
          rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk₀_lt] at hv
        have hm1 := hmod k₁ hk₁.2.1
        have hm2 := hmod k₂ hk₂.2.1
        have hd1 := Nat.div_add_mod k₁ m'
        have hd2 := Nat.div_add_mod k₂ m'
        dsimp only at heq
        rw [heq, hm1, ← hm2] at hd1
        linarith
    have hP''_cop : ∀ q ∈ Q, ¬ q ∣ P'' := by
      intro q hq hqd
      apply hP_cop q hq
      have h1 : P'' ∣ P' := ⟨g, by rw [mul_comm, hP''_eq]⟩
      have h2 : P' ∣ P := ⟨d, by rw [mul_comm, hP'_eq]⟩
      exact hqd.trans (h1.trans h2)
    have hsieve := selberg_sieve_ap (P + 1) Z a₀ P'' Q hZ (fun q hq => (mem_filter.mp hq).2) hP''_cop
    exact (Nat.cast_le.mpr hcard_le).trans hsieve

/-- Existence of a sufficiently large parameter `z` satisfying all asymptotic bounds. -/
private lemma exists_good_z (c₁ : ℝ) (hc₁_ge1 : 1 ≤ c₁) (N₀ : ℕ) (C_inv : ℝ) (_hC_inv_pos : 0 < C_inv)
    (hC_inv : ∀ z : ℕ, 4 ≤ z →
      ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
        5 * log (log (z : ℝ)) + C_inv) :
    let H_fn : ℕ → ℕ := fun z => ⌊5 * c₁ * (z : ℝ)⌋₊ + 1
    let A_fn : ℕ → ℕ := fun z => ⌊(log (z : ℝ)) ^ 12⌋₊
    let y_fn : ℕ → ℕ := fun z => ⌊exp (sqrt (log (z : ℝ)))⌋₊
    let C_sieve : ℝ := 200 * exp (2 * C_inv)
    ∃ z : ℕ,
      ((z : ℝ) / 2 ≤ log (primorial z : ℝ) ∧ log (primorial z : ℝ) ≤ 2 * (z : ℝ)) ∧
      ((z : ℝ) / (10 * log (z : ℝ)) ≤ (((Ioc (z / 4) z).filter Nat.Prime).card : ℝ)) ∧
      ((((Icc 1 (H_fn z)).filter (fun j => ∀ p ∈ j.primeFactors, p ≤ y_fn z)).card : ℝ) ≤
        (z : ℝ) / (20 * log (z : ℝ))) ∧
      (4 ≤ A_fn z ∧ A_fn z < y_fn z ∧ y_fn z < z / 4) ∧
      (log (3000 * c₁ * (1 + c₁)) ≤
        ∑ p ∈ (Ioc (A_fn z) (y_fn z)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧
      ((N₀ : ℝ) ≤ exp ((z : ℝ) / 2) ∧
        (16 : ℝ) ≤ exp ((z : ℝ) / 2) ∧
        (2000 * c₁ * (z : ℝ) ^ 3) < exp ((z : ℝ) / 8) / 2 ∧
        (2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2) < exp ((z : ℝ) / 2) ∧
        (z : ℝ) ^ 2 ≤ exp ((z : ℝ) / 4) ∧
        1000 * c₁ * C_sieve < log (z : ℝ)) ∧
      ((Nat.primeCounting (H_fn z) : ℝ) ≤ 1.5 * (H_fn z : ℝ) / log (H_fn z : ℝ)) ∧
      10000 ≤ z := by
  intro H_fn A_fn y_fn C_sieve
  -- Collect asymptotic conditions on z
  have hH_tendsto : Tendsto H_fn atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b; refine ⟨b, fun z hz => ?_⟩
    have : (b : ℝ) ≤ 5 * c₁ * (z : ℝ) := by
      have : (b : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
      nlinarith
    have := Nat.le_floor this
    dsimp only [H_fn]; omega
  -- Smooth count / (z / log z) → 0
  have hsmooth_small : ∀ᶠ z : ℕ in atTop,
      (((Icc 1 (H_fn z)).filter (fun j => ∀ p ∈ j.primeFactors, p ≤ y_fn z)).card : ℝ) ≤
        (z : ℝ) / (20 * log (z : ℝ)) := by
    -- log(H_fn z) / (2 * log(y_fn z)) ≥ (1/2) * sqrt(log z), while 4 * (5 log log y + C) ≤ 20 log log z + C'
    have ht : Tendsto (fun z : ℕ =>
        (6 * c₁) * (16 * exp (4 * C_inv)) * (20 * log (z : ℝ)) *
          exp (-(sqrt (log (z : ℝ)) / 2) + 20 * log (log (z : ℝ)))) atTop (nhds 0) := by
      have hlog : Tendsto (fun z : ℕ => log (z : ℝ)) atTop atTop :=
        tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      have hcore : Tendsto (fun t : ℝ =>
          (6 * c₁) * (16 * exp (4 * C_inv)) * (20 * t) *
            exp (-(sqrt t / 2) + 20 * log t)) atTop (nhds 0) := by
        have hdom : ∀ᶠ t : ℝ in atTop,
            (6 * c₁) * (16 * exp (4 * C_inv)) * (20 * t) *
              exp (-(sqrt t / 2) + 20 * log t) ≤
              exp (-(sqrt t / 4)) := by
          have hlim : Tendsto (fun t : ℝ =>
              (log ((6 * c₁) * (16 * exp (4 * C_inv)) * 20) + 21 * log t) / sqrt t)
              atTop (nhds 0) := by
            have h1 : Tendsto (fun t : ℝ => log ((6 * c₁) * (16 * exp (4 * C_inv)) * 20) / sqrt t)
                atTop (nhds 0) :=
              tendsto_const_nhds.div_atTop
                ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr fun t => by rw [sqrt_eq_rpow])
            have h2 : Tendsto (fun t : ℝ => 21 * log t / sqrt t) atTop (nhds 0) := by
              have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero.const_mul 21
              simpa using hl.congr' (by
                filter_upwards [eventually_gt_atTop 0] with t _; rw [sqrt_eq_rpow]; ring)
            simpa [add_div] using h1.add h2
          filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
            eventually_gt_atTop (1 : ℝ)] with t ht ht1
          have hsq : 0 < sqrt t := sqrt_pos.mpr (by linarith)
          have hlt := (div_lt_iff₀ hsq).mp ht
          have hK_pos : 0 < (6 * c₁) * (16 * exp (4 * C_inv)) * 20 := by positivity
          have heq : (6 * c₁) * (16 * exp (4 * C_inv)) * (20 * t) *
              exp (-(sqrt t / 2) + 20 * log t) =
              exp (log ((6 * c₁) * (16 * exp (4 * C_inv)) * 20) + 21 * log t - sqrt t / 2) := by
            calc (6 * c₁) * (16 * exp (4 * C_inv)) * (20 * t) *
                  exp (-(sqrt t / 2) + 20 * log t)
                = ((6 * c₁) * (16 * exp (4 * C_inv)) * 20) * t *
                  exp (-(sqrt t / 2) + 20 * log t) := by ring
              _ = exp (log ((6 * c₁) * (16 * exp (4 * C_inv)) * 20)) *
                  exp (log t) * exp (-(sqrt t / 2) + 20 * log t) := by
                    rw [exp_log hK_pos, exp_log (by linarith : (0 : ℝ) < t)]
              _ = exp (log ((6 * c₁) * (16 * exp (4 * C_inv)) * 20) + 21 * log t - sqrt t / 2) := by
                    rw [← exp_add, ← exp_add]; congr 1; ring
          rw [heq]
          exact exp_le_exp.mpr (by linarith)
        have hexp0 : Tendsto (fun t : ℝ => exp (-(sqrt t / 4))) atTop (nhds 0) := by
          have h1 : Tendsto (fun t : ℝ => -(sqrt t / 4)) atTop atBot :=
            Filter.tendsto_neg_atTop_atBot.comp
              (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr fun t => by
                rw [sqrt_eq_rpow]).atTop_div_const (by norm_num : (0 : ℝ) < 4))
          exact Real.tendsto_exp_atBot.comp h1
        exact squeeze_zero' (by filter_upwards [eventually_gt_atTop 0] with t ht; positivity) hdom hexp0
      exact hcore.comp hlog
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      eventually_ge_atTop 10000] with z hz hz10000
    have hzR : (10000 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz10000
    have hlogz : 7 < log (z : ℝ) := by
      have he : exp 1 < 3 := by linarith [exp_one_lt_d9]
      have h7 : exp 7 = (exp 1) ^ 7 := by rw [← exp_nat_mul]; norm_num
      have h1 : exp 7 < 10000 := by
        rw [h7]
        calc (exp 1) ^ 7 < 3 ^ 7 := pow_lt_pow_left₀ he (exp_pos 1).le (by norm_num)
          _ < 10000 := by norm_num
      exact (lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
    have hH_ge : (z : ℝ) ≤ (H_fn z : ℝ) := by
      have h1 : (z : ℝ) ≤ 5 * c₁ * (z : ℝ) := by nlinarith
      have h2 := Nat.lt_floor_add_one (5 * c₁ * (z : ℝ))
      dsimp only [H_fn]; push_cast; linarith
    have hH_le : (H_fn z : ℝ) ≤ 6 * c₁ * (z : ℝ) := by
      have h1 := Nat.floor_le (show (0 : ℝ) ≤ 5 * c₁ * (z : ℝ) by positivity)
      dsimp only [H_fn]; push_cast; nlinarith
    have hy_ge4 : 4 ≤ y_fn z := by
      have hsq : (2 : ℝ) ≤ sqrt (log (z : ℝ)) := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      have hexp2 : (4 : ℝ) ≤ exp 2 := by
        have : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
        have h2 : exp 2 = (exp 1) ^ 2 := by rw [← exp_nat_mul]; norm_num
        rw [h2]; nlinarith
      exact Nat.le_floor (by push_cast; exact hexp2.trans (exp_le_exp.mpr hsq))
    have hy_le : (y_fn z : ℝ) ≤ exp (sqrt (log (z : ℝ))) := Nat.floor_le (by positivity)
    have hlogy_pos : 0 < log (y_fn z : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < y_fn z))
    have hlogy_le : log (y_fn z : ℝ) ≤ sqrt (log (z : ℝ)) := by
      have h1 := log_le_log (by exact_mod_cast (by omega : 0 < y_fn z)) hy_le
      rwa [log_exp] at h1
    have hsm := smooth_card_le (H_fn z) (y_fn z) (by dsimp only [H_fn]; omega) hy_ge4
    have hinv_y := hC_inv (y_fn z) hy_ge4
    have hlogH_ge : log (z : ℝ) ≤ log (H_fn z : ℝ) := log_le_log (by linarith) hH_ge
    have hexp_main : exp (-log (H_fn z : ℝ) / (2 * log (y_fn z : ℝ))) ≤
        exp (-(sqrt (log (z : ℝ)) / 2)) := by
      apply exp_le_exp.mpr
      have hdiv : sqrt (log (z : ℝ)) / 2 ≤ log (H_fn z : ℝ) / (2 * log (y_fn z : ℝ)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have hsq2 : sqrt (log (z : ℝ)) * sqrt (log (z : ℝ)) = log (z : ℝ) :=
          Real.mul_self_sqrt (by linarith)
        nlinarith [sqrt_nonneg (log (z : ℝ))]
      rw [neg_div]; linarith
    have hlogy_le_logz : log (log (y_fn z : ℝ)) ≤ log (log (z : ℝ)) := by
      apply log_le_log hlogy_pos
      have hsq_le : sqrt (log (z : ℝ)) ≤ log (z : ℝ) := by
        rw [sqrt_le_left (by linarith)]; nlinarith
      exact hlogy_le.trans hsq_le
    have hexp_inv : exp (4 * ∑ p ∈ (Icc 1 (y_fn z)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
        exp (4 * C_inv) * exp (20 * log (log (z : ℝ))) := by
      rw [← exp_add]
      exact exp_le_exp.mpr (by linarith)
    have hcomb :
        (H_fn z : ℝ) * exp (-log (H_fn z : ℝ) / (2 * log (y_fn z : ℝ))) * 16 *
            exp (4 * ∑ p ∈ (Icc 1 (y_fn z)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
          (z : ℝ) / (20 * log (z : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      calc
        (H_fn z : ℝ) * exp (-log (H_fn z : ℝ) / (2 * log (y_fn z : ℝ))) * 16 *
            exp (4 * ∑ p ∈ (Icc 1 (y_fn z)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) *
            (20 * log (z : ℝ))
          ≤ (6 * c₁ * (z : ℝ)) * exp (-(sqrt (log (z : ℝ)) / 2)) * 16 *
              (exp (4 * C_inv) * exp (20 * log (log (z : ℝ)))) *
              (20 * log (z : ℝ)) := by
            gcongr
        _ = (z : ℝ) * ((6 * c₁) * (16 * exp (4 * C_inv)) * (20 * log (z : ℝ)) *
              exp (-(sqrt (log (z : ℝ)) / 2) + 20 * log (log (z : ℝ)))) := by
            rw [exp_add]; ring
        _ ≤ (z : ℝ) * 1 := mul_le_mul_of_nonneg_left hz.le (by positivity)
        _ = (z : ℝ) := mul_one _
    exact hsm.trans hcomb
  -- Now gather all eventually-true conditions on z
  have hcond_A_y : ∀ᶠ z : ℕ in atTop,
      4 ≤ A_fn z ∧ A_fn z < y_fn z ∧ y_fn z < z / 4 := by
    have hlog : Tendsto (fun z : ℕ => log (z : ℝ)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h1 : ∀ᶠ z : ℕ in atTop, (4 : ℝ) ≤ (log (z : ℝ)) ^ 12 := by
      filter_upwards [hlog.eventually_ge_atTop 4] with z hz
      have : (4 : ℝ) ^ 1 ≤ (log (z : ℝ)) ^ 12 := by
        calc (4 : ℝ) ^ 1 ≤ (4 : ℝ) ^ 12 := pow_le_pow_right₀ (by norm_num) (by norm_num)
          _ ≤ (log (z : ℝ)) ^ 12 := pow_le_pow_left₀ (by norm_num) hz 12
      simpa using this
    have h2 : ∀ᶠ z : ℕ in atTop, (log (z : ℝ)) ^ 12 + 2 ≤ exp (sqrt (log (z : ℝ))) := by
      have hcore : ∀ᶠ t : ℝ in atTop, t ^ 12 + 2 ≤ exp (sqrt t) := by
        have hlim : Tendsto (fun t : ℝ => (12 * log t + 1) / sqrt t) atTop (nhds 0) := by
          have ha := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero.const_mul 12
          have hb : Tendsto (fun t : ℝ => (1 : ℝ) / sqrt t) atTop (nhds 0) :=
            tendsto_const_nhds.div_atTop
              ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr fun t => by rw [sqrt_eq_rpow])
          simpa [add_div] using (ha.congr' (by filter_upwards [eventually_gt_atTop 0] with t _; rw [sqrt_eq_rpow]; ring)).add hb
        filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
          eventually_gt_atTop (2 : ℝ)] with t ht ht2
        have hsq : 0 < sqrt t := sqrt_pos.mpr (by linarith)
        have hlt := (div_lt_iff₀ hsq).mp ht
        have hle : t ^ 12 + 2 ≤ 2 * t ^ 12 := by
          have : (2 : ℝ) ≤ t ^ 12 := by
            calc (2 : ℝ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ 12 := pow_le_pow_right₀ (by norm_num) (by norm_num)
              _ ≤ t ^ 12 := pow_le_pow_left₀ (by norm_num) ht2.le 12
          linarith
        have h2e : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
        have ht12 : t ^ 12 = exp (12 * log t) := by
          rw [← rpow_natCast, rpow_def_of_pos (by linarith)]; congr 1; ring
        calc t ^ 12 + 2 ≤ 2 * t ^ 12 := hle
          _ ≤ exp 1 * exp (12 * log t) := by rw [ht12]; gcongr
          _ = exp (12 * log t + 1) := by rw [← exp_add]; ring_nf
          _ ≤ exp (sqrt t) := exp_le_exp.mpr (by linarith)
      exact hlog.eventually hcore
    have h3 : ∀ᶠ z : ℕ in atTop, exp (sqrt (log (z : ℝ))) + 4 ≤ (z : ℝ) / 4 := by
      have hcore : ∀ᶠ t : ℝ in atTop, exp (sqrt t) + 4 ≤ exp t / 4 := by
        filter_upwards [eventually_ge_atTop (100 : ℝ)] with t ht
        have hsq : sqrt t ≤ t / 2 := by
          rw [sqrt_le_left (by linarith)]; nlinarith
        have hexp_half : exp (t / 2) ≥ 100 := by
          have h1 : (50 : ℝ) ≤ t / 2 := by linarith
          have h2 : (50 : ℝ) + 1 ≤ exp (t / 2) := (by linarith : (50 : ℝ) + 1 ≤ t / 2 + 1).trans (add_one_le_exp _)
          have h3 : exp (t / 2) = (exp (t / 4)) ^ 2 := by rw [← exp_nat_mul]; congr 1; ring
          have h4 : (25 : ℝ) ≤ exp (t / 4) := by linarith [add_one_le_exp (t / 4)]
          rw [h3]; nlinarith
        have hprod : exp t = exp (t / 2) * exp (t / 2) := by rw [← exp_add]; congr 1; ring
        have hle1 : exp (sqrt t) ≤ exp (t / 2) := exp_le_exp.mpr hsq
        nlinarith [exp_pos (t / 2)]
      filter_upwards [hlog.eventually hcore, eventually_ge_atTop 2] with z hz hz2
      rwa [exp_log (by exact_mod_cast (by omega : 0 < z))] at hz
    filter_upwards [h1, h2, h3, eventually_ge_atTop 100] with z h1z h2z h3z hz100
    refine ⟨Nat.le_floor h1z, ?_, ?_⟩
    · have hA : (A_fn z : ℝ) ≤ (log (z : ℝ)) ^ 12 := Nat.floor_le (by positivity)
      have hy : exp (sqrt (log (z : ℝ))) - 1 < (y_fn z : ℝ) := Nat.sub_one_lt_floor _
      have : (A_fn z : ℝ) < (y_fn z : ℝ) := by linarith
      exact_mod_cast this
    · have hy : (y_fn z : ℝ) ≤ exp (sqrt (log (z : ℝ))) := Nat.floor_le (by positivity)
      have hq : (z : ℝ) / 4 - 1 < ((z / 4 : ℕ) : ℝ) := by
        have : z < 4 * (z / 4 + 1) := by omega
        have hR : (z : ℝ) < 4 * ((z / 4 : ℕ) + 1 : ℝ) := by exact_mod_cast this
        linarith
      have : (y_fn z : ℝ) < ((z / 4 : ℕ) : ℝ) := by linarith
      exact_mod_cast this
  -- Greedy sieve exponent beats 3000 * c₁ * (1 + c₁)
  have hgreedy_big : ∀ᶠ z : ℕ in atTop,
      log (3000 * c₁ * (1 + c₁)) ≤
        ∑ p ∈ (Ioc (A_fn z) (y_fn z)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
    sum_inv_primes_Ioc_tendsto.eventually_ge_atTop _
  -- Exponential dominance of P = primorial z ≥ exp(z/2) over polynomials in z
  have hpoly_vs_exp : ∀ᶠ z : ℕ in atTop,
      (N₀ : ℝ) ≤ exp ((z : ℝ) / 2) ∧
      (16 : ℝ) ≤ exp ((z : ℝ) / 2) ∧
      (2000 * c₁ * (z : ℝ) ^ 3) < exp ((z : ℝ) / 8) / 2 ∧
      (2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2) < exp ((z : ℝ) / 2) ∧
      (z : ℝ) ^ 2 ≤ exp ((z : ℝ) / 4) ∧
      1000 * c₁ * C_sieve < log (z : ℝ) := by
    have hpow_exp : ∀ (C k : ℝ) (hk : 0 < k) (n : ℕ),
        ∀ᶠ z : ℕ in atTop, C * (z : ℝ) ^ n < exp ((z : ℝ) / k) := by
      intro C k hk n
      have hlim : Tendsto (fun x : ℝ => C * x ^ n / exp (x / k)) atTop (nhds 0) := by
        have h := ((isLittleO_pow_exp_atTop (n := n)).tendsto_div_nhds_zero.comp
          (tendsto_id.atTop_div_const hk)).const_mul (C * k ^ n)
        simpa using h.congr fun x => by simp only [Function.comp_apply, id_eq]; rw [div_pow]; field_simp [hk.ne']
      filter_upwards [(hlim.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds one_pos)] with z hz
      exact (div_lt_one (exp_pos _)).mp hz
    have h1 := (tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))).eventually_ge_atTop (N₀ : ℝ)
    have h2 := (tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))).eventually_ge_atTop (16 : ℝ)
    have h3 : ∀ᶠ z : ℕ in atTop, (2000 * c₁ * (z : ℝ) ^ 3) < exp ((z : ℝ) / 8) / 2 := by
      filter_upwards [hpow_exp (4000 * c₁) 8 (by norm_num) 3] with z hz; linarith
    have h4 : ∀ᶠ z : ℕ in atTop, (2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2) < exp ((z : ℝ) / 2) := by
      filter_upwards [hpow_exp (720000 * c₁ ^ 2) 2 (by norm_num) 4] with z hz; linarith
    have h5 : ∀ᶠ z : ℕ in atTop, (z : ℝ) ^ 2 ≤ exp ((z : ℝ) / 4) := by
      filter_upwards [hpow_exp 1 4 (by norm_num) 2] with z hz; linarith
    have h6 : ∀ᶠ z : ℕ in atTop, 1000 * c₁ * C_sieve < log (z : ℝ) :=
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
    filter_upwards [h1, h2, h3, h4, h5, h6] with z a1 a2 a3 a4 a5 a6
    exact ⟨a1, a2, a3, a4, a5, a6⟩
  -- Pick a single z satisfying all conditions!
  have hall := primorial_log_bounds.and
    (primes_in_quarter_ge.and
    (hsmooth_small.and
    (hcond_A_y.and
    (hgreedy_big.and
    (hpoly_vs_exp.and
    ((hH_tendsto.eventually eventually_pi_bounds).and
    (eventually_ge_atTop 10000)))))))
  obtain ⟨z, ⟨hP_lb, hP_ub⟩, hP3_ge, hsm_le, ⟨hA4, hAy, hyq⟩, hgr_ge,
    hpoly, ⟨_, hpiH_ub⟩, hz10000⟩ := hall.exists
  exact ⟨z, ⟨hP_lb, hP_ub⟩, hP3_ge, hsm_le, ⟨hA4, hAy, hyq⟩, hgr_ge, hpoly, hpiH_ub, hz10000⟩

/-- Construct a CRT residue `r < primorial z` so that every `j ∈ [1, H]` has a prime divisor
`d ∈ (A, z]` dividing `r + j`. -/
private lemma build_crt_residue (c₁ : ℝ) (hc₁_ge1 : 1 ≤ c₁) (z H A y : ℕ)
    (hz10000 : 10000 ≤ z)
    (hlogz_ge7 : 7 < log (z : ℝ))
    (hH_ge_z : (z : ℝ) ≤ (H : ℝ))
    (hH_le_6cz : (H : ℝ) ≤ 6 * c₁ * (z : ℝ))
    (_hA4 : 4 ≤ A) (hAy : A < y) (hyq : y < z / 4)
    (hsm_le : (((Icc 1 H).filter (fun j => ∀ p ∈ j.primeFactors, p ≤ y)).card : ℝ) ≤
      (z : ℝ) / (20 * log (z : ℝ)))
    (hpiH_ub : (Nat.primeCounting H : ℝ) ≤ 1.5 * (H : ℝ) / log (H : ℝ))
    (hgr_ge : log (3000 * c₁ * (1 + c₁)) ≤
      ∑ p ∈ (Ioc A y).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
    (hP3_ge : (z : ℝ) / (10 * log (z : ℝ)) ≤ (((Ioc (z / 4) z).filter Nat.Prime).card : ℝ)) :
    ∃ r : ℕ, r < primorial z ∧
      ∀ j ∈ Icc 1 H, ∃ d ∈ (Ioc A z).filter Nat.Prime, d ∣ r + j := by
  let P := primorial z
  have hzR : (10000 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz10000
  -- Step 1: Build CRT residue r < P so every j ∈ Icc 1 H has a prime divisor d_j ∈ Ioc A z dividing r + j
  let P₁ := (Ioc A y).filter Nat.Prime
  let P₂ := (Ioc y (z / 4)).filter Nat.Prime
  let P₃ := (Ioc (z / 4) z).filter Nat.Prime
  let S_surv := (Icc 1 H).filter (fun j => ∀ p ∈ P₂, ¬ p ∣ j)
  have hS_surv_card : (S_surv.card : ℝ) ≤ 300 * c₁ * (1 + c₁) * (z : ℝ) / log (z : ℝ) := by
    let S_sm := (Icc 1 H).filter (fun j => ∀ p ∈ j.primeFactors, p ≤ y)
    let K_big := ⌊24 * c₁⌋₊ + 1
    let S_big := (Icc 1 K_big ×ˢ (Icc 1 H).filter Nat.Prime).image (fun x : ℕ × ℕ => x.1 * x.2)
    have hsub_surv : S_surv ⊆ S_sm ∪ S_big := by
      intro j hj
      simp only [S_surv, mem_filter, mem_Icc] at hj
      by_cases hsm : ∀ p ∈ j.primeFactors, p ≤ y
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr hj.1, hsm⟩)
      · push Not at hsm
        obtain ⟨p, hp_mem, hp_gt⟩ := hsm
        have hp_prime := Nat.prime_of_mem_primeFactors hp_mem
        have hp_dvd : p ∣ j := Nat.dvd_of_mem_primeFactors hp_mem
        have hp_gt_q : z / 4 < p := by
          by_contra hle
          push Not at hle
          exact hj.2 p (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp_gt, hle⟩, hp_prime⟩) hp_dvd
        have hp_le_H : p ≤ H := (Nat.le_of_dvd (by omega) hp_dvd).trans hj.1.2
        let q := j / p
        have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp_prime.pos
        have hq_le : q ≤ K_big := by
          have hmul : q * p ≤ H := by rw [Nat.div_mul_cancel hp_dvd]; exact hj.1.2
          have hqR : (q : ℝ) * ((z : ℝ) / 4) ≤ 6 * c₁ * (z : ℝ) := by
            have hpR : (z : ℝ) / 4 < (p : ℝ) := by
              have : z < 4 * (z / 4 + 1) := by omega
              have h1 : (z : ℝ) < 4 * ((z / 4 + 1 : ℕ) : ℝ) := by exact_mod_cast this
              have h2 : ((z / 4 + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_gt_q
              linarith
            have hmulR : (q : ℝ) * (p : ℝ) ≤ (H : ℝ) := by exact_mod_cast hmul
            nlinarith [show (0 : ℝ) < (q : ℝ) by exact_mod_cast hq_pos]
          have hq24 : (q : ℝ) ≤ 24 * c₁ := by nlinarith
          have : q ≤ ⌊24 * c₁⌋₊ := Nat.le_floor hq24
          omega
        refine mem_union_right _ (mem_image.mpr ?_)
        refine ⟨(q, p), mem_product.mpr ⟨mem_Icc.mpr ⟨hq_pos, hq_le⟩,
          mem_filter.mpr ⟨mem_Icc.mpr ⟨hp_prime.one_le, hp_le_H⟩, hp_prime⟩⟩, ?_⟩
        exact Nat.div_mul_cancel hp_dvd
    have hcard_big : (S_big.card : ℝ) ≤ (K_big : ℝ) * (Nat.primeCounting H : ℝ) := by
      have h1 : S_big.card ≤ (Icc 1 K_big ×ˢ (Icc 1 H).filter Nat.Prime).card :=
        card_image_le
      rw [card_product, Nat.card_Icc] at h1
      have hpi : ((Icc 1 H).filter Nat.Prime).card = Nat.primeCounting H := by
        rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
        congr 1; ext p; simp only [mem_filter, mem_Icc, mem_range]
        constructor
        · intro ⟨⟨_, h2⟩, hp⟩; exact ⟨Nat.lt_succ_of_le h2, hp⟩
        · intro ⟨h1, hp⟩; exact ⟨⟨hp.one_le, Nat.lt_succ_iff.mp h1⟩, hp⟩
      rw [hpi, show K_big + 1 - 1 = K_big by omega] at h1
      exact_mod_cast h1
    have hK_le : (K_big : ℝ) ≤ 25 * c₁ := by
      have h1 := Nat.floor_le (show (0 : ℝ) ≤ 24 * c₁ by positivity)
      dsimp only [K_big]; push_cast; linarith
    have hlogH_ge : log (z : ℝ) ≤ log (H : ℝ) := log_le_log (by linarith) hH_ge_z
    have hpiH_le : (Nat.primeCounting H : ℝ) ≤ 9 * c₁ * (z : ℝ) / log (z : ℝ) := by
      calc
        (Nat.primeCounting H : ℝ) ≤ 1.5 * (H : ℝ) / log (H : ℝ) := hpiH_ub
        _ ≤ (1.5 * (6 * c₁ * (z : ℝ))) / log (z : ℝ) := by
            exact div_le_div₀ (by positivity) (by nlinarith) (by linarith) hlogH_ge
        _ = 9 * c₁ * (z : ℝ) / log (z : ℝ) := by ring
    have hcard_union : (S_surv.card : ℝ) ≤ (S_sm.card : ℝ) + (S_big.card : ℝ) := by
      have := (Finset.card_le_card hsub_surv).trans (Finset.card_union_le S_sm S_big)
      exact_mod_cast this
    have hbig_bound : (S_big.card : ℝ) ≤ 225 * c₁ * c₁ * (z : ℝ) / log (z : ℝ) := by
      calc
        (S_big.card : ℝ) ≤ (K_big : ℝ) * (Nat.primeCounting H : ℝ) := hcard_big
        _ ≤ (25 * c₁) * (9 * c₁ * (z : ℝ) / log (z : ℝ)) := by gcongr
        _ = 225 * c₁ * c₁ * (z : ℝ) / log (z : ℝ) := by ring
    have hsm_bound : (S_sm.card : ℝ) ≤ (z : ℝ) / log (z : ℝ) := by
      have hpos : 0 ≤ (z : ℝ) / log (z : ℝ) := by positivity
      calc (S_sm.card : ℝ) ≤ (z : ℝ) / (20 * log (z : ℝ)) := hsm_le
        _ = (1 / 20) * ((z : ℝ) / log (z : ℝ)) := by ring
        _ ≤ 1 * ((z : ℝ) / log (z : ℝ)) := by nlinarith
        _ = (z : ℝ) / log (z : ℝ) := one_mul _
    have hpos : 0 ≤ (z : ℝ) / log (z : ℝ) := by positivity
    have hc_ineq : 1 + 225 * c₁ * c₁ ≤ 300 * c₁ * (1 + c₁) := by nlinarith
    calc
      (S_surv.card : ℝ) ≤ (S_sm.card : ℝ) + (S_big.card : ℝ) := hcard_union
      _ ≤ (z : ℝ) / log (z : ℝ) + 225 * c₁ * c₁ * (z : ℝ) / log (z : ℝ) := add_le_add hsm_bound hbig_bound
      _ = (1 + 225 * c₁ * c₁) * ((z : ℝ) / log (z : ℝ)) := by ring
      _ ≤ (300 * c₁ * (1 + c₁)) * ((z : ℝ) / log (z : ℝ)) := mul_le_mul_of_nonneg_right hc_ineq hpos
      _ = 300 * c₁ * (1 + c₁) * (z : ℝ) / log (z : ℝ) := by ring
  -- Apply greedy sieving on P₁
  obtain ⟨a₁, ha₁⟩ := greedy_sieve_finset S_surv P₁ (fun p hp => (mem_filter.mp hp).2)
  let S_rem := S_surv.filter (fun j => ∀ p ∈ P₁, ¬ p ∣ j + a₁ p)
  have hS_rem_le_P3 : S_rem.card ≤ P₃.card := by
    have hexp_le : exp (-∑ p ∈ P₁, (1 : ℝ) / (p : ℝ)) ≤ (1 : ℝ) / (3000 * c₁ * (1 + c₁)) := by
      rw [Real.exp_neg, inv_eq_one_div]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have := exp_le_exp.mpr hgr_ge
      rwa [exp_log (by positivity)] at this
    have hleR : (S_rem.card : ℝ) ≤ (P₃.card : ℝ) := by
      calc
        (S_rem.card : ℝ) ≤ (S_surv.card : ℝ) * exp (-∑ p ∈ P₁, (1 : ℝ) / (p : ℝ)) := ha₁
        _ ≤ (300 * c₁ * (1 + c₁) * (z : ℝ) / log (z : ℝ)) * (1 / (3000 * c₁ * (1 + c₁))) := by gcongr
        _ = (z : ℝ) / (10 * log (z : ℝ)) := by
            have hne : c₁ * (1 + c₁) ≠ 0 := by positivity
            field_simp [hne]; ring
        _ ≤ (P₃.card : ℝ) := hP3_ge
    exact_mod_cast hleR
  -- Inject S_rem into P₃
  obtain ⟨φ, hφ_inj⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card S_rem ≤ Fintype.card P₃ by simpa using hS_rem_le_P3)
  let a_crt : ℕ → ℕ := fun p =>
    if p ∈ P₁ then a₁ p
    else if p ∈ P₃ then
      if h : ∃ j : S_rem, (φ j : ℕ) = p then
        (p - ((Classical.choose h : S_rem) : ℕ) % p) % p
      else 0
    else 0
  obtain ⟨r, hr_lt_prod, hr_mod⟩ := crt_finset_primes ((Icc 1 z).filter Nat.Prime)
    (fun p hp => (mem_filter.mp hp).2) a_crt
  have hr_lt_P : r < P := by dsimp only [P]; rwa [primorial_eq_prod_Icc]
  -- Every j ∈ Icc 1 H has a prime divisor d_j ∈ Ioc A z dividing r + j
  have hcover_j : ∀ j ∈ Icc 1 H, ∃ d ∈ (Ioc A z).filter Nat.Prime, d ∣ r + j := by
    intro j hj
    by_cases hP2 : ∃ p ∈ P₂, p ∣ j
    · obtain ⟨p, hp2, hpd⟩ := hP2
      have hp_mem := mem_filter.mp hp2
      have hp_ioc := mem_Ioc.mp hp_mem.1
      have hp_le_z : p ≤ z := hp_ioc.2.trans (Nat.div_le_self z 4)
      have hp_Icc : p ∈ (Icc 1 z).filter Nat.Prime :=
        mem_filter.mpr ⟨mem_Icc.mpr ⟨hp_mem.2.one_le, hp_le_z⟩, hp_mem.2⟩
      have hnot1 : p ∉ P₁ := by
        intro h; have := (mem_Ioc.mp (mem_filter.mp h).1).2; omega
      have hnot3 : p ∉ P₃ := by
        intro h; have := (mem_Ioc.mp (mem_filter.mp h).1).1; omega
      have ha0 : a_crt p = 0 := by simp [a_crt, hnot1, hnot3]
      have hr0 : p ∣ r := by
        have hm := hr_mod p hp_Icc
        rw [ha0] at hm
        exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hm)
      exact ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hp_le_z⟩, hp_mem.2⟩,
        Nat.dvd_add hr0 hpd⟩
    · push Not at hP2
      have hj_surv : j ∈ S_surv := mem_filter.mpr ⟨hj, hP2⟩
      by_cases hP1 : ∃ p ∈ P₁, p ∣ j + a₁ p
      · obtain ⟨p, hp1, hpd⟩ := hP1
        have hp_mem := mem_filter.mp hp1
        have hp_ioc := mem_Ioc.mp hp_mem.1
        have hp_le_z : p ≤ z := hp_ioc.2.trans (hyq.le.trans (Nat.div_le_self z 4))
        have hp_Icc : p ∈ (Icc 1 z).filter Nat.Prime :=
          mem_filter.mpr ⟨mem_Icc.mpr ⟨hp_mem.2.one_le, hp_le_z⟩, hp_mem.2⟩
        have ha_eq : a_crt p = a₁ p := by simp [a_crt, hp1]
        have hm : r ≡ a₁ p [MOD p] := ha_eq ▸ hr_mod p hp_Icc
        have hsum_mod : r + j ≡ a₁ p + j [MOD p] := hm.add_right j
        have hdvd : p ∣ r + j := by
          rw [Nat.dvd_iff_mod_eq_zero, hsum_mod, add_comm]
          exact Nat.mod_eq_zero_of_dvd hpd
        exact ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp_ioc.1, hp_le_z⟩, hp_mem.2⟩, hdvd⟩
      · push Not at hP1
        have hj_rem : j ∈ S_rem := mem_filter.mpr ⟨hj_surv, hP1⟩
        let p := (φ ⟨j, hj_rem⟩ : ℕ)
        have hp3 : p ∈ P₃ := (φ ⟨j, hj_rem⟩).2
        have hp_mem := mem_filter.mp hp3
        have hp_ioc := mem_Ioc.mp hp_mem.1
        have hp_Icc : p ∈ (Icc 1 z).filter Nat.Prime :=
          mem_filter.mpr ⟨mem_Icc.mpr ⟨hp_mem.2.one_le, hp_ioc.2⟩, hp_mem.2⟩
        have hnot1 : p ∉ P₁ := by
          intro h; have := (mem_Ioc.mp (mem_filter.mp h).1).2; omega
        have hex_j : ∃ j' : S_rem, (φ j' : ℕ) = p := ⟨⟨j, hj_rem⟩, rfl⟩
        have hchoose_eq : Classical.choose hex_j = ⟨j, hj_rem⟩ := by
          apply hφ_inj
          exact Subtype.ext (Classical.choose_spec hex_j)
        have ha_eq : a_crt p = (p - j % p) % p := by
          simp only [a_crt, hnot1, ↓reduceIte, hp3, hex_j, ↓reduceDIte, hchoose_eq]
        have hm : r ≡ (p - j % p) % p [MOD p] := ha_eq ▸ hr_mod p hp_Icc
        have hdvd : p ∣ r + j := by
          rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hm]
          have hj_lt : j % p < p := Nat.mod_lt j hp_mem.2.pos
          by_cases hj0 : j % p = 0
          · simp [hj0]
          · have hlt : p - j % p < p := by omega
            rw [Nat.mod_mod, Nat.mod_eq_of_lt hlt, show p - j % p + j % p = p by omega, Nat.mod_self]
        exact ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hp_ioc.2⟩, hp_mem.2⟩, hdvd⟩
  exact ⟨r, hr_lt_P, hcover_j⟩

/-- Small-prime part of the pointwise prime-cost bound for `n = r + k * P` and `j ∈ [1, H]`. -/
private lemma pointwise_prime_cost_j_small (c₁ : ℝ) (hc₁_ge1 : 1 ≤ c₁)
    (z H r : ℕ)
    (hz10000 : 10000 ≤ z)
    (hP_ub : log (primorial z : ℝ) ≤ 2 * (z : ℝ))
    (hP_ge_exp : exp ((z : ℝ) / 2) ≤ (primorial z : ℝ))
    (hH_pos : 1 ≤ H)
    (hH_le_6cz : (H : ℝ) ≤ 6 * c₁ * (z : ℝ))
    (hH_sq : 2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2 < exp ((z : ℝ) / 2))
    (hr_lt_P : r < primorial z)
    (k : ℕ) (hk : k ∈ Icc 1 (primorial z))
    (j : ℕ) (hj : j ∈ Icc 1 H) :
    let P := primorial z
    let n := r + k * P
    let T_thr : ℝ := (n : ℝ) / (100 * (H : ℝ) * (z : ℝ))
    (∑ p ∈ (n + j).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ T_thr),
      ((n + j).factorization p : ℝ) * (p : ℝ)) / (n : ℝ) ≤
      (1 : ℝ) / (10 * (H : ℝ)) := by
  intro P n T_thr
  have hzR : (10000 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz10000
  have hP_pos : 0 < P := primorial_pos z
  rw [mem_Icc] at hk
  have hn_ge_P : P ≤ n := by
    have : 1 * P ≤ k * P := Nat.mul_le_mul_right P hk.1
    dsimp only [n]; omega
  have hn_pos : 0 < n := hP_pos.trans_le hn_ge_P
  have hn_le_2P2 : n ≤ 2 * P ^ 2 := by
    have hkP : k * P ≤ P * P := Nat.mul_le_mul_right P hk.2
    dsimp only [n]; nlinarith [sq P]
  have hj_icc := mem_Icc.mp hj
  have hnj_le : ((n + j : ℕ) : ℝ) ≤ 3 * (P : ℝ) ^ 2 := by
    have hHP : H ≤ P := by
      have h1 : (H : ℝ) ≤ 6 * c₁ * (z : ℝ) := hH_le_6cz
      have h600 : 1 ≤ 600 * c₁ * (z : ℝ) ^ 2 := by nlinarith
      have h2 : 6 * c₁ * (z : ℝ) ≤ 2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := by
        have ha : 6 * c₁ * (z : ℝ) ≤ 600 * c₁ * (z : ℝ) ^ 2 := by nlinarith
        have hb : 600 * c₁ * (z : ℝ) ^ 2 ≤ (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := by nlinarith
        linarith
      exact_mod_cast (h1.trans (h2.trans (hH_sq.le.trans hP_ge_exp)))
    have : n + j ≤ 3 * P ^ 2 := by nlinarith [sq P]
    exact_mod_cast this
  have hsum_v : ((∑ p ∈ (n + j).primeFactors, (n + j).factorization p : ℕ) : ℝ) ≤ 10 * (z : ℝ) := by
    have h1 := sum_factorization_le_log2 (n + j) (by omega)
    have hlog3P2 : log ((n + j : ℕ) : ℝ) ≤ 5 * (z : ℝ) := by
      calc
        log ((n + j : ℕ) : ℝ) ≤ log (3 * (P : ℝ) ^ 2) :=
          log_le_log (by positivity) hnj_le
        _ = log 3 + 2 * log (P : ℝ) := by
          rw [log_mul (by norm_num) (by positivity), log_pow]; ring
        _ ≤ 2 + 2 * (2 * (z : ℝ)) := by
          have hlog3 : log 3 < 2 := by
            have : log 3 < log 4 := log_lt_log (by norm_num) (by norm_num)
            have h4 : log 4 = 2 * log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; ring
            linarith [log_two_lt_d9]
          linarith
        _ ≤ 5 * (z : ℝ) := by linarith
    have hlog2 : (0.5 : ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
    have hdiv : log ((n + j : ℕ) : ℝ) / log 2 ≤ 10 * (z : ℝ) := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    exact h1.trans hdiv
  have hsmall_le :
      ∑ p ∈ (n + j).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ T_thr),
        ((n + j).factorization p : ℝ) * (p : ℝ) ≤ 10 * (z : ℝ) * T_thr := by
    calc
      ∑ p ∈ (n + j).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ T_thr),
          ((n + j).factorization p : ℝ) * (p : ℝ)
        ≤ ∑ p ∈ (n + j).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ T_thr),
            ((n + j).factorization p : ℝ) * T_thr := by
          refine sum_le_sum fun p hp =>
            mul_le_mul_of_nonneg_left (mem_filter.mp hp).2 (by positivity)
      _ = (∑ p ∈ (n + j).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ T_thr),
            ((n + j).factorization p : ℝ)) * T_thr := (sum_mul _ _ _).symm
      _ ≤ ((∑ p ∈ (n + j).primeFactors, (n + j).factorization p : ℕ) : ℝ) * T_thr := by
          rw [Nat.cast_sum]
          exact mul_le_mul_of_nonneg_right
            (sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity)
            (by positivity)
      _ ≤ 10 * (z : ℝ) * T_thr := mul_le_mul_of_nonneg_right hsum_v (by positivity)
  calc
    (∑ p ∈ (n + j).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ T_thr),
        ((n + j).factorization p : ℝ) * (p : ℝ)) / (n : ℝ)
      ≤ (10 * (z : ℝ) * T_thr) / (n : ℝ) :=
        div_le_div_of_nonneg_right hsmall_le (by positivity)
    _ = (1 : ℝ) / (10 * (H : ℝ)) := by
        dsimp only [T_thr]
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
        have hHR : (H : ℝ) ≠ 0 := by positivity
        have hzR' : (z : ℝ) ≠ 0 := by positivity
        field_simp [hnR, hHR, hzR']; ring

/-- Single-index pointwise prime-cost bound for `n = r + k * P` and `j ∈ [1, H]`. -/
private lemma pointwise_prime_cost_j (c₁ : ℝ) (hc₁_ge1 : 1 ≤ c₁)
    (z H A r : ℕ) (d_fn : ℕ → ℕ)
    (hz10000 : 10000 ≤ z)
    (hP_ub : log (primorial z : ℝ) ≤ 2 * (z : ℝ))
    (hP_ge_exp : exp ((z : ℝ) / 2) ≤ (primorial z : ℝ))
    (hH_pos : 1 ≤ H)
    (hH_le_6cz : (H : ℝ) ≤ 6 * c₁ * (z : ℝ))
    (hH_sq : 2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2 < exp ((z : ℝ) / 2))
    (hr_lt_P : r < primorial z)
    (hd_spec : ∀ j ∈ Icc 1 H, d_fn j ∈ (Ioc A z).filter Nat.Prime ∧ d_fn j ∣ r + j)
    (k : ℕ) (hk : k ∈ Icc 1 (primorial z))
    (j : ℕ) (hj : j ∈ Icc 1 H) :
    let P := primorial z
    let M := 200 * H * z
    let n := r + k * P
    (∑ p ∈ (n + j).primeFactors, ((n + j).factorization p : ℝ) * (p : ℝ)) / (n : ℝ) ≤
      (1 : ℝ) / (10 * (H : ℝ)) + ∑ m ∈ Icc 1 M,
        if d_fn j * m ∣ n + j ∧ ((n + j) / (d_fn j * m)).Prime then
          (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) else 0 := by
  intro P M n
  have hzR : (10000 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz10000
  have hP_pos : 0 < P := primorial_pos z
  have hk_icc := mem_Icc.mp hk
  have hn_ge_P : P ≤ n := by
    have : 1 * P ≤ k * P := Nat.mul_le_mul_right P hk_icc.1
    dsimp only [n]; omega
  have hn_pos : 0 < n := hP_pos.trans_le hn_ge_P
  have hj_icc := mem_Icc.mp hj
  -- Split (n + j).primeFactors into small (p ≤ n / (100 * H * z)) and large
  let T_thr : ℝ := (n : ℝ) / (100 * (H : ℝ) * (z : ℝ))
  have hsplit : ∑ p ∈ (n + j).primeFactors, ((n + j).factorization p : ℝ) * (p : ℝ) =
      (∑ p ∈ (n + j).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ T_thr),
        ((n + j).factorization p : ℝ) * (p : ℝ)) +
      (∑ p ∈ (n + j).primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ T_thr),
        ((n + j).factorization p : ℝ) * (p : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit, add_div]
  refine add_le_add
    (pointwise_prime_cost_j_small c₁ hc₁_ge1 z H r hz10000 hP_ub hP_ge_exp hH_pos
      hH_le_6cz hH_sq hr_lt_P k hk j hj) ?_
  · -- Large primes contribution: at most one prime p > T_thr, with multiplicity 1
    let L_pf := (n + j).primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ T_thr)
    have hT_sq : ((n + j : ℕ) : ℝ) < T_thr ^ 2 := by
      have h2n : ((n + j : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
        have hHP : (H : ℝ) ≤ (P : ℝ) := by
          have h1 : (H : ℝ) ≤ 6 * c₁ * (z : ℝ) := hH_le_6cz
          have h600 : 1 ≤ 600 * c₁ * (z : ℝ) ^ 2 := by nlinarith
          have h2 : 6 * c₁ * (z : ℝ) ≤ 2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := by
            have ha : 6 * c₁ * (z : ℝ) ≤ 600 * c₁ * (z : ℝ) ^ 2 := by nlinarith
            have hb : 600 * c₁ * (z : ℝ) ^ 2 ≤ (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := by nlinarith
            linarith
          exact h1.trans (h2.trans (hH_sq.le.trans hP_ge_exp))
        have : (j : ℝ) ≤ (n : ℝ) := by
          have hjH : (j : ℝ) ≤ (H : ℝ) := by exact_mod_cast hj_icc.2
          have hPn : (P : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_P
          linarith
        push_cast; linarith
      have h100Hz : 100 * (H : ℝ) * (z : ℝ) ≤ 600 * c₁ * (z : ℝ) ^ 2 := by nlinarith
      have h2n_lt : 2 * (100 * (H : ℝ) * (z : ℝ)) ^ 2 < (n : ℝ) := by
        have h1 : 2 * (100 * (H : ℝ) * (z : ℝ)) ^ 2 ≤ 2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := by gcongr
        exact h1.trans_lt (hH_sq.trans_le (hP_ge_exp.trans (by exact_mod_cast hn_ge_P)))
      have hden_pos : 0 < (100 * (H : ℝ) * (z : ℝ)) ^ 2 := by positivity
      have hT_eq : T_thr ^ 2 = (n : ℝ) ^ 2 / (100 * (H : ℝ) * (z : ℝ)) ^ 2 := by
        dsimp only [T_thr]; rw [div_pow]
      rw [hT_eq, lt_div_iff₀ hden_pos]
      nlinarith [show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn_pos]
    change (∑ p ∈ L_pf, ((n + j).factorization p : ℝ) * (p : ℝ)) / (n : ℝ) ≤ _
    by_cases hLempty : L_pf = ∅
    · rw [hLempty, Finset.sum_empty, zero_div]
      exact sum_nonneg fun m _ => by split_ifs <;> positivity
    · obtain ⟨p, hpL⟩ := Finset.nonempty_iff_ne_empty.mpr hLempty
      have hnj_ne : n + j ≠ 0 := (Nat.add_pos_left hn_pos j).ne'
      have hL_sing : L_pf = {p} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨hpL, fun q hqL => ?_⟩
        by_contra hne
        have hp_mem := mem_filter.mp hpL
        have hq_mem := mem_filter.mp hqL
        have hp_pr := Nat.prime_of_mem_primeFactors hp_mem.1
        have hq_pr := Nat.prime_of_mem_primeFactors hq_mem.1
        have hcop := (Nat.coprime_primes hp_pr hq_pr).mpr (Ne.symm hne)
        have hmul_dvd : p * q ∣ n + j :=
          hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_mem.1)
            (Nat.dvd_of_mem_primeFactors hq_mem.1)
        have hmul_le : ((p * q : ℕ) : ℝ) ≤ ((n + j : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (Nat.add_pos_left hn_pos j) hmul_dvd
        have hp_gt : T_thr < (p : ℝ) := not_le.mp hp_mem.2
        have hq_gt : T_thr < (q : ℝ) := not_le.mp hq_mem.2
        rw [Nat.cast_mul] at hmul_le
        have hT_pos : 0 < T_thr := by positivity
        have h1 : T_thr ^ 2 < (p : ℝ) * (q : ℝ) := by
          rw [sq]; exact mul_lt_mul'' hp_gt hq_gt hT_pos.le hT_pos.le
        linarith
      have hp_mem := mem_filter.mp hpL
      have hp_pr := Nat.prime_of_mem_primeFactors hp_mem.1
      have hp_gt : T_thr < (p : ℝ) := not_le.mp hp_mem.2
      have hv1 : (n + j).factorization p = 1 := by
        have hge1 : 1 ≤ (n + j).factorization p :=
          (hp_pr.pow_dvd_iff_le_factorization hnj_ne).mp
            (by rw [pow_one]; exact Nat.dvd_of_mem_primeFactors hp_mem.1)
        have hlt2 : (n + j).factorization p < 2 := by
          by_contra hge2
          push Not at hge2
          have hp2 : p ^ 2 ∣ n + j := (hp_pr.pow_dvd_iff_le_factorization hnj_ne).mpr hge2
          have hle : ((p ^ 2 : ℕ) : ℝ) ≤ ((n + j : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_of_dvd (Nat.add_pos_left hn_pos j) hp2
          rw [Nat.cast_pow] at hle
          have hT_pos : 0 < T_thr := by positivity
          have h1 : T_thr ^ 2 < (p : ℝ) ^ 2 := by
            rw [sq, sq]; exact mul_lt_mul'' hp_gt hp_gt hT_pos.le hT_pos.le
          linarith
        omega
      rw [hL_sing, Finset.sum_singleton, hv1, Nat.cast_one, one_mul]
      -- Show d_fn j * m ∣ n + j with (n + j) / (d_fn j * m) = p and m ∈ Icc 1 M
      have hd_j := hd_spec j hj
      have hd_pr : (d_fn j).Prime := (mem_filter.mp hd_j.1).2
      have hd_le_z : d_fn j ≤ z := (mem_Ioc.mp (mem_filter.mp hd_j.1).1).2
      have hd_dvd_P : d_fn j ∣ P := by
        dsimp only [P]
        rw [primorial_eq_prod_Icc]
        exact dvd_prod_of_mem id (mem_filter.mpr ⟨mem_Icc.mpr ⟨hd_pr.one_le, hd_le_z⟩, hd_pr⟩)
      have hd_dvd_nj : d_fn j ∣ n + j := by
        have h1 : n + j = (r + j) + k * P := by dsimp only [n]; ring
        rw [h1]
        exact Nat.dvd_add hd_j.2 (hd_dvd_P.trans (dvd_mul_left P k))
      have hd_lt_p : d_fn j < p := by
        have hz_lt_T : (z : ℝ) < T_thr := by
          dsimp only [T_thr]
          rw [lt_div_iff₀ (by positivity)]
          have h1 : (z : ℝ) * (100 * (H : ℝ) * (z : ℝ)) ≤ 600 * c₁ * (z : ℝ) ^ 3 := by
            calc (z : ℝ) * (100 * (H : ℝ) * (z : ℝ))
                ≤ (z : ℝ) * (100 * (6 * c₁ * (z : ℝ)) * (z : ℝ)) := by gcongr
              _ = 600 * c₁ * (z : ℝ) ^ 3 := by ring
          have h2 : 600 * c₁ * (z : ℝ) ^ 3 ≤ 2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := by
            have hcz : (1 : ℝ) ≤ 600 * c₁ * (z : ℝ) := by
              calc (1 : ℝ) ≤ 600 * 1 * 10000 := by norm_num
                _ ≤ 600 * c₁ * (z : ℝ) := by gcongr
            have hz_le : (z : ℝ) ≤ 600 * c₁ * (z : ℝ) ^ 2 := by
              calc (z : ℝ) = 1 * (z : ℝ) := (one_mul _).symm
                _ ≤ (600 * c₁ * (z : ℝ)) * (z : ℝ) := mul_le_mul_of_nonneg_right hcz (Nat.cast_nonneg z)
                _ = 600 * c₁ * (z : ℝ) ^ 2 := by ring
            calc 600 * c₁ * (z : ℝ) ^ 3
                = (600 * c₁ * (z : ℝ) ^ 2) * (z : ℝ) := by ring
              _ ≤ (600 * c₁ * (z : ℝ) ^ 2) * (600 * c₁ * (z : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_left hz_le (by positivity)
              _ = (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := (sq _).symm
              _ ≤ 2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := by linarith [sq_nonneg (600 * c₁ * (z : ℝ) ^ 2)]
          exact (h1.trans h2).trans_lt (hH_sq.trans_le (hP_ge_exp.trans (by exact_mod_cast hn_ge_P)))
        have : (d_fn j : ℝ) < (p : ℝ) := lt_trans (lt_of_le_of_lt (by exact_mod_cast hd_le_z) hz_lt_T) hp_gt
        exact_mod_cast this
      have hcop_dp : Nat.Coprime (d_fn j) p :=
        (Nat.coprime_primes hd_pr hp_pr).mpr hd_lt_p.ne
      have hdp_dvd : d_fn j * p ∣ n + j :=
        hcop_dp.mul_dvd_of_dvd_of_dvd hd_dvd_nj (Nat.dvd_of_mem_primeFactors hp_mem.1)
      let m := (n + j) / (d_fn j * p)
      have hm_eq : d_fn j * m * p = n + j := by
        calc d_fn j * m * p = d_fn j * p * m := by ring
          _ = n + j := Nat.mul_div_cancel' hdp_dvd
      have hm_pos : 1 ≤ m := by
        exact Nat.div_pos (Nat.le_of_dvd (Nat.add_pos_left hn_pos j) hdp_dvd) (mul_pos hd_pr.pos hp_pr.pos)
      have h2n : ((n + j : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
        have hHP : (H : ℝ) ≤ (P : ℝ) := by
          have h1 : (H : ℝ) ≤ 6 * c₁ * (z : ℝ) := hH_le_6cz
          have h600 : (1 : ℝ) ≤ 600 * c₁ * (z : ℝ) ^ 2 := by
            calc (1 : ℝ) ≤ 600 * 1 * 10000 ^ 2 := by norm_num
              _ ≤ 600 * c₁ * (z : ℝ) ^ 2 := by gcongr
          have ha : 6 * c₁ * (z : ℝ) ≤ 600 * c₁ * (z : ℝ) ^ 2 := by
            calc 6 * c₁ * (z : ℝ) ≤ 600 * c₁ * (z : ℝ) * 1 := by linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c₁) (Nat.cast_nonneg z)]
              _ ≤ 600 * c₁ * (z : ℝ) * (z : ℝ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              _ = 600 * c₁ * (z : ℝ) ^ 2 := by ring
          have hb : 600 * c₁ * (z : ℝ) ^ 2 ≤ (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := by
            calc 600 * c₁ * (z : ℝ) ^ 2 = 1 * (600 * c₁ * (z : ℝ) ^ 2) := (one_mul _).symm
              _ ≤ (600 * c₁ * (z : ℝ) ^ 2) * (600 * c₁ * (z : ℝ) ^ 2) := mul_le_mul_of_nonneg_right h600 (by positivity)
              _ = (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := (sq _).symm
          have h2 : 6 * c₁ * (z : ℝ) ≤ 2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2 := by linarith
          exact h1.trans (h2.trans (hH_sq.le.trans hP_ge_exp))
        have : (j : ℝ) ≤ (n : ℝ) := by
          have hjH : (j : ℝ) ≤ (H : ℝ) := by exact_mod_cast hj_icc.2
          have hPn : (P : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_P
          linarith
        push_cast; linarith
      have hm_le_M : m ≤ M := by
        have hmR : (m : ℝ) * T_thr < 2 * (n : ℝ) := by
          have h1 : (m : ℝ) * (p : ℝ) ≤ ((n + j : ℕ) : ℝ) := by
            have : m * p ≤ n + j := by
              have : 1 * (m * p) ≤ d_fn j * (m * p) := Nat.mul_le_mul_right _ hd_pr.one_le
              linarith [show d_fn j * (m * p) = d_fn j * m * p by ring]
            exact_mod_cast this
          have hlt : (m : ℝ) * T_thr < (m : ℝ) * (p : ℝ) :=
            mul_lt_mul_of_pos_left hp_gt (by exact_mod_cast hm_pos)
          linarith
        have hM_eq : (M : ℝ) = 200 * (H : ℝ) * (z : ℝ) := by dsimp only [M]; push_cast; ring
        have hm_lt : (m : ℝ) < (M : ℝ) := by
          dsimp only [T_thr] at hmR
          rw [hM_eq]
          have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
          have hden : 0 < 100 * (H : ℝ) * (z : ℝ) :=
            mul_pos (mul_pos (by norm_num) (by exact_mod_cast hH_pos)) (by exact_mod_cast (by omega : 0 < z))
          have h1 : (m : ℝ) * (n : ℝ) / (100 * (H : ℝ) * (z : ℝ)) < 2 * (n : ℝ) := by
            rwa [mul_div_assoc]
          have hlt2 := (div_lt_iff₀ hden).mp h1
          have hlt3 : (m : ℝ) * (n : ℝ) < (200 * (H : ℝ) * (z : ℝ)) * (n : ℝ) := by
            calc (m : ℝ) * (n : ℝ) < 2 * (n : ℝ) * (100 * (H : ℝ) * (z : ℝ)) := hlt2
              _ = (200 * (H : ℝ) * (z : ℝ)) * (n : ℝ) := by ring
          exact lt_of_mul_lt_mul_right hlt3 hnR.le
        exact_mod_cast hm_lt.le
      have hdm_dvd : d_fn j * m ∣ n + j := ⟨p, hm_eq.symm⟩
      have hquot_p : (n + j) / (d_fn j * m) = p := by
        apply Nat.div_eq_of_eq_mul_left (mul_pos hd_pr.pos hm_pos)
        calc n + j = d_fn j * m * p := hm_eq.symm
          _ = p * (d_fn j * m) := by ring
      have hterm_le : (p : ℝ) / (n : ℝ) ≤ (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) := by
        have heqR : (d_fn j : ℝ) * (m : ℝ) * (p : ℝ) = ((n + j : ℕ) : ℝ) := by exact_mod_cast hm_eq
        rw [div_le_div_iff₀ (by exact_mod_cast hn_pos)
          (mul_pos (by exact_mod_cast hd_pr.pos) (by exact_mod_cast hm_pos))]
        rw [show (p : ℝ) * ((d_fn j : ℝ) * (m : ℝ)) = (d_fn j : ℝ) * (m : ℝ) * (p : ℝ) by ring, heqR]
        exact h2n
      have hmem_m : m ∈ Icc 1 M := mem_Icc.mpr ⟨hm_pos, hm_le_M⟩
      calc
        (p : ℝ) / (n : ℝ) ≤ (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) := hterm_le
        _ = if d_fn j * m ∣ n + j ∧ ((n + j) / (d_fn j * m)).Prime then
              (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) else 0 := by
            rw [if_pos ⟨hdm_dvd, hquot_p ▸ hp_pr⟩]
        _ ≤ ∑ m' ∈ Icc 1 M,
              if d_fn j * m' ∣ n + j ∧ ((n + j) / (d_fn j * m')).Prime then
                (2 : ℝ) / ((d_fn j : ℝ) * (m' : ℝ)) else 0 :=
            Finset.single_le_sum (f := fun m' =>
              if d_fn j * m' ∣ n + j ∧ ((n + j) / (d_fn j * m')).Prime then
                (2 : ℝ) / ((d_fn j : ℝ) * (m' : ℝ)) else 0)
              (fun m' _ => by
                split_ifs
                · exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
                · exact le_rfl) hmem_m
/-- Pointwise prime-cost bound for `n = r + k * P` (`1 ≤ k ≤ P`). -/
private lemma pointwise_prime_cost_bound (c₁ : ℝ) (hc₁_ge1 : 1 ≤ c₁)
    (z H A r : ℕ) (d_fn : ℕ → ℕ)
    (hz10000 : 10000 ≤ z)
    (hP_ub : log (primorial z : ℝ) ≤ 2 * (z : ℝ))
    (hP_ge_exp : exp ((z : ℝ) / 2) ≤ (primorial z : ℝ))
    (hH_pos : 1 ≤ H)
    (hH_le_6cz : (H : ℝ) ≤ 6 * c₁ * (z : ℝ))
    (hH_sq : 2 * (600 * c₁ * (z : ℝ) ^ 2) ^ 2 < exp ((z : ℝ) / 2))
    (hr_lt_P : r < primorial z)
    (hd_spec : ∀ j ∈ Icc 1 H, d_fn j ∈ (Ioc A z).filter Nat.Prime ∧ d_fn j ∣ r + j)
    (k : ℕ) (hk : k ∈ Icc 1 (primorial z)) :
    let P := primorial z
    let M := 200 * H * z
    let n := r + k * P
    (∑ j ∈ range H,
      ∑ p ∈ (n + j + 1).primeFactors, ((n + j + 1).factorization p : ℝ) * (p : ℝ)) / (n : ℝ) ≤
      (1 : ℝ) / 10 + ∑ j ∈ Icc 1 H, ∑ m ∈ Icc 1 M,
        if d_fn j * m ∣ n + j ∧ ((n + j) / (d_fn j * m)).Prime then
          (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) else 0 := by
  intro P M n
  have hreindex :
      ∑ j ∈ range H,
        ∑ p ∈ (n + j + 1).primeFactors, ((n + j + 1).factorization p : ℝ) * (p : ℝ) =
      ∑ j ∈ Icc 1 H,
        ∑ p ∈ (n + j).primeFactors, ((n + j).factorization p : ℝ) * (p : ℝ) := by
    refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
    · intro j hj; rw [mem_range] at hj; rw [mem_Icc]; omega
    · intro j₁ _ j₂ _ h; omega
    · intro j hj; rw [mem_Icc] at hj
      exact ⟨j - 1, mem_range.mpr (by omega), by omega⟩
    · intro j _; congr 1
  rw [hreindex, sum_div]
  calc
    ∑ j ∈ Icc 1 H,
        (∑ p ∈ (n + j).primeFactors, ((n + j).factorization p : ℝ) * (p : ℝ)) / (n : ℝ)
      ≤ ∑ j ∈ Icc 1 H,
          ((1 : ℝ) / (10 * (H : ℝ)) + ∑ m ∈ Icc 1 M,
            if d_fn j * m ∣ n + j ∧ ((n + j) / (d_fn j * m)).Prime then
              (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) else 0) :=
        sum_le_sum fun j hj =>
          pointwise_prime_cost_j c₁ hc₁_ge1 z H A r d_fn hz10000 hP_ub hP_ge_exp hH_pos
            hH_le_6cz hH_sq hr_lt_P hd_spec k hk j hj
    _ = (1 : ℝ) / 10 + ∑ j ∈ Icc 1 H, ∑ m ∈ Icc 1 M,
          if d_fn j * m ∣ n + j ∧ ((n + j) / (d_fn j * m)).Prime then
            (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) else 0 := by
        rw [Finset.sum_add_distrib, sum_const, Nat.card_Icc,
          show H + 1 - 1 = H by omega, nsmul_eq_mul]
        congr 1
        have hHR : (H : ℝ) ≠ 0 := by positivity
        field_simp [hHR]

/-- Average the large-prime weight over `k ∈ [1, primorial z]` via Selberg's sieve. -/
private lemma average_sieve_bound (c₁ C_inv : ℝ) (hc₁_ge1 : 1 ≤ c₁) (hC_inv_pos : 0 < C_inv)
    (z H A Z r : ℕ) (d_fn : ℕ → ℕ)
    (hz10000 : 10000 ≤ z)
    (hlogz_ge7 : 7 < log (z : ℝ))
    (hP_ge_exp : exp ((z : ℝ) / 2) ≤ (primorial z : ℝ))
    (hP_ge_16 : 16 ≤ primorial z)
    (hH_pos : 1 ≤ H)
    (hH_le_6cz : (H : ℝ) ≤ 6 * c₁ * (z : ℝ))
    (hA_eq : A = ⌊(log (z : ℝ)) ^ 12⌋₊)
    (hZ_ge2 : 2 ≤ Z)
    (hZ_le_P14 : (Z : ℝ) ≤ (primorial z : ℝ) ^ (1 / 4 : ℝ))
    (hZ_big : 2000 * c₁ * (z : ℝ) ^ 3 < exp ((z : ℝ) / 8) / 2)
    (hlogz_sieve : 1000 * c₁ * (200 * exp (2 * C_inv)) < log (z : ℝ))
    (hsieve_ub :
      let P := primorial z
      let Q := (Ioc z Z).filter Nat.Prime
      let D := (Icc 1 Z).filter (fun e => Squarefree e ∧ ∀ p ∈ e.primeFactors, p ∈ Q)
      let S_selb := ∑ e ∈ D, (1 : ℝ) / (e.totient : ℝ)
      ((P + 1 : ℕ) : ℝ) / S_selb + (Z : ℝ) ^ 2 ≤
        (200 * exp (2 * C_inv)) * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ))
    (hd_spec : ∀ j ∈ Icc 1 H, d_fn j ∈ (Ioc A z).filter Nat.Prime ∧ d_fn j ∣ r + j) :
    let P := primorial z
    let M := 200 * H * z
    ∑ k ∈ Icc 1 P,
      (∑ j ∈ Icc 1 H, ∑ m ∈ Icc 1 M,
        if d_fn j * m ∣ r + k * P + j ∧ ((r + k * P + j) / (d_fn j * m)).Prime then
          (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) else 0) ≤ (P : ℝ) / 10 := by
  intro P M
  let C_sieve : ℝ := 200 * exp (2 * C_inv)
  let Q := (Ioc z Z).filter Nat.Prime
  let D := (Icc 1 Z).filter (fun e => Squarefree e ∧ ∀ p ∈ e.primeFactors, p ∈ Q)
  let S_selb := ∑ e ∈ D, (1 : ℝ) / (e.totient : ℝ)
  have hzR : (10000 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz10000
  have hP_pos : 0 < P := primorial_pos z
  have hM_pos : 1 ≤ M := Nat.mul_pos (Nat.mul_pos (by norm_num) hH_pos) (by omega)
  let W_fn : ℕ → ℝ := fun k =>
    ∑ j ∈ Icc 1 H, ∑ m ∈ Icc 1 M,
      if d_fn j * m ∣ r + k * P + j ∧ ((r + k * P + j) / (d_fn j * m)).Prime then
        (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) else 0
  change ∑ k ∈ Icc 1 P, W_fn k ≤ (P : ℝ) / 10
  have hswap : ∑ k ∈ Icc 1 P, W_fn k =
      ∑ j ∈ Icc 1 H, ∑ m ∈ Icc 1 M,
        ((2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ))) *
          (((Icc 1 P).filter (fun k =>
            d_fn j * m ∣ r + k * P + j ∧ ((r + k * P + j) / (d_fn j * m)).Prime)).card : ℝ) := by
    dsimp only [W_fn]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap]
  have hP_cop : ∀ q ∈ (Ioc z Z).filter Nat.Prime, ¬ q ∣ P := by
    intro q hq hqd
    have hq_mem := mem_filter.mp hq
    have hq_gt : z < q := (mem_Ioc.mp hq_mem.1).1
    dsimp only [P] at hqd
    rw [primorial_eq_prod_Icc] at hqd
    obtain ⟨p, hp, hqp⟩ := hq_mem.2.prime.exists_mem_finset_dvd hqd
    have hp_mem := mem_filter.mp hp
    have heq := (Nat.prime_dvd_prime_iff_eq hq_mem.2 hp_mem.2).mp hqp
    have hp_le := (mem_Icc.mp hp_mem.1).2
    omega
  have hterm_le : ∀ j ∈ Icc 1 H, ∀ m ∈ Icc 1 M,
      ((2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ))) *
          (((Icc 1 P).filter (fun k =>
            d_fn j * m ∣ r + k * P + j ∧ ((r + k * P + j) / (d_fn j * m)).Prime)).card : ℝ) ≤
        ((2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ))) *
          (C_sieve * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ)) := by
    intro j hj m hm
    have hd_j := hd_spec j hj
    have hd_pr : (d_fn j).Prime := (mem_filter.mp hd_j.1).2
    have hd_le_z : d_fn j ≤ z := (mem_Ioc.mp (mem_filter.mp hd_j.1).1).2
    have hd_P : d_fn j ∣ P := by
      dsimp only [P]
      rw [primorial_eq_prod_Icc]
      exact dvd_prod_of_mem id (mem_filter.mpr ⟨mem_Icc.mpr ⟨hd_pr.one_le, hd_le_z⟩, hd_pr⟩)
    have hm_icc := mem_Icc.mp hm
    have hquot_gt : Z < P / (d_fn j * m) := by
      have hdm_le : ((d_fn j * m : ℕ) : ℝ) < exp ((z : ℝ) / 8) / 2 := by
        have h1 : ((d_fn j * m : ℕ) : ℝ) ≤ (z : ℝ) * (M : ℝ) := by
          push_cast
          exact mul_le_mul (by exact_mod_cast hd_le_z) (by exact_mod_cast hm_icc.2) (by positivity) (by positivity)
        have h2 : (z : ℝ) * (M : ℝ) ≤ 1200 * c₁ * (z : ℝ) ^ 3 := by
          have hM_R : (M : ℝ) = 200 * (H : ℝ) * (z : ℝ) := by dsimp only [M]; push_cast; ring
          calc (z : ℝ) * (M : ℝ) = 200 * (H : ℝ) * (z : ℝ) ^ 2 := by rw [hM_R]; ring
            _ ≤ 200 * (6 * c₁ * (z : ℝ)) * (z : ℝ) ^ 2 := by gcongr
            _ = 1200 * c₁ * (z : ℝ) ^ 3 := by ring
        have h3 : 1200 * c₁ * (z : ℝ) ^ 3 ≤ 2000 * c₁ * (z : ℝ) ^ 3 := by
          have : (0 : ℝ) ≤ c₁ * (z : ℝ) ^ 3 := by positivity
          linarith
        exact (h1.trans (h2.trans h3)).trans_lt hZ_big
      have hZdm_lt_P : (Z + 1 : ℝ) * ((d_fn j * m : ℕ) : ℝ) < (P : ℝ) := by
        have hZ1 : (Z + 1 : ℝ) ≤ 2 * (P : ℝ) ^ (1 / 4 : ℝ) := by
          have : (1 : ℝ) ≤ (P : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by exact_mod_cast hP_pos) (by norm_num)
          linarith
        have hdm_P14 : ((d_fn j * m : ℕ) : ℝ) < (P : ℝ) ^ (1 / 4 : ℝ) / 2 := by
          have hP14 : exp ((z : ℝ) / 8) ≤ (P : ℝ) ^ (1 / 4 : ℝ) := by
            have h1 : exp ((z : ℝ) / 8) = (exp ((z : ℝ) / 2)) ^ (1 / 4 : ℝ) := by
              rw [← exp_mul]; congr 1; ring
            rw [h1]
            exact rpow_le_rpow (exp_pos _).le hP_ge_exp (by norm_num)
          linarith
        have hP12_lt_P : (P : ℝ) ^ (1 / 2 : ℝ) < (P : ℝ) := by
          have h1 : (P : ℝ) ^ (1 / 2 : ℝ) < (P : ℝ) ^ (1 : ℝ) :=
            Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < P)) (by norm_num)
          simpa using h1
        have hmul_P14 : (2 * (P : ℝ) ^ (1 / 4 : ℝ)) * ((P : ℝ) ^ (1 / 4 : ℝ) / 2) = (P : ℝ) ^ (1 / 2 : ℝ) := by
          have hsq : (P : ℝ) ^ (1 / 4 : ℝ) * (P : ℝ) ^ (1 / 4 : ℝ) = (P : ℝ) ^ (1 / 2 : ℝ) := by
            rw [← rpow_add (by exact_mod_cast hP_pos)]; norm_num
          rw [← hsq]; ring
        have hlt1 : (Z + 1 : ℝ) * ((d_fn j * m : ℕ) : ℝ) < (P : ℝ) ^ (1 / 2 : ℝ) := by
          calc
            (Z + 1 : ℝ) * ((d_fn j * m : ℕ) : ℝ)
              ≤ (2 * (P : ℝ) ^ (1 / 4 : ℝ)) * ((d_fn j * m : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_right hZ1 (by positivity)
            _ < (2 * (P : ℝ) ^ (1 / 4 : ℝ)) * ((P : ℝ) ^ (1 / 4 : ℝ) / 2) :=
                mul_lt_mul_of_pos_left hdm_P14 (by positivity)
            _ = (P : ℝ) ^ (1 / 2 : ℝ) := hmul_P14
        exact hlt1.trans hP12_lt_P
      have hnat : (Z + 1) * (d_fn j * m) < P := by exact_mod_cast hZdm_lt_P
      exact (Nat.le_div_iff_mul_le (mul_pos hd_pr.pos hm_icc.1)).mpr hnat.le
    have hcnt : (((Icc 1 P).filter (fun k =>
          d_fn j * m ∣ r + k * P + j ∧ ((r + k * P + j) / (d_fn j * m)).Prime)).card : ℝ) ≤
        ((P + 1 : ℕ) : ℝ) / S_selb + (Z : ℝ) ^ 2 :=
      count_prime_quot_le z P Z r j (d_fn j) m (Nat.le_of_succ_le hZ_ge2) hd_pr.pos hm_icc.1
        hd_j.2 hd_P hP_cop hquot_gt
    exact mul_le_mul_of_nonneg_left (le_trans hcnt hsieve_ub)
      (div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hdj_ge : ∀ j ∈ Icc 1 H, (log (z : ℝ)) ^ 12 ≤ (d_fn j : ℝ) := by
    intro j hj
    have hgt : A < d_fn j := (mem_Ioc.mp (mem_filter.mp (hd_spec j hj).1).1).1
    have hfl := Nat.lt_floor_add_one ((log (z : ℝ)) ^ 12)
    have h1 : ((A + 1 : ℕ) : ℝ) ≤ (d_fn j : ℝ) := by exact_mod_cast hgt
    rw [hA_eq] at h1
    push_cast at h1
    linarith
  have hharm_M : ∑ m ∈ Icc 1 M, (1 : ℝ) / (m : ℝ) ≤ 5 * log (z : ℝ) := by
    have h1 := harmonic_sum_le_one_add_log M hM_pos
    have hM_le : (M : ℝ) ≤ (z : ℝ) ^ 4 := by
      have hM_R : (M : ℝ) = 200 * (H : ℝ) * (z : ℝ) := by dsimp only [M]; push_cast; ring
      have hc1_lt_z : 1200 * c₁ ≤ (z : ℝ) ^ 2 := by
        have hCs : (200 : ℝ) ≤ C_sieve := by
          dsimp only [C_sieve]
          have : 1 ≤ exp (2 * C_inv) := one_le_exp (by positivity)
          linarith
        have hlog_lt_z : log (z : ℝ) ≤ (z : ℝ) := Real.log_le_self (by positivity)
        have h1 : 1200 * c₁ ≤ 1000 * c₁ * C_sieve := by
          have : 1200 * c₁ ≤ 1000 * c₁ * 200 := by linarith
          exact this.trans (mul_le_mul_of_nonneg_left hCs (by positivity))
        have h2 : (z : ℝ) ≤ (z : ℝ) ^ 2 := by
          calc (z : ℝ) = (z : ℝ) * 1 := (mul_one _).symm
            _ ≤ (z : ℝ) * (z : ℝ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = (z : ℝ) ^ 2 := (sq _).symm
        exact (h1.trans (hlogz_sieve.le.trans hlog_lt_z)).trans h2
      calc (M : ℝ) = 200 * (H : ℝ) * (z : ℝ) := hM_R
        _ ≤ 200 * (6 * c₁ * (z : ℝ)) * (z : ℝ) := by gcongr
        _ = (1200 * c₁) * (z : ℝ) ^ 2 := by ring
        _ ≤ (z : ℝ) ^ 2 * (z : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hc1_lt_z (by positivity)
        _ = (z : ℝ) ^ 4 := by ring
    have hlogM : log (M : ℝ) ≤ 4 * log (z : ℝ) := by
      calc log (M : ℝ) ≤ log ((z : ℝ) ^ 4) := log_le_log (by positivity) hM_le
        _ = 4 * log (z : ℝ) := by rw [log_pow]; ring
    linarith
  calc
    ∑ j ∈ Icc 1 H, ∑ m ∈ Icc 1 M,
        ((2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ))) *
          (((Icc 1 P).filter (fun k =>
            d_fn j * m ∣ r + k * P + j ∧ ((r + k * P + j) / (d_fn j * m)).Prime)).card : ℝ)
      ≤ ∑ j ∈ Icc 1 H, ∑ m ∈ Icc 1 M,
          ((2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ))) *
            (C_sieve * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ)) :=
        sum_le_sum fun j hj => sum_le_sum fun m hm => hterm_le j hj m hm
    _ ≤ ∑ j ∈ Icc 1 H,
          ((2 : ℝ) / (log (z : ℝ)) ^ 12) * (5 * log (z : ℝ)) *
            (C_sieve * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ)) := by
        refine sum_le_sum fun j hj => ?_
        have hpull :
            ∑ m ∈ Icc 1 M,
              ((2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ))) *
                (C_sieve * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ)) =
            ((2 : ℝ) / (d_fn j : ℝ)) * (∑ m ∈ Icc 1 M, (1 : ℝ) / (m : ℝ)) *
              (C_sieve * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ)) := by
          rw [mul_sum, sum_mul]
          refine sum_congr rfl fun m _ => by ring
        rw [hpull]
        have hd_inv : (2 : ℝ) / (d_fn j : ℝ) ≤ (2 : ℝ) / (log (z : ℝ)) ^ 12 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (hdj_ge j hj)
        gcongr
    _ = (H : ℝ) * ((2 : ℝ) / (log (z : ℝ)) ^ 12) * (5 * log (z : ℝ)) *
          (C_sieve * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ)) := by
        rw [sum_const, Nat.card_Icc, show H + 1 - 1 = H by omega, nsmul_eq_mul]; ring
    _ ≤ (6 * c₁ * (z : ℝ)) * ((2 : ℝ) / (log (z : ℝ)) ^ 12) * (5 * log (z : ℝ)) *
          (C_sieve * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ)) := by
        gcongr
    _ = (60 * c₁ * C_sieve / log (z : ℝ)) * (P : ℝ) := by
        have hz_ne : (z : ℝ) ≠ 0 := by positivity
        have hl_ne : log (z : ℝ) ≠ 0 := by linarith
        field_simp [hz_ne, hl_ne]; ring
    _ ≤ (1 : ℝ) / 10 * (P : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ (by linarith)]
        linarith
    _ = (P : ℝ) / 10 := by ring

/-- Main theorem: for every `c > 0`, `F (fun m ↦ c * log m) n < 2` holds for infinitely many `n`. -/
private lemma main_theorem :
    ∀ c > (0 : ℝ), ∃ᶠ n : ℕ in atTop, Erdos420.F (fun m ↦ c * log m) n < 2 := by
  intro c hc
  rw [Filter.frequently_atTop]
  intro N₀
  let c₁ : ℝ := max c 1
  have hc₁_ge1 : 1 ≤ c₁ := le_max_right c 1
  have hc_le_c₁ : c ≤ c₁ := le_max_left c 1
  obtain ⟨C_inv, hC_inv_pos, hC_inv⟩ := sum_inv_primes_le
  let H_fn : ℕ → ℕ := fun z => ⌊5 * c₁ * (z : ℝ)⌋₊ + 1
  let A_fn : ℕ → ℕ := fun z => ⌊(log (z : ℝ)) ^ 12⌋₊
  let y_fn : ℕ → ℕ := fun z => ⌊exp (sqrt (log (z : ℝ)))⌋₊
  let C_sieve : ℝ := 200 * exp (2 * C_inv)
  obtain ⟨z, ⟨hP_lb, hP_ub⟩, hP3_ge, hsm_le, ⟨hA4, hAy, hyq⟩, hgr_ge,
    ⟨hPN0, hP16, hZ_big, hH_sq, hz_sq, hlogz_sieve⟩, hpiH_ub, hz10000⟩ :=
    exists_good_z c₁ hc₁_ge1 N₀ C_inv hC_inv_pos hC_inv
  let P := primorial z
  let H := H_fn z
  let A := A_fn z
  let y := y_fn z
  let Z := ⌊(P : ℝ) ^ (1 / 4 : ℝ)⌋₊
  have hzR : (10000 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz10000
  have hlogz_ge7 : 7 < log (z : ℝ) := by
    have he : exp 1 < 3 := by linarith [exp_one_lt_d9]
    have h7 : exp 7 = (exp 1) ^ 7 := by rw [← exp_nat_mul]; norm_num
    have h1 : exp 7 < 10000 := by
      rw [h7]
      calc (exp 1) ^ 7 < 3 ^ 7 := pow_lt_pow_left₀ he (exp_pos 1).le (by norm_num)
        _ < 10000 := by norm_num
    exact (lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
  have hP_pos : 0 < P := primorial_pos z
  have hP_ge_exp : exp ((z : ℝ) / 2) ≤ (P : ℝ) := by
    have := exp_le_exp.mpr hP_lb
    rwa [exp_log (by exact_mod_cast hP_pos)] at this
  have hP_le_exp : (P : ℝ) ≤ exp (2 * (z : ℝ)) := by
    have := exp_le_exp.mpr hP_ub
    rwa [exp_log (by exact_mod_cast hP_pos)] at this
  have hP_ge_N0 : N₀ ≤ P := by exact_mod_cast (hPN0.trans hP_ge_exp)
  have hP_ge_16 : 16 ≤ P := by exact_mod_cast (hP16.trans hP_ge_exp)
  have hH_ge_z : (z : ℝ) ≤ (H : ℝ) := by
    have h1 : (z : ℝ) ≤ 5 * c₁ * (z : ℝ) := by nlinarith
    have h2 := Nat.lt_floor_add_one (5 * c₁ * (z : ℝ))
    dsimp only [H, H_fn]; push_cast; linarith
  have hH_le_6cz : (H : ℝ) ≤ 6 * c₁ * (z : ℝ) := by
    have h1 := Nat.floor_le (show (0 : ℝ) ≤ 5 * c₁ * (z : ℝ) by positivity)
    dsimp only [H, H_fn]; push_cast; nlinarith
  obtain ⟨r, hr_lt_P, hcover_j⟩ :=
    build_crt_residue c₁ hc₁_ge1 z H A y hz10000 hlogz_ge7 hH_ge_z hH_le_6cz
      hA4 hAy hyq hsm_le hpiH_ub hgr_ge hP3_ge
  -- Choose a witness prime d_j for each j ∈ Icc 1 H
  let d_fn : ℕ → ℕ := fun j => if h : j ∈ Icc 1 H then Classical.choose (hcover_j j h) else 1
  have hd_spec : ∀ j ∈ Icc 1 H, d_fn j ∈ (Ioc A z).filter Nat.Prime ∧ d_fn j ∣ r + j := by
    intro j hj
    simp only [d_fn, hj, ↓reduceDIte]
    exact Classical.choose_spec (hcover_j j hj)
  -- Step 2: Bound Z and S_selb
  have hZ_ge2 : 2 ≤ Z := by
    have h1 : (2 : ℝ) ≤ (P : ℝ) ^ (1 / 4 : ℝ) := by
      have h16 : (16 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP_ge_16
      have h2 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, ← rpow_natCast,
          ← rpow_mul (by norm_num)]; norm_num
      rw [← h2]
      exact rpow_le_rpow (by norm_num) h16 (by norm_num)
    exact Nat.le_floor h1
  have hZ_gt_half_exp : exp ((z : ℝ) / 8) / 2 ≤ (Z : ℝ) := by
    have hP14 : exp ((z : ℝ) / 8) ≤ (P : ℝ) ^ (1 / 4 : ℝ) := by
      have h1 : exp ((z : ℝ) / 8) = (exp ((z : ℝ) / 2)) ^ (1 / 4 : ℝ) := by
        rw [← exp_mul]; congr 1; ring
      rw [h1]
      exact rpow_le_rpow (exp_pos _).le hP_ge_exp (by norm_num)
    have hfl : (P : ℝ) ^ (1 / 4 : ℝ) - 1 < (Z : ℝ) := Nat.sub_one_lt_floor _
    have hexp_ge2 : (2 : ℝ) ≤ exp ((z : ℝ) / 8) := by
      have : (1 : ℝ) ≤ (z : ℝ) / 8 := by linarith
      have : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
      exact this.trans (exp_le_exp.mpr (by linarith))
    linarith
  have hZ_le_P14 : (Z : ℝ) ≤ (P : ℝ) ^ (1 / 4 : ℝ) := Nat.floor_le (by positivity)
  have hlogZ_ge : (z : ℝ) / 16 ≤ log (Z : ℝ) := by
    have h1 := log_le_log (by positivity) hZ_gt_half_exp
    rw [log_div (exp_pos _).ne' (by norm_num), log_exp] at h1
    have hlog2 : log 2 < 1 := by linarith [log_two_lt_d9]
    linarith
  let Q := (Ioc z Z).filter Nat.Prime
  let D := (Icc 1 Z).filter (fun e => Squarefree e ∧ ∀ p ∈ e.primeFactors, p ∈ Q)
  let S_selb := ∑ e ∈ D, (1 : ℝ) / (e.totient : ℝ)
  have hS_selb_ge : (z : ℝ) / (64 * exp (2 * C_inv) * (log (z : ℝ)) ^ 10) ≤ S_selb := by
    have h1 := selberg_S_ge z Z (by omega) hZ_ge2
    have hinv_z := hC_inv z (by omega)
    have hexp_z : exp (2 * ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
        exp (2 * C_inv) * (log (z : ℝ)) ^ 10 := by
      have hpow : (log (z : ℝ)) ^ 10 = exp (10 * log (log (z : ℝ))) := by
        rw [← rpow_natCast, rpow_def_of_pos (by linarith)]; congr 1; ring
      rw [hpow, ← exp_add]
      exact exp_le_exp.mpr (by linarith)
    calc
      (z : ℝ) / (64 * exp (2 * C_inv) * (log (z : ℝ)) ^ 10)
        = ((z : ℝ) / 16) / (4 * (exp (2 * C_inv) * (log (z : ℝ)) ^ 10)) := by ring
      _ ≤ log (Z : ℝ) / (4 * exp (2 * ∑ p ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / (p : ℝ))) := by
          exact div_le_div₀ (by positivity) hlogZ_ge (by positivity) (by gcongr)
      _ ≤ S_selb := h1
  have hS_selb_pos : 0 < S_selb := lt_of_lt_of_le (by positivity) hS_selb_ge
  -- Bound (P + 1) / S_selb + Z^2 ≤ C_sieve * P * (log z)^10 / z
  have hsieve_ub : ((P + 1 : ℕ) : ℝ) / S_selb + (Z : ℝ) ^ 2 ≤
      C_sieve * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ) := by
    have hZ2_le : (Z : ℝ) ^ 2 ≤ (P : ℝ) / (z : ℝ) := by
      have hZ2 : (Z : ℝ) ^ 2 ≤ (P : ℝ) ^ (1 / 2 : ℝ) := by
        have hsq : ((P : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (P : ℝ) ^ (1 / 2 : ℝ) := by
          rw [sq, ← rpow_add (by exact_mod_cast hP_pos)]; norm_num
        rw [← hsq]
        exact pow_le_pow_left₀ (by positivity) hZ_le_P14 2
      have hP12 : (z : ℝ) ≤ (P : ℝ) ^ (1 / 2 : ℝ) := by
        have h1 : (z : ℝ) ≤ exp ((z : ℝ) / 4) := by
          have : (z : ℝ) ≤ (z : ℝ) ^ 2 := by nlinarith
          exact this.trans hz_sq
        have h2 : exp ((z : ℝ) / 4) = (exp ((z : ℝ) / 2)) ^ (1 / 2 : ℝ) := by
          rw [← exp_mul]; congr 1; ring
        rw [h2] at h1
        exact h1.trans (rpow_le_rpow (exp_pos _).le hP_ge_exp (by norm_num))
      rw [le_div_iff₀ (by positivity)]
      calc
        (Z : ℝ) ^ 2 * (z : ℝ) ≤ (P : ℝ) ^ (1 / 2 : ℝ) * (P : ℝ) ^ (1 / 2 : ℝ) := by gcongr
        _ = (P : ℝ) := by rw [← rpow_add (by exact_mod_cast hP_pos)]; norm_num
    have hP1_le : ((P + 1 : ℕ) : ℝ) ≤ 2 * (P : ℝ) := by
      push_cast; linarith [show (1 : ℝ) ≤ (P : ℝ) by exact_mod_cast hP_pos]
    have hterm1 : ((P + 1 : ℕ) : ℝ) / S_selb ≤
        128 * exp (2 * C_inv) * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ) := by
      calc
        ((P + 1 : ℕ) : ℝ) / S_selb
          ≤ (2 * (P : ℝ)) / ((z : ℝ) / (64 * exp (2 * C_inv) * (log (z : ℝ)) ^ 10)) :=
            div_le_div₀ (by positivity) hP1_le (by positivity) hS_selb_ge
        _ = 128 * exp (2 * C_inv) * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ) := by
            rw [div_div_eq_mul_div]; ring
    have hterm2 : (Z : ℝ) ^ 2 ≤ (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ) := by
      have hlog1 : (1 : ℝ) ≤ (log (z : ℝ)) ^ 10 := one_le_pow₀ (by linarith)
      calc (Z : ℝ) ^ 2 ≤ (P : ℝ) / (z : ℝ) := hZ2_le
        _ = (P : ℝ) * 1 / (z : ℝ) := by ring
        _ ≤ (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ) := by gcongr
    have he1 : 1 ≤ exp (2 * C_inv) := one_le_exp (by positivity)
    have hpos_f : 0 ≤ (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ) := by positivity
    dsimp only [C_sieve]
    calc
      ((P + 1 : ℕ) : ℝ) / S_selb + (Z : ℝ) ^ 2
        ≤ 128 * exp (2 * C_inv) * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ) +
            (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ) := add_le_add hterm1 hterm2
      _ = (128 * exp (2 * C_inv) + 1) * ((P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ)) := by ring
      _ ≤ (200 * exp (2 * C_inv)) * ((P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith) hpos_f
      _ = 200 * exp (2 * C_inv) * (P : ℝ) * (log (z : ℝ)) ^ 10 / (z : ℝ) := by ring
  -- Step 3: Pointwise prime-cost bound for each k ∈ Icc 1 P
  let M := 200 * H * z
  have hM_pos : 1 ≤ M := by
    have hH1 : 1 ≤ H := by dsimp only [H, H_fn]; omega
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hH1) (by omega)
  have hpointwise : ∀ k ∈ Icc 1 P,
      let n := r + k * P
      (∑ j ∈ range H,
        ∑ p ∈ (n + j + 1).primeFactors, ((n + j + 1).factorization p : ℝ) * (p : ℝ)) / (n : ℝ) ≤
        (1 : ℝ) / 10 + ∑ j ∈ Icc 1 H, ∑ m ∈ Icc 1 M,
          if d_fn j * m ∣ n + j ∧ ((n + j) / (d_fn j * m)).Prime then
            (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) else 0 :=
    fun k hk =>
      pointwise_prime_cost_bound c₁ hc₁_ge1 z H A r d_fn hz10000 hP_ub hP_ge_exp
        (by dsimp only [H, H_fn]; omega) hH_le_6cz hH_sq hr_lt_P hd_spec k hk
  -- Step 4: Average over k ∈ Icc 1 P!
  let W_fn : ℕ → ℝ := fun k =>
    ∑ j ∈ Icc 1 H, ∑ m ∈ Icc 1 M,
      if d_fn j * m ∣ r + k * P + j ∧ ((r + k * P + j) / (d_fn j * m)).Prime then
        (2 : ℝ) / ((d_fn j : ℝ) * (m : ℝ)) else 0
  have hsum_W_le : ∑ k ∈ Icc 1 P, W_fn k ≤ (P : ℝ) / 10 :=
    average_sieve_bound c₁ C_inv hc₁_ge1 hC_inv_pos z H A Z r d_fn hz10000 hlogz_ge7
      hP_ge_exp hP_ge_16 (by dsimp only [H, H_fn]; omega) hH_le_6cz rfl hZ_ge2 hZ_le_P14
      hZ_big hlogz_sieve hsieve_ub hd_spec
  -- Step 5: Pigeonhole picks k ∈ Icc 1 P with W_fn k ≤ 1 / 10
  have hex_k : ∃ k ∈ Icc 1 P, W_fn k ≤ (1 : ℝ) / 10 := by
    by_contra hnot
    push Not at hnot
    have hgt : ∑ _k ∈ Icc 1 P, ((1 : ℝ) / 10) < ∑ k ∈ Icc 1 P, W_fn k := by
      apply sum_lt_sum_of_nonempty (nonempty_Icc.mpr hP_pos)
      exact hnot
    rw [sum_const, Nat.card_Icc, show P + 1 - 1 = P by omega, nsmul_eq_mul] at hgt
    linarith
  obtain ⟨k, hk, hWk⟩ := hex_k
  let n := r + k * P
  have hn_ge_P : P ≤ n := by
    have : 1 * P ≤ k * P := Nat.mul_le_mul_right P (mem_Icc.mp hk).1
    dsimp only [n]; omega
  have hn_pos : 0 < n := hP_pos.trans_le hn_ge_P
  refine ⟨n, hP_ge_N0.trans hn_ge_P, ?_⟩
  -- Show ⌊c * log n⌋₊ ≤ H
  have hh_le_H : ⌊c * log (n : ℝ)⌋₊ ≤ H := by
    have hn_le : (n : ℝ) ≤ 2 * (P : ℝ) ^ 2 := by
      have hkP : k * P ≤ P * P := Nat.mul_le_mul_right P (mem_Icc.mp hk).2
      have hPP : P ≤ P * P := Nat.le_mul_of_pos_left P hP_pos
      have : n ≤ 2 * P ^ 2 := by
        dsimp only [n]
        calc r + k * P ≤ P + P * P := by omega
          _ ≤ P * P + P * P := Nat.add_le_add_right hPP _
          _ = 2 * P ^ 2 := by ring
      exact_mod_cast this
    have hlogn : log (n : ℝ) ≤ 5 * (z : ℝ) := by
      calc
        log (n : ℝ) ≤ log (2 * (P : ℝ) ^ 2) :=
          log_le_log (by exact_mod_cast hn_pos) hn_le
        _ = log 2 + 2 * log (P : ℝ) := by
          rw [log_mul (by norm_num) (by positivity), log_pow]; ring
        _ ≤ 1 + 2 * (2 * (z : ℝ)) := by linarith [log_two_lt_d9]
        _ ≤ 5 * (z : ℝ) := by linarith
    have hcn : c * log (n : ℝ) ≤ 5 * c₁ * (z : ℝ) := by
      have hlogn_nn : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn_pos)
      calc c * log (n : ℝ) ≤ c₁ * log (n : ℝ) := mul_le_mul_of_nonneg_right hc_le_c₁ hlogn_nn
        _ ≤ c₁ * (5 * (z : ℝ)) := mul_le_mul_of_nonneg_left hlogn (by linarith)
        _ = 5 * c₁ * (z : ℝ) := by ring
    exact (Nat.floor_mono hcn).trans (Nat.le_succ _)
  -- Monotonicity of F in the window size + ratio_le_exp_prime_cost
  have hF_le : Erdos420.F (fun m => c * log m) n ≤
      (σ 0 (n + H).factorial : ℝ) / (σ 0 n.factorial : ℝ) := by
    rw [Erdos420.F]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    simp only [ArithmeticFunction.sigma_zero_apply]
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _)
      (Nat.factorial_dvd_factorial (Nat.add_le_add_left hh_le_H n)))
  have hcost_le :
      (∑ j ∈ range H,
        ∑ p ∈ (n + j + 1).primeFactors, ((n + j + 1).factorization p : ℝ) * (p : ℝ)) / (n : ℝ) ≤
        (1 : ℝ) / 5 := by
    have hp := hpointwise k hk
    dsimp only [n, W_fn] at hp hWk ⊢
    exact hp.trans ((add_le_add le_rfl hWk).trans (by norm_num))
  have hexp_lt2 : exp ((1 : ℝ) / 5) < 2 := by
    have hpow : (exp ((1 : ℝ) / 5)) ^ 5 < (2 : ℝ) ^ 5 := by
      rw [← exp_nat_mul]
      have h5 : (5 : ℕ) * ((1 : ℝ) / 5) = 1 := by norm_num
      rw [h5]
      exact exp_one_lt_d9.trans (by norm_num)
    by_contra hge
    push Not at hge
    exact not_le_of_gt hpow (pow_le_pow_left₀ (by norm_num) hge 5)
  calc
    Erdos420.F (fun m => c * log m) n
      ≤ (σ 0 (n + H).factorial : ℝ) / (σ 0 n.factorial : ℝ) := hF_le
    _ ≤ exp ((∑ j ∈ range H,
          ∑ p ∈ (n + j + 1).primeFactors, ((n + j + 1).factorization p : ℝ) * (p : ℝ)) / (n : ℝ)) :=
        ratio_le_exp_prime_cost n H hn_pos
    _ ≤ exp ((1 : ℝ) / 5) := exp_le_exp.mpr hcost_le
    _ < 2 := hexp_lt2

end Erdos420Proof

theorem OMA.solution : type_of% @Erdos420.erdos_420.variants.log_frequently_lt_two :=
  Erdos420Proof.main_theorem
