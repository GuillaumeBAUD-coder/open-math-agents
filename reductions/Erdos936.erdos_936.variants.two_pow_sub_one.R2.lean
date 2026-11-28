import FormalConjectures.ErdosProblems.«936»

-- Reduction Erdos936.erdos_936.variants.two_pow_sub_one.R2 of Erdős Problem 936 — two pow sub one
-- Credit: @umarsxlim
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Elementary prime-power cyclotomic reduction of Erdős Problem 936 (2^n - 1 case)

Unlike R1 (which assumes an abc estimate with exponent 3/2), this reduction is purely elementary
and splits `EventuallyNotPowerful (2 ^ · - 1)` into two weaker, independent statements:

* `H1`: Only finitely many prime-exponent Mersenne numbers `2 ^ p - 1` are powerful.
  (This is a subsequence of the target, hence strictly necessary.)
* `H2`: For every prime `p`, infinitely many prime-power cyclotomic numbers
  `Phi_{p^(k+1)}(2) = ∑ j ∈ Finset.range p, (2 ^ (p ^ k)) ^ j` are not powerful.
  (For `p = 2`, this asks only for infinitely many non-powerful Fermat numbers `2 ^ (2 ^ k) + 1`.)

`main` proves two elementary lifting/isolation lemmas:
1. If `n ≥ 2`, `(2 ^ n - 1).Powerful`, and `p` is the largest prime factor of `n`, then
   `(2 ^ p - 1).Powerful`. Thus `H1` forces all powerful exponents `n ≥ 2` to be `P`-smooth.
2. If `n ≥ 2` is `P`-smooth, `(2 ^ n - 1).Powerful`, and `p ^ (k + 1) ∣ n` with `P < p ^ (k + 1)`,
   then `Phi_{p^(k+1)}(2)` is powerful. Thus `H2` caps the `p`-adic valuation of `n` for each
   prime `p ≤ P`, bounding `n` explicitly by `∏ p ≤ P, p ^ k(p)`.
-/

open Finset Filter Nat

namespace OMA.R_Erdos936_erdos_936_variants_two_pow_sub_one_R2

/-- Only finitely many prime-exponent Mersenne numbers `2 ^ p - 1` are powerful. -/
def H1 : Prop :=
  ∀ᶠ p : ℕ in Filter.atTop, p.Prime → ¬ (2 ^ p - 1).Powerful

/-- For every prime `p`, infinitely many prime-power cyclotomic values
`Phi_{p^(k+1)}(2) = ∑ j ∈ Finset.range p, (2 ^ (p ^ k)) ^ j` are not powerful. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → ∃ᶠ k : ℕ in Filter.atTop,
    ¬ (∑ j ∈ Finset.range p, (2 ^ (p ^ k)) ^ j).Powerful

lemma geom_sum_mul_sub_one (a m : ℕ) (ha : 1 ≤ a) :
    (a - 1) * (∑ j ∈ Finset.range m, a ^ j) = a ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : 1 ≤ a ^ m := Nat.one_le_pow m a ha
    have h2 : 1 ≤ a ^ (m + 1) := Nat.one_le_pow (m + 1) a ha
    zify [ha, h1, h2]
    ring

lemma pow_two_prime_pow_eq_two (p : ℕ) [Fact p.Prime] (r : ℕ) :
    (2 : ZMod p) ^ (p ^ r) = 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, pow_mul, ih, ZMod.pow_card]

lemma zmod_two_ne_one_of_prime {q : ℕ} (hq : q.Prime) :
    (2 : ZMod q) ≠ 1 := by
  have : Fact q.Prime := ⟨hq⟩
  intro h
  have hsub : (2 : ZMod q) - 1 = 1 - 1 := congrArg (· - 1) h
  norm_num at hsub

lemma zmod_pow_eq_one_of_dvd {a k q : ℕ} (ha : 1 ≤ a) (hdvd : q ∣ a ^ k - 1) :
    (a : ZMod q) ^ k = 1 := by
  have h1 : 1 ≤ a ^ k := Nat.one_le_pow k a ha
  have h0 : ((a ^ k - 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one] at h0
  exact sub_eq_zero.mp h0

lemma dvd_pow_sub_one_of_zmod {a k q : ℕ} (ha : 1 ≤ a) (h : (a : ZMod q) ^ k = 1) :
    q ∣ a ^ k - 1 := by
  have h1 : 1 ≤ a ^ k := Nat.one_le_pow k a ha
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, h, sub_self]

lemma not_dvd_geom_sum_of_dvd_sub_one {a m q : ℕ} (ha : 1 ≤ a)
    (hdvd : q ∣ a - 1) (hndvd : ¬ q ∣ m) :
    ¬ q ∣ ∑ j ∈ Finset.range m, a ^ j := by
  intro hS
  have ha1 : (a : ZMod q) = 1 := by
    have h0 := zmod_pow_eq_one_of_dvd (k := 1) ha (by simpa using hdvd)
    simpa using h0
  have h0 : ((∑ j ∈ Finset.range m, a ^ j : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hS
  rw [Nat.cast_sum] at h0
  have hsum : (∑ j ∈ Finset.range m, ((a ^ j : ℕ) : ZMod q)) = (m : ZMod q) := by
    simp [Nat.cast_pow, ha1]
  rw [hsum] at h0
  exact hndvd ((ZMod.natCast_eq_zero_iff m q).1 h0)

lemma two_ne_zero_zmod_of_dvd_two_pow_sub_one {k q : ℕ} (hk : 1 ≤ k) (hq : q.Prime)
    (hdvd : q ∣ 2 ^ k - 1) : (2 : ZMod q) ≠ 0 := by
  intro h0
  have hq2 : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).1 h0
  have hqeq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hq2
  subst hqeq
  have heven : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  have hodd : ¬ 2 ∣ 2 ^ k - 1 := by
    intro h
    have h2 : 2 ∣ (2 ^ k - 1) + 1 := by rwa [Nat.sub_add_cancel h1]
    have h3 : 2 ∣ 1 := (Nat.dvd_add_right h).1 h2
    omega
  exact hodd hdvd

/-- If `n ≥ 2`, `2 ^ n - 1` is powerful, and `p` is the greatest prime factor of `n`,
then `2 ^ p - 1` is powerful. -/
lemma powerful_mersenne_of_greatest_prime_factor {n p : ℕ} (hn : 2 ≤ n)
    (hpow : (2 ^ n - 1).Powerful) (hp : p.Prime) (hpn : p ∣ n)
    (hmax : ∀ r : ℕ, r.Prime → r ∣ n → r ≤ p) :
    (2 ^ p - 1).Powerful := by
  intro q hq_mem
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq_dvd : q ∣ 2 ^ p - 1 := Nat.dvd_of_mem_primeFactors hq_mem
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨m, rfl⟩ := hpn
  have hm_pos : 1 ≤ m := by
    by_contra hm
    have : m = 0 := by omega
    subst this
    omega
  have hfactor : (2 ^ p - 1) * (∑ j ∈ Finset.range m, (2 ^ p) ^ j) = 2 ^ (p * m) - 1 := by
    rw [pow_mul]
    exact geom_sum_mul_sub_one (2 ^ p) m (Nat.one_le_pow p 2 (by omega))
  have hq_dvd_big : q ∣ 2 ^ (p * m) - 1 := by
    rw [← hfactor]
    exact dvd_mul_of_dvd_left hq_dvd _
  have hbig_ne : 2 ^ (p * m) - 1 ≠ 0 := by
    have : 2 ^ 1 < 2 ^ (p * m) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hq2_big : q ^ 2 ∣ 2 ^ (p * m) - 1 :=
    hpow q (Nat.mem_primeFactors.2 ⟨hq, hq_dvd_big, hbig_ne⟩)
  have h2ne : (2 : ZMod q) ≠ 0 :=
    two_ne_zero_zmod_of_dvd_two_pow_sub_one (by have := hp.two_le; omega) hq hq_dvd
  have h2p : (2 : ZMod q) ^ p = 1 := zmod_pow_eq_one_of_dvd (a := 2) (by norm_num) hq_dvd
  have hord_dvd_p : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one h2p
  have hord_ne_one : orderOf (2 : ZMod q) ≠ 1 := by
    intro h1
    rw [orderOf_eq_one_iff] at h1
    exact zmod_two_ne_one_of_prime hq h1
  have hord_eq : orderOf (2 : ZMod q) = p :=
    (hp.eq_one_or_self_of_dvd _ hord_dvd_p).resolve_left hord_ne_one
  have hfermat : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hp_dvd_q1 : p ∣ q - 1 := by
    rw [← hord_eq]
    exact orderOf_dvd_of_pow_eq_one hfermat
  have hp_lt_q : p < q := by
    have hq1_pos : 0 < q - 1 := by have := hq.two_le; omega
    have hle : p ≤ q - 1 := Nat.le_of_dvd hq1_pos hp_dvd_q1
    omega
  have hq_ndvd_n : ¬ q ∣ p * m := by
    intro hqn
    have := hmax q hq hqn
    omega
  have hq_ndvd_m : ¬ q ∣ m := fun hqm => hq_ndvd_n (dvd_mul_of_dvd_right hqm p)
  have hq_ndvd_S : ¬ q ∣ ∑ j ∈ Finset.range m, (2 ^ p) ^ j :=
    not_dvd_geom_sum_of_dvd_sub_one (Nat.one_le_pow p 2 (by omega)) hq_dvd hq_ndvd_m
  have hcop : Nat.Coprime (q ^ 2) (∑ j ∈ Finset.range m, (2 ^ p) ^ j) :=
    (hq.coprime_iff_not_dvd.2 hq_ndvd_S).pow_left 2
  rw [← hfactor] at hq2_big
  exact hcop.dvd_of_dvd_mul_right hq2_big

/-- If `n ≥ 2` is `P`-smooth, `2 ^ n - 1` is powerful, and `p ^ (k + 1) ∣ n` with
`P < p ^ (k + 1)`, then `Phi_{p^(k+1)}(2)` is powerful. -/
lemma powerful_prime_pow_cyclotomic_of_smooth {n P p k : ℕ} (hn : 2 ≤ n)
    (hpow : (2 ^ n - 1).Powerful) (hsmooth : ∀ r : ℕ, r.Prime → r ∣ n → r ≤ P)
    (hp : p.Prime) (hdvd : p ^ (k + 1) ∣ n) (hgt : P < p ^ (k + 1)) :
    (∑ j ∈ Finset.range p, (2 ^ (p ^ k)) ^ j).Powerful := by
  set Φ := ∑ j ∈ Finset.range p, (2 ^ (p ^ k)) ^ j
  intro q hq_mem
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq_dvd_Φ : q ∣ Φ := Nat.dvd_of_mem_primeFactors hq_mem
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, rfl⟩ := hdvd
  have hm_pos : 1 ≤ m := by
    by_contra hm
    have : m = 0 := by omega
    subst this
    omega
  have hΦ_mul : (2 ^ (p ^ k) - 1) * Φ = 2 ^ (p ^ (k + 1)) - 1 := by
    have hpow_eq : (2 ^ (p ^ k)) ^ p = 2 ^ (p ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]
    rw [← hpow_eq]
    exact geom_sum_mul_sub_one (2 ^ (p ^ k)) p (Nat.one_le_pow _ 2 (by omega))
  set S := ∑ j ∈ Finset.range m, (2 ^ (p ^ (k + 1))) ^ j
  have hS_mul : (2 ^ (p ^ (k + 1)) - 1) * S = 2 ^ (p ^ (k + 1) * m) - 1 := by
    rw [pow_mul]
    exact geom_sum_mul_sub_one (2 ^ (p ^ (k + 1))) m (Nat.one_le_pow _ 2 (by omega))
  have hq_dvd_pk1 : q ∣ 2 ^ (p ^ (k + 1)) - 1 := by
    rw [← hΦ_mul]
    exact dvd_mul_of_dvd_right hq_dvd_Φ _
  have hq_dvd_big : q ∣ 2 ^ (p ^ (k + 1) * m) - 1 := by
    rw [← hS_mul]
    exact dvd_mul_of_dvd_left hq_dvd_pk1 _
  have hbig_ne : 2 ^ (p ^ (k + 1) * m) - 1 ≠ 0 := by
    have : 2 ^ 1 < 2 ^ (p ^ (k + 1) * m) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hq2_big : q ^ 2 ∣ 2 ^ (p ^ (k + 1) * m) - 1 :=
    hpow q (Nat.mem_primeFactors.2 ⟨hq, hq_dvd_big, hbig_ne⟩)
  have hq_ne_p : q ≠ p := by
    intro hqp
    subst hqp
    have h1 : (2 : ZMod q) ^ (q ^ (k + 1)) = 1 :=
      zmod_pow_eq_one_of_dvd (a := 2) (by norm_num) hq_dvd_pk1
    have h2 : (2 : ZMod q) ^ (q ^ (k + 1)) = 2 :=
      pow_two_prime_pow_eq_two q (k + 1)
    exact zmod_two_ne_one_of_prime hq (h2.symm.trans h1)
  have hq_ndvd_pk : ¬ q ∣ 2 ^ (p ^ k) - 1 := by
    intro hqpk
    have hndvd_p : ¬ q ∣ p := by
      intro hqp
      exact hq_ne_p ((Nat.prime_dvd_prime_iff_eq hq hp).1 hqp)
    exact not_dvd_geom_sum_of_dvd_sub_one (Nat.one_le_pow _ 2 (by omega)) hqpk hndvd_p hq_dvd_Φ
  have h2ne : (2 : ZMod q) ≠ 0 :=
    two_ne_zero_zmod_of_dvd_two_pow_sub_one (Nat.one_le_pow _ _ hp.pos) hq hq_dvd_pk1
  have h2_pk1 : (2 : ZMod q) ^ (p ^ (k + 1)) = 1 :=
    zmod_pow_eq_one_of_dvd (a := 2) (by norm_num) hq_dvd_pk1
  have h2_pk : (2 : ZMod q) ^ (p ^ k) ≠ 1 := fun h =>
    hq_ndvd_pk (dvd_pow_sub_one_of_zmod (a := 2) (by norm_num) h)
  have hord_dvd : orderOf (2 : ZMod q) ∣ p ^ (k + 1) := orderOf_dvd_of_pow_eq_one h2_pk1
  obtain ⟨j, hj_le, hj_eq⟩ := (Nat.dvd_prime_pow hp).1 hord_dvd
  have hj_eq_k1 : j = k + 1 := by
    by_contra hne
    have hjk : j ≤ k := by omega
    have hdvd_k : orderOf (2 : ZMod q) ∣ p ^ k := by
      rw [hj_eq]
      exact Nat.pow_dvd_pow p hjk
    exact h2_pk (orderOf_dvd_iff_pow_eq_one.1 hdvd_k)
  have hord_eq : orderOf (2 : ZMod q) = p ^ (k + 1) := by rw [hj_eq, hj_eq_k1]
  have hfermat : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hpk1_dvd_q1 : p ^ (k + 1) ∣ q - 1 := by
    rw [← hord_eq]
    exact orderOf_dvd_of_pow_eq_one hfermat
  have hpk1_lt_q : p ^ (k + 1) < q := by
    have hq1_pos : 0 < q - 1 := by have := hq.two_le; omega
    have hle : p ^ (k + 1) ≤ q - 1 := Nat.le_of_dvd hq1_pos hpk1_dvd_q1
    omega
  have hq_ndvd_n : ¬ q ∣ p ^ (k + 1) * m := by
    intro hqn
    have := hsmooth q hq hqn
    omega
  have hq_ndvd_m : ¬ q ∣ m := fun hqm => hq_ndvd_n (dvd_mul_of_dvd_right hqm _)
  have hq_ndvd_S : ¬ q ∣ S :=
    not_dvd_geom_sum_of_dvd_sub_one (Nat.one_le_pow _ 2 (by omega)) hq_dvd_pk1 hq_ndvd_m
  have hq_ndvd_rest : ¬ q ∣ (2 ^ (p ^ k) - 1) * S := by
    intro hprod
    rcases hq.dvd_mul.1 hprod with h1 | h2
    · exact hq_ndvd_pk h1
    · exact hq_ndvd_S h2
  have hcop : Nat.Coprime (q ^ 2) ((2 ^ (p ^ k) - 1) * S) :=
    (hq.coprime_iff_not_dvd.2 hq_ndvd_rest).pow_left 2
  have hfull : Φ * ((2 ^ (p ^ k) - 1) * S) = 2 ^ (p ^ (k + 1) * m) - 1 := by
    rw [← hS_mul, ← hΦ_mul]
    ring
  rw [← hfull] at hq2_big
  exact hcop.dvd_of_dvd_mul_right hq2_big

theorem main : H1 → H2 → type_of% @Erdos936.erdos_936.variants.two_pow_sub_one := by
  intro hH1 hH2
  change ∀ᶠ n : ℕ in Filter.atTop, ¬ (2 ^ n - 1).Powerful
  unfold H1 at hH1
  unfold H2 at hH2
  rw [Filter.eventually_atTop] at hH1
  obtain ⟨P, hP⟩ := hH1
  have hsmooth_all : ∀ n : ℕ, 2 ≤ n → (2 ^ n - 1).Powerful →
      ∀ r : ℕ, r.Prime → r ∣ n → r ≤ P := by
    intro n hn hpow r hr hrn
    have hne : n.primeFactors.Nonempty := by
      refine ⟨r, Nat.mem_primeFactors.2 ⟨hr, hrn, by omega⟩⟩
    set p := n.primeFactors.max' hne
    have hp_mem : p ∈ n.primeFactors := Finset.max'_mem _ hne
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
    have hmax : ∀ q : ℕ, q.Prime → q ∣ n → q ≤ p := by
      intro q hq hqn
      exact Finset.le_max' _ q (Nat.mem_primeFactors.2 ⟨hq, hqn, by omega⟩)
    have hpow_p : (2 ^ p - 1).Powerful :=
      powerful_mersenne_of_greatest_prime_factor hn hpow hp hpn hmax
    have hp_le_P : p ≤ P := by
      by_contra hgt
      have hge : P ≤ p := by omega
      exact hP p hge hp hpow_p
    exact (hmax r hr hrn).trans hp_le_P
  have hex_k : ∀ p : ℕ, ∃ k : ℕ, ¬ p.Prime ∨
      (P < p ^ (k + 1) ∧ ¬ (∑ j ∈ Finset.range p, (2 ^ (p ^ k)) ^ j).Powerful) := by
    intro p
    by_cases hp : p.Prime
    · have hfreq := (Filter.frequently_atTop.1 (hH2 p hp)) P
      obtain ⟨k, hkP, hk_not⟩ := hfreq
      refine ⟨k, Or.inr ⟨?_, hk_not⟩⟩
      have h1 : P < 2 ^ P := Nat.lt_two_pow_self
      have h2 : 2 ^ P ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : 2 ^ (k + 1) ≤ p ^ (k + 1) := Nat.pow_le_pow_left hp.two_le (k + 1)
      omega
    · exact ⟨0, Or.inl hp⟩
  choose k hk using hex_k
  set B := (Finset.range (P + 1)).filter Nat.Prime
  set M := ∏ p ∈ B, p ^ (k p)
  rw [Filter.eventually_atTop]
  refine ⟨max 2 (M + 1), fun n hn hpow => ?_⟩
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hsmooth : ∀ r : ℕ, r.Prime → r ∣ n → r ≤ P := hsmooth_all n hn2 hpow
  have hsub : n.primeFactors ⊆ B := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
    have hpP : p ≤ P := hsmooth p hp hpn
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩
  have hfac_le : ∀ p ∈ n.primeFactors, n.factorization p ≤ k p := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    obtain ⟨hgt, hnotpow⟩ := (hk p).resolve_left (not_not.2 hp)
    by_contra hlt
    have hge : k p + 1 ≤ n.factorization p := by omega
    have hdvd : p ^ (k p + 1) ∣ n :=
      (Nat.pow_dvd_pow p hge).trans (Nat.ordProj_dvd n p)
    exact hnotpow (powerful_prime_pow_cyclotomic_of_smooth hn2 hpow hsmooth hp hdvd hgt)
  have hn_le_M : n ≤ M := by
    have hprod_eq : n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) :=
      (Nat.prod_factorization_pow_eq_self (by omega)).symm
    rw [hprod_eq]
    calc
      ∏ p ∈ n.primeFactors, p ^ (n.factorization p)
          ≤ ∏ p ∈ n.primeFactors, p ^ (k p) := by
            refine Finset.prod_le_prod' fun p hp_mem => ?_
            exact Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp_mem).pos (hfac_le p hp_mem)
      _ ≤ ∏ p ∈ B, p ^ (k p) := by
            refine Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hpB _ => ?_
            exact Nat.one_le_pow _ _ (Finset.mem_filter.1 hpB).2.pos
  have : M + 1 ≤ n := (le_max_right _ _).trans hn
  omega

end OMA.R_Erdos936_erdos_936_variants_two_pow_sub_one_R2
