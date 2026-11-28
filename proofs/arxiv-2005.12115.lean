import OMAStatements.S_arxiv_2005_12115

-- Problem: arXiv 2005.12115 (Zelinsky), Theorem 2: a primitive non-deficient number
-- n = p_1^{a_1} ⋯ p_k^{a_k} has a component with p_i^{a_i+1} < 2k · rad(n).
-- Proof (by contradiction; R = rad n, F = ∏ (p_i - 1), q_i = p_i^{a_i+1} ≥ 2kR for all i):
--  * σ(n)/n = ∏ p_i/(p_i-1) · ∏ (1 - 1/q_i) =: G·W with G = R/F, W < 1; as σ(n)/n ≥ 2, G > 2,
--    hence R ≥ 2F + 1 (integers).
--  * k distinct integers ≥ k+2 have ∏ x/(x-1) ≤ (2k+1)/(k+1) < 2, so some prime p | n is ≤ k+1.
--  * W ≥ 1 - ∑ 1/q_i ≥ 1 - 1/(2R), so 2F·σ(n)/n ≥ 2R - 1 ≥ 4F + 1.
--  * For that p: q - p ≥ 4F(p-1), which gives σ(n)(q - p) ≥ 2n(q - 1); this is exactly
--    σ(n/p) ≥ 2(n/p), so the proper divisor n/p is non-deficient, contradicting primitivity.

open Finset

namespace OMA.Proof_arxiv_2005_12115

open OMA.S_arxiv_2005_12115


lemma prod_ratio_le (c : ℕ) (hc : 2 ≤ c) (S : Finset ℕ) :
    (∀ x ∈ S, c ≤ x) →
      ∏ x ∈ S, ((x : ℚ) / ((x : ℚ) - 1)) ≤ ((c : ℚ) + (S.card : ℚ) - 1) / ((c : ℚ) - 1) := by
  have hc1 : (0 : ℚ) < (c : ℚ) - 1 := by
    have : (2 : ℚ) ≤ c := by exact_mod_cast hc
    linarith
  induction S using Finset.induction_on_max with
  | empty =>
    intro _
    rw [Finset.prod_empty, Finset.card_empty, le_div_iff₀ hc1]
    push_cast
    linarith
  | insert a s ha ih =>
    intro h
    have hs : ∀ x ∈ s, c ≤ x := fun x hx => h x (mem_insert_of_mem hx)
    have ih' := ih hs
    have hnot : a ∉ s := fun hmem => lt_irrefl a (ha a hmem)
    rw [prod_insert hnot, card_insert_of_notMem hnot]
    have hcard : c + s.card ≤ a := by
      have hsub : s ⊆ Finset.Ico c a := fun x hx => Finset.mem_Ico.mpr ⟨hs x hx, ha x hx⟩
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Ico] at h1
      have h2 : c ≤ a := h a (mem_insert_self a s)
      omega
    have hcq : (c : ℚ) + (s.card : ℚ) ≤ (a : ℚ) := by exact_mod_cast hcard
    have hk0 : (0 : ℚ) ≤ (s.card : ℚ) := Nat.cast_nonneg _
    have ha1 : (0 : ℚ) < (a : ℚ) - 1 := by linarith
    have hd : (0 : ℚ) < (c : ℚ) + (s.card : ℚ) - 1 := by linarith
    have hd' : (c : ℚ) + (s.card : ℚ) - 1 ≠ 0 := hd.ne'
    have hc1' : (c : ℚ) - 1 ≠ 0 := hc1.ne'
    have h1 : (a : ℚ) / ((a : ℚ) - 1) ≤
        ((c : ℚ) + (s.card : ℚ)) / ((c : ℚ) + (s.card : ℚ) - 1) := by
      rw [div_le_div_iff₀ ha1 hd]
      nlinarith
    have hprod_nonneg : (0 : ℚ) ≤ ∏ x ∈ s, ((x : ℚ) / ((x : ℚ) - 1)) := by
      apply Finset.prod_nonneg
      intro x hx
      have : (2 : ℚ) ≤ x := by exact_mod_cast le_trans hc (hs x hx)
      apply div_nonneg <;> linarith
    calc (a : ℚ) / ((a : ℚ) - 1) * ∏ x ∈ s, ((x : ℚ) / ((x : ℚ) - 1))
        ≤ ((c : ℚ) + (s.card : ℚ)) / ((c : ℚ) + (s.card : ℚ) - 1) *
            (((c : ℚ) + (s.card : ℚ) - 1) / ((c : ℚ) - 1)) := by
          apply mul_le_mul h1 ih' hprod_nonneg
          apply div_nonneg <;> linarith
      _ = ((c : ℚ) + (s.card : ℚ)) / ((c : ℚ) - 1) := by
          field_simp
      _ = ((c : ℚ) + ((s.card + 1 : ℕ) : ℚ) - 1) / ((c : ℚ) - 1) := by
          push_cast; ring

lemma one_sub_sum_le_prod (S : Finset ℕ) (t : ℕ → ℚ) :
    (∀ i ∈ S, 0 ≤ t i ∧ t i ≤ 1) → 1 - ∑ i ∈ S, t i ≤ ∏ i ∈ S, (1 - t i) := by
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro h
    have h1 := h a (mem_insert_self a s)
    have ih' := ih (fun i hi => h i (mem_insert_of_mem hi))
    have hsum : 0 ≤ ∑ i ∈ s, t i := Finset.sum_nonneg (fun i hi => (h i (mem_insert_of_mem hi)).1)
    rw [sum_insert ha, prod_insert ha]
    have h2 : (1 - t a) * (1 - ∑ i ∈ s, t i) ≤ (1 - t a) * ∏ i ∈ s, (1 - t i) :=
      mul_le_mul_of_nonneg_left ih' (by linarith [h1.2])
    nlinarith [mul_nonneg h1.1 hsum]

lemma deficient_iff (n : ℕ) : n.Deficient ↔ (ArithmeticFunction.sigma 1) n < 2 * n := by
  unfold Nat.Deficient
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

lemma sigma_pp (p a : ℕ) (hp : p.Prime) :
    (((ArithmeticFunction.sigma 1) (p ^ a) : ℕ) : ℚ) / (p : ℚ) ^ a =
      (p : ℚ) / ((p : ℚ) - 1) * (1 - 1 / (p : ℚ) ^ (a + 1)) := by
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (p : ℚ) - 1 ≠ 0 := fun h => by linarith
  have hp0 : (p : ℚ) ≠ 0 := fun h => by linarith
  have hpa : (p : ℚ) ^ a ≠ 0 := pow_ne_zero _ hp0
  have hpa1 : (p : ℚ) ^ (a + 1) ≠ 0 := pow_ne_zero _ hp0
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  have hgs : ((∑ k ∈ range (a + 1), p ^ k : ℕ) : ℚ) = ((p : ℚ) ^ (a + 1) - 1) / ((p : ℚ) - 1) := by
    push_cast
    rw [eq_div_iff hp1]
    exact geom_sum_mul _ _
  rw [hgs, div_div, div_eq_iff (mul_ne_zero hp1 hpa)]
  have e1 : (p : ℚ) / ((p : ℚ) - 1) * (1 - 1 / (p : ℚ) ^ (a + 1)) * (((p : ℚ) - 1) * (p : ℚ) ^ a)
      = (p : ℚ) * (p : ℚ) ^ a * (1 - 1 / (p : ℚ) ^ (a + 1)) * (((p : ℚ) - 1) / ((p : ℚ) - 1)) := by
    ring
  rw [e1, div_self hp1, mul_one, mul_sub, mul_one, ← pow_succ', mul_one_div, div_self hpa1]

lemma sigma_div (n : ℕ) (hn : n ≠ 0) :
    (((ArithmeticFunction.sigma 1) n : ℕ) : ℚ) / (n : ℚ) = ∏ p ∈ n.primeFactors,
      ((p : ℚ) / ((p : ℚ) - 1) * (1 - 1 / (p : ℚ) ^ (n.factorization p + 1))) := by
  have h1 : (ArithmeticFunction.sigma 1) n = ∏ p ∈ n.primeFactors, (ArithmeticFunction.sigma 1) (p ^ n.factorization p) := by
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization ((ArithmeticFunction.sigma 1))
      ArithmeticFunction.isMultiplicative_sigma hn]
    rfl
  have h2 : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    have h := Nat.prod_factorization_pow_eq_self hn
    exact h
  have hcast : (((ArithmeticFunction.sigma 1) n : ℕ) : ℚ) / (n : ℚ) = ∏ p ∈ n.primeFactors,
      ((((ArithmeticFunction.sigma 1) (p ^ n.factorization p) : ℕ) : ℚ) / (p : ℚ) ^ n.factorization p) := by
    rw [Finset.prod_div_distrib]
    have e1 : (((ArithmeticFunction.sigma 1) n : ℕ) : ℚ) = ∏ p ∈ n.primeFactors, (((ArithmeticFunction.sigma 1) (p ^ n.factorization p) : ℕ) : ℚ) := by
      rw [h1, Nat.cast_prod]
    have e2 : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
      have : ((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ℚ) = (n : ℚ) := by rw [h2]
      rw [← this]; push_cast; rfl
    rw [← e1, ← e2]
  rw [hcast]
  apply Finset.prod_congr rfl
  intro p hp
  exact sigma_pp p _ (Nat.prime_of_mem_primeFactors hp)

lemma drop_prime (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n)
    (hineq : 2 * (n : ℚ) * ((p : ℚ) ^ (n.factorization p + 1) - 1) ≤
      (((ArithmeticFunction.sigma 1) n : ℕ) : ℚ) * ((p : ℚ) ^ (n.factorization p + 1) - p)) :
    ∃ m, m ∣ n ∧ m ≠ n ∧ 2 * m ≤ (ArithmeticFunction.sigma 1) m := by
  have ha : 0 < n.factorization p := hp.factorization_pos_of_dvd hn hpn
  obtain ⟨b, hb⟩ : ∃ b, n.factorization p = b + 1 := ⟨n.factorization p - 1, by omega⟩
  have hdec := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop := Nat.coprime_ordCompl hp hn
  rw [hb] at hdec hcop hineq
  generalize n / p ^ (b + 1) = u at hdec hcop
  have hm : n = p * (p ^ b * u) := by rw [← hdec]; ring
  have hP2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hP0 : (0 : ℚ) < p := by linarith
  refine ⟨p ^ b * u, ⟨p, by rw [hm]; ring⟩, ?_, ?_⟩
  · intro h
    rw [h] at hm
    have h2 : 2 * n ≤ p * n := Nat.mul_le_mul_right n hp.two_le
    have h3 : 0 < n := Nat.pos_of_ne_zero hn
    linarith
  · have hs_n : (ArithmeticFunction.sigma 1) n = (ArithmeticFunction.sigma 1) (p ^ (b + 1)) * (ArithmeticFunction.sigma 1) u := by
      rw [← hdec]
      exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (Nat.Coprime.pow_left _ hcop)
    have hs_m : (ArithmeticFunction.sigma 1) (p ^ b * u) = (ArithmeticFunction.sigma 1) (p ^ b) * (ArithmeticFunction.sigma 1) u :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow_left _ hcop)
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp] at hs_n hs_m
    have hA := geom_sum_mul (p : ℚ) (b + 1 + 1)
    have hB := geom_sum_mul (p : ℚ) (b + 1)
    have hApos : (0 : ℚ) < ∑ i ∈ range (b + 1 + 1), (p : ℚ) ^ i :=
      Finset.sum_pos (fun i _ => pow_pos hP0 i) ⟨0, mem_range.mpr (by omega)⟩
    have hnq : (n : ℚ) = (p : ℚ) ^ (b + 1) * (u : ℚ) := by
      rw [← hdec]; push_cast; ring
    have hsnq : (((ArithmeticFunction.sigma 1) n : ℕ) : ℚ) = (∑ i ∈ range (b + 1 + 1), (p : ℚ) ^ i) * (((ArithmeticFunction.sigma 1) u : ℕ) : ℚ) := by
      rw [hs_n]; push_cast; ring
    rw [hnq, hsnq] at hineq
    have cpos : (0 : ℚ) < (∑ i ∈ range (b + 1 + 1), (p : ℚ) ^ i) * (p : ℚ) * ((p : ℚ) - 1) :=
      mul_pos (mul_pos hApos hP0) (by linarith)
    have e1 : 2 * ((p : ℚ) ^ b * (u : ℚ)) *
        ((∑ i ∈ range (b + 1 + 1), (p : ℚ) ^ i) * (p : ℚ) * ((p : ℚ) - 1)) =
        2 * ((p : ℚ) ^ (b + 1) * (u : ℚ)) * ((p : ℚ) ^ (b + 1 + 1) - 1) := by
      rw [← hA]; ring
    have e2 : (∑ i ∈ range (b + 1), (p : ℚ) ^ i) * (((ArithmeticFunction.sigma 1) u : ℕ) : ℚ) *
        ((∑ i ∈ range (b + 1 + 1), (p : ℚ) ^ i) * (p : ℚ) * ((p : ℚ) - 1)) =
        (∑ i ∈ range (b + 1 + 1), (p : ℚ) ^ i) * (((ArithmeticFunction.sigma 1) u : ℕ) : ℚ) *
          ((p : ℚ) ^ (b + 1 + 1) - p) := by
      have e3 : (p : ℚ) ^ (b + 1 + 1) - p =
          (p : ℚ) * ((∑ i ∈ range (b + 1), (p : ℚ) ^ i) * ((p : ℚ) - 1)) := by
        rw [hB]; ring
      rw [e3]; ring
    have hfin : 2 * ((p : ℚ) ^ b * (u : ℚ)) ≤
        (∑ i ∈ range (b + 1), (p : ℚ) ^ i) * (((ArithmeticFunction.sigma 1) u : ℕ) : ℚ) :=
      le_of_mul_le_mul_right (by rw [e1, e2]; exact hineq) cpos
    have hcastgoal : ((2 * (p ^ b * u) : ℕ) : ℚ) ≤ (((ArithmeticFunction.sigma 1) (p ^ b * u) : ℕ) : ℚ) := by
      rw [hs_m]; push_cast; linarith
    exact_mod_cast hcastgoal

theorem key (n : ℕ) (hPND : PrimitiveNonDeficient n) :
    ∃ p ∈ n.primeFactors,
      p ^ (n.factorization p + 1) < 2 * n.primeFactors.card * ∏ q ∈ n.primeFactors, q := by
  obtain ⟨hn0, hnd, hprim⟩ := hPND
  have hn : n ≠ 0 := by omega
  by_contra hcon
  push_neg at hcon
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn0
  have hσ : 2 * n ≤ (ArithmeticFunction.sigma 1) n := by
    have := (deficient_iff n).not.mp hnd
    omega
  have hσq : 2 * (n : ℚ) ≤ (((ArithmeticFunction.sigma 1) n : ℕ) : ℚ) := by exact_mod_cast hσ
  have hH := sigma_div n hn
  rw [Finset.prod_mul_distrib] at hH
  have hprime : ∀ p ∈ n.primeFactors, (2 : ℚ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hGpos : (0 : ℚ) < ∏ p ∈ n.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
    apply Finset.prod_pos
    intro p hp
    have := hprime p hp
    apply div_pos <;> linarith
  have ht : ∀ p ∈ n.primeFactors, 0 < 1 / (p : ℚ) ^ (n.factorization p + 1) ∧
      1 / (p : ℚ) ^ (n.factorization p + 1) ≤ 1 / 2 := by
    intro p hp
    have h2 := hprime p hp
    have hpow : (2 : ℚ) ≤ (p : ℚ) ^ (n.factorization p + 1) := by
      calc (2 : ℚ) ≤ p := h2
        _ = (p : ℚ) ^ 1 := (pow_one _).symm
        _ ≤ (p : ℚ) ^ (n.factorization p + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    constructor
    · apply div_pos one_pos; linarith
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hne : n.primeFactors.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hH
    simp only [Finset.prod_empty, mul_one] at hH
    rw [div_eq_iff hnq.ne'] at hH
    linarith
  have hW1 : ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (n.factorization p + 1)) < 1 := by
    calc ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ (n.factorization p + 1))
        < ∏ p ∈ n.primeFactors, (1 : ℚ) := by
          apply Finset.prod_lt_prod_of_nonempty
          · intro p hp; have := ht p hp; linarith [this.2]
          · intro p hp; have := ht p hp; linarith [this.1]
          · exact hne
      _ = 1 := Finset.prod_const_one
  have hWlow0 := one_sub_sum_le_prod n.primeFactors
    (fun p => 1 / (p : ℚ) ^ (n.factorization p + 1))
    (fun p hp => ⟨(ht p hp).1.le, by linarith [(ht p hp).2]⟩)
  beta_reduce at hWlow0
  have hF : ((∏ q ∈ n.primeFactors, (q - 1) : ℕ) : ℚ) = ∏ q ∈ n.primeFactors, ((q : ℚ) - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_pred (Nat.prime_of_mem_primeFactors hp).pos]
  have hR : ((∏ q ∈ n.primeFactors, q : ℕ) : ℚ) = ∏ q ∈ n.primeFactors, (q : ℚ) :=
    Nat.cast_prod _ _
  have hGRF0 : ∏ p ∈ n.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) =
      ((∏ q ∈ n.primeFactors, q : ℕ) : ℚ) / ((∏ q ∈ n.primeFactors, (q - 1) : ℕ) : ℚ) := by
    rw [hR, hF, ← Finset.prod_div_distrib]
  have hFpos0 : 0 < ∏ q ∈ n.primeFactors, (q - 1) :=
    Finset.prod_pos (fun q hq => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hq).one_lt)
  have hk1' : 1 ≤ n.primeFactors.card := Finset.card_pos.mpr hne
  have hA0 := prod_ratio_le (n.primeFactors.card + 2) (by omega) n.primeFactors
  have hsumcard := Finset.sum_le_card_nsmul n.primeFactors
    (fun p => 1 / (p : ℚ) ^ (n.factorization p + 1))
  beta_reduce at hsumcard
  -- abstract the main quantities
  obtain ⟨G, hGdef⟩ : ∃ G : ℚ, G = ∏ p ∈ n.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : ℚ, W = ∏ p ∈ n.primeFactors,
      (1 - 1 / (p : ℚ) ^ (n.factorization p + 1)) := ⟨_, rfl⟩
  obtain ⟨Rn, hRn⟩ : ∃ Rn : ℕ, Rn = ∏ q ∈ n.primeFactors, q := ⟨_, rfl⟩
  obtain ⟨Fn, hFn⟩ : ∃ Fn : ℕ, Fn = ∏ q ∈ n.primeFactors, (q - 1) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = n.primeFactors.card := ⟨_, rfl⟩
  rw [← hGdef, ← hWdef] at hH
  rw [← hGdef] at hGpos hGRF0 hA0
  rw [← hWdef] at hW1 hWlow0
  rw [← hRn, ← hFn] at hGRF0
  rw [← hFn] at hFpos0
  rw [← hk] at hk1' hA0 hsumcard
  rw [← hRn, ← hk] at hcon
  have hFq : (0 : ℚ) < (Fn : ℚ) := by exact_mod_cast hFpos0
  have hkq : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk1'
  have hh2 : 2 ≤ G * W := by
    rw [← hH, le_div_iff₀ hnq]; linarith
  have hG2 : 2 < G := by nlinarith [mul_pos hGpos (sub_pos.mpr hW1)]
  have hRF : 2 * Fn + 1 ≤ Rn := by
    have h1 : (2 : ℚ) * (Fn : ℚ) < (Rn : ℚ) := by
      have h := hG2
      rw [hGRF0, lt_div_iff₀ hFq] at h
      exact h
    have h2 : 2 * Fn < Rn := by exact_mod_cast h1
    omega
  have h3 : (2 : ℚ) * (Fn : ℚ) + 1 ≤ (Rn : ℚ) := by exact_mod_cast hRF
  have hRq : (1 : ℚ) ≤ (Rn : ℚ) := by linarith
  -- a prime factor p ≤ k + 1
  obtain ⟨p, hpS, hpk⟩ : ∃ p ∈ n.primeFactors, p ≤ k + 1 := by
    by_contra hno
    push_neg at hno
    have hA := hA0 (fun x hx => by have := hno x hx; omega)
    have hlt : (((k + 2 : ℕ) : ℚ) + (k : ℚ) - 1) / (((k + 2 : ℕ) : ℚ) - 1) < 2 := by
      rw [div_lt_iff₀ (by push_cast; linarith)]; push_cast; linarith
    linarith
  -- the Weierstrass bound
  have hsum : ∑ p ∈ n.primeFactors, 1 / (p : ℚ) ^ (n.factorization p + 1) ≤ 1 / (2 * (Rn : ℚ)) := by
    have hpos : (0 : ℚ) < 2 * (k : ℚ) * (Rn : ℚ) := mul_pos (mul_pos two_pos (by linarith)) (by linarith)
    have hb : ∀ p ∈ n.primeFactors,
        1 / (p : ℚ) ^ (n.factorization p + 1) ≤ 1 / (2 * (k : ℚ) * (Rn : ℚ)) := by
      intro p hp
      have h := hcon p hp
      have hq : (2 : ℚ) * (k : ℚ) * (Rn : ℚ) ≤ (p : ℚ) ^ (n.factorization p + 1) := by
        exact_mod_cast h
      exact one_div_le_one_div_of_le hpos hq
    have h5 := hsumcard _ hb
    rw [nsmul_eq_mul] at h5
    have hk0 : (k : ℚ) ≠ 0 := by intro h; linarith
    have hR0 : (Rn : ℚ) ≠ 0 := by intro h; linarith
    have e : (k : ℚ) * (1 / (2 * (k : ℚ) * (Rn : ℚ))) = 1 / (2 * (Rn : ℚ)) := by
      rw [mul_one_div, mul_comm (2 : ℚ) (k : ℚ), mul_assoc, ← div_div, div_self hk0]
    linarith
  have hWlow : 1 - 1 / (2 * (Rn : ℚ)) ≤ W := by linarith
  have hGW : 4 * (Fn : ℚ) + 1 ≤ 2 * (Fn : ℚ) * (G * W) := by
    have h1 : G * (1 - 1 / (2 * (Rn : ℚ))) ≤ G * W := mul_le_mul_of_nonneg_left hWlow hGpos.le
    have hR0 : (Rn : ℚ) ≠ 0 := by intro h; linarith
    have h2 : 2 * (Fn : ℚ) * (G * (1 - 1 / (2 * (Rn : ℚ)))) = 2 * (Rn : ℚ) - 1 := by
      rw [hGRF0]
      field_simp
    have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℚ) ≤ 2 * (Fn : ℚ))
    rw [h2] at h4
    linarith
  -- the chosen prime
  have hp := Nat.prime_of_mem_primeFactors hpS
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpS
  have hP2 : (2 : ℚ) ≤ p := hprime p hpS
  have hpkq : (p : ℚ) ≤ (k : ℚ) + 1 := by exact_mod_cast hpk
  have hqq : (2 : ℚ) * (k : ℚ) * (Rn : ℚ) ≤ (p : ℚ) ^ (n.factorization p + 1) := by
    exact_mod_cast hcon p hpS
  obtain ⟨Q, hQ⟩ : ∃ Q : ℚ, Q = (p : ℚ) ^ (n.factorization p + 1) := ⟨_, rfl⟩
  rw [← hQ] at hqq
  have hqp : 4 * (Fn : ℚ) * ((p : ℚ) - 1) ≤ Q - p := by
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (k : ℚ))
        (by linarith : (0 : ℚ) ≤ (Rn : ℚ) - (2 * (Fn : ℚ) + 1)),
      mul_nonneg hFq.le (by linarith : (0 : ℚ) ≤ (k : ℚ) + 1 - (p : ℚ))]
  have hQp : 0 ≤ Q - p := by
    have : 0 ≤ 4 * (Fn : ℚ) * ((p : ℚ) - 1) := by
      apply mul_nonneg <;> linarith
    linarith
  have hmain : 2 * (Q - 1) ≤ G * W * (Q - p) := by
    have h6 := mul_le_mul_of_nonneg_right hGW hQp
    have h5 : 2 * (Fn : ℚ) * (2 * (Q - 1)) ≤ 2 * (Fn : ℚ) * (G * W * (Q - p)) := by
      nlinarith
    exact le_of_mul_le_mul_left h5 (by linarith)
  have hsn : (((ArithmeticFunction.sigma 1) n : ℕ) : ℚ) = G * W * (n : ℚ) := by
    rw [← hH, div_mul_cancel₀ _ hnq.ne']
  have hineq : 2 * (n : ℚ) * ((p : ℚ) ^ (n.factorization p + 1) - 1) ≤
      (((ArithmeticFunction.sigma 1) n : ℕ) : ℚ) * ((p : ℚ) ^ (n.factorization p + 1) - p) := by
    rw [← hQ, hsn]
    nlinarith [mul_le_mul_of_nonneg_left hmain hnq.le]
  obtain ⟨m, hmn, hmne, hm⟩ := drop_prime n p hn hp hpn hineq
  have hdef := hprim m hmn hmne
  rw [deficient_iff] at hdef
  omega

end OMA.Proof_arxiv_2005_12115

theorem OMA.solution : type_of% @OMA.S_arxiv_2005_12115.main :=
  fun n h => OMA.Proof_arxiv_2005_12115.key n h
