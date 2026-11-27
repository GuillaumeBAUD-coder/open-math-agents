import FormalConjectures.ErdosProblems.«1100»

/-!
# Reduction of Erdős Problem 1100 — normal order

Reduction `Erdos1100.erdos_1100.variants.normal_order.R1` of
`Erdos1100.erdos_1100.variants.normal_order` into four literature-faithful hypotheses `H1`–`H4`,
none of which mentions `tauPerp`:

* Lower bound `(log n)^(log 3 - 1 + o(1)) <= tauPerp(n)` p.p. ([ErTe89, Section 4, Theorem 3]):
  `H1` (Maier–Tenenbaum 1984; Hall–Tenenbaum, Divisors, Ch. 4–5; [ErTe89, (4.1)]) gives the
  normal-order lower bound for close coprime divisor pairs `U^<(n, α)`, while `H2`
  ([ErTe89, (4.5)]) bounds the subset `W^<(n, α)` of non-consecutive such pairs. Removing
  `W^<(n, α)` from `U^<(n, α)` leaves consecutive coprime divisor pairs, giving
  `U^<(n, α) - W^<(n, α) <= tauPerp(n)`.
* Upper bound `tauPerp(n) <= (log n)^(log 2 - 1/2 + o(1))` p.p. ([ErTe83, Section 7, Theorem 5]):
  Every consecutive coprime divisor pair `d < d'` of `n` determines `m = d * d' | n` uniquely with
  `d = ρ₁(m) = max {e | m : e² ≤ m}`, `d' = m / d`, and every prime factor `p` of `r = n / m`
  satisfying `p ≥ d' / d` (equivalently `m ≤ p * ρ₁(m)²`). Summing over `n < N` with weight
  `(1/2)^Ω(n)` reduces to the double sum bounded by `H3` ([ErTe83, (28)–(30) at t = 1/2]).
  Combining `H3` with the Hardy–Ramanujan upper normal order `H4` for `Ω(n)` via Markov's
  inequality yields the upper bound on a set of density `1`.
-/

-- Credit: @ItsNotTheGabs
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos1100_erdos_1100_variants_normal_order_R1

open Erdos1100 Filter Finset Real
open scoped Classical Topology

-- H1 (Maier-Tenenbaum 1984; Hall-Tenenbaum, Divisors, Ch. 4-5; [ErTe89, (4.1)]):
-- Normal-order lower bound on the number U^<(n, alpha) of coprime divisor pairs d < d' of n
-- with log(d'/d) <= (log n)^(-alpha).
def H1 : Prop :=
  ∀ α : ℝ, 0 < α → α < (Real.log 3 - 1) / 2 → ∀ δ : ℝ, 0 < δ →
    {n : ℕ | Real.log n ^ (Real.log 3 - 1 - α - δ) ≤
      (((n.divisors ×ˢ n.divisors).filter fun p =>
        p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
          Real.log ((p.2 : ℝ) / (p.1 : ℝ)) ≤ Real.log n ^ (-α)).card : ℝ)}.HasDensity 1

-- H2 (Erdos-Tenenbaum 1989 [ErTe89, Section 4, (4.5)]):
-- Normal-order upper bound on the number W^<(n, alpha) of non-consecutive coprime divisor pairs
-- d < d' of n with log(d'/d) <= (log n)^(-alpha).
def H2 : Prop :=
  ∀ α : ℝ, 0 < α → α < (Real.log 3 - 1) / 2 → ∀ δ : ℝ, 0 < δ →
    {n : ℕ | (((n.divisors ×ˢ n.divisors).filter fun p =>
        p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
          Real.log ((p.2 : ℝ) / (p.1 : ℝ)) ≤ Real.log n ^ (-α) ∧
          ∃ t ∈ n.divisors, p.1 < t ∧ t < p.2).card : ℝ) ≤
      Real.log n ^ (Real.log 3 - 1 - 2 * α + δ)}.HasDensity 1

-- H3 (Erdos-Tenenbaum 1983 [ErTe83, Section 7, (28)-(30) at t = 1/2]):
-- Asymptotic upper bound on the (1/2)^Omega-weighted sum over pairs (m, r) with m * r < N and
-- every prime factor p of r satisfying p >= rho2(m) / rho1(m) (equivalently m <= p * rho1(m)^2),
-- where rho1(m) = max {d | m : d^2 <= m}.
def H3 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
    (∑ m ∈ Finset.Ico 2 N,
      ∑ r ∈ (Finset.Icc 1 ((N - 1) / m)).filter (fun r =>
        ∀ p ∈ r.primeFactors,
          m ≤ p * (Finset.sup (m.divisors.filter fun d => d * d ≤ m) id) ^ 2),
      ((1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors m + ArithmeticFunction.cardFactors r))) ≤
    (N : ℝ) * Real.log N ^ (-(1 / 2 : ℝ) + δ)

-- H4 (Hardy-Ramanujan 1917):
-- Upper normal order of the prime-factor multiplicity count Omega(n).
def H4 : Prop :=
  ∀ δ : ℝ, 0 < δ →
    {n : ℕ | (ArithmeticFunction.cardFactors n : ℝ) ≤
      (1 + δ) * Real.log (Real.log n)}.HasDensity 1

/- ### Density helper lemmas -/

lemma card_filter_add_compl {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] [DecidablePred (fun x => ¬ p x)] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint
    (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  tauto

lemma pd_eq (S : Set ℕ) (N : ℕ) [DecidablePred (· ∈ S)] :
    Set.partialDensity S Set.univ N =
      (((Finset.range N).filter fun n => n ∈ S).card : ℝ) / (N : ℝ) := by
  unfold Set.partialDensity
  have h1 : (S ∩ Set.univ ∩ Set.Iio N : Set ℕ) =
      (((Finset.range N).filter fun n => n ∈ S) : Set ℕ) := by
    ext n
    simp [Finset.mem_range, and_comm]
  have h2 : (Set.univ ∩ Set.Iio N : Set ℕ) = ((Finset.range N : Finset ℕ) : Set ℕ) := by
    ext n
    simp
  rw [h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_range]

lemma pd_nonneg (S : Set ℕ) (N : ℕ) : 0 ≤ Set.partialDensity S Set.univ N := by
  rw [pd_eq]
  positivity

lemma pd_add_compl (S : Set ℕ) {N : ℕ} (hN : 1 ≤ N) :
    Set.partialDensity S Set.univ N + Set.partialDensity Sᶜ Set.univ N = 1 := by
  rw [pd_eq, pd_eq, ← add_div, ← Nat.cast_add]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine (div_eq_one_iff_eq hN0).mpr ?_
  norm_cast
  rw [← Finset.card_union_of_disjoint
    (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  have hunion :
      ((Finset.range N).filter fun n => n ∈ S) ∪
      ((Finset.range N).filter fun n => n ∈ Sᶜ) = Finset.range N := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Set.mem_compl_iff]
    tauto
  rw [hunion, Finset.card_range]

lemma hasDensity_one_iff_compl_zero {S : Set ℕ} : S.HasDensity 1 ↔ Sᶜ.HasDensity 0 := by
  unfold Set.HasDensity
  constructor
  · intro hS
    have hsub : Tendsto (fun N : ℕ => 1 - Set.partialDensity S Set.univ N) atTop (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub hS
    rw [sub_self] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    linarith [pd_add_compl S hN]
  · intro hSc
    have hsub : Tendsto (fun N : ℕ => 1 - Set.partialDensity Sᶜ Set.univ N) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hSc
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    linarith [pd_add_compl S hN]

lemma hasDensity_zero_mono {S T : Set ℕ} (hsub : S ⊆ T) (hT : T.HasDensity 0) :
    S.HasDensity 0 := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
    (fun N => pd_nonneg S N) (fun N => ?_)
  rw [pd_eq, pd_eq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hsub hn.2⟩

lemma hasDensity_zero_union {S T : Set ℕ} (hS : S.HasDensity 0) (hT : T.HasDensity 0) :
    (S ∪ T).HasDensity 0 := by
  have hadd : Tendsto
      (fun N : ℕ => Set.partialDensity S Set.univ N + Set.partialDensity T Set.univ N)
      atTop (𝓝 (0 + 0)) := hS.add hT
  rw [add_zero] at hadd
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hadd
    (fun N => pd_nonneg (S ∪ T) N) (fun N => ?_)
  rw [pd_eq, pd_eq, pd_eq, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  rw [← Nat.cast_add]
  apply Nat.cast_le.mpr
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at hn ⊢
  rcases hn.2 with h | h
  · exact Or.inl ⟨hn.1, h⟩
  · exact Or.inr ⟨hn.1, h⟩

lemma hasDensity_one_inter {S T : Set ℕ} (hS : S.HasDensity 1) (hT : T.HasDensity 1) :
    (S ∩ T).HasDensity 1 := by
  rw [hasDensity_one_iff_compl_zero, Set.compl_inter]
  exact hasDensity_zero_union (hasDensity_one_iff_compl_zero.mp hS)
    (hasDensity_one_iff_compl_zero.mp hT)

lemma hasDensity_one_of_eventually_subset {S T : Set ℕ} (hS : S.HasDensity 1)
    (h : ∀ᶠ n : ℕ in atTop, n ∈ S → n ∈ T) : T.HasDensity 1 := by
  rw [Filter.eventually_atTop] at h
  obtain ⟨M, hM⟩ := h
  rw [hasDensity_one_iff_compl_zero] at hS ⊢
  have hsub : Tᶜ ⊆ Sᶜ ∪ Set.Iio M := by
    intro n hn
    by_cases hle : M ≤ n
    · left
      intro hnS
      exact hn (hM n hle hnS)
    · right
      exact Nat.lt_of_not_ge hle
  exact hasDensity_zero_mono hsub
    (hasDensity_zero_union hS (Nat.hasDensity_zero_of_finite (Set.finite_Iio M)))

/- ### Elementary real log and limit lemmas -/

lemma log_three_sub_one_pos : 0 < Real.log 3 - 1 := by
  have he : Real.exp 1 < 3 := by
    linarith [Real.exp_one_lt_d9]
  have hlog : 1 < Real.log 3 := by
    have := Real.log_lt_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at this
  linarith

lemma log_two_sub_half_pos : 0 < Real.log 2 - 1 / 2 := by
  have he : Real.exp (1 / 2 : ℝ) < 2 := by
    have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) < 4 := by
      rw [← Real.exp_add]
      norm_num
      linarith [Real.exp_one_lt_d9]
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_lt_log (Real.exp_pos (1 / 2 : ℝ)) he
    rwa [Real.log_exp] at this
  linarith

lemma tendsto_log_nat_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_log_rpow_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ a) atTop atTop :=
  (tendsto_rpow_atTop ha).comp tendsto_log_nat_atTop

lemma tendsto_log_rpow_neg_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ (-a)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp tendsto_log_nat_atTop

lemma tendsto_sqrt_add_one_div :
    Tendsto (fun N : ℕ => ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsum : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ)) + 1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun N => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq : (Nat.sqrt N : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    rw [sq]
    exact_mod_cast Nat.sqrt_le N
  have hdiv : (N : ℝ) ^ (1 / 2 : ℝ) / (N : ℝ) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hsub : (N : ℝ) ^ (1 / 2 : ℝ) / (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ ((1 / 2 : ℝ) - 1) :=
      (Real.rpow_sub hNpos _ _).symm
    rw [Real.rpow_one] at hsub
    rw [hsub]
    norm_num
  push_cast
  rw [add_div, ← hdiv]
  gcongr

/- ### Part 1: Combinatorial and density lower bound ([ErTe89, Section 4]) -/

lemma card_close_sub_nonconsec_le_tauPerp (n : ℕ) (hn : 0 < n) (α : ℝ) :
    (((n.divisors ×ˢ n.divisors).filter fun p =>
        p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
          Real.log ((p.2 : ℝ) / (p.1 : ℝ)) ≤ Real.log n ^ (-α)).card : ℝ) -
    (((n.divisors ×ˢ n.divisors).filter fun p =>
        p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
          Real.log ((p.2 : ℝ) / (p.1 : ℝ)) ≤ Real.log n ^ (-α) ∧
          ∃ t ∈ n.divisors, p.1 < t ∧ t < p.2).card : ℝ) ≤
    (tauPerp n : ℝ) := by
  let U := (n.divisors ×ˢ n.divisors).filter fun p =>
    p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
      Real.log ((p.2 : ℝ) / (p.1 : ℝ)) ≤ Real.log n ^ (-α)
  let W := U.filter fun p => ∃ t ∈ n.divisors, p.1 < t ∧ t < p.2
  let C := U.filter fun p => ¬ ∃ t ∈ n.divisors, p.1 < t ∧ t < p.2
  have hWeq : W = (n.divisors ×ˢ n.divisors).filter fun p =>
      p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
        Real.log ((p.2 : ℝ) / (p.1 : ℝ)) ≤ Real.log n ^ (-α) ∧
        ∃ t ∈ n.divisors, p.1 < t ∧ t < p.2 := by
    ext p
    simp only [W, U, Finset.mem_filter]
    tauto
  have hadd : W.card + C.card = U.card :=
    card_filter_add_compl U (fun p => ∃ t ∈ n.divisors, p.1 < t ∧ t < p.2)
  have hC_le : C.card ≤ tauPerp n := by
    by_cases hCempty : C = ∅
    · simp [hCempty]
    obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hCempty
    have hf : (Set.ofPred (· ∣ n)).Finite :=
      (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
    have hcard : hf.toFinset.card = n.divisors.card := by
      congr 1
      ext d
      simp [hn.ne']
    have hpos_card : 0 < n.divisors.card - 1 := by
      have hp0U : p0 ∈ U := (Finset.mem_filter.mp hp0).1
      have hp0' := Finset.mem_filter.mp hp0U
      have h1 : p0.1 ∣ n := (Nat.mem_divisors.mp (Finset.mem_product.mp hp0'.1).1).1
      have h2 : p0.2 ∣ n := (Nat.mem_divisors.mp (Finset.mem_product.mp hp0'.1).2).1
      have hlt : p0.1 < p0.2 := hp0'.2.1
      have hj1 : Nat.count (· ∣ n) p0.1 < Nat.count (· ∣ n) p0.2 :=
        Nat.count_strict_mono (p := (· ∣ n)) h1 hlt
      have hj2 : Nat.count (· ∣ n) p0.2 < hf.toFinset.card := Nat.count_lt_card hf h2
      omega
    have hconsec : ∀ p ∈ C,
        Nat.count (· ∣ n) p.1 < n.divisors.card - 1 ∧
        Nat.nth (· ∣ n) (Nat.count (· ∣ n) p.1) = p.1 ∧
        Nat.nth (· ∣ n) (Nat.count (· ∣ n) p.1 + 1) = p.2 := by
      intro p hpC
      have hpU : p ∈ U := (Finset.mem_filter.mp hpC).1
      have hno : ¬ ∃ t ∈ n.divisors, p.1 < t ∧ t < p.2 := (Finset.mem_filter.mp hpC).2
      have hp' := Finset.mem_filter.mp hpU
      have hd1 : p.1 ∣ n := (Nat.mem_divisors.mp (Finset.mem_product.mp hp'.1).1).1
      have hd2 : p.2 ∣ n := (Nat.mem_divisors.mp (Finset.mem_product.mp hp'.1).2).1
      have hlt : p.1 < p.2 := hp'.2.1
      set j := Nat.count (· ∣ n) p.1
      set j' := Nat.count (· ∣ n) p.2
      have hjj' : j < j' := Nat.count_strict_mono (p := (· ∣ n)) hd1 hlt
      have hj'_lt : j' < hf.toFinset.card := Nat.count_lt_card hf hd2
      have hj_lt : j < n.divisors.card - 1 := by omega
      have hnth_j : Nat.nth (· ∣ n) j = p.1 := Nat.nth_count (p := (· ∣ n)) hd1
      have hnth_j' : Nat.nth (· ∣ n) j' = p.2 := Nat.nth_count (p := (· ∣ n)) hd2
      have hnth_j1 : Nat.nth (· ∣ n) (j + 1) = p.2 := by
        set e := Nat.nth (· ∣ n) (j + 1)
        have hj1_lt : j + 1 < hf.toFinset.card := by omega
        have he_dvd : e ∣ n := Nat.nth_mem_of_lt_card hf hj1_lt
        have he_gt : p.1 < e := by
          have := Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self j) hj1_lt
          rwa [hnth_j] at this
        have he_le : e ≤ p.2 := by
          rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj') with heq | hlt'
          · rw [← hnth_j', ← heq]
          · have := Nat.nth_lt_nth_of_lt_card hf hlt' hj'_lt
            rw [hnth_j'] at this
            exact this.le
        by_contra hne
        have he_lt : e < p.2 := lt_of_le_of_ne he_le hne
        exact hno ⟨e, Nat.mem_divisors.mpr ⟨he_dvd, hn.ne'⟩, he_gt, he_lt⟩
      exact ⟨hj_lt, hnth_j, hnth_j1⟩
    unfold tauPerp
    refine Finset.card_le_card_of_injOn
      (fun p => if h : Nat.count (· ∣ n) p.1 < n.divisors.card - 1 then
        ⟨Nat.count (· ∣ n) p.1, h⟩ else ⟨0, hpos_card⟩) ?_ ?_
    · intro p hp
      obtain ⟨hj_lt, hnth_j, hnth_j1⟩ := hconsec p hp
      have hpU : p ∈ U := (Finset.mem_filter.mp hp).1
      have hcop : Nat.Coprime p.1 p.2 := (Finset.mem_filter.mp hpU).2.2.1
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [dif_pos hj_lt]
      show Nat.Coprime (Nat.nth (· ∣ n) (Nat.count (· ∣ n) p.1))
        (Nat.nth (· ∣ n) (Nat.count (· ∣ n) p.1 + 1))
      rw [hnth_j, hnth_j1]
      exact hcop
    · intro p hp q hq hpq
      obtain ⟨hjp_lt, hp1, hp2⟩ := hconsec p hp
      obtain ⟨hjq_lt, hq1, hq2⟩ := hconsec q hq
      dsimp only at hpq
      rw [dif_pos hjp_lt, dif_pos hjq_lt, Fin.mk.injEq] at hpq
      have h1 : p.1 = q.1 := by rw [← hp1, hpq, hq1]
      have h2 : p.2 = q.2 := by rw [← hp2, hpq, hq2]
      exact Prod.ext h1 h2
  rw [← hWeq]
  have haddR : (W.card : ℝ) + (C.card : ℝ) = (U.card : ℝ) := by exact_mod_cast hadd
  have hC_leR : (C.card : ℝ) ≤ (tauPerp n : ℝ) := by exact_mod_cast hC_le
  linarith

lemma lower_bound_hasDensity_one (h1 : H1) (h2 : H2) (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | Real.log n ^ (Real.log 3 - 1 - ε) ≤ (tauPerp n : ℝ)}.HasDensity 1 := by
  have hlog3 : 0 < Real.log 3 - 1 := log_three_sub_one_pos
  set α := min (ε / 3) ((Real.log 3 - 1) / 4)
  have hα_pos : 0 < α := lt_min (by linarith) (by linarith)
  have hα_lt : α < (Real.log 3 - 1) / 2 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h3α : 3 * α ≤ ε := by
    have := min_le_left (ε / 3) ((Real.log 3 - 1) / 4)
    linarith
  have hδ_pos : 0 < α / 4 := by linarith
  have hS1 := h1 α hα_pos hα_lt (α / 4) hδ_pos
  have hS2 := h2 α hα_pos hα_lt (α / 4) hδ_pos
  have hS12 := hasDensity_one_inter hS1 hS2
  apply hasDensity_one_of_eventually_subset hS12
  have hpow1 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log (n : ℝ) ^ (α / 2) :=
    (tendsto_log_rpow_atTop (by linarith : 0 < α / 2)).eventually (eventually_ge_atTop 2)
  have hlog_ge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 3, hpow1, hlog_ge] with n hn3 hpow hlog1 hnS
  obtain ⟨hn1, hn2⟩ := hnS
  have hn1' : Real.log n ^ (Real.log 3 - 1 - α - α / 4) ≤
      (((n.divisors ×ˢ n.divisors).filter fun p =>
        p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
          Real.log ((p.2 : ℝ) / (p.1 : ℝ)) ≤ Real.log n ^ (-α)).card : ℝ) := hn1
  have hn2' : (((n.divisors ×ˢ n.divisors).filter fun p =>
        p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
          Real.log ((p.2 : ℝ) / (p.1 : ℝ)) ≤ Real.log n ^ (-α) ∧
          ∃ t ∈ n.divisors, p.1 < t ∧ t < p.2).card : ℝ) ≤
      Real.log n ^ (Real.log 3 - 1 - 2 * α + α / 4) := hn2
  show Real.log n ^ (Real.log 3 - 1 - ε) ≤ (tauPerp n : ℝ)
  have hn_pos : 0 < n := by omega
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hcomb := card_close_sub_nonconsec_le_tauPerp n hn_pos α
  have hW_half :
      Real.log (n : ℝ) ^ (Real.log 3 - 1 - 2 * α + α / 4) ≤
      (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (Real.log 3 - 1 - α - α / 4) := by
    have hexp :
        Real.log (n : ℝ) ^ (Real.log 3 - 1 - α - α / 4) =
        Real.log (n : ℝ) ^ (Real.log 3 - 1 - 2 * α + α / 4) *
          Real.log (n : ℝ) ^ (α / 2) := by
      rw [← Real.rpow_add hlog_pos]
      congr 1
      ring
    have hnonneg : 0 ≤ Real.log (n : ℝ) ^ (Real.log 3 - 1 - 2 * α + α / 4) :=
      Real.rpow_nonneg hlog_pos.le _
    rw [hexp]
    nlinarith
  have hhalf_ge :
      Real.log (n : ℝ) ^ (Real.log 3 - 1 - 3 * α) ≤
      (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (Real.log 3 - 1 - α - α / 4) := by
    have hexp :
        Real.log (n : ℝ) ^ (Real.log 3 - 1 - α - α / 4) =
        Real.log (n : ℝ) ^ (Real.log 3 - 1 - 3 * α) *
          Real.log (n : ℝ) ^ (7 * α / 4) := by
      rw [← Real.rpow_add hlog_pos]
      congr 1
      ring
    have h2le : (2 : ℝ) ≤ Real.log (n : ℝ) ^ (7 * α / 4) :=
      le_trans hpow (Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith))
    have hnonneg : 0 ≤ Real.log (n : ℝ) ^ (Real.log 3 - 1 - 3 * α) :=
      Real.rpow_nonneg hlog_pos.le _
    rw [hexp]
    nlinarith
  have hmono :
      Real.log (n : ℝ) ^ (Real.log 3 - 1 - ε) ≤
      Real.log (n : ℝ) ^ (Real.log 3 - 1 - 3 * α) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
  linarith

/- ### Part 2: Combinatorial and Markov upper bound ([ErTe83, Section 7]) -/

lemma tauPerp_le_card_good_divisors (n : ℕ) (hn : 0 < n) :
    tauPerp n ≤ (n.divisors.filter fun m =>
      2 ≤ m ∧ ∀ p ∈ (n / m).primeFactors,
        m ≤ p * (Finset.sup (m.divisors.filter fun d => d * d ≤ m) id) ^ 2).card := by
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn.ne']
  have hsup_eq : ∀ i : Fin (n.divisors.card - 1),
      let d := Nat.nth (· ∣ n) (i : ℕ)
      let d' := Nat.nth (· ∣ n) ((i : ℕ) + 1)
      Nat.Coprime d d' →
      Finset.sup ((d * d').divisors.filter fun e => e * e ≤ d * d') id = d := by
    intro i d d' hcop
    have hi1 : (i : ℕ) + 1 < hf.toFinset.card := by
      have := i.isLt
      omega
    have hd : d ∣ n := Nat.nth_mem_of_lt_card hf (by omega)
    have hd' : d' ∣ n := Nat.nth_mem_of_lt_card hf hi1
    have hlt : d < d' := Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self _) hi1
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    have hm_ne : d * d' ≠ 0 := Nat.mul_ne_zero hd_pos.ne' (by omega)
    apply le_antisymm
    · apply Finset.sup_le
      intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors] at he
      obtain ⟨⟨he_dvd, _⟩, he_sq⟩ := he
      have hm_dvd : d * d' ∣ n := hcop.mul_dvd_of_dvd_of_dvd hd hd'
      have he_n : e ∣ n := dvd_trans he_dvd hm_dvd
      by_contra hnotle
      have hde : d < e := Nat.lt_of_not_ge hnotle
      have hed' : e < d' := by
        by_contra hge
        have hd'e : d' ≤ e := Nat.le_of_not_lt hge
        have h1 : d * d' < d' * d' := Nat.mul_lt_mul_of_pos_right hlt (by omega)
        have h2 : d' * d' ≤ e * e := Nat.mul_le_mul hd'e hd'e
        omega
      have hle_d : e ≤ d := Nat.le_nth_of_lt_nth_succ (p := (· ∣ n)) hed' he_n
      omega
    · refine Finset.le_sup (f := id) ?_
      simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨dvd_mul_right d d', hm_ne⟩, Nat.mul_le_mul_left d hlt.le⟩
  unfold tauPerp
  refine Finset.card_le_card_of_injOn
    (fun i : Fin (n.divisors.card - 1) =>
      Nat.nth (· ∣ n) (i : ℕ) * Nat.nth (· ∣ n) ((i : ℕ) + 1)) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    set d := Nat.nth (· ∣ n) (i : ℕ)
    set d' := Nat.nth (· ∣ n) ((i : ℕ) + 1)
    have hi1 : (i : ℕ) + 1 < hf.toFinset.card := by
      have := i.isLt
      omega
    have hd : d ∣ n := Nat.nth_mem_of_lt_card hf (by omega)
    have hd' : d' ∣ n := Nat.nth_mem_of_lt_card hf hi1
    have hlt : d < d' := Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self _) hi1
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    have hm_dvd : d * d' ∣ n := hi.mul_dvd_of_dvd_of_dvd hd hd'
    have hsup : Finset.sup ((d * d').divisors.filter fun e => e * e ≤ d * d') id = d :=
      hsup_eq i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨hm_dvd, hn.ne'⟩, ?_, ?_⟩
    · change 2 ≤ d * d'
      have : 2 ≤ d' := by omega
      nlinarith
    · intro p hp
      change d * d' ≤ p * (Finset.sup ((d * d').divisors.filter fun e => e * e ≤ d * d') id) ^ 2
      rw [hsup]
      obtain ⟨hp_prime, hp_dvd, -⟩ := Nat.mem_primeFactors.mp hp
      have hpd_dvd : p * d ∣ n := by
        have h1 : p * d ∣ (n / (d * d')) * d := Nat.mul_dvd_mul_right hp_dvd d
        have h2 : (n / (d * d')) * d ∣ (n / (d * d')) * (d * d') :=
          Nat.mul_dvd_mul_left _ (dvd_mul_right d d')
        rw [Nat.div_mul_cancel hm_dvd] at h2
        exact dvd_trans h1 h2
      have hpd_gt : d < p * d := by
        have := hp_prime.one_lt
        nlinarith
      have hd'_le : d' ≤ p * d := by
        by_contra hlt_pd
        have hle := Nat.le_nth_of_lt_nth_succ (p := (· ∣ n)) (Nat.lt_of_not_ge hlt_pd) hpd_dvd
        omega
      calc
        d * d' ≤ d * (p * d) := Nat.mul_le_mul_left d hd'_le
        _ = p * d ^ 2 := by ring
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    dsimp only at hij
    have hsi := hsup_eq i hi
    have hsj := hsup_eq j hj
    have hdeq : Nat.nth (· ∣ n) (i : ℕ) = Nat.nth (· ∣ n) (j : ℕ) := by
      rw [← hsi, hij, hsj]
    have hi_lt : (i : ℕ) ∈ Set.Iio hf.toFinset.card := by
      have := i.isLt
      simp only [Set.mem_Iio]
      omega
    have hj_lt : (j : ℕ) ∈ Set.Iio hf.toFinset.card := by
      have := j.isLt
      simp only [Set.mem_Iio]
      omega
    exact Fin.ext (Nat.nth_injOn hf hi_lt hj_lt hdeq)

lemma sum_tauPerp_weighted_le (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N,
      (tauPerp n : ℝ) * (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n)) ≤
    ∑ m ∈ Finset.Ico 2 N,
      ∑ r ∈ (Finset.Icc 1 ((N - 1) / m)).filter (fun r =>
        ∀ p ∈ r.primeFactors,
          m ≤ p * (Finset.sup (m.divisors.filter fun d => d * d ≤ m) id) ^ 2),
      ((1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors m + ArithmeticFunction.cardFactors r)) := by
  have hstep1 :
      (∑ n ∈ Finset.Ico 1 N,
        (tauPerp n : ℝ) * (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n)) ≤
      ∑ n ∈ Finset.Ico 1 N,
        ∑ m ∈ Finset.Ico 2 N,
          if m ∣ n ∧ ∀ p ∈ (n / m).primeFactors,
              m ≤ p * (Finset.sup (m.divisors.filter fun d => d * d ≤ m) id) ^ 2
          then (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n)
          else 0 := by
    apply Finset.sum_le_sum
    intro n hn
    have hn_pos : 0 < n := (Finset.mem_Ico.mp hn).1
    have hn_lt : n < N := (Finset.mem_Ico.mp hn).2
    have hle := tauPerp_le_card_good_divisors n hn_pos
    have hmul :
        (tauPerp n : ℝ) * (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n) ≤
        ((n.divisors.filter fun m =>
          2 ≤ m ∧ ∀ p ∈ (n / m).primeFactors,
            m ≤ p * (Finset.sup (m.divisors.filter fun d => d * d ≤ m) id) ^ 2).card : ℝ) *
          (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (by positivity)
    refine le_trans hmul (le_of_eq ?_)
    have hfeq :
        (n.divisors.filter fun m =>
          2 ≤ m ∧ ∀ p ∈ (n / m).primeFactors,
            m ≤ p * (Finset.sup (m.divisors.filter fun d => d * d ≤ m) id) ^ 2) =
        (Finset.Ico 2 N).filter fun m =>
          m ∣ n ∧ ∀ p ∈ (n / m).primeFactors,
            m ≤ p * (Finset.sup (m.divisors.filter fun d => d * d ≤ m) id) ^ 2 := by
      ext m
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨hmd, _⟩, hm2, hpr⟩
        exact ⟨⟨hm2, lt_of_le_of_lt (Nat.le_of_dvd hn_pos hmd) hn_lt⟩, hmd, hpr⟩
      · rintro ⟨⟨hm2, _⟩, hmd, hpr⟩
        exact ⟨⟨hmd, hn_pos.ne'⟩, hm2, hpr⟩
    rw [hfeq, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
  refine le_trans hstep1 ?_
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro m hm
  have hm2 : 2 ≤ m := (Finset.mem_Ico.mp hm).1
  have hm_lt : m < N := (Finset.mem_Ico.mp hm).2
  have hm_pos : 0 < m := by omega
  rw [← Finset.sum_filter]
  refine le_of_eq ?_
  refine Finset.sum_nbij' (fun n => n / m) (fun r => m * r) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnN⟩, hmd, hpr⟩ := hn
    have hr1 : 1 ≤ n / m := Nat.div_pos (Nat.le_of_dvd (by omega) hmd) hm_pos
    have hmr : m * (n / m) = n := Nat.mul_div_cancel' hmd
    have hr_le : n / m ≤ (N - 1) / m := by
      rw [Nat.le_div_iff_mul_le hm_pos, mul_comm, hmr]
      omega
    exact ⟨⟨hr1, hr_le⟩, hpr⟩
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc] at hr ⊢
    obtain ⟨⟨hr1, hr_le⟩, hpr⟩ := hr
    have hmul_le : m * r ≤ N - 1 := by
      have := (Nat.le_div_iff_mul_le hm_pos).mp hr_le
      linarith
    have hN1 : 1 ≤ N := by omega
    refine ⟨⟨by nlinarith, by omega⟩, dvd_mul_right m r, ?_⟩
    rwa [Nat.mul_div_cancel_left r hm_pos]
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2.1
  · intro r _
    exact Nat.mul_div_cancel_left r hm_pos
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    obtain ⟨⟨hn1, _⟩, hmd, _⟩ := hn
    have hr_ne : n / m ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (by omega) hmd) hm_pos
      omega
    have hmr : m * (n / m) = n := Nat.mul_div_cancel' hmd
    conv_lhs => rw [← hmr]
    rw [ArithmeticFunction.cardFactors_mul hm_pos.ne' hr_ne]

lemma upper_bound_hasDensity_one (h3 : H3) (h4 : H4) (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | (tauPerp n : ℝ) ≤ Real.log n ^ (Real.log 2 - 1 / 2 + ε)}.HasDensity 1 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp_pos : 0 < Real.log 2 - 1 / 2 + ε := by
    linarith [log_two_sub_half_pos]
  set δ4 := ε / (4 * Real.log 2)
  have hδ4_pos : 0 < δ4 := by positivity
  set δ3 := ε / 4
  have hδ3_pos : 0 < δ3 := by positivity
  set A : Set ℕ :=
    {n : ℕ | (ArithmeticFunction.cardFactors n : ℝ) ≤ (1 + δ4) * Real.log (Real.log n)}
  have hA : A.HasDensity 1 := h4 δ4 hδ4_pos
  have hAc : Aᶜ.HasDensity 0 := hasDensity_one_iff_compl_zero.mp hA
  set B : Set ℕ :=
    {n : ℕ | Real.log n ^ (Real.log 2 - 1 / 2 + ε) < (tauPerp n : ℝ)}
  have hBc_eq : Bᶜ = {n : ℕ | (tauPerp n : ℝ) ≤ Real.log n ^ (Real.log 2 - 1 / 2 + ε)} := by
    ext n
    simp [B, Set.mem_compl_iff]
  rw [← hBc_eq, hasDensity_one_iff_compl_zero, compl_compl]
  set c : ℝ := (1 / 2 : ℝ) ^ (Real.log 2 - 1 / 2 + ε)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hH3 : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Ico 1 N,
        (tauPerp n : ℝ) * (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n)) ≤
      (N : ℝ) * Real.log N ^ (-(1 / 2 : ℝ) + δ3) := by
    filter_upwards [h3 δ3 hδ3_pos] with N hN
    exact le_trans (sum_tauPerp_weighted_le N) hN
  have hbound_tendsto :
      Tendsto
        (fun N : ℕ =>
          ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ) +
          Set.partialDensity Aᶜ Set.univ N +
          c⁻¹ * Real.log (N : ℝ) ^ (-(ε / 2)))
        atTop (𝓝 0) := by
    have ht3 : Tendsto (fun N : ℕ => c⁻¹ * Real.log (N : ℝ) ^ (-(ε / 2))) atTop (𝓝 0) := by
      simpa using (tendsto_log_rpow_neg_zero (by linarith : 0 < ε / 2)).const_mul c⁻¹
    simpa using (tendsto_sqrt_add_one_div.add hAc).add ht3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound_tendsto
    (Eventually.of_forall fun N => pd_nonneg B N) ?_
  filter_upwards [eventually_ge_atTop 16, hH3] with N hN16 hsumN
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlogN_ge2 : (2 : ℝ) ≤ Real.log (N : ℝ) := by
    have he2 : Real.exp 2 ≤ (N : ℝ) := by
      have he1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have hN16R : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN16
      nlinarith [Real.exp_pos 1]
    have := Real.log_le_log (Real.exp_pos 2) he2
    rwa [Real.log_exp] at this
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  let E := (Finset.Ico (Nat.sqrt N + 1) N).filter fun n => n ∈ B ∧ n ∈ A
  have hcard_split :
      ((Finset.range N).filter fun n => n ∈ B).card ≤
      (Nat.sqrt N + 1) + ((Finset.range N).filter fun n => n ∈ Aᶜ).card + E.card := by
    have hsub :
        ((Finset.range N).filter fun n => n ∈ B) ⊆
        Finset.range (Nat.sqrt N + 1) ∪
          ((Finset.range N).filter fun n => n ∈ Aᶜ) ∪ E := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico, E,
        Set.mem_compl_iff]
      by_cases hlt : n < Nat.sqrt N + 1
      · left; left; exact hlt
      · by_cases hnA : n ∈ A
        · right; exact ⟨⟨Nat.le_of_not_lt hlt, hn.1⟩, hn.2, hnA⟩
        · left; right; exact ⟨hn.1, hnA⟩
    calc
      ((Finset.range N).filter fun n => n ∈ B).card
          ≤ (Finset.range (Nat.sqrt N + 1) ∪
              ((Finset.range N).filter fun n => n ∈ Aᶜ) ∪ E).card := Finset.card_le_card hsub
      _ ≤ (Finset.range (Nat.sqrt N + 1) ∪
              ((Finset.range N).filter fun n => n ∈ Aᶜ)).card + E.card := Finset.card_union_le _ _
      _ ≤ (Finset.range (Nat.sqrt N + 1)).card +
            ((Finset.range N).filter fun n => n ∈ Aᶜ).card + E.card := by
          gcongr; exact Finset.card_union_le _ _
      _ = (Nat.sqrt N + 1) + ((Finset.range N).filter fun n => n ∈ Aᶜ).card + E.card := by
          rw [Finset.card_range]
  have hE_elem : ∀ n ∈ E,
      c * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + 3 * ε / 4) ≤
      (tauPerp n : ℝ) * (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico, E] at hn
    obtain ⟨⟨hn_ge, hn_lt⟩, hnB, hnA⟩ := hn
    have hnsq_ge : (N : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
      have h1 : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
      have h2 : (Nat.sqrt N + 1) * (Nat.sqrt N + 1) ≤ n * n := Nat.mul_le_mul hn_ge hn_ge
      exact_mod_cast (lt_of_lt_of_le h1 h2).le
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      have : 1 ≤ n := by omega
      exact_mod_cast this
    have hlogn_ge : (1 / 2 : ℝ) * Real.log (N : ℝ) ≤ Real.log (n : ℝ) := by
      have h1 : Real.log (N : ℝ) ≤ Real.log ((n : ℝ) * (n : ℝ)) :=
        Real.log_le_log hN_pos hnsq_ge
      rw [Real.log_mul hn_pos.ne' hn_pos.ne'] at h1
      linarith
    have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
    have hlogn_le : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log hn_pos (by exact_mod_cast hn_lt.le)
    have htau_lb :
        c * Real.log (N : ℝ) ^ (Real.log 2 - 1 / 2 + ε) ≤ (tauPerp n : ℝ) := by
      have h1 : ((1 / 2 : ℝ) * Real.log (N : ℝ)) ^ (Real.log 2 - 1 / 2 + ε) ≤
          Real.log (n : ℝ) ^ (Real.log 2 - 1 / 2 + ε) :=
        Real.rpow_le_rpow (by positivity) hlogn_ge hexp_pos.le
      rw [Real.mul_rpow (by norm_num) hlogN_pos.le] at h1
      exact le_trans h1 (le_of_lt hnB)
    have hpow_lb :
        Real.log (N : ℝ) ^ (-(Real.log 2 + ε / 4)) ≤
        (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n) := by
      have hloglog : Real.log (Real.log (n : ℝ)) ≤ Real.log (Real.log (N : ℝ)) :=
        Real.log_le_log hlogn_pos hlogn_le
      have hOm : (ArithmeticFunction.cardFactors n : ℝ) ≤
          (1 + δ4) * Real.log (Real.log (N : ℝ)) :=
        le_trans hnA (mul_le_mul_of_nonneg_left hloglog (by linarith))
      have h12 : (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n) =
          Real.exp (-((ArithmeticFunction.cardFactors n : ℝ) * Real.log 2)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        congr 1
        rw [one_div, Real.log_inv]
        ring
      have hrhs : Real.log (N : ℝ) ^ (-(Real.log 2 + ε / 4)) =
          Real.exp (-((1 + δ4) * Real.log (Real.log (N : ℝ)) * Real.log 2)) := by
        rw [Real.rpow_def_of_pos hlogN_pos]
        congr 1
        have hδ4mul : δ4 * Real.log 2 = ε / 4 := by
          dsimp only [δ4]
          field_simp [hlog2_pos.ne']
        rw [← hδ4mul]
        ring
      rw [h12, hrhs]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hOm hlog2_pos.le
      linarith
    have hprod := mul_le_mul htau_lb hpow_lb (Real.rpow_nonneg hlogN_pos.le _)
      (Nat.cast_nonneg (tauPerp n))
    refine le_trans ?_ hprod
    rw [mul_assoc, ← Real.rpow_add hlogN_pos]
    apply le_of_eq
    congr 2
    ring
  have hE_sum :
      (E.card : ℝ) * (c * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + 3 * ε / 4)) ≤
      (N : ℝ) * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + δ3) := by
    have hE_sub : E ⊆ Finset.Ico 1 N := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico, E] at hn
      exact Finset.mem_Ico.mpr ⟨by omega, hn.1.2⟩
    calc
      (E.card : ℝ) * (c * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + 3 * ε / 4))
          = ∑ _n ∈ E, c * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + 3 * ε / 4) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ E, (tauPerp n : ℝ) * (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n) :=
            Finset.sum_le_sum hE_elem
      _ ≤ ∑ n ∈ Finset.Ico 1 N,
            (tauPerp n : ℝ) * (1 / 2 : ℝ) ^ (ArithmeticFunction.cardFactors n) :=
            Finset.sum_le_sum_of_subset_of_nonneg hE_sub (fun _ _ _ => by positivity)
      _ ≤ (N : ℝ) * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + δ3) := hsumN
  have hE_div : (E.card : ℝ) / (N : ℝ) ≤ c⁻¹ * Real.log (N : ℝ) ^ (-(ε / 2)) := by
    have hden_pos : 0 < c * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + 3 * ε / 4) :=
      mul_pos hc_pos (Real.rpow_pos_of_pos hlogN_pos _)
    have h1 : (E.card : ℝ) ≤
        ((N : ℝ) * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + δ3)) /
          (c * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + 3 * ε / 4)) :=
      (le_div_iff₀ hden_pos).mpr hE_sum
    have h2 : (E.card : ℝ) / (N : ℝ) ≤
        Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + δ3) /
          (c * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + 3 * ε / 4)) := by
      calc
        (E.card : ℝ) / (N : ℝ)
            ≤ (((N : ℝ) * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + δ3)) /
                (c * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + 3 * ε / 4))) / (N : ℝ) :=
              div_le_div_of_nonneg_right h1 hN_pos.le
        _ = Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + δ3) /
              (c * Real.log (N : ℝ) ^ (-(1 / 2 : ℝ) + 3 * ε / 4)) := by
              field_simp [hN_pos.ne']
    refine le_trans h2 (le_of_eq ?_)
    rw [div_mul_eq_div_div_swap, div_eq_mul_inv (Real.log (N : ℝ) ^ _ / _),
      ← Real.rpow_sub hlogN_pos]
    rw [mul_comm]
    congr 2
    dsimp only [δ3]
    ring
  rw [pd_eq, pd_eq]
  have hcardR :
      (((Finset.range N).filter fun n => n ∈ B).card : ℝ) ≤
      ((Nat.sqrt N + 1 : ℕ) : ℝ) +
        (((Finset.range N).filter fun n => n ∈ Aᶜ).card : ℝ) + (E.card : ℝ) := by
    exact_mod_cast hcard_split
  calc
    (((Finset.range N).filter fun n => n ∈ B).card : ℝ) / (N : ℝ)
        ≤ (((Nat.sqrt N + 1 : ℕ) : ℝ) +
            (((Finset.range N).filter fun n => n ∈ Aᶜ).card : ℝ) + (E.card : ℝ)) / (N : ℝ) :=
          div_le_div_of_nonneg_right hcardR hN_pos.le
    _ = ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ) +
          (((Finset.range N).filter fun n => n ∈ Aᶜ).card : ℝ) / (N : ℝ) +
          (E.card : ℝ) / (N : ℝ) := by ring
    _ ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ) +
          (((Finset.range N).filter fun n => n ∈ Aᶜ).card : ℝ) / (N : ℝ) +
          c⁻¹ * Real.log (N : ℝ) ^ (-(ε / 2)) := by linarith

/- ### Main reduction theorem -/

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos1100.erdos_1100.variants.normal_order := by
  intro h1 h2 h3 h4 ε hε
  exact hasDensity_one_inter (lower_bound_hasDensity_one h1 h2 ε hε)
    (upper_bound_hasDensity_one h3 h4 ε hε)

end OMA.R_Erdos1100_erdos_1100_variants_normal_order_R1
