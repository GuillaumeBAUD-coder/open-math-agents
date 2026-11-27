import FormalConjectures.ErdosProblems.«121»
import Mathlib.NumberTheory.SumPrimeReciprocals

-- Problem: Erdős Problem 121 — three
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/121.lean:92 (declaration Erdos121.erdos_121.variants.three)
-- Credit: @skhakim (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos121Three

open Filter Topology Finset

private noncomputable def H (X : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (1 : ℝ) / (p : ℝ)

private lemma H_mono {X Y : ℕ} (h : X ≤ Y) : H X ≤ H Y := by
  unfold H
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans h⟩, hp.2⟩

private lemma H_nonneg (X : ℕ) : 0 ≤ H X :=
  Finset.sum_nonneg fun _ _ => by positivity

private lemma tendsto_H_atTop : Tendsto H atTop atTop := by
  have hnot := not_summable_one_div_on_primes
  have hnn : ∀ n : ℕ, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n := by
    intro n
    by_cases hn : n.Prime <;> simp [Set.indicator, hn]
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp hnot
  have hEq : ∀ X : ℕ, H X = ∑ n ∈ Finset.range (X + 1),
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n := by
    intro X
    unfold H
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hpX⟩, hp⟩; exact ⟨Nat.lt_succ_of_le hpX, hp⟩
    · rintro ⟨hpX, hp⟩; exact ⟨⟨hp.pos, Nat.le_of_lt_succ hpX⟩, hp⟩
  have hfun : H = fun X => ∑ n ∈ Finset.range (X + 1),
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n := funext hEq
  rw [hfun]
  exact ht.comp (tendsto_add_atTop_nat 1)

private lemma sum_primes_dyadic_le (j : ℕ) (hj : 1 ≤ j) :
    ∑ p ∈ (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      (2 : ℝ) / (j : ℝ) := by
  set P := (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime
  set m := 2 ^ j
  have hm_pos : 0 < m := by positivity
  have h2m : 2 ^ (j + 1) = 2 * m := by ring
  have hdvd_each : ∀ p ∈ P, p ∣ (2 * m).choose m := by
    intro p hp
    simp only [P, Finset.mem_filter, Finset.mem_Ioc] at hp
    rcases hp with ⟨⟨hpm, hp2m⟩, hprime⟩
    have hmul : (2 * m).choose m * m.factorial * m.factorial = (2 * m).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
      simpa [show 2 * m - m = m by omega] using this
    have hdvd_top : p ∣ (2 * m).factorial := hprime.dvd_factorial.mpr (by omega)
    have hndvd_bot : ¬ p ∣ m.factorial := by
      rw [hprime.dvd_factorial]; omega
    rw [← hmul] at hdvd_top
    rcases hprime.dvd_mul.mp hdvd_top with h1 | h2
    · rcases hprime.dvd_mul.mp h1 with h11 | h12
      · exact h11
      · exact absurd h12 hndvd_bot
    · exact absurd h2 hndvd_bot
  have hprod_dvd : ∏ p ∈ P, p ∣ (2 * m).choose m := by
    have hgen : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ p ∣ (2 * m).choose m) →
        ∏ p ∈ s, p ∣ (2 * m).choose m := by
      intro s
      induction s using Finset.induction with
      | empty => intro _; simp
      | insert a s ha ih =>
        intro h
        rw [Finset.prod_insert ha]
        have ha' := h a (Finset.mem_insert_self _ _)
        have hs' : ∏ p ∈ s, p ∣ (2 * m).choose m := ih fun p hp => h p (Finset.mem_insert_of_mem hp)
        have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
          Nat.Coprime.prod_right fun p hp =>
            (Nat.coprime_primes ha'.1 (h p (Finset.mem_insert_of_mem hp)).1).mpr
              (fun heq => ha (heq ▸ hp))
        exact hcop.mul_dvd_of_dvd_of_dvd ha'.2 hs'
    exact hgen P fun p hp => ⟨(Finset.mem_filter.mp hp).2, hdvd_each p hp⟩
  have hchoose_pos : 0 < (2 * m).choose m := Nat.choose_pos (by omega)
  have hprod_le_choose : ∏ p ∈ P, p ≤ (2 * m).choose m := Nat.le_of_dvd hchoose_pos hprod_dvd
  have hchoose_le : (2 * m).choose m ≤ 2 ^ (2 * m) := by
    have hsum := Nat.sum_range_choose (2 * m)
    have hmem : m ∈ Finset.range (2 * m + 1) := Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem).trans hsum.le
  have hpow_le_prod : m ^ P.card ≤ ∏ p ∈ P, p := by
    calc m ^ P.card = ∏ _p ∈ P, m := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ P, p := by
          refine Finset.prod_le_prod' fun p hp => ?_
          simp only [P, Finset.mem_filter, Finset.mem_Ioc] at hp
          exact le_of_lt hp.1.1
  have h2pow : 2 ^ (j * P.card) ≤ 2 ^ (2 * m) := by
    calc 2 ^ (j * P.card) = (2 ^ j) ^ P.card := by rw [pow_mul]
      _ ≤ ∏ p ∈ P, p := hpow_le_prod
      _ ≤ (2 * m).choose m := hprod_le_choose
      _ ≤ 2 ^ (2 * m) := hchoose_le
  have hcard_bound : j * P.card ≤ 2 * m := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2pow
  have hsum_le : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ (P.card : ℝ) / (m : ℝ) := by
    calc ∑ p ∈ P, (1 : ℝ) / (p : ℝ)
        ≤ ∑ _p ∈ P, (1 : ℝ) / (m : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          simp only [P, Finset.mem_filter, Finset.mem_Ioc] at hp
          exact one_div_le_one_div_of_le (by exact_mod_cast hm_pos) (by exact_mod_cast le_of_lt hp.1.1)
      _ = (P.card : ℝ) / (m : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  refine hsum_le.trans ?_
  rw [div_le_div_iff₀ (by exact_mod_cast hm_pos) (by exact_mod_cast (by omega : 0 < j))]
  exact_mod_cast (show P.card * j ≤ 2 * m by linarith)

private lemma H_sub_H_sqrt_le (N : ℕ) (hN : 4 ≤ N) :
    H N - H (Nat.sqrt N) ≤ 6 := by
  have hsqrt_ge : 2 ≤ Nat.sqrt N := by
    rw [Nat.le_sqrt]; omega
  set L := Nat.log 2 (Nat.sqrt N)
  have hL_ge : 1 ≤ L := by
    rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
    simpa using hsqrt_ge
  have h2L_le : 2 ^ L ≤ Nat.sqrt N := Nat.pow_log_le_self 2 (by omega)
  have hsqrt_lt : Nat.sqrt N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) (Nat.sqrt N)
  have hN_le : N ≤ 2 ^ (2 * L + 2) := by
    have h1 : N < (Nat.sqrt N + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt N
      nlinarith
    have h2 : Nat.sqrt N + 1 ≤ 2 ^ (L + 1) := hsqrt_lt
    have h3 : (Nat.sqrt N + 1) ^ 2 ≤ (2 ^ (L + 1)) ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : (2 ^ (L + 1)) ^ 2 = 2 ^ (2 * L + 2) := by
      rw [← pow_mul]; congr 1; omega
    omega
  have hdiff : H N - H (Nat.sqrt N) =
      ∑ p ∈ (Finset.Ioc (Nat.sqrt N) N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    unfold H
    rw [sub_eq_iff_eq_add]
    rw [← Finset.sum_union]
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩
        by_cases h : p ≤ Nat.sqrt N
        · exact Or.inr ⟨⟨h1, h⟩, hp⟩
        · exact Or.inl ⟨⟨by omega, h2⟩, hp⟩
      · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
        · exact ⟨⟨by omega, h2⟩, hp⟩
        · exact ⟨⟨h1, h2.trans (Nat.sqrt_le_self N)⟩, hp⟩
    · rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp1 hp2
      omega
  rw [hdiff]
  have hsub : (Finset.Ioc (Nat.sqrt N) N).filter Nat.Prime ⊆
      (Finset.Ico L (2 * L + 2)).biUnion
        (fun j => (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_filter, Finset.mem_Ioc]
    have hp_gt : 2 ^ L < p := lt_of_le_of_lt h2L_le hp.1.1
    have hp_le : p ≤ 2 ^ (2 * L + 2) := hp.1.2.trans hN_le
    set j := Nat.log 2 (p - 1)
    have hp1_ne : p - 1 ≠ 0 := by
      have : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      omega
    have hj_lo : 2 ^ j ≤ p - 1 := Nat.pow_log_le_self 2 hp1_ne
    have hj_hi : p - 1 < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) (p - 1)
    have hj_ge_L : L ≤ j := by
      have h1 : 2 ^ L ≤ p - 1 := by omega
      have := Nat.log_mono_right (b := 2) h1
      simpa [j, Nat.log_pow (by norm_num : 1 < 2)] using this
    have hj_lt : j < 2 * L + 2 := by
      by_contra hge
      push Not at hge
      have h1 : 2 ^ (2 * L + 2) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hge
      omega
    exact ⟨j, ⟨hj_ge_L, hj_lt⟩, ⟨by omega, by omega⟩, hp.2⟩
  calc ∑ p ∈ (Finset.Ioc (Nat.sqrt N) N).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ (Finset.Ico L (2 * L + 2)).biUnion
          (fun j => (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime), (1 : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ j ∈ Finset.Ico L (2 * L + 2),
          ∑ p ∈ (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
        have hbi : ∀ (s : Finset ℕ) (f : ℕ → Finset ℕ),
            ∑ p ∈ s.biUnion f, (1 : ℝ) / (p : ℝ) ≤ ∑ j ∈ s, ∑ p ∈ f j, (1 : ℝ) / (p : ℝ) := by
          intro s f
          classical
          induction s using Finset.induction with
          | empty => simp
          | insert a s ha ih =>
            rw [Finset.biUnion_insert, Finset.sum_insert ha]
            have hun : ∑ p ∈ f a ∪ s.biUnion f, (1 : ℝ) / (p : ℝ) ≤
                (∑ p ∈ f a, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ s.biUnion f, (1 : ℝ) / (p : ℝ) := by
              have h := Finset.sum_union_inter (s₁ := f a) (s₂ := s.biUnion f)
                (f := fun p : ℕ => (1 : ℝ) / (p : ℝ))
              have hnn : 0 ≤ ∑ p ∈ f a ∩ s.biUnion f, (1 : ℝ) / (p : ℝ) :=
                Finset.sum_nonneg fun _ _ => by positivity
              linarith
            exact hun.trans (add_le_add le_rfl ih)
        exact hbi _ _
    _ ≤ ∑ j ∈ Finset.Ico L (2 * L + 2), (2 : ℝ) / (j : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        simp only [Finset.mem_Ico] at hj
        exact sum_primes_dyadic_le j (le_trans hL_ge hj.1)
    _ ≤ ∑ _j ∈ Finset.Ico L (2 * L + 2), (2 : ℝ) / (L : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        simp only [Finset.mem_Ico] at hj
        exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast (by omega : 0 < L))
          (by exact_mod_cast hj.1)
    _ = ((L + 2 : ℕ) : ℝ) * ((2 : ℝ) / (L : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Ico, show 2 * L + 2 - L = L + 2 by omega, nsmul_eq_mul]
    _ ≤ 6 := by
        have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
        rw [mul_div_assoc', div_le_iff₀ hL_pos]
        have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge
        push_cast
        linarith

private lemma card_multiples_Icc (X d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 X).filter (fun n => d ∣ n)).card = X / d := by
  have hbij : ((Finset.Icc 1 X).filter (fun n => d ∣ n)) =
      (Finset.Icc 1 (X / d)).image (fun k => d * k) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hn1, hnX⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · by_contra hk0
        have : k = 0 := by omega
        subst this; omega
      · exact (Nat.le_div_iff_mul_le hd).mpr (by linarith)
    · rintro ⟨k, ⟨hk1, hkdiv⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, k, rfl⟩
      · exact Nat.mul_pos hd (by omega)
      · exact (Nat.le_div_iff_mul_le hd).mp hkdiv |> fun h => by linarith
  rw [hbij, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hd h),
    Nat.card_Icc]
  simp

private lemma turan_variance (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, ((n.primeFactors.card : ℝ) - H X) ^ 2 ≤ 3 * (X : ℝ) * H X := by
  set P := (Finset.Icc 1 X).filter Nat.Prime
  have homega : ∀ n ∈ Finset.Icc 1 X,
      (n.primeFactors.card : ℝ) = ∑ p ∈ P, if p ∣ n then (1 : ℝ) else 0 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast congrArg Finset.card (by
      ext p
      simp only [Nat.mem_primeFactors, P, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hp, hpdvd, hn0⟩
        exact ⟨⟨⟨hp.pos, (Nat.le_of_dvd (by omega) hpdvd).trans hn.2⟩, hp⟩, hpdvd⟩
      · rintro ⟨⟨_, hp⟩, hpdvd⟩
        exact ⟨hp, hpdvd, by omega⟩)
  have hsum1_ge : (X : ℝ) * H X - (X : ℝ) ≤ ∑ n ∈ Finset.Icc 1 X, (n.primeFactors.card : ℝ) := by
    calc ∑ n ∈ Finset.Icc 1 X, (n.primeFactors.card : ℝ)
        = ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ P, if p ∣ n then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl homega
      _ = ∑ p ∈ P, ∑ n ∈ Finset.Icc 1 X, if p ∣ n then (1 : ℝ) else 0 := Finset.sum_comm
      _ = ∑ p ∈ P, ((X / p : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          simp only [P, Finset.mem_filter] at hp
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
            card_multiples_Icc X p hp.2.pos]
      _ ≥ ∑ p ∈ P, ((X : ℝ) / (p : ℝ) - 1) := by
          refine Finset.sum_le_sum fun p hp => ?_
          simp only [P, Finset.mem_filter] at hp
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
          have hdiv : (X : ℝ) < ((X / p : ℕ) + 1 : ℝ) * (p : ℝ) := by
            have := Nat.lt_div_mul_add hp.2.pos (a := X)
            exact_mod_cast (show X < (X / p + 1) * p by nlinarith)
          rw [sub_le_iff_le_add, div_le_iff₀ hp_pos]
          linarith
      _ = (X : ℝ) * H X - (P.card : ℝ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
          unfold H
          rw [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun p _ => by ring
      _ ≥ (X : ℝ) * H X - (X : ℝ) := by
          have hP_le : P.card ≤ X := by
            calc P.card ≤ (Finset.Icc 1 X).card := Finset.card_filter_le _ _
              _ = X := by rw [Nat.card_Icc]; omega
          have : (P.card : ℝ) ≤ (X : ℝ) := by exact_mod_cast hP_le
          linarith
  have hsum2_le : ∑ n ∈ Finset.Icc 1 X, (n.primeFactors.card : ℝ) ^ 2 ≤
      (X : ℝ) * H X + (X : ℝ) * (H X) ^ 2 := by
    have hsq : ∀ n ∈ Finset.Icc 1 X,
        (n.primeFactors.card : ℝ) ^ 2 =
          ∑ p ∈ P, ∑ q ∈ P, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 := by
      intro n hn
      rw [homega n hn, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [hp, hq]
    calc ∑ n ∈ Finset.Icc 1 X, (n.primeFactors.card : ℝ) ^ 2
        = ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ P, ∑ q ∈ P, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl hsq
      _ = ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Finset.Icc 1 X, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((if p = q then (X : ℝ) / (p : ℝ) else 0) +
            (X : ℝ) / ((p : ℝ) * (q : ℝ))) := by
          refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
          simp only [P, Finset.mem_filter] at hp hq
          by_cases hpq : p = q
          · subst hpq
            have h1 : (∑ n ∈ Finset.Icc 1 X, if p ∣ n ∧ p ∣ n then (1 : ℝ) else 0) =
                ((X / p : ℕ) : ℝ) := by
              simp only [and_self]
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
                card_multiples_Icc X p hp.2.pos]
            rw [h1, if_pos rfl]
            have hle : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / (p : ℝ) := by
              rw [le_div_iff₀ (by exact_mod_cast hp.2.pos)]
              exact_mod_cast Nat.div_mul_le_self X p
            have hnn : (0 : ℝ) ≤ (X : ℝ) / ((p : ℝ) * (p : ℝ)) := by positivity
            linarith
          · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp.2 hq.2).mpr hpq
            have h1 : (∑ n ∈ Finset.Icc 1 X, if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) =
                ((X / (p * q) : ℕ) : ℝ) := by
              have hiff : ∀ n, (p ∣ n ∧ q ∣ n) ↔ p * q ∣ n := fun n =>
                ⟨fun ⟨h1, h2⟩ => hcop.mul_dvd_of_dvd_of_dvd h1 h2,
                 fun h => ⟨dvd_trans (dvd_mul_right p q) h, dvd_trans (dvd_mul_left q p) h⟩⟩
              simp_rw [hiff]
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
                card_multiples_Icc X (p * q) (Nat.mul_pos hp.2.pos hq.2.pos)]
            rw [h1, if_neg hpq, zero_add]
            rw [le_div_iff₀ (by exact_mod_cast Nat.mul_pos hp.2.pos hq.2.pos)]
            exact_mod_cast Nat.div_mul_le_self X (p * q)
      _ = (X : ℝ) * H X + (X : ℝ) * (H X) ^ 2 := by
          simp_rw [Finset.sum_add_distrib]
          congr 1
          · unfold H
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [Finset.sum_ite_eq P p, if_pos hp]
            ring
          · unfold H
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => by ring
  have hexpand : ∑ n ∈ Finset.Icc 1 X, ((n.primeFactors.card : ℝ) - H X) ^ 2 =
      (∑ n ∈ Finset.Icc 1 X, (n.primeFactors.card : ℝ) ^ 2) -
        2 * H X * (∑ n ∈ Finset.Icc 1 X, (n.primeFactors.card : ℝ)) +
        (X : ℝ) * (H X) ^ 2 := by
    have hcard : ((Finset.Icc 1 X).card : ℝ) = (X : ℝ) := by
      rw [Nat.card_Icc]; simp
    calc ∑ n ∈ Finset.Icc 1 X, ((n.primeFactors.card : ℝ) - H X) ^ 2
        = ∑ n ∈ Finset.Icc 1 X, ((n.primeFactors.card : ℝ) ^ 2 -
            2 * H X * (n.primeFactors.card : ℝ) + (H X) ^ 2) := by
          refine Finset.sum_congr rfl fun n _ => by ring
      _ = (∑ n ∈ Finset.Icc 1 X, (n.primeFactors.card : ℝ) ^ 2) -
            2 * H X * (∑ n ∈ Finset.Icc 1 X, (n.primeFactors.card : ℝ)) +
            ((Finset.Icc 1 X).card : ℝ) * (H X) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_const, nsmul_eq_mul]
      _ = _ := by rw [hcard]
  rw [hexpand]
  have hH_nn : 0 ≤ H X := H_nonneg X
  nlinarith

private lemma sum_Omega_sub_omega_le (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, ((n.primeFactorsList.length - n.primeFactors.card : ℕ) : ℝ) ≤ (X : ℝ) := by
  have hdiff_n : ∀ n ∈ Finset.Icc 1 X,
      n.primeFactorsList.length - n.primeFactors.card =
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
          ∑ k ∈ Finset.Icc 2 X, if p ^ k ∣ n then 1 else 0 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hlen : n.primeFactorsList.length = ∑ p ∈ n.primeFactors, n.factorization p := by
      have hlist : ∀ l : List ℕ, l.length = ∑ x ∈ l.toFinset, l.count x := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih =>
          rw [List.length_cons, ih, List.toFinset_cons]
          by_cases ha : a ∈ l.toFinset
          · rw [Finset.insert_eq_of_mem ha]
            have hsplit : ∑ x ∈ l.toFinset, (a :: l).count x =
                ∑ x ∈ l.toFinset, (l.count x + if a = x then 1 else 0) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              by_cases hax : a = x
              · subst hax; simp
              · simp [hax]
            rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq l.toFinset a, if_pos ha]
          · rw [Finset.sum_insert ha]
            have ha' : a ∉ l := by simpa using ha
            have hc0 : l.count a = 0 := List.count_eq_zero.mpr ha'
            have hrest : ∑ x ∈ l.toFinset, (a :: l).count x = ∑ x ∈ l.toFinset, l.count x := by
              refine Finset.sum_congr rfl fun x hx => ?_
              have hne : x ≠ a := fun h => ha (h ▸ hx)
              simp [hne.symm]
            rw [hrest, List.count_cons_self, hc0]
            omega
      have hfin : n.primeFactorsList.toFinset = n.primeFactors := by
        ext p; simp [Nat.mem_primeFactors, hn0]
      rw [hlist n.primeFactorsList, hfin]
      refine Finset.sum_congr rfl fun p _ => Nat.primeFactorsList_count_eq
    have hcard : n.primeFactors.card = ∑ _p ∈ n.primeFactors, 1 := by simp
    have hsub : n.primeFactorsList.length - n.primeFactors.card =
        ∑ p ∈ n.primeFactors, (n.factorization p - 1) := by
      rw [hlen, hcard]
      have hle : ∀ p ∈ n.primeFactors, 1 ≤ n.factorization p := fun p hp =>
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hp))
      have hadd : ∑ p ∈ n.primeFactors, (n.factorization p - 1) + ∑ _p ∈ n.primeFactors, 1 =
          ∑ p ∈ n.primeFactors, n.factorization p := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p hp => Nat.sub_add_cancel (hle p hp)
      omega
    rw [hsub]
    have hsub_P : n.primeFactors ⊆ (Finset.Icc 1 X).filter Nat.Prime := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp.1.pos, (Nat.le_of_dvd (by omega) hp.2.1).trans hn.2⟩, hp.1⟩
    rw [Finset.sum_subset hsub_P]
    · refine Finset.sum_congr rfl fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      have hinner : (∑ k ∈ Finset.Icc 2 X, if p ^ k ∣ n then 1 else 0) =
          ((Finset.Icc 2 X).filter (fun k => p ^ k ∣ n)).card := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      rw [hinner]
      have hfilt : (Finset.Icc 2 X).filter (fun k => p ^ k ∣ n) =
          Finset.Icc 2 (n.factorization p) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, hp.2.pow_dvd_iff_le_factorization hn0]
        constructor
        · rintro ⟨⟨h2, _⟩, hle⟩; exact ⟨h2, hle⟩
        · rintro ⟨h2, hle⟩
          refine ⟨⟨h2, ?_⟩, hle⟩
          have hpow : p ^ k ∣ n := (hp.2.pow_dvd_iff_le_factorization hn0).mpr hle
          have hple : p ^ k ≤ n := Nat.le_of_dvd (by omega) hpow
          have h2k : k ≤ 2 ^ k := Nat.le_of_lt (Nat.lt_two_pow_self)
          have h2p : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.2.two_le k
          omega
      rw [hfilt, Nat.card_Icc]
      omega
    · intro p hp hnot
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      have hfac0 : n.factorization p = 0 := by
        by_contra hne
        exact hnot (Nat.support_factorization n ▸ Finsupp.mem_support_iff.mpr hne)
      rw [hfac0]
      rfl
  calc ∑ n ∈ Finset.Icc 1 X, ((n.primeFactorsList.length - n.primeFactors.card : ℕ) : ℝ)
      = ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
          ∑ k ∈ Finset.Icc 2 X, if p ^ k ∣ n then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hdiff_n n hn]
        push_cast
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
    _ = ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, ∑ k ∈ Finset.Icc 2 X,
          ∑ n ∈ Finset.Icc 1 X, if p ^ k ∣ n then (1 : ℝ) else 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ ≤ ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, ∑ k ∈ Finset.Icc 2 X, (X : ℝ) / ((p : ℝ) ^ k) := by
        refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun k _ => ?_
        simp only [Finset.mem_filter] at hp
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
          card_multiples_Icc X (p ^ k) (pow_pos hp.2.pos k)]
        rw [le_div_iff₀ (by exact_mod_cast pow_pos hp.2.pos k)]
        exact_mod_cast Nat.div_mul_le_self X (p ^ k)
    _ ≤ ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (X : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        simp only [Finset.mem_filter] at hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
        have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
        have hpm1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        have hgeom : ∑ k ∈ Finset.Icc 2 X, ((1 : ℝ) / (p : ℝ)) ^ k ≤
            (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
          have htele : ∀ k : ℕ, 1 ≤ k → ((1 : ℝ) / (p : ℝ)) ^ k =
              (1 / ((p : ℝ) - 1)) * (((1 : ℝ) / (p : ℝ)) ^ (k - 1) - ((1 : ℝ) / (p : ℝ)) ^ k) := by
            intro k hk
            cases k with
            | zero => omega
            | succ m =>
              simp only [Nat.add_sub_cancel, pow_succ]
              field_simp
          have hsum_eq : ∑ k ∈ Finset.Icc 2 X, ((1 : ℝ) / (p : ℝ)) ^ k =
              (1 / ((p : ℝ) - 1)) * ∑ k ∈ Finset.Icc 2 X,
                (((1 : ℝ) / (p : ℝ)) ^ (k - 1) - ((1 : ℝ) / (p : ℝ)) ^ k) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k hk => htele k (by
              simp only [Finset.mem_Icc] at hk; omega)
          rw [hsum_eq]
          have htele_le : ∑ k ∈ Finset.Icc 2 X,
              (((1 : ℝ) / (p : ℝ)) ^ (k - 1) - ((1 : ℝ) / (p : ℝ)) ^ k) ≤ (1 : ℝ) / (p : ℝ) := by
            by_cases hX2 : X < 2
            · have : Finset.Icc 2 X = ∅ := Finset.Icc_eq_empty (by omega)
              rw [this, Finset.sum_empty]; positivity
            · have hrec : ∀ m : ℕ, 2 ≤ m →
                  ∑ k ∈ Finset.Icc 2 m,
                    (((1 : ℝ) / (p : ℝ)) ^ (k - 1) - ((1 : ℝ) / (p : ℝ)) ^ k) =
                  (1 : ℝ) / (p : ℝ) - ((1 : ℝ) / (p : ℝ)) ^ m := by
                intro m hm
                induction m with
                | zero => omega
                | succ m ih =>
                  by_cases hm2 : m < 2
                  · have hm1 : m = 1 := by omega
                    subst hm1; simp
                  · rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
                    simp only [Nat.add_sub_cancel]
                    ring
              rw [hrec X (by omega)]
              have : (0 : ℝ) ≤ ((1 : ℝ) / (p : ℝ)) ^ X := by positivity
              linarith
          calc (1 / ((p : ℝ) - 1)) * ∑ k ∈ Finset.Icc 2 X,
                (((1 : ℝ) / (p : ℝ)) ^ (k - 1) - ((1 : ℝ) / (p : ℝ)) ^ k)
              ≤ (1 / ((p : ℝ) - 1)) * ((1 : ℝ) / (p : ℝ)) :=
                mul_le_mul_of_nonneg_left htele_le (by positivity)
            _ = (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by field_simp
        calc ∑ k ∈ Finset.Icc 2 X, (X : ℝ) / ((p : ℝ) ^ k)
            = (X : ℝ) * ∑ k ∈ Finset.Icc 2 X, ((1 : ℝ) / (p : ℝ)) ^ k := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => by rw [one_div_pow, mul_one_div]
          _ ≤ (X : ℝ) * ((1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) :=
              mul_le_mul_of_nonneg_left hgeom (by positivity)
          _ = (X : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by ring
    _ ≤ ∑ m ∈ Finset.Icc 2 X, (X : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m hm _ => ?_)
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨hp.2.two_le, hp.1.2⟩
        · simp only [Finset.mem_Icc] at hm
          have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
          have : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) := by nlinarith
          exact div_nonneg (by positivity) this
    _ ≤ (X : ℝ) := by
        have htele : ∀ m : ℕ, 2 ≤ m →
            (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) = (1 : ℝ) / ((m - 1 : ℕ) : ℝ) - (1 : ℝ) / (m : ℝ) := by
          intro m hm
          have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
            simpa using Nat.cast_sub (R := ℝ) (by omega : 1 ≤ m)
          rw [hm1]
          have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
          have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
            have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
            linarith
          field_simp
          ring
        have hsum_le : ∑ m ∈ Finset.Icc 2 X, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 1 := by
          by_cases hX2 : X < 2
          · have : Finset.Icc 2 X = ∅ := Finset.Icc_eq_empty (by omega)
            rw [this, Finset.sum_empty]; norm_num
          · have hrec : ∀ M : ℕ, 2 ≤ M →
                ∑ m ∈ Finset.Icc 2 M, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) = 1 - (1 : ℝ) / (M : ℝ) := by
              intro M hM
              induction M with
              | zero => omega
              | succ M ih =>
                by_cases hM2 : M < 2
                · have hM1 : M = 1 := by omega
                  subst hM1; norm_num
                · rw [Finset.sum_Icc_succ_top (by omega), ih (by omega), htele (M + 1) (by omega)]
                  simp only [Nat.add_sub_cancel]
                  ring
            rw [hrec X (by omega)]
            have : (0 : ℝ) ≤ (1 : ℝ) / (X : ℝ) := by positivity
            linarith
        calc ∑ m ∈ Finset.Icc 2 X, (X : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))
            = (X : ℝ) * ∑ m ∈ Finset.Icc 2 X, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun m _ => by ring
          _ ≤ (X : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = (X : ℝ) := mul_one _

private lemma exists_sqfree_part (n : ℕ) (hn : 0 < n) :
    ∃ s r : ℕ, Squarefree s ∧ n = s * r ^ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsq : Squarefree n
    · exact ⟨n, 1, hsq, by ring⟩
    · rw [Nat.squarefree_iff_prime_squarefree] at hsq
      push Not at hsq
      obtain ⟨p, hp, hpp⟩ := hsq
      obtain ⟨m, hm⟩ := hpp
      have hm_pos : 0 < m := by
        by_contra h0
        have : m = 0 := by omega
        subst this; simp at hm; omega
      have hm_lt : m < n := by
        have hp2 : 2 ≤ p := hp.two_le
        have : 4 ≤ p * p := by nlinarith
        nlinarith
      obtain ⟨s, r, hs, hms⟩ := ih m hm_lt hm_pos
      exact ⟨s, p * r, hs, by rw [hm, hms]; ring⟩

private lemma squarefree_triple_prod_square {s₁ s₂ s₃ : ℕ}
    (h1 : Squarefree s₁) (h2 : Squarefree s₂) (h3 : Squarefree s₃)
    (hsq : IsSquare (s₁ * s₂ * s₃)) :
    let u := Nat.gcd s₁ s₂
    u ∣ s₁ ∧ u ^ 2 * s₃ = s₁ * s₂ := by
  intro u
  have h1ne : s₁ ≠ 0 := h1.ne_zero
  have h2ne : s₂ ≠ 0 := h2.ne_zero
  have h3ne : s₃ ≠ 0 := h3.ne_zero
  have hune : u ≠ 0 := Nat.gcd_ne_zero_left h1ne
  refine ⟨Nat.gcd_dvd_left s₁ s₂, ?_⟩
  apply Nat.eq_of_factorization_eq (mul_ne_zero (pow_ne_zero 2 hune) h3ne) (mul_ne_zero h1ne h2ne)
  intro p
  rw [Nat.factorization_mul (pow_ne_zero 2 hune) h3ne, Nat.factorization_pow,
    Nat.factorization_mul h1ne h2ne]
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hp : p.Prime
  · have hv1 : s₁.factorization p ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have hpp : p * p ∣ s₁ := by
        rw [← sq]; exact (hp.pow_dvd_iff_le_factorization h1ne).mpr hgt
      exact hp.ne_one (Nat.isUnit_iff.mp (h1 p hpp))
    have hv2 : s₂.factorization p ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have hpp : p * p ∣ s₂ := by
        rw [← sq]; exact (hp.pow_dvd_iff_le_factorization h2ne).mpr hgt
      exact hp.ne_one (Nat.isUnit_iff.mp (h2 p hpp))
    have hv3 : s₃.factorization p ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have hpp : p * p ∣ s₃ := by
        rw [← sq]; exact (hp.pow_dvd_iff_le_factorization h3ne).mpr hgt
      exact hp.ne_one (Nat.isUnit_iff.mp (h3 p hpp))
    have heven : Even (s₁.factorization p + s₂.factorization p + s₃.factorization p) := by
      obtain ⟨k, hk⟩ := hsq
      have hkne : k ≠ 0 := by
        intro hk0; subst hk0; simp at hk
        rcases hk with (h | h) | h
        · exact h1ne h
        · exact h2ne h
        · exact h3ne h
      have hfac := congrArg (fun m => m.factorization p) hk
      rw [Nat.factorization_mul (mul_ne_zero h1ne h2ne) h3ne,
        Nat.factorization_mul h1ne h2ne, Nat.factorization_mul hkne hkne] at hfac
      simp only [Finsupp.coe_add, Pi.add_apply] at hfac
      exact ⟨k.factorization p, hfac⟩
    have hgcd_fac : u.factorization p = min (s₁.factorization p) (s₂.factorization p) := by
      exact Nat.factorization_gcd h1ne h2ne |> fun h => congrArg (fun f => f p) h
    rw [hgcd_fac]
    rcases heven with ⟨t, ht⟩
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma no_triple_square_in_good_set (N M T : ℕ) (hM : 1 ≤ M) (hT : 1 ≤ T) :
    let K := M * T ^ 2
    let A := (Finset.Icc 1 N).filter fun n =>
      N ≤ M * n ∧ (∀ t ∈ Finset.Icc (T + 1) N, ¬ t ^ 2 ∣ n) ∧
      (∀ d ∈ Finset.Icc 1 N, d ∣ n → ¬ (N ≤ K ^ 2 * d ^ 2 ∧ d ^ 2 ≤ K ^ 2 * N))
    ∀ S ⊆ A, S.card = 3 → ¬ IsSquare (∏ n ∈ S, n) := by
  intro K A S hSA hScard hsq
  rw [Finset.card_eq_three] at hScard
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hScard
  have hprod : ∏ n ∈ ({a, b, c} : Finset ℕ), n = a * b * c := by
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
      Finset.prod_singleton]
    ring
  rw [hprod] at hsq
  have haA : a ∈ A := hSA (by simp)
  have hbA : b ∈ A := hSA (by simp)
  have hcA : c ∈ A := hSA (by simp)
  simp only [A, Finset.mem_filter, Finset.mem_Icc] at haA hbA hcA
  obtain ⟨s₁, r₁, hs₁, ha_eq⟩ := exists_sqfree_part a (by omega)
  obtain ⟨s₂, r₂, hs₂, hb_eq⟩ := exists_sqfree_part b (by omega)
  obtain ⟨s₃, r₃, hs₃, hc_eq⟩ := exists_sqfree_part c (by omega)
  have hr₁_le : r₁ ≤ T := by
    by_contra hgt
    have hr₁_le_N : r₁ ≤ N := by
      have hs₁_pos : 1 ≤ s₁ := Nat.pos_of_ne_zero hs₁.ne_zero
      have h1 : r₁ ^ 2 ≤ a := by rw [ha_eq]; exact Nat.le_mul_of_pos_left _ hs₁_pos
      have h2 : r₁ ≤ r₁ ^ 2 := Nat.le_self_pow (by norm_num) r₁
      omega
    exact haA.2.2.1 r₁ ⟨by omega, hr₁_le_N⟩ ⟨s₁, by rw [ha_eq]; ring⟩
  have hr₂_le : r₂ ≤ T := by
    by_contra hgt
    have hr₂_le_N : r₂ ≤ N := by
      have hs₂_pos : 1 ≤ s₂ := Nat.pos_of_ne_zero hs₂.ne_zero
      have h1 : r₂ ^ 2 ≤ b := by rw [hb_eq]; exact Nat.le_mul_of_pos_left _ hs₂_pos
      have h2 : r₂ ≤ r₂ ^ 2 := Nat.le_self_pow (by norm_num) r₂
      omega
    exact hbA.2.2.1 r₂ ⟨by omega, hr₂_le_N⟩ ⟨s₂, by rw [hb_eq]; ring⟩
  have hr₃_le : r₃ ≤ T := by
    by_contra hgt
    have hr₃_le_N : r₃ ≤ N := by
      have hs₃_pos : 1 ≤ s₃ := Nat.pos_of_ne_zero hs₃.ne_zero
      have h1 : r₃ ^ 2 ≤ c := by rw [hc_eq]; exact Nat.le_mul_of_pos_left _ hs₃_pos
      have h2 : r₃ ≤ r₃ ^ 2 := Nat.le_self_pow (by norm_num) r₃
      omega
    exact hcA.2.2.1 r₃ ⟨by omega, hr₃_le_N⟩ ⟨s₃, by rw [hc_eq]; ring⟩
  have hsq_s : IsSquare (s₁ * s₂ * s₃) := by
    obtain ⟨w, hw⟩ := hsq
    have hmul : a * b * c = (s₁ * s₂ * s₃) * (r₁ * r₂ * r₃) ^ 2 := by
      rw [ha_eq, hb_eq, hc_eq]; ring
    rw [hmul] at hw
    have hr_ne : r₁ * r₂ * r₃ ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num), mul_zero] at hmul
      have : 0 < a * b * c := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
      omega
    have hdvd : r₁ * r₂ * r₃ ∣ w := by
      have hsq_dvd : (r₁ * r₂ * r₃) ^ 2 ∣ w ^ 2 := ⟨s₁ * s₂ * s₃, by rw [sq, ← hw]; ring⟩
      exact (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp hsq_dvd
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨t, ?_⟩
    have hcancel : (s₁ * s₂ * s₃) * (r₁ * r₂ * r₃) ^ 2 = (t * t) * (r₁ * r₂ * r₃) ^ 2 := by
      rw [hw, ht]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hr_ne) 2) hcancel
  obtain ⟨hu_dvd_s₁, hu_eq⟩ := squarefree_triple_prod_square hs₁ hs₂ hs₃ hsq_s
  set u := Nat.gcd s₁ s₂
  have hs₁_lo : N ≤ K * s₁ := by
    have h1 : r₁ ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hr₁_le 2
    have h2 : a ≤ s₁ * T ^ 2 := by rw [ha_eq]; exact Nat.mul_le_mul_left s₁ h1
    calc N ≤ M * a := haA.2.1
      _ ≤ M * (s₁ * T ^ 2) := Nat.mul_le_mul_left M h2
      _ = K * s₁ := by simp only [K]; ring
  have hs₂_lo : N ≤ K * s₂ := by
    have h1 : r₂ ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hr₂_le 2
    have h2 : b ≤ s₂ * T ^ 2 := by rw [hb_eq]; exact Nat.mul_le_mul_left s₂ h1
    calc N ≤ M * b := hbA.2.1
      _ ≤ M * (s₂ * T ^ 2) := Nat.mul_le_mul_left M h2
      _ = K * s₂ := by simp only [K]; ring
  have hs₃_lo : N ≤ K * s₃ := by
    have h1 : r₃ ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hr₃_le 2
    have h2 : c ≤ s₃ * T ^ 2 := by rw [hc_eq]; exact Nat.mul_le_mul_left s₃ h1
    calc N ≤ M * c := hcA.2.1
      _ ≤ M * (s₃ * T ^ 2) := Nat.mul_le_mul_left M h2
      _ = K * s₃ := by simp only [K]; ring
  have hs₁_hi : s₁ ≤ N := by
    have hr1_pos : 1 ≤ r₁ ^ 2 := by
      by_contra h0
      have : r₁ ^ 2 = 0 := by omega
      rw [this, mul_zero] at ha_eq; omega
    calc s₁ ≤ s₁ * r₁ ^ 2 := Nat.le_mul_of_pos_right s₁ hr1_pos
      _ = a := ha_eq.symm
      _ ≤ N := haA.1.2
  have hs₂_hi : s₂ ≤ N := by
    have hr2_pos : 1 ≤ r₂ ^ 2 := by
      by_contra h0
      have : r₂ ^ 2 = 0 := by omega
      rw [this, mul_zero] at hb_eq; omega
    calc s₂ ≤ s₂ * r₂ ^ 2 := Nat.le_mul_of_pos_right s₂ hr2_pos
      _ = b := hb_eq.symm
      _ ≤ N := hbA.1.2
  have hs₃_hi : s₃ ≤ N := by
    have hr3_pos : 1 ≤ r₃ ^ 2 := by
      by_contra h0
      have : r₃ ^ 2 = 0 := by omega
      rw [this, mul_zero] at hc_eq; omega
    calc s₃ ≤ s₃ * r₃ ^ 2 := Nat.le_mul_of_pos_right s₃ hr3_pos
      _ = c := hc_eq.symm
      _ ≤ N := hcA.1.2
  have hK_pos : 1 ≤ K := by
    have : 1 ≤ T ^ 2 := by nlinarith
    exact Nat.mul_pos hM this
  have hN_pos : 0 < N := by omega
  have hu_lo : N ≤ K ^ 2 * u ^ 2 := by
    have h1 : N * N ≤ K ^ 2 * (s₁ * s₂) := by
      calc N * N ≤ (K * s₁) * (K * s₂) := Nat.mul_le_mul hs₁_lo hs₂_lo
        _ = K ^ 2 * (s₁ * s₂) := by ring
    have h2 : K ^ 2 * (s₁ * s₂) = K ^ 2 * u ^ 2 * s₃ := by rw [← hu_eq]; ring
    have h3 : K ^ 2 * u ^ 2 * s₃ ≤ K ^ 2 * u ^ 2 * N := Nat.mul_le_mul_left _ hs₃_hi
    exact Nat.le_of_mul_le_mul_right (by linarith) hN_pos
  have hu_hi : u ^ 2 ≤ K ^ 2 * N := by
    have h1 : u ^ 2 * N ≤ K * (u ^ 2 * s₃) := by
      calc u ^ 2 * N ≤ u ^ 2 * (K * s₃) := Nat.mul_le_mul_left _ hs₃_lo
        _ = K * (u ^ 2 * s₃) := by ring
    have h2 : K * (u ^ 2 * s₃) = K * (s₁ * s₂) := by rw [hu_eq]
    have h3 : K * (s₁ * s₂) ≤ K * (N * N) := Nat.mul_le_mul_left K (Nat.mul_le_mul hs₁_hi hs₂_hi)
    have h4 : K * (N * N) ≤ K ^ 2 * N * N := by
      have : K ≤ K ^ 2 := Nat.le_self_pow (by norm_num) K
      nlinarith
    exact Nat.le_of_mul_le_mul_right (by linarith) hN_pos
  have hu_dvd_a : u ∣ a := dvd_trans hu_dvd_s₁ ⟨r₁ ^ 2, ha_eq⟩
  have hu_pos : 1 ≤ u := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left hs₁.ne_zero)
  have hu_le_N : u ≤ N := (Nat.le_of_dvd (by omega) hu_dvd_a).trans haA.1.2
  exact haA.2.2.2 u ⟨hu_pos, hu_le_N⟩ hu_dvd_a ⟨hu_lo, hu_hi⟩

private lemma card_B3_le (N K : ℕ) (hK : 1 ≤ K) (hN : 4 ≤ N) (hS : 48 ≤ H (Nat.sqrt N))
    (hMN : K * Nat.sqrt N + K ≤ N) :
    let B3 := (Finset.Icc 1 N).filter fun n =>
      ∃ d ∈ Finset.Icc 1 N, d ∣ n ∧ N ≤ K ^ 2 * d ^ 2 ∧ d ^ 2 ≤ K ^ 2 * N
    (B3.card : ℝ) ≤ (388 + 384 * (K : ℝ) ^ 2) * (N : ℝ) / H (Nat.sqrt N) := by
  intro B3
  set S := H (Nat.sqrt N)
  have hS_pos : 0 < S := by linarith
  set M₀ := K * Nat.sqrt N + K
  have hM₀_ge_sqrt : Nat.sqrt N ≤ M₀ := by
    have : Nat.sqrt N ≤ K * Nat.sqrt N := Nat.le_mul_of_pos_left _ hK
    omega
  have hM₀_le_real : (M₀ : ℝ) ≤ 2 * (K : ℝ) * Real.sqrt (N : ℝ) := by
    have hsqrt_ge1 : 1 ≤ Nat.sqrt N := by rw [Nat.le_sqrt]; omega
    have hsqrt_le : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity), sq]
      exact_mod_cast Nat.sqrt_le N
    have hK_nn : (0 : ℝ) ≤ (K : ℝ) := by positivity
    have h1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      exact_mod_cast (show 1 ^ 2 ≤ N by omega)
    have hM₀_cast : (M₀ : ℝ) = (K : ℝ) * (Nat.sqrt N : ℝ) + (K : ℝ) := by push_cast [M₀]; ring
    nlinarith
  have hB3_prod : ∀ n ∈ B3, ∃ d ∈ Finset.Icc 1 M₀, ∃ e ∈ Finset.Icc 1 M₀, n = d * e := by
    intro n hn
    simp only [B3, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, d, ⟨hd1, _⟩, ⟨e, he⟩, hdlo, hdhi⟩ := hn
    have he1 : 1 ≤ e := by
      by_contra h0; have : e = 0 := by omega
      subst this; simp at he; omega
    have hd_le : d ≤ M₀ := by
      have h1 : d ^ 2 < (M₀ + 1) ^ 2 := by
        have hsq : N < (Nat.sqrt N + 1) ^ 2 := by
          have := Nat.lt_succ_sqrt N; nlinarith
        have hmul : K ^ 2 * N < K ^ 2 * (Nat.sqrt N + 1) ^ 2 :=
          Nat.mul_lt_mul_of_pos_left hsq (pow_pos hK 2)
        have hM : K ^ 2 * (Nat.sqrt N + 1) ^ 2 = M₀ ^ 2 := by simp only [M₀]; ring
        have : M₀ ^ 2 < (M₀ + 1) ^ 2 := by nlinarith
        omega
      by_contra hgt
      have : (M₀ + 1) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have he_le : e ≤ M₀ := by
      have he_sq : e ^ 2 ≤ K ^ 2 * N := by
        have h1 : (d * e) ^ 2 ≤ N ^ 2 := by rw [← he]; exact Nat.pow_le_pow_left hnN 2
        have h2 : N * e ^ 2 ≤ (K ^ 2 * d ^ 2) * e ^ 2 := Nat.mul_le_mul_right _ hdlo
        have h3 : (K ^ 2 * d ^ 2) * e ^ 2 = K ^ 2 * (d * e) ^ 2 := by ring
        have h4 : K ^ 2 * (d * e) ^ 2 ≤ K ^ 2 * N ^ 2 := Nat.mul_le_mul_left _ h1
        have h5 : K ^ 2 * N ^ 2 = N * (K ^ 2 * N) := by ring
        exact Nat.le_of_mul_le_mul_left (by linarith) (by omega : 0 < N)
      have h1 : e ^ 2 < (M₀ + 1) ^ 2 := by
        have hsq : N < (Nat.sqrt N + 1) ^ 2 := by
          have := Nat.lt_succ_sqrt N; nlinarith
        have hmul : K ^ 2 * N < K ^ 2 * (Nat.sqrt N + 1) ^ 2 :=
          Nat.mul_lt_mul_of_pos_left hsq (pow_pos hK 2)
        have hM : K ^ 2 * (Nat.sqrt N + 1) ^ 2 = M₀ ^ 2 := by simp only [M₀]; ring
        have : M₀ ^ 2 < (M₀ + 1) ^ 2 := by nlinarith
        omega
      by_contra hgt
      have : (M₀ + 1) ^ 2 ≤ e ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    exact ⟨d, Finset.mem_Icc.mpr ⟨hd1, hd_le⟩, e, Finset.mem_Icc.mpr ⟨he1, he_le⟩, he⟩
  set C1 := (Finset.Icc 1 N).filter fun n => (5 / 4 : ℝ) * S < (n.primeFactors.card : ℝ)
  set C2 := (Finset.Icc 1 N).filter fun n =>
    (1 / 4 : ℝ) * S < ((n.primeFactorsList.length - n.primeFactors.card : ℕ) : ℝ)
  set D := (Finset.Icc 1 M₀).filter fun d => (d.primeFactors.card : ℝ) ≤ (3 / 4 : ℝ) * S
  set C3 := (D ×ˢ Finset.Icc 1 M₀).image fun p => p.1 * p.2
  have hB3_sub : B3 ⊆ C1 ∪ C2 ∪ C3 := by
    intro n hn
    by_cases h1 : n ∈ C1
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
    · by_cases h2 : n ∈ C2
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
      · refine Finset.mem_union_right _ ?_
        have hnIcc : n ∈ Finset.Icc 1 N := (Finset.mem_filter.mp hn).1
        simp only [C1, C2, Finset.mem_filter, not_and, not_lt] at h1 h2
        have h1' := h1 hnIcc
        have h2' := h2 hnIcc
        have hcard_le : ∀ m : ℕ, m ≠ 0 → m.primeFactors.card ≤ m.primeFactorsList.length := by
          intro m hm0
          have hfin : m.primeFactors = m.primeFactorsList.toFinset := by
            ext p; simp [Nat.mem_primeFactors, hm0]
          rw [hfin]
          exact List.toFinset_card_le _
        have hn0 : n ≠ 0 := by simp only [Finset.mem_Icc] at hnIcc; omega
        have hOm : (n.primeFactorsList.length : ℝ) ≤ (3 / 2 : ℝ) * S := by
          have hcast : ((n.primeFactorsList.length - n.primeFactors.card : ℕ) : ℝ) =
              (n.primeFactorsList.length : ℝ) - (n.primeFactors.card : ℝ) :=
            Nat.cast_sub (hcard_le n hn0)
          linarith
        obtain ⟨d, hd, e, he, rfl⟩ := hB3_prod n hn
        have hd0 : d ≠ 0 := by simp only [Finset.mem_Icc] at hd; omega
        have he0 : e ≠ 0 := by simp only [Finset.mem_Icc] at he; omega
        have hOm_mul : (d * e).primeFactorsList.length =
            d.primeFactorsList.length + e.primeFactorsList.length := by
          have hperm := Nat.perm_primeFactorsList_mul hd0 he0
          rw [hperm.length_eq, List.length_append]
        have hle_d : d.primeFactors.card ≤ d.primeFactorsList.length := hcard_le d hd0
        have hle_e : e.primeFactors.card ≤ e.primeFactorsList.length := hcard_le e he0
        rw [hOm_mul, Nat.cast_add] at hOm
        simp only [C3, Finset.mem_image, Finset.mem_product, Prod.exists]
        by_cases hds : (d.primeFactors.card : ℝ) ≤ (3 / 4 : ℝ) * S
        · exact ⟨d, e, ⟨Finset.mem_filter.mpr ⟨hd, hds⟩, he⟩, rfl⟩
        · have hes : (e.primeFactors.card : ℝ) ≤ (3 / 4 : ℝ) * S := by
            have hd_r : (d.primeFactors.card : ℝ) ≤ (d.primeFactorsList.length : ℝ) := by
              exact_mod_cast hle_d
            have he_r : (e.primeFactors.card : ℝ) ≤ (e.primeFactorsList.length : ℝ) := by
              exact_mod_cast hle_e
            linarith
          exact ⟨e, d, ⟨Finset.mem_filter.mpr ⟨he, hes⟩, hd⟩, mul_comm e d⟩
  have hHN_le : H N ≤ S + 6 := by
    have := H_sub_H_sqrt_le N hN
    linarith
  have hC1_le : (C1.card : ℝ) ≤ 384 * (N : ℝ) / S := by
    have h1 : (C1.card : ℝ) * (S / 8) ^ 2 ≤ ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ) - H N) ^ 2 := by
      calc (C1.card : ℝ) * (S / 8) ^ 2
          = ∑ _n ∈ C1, (S / 8) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ n ∈ C1, ((n.primeFactors.card : ℝ) - H N) ^ 2 := by
            refine Finset.sum_le_sum fun n hn => ?_
            simp only [C1, Finset.mem_filter] at hn
            have hdiff : S / 8 ≤ (n.primeFactors.card : ℝ) - H N := by linarith
            nlinarith
        _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ) - H N) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have h2 := turan_variance N
    have h3 : 3 * (N : ℝ) * H N ≤ 6 * (N : ℝ) * S := by
      have : H N ≤ 2 * S := by linarith
      nlinarith
    rw [le_div_iff₀ hS_pos]
    nlinarith
  have hC2_le : (C2.card : ℝ) ≤ 4 * (N : ℝ) / S := by
    have h1 : (C2.card : ℝ) * (S / 4) ≤
        ∑ n ∈ Finset.Icc 1 N, ((n.primeFactorsList.length - n.primeFactors.card : ℕ) : ℝ) := by
      calc (C2.card : ℝ) * (S / 4)
          = ∑ _n ∈ C2, (S / 4) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ n ∈ C2, ((n.primeFactorsList.length - n.primeFactors.card : ℕ) : ℝ) := by
            refine Finset.sum_le_sum fun n hn => ?_
            simp only [C2, Finset.mem_filter] at hn
            linarith
        _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n.primeFactorsList.length - n.primeFactors.card : ℕ) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    have h2 := sum_Omega_sub_omega_le N
    rw [le_div_iff₀ hS_pos]
    linarith
  have hHM₀_ge : S ≤ H M₀ := H_mono hM₀_ge_sqrt
  have hHM₀_le : H M₀ ≤ 2 * S := by
    have := H_mono hMN
    linarith
  have hD_le : (D.card : ℝ) ≤ 96 * (M₀ : ℝ) / S := by
    have h1 : (D.card : ℝ) * (S / 4) ^ 2 ≤
        ∑ d ∈ Finset.Icc 1 M₀, ((d.primeFactors.card : ℝ) - H M₀) ^ 2 := by
      calc (D.card : ℝ) * (S / 4) ^ 2
          = ∑ _d ∈ D, (S / 4) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ d ∈ D, ((d.primeFactors.card : ℝ) - H M₀) ^ 2 := by
            refine Finset.sum_le_sum fun d hd => ?_
            simp only [D, Finset.mem_filter] at hd
            have hdiff : S / 4 ≤ H M₀ - (d.primeFactors.card : ℝ) := by linarith
            nlinarith
        _ ≤ ∑ d ∈ Finset.Icc 1 M₀, ((d.primeFactors.card : ℝ) - H M₀) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have h2 := turan_variance M₀
    have h3 : 3 * (M₀ : ℝ) * H M₀ ≤ 6 * (M₀ : ℝ) * S := by nlinarith
    rw [le_div_iff₀ hS_pos]
    nlinarith
  have hC3_le : (C3.card : ℝ) ≤ 384 * (K : ℝ) ^ 2 * (N : ℝ) / S := by
    have hcard_C3 : C3.card ≤ D.card * M₀ := by
      calc C3.card ≤ (D ×ˢ Finset.Icc 1 M₀).card := Finset.card_image_le
        _ = D.card * (Finset.Icc 1 M₀).card := Finset.card_product _ _
        _ = D.card * M₀ := by rw [Nat.card_Icc]; simp
    have hcard_C3_r : (C3.card : ℝ) ≤ (D.card : ℝ) * (M₀ : ℝ) := by exact_mod_cast hcard_C3
    have hM₀_sq : (M₀ : ℝ) ^ 2 ≤ 4 * (K : ℝ) ^ 2 * (N : ℝ) := by
      have hsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
      have h1 : (M₀ : ℝ) ^ 2 ≤ (2 * (K : ℝ) * Real.sqrt (N : ℝ)) ^ 2 := by
        nlinarith [hM₀_le_real]
      calc (M₀ : ℝ) ^ 2 ≤ (2 * (K : ℝ) * Real.sqrt (N : ℝ)) ^ 2 := h1
        _ = 4 * (K : ℝ) ^ 2 * (Real.sqrt (N : ℝ)) ^ 2 := by ring
        _ = 4 * (K : ℝ) ^ 2 * (N : ℝ) := by rw [hsq]
    calc (C3.card : ℝ) ≤ (D.card : ℝ) * (M₀ : ℝ) := hcard_C3_r
      _ ≤ (96 * (M₀ : ℝ) / S) * (M₀ : ℝ) := mul_le_mul_of_nonneg_right hD_le (by positivity)
      _ = 96 * (M₀ : ℝ) ^ 2 / S := by ring
      _ ≤ 96 * (4 * (K : ℝ) ^ 2 * (N : ℝ)) / S :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 384 * (K : ℝ) ^ 2 * (N : ℝ) / S := by ring
  have hB3_card : B3.card ≤ C1.card + C2.card + C3.card := by
    calc B3.card ≤ (C1 ∪ C2 ∪ C3).card := Finset.card_le_card hB3_sub
      _ ≤ (C1 ∪ C2).card + C3.card := Finset.card_union_le _ _
      _ ≤ C1.card + C2.card + C3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hB3_r : (B3.card : ℝ) ≤ (C1.card : ℝ) + (C2.card : ℝ) + (C3.card : ℝ) := by
    exact_mod_cast hB3_card
  have hsum_eq : 384 * (N : ℝ) / S + 4 * (N : ℝ) / S + 384 * (K : ℝ) ^ 2 * (N : ℝ) / S =
      (388 + 384 * (K : ℝ) ^ 2) * (N : ℝ) / S := by ring
  linarith

private lemma card_B2_le (N T : ℕ) (hT : 1 ≤ T) :
    let B2 := (Finset.Icc 1 N).filter fun n => ∃ t ∈ Finset.Icc (T + 1) N, t ^ 2 ∣ n
    (B2.card : ℝ) ≤ (N : ℝ) / (T : ℝ) := by
  intro B2
  have hsub : B2 ⊆ (Finset.Icc (T + 1) N).biUnion
      (fun t => (Finset.Icc 1 N).filter fun n => t ^ 2 ∣ n) := by
    intro n hn
    simp only [B2, Finset.mem_filter] at hn
    obtain ⟨hnIcc, t, ht, hdvd⟩ := hn
    exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_filter.mpr ⟨hnIcc, hdvd⟩⟩
  have hcard : (B2.card : ℝ) ≤ ∑ t ∈ Finset.Icc (T + 1) N, (N : ℝ) / ((t : ℝ) ^ 2) := by
    calc (B2.card : ℝ)
        ≤ (((Finset.Icc (T + 1) N).biUnion
            (fun t => (Finset.Icc 1 N).filter fun n => t ^ 2 ∣ n)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ t ∈ Finset.Icc (T + 1) N,
            (((Finset.Icc 1 N).filter fun n => t ^ 2 ∣ n).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ t ∈ Finset.Icc (T + 1) N, ((N / t ^ 2 : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          simp only [Finset.mem_Icc] at ht
          rw [card_multiples_Icc N (t ^ 2) (pow_pos (by omega) 2)]
      _ ≤ ∑ t ∈ Finset.Icc (T + 1) N, (N : ℝ) / ((t : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun t ht => ?_
          simp only [Finset.mem_Icc] at ht
          rw [le_div_iff₀ (by exact_mod_cast pow_pos (by omega : 0 < t) 2)]
          exact_mod_cast Nat.div_mul_le_self N (t ^ 2)
  have htele_sum : ∑ t ∈ Finset.Icc (T + 1) N, (1 : ℝ) / ((t : ℝ) ^ 2) ≤ (1 : ℝ) / (T : ℝ) := by
    by_cases hNT : N < T + 1
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
    · have hle_tele : ∑ t ∈ Finset.Icc (T + 1) N, (1 : ℝ) / ((t : ℝ) ^ 2) ≤
          ∑ t ∈ Finset.Icc (T + 1) N, ((1 : ℝ) / ((t - 1 : ℕ) : ℝ) - (1 : ℝ) / (t : ℝ)) := by
        refine Finset.sum_le_sum fun t ht => ?_
        simp only [Finset.mem_Icc] at ht
        have ht1 : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
          simpa using Nat.cast_sub (R := ℝ) (by omega : 1 ≤ t)
        rw [ht1]
        have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
        have htm1_pos : (0 : ℝ) < (t : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 2 ≤ t)
          linarith
        have hdiff : (1 : ℝ) / ((t : ℝ) - 1) - (1 : ℝ) / (t : ℝ) =
            (1 : ℝ) / ((t : ℝ) * ((t : ℝ) - 1)) := by field_simp; ring
        rw [hdiff]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have hrec : ∀ M : ℕ, T + 1 ≤ M →
          ∑ t ∈ Finset.Icc (T + 1) M, ((1 : ℝ) / ((t - 1 : ℕ) : ℝ) - (1 : ℝ) / (t : ℝ)) =
            (1 : ℝ) / (T : ℝ) - (1 : ℝ) / (M : ℝ) := by
        intro M hM
        induction M with
        | zero => omega
        | succ M ih =>
          by_cases hMT : M < T + 1
          · have hMeq : M = T := by omega
            subst hMeq
            simp [Finset.Icc_self]
          · rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
            simp only [Nat.add_sub_cancel]
            ring
      refine hle_tele.trans ?_
      rw [hrec N (by omega)]
      have : (0 : ℝ) ≤ (1 : ℝ) / (N : ℝ) := by positivity
      linarith
  calc (B2.card : ℝ) ≤ ∑ t ∈ Finset.Icc (T + 1) N, (N : ℝ) / ((t : ℝ) ^ 2) := hcard
    _ = (N : ℝ) * ∑ t ∈ Finset.Icc (T + 1) N, (1 : ℝ) / ((t : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => by ring
    _ ≤ (N : ℝ) * ((1 : ℝ) / (T : ℝ)) := mul_le_mul_of_nonneg_left htele_sum (by positivity)
    _ = (N : ℝ) / (T : ℝ) := by ring

private lemma F3_le_N (N : ℕ) : Erdos121.F 3 N ≤ N := by
  unfold Erdos121.F
  apply csSup_le
  · refine ⟨0, ∅, Finset.empty_subset _, ?_, rfl⟩
    intro S hS hcard
    have : S = ∅ := Finset.subset_empty.mp hS
    subst this
    simp at hcard
  · rintro m ⟨A, hA, _, rfl⟩
    calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA
      _ = N := by rw [Nat.card_Icc]; omega

private lemma card_le_F3 (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hfree : ∀ S ⊆ A, S.card = 3 → ¬ IsSquare (∏ n ∈ S, n)) :
    A.card ≤ Erdos121.F 3 N := by
  unfold Erdos121.F
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro m ⟨B, hB, _, rfl⟩
    calc B.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hB
      _ = N := by rw [Nat.card_Icc]; omega
  · exact ⟨A, hA, hfree, rfl⟩

end Erdos121Three

theorem OMA.solution : type_of% @Erdos121.erdos_121.variants.three := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one
    (Filter.eventually_atTop.mpr ⟨1, fun N hN => by exact_mod_cast (by omega : N ≠ 0)⟩)]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℕ := max 2 (Nat.ceil (4 / ε))
  have hM_ge2 : 2 ≤ M := le_max_left _ _
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM_inv : (1 : ℝ) / (M : ℝ) ≤ ε / 4 := by
    have h1 : 4 / ε ≤ (M : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 _)
    rw [div_le_iff₀ hε] at h1
    rw [div_le_div_iff₀ hM_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  set K : ℕ := M * M ^ 2
  have hK_ge1 : 1 ≤ K := by
    have : 1 ≤ M ^ 2 := by nlinarith
    exact Nat.mul_pos (by omega) this
  have htend : Filter.Tendsto (fun N : ℕ => Erdos121Three.H (Nat.sqrt N)) Filter.atTop Filter.atTop := by
    refine Erdos121Three.tendsto_H_atTop.comp ?_
    rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b ^ 2, fun N hN => by rw [Nat.le_sqrt]; nlinarith⟩
  set C_const : ℝ := 388 + 384 * (K : ℝ) ^ 2
  have hC_pos : 0 < C_const := by positivity
  obtain ⟨N₁, hN₁⟩ := Filter.tendsto_atTop_atTop.mp htend (max 48 (2 * C_const / ε + 1))
  refine ⟨max N₁ (max 4 (4 * K ^ 2)), fun N hN => ?_⟩
  have hN_ge_N₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN_ge4 : 4 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN_ge_4K2 : 4 * K ^ 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hS_ge : max 48 (2 * C_const / ε + 1) ≤ Erdos121Three.H (Nat.sqrt N) := hN₁ N hN_ge_N₁
  have hS48 : 48 ≤ Erdos121Three.H (Nat.sqrt N) := le_trans (le_max_left _ _) hS_ge
  have hS_eps : 2 * C_const / ε + 1 ≤ Erdos121Three.H (Nat.sqrt N) := le_trans (le_max_right _ _) hS_ge
  have hS_pos : 0 < Erdos121Three.H (Nat.sqrt N) := by linarith
  have hMN : K * Nat.sqrt N + K ≤ N := by
    have hsqrt_ge1 : 1 ≤ Nat.sqrt N := by rw [Nat.le_sqrt]; omega
    have hsq : (2 * K * Nat.sqrt N) ^ 2 ≤ N ^ 2 := by
      have h1 : (Nat.sqrt N) ^ 2 ≤ N := by rw [sq]; exact Nat.sqrt_le N
      have h2 : 4 * K ^ 2 * (Nat.sqrt N) ^ 2 ≤ 4 * K ^ 2 * N := Nat.mul_le_mul_left _ h1
      have h3 : 4 * K ^ 2 * N ≤ N * N := Nat.mul_le_mul_right N hN_ge_4K2
      nlinarith
    have hle : 2 * K * Nat.sqrt N ≤ N := by nlinarith
    have : K ≤ K * Nat.sqrt N := Nat.le_mul_of_pos_right K hsqrt_ge1
    nlinarith
  set A := (Finset.Icc 1 N).filter fun n =>
    N ≤ M * n ∧ (∀ t ∈ Finset.Icc (M + 1) N, ¬ t ^ 2 ∣ n) ∧
    (∀ d ∈ Finset.Icc 1 N, d ∣ n → ¬ (N ≤ K ^ 2 * d ^ 2 ∧ d ^ 2 ≤ K ^ 2 * N))
  set B1 := (Finset.Icc 1 N).filter fun n => ¬ N ≤ M * n
  set B2 := (Finset.Icc 1 N).filter fun n => ∃ t ∈ Finset.Icc (M + 1) N, t ^ 2 ∣ n
  set B3 := (Finset.Icc 1 N).filter fun n =>
    ∃ d ∈ Finset.Icc 1 N, d ∣ n ∧ N ≤ K ^ 2 * d ^ 2 ∧ d ^ 2 ≤ K ^ 2 * N
  have hcover : Finset.Icc 1 N ⊆ A ∪ B1 ∪ B2 ∪ B3 := by
    intro n hn
    by_cases h1 : N ≤ M * n
    · by_cases h2 : ∀ t ∈ Finset.Icc (M + 1) N, ¬ t ^ 2 ∣ n
      · by_cases h3 : ∀ d ∈ Finset.Icc 1 N, d ∣ n → ¬ (N ≤ K ^ 2 * d ^ 2 ∧ d ^ 2 ≤ K ^ 2 * N)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hn, h1, h2, h3⟩)))
        · push Not at h3
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, h3⟩)
      · push Not at h2
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, h2⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hn, h1⟩)))
  have hN_le_cards : N ≤ A.card + B1.card + B2.card + B3.card := by
    have h1 : (Finset.Icc 1 N).card = N := by rw [Nat.card_Icc]; omega
    calc N = (Finset.Icc 1 N).card := h1.symm
      _ ≤ (A ∪ B1 ∪ B2 ∪ B3).card := Finset.card_le_card hcover
      _ ≤ (A ∪ B1 ∪ B2).card + B3.card := Finset.card_union_le _ _
      _ ≤ (A ∪ B1).card + B2.card + B3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ A.card + B1.card + B2.card + B3.card :=
          Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have hB1_le : (B1.card : ℝ) ≤ (N : ℝ) / (M : ℝ) := by
    have hsub : B1 ⊆ Finset.Icc 1 (N / M) := by
      intro n hn
      simp only [B1, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      refine ⟨hn.1.1, (Nat.le_div_iff_mul_le (by omega : 0 < M)).mpr (by linarith)⟩
    have hcard : B1.card ≤ N / M := by
      calc B1.card ≤ (Finset.Icc 1 (N / M)).card := Finset.card_le_card hsub
        _ = N / M := by rw [Nat.card_Icc]; simp
    calc (B1.card : ℝ) ≤ ((N / M : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ (N : ℝ) / (M : ℝ) := by
        rw [le_div_iff₀ hM_pos]
        exact_mod_cast Nat.div_mul_le_self N M
  have hB2_le : (B2.card : ℝ) ≤ (N : ℝ) / (M : ℝ) := Erdos121Three.card_B2_le N M (by omega)
  have hB3_le : (B3.card : ℝ) ≤ C_const * (N : ℝ) / Erdos121Three.H (Nat.sqrt N) :=
    Erdos121Three.card_B3_le N K hK_ge1 hN_ge4 hS48 hMN
  have hB3_eps : C_const * (N : ℝ) / Erdos121Three.H (Nat.sqrt N) < (ε / 2) * (N : ℝ) := by
    have hdiv : C_const / Erdos121Three.H (Nat.sqrt N) < ε / 2 := by
      rw [div_lt_iff₀ hS_pos]
      have h1 : 2 * C_const / ε < Erdos121Three.H (Nat.sqrt N) := by linarith
      rw [div_lt_iff₀ hε] at h1
      linarith
    calc C_const * (N : ℝ) / Erdos121Three.H (Nat.sqrt N)
        = (C_const / Erdos121Three.H (Nat.sqrt N)) * (N : ℝ) := by ring
      _ < (ε / 2) * (N : ℝ) := mul_lt_mul_of_pos_right hdiv hN_pos
  have hA_le_F3 : A.card ≤ Erdos121.F 3 N :=
    Erdos121Three.card_le_F3 N A (Finset.filter_subset _ _)
      (Erdos121Three.no_triple_square_in_good_set N M M (by omega) (by omega))
  have hF3_le : (Erdos121.F 3 N : ℝ) ≤ (N : ℝ) := by exact_mod_cast Erdos121Three.F3_le_N N
  have hF3_ge : (1 - ε) * (N : ℝ) < (Erdos121.F 3 N : ℝ) := by
    have hA_r : (A.card : ℝ) ≤ (Erdos121.F 3 N : ℝ) := by exact_mod_cast hA_le_F3
    have hN_r : (N : ℝ) ≤ (A.card : ℝ) + (B1.card : ℝ) + (B2.card : ℝ) + (B3.card : ℝ) := by
      exact_mod_cast hN_le_cards
    have hB12 : (N : ℝ) / (M : ℝ) ≤ (ε / 4) * (N : ℝ) := by
      calc (N : ℝ) / (M : ℝ) = (1 / (M : ℝ)) * (N : ℝ) := by ring
        _ ≤ (ε / 4) * (N : ℝ) := mul_le_mul_of_nonneg_right hM_inv (by positivity)
    linarith
  rw [Real.dist_eq, abs_lt]
  change -ε < (Erdos121.F 3 N : ℝ) / (N : ℝ) - 1 ∧ (Erdos121.F 3 N : ℝ) / (N : ℝ) - 1 < ε
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hN_pos]
    linarith
  · have hle : (Erdos121.F 3 N : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hN_pos).mpr hF3_le
    linarith

