import OMAStatements.S_oeis_a347748

namespace OMA_A347748_TryA

open OMA.S_oeis_a347748 Filter Topology
open scoped BigOperators

private lemma hasPairEndingIn_iff (m d : ℕ) :
    hasPairEndingIn m d = true ↔ ∃ a, a ∣ m ∧ m ≠ 0 ∧ a % 10 = d ∧ (m / a) % 10 = d := by
  rw [hasPairEndingIn, decide_eq_true_eq]
  simp only [Finset.Nonempty, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨a, ⟨ha, hm⟩, h1, h2⟩
    exact ⟨a, ha, hm, h1, h2⟩
  · rintro ⟨a, ha, hm, h1, h2⟩
    exact ⟨a, ⟨ha, hm⟩, h1, h2⟩

private lemma hasPairEndingIn_four_imp_mod20 {m : ℕ} (h : hasPairEndingIn m 4 = true) :
    m % 20 = 16 := by
  rw [hasPairEndingIn_iff] at h
  obtain ⟨a, ha, _, ha4, hb4⟩ := h
  have hmul : a * (m / a) = m := Nat.mul_div_cancel' ha
  have hu : a = 10 * (a / 10) + 4 := by omega
  have hv : m / a = 10 * (m / a / 10) + 4 := by omega
  have hm : m = 20 * (5 * (a / 10) * (m / a / 10) + 2 * (a / 10) + 2 * (m / a / 10)) + 16 := by
    calc m = a * (m / a) := hmul.symm
      _ = (10 * (a / 10) + 4) * (10 * (m / a / 10) + 4) := by rw [← hu, ← hv]
      _ = 20 * (5 * (a / 10) * (m / a / 10) + 2 * (a / 10) + 2 * (m / a / 10)) + 16 := by ring
  omega

private lemma hasPairEndingIn_four_of_dvd_mod10_seven {m p : ℕ}
    (hm0 : m ≠ 0) (hm20 : m % 20 = 16) (hp : p ∣ m) (hp10 : p % 10 = 7) :
    hasPairEndingIn m 4 = true := by
  rw [hasPairEndingIn_iff]
  have h2m : 2 ∣ m := by omega
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr (by omega)
  have h2p : 2 * p ∣ m := hcop.mul_dvd_of_dvd_of_dvd h2m hp
  refine ⟨2 * p, h2p, hm0, by omega, ?_⟩
  have hmul : (2 * p) * (m / (2 * p)) = m := Nat.mul_div_cancel' h2p
  set b := m / (2 * p)
  have hp_eq : 2 * p = 20 * (p / 10) + 14 := by omega
  have hb_eq : b = 10 * (b / 10) + b % 10 := by omega
  have hm_eq : m = 20 * (10 * (p / 10) * (b / 10) + (p / 10) * (b % 10) + 7 * (b / 10)) + 14 * (b % 10) := by
    calc m = (2 * p) * b := hmul.symm
      _ = (20 * (p / 10) + 14) * (10 * (b / 10) + b % 10) := by rw [← hp_eq, ← hb_eq]
      _ = 20 * (10 * (p / 10) * (b / 10) + (p / 10) * (b % 10) + 7 * (b / 10)) + 14 * (b % 10) := by ring
  have hr : b % 10 < 10 := Nat.mod_lt b (by decide)
  omega

private lemma hasPairEndingIn_six_of_dvd_mod10_three {m q : ℕ}
    (hm0 : m ≠ 0) (hm20 : m % 20 = 16) (hq : q ∣ m) (hq10 : q % 10 = 3) :
    hasPairEndingIn m 6 = true := by
  rw [hasPairEndingIn_iff]
  have h2m : 2 ∣ m := by omega
  have hcop : Nat.Coprime 2 q := by
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr (by omega)
  have h2q : 2 * q ∣ m := hcop.mul_dvd_of_dvd_of_dvd h2m hq
  refine ⟨2 * q, h2q, hm0, by omega, ?_⟩
  have hmul : (2 * q) * (m / (2 * q)) = m := Nat.mul_div_cancel' h2q
  set b := m / (2 * q)
  have hq_eq : 2 * q = 20 * (q / 10) + 6 := by omega
  have hb_eq : b = 10 * (b / 10) + b % 10 := by omega
  have hm_eq : m = 20 * (10 * (q / 10) * (b / 10) + (q / 10) * (b % 10) + 3 * (b / 10)) + 6 * (b % 10) := by
    calc m = (2 * q) * b := hmul.symm
      _ = (20 * (q / 10) + 6) * (10 * (b / 10) + b % 10) := by rw [← hq_eq, ← hb_eq]
      _ = 20 * (10 * (q / 10) * (b / 10) + (q / 10) * (b % 10) + 3 * (b / 10)) + 6 * (b % 10) := by ring
  have hr : b % 10 < 10 := Nat.mod_lt b (by decide)
  omega

private lemma card_filter_Ico_add_period {M : ℕ} (hM : 0 < M) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ x, P x ↔ P (x % M)) (c : ℕ) :
    ((Finset.Ico c (c + M)).filter P).card = ((Finset.range M).filter P).card := by
  refine Finset.card_bij (fun x _ => x % M) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hx ⊢
    exact ⟨Nat.mod_lt x hM, (hP x).mp hx.2⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx hy
    have hx_div : x = M * (x / M) + x % M := (Nat.div_add_mod x M).symm
    have hy_div : y = M * (y / M) + y % M := (Nat.div_add_mod y M).symm
    have hlt1 : M * (x / M) < M * (y / M) + M := by omega
    have hlt2 : M * (y / M) < M * (x / M) + M := by omega
    have hle1 : x / M ≤ y / M := by
      by_contra h
      push Not at h
      have : M * (y / M + 1) ≤ M * (x / M) := Nat.mul_le_mul_left M h
      linarith
    have hle2 : y / M ≤ x / M := by
      by_contra h
      push Not at h
      have : M * (x / M + 1) ≤ M * (y / M) := Nat.mul_le_mul_left M h
      linarith
    have heq : x / M = y / M := le_antisymm hle1 hle2
    rw [heq] at hx_div
    omega
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    set t := (r + M - c % M) % M
    have ht : t < M := Nat.mod_lt _ hM
    have h1 : c % M < M := Nat.mod_lt c hM
    have hmod : (c + t) % M = r := by
      rw [Nat.add_mod]
      dsimp only [t]
      rw [Nat.mod_mod, Nat.add_mod_mod, show c % M + (r + M - c % M) = r + M by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hr.1]
    refine ⟨c + t, ?_, hmod⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Nat.le_add_right c t, by omega⟩, (hP (c + t)).mpr (hmod ▸ hr.2)⟩

private lemma card_filter_Ico_add_mul {M : ℕ} (hM : 0 < M) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ x, P x ↔ P (x % M)) (a q : ℕ) :
    ((Finset.Ico a (a + q * M)).filter P).card = q * ((Finset.range M).filter P).card := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Finset.Ico a (a + (q + 1) * M) =
        Finset.Ico a (a + q * M) ∪ Finset.Ico (a + q * M) (a + q * M + M) := by
      have hle1 : a ≤ a + q * M := Nat.le_add_right a (q * M)
      have hle2 : a + q * M ≤ a + (q + 1) * M := by
        rw [Nat.add_mul, one_mul, ← Nat.add_assoc]
        exact Nat.le_add_right _ M
      rw [show a + q * M + M = a + (q + 1) * M by ring]
      exact (Finset.Ico_union_Ico_eq_Ico hle1 hle2).symm
    have hdisj : Disjoint (Finset.Ico a (a + q * M))
        (Finset.Ico (a + q * M) (a + q * M + M)) :=
      Finset.Ico_disjoint_Ico_consecutive a (a + q * M) (a + q * M + M)
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      ih, card_filter_Ico_add_period hM P hP (a + q * M)]
    ring

private lemma card_filter_Ico_le {M : ℕ} (hM : 0 < M) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ x, P x ↔ P (x % M)) {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ico a b).filter P).card ≤
      ((b - a) / M + 1) * ((Finset.range M).filter P).card := by
  have hb : b ≤ a + ((b - a) / M + 1) * M := by
    have hdiv : M * ((b - a) / M) + (b - a) % M = b - a := Nat.div_add_mod (b - a) M
    have hmod : (b - a) % M < M := Nat.mod_lt (b - a) hM
    rw [Nat.add_mul, one_mul, mul_comm ((b - a) / M) M]
    omega
  calc ((Finset.Ico a b).filter P).card
      ≤ ((Finset.Ico a (a + ((b - a) / M + 1) * M)).filter P).card :=
        Finset.card_le_card (Finset.filter_subset_filter P (Finset.Ico_subset_Ico_right hb))
    _ = ((b - a) / M + 1) * ((Finset.range M).filter P).card :=
        card_filter_Ico_add_mul hM P hP a ((b - a) / M + 1)

private lemma card_filter_range_sieve (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime ∧ Nat.Coprime p 20) :
    ((Finset.range (20 * ∏ p ∈ F, p)).filter (fun x => x % 20 = 16 ∧ ∀ p ∈ F, ¬ p ∣ x)).card =
      ∏ p ∈ F, (p - 1) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
      and_true]
    decide
  | @insert p F hp ih =>
    have hF' : ∀ q ∈ F, q.Prime ∧ Nat.Coprime q 20 := fun q hq => hF q (Finset.mem_insert_of_mem hq)
    have hp' : p.Prime ∧ Nat.Coprime p 20 := hF p (Finset.mem_insert_self p F)
    set M := 20 * ∏ q ∈ F, q
    have hM_pos : 0 < M := by
      refine Nat.mul_pos (by decide) (Finset.prod_pos fun q hq => (hF' q hq).1.pos)
    have hp_pos : 0 < p := hp'.1.pos
    have hcop : Nat.Coprime M p := by
      refine Nat.Coprime.mul_left hp'.2.symm ?_
      refine Nat.Coprime.prod_left fun q hq => ?_
      have hqp : q ≠ p := fun h => hp (h ▸ hq)
      exact (Nat.coprime_primes (hF' q hq).1 hp'.1).mpr hqp
    have hprod_eq : 20 * ∏ q ∈ insert p F, q = M * p := by
      rw [Finset.prod_insert hp]
      dsimp [M]
      ring
    rw [hprod_eq, Finset.prod_insert hp, mul_comm (p - 1), ← ih hF']
    have hcard_p : ((Finset.range p).filter (· ≠ 0)).card = p - 1 := by
      have hsub : (Finset.range p).filter (· ≠ 0) = (Finset.range p).erase 0 := by
        ext x
        simp [and_comm]
      rw [hsub, Finset.card_erase_of_mem (Finset.mem_range.mpr hp_pos), Finset.card_range]
    rw [← hcard_p, ← Finset.card_product]
    refine Finset.card_bij (fun x _ => (x % M, x % p)) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hx ⊢
      have h20M : 20 ∣ M := dvd_mul_right 20 _
      refine ⟨⟨Nat.mod_lt x hM_pos, ?_, ?_⟩, Nat.mod_lt x hp_pos, ?_⟩
      · rw [Nat.mod_mod_of_dvd x h20M]
        exact hx.2.1
      · intro q hq hdvd
        have hqM : q ∣ M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hq) 20
        exact hx.2.2 q (Finset.mem_insert_of_mem hq) ((Nat.dvd_mod_iff hqM).mp hdvd)
      · intro h0
        exact hx.2.2 p (Finset.mem_insert_self p F) (Nat.dvd_of_mod_eq_zero h0)
    · intro x hx y hy hxy
      simp only [Finset.mem_filter, Finset.mem_range] at hx hy
      have h1 : x ≡ y [MOD M] := congrArg Prod.fst hxy
      have h2 : x ≡ y [MOD p] := congrArg Prod.snd hxy
      have hmp : x ≡ y [MOD M * p] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
      change x % (M * p) = y % (M * p) at hmp
      rw [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at hmp
      exact hmp
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hab
      rcases hab with ⟨⟨haM, ha20, haF⟩, hbp, hb0⟩
      set k := (Nat.chineseRemainder hcop a b).val
      have hk1 : k ≡ a [MOD M] := (Nat.chineseRemainder hcop a b).prop.1
      have hk2 : k ≡ b [MOD p] := (Nat.chineseRemainder hcop a b).prop.2
      set c := k % (M * p)
      have hcM : c % M = a := by
        rw [Nat.mod_mod_of_dvd k (dvd_mul_right M p)]
        exact Eq.trans hk1 (Nat.mod_eq_of_lt haM)
      have hcp : c % p = b := by
        rw [Nat.mod_mod_of_dvd k (dvd_mul_left p M)]
        exact Eq.trans hk2 (Nat.mod_eq_of_lt hbp)
      refine ⟨c, ?_, Prod.ext hcM hcp⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt k (Nat.mul_pos hM_pos hp_pos), ?_, ?_⟩
      · rw [← Nat.mod_mod_of_dvd c (dvd_mul_right 20 _), hcM]
        exact ha20
      · intro q hq hdvd
        rcases Finset.mem_insert.mp hq with rfl | hqF
        · exact hb0 (hcp ▸ Nat.mod_eq_zero_of_dvd hdvd)
        · have hqM : q ∣ M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hqF) 20
          exact haF q hqF (hcM ▸ (Nat.dvd_mod_iff hqM).mpr hdvd)

private lemma not_summable_primes_modEq {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ¬ Summable (fun n : ℕ => if n.Prime ∧ (n : ZMod q) = a then (n : ℝ)⁻¹ else 0) := by
  intro hf
  let f : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod q) = a then (n : ℝ)⁻¹ else 0
  let g : ℕ → ℝ := fun n => if n.Prime then ArithmeticFunction.vonMangoldt.residueClass a n else 0
  let hnp : ℕ → ℝ := fun n =>
    (if n.Prime then 0 else ArithmeticFunction.vonMangoldt.residueClass a n) / (n : ℝ)
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => by
    dsimp [f]
    split_ifs <;> positivity
  have hhnp : Summable hnp := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div a
  obtain ⟨C, hC⟩ := ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound ha
  have hq : 0 < (q.totient : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q))
  obtain ⟨s, hs⟩ := Metric.tendsto_atTop.mp hf.hasSum ((q.totient : ℝ)⁻¹ / 2) (half_pos hq)
  have hdist : dist (∑ n ∈ s, f n) (∑' n, f n) < (q.totient : ℝ)⁻¹ / 2 := hs s le_rfl
  let f₁ : ℕ → ℝ := fun n => if n ∈ s then f n else 0
  let f₂ : ℕ → ℝ := fun n => if n ∈ s then 0 else f n
  let g₁ : ℕ → ℝ := fun n => if n ∈ s then g n else 0
  have hf₁ : Summable f₁ := summable_of_ne_finset_zero (s := s) fun n hn => if_neg hn
  have hf₂ : Summable f₂ := hf.of_nonneg_of_le
    (fun n => by
      dsimp only [f₂]
      by_cases h : n ∈ s
      · rw [if_pos h]
      · rw [if_neg h]; exact hf_nonneg n)
    (fun n => by
      dsimp only [f₂]
      by_cases h : n ∈ s
      · rw [if_pos h]; exact hf_nonneg n
      · rw [if_neg h])
  have hg₁ : Summable g₁ := summable_of_ne_finset_zero (s := s) fun n hn => if_neg hn
  have hf₁_sum : ∑' n, f₁ n = ∑ n ∈ s, f n := by
    rw [tsum_eq_sum (s := s) (fun n hn => if_neg hn)]
    exact Finset.sum_congr rfl fun n hn => if_pos hn
  have hf_split : (∑' n, f₁ n) + (∑' n, f₂ n) = ∑' n, f n := by
    rw [← hf₁.tsum_add hf₂]
    refine tsum_congr fun n => ?_
    dsimp [f₁, f₂]
    split_ifs <;> ring
  set T := ∑' n, f₂ n
  have hT_lt : T < (q.totient : ℝ)⁻¹ / 2 := by
    have h1 : T = (∑' n, f n) - ∑ n ∈ s, f n := by linarith [hf₁_sum, hf_split]
    rw [Real.dist_eq] at hdist
    have h2 : (∑' n, f n) - ∑ n ∈ s, f n ≤ |(∑ n ∈ s, f n) - ∑' n, f n| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith
  set K := C + (∑' n, hnp n) + (∑' n, g₁ n)
  have hbound : ∀ x ∈ Set.Ioc (1 : ℝ) 2, (q.totient : ℝ)⁻¹ - T ≤ K * (x - 1) := by
    intro x hx
    have hx1 : 0 < x - 1 := sub_pos.mpr hx.1
    have hsumm : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ x) :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one a).trans_lt <|
          by exact_mod_cast hx.1
    have hpt : ∀ n : ℕ,
        ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ x ≤
          hnp n + g₁ n + (x - 1)⁻¹ * f₂ n := by
      intro n
      by_cases hnp_prime : n.Prime
      · have hhnp0 : hnp n = 0 := by simp [hnp, hnp_prime]
        rw [hhnp0, zero_add]
        by_cases hns : n ∈ s
        · have hf₂0 : f₂ n = 0 := if_pos hns
          have hg₁eq : g₁ n = ArithmeticFunction.vonMangoldt.residueClass a n := by
            simp [g₁, g, hns, hnp_prime]
          rw [hf₂0, mul_zero, add_zero, hg₁eq]
          have h1le : (1 : ℝ) ≤ (n : ℝ) ^ x :=
            Real.one_le_rpow (by exact_mod_cast hnp_prime.one_le) (by linarith [hx.1])
          exact div_le_self (ArithmeticFunction.vonMangoldt.residueClass_nonneg a n) h1le
        · have hg₁0 : g₁ n = 0 := if_neg hns
          have hf₂eq : f₂ n = f n := if_neg hns
          rw [hg₁0, zero_add, hf₂eq]
          by_cases hmod : (n : ZMod q) = a
          · have hres : ArithmeticFunction.vonMangoldt.residueClass a n = Real.log n := by
              simp [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_of_mem, hmod,
                ArithmeticFunction.vonMangoldt_apply_prime hnp_prime]
            have hfeq : f n = (n : ℝ)⁻¹ := if_pos ⟨hnp_prime, hmod⟩
            rw [hres, hfeq]
            have hn_pos : (0 : ℝ) < n := by exact_mod_cast hnp_prime.pos
            have hlog : (x - 1) * Real.log n ≤ (n : ℝ) ^ (x - 1) := by
              calc (x - 1) * Real.log n ≤ (x - 1) * Real.log n + 1 := by linarith
                _ ≤ Real.exp ((x - 1) * Real.log n) := Real.add_one_le_exp _
                _ = Real.exp (Real.log n * (x - 1)) := by ring_nf
                _ = (n : ℝ) ^ (x - 1) := (Real.rpow_def_of_pos hn_pos _).symm
            have hpow : (n : ℝ) ^ x = (n : ℝ) * (n : ℝ) ^ (x - 1) := by
              conv_lhs => rw [show x = 1 + (x - 1) by ring]
              rw [Real.rpow_add hn_pos, Real.rpow_one]
            rw [hpow, div_le_iff₀ (mul_pos hn_pos (Real.rpow_pos_of_pos hn_pos _))]
            have hmul : (x - 1)⁻¹ * (n : ℝ)⁻¹ * ((n : ℝ) * (n : ℝ) ^ (x - 1)) =
                (x - 1)⁻¹ * (n : ℝ) ^ (x - 1) := by
              field_simp [hn_pos.ne']
            rw [hmul, le_inv_mul_iff₀ hx1]
            exact hlog
          · have hres : ArithmeticFunction.vonMangoldt.residueClass a n = 0 := by
              simp [ArithmeticFunction.vonMangoldt.residueClass, hmod]
            have hfeq : f n = 0 := if_neg (fun h => hmod h.2)
            rw [hres, hfeq, zero_div, mul_zero]
      · have hg₁0 : g₁ n = 0 := by simp [g₁, g, hnp_prime]
        have hf₂0 : f₂ n = 0 := by simp [f₂, f, hnp_prime]
        have hhnpeq : hnp n = ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) := by
          simp [hnp, hnp_prime]
        rw [hg₁0, hf₂0, add_zero, mul_zero, add_zero, hhnpeq]
        rcases n.eq_zero_or_pos with rfl | hn_pos
        · simp
        · refine div_le_div_of_nonneg_left
            (ArithmeticFunction.vonMangoldt.residueClass_nonneg a n) (by exact_mod_cast hn_pos) ?_
          conv_lhs => rw [← Real.rpow_one (n : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn_pos) hx.1.le
    have htsum_le :
        ∑' n, ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ x ≤
          (∑' n, hnp n) + (∑' n, g₁ n) + (x - 1)⁻¹ * T := by
      have h1 := Summable.tsum_le_tsum hpt hsumm ((hhnp.add hg₁).add (hf₂.mul_left _))
      rw [Summable.tsum_add (hhnp.add hg₁) (hf₂.mul_left _), Summable.tsum_add hhnp hg₁,
        tsum_mul_left] at h1
      exact h1
    have hcomb := (hC hx).trans htsum_le
    have hmul := mul_le_mul_of_nonneg_right hcomb hx1.le
    have hlhs : ((q.totient : ℝ)⁻¹ / (x - 1) - C) * (x - 1) = (q.totient : ℝ)⁻¹ - C * (x - 1) := by
      rw [sub_mul, div_mul_cancel₀ _ hx1.ne']
    have hrhs : ((∑' n, hnp n) + (∑' n, g₁ n) + (x - 1)⁻¹ * T) * (x - 1) =
        ((∑' n, hnp n) + (∑' n, g₁ n)) * (x - 1) + T := by
      rw [add_mul, mul_right_comm, inv_mul_cancel₀ hx1.ne', one_mul]
    rw [hlhs, hrhs] at hmul
    dsimp [K]
    linarith
  set δ := (q.totient : ℝ)⁻¹ - T
  have hδ : 0 < δ := by linarith
  have hden : 0 < 2 * (|K| + 1) := by positivity
  set t := min 1 (δ / (2 * (|K| + 1)))
  have ht_pos : 0 < t := lt_min one_pos (div_pos hδ hden)
  have ht_le1 : t ≤ 1 := min_le_left _ _
  have ht_le2 : t ≤ δ / (2 * (|K| + 1)) := min_le_right _ _
  have hx_mem : 1 + t ∈ Set.Ioc (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hbd := hbound (1 + t) hx_mem
  rw [add_sub_cancel_left] at hbd
  have hK_le : K * t ≤ δ / 2 := by
    calc K * t ≤ |K| * t := mul_le_mul_of_nonneg_right (le_abs_self K) ht_pos.le
      _ ≤ (|K| + 1) * t := mul_le_mul_of_nonneg_right (by linarith) ht_pos.le
      _ ≤ (|K| + 1) * (δ / (2 * (|K| + 1))) := mul_le_mul_of_nonneg_left ht_le2 (by positivity)
      _ = δ / 2 := by
        have hpos : (|K| + 1) ≠ 0 := by positivity
        field_simp [hpos]
  linarith

private lemma exists_finset_primes_prod_lt {r : ℕ} (hr : r = 3 ∨ r = 7) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ p % 10 = r) ∧
      (∏ p ∈ F, (1 - (p : ℝ)⁻¹)) < ε := by
  have hu : IsUnit (r : ZMod 10) := by
    rcases hr with rfl | rfl
    · exact isUnit_iff_exists_inv.mpr ⟨7, by decide⟩
    · exact isUnit_iff_exists_inv.mpr ⟨3, by decide⟩
  have hns := not_summable_primes_modEq (q := 10) hu
  let f : ℕ → ℝ := fun n => if n.Prime ∧ n % 10 = r then (n : ℝ)⁻¹ else 0
  have hfeq : f = fun n : ℕ => if n.Prime ∧ (n : ZMod 10) = (r : ZMod 10) then (n : ℝ)⁻¹ else 0 := by
    funext n
    have hr10 : r < 10 := by omega
    have hiff : n % 10 = r ↔ (n : ZMod 10) = (r : ZMod 10) := by
      rw [ZMod.natCast_eq_natCast_iff']
      rw [Nat.mod_eq_of_lt hr10]
    simp [f, hiff]
  have hns' : ¬ Summable f := hfeq ▸ hns
  have hgt : ∃ s : Finset ℕ, -Real.log ε < ∑ n ∈ s, f n := by
    by_contra h
    push Not at h
    exact hns' (summable_of_sum_le (fun n => by dsimp [f]; split_ifs <;> positivity) h)
  obtain ⟨s, hs⟩ := hgt
  refine ⟨s.filter (fun p => p.Prime ∧ p % 10 = r), fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  set F := s.filter (fun p => p.Prime ∧ p % 10 = r)
  have hsum : ∑ p ∈ F, (p : ℝ)⁻¹ = ∑ n ∈ s, f n := by
    simp [F, f, Finset.sum_filter]
  have hprod_le : ∏ p ∈ F, (1 - (p : ℝ)⁻¹) ≤ Real.exp (-(∑ p ∈ F, (p : ℝ)⁻¹)) := by
    calc ∏ p ∈ F, (1 - (p : ℝ)⁻¹)
        ≤ ∏ p ∈ F, Real.exp (-(p : ℝ)⁻¹) := by
          refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
          · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le
            have hinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
            linarith
          · linarith [Real.add_one_le_exp (-(p : ℝ)⁻¹)]
      _ = Real.exp (∑ p ∈ F, -(p : ℝ)⁻¹) := (Real.exp_sum F _).symm
      _ = Real.exp (-(∑ p ∈ F, (p : ℝ)⁻¹)) := by rw [Finset.sum_neg_distrib]
  calc ∏ p ∈ F, (1 - (p : ℝ)⁻¹)
      ≤ Real.exp (-(∑ p ∈ F, (p : ℝ)⁻¹)) := hprod_le
    _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
    _ = ε := Real.exp_log hε

private lemma bad_count_bound {r : ℕ} (hr : r = 3 ∨ r = 7) (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime ∧ p % 10 = r) (n : ℕ) (hn : 3 ≤ n) :
    (((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
        (fun m => m % 20 = 16 ∧ ∀ p ∈ F, ¬ p ∣ m)).card : ℝ) ≤
      (45 * 10 ^ (n - 3) : ℝ) * (∏ p ∈ F, (1 - (p : ℝ)⁻¹)) + (∏ p ∈ F, (p - 1) : ℕ) := by
  classical
  set P := ∏ p ∈ F, p
  set M := 20 * P
  have hFcop : ∀ p ∈ F, p.Prime ∧ Nat.Coprime p 20 := by
    intro p hp
    have ⟨hpr, hmod⟩ := hF p hp
    refine ⟨hpr, hpr.coprime_iff_not_dvd.mpr fun h => ?_⟩
    have hle := Nat.le_of_dvd (by decide) h
    have hdiv := Nat.mod_eq_zero_of_dvd h
    have hcases : p = 3 ∨ p = 7 ∨ p = 13 ∨ p = 17 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;> omega
  have hP_pos : 0 < P := Finset.prod_pos fun p hp => (hF p hp).1.pos
  have hM_pos : 0 < M := Nat.mul_pos (by decide) hP_pos
  have hper : ∀ x, (x % 20 = 16 ∧ ∀ p ∈ F, ¬ p ∣ x) ↔
      ((x % M) % 20 = 16 ∧ ∀ p ∈ F, ¬ p ∣ x % M) := by
    intro x
    have h20 : (x % M) % 20 = x % 20 := Nat.mod_mod_of_dvd x (dvd_mul_right 20 P)
    rw [h20]
    refine and_congr_right fun _ => forall₂_congr fun p hp => ?_
    have hpM : p ∣ M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) 20
    exact not_congr (Nat.dvd_mod_iff hpM).symm
  have hab : 10 ^ (n - 1) ≤ 10 ^ n := Nat.pow_le_pow_right (by decide) (Nat.sub_le n 1)
  have hle_nat := card_filter_Ico_le hM_pos (fun m => m % 20 = 16 ∧ ∀ p ∈ F, ¬ p ∣ m) hper hab
  rw [card_filter_range_sieve F hFcop] at hle_nat
  have hdiff : 10 ^ n - 10 ^ (n - 1) = 20 * (45 * 10 ^ (n - 3)) := by
    have h1 : 10 ^ (n - 1) = 100 * 10 ^ (n - 3) := by
      rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
      ring
    have h2 : 10 ^ n = 1000 * 10 ^ (n - 3) := by
      conv_lhs => rw [show n = (n - 3) + 3 by omega]
      rw [pow_add]
      ring
    omega
  rw [hdiff] at hle_nat
  set R := ∏ p ∈ F, (p - 1)
  have hcast : (((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
      (fun m => m % 20 = 16 ∧ ∀ p ∈ F, ¬ p ∣ m)).card : ℝ) ≤
      ((((20 * (45 * 10 ^ (n - 3))) / M : ℕ) : ℝ) + 1) * (R : ℝ) := by
    exact_mod_cast hle_nat
  have hdiv_le : (((20 * (45 * 10 ^ (n - 3))) / M : ℕ) : ℝ) ≤
      ((20 * (45 * 10 ^ (n - 3)) : ℕ) : ℝ) / (M : ℝ) := Nat.cast_div_le
  have hRP : (R : ℝ) / (P : ℝ) = ∏ p ∈ F, (1 - (p : ℝ)⁻¹) := by
    dsimp [R, P]
    push_cast
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : 1 ≤ p := (hF p hp).1.one_le
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hF p hp).1.ne_zero
    rw [Nat.cast_sub hp1, Nat.cast_one, sub_div, div_self hp0, one_div]
  have hP_ne : (P : ℝ) ≠ 0 := by exact_mod_cast hP_pos.ne'
  have hcalc : (((20 * (45 * 10 ^ (n - 3)) : ℕ) : ℝ) / (M : ℝ) + 1) * (R : ℝ) =
      (45 * 10 ^ (n - 3) : ℝ) * (∏ p ∈ F, (1 - (p : ℝ)⁻¹)) + (R : ℝ) := by
    rw [← hRP]
    dsimp [M]
    push_cast
    field_simp [hP_ne]
  calc (((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
        (fun m => m % 20 = 16 ∧ ∀ p ∈ F, ¬ p ∣ m)).card : ℝ)
      ≤ ((((20 * (45 * 10 ^ (n - 3))) / M : ℕ) : ℝ) + 1) * (R : ℝ) := hcast
    _ ≤ (((20 * (45 * 10 ^ (n - 3)) : ℕ) : ℝ) / (M : ℝ) + 1) * (R : ℝ) := by
        gcongr
    _ = (45 * 10 ^ (n - 3) : ℝ) * (∏ p ∈ F, (1 - (p : ℝ)⁻¹)) + (R : ℝ) := hcalc

private lemma card_mod20_eq (n : ℕ) (hn : 3 ≤ n) :
    ((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (fun m => m % 20 = 16)).card =
      45 * 10 ^ (n - 3) := by
  have h1 : 10 ^ (n - 1) = 100 * 10 ^ (n - 3) := by
    rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
    ring
  have h2 : 10 ^ n = 10 ^ (n - 1) + (45 * 10 ^ (n - 3)) * 20 := by
    have h3 : 10 ^ n = 1000 * 10 ^ (n - 3) := by
      conv_lhs => rw [show n = (n - 3) + 3 by omega]
      rw [pow_add]
      ring
    omega
  rw [h2, card_filter_Ico_add_mul (by decide : 0 < 20) (fun m => m % 20 = 16)
    (fun x => by simp)]
  have h20 : ((Finset.range 20).filter (fun m => m % 20 = 16)).card = 1 := by decide
  rw [h20, mul_one]

private lemma tendsto_term_div_main :
    Tendsto (fun n : ℕ => (term n : ℝ) / (45 * 10 ^ (n - 3) : ℝ)) atTop (nhds 1) := by
  classical
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨F₃, hF₃_mem, hF₃_prod⟩ := exists_finset_primes_prod_lt (Or.inl rfl) (show (0 : ℝ) < δ / 3 by linarith)
  obtain ⟨F₇, hF₇_mem, hF₇_prod⟩ := exists_finset_primes_prod_lt (Or.inr rfl) (show (0 : ℝ) < δ / 3 by linarith)
  set R₃ := ∏ p ∈ F₃, (p - 1)
  set R₇ := ∏ p ∈ F₇, (p - 1)
  set N := 3 + Nat.ceil (3 * ((R₃ : ℝ) + (R₇ : ℝ) + 1) / δ) + 1
  refine ⟨N, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := by omega
  set A : ℝ := 45 * 10 ^ (n - 3)
  have hA_pos : 0 < A := by positivity
  set S_all := (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (fun m => m % 20 = 16)
  set S_good := (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
    (fun m => hasPairEndingIn m 4 = true ∧ hasPairEndingIn m 6 = true)
  set S_bad3 := (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
    (fun m => m % 20 = 16 ∧ ∀ p ∈ F₃, ¬ p ∣ m)
  set S_bad7 := (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
    (fun m => m % 20 = 16 ∧ ∀ p ∈ F₇, ¬ p ∣ m)
  have hAll_card : S_all.card = 45 * 10 ^ (n - 3) := card_mod20_eq n hn3
  have hupper_nat : term n ≤ 45 * 10 ^ (n - 3) := by
    rw [← hAll_card]
    refine Finset.card_le_card fun m hm => ?_
    simp only [S_all, Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hasPairEndingIn_four_imp_mod20 hm.2.1⟩
  have hupper : (term n : ℝ) ≤ A := by
    dsimp only [A]
    exact_mod_cast hupper_nat
  have hcover : S_all ⊆ S_good ∪ S_bad3 ∪ S_bad7 := by
    intro m hm
    simp only [S_all, Finset.mem_filter, Finset.mem_Ico] at hm
    have hm0 : m ≠ 0 := by
      have : 1 ≤ 10 ^ (n - 1) := Nat.one_le_pow _ _ (by decide)
      omega
    by_cases h3 : ∀ p ∈ F₃, ¬ p ∣ m
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hm.1, hm.2, h3⟩))
    · by_cases h7 : ∀ p ∈ F₇, ¬ p ∣ m
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hm.1, hm.2, h7⟩)
      · push Not at h3 h7
        obtain ⟨q, hqF, hqm⟩ := h3
        obtain ⟨p, hpF, hpm⟩ := h7
        have h4 := hasPairEndingIn_four_of_dvd_mod10_seven hm0 hm.2 hpm (hF₇_mem p hpF).2
        have h6 := hasPairEndingIn_six_of_dvd_mod10_three hm0 hm.2 hqm (hF₃_mem q hqF).2
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hm.1, h4, h6⟩))
  have hlower_nat : 45 * 10 ^ (n - 3) ≤ term n + S_bad3.card + S_bad7.card := by
    calc 45 * 10 ^ (n - 3) = S_all.card := hAll_card.symm
      _ ≤ (S_good ∪ S_bad3 ∪ S_bad7).card := Finset.card_le_card hcover
      _ ≤ (S_good ∪ S_bad3).card + S_bad7.card := Finset.card_union_le _ _
      _ ≤ S_good.card + S_bad3.card + S_bad7.card := by
          gcongr
          exact Finset.card_union_le _ _
  have hlower_real : A ≤ (term n : ℝ) + (S_bad3.card : ℝ) + (S_bad7.card : ℝ) := by
    dsimp only [A]
    exact_mod_cast hlower_nat
  have hbad3 := bad_count_bound (Or.inl rfl) F₃ hF₃_mem n hn3
  have hbad7 := bad_count_bound (Or.inr rfl) F₇ hF₇_mem n hn3
  have hbad3' : (S_bad3.card : ℝ) ≤ A * (δ / 3) + (R₃ : ℝ) := by
    calc (S_bad3.card : ℝ) ≤ A * (∏ p ∈ F₃, (1 - (p : ℝ)⁻¹)) + (R₃ : ℝ) := hbad3
      _ ≤ A * (δ / 3) + (R₃ : ℝ) := by gcongr
  have hbad7' : (S_bad7.card : ℝ) ≤ A * (δ / 3) + (R₇ : ℝ) := by
    calc (S_bad7.card : ℝ) ≤ A * (∏ p ∈ F₇, (1 - (p : ℝ)⁻¹)) + (R₇ : ℝ) := hbad7
      _ ≤ A * (δ / 3) + (R₇ : ℝ) := by gcongr
  have hR_lt : ((R₃ : ℝ) + (R₇ : ℝ)) / A < δ / 3 := by
    have hpow_gt : ((n - 3 : ℕ) : ℝ) < (10 ^ (n - 3) : ℝ) := by
      exact_mod_cast Nat.lt_pow_self (by decide : 1 < 10)
    have hceil : 3 * ((R₃ : ℝ) + (R₇ : ℝ) + 1) / δ ≤ ((n - 3 : ℕ) : ℝ) := by
      have h1 : Nat.ceil (3 * ((R₃ : ℝ) + (R₇ : ℝ) + 1) / δ) ≤ n - 3 := by omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have hA_gt : 3 * ((R₃ : ℝ) + (R₇ : ℝ) + 1) / δ < A := by
      have hleA : (10 ^ (n - 3) : ℝ) ≤ A := by
        dsimp [A]
        have : (0 : ℝ) ≤ 10 ^ (n - 3) := by positivity
        linarith
      linarith
    rw [div_lt_iff₀ hA_pos]
    rw [div_lt_iff₀ hδ] at hA_gt
    linarith
  have hratio_le : (term n : ℝ) / A ≤ 1 := (div_le_one hA_pos).mpr hupper
  have hratio_ge : 1 - (term n : ℝ) / A ≤ 2 * (δ / 3) + ((R₃ : ℝ) + (R₇ : ℝ)) / A := by
    have h1 : A - (term n : ℝ) ≤ A * (2 * (δ / 3)) + ((R₃ : ℝ) + (R₇ : ℝ)) := by linarith
    have h2 := div_le_div_of_nonneg_right h1 hA_pos.le
    rw [sub_div, div_self hA_pos.ne', add_div, mul_div_cancel_left₀ _ hA_pos.ne'] at h2
    exact h2
  rw [Real.dist_eq, abs_of_nonpos (by linarith : (term n : ℝ) / A - 1 ≤ 0)]
  linarith

end OMA_A347748_TryA

theorem OMA.solution : type_of% @OMA.S_oeis_a347748.main := by
  open OMA.S_oeis_a347748 Filter Topology in
  have h1 : Tendsto (fun n : ℕ => (term n : ℝ) / (45 * 10 ^ (n - 3) : ℝ)) atTop (nhds 1) :=
    OMA_A347748_TryA.tendsto_term_div_main
  have hsub : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b + 1, fun a ha => by omega⟩
  have h2 : Tendsto (fun n : ℕ => (term (n - 1) : ℝ) / (45 * 10 ^ (n - 1 - 3) : ℝ)) atTop (nhds 1) :=
    h1.comp hsub
  have hrat : Tendsto (fun n : ℕ =>
      ((term n : ℝ) / (45 * 10 ^ (n - 3) : ℝ)) /
        ((term (n - 1) : ℝ) / (45 * 10 ^ (n - 1 - 3) : ℝ)) * 10) atTop (nhds (1 / 1 * 10)) :=
    (h1.div h2 one_ne_zero).mul_const 10
  rw [div_one, one_mul] at hrat
  have hpos : ∀ᶠ n in atTop, (0 : ℝ) < (term (n - 1) : ℝ) / (45 * 10 ^ (n - 1 - 3) : ℝ) :=
    h2.eventually (lt_mem_nhds zero_lt_one)
  refine hrat.congr' ?_
  filter_upwards [hpos, eventually_ge_atTop 4] with n hpn hn4
  have hA1 : (45 * 10 ^ (n - 1 - 3) : ℝ) ≠ 0 := by positivity
  have hA2 : (45 * 10 ^ (n - 3) : ℝ) = (45 * 10 ^ (n - 1 - 3) : ℝ) * 10 := by
    have : n - 3 = (n - 1 - 3) + 1 := by omega
    rw [this, pow_succ]
    ring
  have htn : (term (n - 1) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hpn
    exact lt_irrefl 0 hpn
  rw [hA2]
  field_simp [hA1, htn]
