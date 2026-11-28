import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R2
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R2.H1
-- Credit: @mijuny

namespace Test36944H1

open Finset Real

theorem count_bound (N q s : ℕ) (hN : 0 < N) (hsN : s ≤ N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (s : ℝ)) :
    N * (2 * N - s) ^ q < (2 * N) ^ q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsr : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hMpos : (0 : ℝ) < 2 * N := by positivity
  set a : ℝ := (s : ℝ) / (2 * N) with ha
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hMpos]
    linarith
  have hcast : (((2 * N - s : ℕ)) : ℝ) = (2 * N) * (1 - a) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [ha]
    field_simp
  have hexp : (1 - a) ^ q ≤ Real.exp (-(q * a)) := by
    calc (1 - a) ^ q ≤ Real.exp (-a) ^ q := by
          apply pow_le_pow_left₀ (by linarith)
          linarith [Real.add_one_le_exp (-a)]
      _ = Real.exp (-(q * a)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  have hlog : Real.log N < q * a := by
    rw [ha, mul_div_assoc', lt_div_iff₀ hMpos]
    linarith
  have hlt : Real.exp (-(q * a)) < 1 / N := by
    rw [one_div, ← Real.exp_log hNr, ← Real.exp_neg, Real.exp_lt_exp]
    linarith
  have hkey : (N : ℝ) * (1 - a) ^ q < 1 := by
    calc (N : ℝ) * (1 - a) ^ q ≤ N * Real.exp (-(q * a)) :=
          mul_le_mul_of_nonneg_left hexp hNr.le
      _ < N * (1 / N) := mul_lt_mul_of_pos_left hlt hNr
      _ = 1 := by field_simp
  have hreal : ((N * (2 * N - s) ^ q : ℕ) : ℝ) < (((2 * N) ^ q : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, hcast, mul_pow, Nat.cast_pow]
    have hpow : (0 : ℝ) < (2 * N) ^ q := by positivity
    have e2 : (((2 * N : ℕ)) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
    rw [e2]
    calc (N : ℝ) * ((2 * N) ^ q * (1 - a) ^ q) = (2 * N) ^ q * ((N : ℝ) * (1 - a) ^ q) := by ring
      _ < (2 * N) ^ q * 1 := mul_lt_mul_of_pos_left hkey hpow
      _ = (2 * N) ^ q := mul_one _
  exact_mod_cast hreal

theorem shift_cover_of_gt (N q : ℕ) (S : Finset ℕ) (hN : 0 < N)
    (hS : S ⊆ Finset.Icc 1 N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ)) :
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Finset.Icc 1 N,
      ∃ t : Fin q, ∃ b ∈ S, x + N = shifts t + b := by
  have hsN : S.card ≤ N := by
    have := card_le_card hS
    simpa using this
  let BadShift : ℕ → Finset (Fin (2 * N)) := fun x =>
    univ.filter (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
  have hBad : ∀ x ∈ Icc 1 N, (BadShift x).card ≤ 2 * N - S.card := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_Icc.mp hx
    let Good := univ.filter (fun r : Fin (2 * N) => ¬ ∀ b ∈ S, r.val + b ≠ x + N)
    have hGood : S.card ≤ Good.card := by
      apply card_le_card_of_injOn
        (fun b => (⟨(x + N - b) % (2 * N), Nat.mod_lt _ (by omega)⟩ : Fin (2 * N)))
      · intro b hb
        rw [mem_coe] at hb
        have hb' := mem_Icc.mp (hS hb)
        rw [mem_coe, mem_filter]
        refine ⟨mem_univ _, ?_⟩
        intro hall
        apply hall b hb
        simp only
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · intro b hb b' hb' heq
        rw [mem_coe] at hb hb'
        have h1 := mem_Icc.mp (hS hb)
        have h2 := mem_Icc.mp (hS hb')
        have hv := congrArg Fin.val heq
        simp only at hv
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
        omega
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * N))))
      (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
    rw [card_univ, Fintype.card_fin] at hsum
    change (BadShift x).card + Good.card = 2 * N at hsum
    omega
  let Bad : ℕ → Finset (Fin q → Fin (2 * N)) := fun x => Fintype.piFinset (fun _ => BadShift x)
  let U := (Icc 1 N).biUnion Bad
  have hU : U.card < (univ : Finset (Fin q → Fin (2 * N))).card := by
    calc U.card ≤ ∑ x ∈ Icc 1 N, (Bad x).card := card_biUnion_le
      _ ≤ ∑ x ∈ Icc 1 N, (2 * N - S.card) ^ q := by
          apply sum_le_sum
          intro x hx
          change (Fintype.piFinset fun _ : Fin q => BadShift x).card ≤ _
          rw [Fintype.card_piFinset_const]
          exact Nat.pow_le_pow_left (hBad x hx) q
      _ = N * (2 * N - S.card) ^ q := by
          rw [sum_const, Nat.card_Icc, smul_eq_mul]
          simp
      _ < (2 * N) ^ q := count_bound N q S.card hN hsN h
      _ = (univ : Finset (Fin q → Fin (2 * N))).card := by
          rw [card_univ]
          simp
  obtain ⟨f, -, hf⟩ := exists_mem_notMem_of_card_lt_card hU
  refine ⟨fun t => (f t).val, ?_⟩
  intro x hx
  have hnot : f ∉ Bad x := fun hmem => hf (mem_biUnion.mpr ⟨x, hx, hmem⟩)
  rw [Fintype.mem_piFinset] at hnot
  push Not at hnot
  obtain ⟨t, ht⟩ := hnot
  simp only [BadShift, mem_filter, mem_univ, true_and, not_forall, not_not] at ht
  obtain ⟨b, hb, hbeq⟩ := ht
  exact ⟨t, b, hb, hbeq.symm⟩

lemma lt_four_pow (j : ℕ) : j < 4 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ']
    omega

lemma sum_biUnion_image_inv_le (K : ℕ) (B : ℕ → Finset ℕ) :
    ∑ n ∈ (Finset.range K).biUnion (fun j => (B j).image (fun b : ℕ => 4 * 4 ^ j + b)),
        (n : ℝ)⁻¹ ≤
      ∑ j ∈ Finset.range K, ((B j).card : ℝ) / (4 : ℝ) ^ j := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.sum_insert Finset.notMem_range_self]
    let s := (B K).image (fun b : ℕ => 4 * 4 ^ K + b)
    let t := (Finset.range K).biUnion (fun j => (B j).image (fun b : ℕ => 4 * 4 ^ j + b))
    have hunion : ∑ n ∈ s ∪ t, (n : ℝ)⁻¹ ≤ (∑ n ∈ s, (n : ℝ)⁻¹) + ∑ n ∈ t, (n : ℝ)⁻¹ := by
      rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union disjoint_sdiff_self_right]
      have hsub : ∑ n ∈ t \ s, (n : ℝ)⁻¹ ≤ ∑ n ∈ t, (n : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => by positivity)
      linarith
    have hs : ∑ n ∈ s, (n : ℝ)⁻¹ ≤ ((B K).card : ℝ) / (4 : ℝ) ^ K := by
      calc ∑ n ∈ s, (n : ℝ)⁻¹
          ≤ ∑ _n ∈ s, ((4 : ℝ) ^ K)⁻¹ := by
            apply Finset.sum_le_sum
            intro n hn
            obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hn
            apply inv_anti₀ (by positivity)
            have hle : 4 ^ K ≤ 4 * 4 ^ K + b := by omega
            exact_mod_cast hle
        _ = (s.card : ℝ) * ((4 : ℝ) ^ K)⁻¹ := by simp
        _ ≤ ((B K).card : ℝ) * ((4 : ℝ) ^ K)⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast Finset.card_image_le
        _ = ((B K).card : ℝ) / (4 : ℝ) ^ K := by rw [div_eq_mul_inv]
    linarith

lemma block_bound_of_prod {j b : ℕ} (hj1 : 1 ≤ j)
    (hprod : ((((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)) * (b : ℝ) ≤
      2 * ((4 ^ j : ℕ) : ℝ) * Real.log ((4 ^ j : ℕ) : ℝ)) :
    (b : ℝ) / (4 : ℝ) ^ j ≤ 2 * (1 / (j : ℝ) ^ 2) := by
  have hexp1 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
  have hlog4 : 1 < Real.log 4 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hexp1
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  set L : ℝ := Real.log ((4 ^ j : ℕ) : ℝ) with hLdef
  have hLval : L = (j : ℝ) * Real.log 4 := by
    rw [hLdef, Nat.cast_pow, Real.log_pow]
    norm_num
  have hj_le_L : (j : ℝ) ≤ L := by
    rw [hLval]
    nlinarith
  have hL1 : 1 ≤ L := hjR.trans hj_le_L
  have hLpos : 0 < L := by linarith
  have hL_le_ceil : L ≤ (⌈L⌉₊ : ℝ) + 1 := by
    have := Nat.le_ceil L
    linarith
  have hL4_le_q : L ^ 4 ≤ (((⌈L⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
    have hq_cast : (((⌈L⌉₊ + 1) ^ 4 : ℕ) : ℝ) = ((⌈L⌉₊ : ℝ) + 1) ^ 4 := by
      push_cast
      ring
    rw [hq_cast]
    exact pow_le_pow_left₀ (by linarith) hL_le_ceil 4
  have h4cast : ((4 ^ j : ℕ) : ℝ) = (4 : ℝ) ^ j := by push_cast; rfl
  rw [h4cast] at hprod
  have hL4_prod : L ^ 4 * (b : ℝ) ≤ 2 * (4 : ℝ) ^ j * L := by
    calc L ^ 4 * (b : ℝ) ≤ (((⌈L⌉₊ + 1) ^ 4 : ℕ) : ℝ) * (b : ℝ) :=
          mul_le_mul_of_nonneg_right hL4_le_q (Nat.cast_nonneg _)
      _ ≤ 2 * (4 : ℝ) ^ j * L := hprod
  have hL3_prod : L ^ 3 * (b : ℝ) ≤ 2 * (4 : ℝ) ^ j := by
    apply le_of_mul_le_mul_right _ hLpos
    calc (L ^ 3 * (b : ℝ)) * L = L ^ 4 * (b : ℝ) := by ring
      _ ≤ 2 * (4 : ℝ) ^ j * L := hL4_prod
  have hj2_le_L3 : (j : ℝ) ^ 2 ≤ L ^ 3 := by
    have hj2_le_L2 : (j : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hj_le_L 2
    calc (j : ℝ) ^ 2 ≤ L ^ 2 * 1 := by linarith
      _ ≤ L ^ 2 * L := mul_le_mul_of_nonneg_left hL1 (sq_nonneg L)
      _ = L ^ 3 := by ring
  have hj2_prod : (j : ℝ) ^ 2 * (b : ℝ) ≤ 2 * (4 : ℝ) ^ j := by
    calc (j : ℝ) ^ 2 * (b : ℝ) ≤ L ^ 3 * (b : ℝ) :=
          mul_le_mul_of_nonneg_right hj2_le_L3 (Nat.cast_nonneg _)
      _ ≤ 2 * (4 : ℝ) ^ j := hL3_prod
  have hpos4 : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
  have hposj2 : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ hpos4]
  have hgoal : (b : ℝ) * (j : ℝ) ^ 2 ≤ 2 * (4 : ℝ) ^ j := by linarith
  calc (b : ℝ)
      = ((b : ℝ) * (j : ℝ) ^ 2) / (j : ℝ) ^ 2 := by field_simp
    _ ≤ (2 * (4 : ℝ) ^ j) / (j : ℝ) ^ 2 := div_le_div_of_nonneg_right hgoal hposj2.le
    _ = 2 * (1 / (j : ℝ) ^ 2) * (4 : ℝ) ^ j := by ring

noncomputable def blockSlice (A : Set ℕ) (j : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun b => 4 * 4 ^ j + b ∈ A) (Classical.decPred _) (Finset.Icc 1 (4 ^ j))

lemma mem_blockSlice {A : Set ℕ} {j b : ℕ} :
    b ∈ blockSlice A j ↔ b ∈ Finset.Icc 1 (4 ^ j) ∧ 4 * 4 ^ j + b ∈ A := by
  unfold blockSlice
  exact @Finset.mem_filter ℕ (fun b => 4 * 4 ^ j + b ∈ A) (Classical.decPred _) (Finset.Icc 1 (4 ^ j)) b

lemma blockSlice_subset (A : Set ℕ) (j : ℕ) : blockSlice A j ⊆ Finset.Icc 1 (4 ^ j) :=
  fun _ hb => (mem_blockSlice.mp hb).1

lemma summable_indicator_of_blocks (A : Set ℕ) (B : ℕ → Finset ℕ)
    (hAB : ∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x - 4 * 4 ^ j ∈ B j)
    (hB_sum : Summable (fun j : ℕ => ((B j).card : ℝ) / (4 : ℝ) ^ j)) :
    Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹)) := by
  classical
  refine summable_of_sum_le (c := ∑' j : ℕ, ((B j).card : ℝ) / (4 : ℝ) ^ j)
    (Set.indicator_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))) (fun s => ?_)
  let K : ℕ := s.sup id + 1
  have hind : ∑ n ∈ s, A.indicator (fun m : ℕ => (m : ℝ)⁻¹) n =
      ∑ n ∈ s.filter (fun m => m ∈ A), (n : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n ∈ A
    · rw [Set.indicator_of_mem hn, if_pos hn]
    · rw [Set.indicator_of_notMem hn, if_neg hn]
  rw [hind]
  have hsub : s.filter (fun m => m ∈ A) ⊆
      (Finset.range K).biUnion (fun j => (B j).image (fun b : ℕ => 4 * 4 ^ j + b)) := by
    intro x hx
    obtain ⟨hxs, hxA⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, hjlo, hxjB⟩ := hAB x hxA
    have hx_le : x ≤ s.sup id := Finset.le_sup (f := id) hxs
    have hj_lt : j < 4 ^ j := lt_four_pow j
    have hjK : j < K := by
      have h4 : 4 ^ j ≤ 4 * 4 ^ j := by omega
      have hxsup : x < K := Nat.lt_succ_of_le hx_le
      omega
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjK, ?_⟩
    exact Finset.mem_image.mpr ⟨x - 4 * 4 ^ j, hxjB, Nat.add_sub_of_le hjlo.le⟩
  calc ∑ n ∈ s.filter (fun m => m ∈ A), (n : ℝ)⁻¹
      ≤ ∑ n ∈ (Finset.range K).biUnion (fun j => (B j).image (fun b : ℕ => 4 * 4 ^ j + b)),
          (n : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ ∑ j ∈ Finset.range K, ((B j).card : ℝ) / (4 : ℝ) ^ j :=
        sum_biUnion_image_inv_le K B
    _ ≤ ∑' j : ℕ, ((B j).card : ℝ) / (4 : ℝ) ^ j :=
        hB_sum.sum_le_tsum (Finset.range K)
          (fun _ _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _))


lemma step_hle (A : Set ℕ) (J : ℕ)
    (hno : ¬ ∃ j : ℕ, J ≤ j ∧
      ∃ shifts : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4) → ℕ,
        ∀ x ∈ Finset.Icc 1 (4 ^ j),
          ∃ t : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
            ∃ b ∈ Finset.Icc 1 (4 ^ j), 4 * 4 ^ j + b ∈ A ∧ x + 4 ^ j = shifts t + b)
    (j : ℕ) (hj : J ≤ j) :
    ((((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ)) * ((blockSlice A j).card : ℝ) ≤
      2 * ((4 ^ j : ℕ) : ℝ) * Real.log ((4 ^ j : ℕ) : ℝ) := by
  by_contra hng
  have hgt := lt_of_not_ge hng
  obtain ⟨shifts, hcov⟩ :=
    shift_cover_of_gt (4 ^ j) ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4) (blockSlice A j)
      (Nat.pos_of_ne_zero (pow_ne_zero j (by decide))) (blockSlice_subset A j) hgt
  apply hno
  refine ⟨j, hj, shifts, fun x hx => ?_⟩
  obtain ⟨t, b, hbB, hbeq⟩ := hcov x hx
  obtain ⟨hbicc, hbA⟩ := mem_blockSlice.mp hbB
  exact ⟨t, b, hbicc, hbA, hbeq⟩

lemma step_summable_of_dom (f : ℕ → ℝ) (J : ℕ) (hf0 : ∀ j, 0 ≤ f j)
    (hdom : ∀ j : ℕ, max J 1 ≤ j → f j ≤ 2 * (1 / (j : ℝ) ^ 2)) :
    Summable f := by
  have hp2 : Summable (fun n : ℕ => 2 * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left 2
  refine Summable.of_norm_bounded_eventually_nat hp2 ?_
  filter_upwards [Filter.eventually_ge_atTop (max J 1)] with j hj
  rw [Real.norm_of_nonneg (hf0 j)]
  exact hdom j hj

theorem prove_H1 :
    ∀ A : Set ℕ, (∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →
      ¬ Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹)) →
      ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧
        ∃ shifts : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4) → ℕ,
          ∀ x ∈ Finset.Icc 1 (4 ^ j),
            ∃ t : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
              ∃ b ∈ Finset.Icc 1 (4 ^ j), 4 * 4 ^ j + b ∈ A ∧ x + 4 ^ j = shifts t + b := by
  intro A hA hns J
  by_contra hno
  have hB_sum : Summable (fun j : ℕ => ((blockSlice A j).card : ℝ) / (4 : ℝ) ^ j) := by
    refine step_summable_of_dom _ J
      (fun _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)) (fun j hj => ?_)
    exact block_bound_of_prod ((le_max_right J 1).trans hj)
      (step_hle A J hno j ((le_max_left J 1).trans hj))
  refine hns (summable_indicator_of_blocks A (blockSlice A) (fun x hxA => ?_) hB_sum)
  obtain ⟨j, hjlo, hjhi⟩ := hA x hxA
  refine ⟨j, hjlo, mem_blockSlice.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩⟩
  rwa [Nat.add_sub_of_le hjlo.le]

end Test36944H1

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2.H1 :=
  Test36944H1.prove_H1
