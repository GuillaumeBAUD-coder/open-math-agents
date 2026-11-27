import FormalConjectures.GreensOpenProblems.«35»

-- Problem: Ben Green's Open Problem 35 — c inf upper ae25
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/35.lean:112 (declaration Green35.variants.c_inf_upper_ae25)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Green35AE25

open MeasureTheory
open scoped Convolution ENNReal

set_option maxRecDepth 8192 in
private def wl : List ℕ :=
  [180171, 91636, 119100, 74630, 85163, 70900, 1775, 983, 34879, 77096, 72421, 80918,
   93642, 111808, 94757, 63188, 38057, 55741, 65551, 37963, 30521, 46103, 103535, 91664,
   79822, 55692, 109014, 123407, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 7515, 5035, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5308, 16189, 11500, 4663, 1, 0, 15658,
   8677, 26527, 10883, 19729, 13553, 11822, 10148, 10463, 18782, 9018, 5657, 25780, 19298,
   28209, 27833, 17486, 15255, 4208, 2909, 395, 24559, 240, 35355, 18607, 21933, 8029,
   2956, 2622, 55, 13438, 5756, 23773, 12919, 17793, 7386, 13682, 7738, 16100, 5322, 59,
   10301, 8100, 23214, 35096, 0, 17064, 0, 704, 1360, 2810, 9725, 30176, 9389, 4593, 0, 0,
   0, 0, 44, 6834, 9406, 2628, 2351, 0, 0, 0, 1, 8974, 24694, 57970, 20468, 54751, 11800,
   28923, 14067, 33010, 19187, 186, 8, 0, 0, 47, 8560, 12063, 37726, 21889, 27956, 2721,
   17138, 10575, 840, 11494, 15398, 44956, 26534, 27638, 24206, 24101, 19479, 2701, 34,
   24162, 18863, 99, 5292, 4382, 17944, 20185, 50794, 41136, 50770, 41035, 56830, 50969,
   58008, 54586, 56033, 50471, 56850, 72226, 48820, 57227, 40753, 57474, 54862, 46354,
   59277, 42594, 62564, 31199, 30351, 37973, 48443, 28050, 33291, 21781, 19103, 8421,
   15689, 27699, 22800, 25179, 2, 6604, 200, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0,
   26, 1, 13465, 2806, 2133, 1, 6, 67, 25180, 13444, 28046, 5394, 0, 0, 9, 4395, 8385,
   30388, 0, 5, 0, 0, 6501, 5263, 0, 0, 0, 0, 186, 7636, 18458, 24779, 0, 37, 1948, 14355,
   17878, 15184, 6788, 19790, 24206, 3125, 1156, 921, 4121, 14176, 19670, 3069, 14917,
   23302, 17207, 4207, 2719, 5417, 12803, 0, 4605, 12267, 29, 5666, 12347, 7035, 8599,
   3404, 3746, 4147, 13, 17, 122, 8561, 11604, 1547, 5356, 18, 8607, 7235, 7545, 5170, 23,
   0, 0, 0, 0, 0, 1396, 5160, 7534, 491, 2524, 12681, 11509, 2610, 28683, 26432, 8831,
   16434, 18065, 35313, 32550, 31838, 41025, 39316, 56713, 51181, 59651, 52544, 59201,
   66726, 62631, 63182, 55504, 21018, 4293, 12147, 5346, 6881, 20249, 26845, 5436, 33264,
   34241, 31512, 44046, 40111, 37839, 45966, 48506, 26935, 27882, 26122, 27127, 38172,
   44820, 42801, 40477, 48897, 30, 0, 0, 0, 31600, 51680, 31743, 82675, 34, 46753, 38537,
   50184, 57148, 54859, 46368, 45040, 28835, 46567, 41810, 32328, 6170, 24837, 14992,
   40434, 36943, 38820, 40593, 34978, 28858, 1971, 31370, 1201, 23124, 19766, 25153,
   33995, 9016, 6328, 28366, 27190, 29502, 60426, 61912, 49634, 42617, 58018, 58182,
   54409, 41749, 27078, 4017, 32019, 28501, 33823, 23053, 14586, 8348, 5325, 30244, 21673,
   20628, 16348, 14191, 11900, 5934, 10168, 12881, 1077, 0, 14090, 32241, 30636, 34681,
   48763, 52341, 51812, 68158, 72425, 46588, 59173, 53339, 43182, 49875, 51178, 26676,
   23886, 34836, 28162, 24974, 28985, 25310, 23372, 20297, 23925, 26114, 13204, 6743,
   16792, 17125, 11776, 14098, 25078, 29664, 29187, 43243, 48548, 48527, 56766, 55283,
   44102, 52711, 62011, 48178, 37839, 37680, 26895, 28086, 37444, 26453, 8431, 11454,
   20518, 23639, 16737, 13031, 13371, 10670, 17421, 13339, 10522, 7754, 724, 9380, 17437,
   14019, 29864, 37305, 33264, 29896, 50174, 60867, 65068, 71596, 43293, 13398, 42684,
   51629, 33166, 26223, 24170, 6669, 54, 14970, 4741, 7980, 1, 30724, 9385, 14, 0, 0, 0,
   0, 0, 0, 2102, 537, 1592, 17595, 52328, 79825, 72466, 31344, 36610, 54979, 65755,
   81853, 120596]

private def M : ℕ := 600
private def S : ℕ := 12418292

set_option maxRecDepth 8192 in
private lemma wl_length : wl.length = M := by decide

set_option maxRecDepth 8192 in
private lemma wl_sum : wl.sum = S := by decide

private def addScaled (k : ℕ) : List ℕ → List ℕ → List ℕ
  | [], acc => acc
  | b :: bs, [] => (k * b) :: addScaled k bs []
  | b :: bs, a :: acc => (k * b + a) :: addScaled k bs acc

private def convList : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: as, bs =>
      if a = 0 then 0 :: convList as bs else addScaled a bs (0 :: convList as bs)

private lemma addScaled_getD (k : ℕ) (bs acc : List ℕ) (m : ℕ) :
    (addScaled k bs acc).getD m 0 = k * bs.getD m 0 + acc.getD m 0 := by
  induction bs generalizing acc m with
  | nil => simp [addScaled]
  | cons b bs ih =>
    cases acc with
    | nil =>
      cases m with
      | zero => simp [addScaled]
      | succ m => simpa [addScaled] using ih [] m
    | cons a acc =>
      cases m with
      | zero => simp [addScaled]
      | succ m => simpa [addScaled] using ih acc m

private lemma getD_eq_zero_of_le {l : List ℕ} {m : ℕ} (hm : l.length ≤ m) :
    l.getD m 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hm]

private lemma convList_getD (as bs : List ℕ) (m : ℕ) :
    (convList as bs).getD m 0 =
      ∑ i ∈ Finset.range as.length, ∑ j ∈ Finset.range bs.length,
        if i + j = m then as.getD i 0 * bs.getD j 0 else 0 := by
  induction as generalizing m with
  | nil => simp [convList]
  | cons a as ih =>
    have hhead : (convList (a :: as) bs).getD m 0 =
        a * bs.getD m 0 + (0 :: convList as bs).getD m 0 := by
      by_cases ha : a = 0
      · simp [convList, ha]
      · dsimp only [convList]
        rw [if_neg ha, addScaled_getD]
    rw [hhead]
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ, zero_add]
    have h0 : (∑ j ∈ Finset.range bs.length, if j = m then a * bs.getD j 0 else 0) =
        a * bs.getD m 0 := by
      by_cases hm : m < bs.length
      · rw [Finset.sum_eq_single m]
        · simp
        · intro j _ hj; simp [hj]
        · intro hm'; exact (hm' (Finset.mem_range.mpr hm)).elim
      · rw [Finset.sum_eq_zero]
        · rw [getD_eq_zero_of_le (Nat.le_of_not_lt hm), mul_zero]
        · intro j hj
          have hjm : j ≠ m := fun h => hm (h ▸ Finset.mem_range.mp hj)
          simp [hjm]
    rw [h0, add_comm]
    congr 1
    cases m with
    | zero =>
      simp only [List.getD_cons_zero]
      symm
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      simp
    | succ m' =>
      simp only [List.getD_cons_succ, ih m']
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hiff : i + 1 + j = m' + 1 ↔ i + j = m' := by omega
      simp [hiff]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
private lemma dd_all_ok :
    (convList wl wl).all (fun c => decide (M * 100000 * c ≤ 75265 * S ^ 2)) = true := by
  decide +kernel

private def dd1 (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
    if i + j = m then wl.getD i 0 * wl.getD j 0 else 0

private lemma dd1_bound (m : ℕ) : M * 100000 * dd1 m ≤ 75265 * S ^ 2 := by
  have hconv : dd1 m = (convList wl wl).getD m 0 := by
    unfold dd1
    rw [← wl_length]
    exact (convList_getD wl wl m).symm
  rw [hconv]
  by_cases hm : m < (convList wl wl).length
  · have hmem : (convList wl wl).getD m 0 ∈ convList wl wl := by
      have : (convList wl wl).getD m 0 = (convList wl wl)[m] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
      rw [this]
      exact List.getElem_mem hm
    have hdec := List.all_eq_true.mp dd_all_ok _ hmem
    exact of_decide_eq_true hdec
  · rw [getD_eq_zero_of_le (Nat.le_of_not_lt hm), mul_zero]
    exact Nat.zero_le _

private lemma dd1_cast (k : ℕ) :
    (dd1 k : ℝ) = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
      if i + j = k then (wl.getD i 0 : ℝ) * (wl.getD j 0 : ℝ) else 0 := by
  unfold dd1
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact Nat.cast_mul _ _
  · exact Nat.cast_zero

private lemma sum_getD_eq_sum (l : List ℕ) :
    (∑ i ∈ Finset.range l.length, l.getD i 0) = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ, List.sum_cons, ih, add_comm]

private noncomputable def I_i (i : ℕ) : Set ℝ :=
  Set.Ico ((i : ℝ) / M) (((i + 1 : ℕ) : ℝ) / M)

private noncomputable def gf (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range M,
    ((M : ℝ) / S * (wl.getD i 0 : ℝ)) * (I_i i).indicator (fun _ => (1 : ℝ)) x

private lemma integral_indicator_one {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : volume s < ⊤) :
    Integrable (s.indicator (fun _ => (1 : ℝ))) ∧
      ∫ y, s.indicator (fun _ => (1 : ℝ)) y = (volume s).toReal := by
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hfin⟩
  refine ⟨(integrable_indicator_iff hs).mpr (integrable_const (1 : ℝ)), ?_⟩
  rw [integral_indicator hs, setIntegral_const, smul_eq_mul, mul_one, Measure.real_def]

private lemma I_i_vol (i : ℕ) : volume (I_i i) = ENNReal.ofReal (1 / (M : ℝ)) := by
  unfold I_i
  rw [Real.volume_Ico]
  congr 1
  push_cast
  ring

private lemma I_i_int (i : ℕ) :
    Integrable ((I_i i).indicator (fun _ => (1 : ℝ))) ∧
      ∫ y, (I_i i).indicator (fun _ => (1 : ℝ)) y = 1 / (M : ℝ) := by
  have h := integral_indicator_one (s := I_i i) measurableSet_Ico
    (by rw [I_i_vol]; exact ENNReal.ofReal_lt_top)
  refine ⟨h.1, ?_⟩
  rw [h.2, I_i_vol, ENNReal.toReal_ofReal (div_nonneg zero_le_one (Nat.cast_nonneg _))]

private lemma gf_density : Green35.IsUnitIntervalDensity gf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine integrable_finsetSum _ fun i _ => ?_
    exact (I_i_int i).1.const_mul _
  · intro x
    refine Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) ?_
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  · intro x hx
    rw [Function.mem_support] at hx
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    have hind : (I_i i).indicator (fun _ => (1 : ℝ)) x ≠ 0 :=
      fun h => hne (by simp [h])
    have hmem : x ∈ I_i i := Set.mem_of_indicator_ne_zero hind
    rw [Finset.mem_range] at hi
    unfold I_i at hmem
    have hMpos : (0 : ℝ) < M := by norm_num [M]
    have h0 : (0 : ℝ) ≤ (i : ℝ) / M := div_nonneg (Nat.cast_nonneg _) hMpos.le
    have h1 : (((i + 1 : ℕ) : ℝ) / M) ≤ 1 := by
      rw [div_le_one hMpos]
      exact_mod_cast hi
    exact ⟨h0.trans hmem.1, hmem.2.le.trans h1⟩
  · unfold gf
    rw [integral_finsetSum]
    · have hMpos : (M : ℝ) ≠ 0 := by norm_num [M]
      have hSpos : (S : ℝ) ≠ 0 := by norm_num [S]
      simp_rw [integral_const_mul, (I_i_int _).2]
      have hsum : (∑ i ∈ Finset.range M, (M : ℝ) / S * (wl.getD i 0 : ℝ) * (1 / M)) =
          (∑ i ∈ Finset.range M, (wl.getD i 0 : ℝ)) / S := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp [hMpos, hSpos]
      rw [hsum]
      have hnat : (∑ i ∈ Finset.range M, wl.getD i 0) = S := by
        rw [← wl_length, sum_getD_eq_sum, wl_sum]
      have hreal : (∑ i ∈ Finset.range M, (wl.getD i 0 : ℝ)) = S := by
        exact_mod_cast hnat
      rw [hreal, div_self hSpos]
    · intro i _
      exact (I_i_int i).1.const_mul _

private lemma inter_vol (i j : ℕ) (x : ℝ) :
    let a : ℝ := (i : ℝ) / M
    let b : ℝ := ((i + 1 : ℕ) : ℝ) / M
    let c : ℝ := (j : ℝ) / M
    let d : ℝ := ((j + 1 : ℕ) : ℝ) / M
    let Sij := I_i i ∩ {y : ℝ | x - y ∈ I_i j}
    MeasurableSet Sij ∧ volume Sij < ⊤ ∧
      (volume Sij).toReal = max 0 (min b (x - c) - max a (x - d)) := by
  intro a b c d Sij
  have hmeas : MeasurableSet Sij :=
    measurableSet_Ico.inter (measurableSet_Ico.preimage (measurable_const.sub measurable_id))
  have hfin : volume Sij < ⊤ :=
    (measure_mono Set.inter_subset_left).trans_lt (by rw [I_i_vol]; exact ENNReal.ofReal_lt_top)
  refine ⟨hmeas, hfin, ?_⟩
  set L := max a (x - d)
  set R := min b (x - c)
  have hsub1 : Set.Ioo L R ⊆ Sij := by
    intro y hy
    refine ⟨⟨((le_max_left _ _).trans_lt hy.1).le, hy.2.trans_le (min_le_left _ _)⟩, ?_⟩
    have hx1 : c < x - y := by linarith [hy.2.trans_le (min_le_right _ _)]
    have hx2 : x - y < d := by linarith [(le_max_right a (x - d)).trans_lt hy.1]
    exact ⟨hx1.le, hx2⟩
  have hsub2 : Sij ⊆ Set.Icc L R := by
    intro y hy
    refine ⟨max_le hy.1.1 (by linarith [hy.2.2]), le_min hy.1.2.le (by linarith [hy.2.1])⟩
  have hvol : volume Sij = ENNReal.ofReal (R - L) := by
    apply le_antisymm
    · exact (measure_mono hsub2).trans_eq Real.volume_Icc
    · exact Real.volume_Ioo.symm.trans_le (measure_mono hsub1)
  rw [hvol]
  by_cases h : 0 ≤ R - L
  · rw [ENNReal.toReal_ofReal h, max_eq_right h]
  · have hle : R - L ≤ 0 := le_of_not_ge h
    rw [ENNReal.ofReal_of_nonpos hle, ENNReal.toReal_zero, max_eq_left hle]

private lemma J_eval (i j : ℕ) (x : ℝ) :
    let J := ∫ y, (I_i i).indicator (fun _ => (1 : ℝ)) y *
      (I_i j).indicator (fun _ => (1 : ℝ)) (x - y)
    Integrable (fun y => (I_i i).indicator (fun _ => (1 : ℝ)) y *
      (I_i j).indicator (fun _ => (1 : ℝ)) (x - y)) ∧
      J = max 0 (min (((i + 1 : ℕ) : ℝ) / M) (x - (j : ℝ) / M) -
        max ((i : ℝ) / M) (x - ((j + 1 : ℕ) : ℝ) / M)) := by
  have heq : (fun y => (I_i i).indicator (fun _ => (1 : ℝ)) y *
      (I_i j).indicator (fun _ => (1 : ℝ)) (x - y)) =
      (I_i i ∩ {y : ℝ | x - y ∈ I_i j}).indicator (fun _ => (1 : ℝ)) := by
    ext y
    by_cases h1 : y ∈ I_i i <;> by_cases h2 : x - y ∈ I_i j <;> simp [h1, h2]
  have hv := inter_vol i j x
  have hi := integral_indicator_one hv.1 hv.2.1
  rw [← heq] at hi
  refine ⟨hi.1, ?_⟩
  rw [hi.2, hv.2.2]

private lemma conv_gf_eq (x : ℝ) :
    (gf ⋆ gf) x = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
      (((M : ℝ) / S) ^ 2 * ((wl.getD i 0 : ℝ) * (wl.getD j 0 : ℝ))) *
        max 0 (min (((i + 1 : ℕ) : ℝ) / M) (x - (j : ℝ) / M) -
          max ((i : ℝ) / M) (x - ((j + 1 : ℕ) : ℝ) / M)) := by
  rw [MeasureTheory.convolution_lsmul]
  simp_rw [smul_eq_mul]
  have hexp : ∀ y, gf y * gf (x - y) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        (((M : ℝ) / S) ^ 2 * ((wl.getD i 0 : ℝ) * (wl.getD j 0 : ℝ))) *
          ((I_i i).indicator (fun _ => (1 : ℝ)) y *
            (I_i j).indicator (fun _ => (1 : ℝ)) (x - y)) := by
    intro y
    unfold gf
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, (J_eval i j x).2]
    · intro j _
      exact (J_eval i j x).1.const_mul _
  · intro i _
    exact integrable_finsetSum _ fun j _ => (J_eval i j x).1.const_mul _

private lemma conv_gf_nonneg (x : ℝ) : 0 ≤ (gf ⋆ gf) x := by
  rw [conv_gf_eq]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (le_max_left _ _)

private lemma grid_kernel_eval (i j m : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    max 0 (min ((i + 1 : ℝ)) ((m : ℝ) + θ - (j : ℝ)) -
      max (i : ℝ) ((m : ℝ) + θ - (j : ℝ) - 1)) =
      if i + j = m then θ else if i + j + 1 = m then 1 - θ else 0 := by
  by_cases h0 : i + j = m
  · have hm : (m : ℝ) = (i : ℝ) + (j : ℝ) := by exact_mod_cast h0.symm
    have ha : (m : ℝ) + θ - (j : ℝ) = (i : ℝ) + θ := by linarith
    have hb : (m : ℝ) + θ - (j : ℝ) - 1 = (i : ℝ) + (θ - 1) := by linarith
    have hmin : min ((i + 1 : ℝ)) ((i : ℝ) + θ) = (i : ℝ) + θ := min_eq_right (by linarith)
    have hmax : max (i : ℝ) ((i : ℝ) + (θ - 1)) = (i : ℝ) := max_eq_left (by linarith)
    rw [hb, ha, hmin, hmax, add_sub_cancel_left, max_eq_right hθ0, if_pos h0]
  · by_cases h1 : i + j + 1 = m
    · have hm : (m : ℝ) = (i : ℝ) + (j : ℝ) + 1 := by exact_mod_cast h1.symm
      have ha : (m : ℝ) + θ - (j : ℝ) = (i : ℝ) + 1 + θ := by linarith
      have hb : (m : ℝ) + θ - (j : ℝ) - 1 = (i : ℝ) + θ := by linarith
      have hmin : min ((i + 1 : ℝ)) ((i : ℝ) + 1 + θ) = (i : ℝ) + 1 := min_eq_left (by linarith)
      have hmax : max (i : ℝ) ((i : ℝ) + θ) = (i : ℝ) + θ := max_eq_right (by linarith)
      rw [hb, ha, hmin, hmax]
      have hsub : (i : ℝ) + 1 - ((i : ℝ) + θ) = 1 - θ := by ring
      rw [hsub, max_eq_right (by linarith)]
      simp [h0, h1]
    · simp only [h0, ↓reduceIte, h1]
      apply max_eq_left
      rcases lt_or_gt_of_ne h0 with hlt | hgt
      · have hge2 : i + j + 2 ≤ m := by omega
        have hge2r : (i : ℝ) + (j : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hge2
        have hle1 : min ((i : ℝ) + 1) ((m : ℝ) + θ - (j : ℝ)) ≤ (i : ℝ) + 1 := min_le_left _ _
        have hle2 : (i : ℝ) + 1 ≤ max (i : ℝ) ((m : ℝ) + θ - (j : ℝ) - 1) :=
          le_max_of_le_right (by linarith)
        linarith
      · have hge1 : m + 1 ≤ i + j := by omega
        have hge1r : (m : ℝ) + 1 ≤ (i : ℝ) + (j : ℝ) := by exact_mod_cast hge1
        have hle1 : min ((i : ℝ) + 1) ((m : ℝ) + θ - (j : ℝ)) ≤ (m : ℝ) + θ - (j : ℝ) :=
          min_le_right _ _
        have hle2 : (i : ℝ) ≤ max (i : ℝ) ((m : ℝ) + θ - (j : ℝ) - 1) := le_max_left _ _
        linarith

private lemma dd1_real_bound (k : ℕ) :
    ((M : ℝ) / (S : ℝ) ^ 2) * (dd1 k : ℝ) ≤ 75265 / 100000 := by
  have hSpos : (0 : ℝ) < (S : ℝ) ^ 2 := by norm_num [S]
  rw [div_mul_eq_mul_div, div_le_iff₀ hSpos]
  have hnat : M * 100000 * dd1 k ≤ 75265 * S ^ 2 := dd1_bound k
  have hreal : (M : ℝ) * 100000 * (dd1 k : ℝ) ≤ 75265 * (S : ℝ) ^ 2 := by
    exact_mod_cast hnat
  linarith

private lemma conv_gf_le (x : ℝ) : (gf ⋆ gf) x ≤ 75265 / 100000 := by
  have hMpos : (0 : ℝ) < M := by norm_num [M]
  by_cases hx0 : x < 0
  · rw [conv_gf_eq, Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_]
    · norm_num
    · have hzero : max 0 (min (((i + 1 : ℕ) : ℝ) / M) (x - (j : ℝ) / M) -
          max ((i : ℝ) / M) (x - ((j + 1 : ℕ) : ℝ) / M)) = 0 := by
        apply max_eq_left
        have h1 : min (((i + 1 : ℕ) : ℝ) / M) (x - (j : ℝ) / M) ≤ x - (j : ℝ) / M :=
          min_le_right _ _
        have h2 : (i : ℝ) / M ≤ max ((i : ℝ) / M) (x - ((j + 1 : ℕ) : ℝ) / M) := le_max_left _ _
        have h3 : x - (j : ℝ) / M ≤ (i : ℝ) / M := by
          have : (0 : ℝ) ≤ (i : ℝ) / M + (j : ℝ) / M :=
            add_nonneg (div_nonneg (Nat.cast_nonneg _) hMpos.le)
              (div_nonneg (Nat.cast_nonneg _) hMpos.le)
          linarith
        linarith
      rw [hzero, mul_zero]
  · push Not at hx0
    by_cases hx2 : 2 ≤ x
    · rw [conv_gf_eq, Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_]
      · norm_num
      · rw [Finset.mem_range] at hi hj
        have hi1 : (((i + 1 : ℕ) : ℝ) / M) ≤ 1 := by
          rw [div_le_one hMpos]; exact_mod_cast hi
        have hj1 : (((j + 1 : ℕ) : ℝ) / M) ≤ 1 := by
          rw [div_le_one hMpos]; exact_mod_cast hj
        have hzero : max 0 (min (((i + 1 : ℕ) : ℝ) / M) (x - (j : ℝ) / M) -
            max ((i : ℝ) / M) (x - ((j + 1 : ℕ) : ℝ) / M)) = 0 := by
          apply max_eq_left
          have h1 : min (((i + 1 : ℕ) : ℝ) / M) (x - (j : ℝ) / M) ≤ 1 :=
            (min_le_left _ _).trans hi1
          have h2 : 1 ≤ max ((i : ℝ) / M) (x - ((j + 1 : ℕ) : ℝ) / M) :=
            le_max_of_le_right (by linarith)
          linarith
        dsimp only
        rw [hzero, mul_zero]
    · push Not at hx2
      set m : ℕ := Nat.floor ((M : ℝ) * x)
      set θ : ℝ := (M : ℝ) * x - (m : ℝ)
      have hm_le : (m : ℝ) ≤ (M : ℝ) * x := Nat.floor_le (mul_nonneg hMpos.le hx0)
      have hm_lt : (M : ℝ) * x < (m : ℝ) + 1 := Nat.lt_floor_add_one _
      have hθ0 : 0 ≤ θ := by linarith
      have hθ1 : θ ≤ 1 := by linarith
      have hker : ∀ i j : ℕ,
          max 0 (min (((i + 1 : ℕ) : ℝ) / M) (x - (j : ℝ) / M) -
            max ((i : ℝ) / M) (x - ((j + 1 : ℕ) : ℝ) / M)) =
            (1 / (M : ℝ)) *
              (if i + j = m then θ else if i + j + 1 = m then 1 - θ else 0) := by
        intro i j
        have hscale : (M : ℝ) * max 0 (min (((i + 1 : ℕ) : ℝ) / M) (x - (j : ℝ) / M) -
            max ((i : ℝ) / M) (x - ((j + 1 : ℕ) : ℝ) / M)) =
            max 0 (min ((i + 1 : ℝ)) ((m : ℝ) + θ - (j : ℝ)) -
              max (i : ℝ) ((m : ℝ) + θ - (j : ℝ) - 1)) := by
          rw [mul_max_of_nonneg _ _ hMpos.le, mul_zero]
          congr 1
          rw [mul_sub, mul_min_of_nonneg _ _ hMpos.le, mul_max_of_nonneg _ _ hMpos.le]
          have hMx : (M : ℝ) * x = (m : ℝ) + θ := by dsimp [θ]; ring
          have ha : (M : ℝ) * (((i + 1 : ℕ) : ℝ) / M) = (i : ℝ) + 1 := by
            push_cast; field_simp [hMpos.ne']
          have hb : (M : ℝ) * (x - (j : ℝ) / M) = (m : ℝ) + θ - (j : ℝ) := by
            rw [mul_sub, hMx]; field_simp [hMpos.ne']
          have hc : (M : ℝ) * ((i : ℝ) / M) = (i : ℝ) := by field_simp [hMpos.ne']
          have hd : (M : ℝ) * (x - ((j + 1 : ℕ) : ℝ) / M) = (m : ℝ) + θ - (j : ℝ) - 1 := by
            rw [mul_sub, hMx]; push_cast; field_simp [hMpos.ne']; ring
          rw [ha, hb, hc, hd]
        rw [← grid_kernel_eval i j m θ hθ0 hθ1, ← hscale]
        field_simp [hMpos.ne']
      rw [conv_gf_eq]
      simp_rw [hker]
      have hfactor : ∀ i j : ℕ,
          (((M : ℝ) / S) ^ 2 * ((wl.getD i 0 : ℝ) * (wl.getD j 0 : ℝ))) *
            ((1 / (M : ℝ)) *
              (if i + j = m then θ else if i + j + 1 = m then 1 - θ else 0)) =
            ((M : ℝ) / (S : ℝ) ^ 2) *
              (θ * (if i + j = m then (wl.getD i 0 : ℝ) * (wl.getD j 0 : ℝ) else 0) +
                (1 - θ) * (if i + j + 1 = m then (wl.getD i 0 : ℝ) * (wl.getD j 0 : ℝ) else 0)) := by
        intro i j
        by_cases h0 : i + j = m
        · have h1 : i + j + 1 ≠ m := by omega
          simp only [if_pos h0, if_neg h1]
          field_simp [hMpos.ne']
          ring
        · by_cases h1 : i + j + 1 = m
          · simp only [if_neg h0, if_pos h1]
            field_simp [hMpos.ne']
            ring
          · simp only [if_neg h0, if_neg h1, mul_zero, add_zero]
      simp_rw [hfactor]
      simp_rw [← Finset.mul_sum]
      have hsplit : (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
          (θ * (if i + j = m then (wl.getD i 0 : ℝ) * (wl.getD j 0 : ℝ) else 0) +
            (1 - θ) * (if i + j + 1 = m then (wl.getD i 0 : ℝ) * (wl.getD j 0 : ℝ) else 0))) =
          θ * (dd1 m : ℝ) + (1 - θ) * (if m = 0 then 0 else (dd1 (m - 1) : ℝ)) := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hA : (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
            if i + j = m then (wl.getD i 0 : ℝ) * (wl.getD j 0 : ℝ) else 0) =
            (dd1 m : ℝ) := (dd1_cast m).symm
        have hB : (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
            if i + j + 1 = m then (wl.getD i 0 : ℝ) * (wl.getD j 0 : ℝ) else 0) =
            if m = 0 then 0 else (dd1 (m - 1) : ℝ) := by
          cases m with
          | zero =>
            simp only [↓reduceIte]
            apply Finset.sum_eq_zero
            intro i _
            apply Finset.sum_eq_zero
            intro j _
            simp
          | succ m' =>
            rw [if_neg (Nat.succ_ne_zero m'), Nat.succ_sub_one, dd1_cast m']
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            have hiff : i + j + 1 = m' + 1 ↔ i + j = m' := by omega
            simp only [hiff]
        rw [hA, hB]
      rw [hsplit]
      have h1 : ((M : ℝ) / (S : ℝ) ^ 2) * (dd1 m : ℝ) ≤ 75265 / 100000 := dd1_real_bound m
      have h2 : ((M : ℝ) / (S : ℝ) ^ 2) * (if m = 0 then (0 : ℝ) else (dd1 (m - 1) : ℝ)) ≤
          75265 / 100000 := by
        cases m with
        | zero => simp; norm_num
        | succ m' => rw [if_neg (Nat.succ_ne_zero m'), Nat.succ_sub_one]; exact dd1_real_bound m'
      have hcomb : ((M : ℝ) / (S : ℝ) ^ 2) *
          (θ * (dd1 m : ℝ) + (1 - θ) * (if m = 0 then 0 else (dd1 (m - 1) : ℝ))) =
          θ * (((M : ℝ) / (S : ℝ) ^ 2) * (dd1 m : ℝ)) +
            (1 - θ) * (((M : ℝ) / (S : ℝ) ^ 2) * (if m = 0 then 0 else (dd1 (m - 1) : ℝ))) := by
        ring
      rw [hcomb]
      nlinarith

private lemma gf_conv_norm_le : eLpNorm (gf ⋆ gf) ⊤ volume ≤ 0.75265 := by
  have hb : ∀ᵐ x ∂volume, ‖(gf ⋆ gf) x‖ ≤ (75265 : ℝ) / 100000 := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (conv_gf_nonneg x)]
    exact conv_gf_le x
  refine (eLpNorm_le_of_ae_bound hb).trans ?_
  rw [show (⊤ : ℝ≥0∞).toReal = 0 by simp, inv_zero, ENNReal.rpow_zero, one_mul]
  have hq : (75265 / 100000 : NNRat) = 0.75265 := by
    apply NNRat.ext
    change ((75265 / 100000 : NNRat) : ℚ) = (0.75265 : ℚ)
    push_cast
    norm_num
  rw [show (75265 : ℝ) / 100000 = (((0.75265 : NNRat) : NNReal) : ℝ) by
      rw [← hq]; push_cast; norm_num,
    ENNReal.ofReal_coe_nnreal]
  exact le_rfl

end Green35AE25

theorem OMA.solution : type_of% @Green35.variants.c_inf_upper_ae25 := by
  unfold Green35.c
  refine le_trans (sInf_le ?_) Green35AE25.gf_conv_norm_le
  exact ⟨Green35AE25.gf, Green35AE25.gf_density, rfl⟩
