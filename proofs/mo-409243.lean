import OMAStatements.S_mo_409243
import Mathlib

-- Parts 1 and 2 are finite counts. For parts 3 to 5, Fubini reduces each event to its slice over
-- the two distinguished first-column entries; every slice is a product of intervals and of a
-- box in the row coordinates, whose measures are explicit, and the resulting one-variable
-- integrals are evaluated with the fundamental theorem of calculus.

open MeasureTheory Set OMA.S_mo_409243

noncomputable def mo409243_c (t : ℝ) : ℝ := max 0 (min t 1)

lemma mo409243_c_mem (t : ℝ) : 0 ≤ mo409243_c t ∧ mo409243_c t ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma mo409243_c_eq {t : ℝ} (h : t ∈ Ioo (0:ℝ) 1) : mo409243_c t = t := by
  unfold mo409243_c; rw [min_eq_left h.2.le, max_eq_right h.1.le]

lemma mo409243_c_meas : Measurable mo409243_c := by
  unfold mo409243_c; fun_prop

instance mo409243_probU : IsProbabilityMeasure U := ⟨by simp [U, Real.volume_Ioo]⟩

instance mo409243_probLaw (s : ℕ) : IsProbabilityMeasure (law s) := by
  unfold law; infer_instance

lemma mo409243_U_Iio (t : ℝ) : U.real (Iio t) = mo409243_c t := by
  rw [measureReal_def, U, Measure.restrict_apply measurableSet_Iio, Set.Iio_inter_Ioo,
    Real.volume_Ioo, ENNReal.toReal_ofReal', sub_zero, mo409243_c, max_comm]

lemma mo409243_U_Ici (t : ℝ) : U.real (Ici t) = 1 - mo409243_c t := by
  rw [← compl_Iio, measureReal_compl measurableSet_Iio, mo409243_U_Iio, probReal_univ]

lemma mo409243_U_Ioi (t : ℝ) : U.real (Ioi t) = 1 - mo409243_c t := by
  have h0 : U {t} = 0 := by
    rw [U, Measure.restrict_apply (measurableSet_singleton t)]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  rw [measureReal_congr (Ioi_ae_eq_Ici' h0), mo409243_U_Ici]

lemma mo409243_g_mem (t : ℝ) :
    0 ≤ 1 - (1 - mo409243_c t) ^ 2 ∧ 1 - (1 - mo409243_c t) ^ 2 ≤ 1 := by
  obtain ⟨h0, h1⟩ := mo409243_c_mem t
  have a0 : 0 ≤ 1 - mo409243_c t := by linarith
  have a1 : 1 - mo409243_c t ≤ 1 := by linarith
  have := pow_le_one₀ (n := 2) a0 a1
  have := sq_nonneg (1 - mo409243_c t)
  constructor <;> linarith

lemma mo409243_P_min (t : ℝ) :
    (U.prod U).real {r : ℝ × ℝ | min r.1 r.2 < t} = 1 - (1 - mo409243_c t) ^ 2 := by
  have hm : MeasurableSet {r : ℝ × ℝ | min r.1 r.2 < t} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hc : {r : ℝ × ℝ | min r.1 r.2 < t}ᶜ = Ici t ×ˢ Ici t := by
    ext r
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ici, min_lt_iff,
      not_or, not_lt]
  have h1 := measureReal_compl (μ := U.prod U) hm
  rw [hc, probReal_univ] at h1
  have h2 : (U.prod U).real (Ici t ×ˢ Ici t) = (1 - mo409243_c t) ^ 2 := by
    rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul, ← measureReal_def,
      mo409243_U_Ici]
    ring
  rw [h2] at h1
  linarith

lemma mo409243_rows (s : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin s => U.prod U).real
        (Set.pi univ fun _ => {r : ℝ × ℝ | min r.1 r.2 < t}) =
      (1 - (1 - mo409243_c t) ^ 2) ^ s := by
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [← measureReal_def, mo409243_P_min, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

lemma mo409243_real_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set (α × β)} (hS : MeasurableSet S) :
    (μ.prod ν).real S = ∫ x, ν.real (Prod.mk x ⁻¹' S) ∂μ := by
  have hi : Integrable (S.indicator (1 : α × β → ℝ)) (μ.prod ν) :=
    (integrable_const (1:ℝ)).indicator hS
  rw [← integral_indicator_one hS, integral_prod _ hi]
  congr 1
  funext x
  rw [← integral_indicator_one (measurable_prodMk_left hS)]
  rfl

lemma mo409243_meas1 (s : ℕ) : MeasurableSet {x : Sample s | miss x x.1.1} := by
  have : {x : Sample s | miss x x.1.1} = {x | min x.1.1 x.2.1.1 < x.1.1} ∩
      ({x | min x.1.2 x.2.1.2 < x.1.1} ∩
        ⋂ i, {x | min (x.2.2 i).1 (x.2.2 i).2 < x.1.1}) := by
    ext x; simp [miss]
  rw [this]
  exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) (by fun_prop)))

lemma mo409243_meas2 (s : ℕ) : MeasurableSet {x : Sample s | miss x x.1.2} := by
  have : {x : Sample s | miss x x.1.2} = {x | min x.1.1 x.2.1.1 < x.1.2} ∩
      ({x | min x.1.2 x.2.1.2 < x.1.2} ∩
        ⋂ i, {x | min (x.2.2 i).1 (x.2.2 i).2 < x.1.2}) := by
    ext x; simp [miss]
  rw [this]
  exact (measurableSet_lt (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) (by fun_prop)))

noncomputable def mo409243_F1 (s : ℕ) (x1 : ℝ × ℝ) : ℝ :=
  mo409243_c x1.1 * (if x1.2 < x1.1 then 1 else mo409243_c x1.1) *
    (1 - (1 - mo409243_c x1.1) ^ 2) ^ s

lemma mo409243_F1_meas (s : ℕ) : Measurable (mo409243_F1 s) := by
  unfold mo409243_F1
  have hc := mo409243_c_meas
  refine ((hc.comp measurable_fst).mul (Measurable.ite
    (measurableSet_lt measurable_snd measurable_fst) measurable_const
    (hc.comp measurable_fst))).mul ?_
  exact (measurable_const.sub ((measurable_const.sub (hc.comp measurable_fst)).pow_const 2)).pow_const s

lemma mo409243_F1_mem (s : ℕ) (x1 : ℝ × ℝ) : mo409243_F1 s x1 ∈ Icc (0:ℝ) 1 := by
  unfold mo409243_F1
  obtain ⟨c0, c1⟩ := mo409243_c_mem x1.1
  obtain ⟨g0, g1⟩ := mo409243_g_mem x1.1
  have i0 : 0 ≤ (if x1.2 < x1.1 then (1:ℝ) else mo409243_c x1.1) := by split_ifs <;> linarith
  have i1 : (if x1.2 < x1.1 then (1:ℝ) else mo409243_c x1.1) ≤ 1 := by split_ifs <;> linarith
  have p0 := pow_nonneg g0 s
  have p1 := pow_le_one₀ (n := s) g0 g1
  exact ⟨mul_nonneg (mul_nonneg c0 i0) p0,
    mul_le_one₀ (mul_le_one₀ c1 i0 i1) p0 p1⟩

lemma mo409243_slice1 (s : ℕ) (x1 : ℝ × ℝ) :
    Prod.mk x1 ⁻¹' {x : Sample s | miss x x.1.1} =
      (Iio x1.1 ×ˢ {w : ℝ | min x1.2 w < x1.1}) ×ˢ
        Set.pi univ (fun _ => {r : ℝ × ℝ | min r.1 r.2 < x1.1}) := by
  ext y; simp [miss, and_assoc]

lemma mo409243_slice2 (s : ℕ) (x1 : ℝ × ℝ) :
    Prod.mk x1 ⁻¹' {x : Sample s | miss x x.1.2} =
      ({w : ℝ | min x1.1 w < x1.2} ×ˢ Iio x1.2) ×ˢ
        Set.pi univ (fun _ => {r : ℝ × ℝ | min r.1 r.2 < x1.2}) := by
  ext y; simp [miss, and_assoc]

lemma mo409243_U_min (a t : ℝ) :
    U.real {w : ℝ | min a w < t} = if a < t then 1 else mo409243_c t := by
  split_ifs with h
  · have : {w : ℝ | min a w < t} = univ := by ext w; simp [min_lt_iff, h]
    rw [this, probReal_univ]
  · have : {w : ℝ | min a w < t} = Iio t := by ext w; simp [min_lt_iff, h]
    rw [this, mo409243_U_Iio]

lemma mo409243_left (s : ℕ) :
    (law s).real {x : Sample s | miss x x.1.1} = ∫ x1, mo409243_F1 s x1 ∂(U.prod U) := by
  rw [law, mo409243_real_prod _ _ (mo409243_meas1 s)]
  congr 1
  funext x1
  rw [mo409243_slice1, measureReal_def, Measure.prod_prod, Measure.prod_prod,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [← measureReal_def]
  rw [mo409243_U_Iio, mo409243_U_min, mo409243_rows, mo409243_F1]

lemma mo409243_right (s : ℕ) :
    (law s).real {x : Sample s | miss x x.1.2} = ∫ x1, mo409243_F1 s x1 ∂(U.prod U) := by
  rw [law, mo409243_real_prod _ _ (mo409243_meas2 s), ← integral_prod_swap]
  congr 1
  funext x1
  rw [mo409243_slice2, measureReal_def, Measure.prod_prod, Measure.prod_prod,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [← measureReal_def]
  rw [mo409243_U_Iio, mo409243_U_min, mo409243_rows, mo409243_F1]
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring

lemma mo409243_int_ite (t1 a : ℝ) :
    ∫ t2, (if t2 < t1 then (1:ℝ) else a) ∂U = a + (1 - a) * mo409243_c t1 := by
  have : (fun t2 : ℝ => if t2 < t1 then (1:ℝ) else a) =
      fun t2 => a + (1 - a) * (Iio t1).indicator 1 t2 := by
    funext t2
    by_cases h : t2 < t1 <;> simp [h, Set.indicator]
  have h2 : Integrable (fun t2 => (1 - a) * (Iio t1).indicator (1 : ℝ → ℝ) t2) U :=
    ((integrable_const (1:ℝ)).indicator measurableSet_Iio).const_mul _
  rw [this, integral_add (integrable_const _) h2, integral_const, integral_const_mul, integral_indicator_one measurableSet_Iio,
    mo409243_U_Iio]
  simp

lemma mo409243_to_interval (f : ℝ → ℝ) (g : ℝ → ℝ) (h : ∀ t ∈ Ioo (0:ℝ) 1, f t = g t) :
    ∫ t, f t ∂U = ∫ t in (0:ℝ)..1, g t := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

lemma mo409243_F1_int (s : ℕ) :
    ∫ x1, mo409243_F1 s x1 ∂(U.prod U) = ∫ x in (0:ℝ)..1, x * (1 - (1 - x) ^ 2) ^ (s + 1) := by
  rw [integral_prod _ (Integrable.of_mem_Icc 0 1 (mo409243_F1_meas s).aemeasurable
    (ae_of_all _ (mo409243_F1_mem s)))]
  apply mo409243_to_interval
  intro t ht
  simp only [mo409243_F1]
  have : (fun t2 : ℝ => mo409243_c t * (if t2 < t then 1 else mo409243_c t) *
      (1 - (1 - mo409243_c t) ^ 2) ^ s) = fun t2 =>
      (mo409243_c t * (1 - (1 - mo409243_c t) ^ 2) ^ s) *
        (if t2 < t then 1 else mo409243_c t) := by
    funext t2; ring
  rw [this, integral_const_mul, mo409243_int_ite, mo409243_c_eq ht]
  ring

lemma mo409243_key (t1 t2 u1 u2 : ℝ) :
    ((min t1 u1 < t1 ∧ min t2 u2 < t1) ∧ (min t1 u1 < t2 ∧ min t2 u2 < t2)) ↔
      (u1 < min t1 t2 ∧ u2 < min t1 t2) := by
  simp only [min_lt_iff, lt_min_iff, lt_self_iff_false, false_or, or_false]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨h1, ?_⟩, ?_, h4⟩
    · rcases h3 with h | h
      · exact lt_trans h1 h
      · exact h
    · rcases h2 with h | h
      · exact lt_trans h4 h
      · exact h
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, Or.inr h3⟩, Or.inr h2, h4⟩

lemma mo409243_slice3 (s : ℕ) (x1 : ℝ × ℝ) :
    Prod.mk x1 ⁻¹' {x : Sample s | miss x x.1.1 ∧ miss x x.1.2} =
      (Iio (min x1.1 x1.2) ×ˢ Iio (min x1.1 x1.2)) ×ˢ
        Set.pi univ (fun _ => {r : ℝ × ℝ | min r.1 r.2 < min x1.1 x1.2}) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, miss, Set.mem_prod, Set.mem_Iio, Set.mem_pi,
    Set.mem_univ, true_implies]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
    exact ⟨(mo409243_key _ _ _ _).1 ⟨⟨h1, h2⟩, h4, h5⟩, fun i => lt_min (h3 i) (h6 i)⟩
  · rintro ⟨⟨hu1, hu2⟩, hr⟩
    obtain ⟨⟨h1, h2⟩, h4, h5⟩ := (mo409243_key x1.1 x1.2 y.1.1 y.1.2).2 ⟨hu1, hu2⟩
    exact ⟨⟨h1, h2, fun i => lt_of_lt_of_le (hr i) (min_le_left _ _)⟩, h4, h5,
      fun i => lt_of_lt_of_le (hr i) (min_le_right _ _)⟩

noncomputable def mo409243_K (s : ℕ) (t : ℝ) : ℝ :=
  mo409243_c t ^ 2 * (1 - (1 - mo409243_c t) ^ 2) ^ s

lemma mo409243_K_meas (s : ℕ) : Measurable (mo409243_K s) := by
  unfold mo409243_K
  have hc := mo409243_c_meas
  exact (hc.pow_const 2).mul ((measurable_const.sub ((measurable_const.sub hc).pow_const 2)).pow_const s)

lemma mo409243_K_mem (s : ℕ) (t : ℝ) : mo409243_K s t ∈ Icc (0:ℝ) 1 := by
  unfold mo409243_K
  obtain ⟨c0, c1⟩ := mo409243_c_mem t
  obtain ⟨g0, g1⟩ := mo409243_g_mem t
  exact ⟨mul_nonneg (pow_nonneg c0 2) (pow_nonneg g0 s),
    mul_le_one₀ (pow_le_one₀ c0 c1) (pow_nonneg g0 s) (pow_le_one₀ g0 g1)⟩

lemma mo409243_both (s : ℕ) :
    (law s).real {x : Sample s | miss x x.1.1 ∧ miss x x.1.2} =
      ∫ x1, mo409243_K s (min x1.1 x1.2) ∂(U.prod U) := by
  have hm : MeasurableSet {x : Sample s | miss x x.1.1 ∧ miss x x.1.2} := by
    rw [Set.setOf_and]; exact (mo409243_meas1 s).inter (mo409243_meas2 s)
  rw [law, mo409243_real_prod _ _ hm]
  congr 1
  funext x1
  rw [mo409243_slice3, measureReal_def, Measure.prod_prod, Measure.prod_prod,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [← measureReal_def]
  rw [mo409243_U_Iio, mo409243_rows, mo409243_K]
  ring

lemma mo409243_ite_mem (p : Prop) [Decidable p] (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) :
    (if p then v else 0) ∈ Icc (0:ℝ) 1 := by
  split_ifs
  · exact hv
  · exact ⟨le_refl 0, zero_le_one⟩

lemma mo409243_K_int (s : ℕ) :
    ∫ x1, mo409243_K s (min x1.1 x1.2) ∂(U.prod U) =
      2 * ∫ x in (0:ℝ)..1, (1 - x) * x ^ 2 * (1 - (1 - x) ^ 2) ^ s := by
  have hKm := mo409243_K_meas s
  have hKb := mo409243_K_mem s
  let f1 : ℝ × ℝ → ℝ := fun z => if z.1 ≤ z.2 then mo409243_K s z.1 else 0
  let f2 : ℝ × ℝ → ℝ := fun z => if z.1 < z.2 then mo409243_K s z.1 else 0
  have hsplit : (fun x1 : ℝ × ℝ => mo409243_K s (min x1.1 x1.2)) = fun z => f1 z + f2 z.swap := by
    funext z
    simp only [f1, f2, Prod.fst_swap, Prod.snd_swap]
    by_cases h : z.1 ≤ z.2
    · rw [min_eq_left h, if_pos h, if_neg (not_lt.2 h), add_zero]
    · rw [min_eq_right (le_of_lt (not_le.1 h)), if_neg h, if_pos (not_le.1 h), zero_add]
  have hf1m : Measurable f1 := Measurable.ite (measurableSet_le measurable_fst measurable_snd)
    (hKm.comp measurable_fst) measurable_const
  have hf2m : Measurable f2 := Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
    (hKm.comp measurable_fst) measurable_const
  have hf1i : Integrable f1 (U.prod U) := Integrable.of_mem_Icc 0 1 hf1m.aemeasurable
    (ae_of_all _ fun z => mo409243_ite_mem _ _ (hKb _))
  have hf2i : Integrable f2 (U.prod U) := Integrable.of_mem_Icc 0 1 hf2m.aemeasurable
    (ae_of_all _ fun z => mo409243_ite_mem _ _ (hKb _))
  have hf2si : Integrable (fun z : ℝ × ℝ => f2 z.swap) (U.prod U) :=
    Integrable.of_mem_Icc 0 1 (hf2m.comp measurable_swap).aemeasurable
      (ae_of_all _ fun z => mo409243_ite_mem _ _ (hKb _))
  rw [hsplit, integral_add hf1i hf2si, integral_prod_swap f2, integral_prod _ hf1i,
    integral_prod _ hf2i]
  have e1 : ∀ t1 : ℝ, ∫ t2, f1 (t1, t2) ∂U = mo409243_K s t1 * (1 - mo409243_c t1) := by
    intro t1
    have : (fun t2 => f1 (t1, t2)) =
        fun t2 => mo409243_K s t1 * (Ici t1).indicator (1 : ℝ → ℝ) t2 := by
      funext t2; by_cases h : t1 ≤ t2 <;> simp [f1, h, Set.indicator]
    rw [this, integral_const_mul, integral_indicator_one measurableSet_Ici, mo409243_U_Ici]
  have e2 : ∀ t1 : ℝ, ∫ t2, f2 (t1, t2) ∂U = mo409243_K s t1 * (1 - mo409243_c t1) := by
    intro t1
    have : (fun t2 => f2 (t1, t2)) =
        fun t2 => mo409243_K s t1 * (Ioi t1).indicator (1 : ℝ → ℝ) t2 := by
      funext t2; by_cases h : t1 < t2 <;> simp [f2, h, Set.indicator]
    rw [this, integral_const_mul, integral_indicator_one measurableSet_Ioi, mo409243_U_Ioi]
  simp only [e1, e2]
  rw [← two_mul]
  congr 1
  apply mo409243_to_interval
  intro t ht
  rw [mo409243_K, mo409243_c_eq ht]
  ring

lemma mo409243_part3 (s : ℕ) :
    (law s).real (leftEvent s)ᶜ = ∫ x in (0:ℝ)..1, x*(1-(1-x)^2)^(s+1) := by
  have : (leftEvent s)ᶜ = {x : Sample s | miss x x.1.1} := by ext x; simp [leftEvent]
  rw [this, mo409243_left, mo409243_F1_int]

lemma mo409243_part3r (s : ℕ) :
    (law s).real (rightEvent s)ᶜ = ∫ x in (0:ℝ)..1, x*(1-(1-x)^2)^(s+1) := by
  have : (rightEvent s)ᶜ = {x : Sample s | miss x x.1.2} := by ext x; simp [rightEvent]
  rw [this, mo409243_right, mo409243_F1_int]

lemma mo409243_part4 (s : ℕ) :
    (law s).real ((leftEvent s)ᶜ ∩ (rightEvent s)ᶜ) =
      2*∫ x in (0:ℝ)..1,(1-x)*x^2*(1-(1-x)^2)^s := by
  have : (leftEvent s)ᶜ ∩ (rightEvent s)ᶜ = {x : Sample s | miss x x.1.1 ∧ miss x x.1.2} := by
    ext x; simp [leftEvent, rightEvent]
  rw [this, mo409243_both, mo409243_K_int]

lemma mo409243_I1 : ∫ x in (0:ℝ)..1, x*(1-(1-x)^2)^(2+1) = 93/280 := by
  have h : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun y : ℝ => 8/5*y^5 - 2*y^6 + 6/7*y^7 - 1/8*y^8) (x*(1-(1-x)^2)^(2+1)) x := by
    intro x _
    have h5 := (hasDerivAt_pow 5 x).const_mul (8/5:ℝ)
    have h6 := (hasDerivAt_pow 6 x).const_mul (2:ℝ)
    have h7 := (hasDerivAt_pow 7 x).const_mul (6/7:ℝ)
    have h8 := (hasDerivAt_pow 8 x).const_mul (1/8:ℝ)
    exact (((h5.sub h6).add h7).sub h8).congr_deriv
      (by simp only [Nat.cast_ofNat, Nat.reduceSub]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num

lemma mo409243_I2 : ∫ x in (0:ℝ)..1, (1-x)*x^2*(1-(1-x)^2)^2 = 47/840 := by
  have h : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun y : ℝ => 4/5*y^5 - 4/3*y^6 + 5/7*y^7 - 1/8*y^8) ((1-x)*x^2*(1-(1-x)^2)^2) x := by
    intro x _
    have h5 := (hasDerivAt_pow 5 x).const_mul (4/5:ℝ)
    have h6 := (hasDerivAt_pow 6 x).const_mul (4/3:ℝ)
    have h7 := (hasDerivAt_pow 7 x).const_mul (5/7:ℝ)
    have h8 := (hasDerivAt_pow 8 x).const_mul (1/8:ℝ)
    exact (((h5.sub h6).add h7).sub h8).congr_deriv
      (by simp only [Nat.cast_ofNat, Nat.reduceSub]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num

theorem OMA.solution : type_of% @OMA.S_mo_409243.main := by
  refine ⟨?_, ?_, mo409243_part3, mo409243_part4, ?_⟩
  · dsimp only
    have c0 : (Finset.univ.filter (binaryGood 0)).card = 13 := by decide
    have c1 : (Finset.univ.filter (binaryGood 1)).card = 13 := by decide
    have c01 : (Finset.univ.filter (binaryGood 0) ∩ Finset.univ.filter (binaryGood 1)).card = 11 := by
      decide
    have cB : Fintype.card Bits = 16 := by decide
    simp only [fair, c0, c1, c01, cB]
    norm_num
  · dsimp only
    have cE : ((Finset.univ : Finset (Bits × Bool)).filter (fun p => p.2=binaryHeight p.1)).card = 16 := by
      decide
    have cA : (((Finset.univ : Finset (Bits × Bool)).filter (fun p => p.2=binaryHeight p.1)).filter
        (fun p => p.1 0 0 ≤ p.2)).card = 13 := by decide
    have cB : (((Finset.univ : Finset (Bits × Bool)).filter (fun p => p.2=binaryHeight p.1)).filter
        (fun p => p.1 1 0 ≤ p.2)).card = 13 := by decide
    have cAB : ((((Finset.univ : Finset (Bits × Bool)).filter (fun p => p.2=binaryHeight p.1)).filter
        (fun p => p.1 0 0 ≤ p.2)) ∩ (((Finset.univ : Finset (Bits × Bool)).filter
        (fun p => p.2=binaryHeight p.1)).filter (fun p => p.1 1 0 ≤ p.2))).card = 11 := by decide
    have cT : Fintype.card (Bits × Bool) = 32 := by decide
    simp only [fair, cE, cA, cB, cAB, cT]
    norm_num
  dsimp only
  have hA : MeasurableSet (leftEvent 2) := by
    have : leftEvent 2 = {x : Sample 2 | miss x x.1.1}ᶜ := by ext x; simp [leftEvent]
    rw [this]; exact (mo409243_meas1 2).compl
  have hB : MeasurableSet (rightEvent 2) := by
    have : rightEvent 2 = {x : Sample 2 | miss x x.1.2}ᶜ := by ext x; simp [rightEvent]
    rw [this]; exact (mo409243_meas2 2).compl
  have hAc : (law 2).real (leftEvent 2)ᶜ = 93/280 := by
    rw [mo409243_part3, mo409243_I1]
  have hBc : (law 2).real (rightEvent 2)ᶜ = 93/280 := by
    rw [mo409243_part3r, mo409243_I1]
  have hABc : (law 2).real ((leftEvent 2)ᶜ ∩ (rightEvent 2)ᶜ) = 47/420 := by
    rw [mo409243_part4, mo409243_I2]; norm_num
  have eA := measureReal_compl (μ := law 2) hA
  have eB := measureReal_compl (μ := law 2) hB
  have eAB := measureReal_compl (μ := law 2) (hA.inter hB)
  have eU := measureReal_union_add_inter (μ := law 2) (s := (leftEvent 2)ᶜ) hB.compl
  rw [probReal_univ] at eA eB eAB
  rw [compl_inter] at eAB
  have vA : (law 2).real (leftEvent 2) = 187/280 := by linarith
  have vB : (law 2).real (rightEvent 2) = 187/280 := by linarith
  have vAB : (law 2).real (leftEvent 2 ∩ rightEvent 2) = 47/105 := by linarith
  rw [vA, vB, vAB]
  norm_num
