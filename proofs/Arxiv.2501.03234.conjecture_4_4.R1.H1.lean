import OMAReductions.R_Arxiv_2501_03234_conjecture_4_4_R1

-- Step Arxiv.2501.03234.conjecture_4_4.R1.H1: hypothesis H1 of reduction Arxiv.2501.03234.conjecture_4_4.R1
-- Credit: @lettucrisp

open Filter Topology MeasureTheory Set Finset

namespace OMA.P_Arxiv_2501_03234_H1

noncomputable section

private def E : ℕ → ℝ → ℝ :=
  Nat.rec (fun _ => 0) (fun _ f x =>
    let r := x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ)
    if x = 0 then 0 else if r < 1 then 1 - f r else 1 + f (2 - r))

private lemma E_zero (x : ℝ) : E 0 x = 0 := rfl

private lemma E_succ (t : ℕ) (x : ℝ) :
    E (t + 1) x =
      let r := x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ)
      if x = 0 then 0 else if r < 1 then 1 - E t r else 1 + E t (2 - r) := rfl

private lemma E_measurable (t : ℕ) : Measurable (E t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hr : Measurable (fun x : ℝ => x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ)) := by
      have h1 : Measurable (fun x : ℝ => x⁻¹) := measurable_inv
      have h2 : Measurable (fun x : ℝ => (⌊x⁻¹ / 2⌋₊ : ℕ)) :=
        Nat.measurable_floor.comp (h1.div_const 2)
      exact h1.sub (measurable_const.mul (measurable_from_top.comp h2))
    have hbranch : Measurable (fun x : ℝ =>
        if x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ) < 1
        then 1 - E t (x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ))
        else 1 + E t (2 - (x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ)))) := by
      refine Measurable.ite (measurableSet_lt hr measurable_const) ?_ ?_
      · exact measurable_const.sub (ih.comp hr)
      · exact measurable_const.add (ih.comp (measurable_const.sub hr))
    refine Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const ?_
    exact hbranch

private lemma E_abs_le (t : ℕ) (x : ℝ) : |E t x| ≤ t := by
  induction t generalizing x with
  | zero => simp [E_zero]
  | succ t ih =>
    rw [E_succ]
    dsimp only
    split_ifs with h0 hr
    · simp; positivity
    · have h := ih (x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ))
      rw [abs_le] at h ⊢
      push_cast
      constructor <;> linarith
    · have h := ih (2 - (x⁻¹ - 2 * (⌊x⁻¹ / 2⌋₊ : ℕ)))
      rw [abs_le] at h ⊢
      push_cast
      constructor <;> linarith

private def InCone (g : ℝ → ℝ) : Prop :=
  Measurable g ∧ (∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ g u) ∧ MonotoneOn g (Icc (0 : ℝ) 1)

private lemma InCone.bound {g : ℝ → ℝ} (hg : InCone g) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ g u ∧ g u ≤ g 1 :=
  ⟨hg.2.1 u hu, hg.2.2 hu ⟨zero_le_one, le_rfl⟩ hu.2⟩

private lemma InCone.smul {g : ℝ → ℝ} (hg : InCone g) {c : ℝ} (hc : 0 ≤ c) :
    InCone (fun u => c * g u) :=
  ⟨measurable_const.mul hg.1,
   fun u hu => mul_nonneg hc (hg.2.1 u hu),
   fun _ hu _ hv huv => mul_le_mul_of_nonneg_left (hg.2.2 hu hv huv) hc⟩

private lemma InCone.add {g₁ g₂ : ℝ → ℝ} (h₁ : InCone g₁) (h₂ : InCone g₂) :
    InCone (fun u => g₁ u + g₂ u) :=
  ⟨h₁.1.add h₂.1,
   fun u hu => add_nonneg (h₁.2.1 u hu) (h₂.2.1 u hu),
   fun _ hu _ hv huv => add_le_add (h₁.2.2 hu hv huv) (h₂.2.2 hu hv huv)⟩

private def Lterm (g : ℝ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2 -
  g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) + u) ^ 2

private def Lstar (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  if u ∈ Icc (0 : ℝ) 1 then ∑' k : ℕ, Lterm g k u else 0

private lemma summable_inv_succ_sq : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr one_lt_two
  have h' := (summable_nat_add_iff 1).mpr h
  refine h'.congr fun k => ?_
  simp [one_div]

private lemma denom_pos_sub (k : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (k : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) - u := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith [hu.1, hu.2]

private lemma denom_pos_add (k : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (k : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) + u := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith [hu.1, hu.2]

private lemma inv_sub_mem (k : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    1 / (2 * ((k : ℝ) + 1) - u) ∈ Icc (0 : ℝ) 1 := by
  have hd : 1 ≤ 2 * ((k : ℝ) + 1) - u := by
    have := denom_pos_sub k hu
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact ⟨by positivity, (div_le_one (by linarith)).mpr hd⟩

private lemma inv_add_mem (k : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    1 / (2 * ((k : ℝ) + 1) + u) ∈ Icc (0 : ℝ) 1 := by
  have hd : 1 ≤ 2 * ((k : ℝ) + 1) + u := by
    have := denom_pos_add k hu
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact ⟨by positivity, (div_le_one (by linarith)).mpr hd⟩

private lemma Lterm_nonneg {g : ℝ → ℝ} (hg : InCone g) (k : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ Lterm g k u := by
  dsimp [Lterm]
  have hd1 : 0 < 2 * ((k : ℝ) + 1) - u := by
    have := denom_pos_sub k hu; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hd2 : 0 < 2 * ((k : ℝ) + 1) + u := by
    have := denom_pos_add k hu; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hle : 2 * ((k : ℝ) + 1) - u ≤ 2 * ((k : ℝ) + 1) + u := by linarith [hu.1]
  have hinv : 1 / (2 * ((k : ℝ) + 1) + u) ≤ 1 / (2 * ((k : ℝ) + 1) - u) :=
    one_div_le_one_div_of_le hd1 hle
  have hg_le : g (1 / (2 * ((k : ℝ) + 1) + u)) ≤ g (1 / (2 * ((k : ℝ) + 1) - u)) :=
    hg.2.2 (inv_add_mem k hu) (inv_sub_mem k hu) hinv
  have hsq : (2 * ((k : ℝ) + 1) - u) ^ 2 ≤ (2 * ((k : ℝ) + 1) + u) ^ 2 := by nlinarith
  have hg_nn : 0 ≤ g (1 / (2 * ((k : ℝ) + 1) + u)) := hg.2.1 _ (inv_add_mem k hu)
  have hstep : g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) + u) ^ 2 ≤
      g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2 := by
    calc g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) + u) ^ 2
        ≤ g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) - u) ^ 2 :=
          div_le_div_of_nonneg_left hg_nn (by positivity) hsq
      _ ≤ g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2 :=
          div_le_div_of_nonneg_right hg_le (by positivity)
  linarith

private lemma Lterm_le {g : ℝ → ℝ} (hg : InCone g) (k : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Lterm g k u ≤ g 1 / ((k : ℝ) + 1) ^ 2 := by
  dsimp [Lterm]
  have hd1 := denom_pos_sub k hu
  have hd2 := denom_pos_add k hu
  have hg1 : g (1 / (2 * ((k : ℝ) + 1) - u)) ≤ g 1 := (hg.bound (inv_sub_mem k hu)).2
  have hg2 : 0 ≤ g (1 / (2 * ((k : ℝ) + 1) + u)) := hg.2.1 _ (inv_add_mem k hu)
  have h2nn : 0 ≤ g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) + u) ^ 2 := by positivity
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ (2 * ((k : ℝ) + 1) - u) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hg1_nn : 0 ≤ g 1 := hg.2.1 1 ⟨zero_le_one, le_rfl⟩
  have h1 : g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2 ≤
      g 1 / ((k : ℝ) + 1) ^ 2 := by
    calc g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2
        ≤ g 1 / (2 * ((k : ℝ) + 1) - u) ^ 2 := div_le_div_of_nonneg_right hg1 (by positivity)
      _ ≤ g 1 / ((k : ℝ) + 1) ^ 2 := div_le_div_of_nonneg_left hg1_nn (by positivity) hsq
  linarith

private lemma Lterm_summable {g : ℝ → ℝ} (hg : InCone g) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Summable (fun k => Lterm g k u) := by
  refine Summable.of_nonneg_of_le (fun k => Lterm_nonneg hg k hu) (fun k => Lterm_le hg k hu) ?_
  simpa [div_eq_mul_inv, one_div] using summable_inv_succ_sq.mul_left (g 1)

private lemma Lterm_monoOn {g : ℝ → ℝ} (hg : InCone g) (k : ℕ) :
    MonotoneOn (Lterm g k) (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  dsimp [Lterm]
  have hu1 : 0 < 2 * ((k : ℝ) + 1) - u := by have := denom_pos_sub k hu; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hv1 : 0 < 2 * ((k : ℝ) + 1) - v := by have := denom_pos_sub k hv; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hu2 : 0 < 2 * ((k : ℝ) + 1) + u := by have := denom_pos_add k hu; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hv2 : 0 < 2 * ((k : ℝ) + 1) + v := by have := denom_pos_add k hv; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hsub_le : 2 * ((k : ℝ) + 1) - v ≤ 2 * ((k : ℝ) + 1) - u := by linarith
  have hadd_le : 2 * ((k : ℝ) + 1) + u ≤ 2 * ((k : ℝ) + 1) + v := by linarith
  have hp1 : g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2 ≤
      g (1 / (2 * ((k : ℝ) + 1) - v)) / (2 * ((k : ℝ) + 1) - v) ^ 2 := by
    have h1 := hg.2.2 (inv_sub_mem k hu) (inv_sub_mem k hv) (one_div_le_one_div_of_le hv1 hsub_le)
    have h2 : (2 * ((k : ℝ) + 1) - v) ^ 2 ≤ (2 * ((k : ℝ) + 1) - u) ^ 2 := by nlinarith
    calc g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2
        ≤ g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - v) ^ 2 :=
          div_le_div_of_nonneg_left (hg.2.1 _ (inv_sub_mem k hu)) (by positivity) h2
      _ ≤ g (1 / (2 * ((k : ℝ) + 1) - v)) / (2 * ((k : ℝ) + 1) - v) ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
  have hp2 : g (1 / (2 * ((k : ℝ) + 1) + v)) / (2 * ((k : ℝ) + 1) + v) ^ 2 ≤
      g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) + u) ^ 2 := by
    have h1 := hg.2.2 (inv_add_mem k hv) (inv_add_mem k hu) (one_div_le_one_div_of_le hu2 hadd_le)
    have h2 : (2 * ((k : ℝ) + 1) + u) ^ 2 ≤ (2 * ((k : ℝ) + 1) + v) ^ 2 := by nlinarith
    calc g (1 / (2 * ((k : ℝ) + 1) + v)) / (2 * ((k : ℝ) + 1) + v) ^ 2
        ≤ g (1 / (2 * ((k : ℝ) + 1) + v)) / (2 * ((k : ℝ) + 1) + u) ^ 2 :=
          div_le_div_of_nonneg_left (hg.2.1 _ (inv_add_mem k hv)) (by positivity) h2
      _ ≤ g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) + u) ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
  linarith

private lemma Lterm_measurable {g : ℝ → ℝ} (hg : Measurable g) (k : ℕ) :
    Measurable (Lterm g k) := by
  unfold Lterm
  have h1 : Measurable (fun u : ℝ => 2 * ((k : ℝ) + 1) - u) := measurable_const.sub measurable_id
  have h2 : Measurable (fun u : ℝ => 2 * ((k : ℝ) + 1) + u) := measurable_const.add measurable_id
  exact ((hg.comp (measurable_const.div h1)).div (h1.pow_const 2)).sub
    ((hg.comp (measurable_const.div h2)).div (h2.pow_const 2))

private lemma Lstar_inCone {g : ℝ → ℝ} (hg : InCone g) : InCone (Lstar g) := by
  refine ⟨?_, ?_, ?_⟩
  · have htend : ∀ u : ℝ, Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N, if u ∈ Icc (0 : ℝ) 1 then Lterm g k u else 0)
        atTop (𝓝 (Lstar g u)) := by
      intro u
      by_cases hu : u ∈ Icc (0 : ℝ) 1
      · simp only [Lstar, if_pos hu]
        exact (Lterm_summable hg hu).hasSum.tendsto_sum_nat
      · simp only [Lstar, if_neg hu, Finset.sum_const_zero]
        exact tendsto_const_nhds
    exact measurable_of_tendsto_metrizable
      (fun N => Finset.measurable_sum _ fun k _ =>
        Measurable.ite measurableSet_Icc (Lterm_measurable hg.1 k) measurable_const)
      (tendsto_pi_nhds.mpr htend)
  · intro u hu
    rw [Lstar, if_pos hu]
    exact tsum_nonneg fun k => Lterm_nonneg hg k hu
  · intro u hu v hv huv
    simp only [Lstar, if_pos hu, if_pos hv]
    exact (Lterm_summable hg hu).tsum_le_tsum (fun k => Lterm_monoOn hg k hu hv huv)
      (Lterm_summable hg hv)

private lemma Lstar_zero (g : ℝ → ℝ) : Lstar g 0 = 0 := by
  rw [Lstar, if_pos ⟨le_rfl, zero_le_one⟩]
  have : ∀ k : ℕ, Lterm g k 0 = 0 := fun k => by simp [Lterm]
  simp [this]

private lemma Lstar_sub_eq {g₁ g₂ : ℝ → ℝ} (h₁ : InCone g₁) (h₂ : InCone g₂)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Lstar g₁ u - Lstar g₂ u = Lstar (fun x => g₁ x - g₂ x) u := by
  simp only [Lstar, if_pos hu]
  rw [← (Lterm_summable h₁ hu).tsum_sub (Lterm_summable h₂ hu)]
  congr 1; ext k
  simp [Lterm]; ring

private lemma Lstar_mono_cone {g₁ g₂ : ℝ → ℝ} (h₁ : InCone g₁) (h₂ : InCone g₂)
    (hdiff : InCone (fun u => g₁ u - g₂ u)) :
    InCone (fun u => Lstar g₁ u - Lstar g₂ u) := by
  have heq : (fun u => Lstar g₁ u - Lstar g₂ u) = Lstar (fun x => g₁ x - g₂ x) := by
    ext u
    by_cases hu : u ∈ Icc (0 : ℝ) 1
    · exact Lstar_sub_eq h₁ h₂ hu
    · simp only [Lstar, if_neg hu, sub_self]
  rw [heq]
  exact Lstar_inCone hdiff

private lemma Lstar_iter_inCone {g : ℝ → ℝ} (hg : InCone g) (j : ℕ) :
    InCone (Lstar^[j] g) := by
  induction j with
  | zero => exact hg
  | succ j ih => simpa [Function.iterate_succ_apply'] using Lstar_inCone ih

-- Step 3: Interval decomposition and transfer identity
private def J (n : ℕ) : Set ℝ := Ioo (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))

private lemma J_measurable (n : ℕ) : MeasurableSet (J n) := measurableSet_Ioo

private lemma J_pairwise_disjoint : Pairwise (Function.onFun Disjoint J) := by
  intro m n hmn
  wlog hlt : m < n generalizing m n
  · exact (this hmn.symm (by omega)).symm
  dsimp only [Function.onFun]
  rw [Set.disjoint_left]
  intro x hxm hxn
  have h1 : (m : ℝ) + 2 ≤ (n : ℝ) + 1 := by exact_mod_cast (show m + 2 ≤ n + 1 by omega)
  have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) h1
  linarith [hxm.1, hxn.2]

private lemma J_subset_Ioo (n : ℕ) : J n ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  have h0 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact ⟨h0.trans hx.1, hx.2.trans_le h1⟩

private lemma iUnion_J_ae_eq : (⋃ n : ℕ, J n : Set ℝ) =ᵐ[volume] Ioo (0 : ℝ) 1 := by
  have hsub : (⋃ n : ℕ, J n) ⊆ Ioo (0 : ℝ) 1 := Set.iUnion_subset J_subset_Ioo
  have hdiff : Ioo (0 : ℝ) 1 \ (⋃ n : ℕ, J n) ⊆ Set.range (fun n : ℕ => 1 / ((n : ℝ) + 2)) := by
    intro x ⟨hx, hnot⟩
    have hxpos : 0 < x := hx.1
    have hinv1 : 1 < x⁻¹ := (one_lt_inv₀ hxpos).mpr hx.2
    set m := ⌊x⁻¹⌋₊
    have hm_ge : 1 ≤ m := Nat.le_floor (by simpa using hinv1.le)
    have hm_le : (m : ℝ) ≤ x⁻¹ := Nat.floor_le (by positivity)
    have hm_lt : x⁻¹ < (m : ℝ) + 1 := Nat.lt_floor_add_one x⁻¹
    rcases eq_or_lt_of_le hm_le with heq | hlt
    · have hm2 : 2 ≤ m := by
        by_contra hlt2
        have hm1 : m = 1 := by omega
        rw [hm1, Nat.cast_one] at heq
        linarith
      refine ⟨m - 2, ?_⟩
      dsimp only
      have hcast : ((m - 2 : ℕ) : ℝ) + 2 = (m : ℝ) := by exact_mod_cast (show m - 2 + 2 = m by omega)
      rw [hcast, heq, one_div, inv_inv]
    · exfalso
      apply hnot
      refine Set.mem_iUnion.mpr ⟨m - 1, ?_⟩
      have h1 : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast (show m - 1 + 1 = m by omega)
      have h2 : ((m - 1 : ℕ) : ℝ) + 2 = (m : ℝ) + 1 := by exact_mod_cast (show m - 1 + 2 = m + 1 by omega)
      rw [J, h1, h2]
      refine ⟨?_, ?_⟩
      · rw [one_div, inv_lt_comm₀ (by positivity) hxpos]; exact hm_lt
      · rw [one_div, lt_inv_comm₀ hxpos (by positivity)]; exact hlt
  have hzero : volume (Ioo (0 : ℝ) 1 \ ⋃ n : ℕ, J n) = 0 :=
    measure_mono_null hdiff ((Set.countable_range _).measure_zero volume)
  rw [MeasureTheory.ae_eq_set]
  exact ⟨measure_mono_null (Set.sdiff_eq_empty.mpr hsub).subset (by simp), hzero⟩

private lemma E_succ_on_J_even (t k : ℕ) {x : ℝ} (hx : x ∈ J (2 * k)) :
    E (t + 1) x = 1 + E t (2 * ((k : ℝ) + 1) - x⁻¹) := by
  have hx0 : 0 < x := (J_subset_Ioo _ hx).1
  have h1 : 2 * ((k : ℝ) + 1) - 1 < x⁻¹ := by
    have := hx.2
    rw [one_div, lt_inv_comm₀ hx0 (by positivity)] at this
    push_cast at this; linarith
  have h2 : x⁻¹ < 2 * ((k : ℝ) + 1) := by
    have := hx.1
    rw [one_div, inv_lt_comm₀ (by positivity) hx0] at this
    push_cast at this; linarith
  have hfl : ⌊x⁻¹ / 2⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  rw [E_succ]
  dsimp only
  rw [if_neg hx0.ne', hfl, if_neg (by linarith)]
  congr 1; ring

private lemma E_succ_on_J_odd (t k : ℕ) {x : ℝ} (hx : x ∈ J (2 * k + 1)) :
    E (t + 1) x = 1 - E t (x⁻¹ - 2 * ((k : ℝ) + 1)) := by
  have hx0 : 0 < x := (J_subset_Ioo _ hx).1
  have h1 : 2 * ((k : ℝ) + 1) < x⁻¹ := by
    have := hx.2
    rw [one_div, lt_inv_comm₀ hx0 (by positivity)] at this
    push_cast at this; linarith
  have h2 : x⁻¹ < 2 * ((k : ℝ) + 1) + 1 := by
    have := hx.1
    rw [one_div, inv_lt_comm₀ (by positivity) hx0] at this
    push_cast at this; linarith
  have hfl : ⌊x⁻¹ / 2⌋₊ = k + 1 := by
    rw [Nat.floor_eq_iff (by positivity)]
    push_cast
    constructor <;> linarith
  rw [E_succ]
  dsimp only
  rw [if_neg hx0.ne', hfl, if_pos (by push_cast; linarith)]
  congr 2; push_cast; ring

private lemma change_of_var_even (k : ℕ) (F : ℝ → ℝ) :
    ∫ x in J (2 * k), F x =
      ∫ u in Ioo (0 : ℝ) 1, (1 / (2 * ((k : ℝ) + 1) - u) ^ 2) * F (1 / (2 * ((k : ℝ) + 1) - u)) := by
  let φ : ℝ → ℝ := fun u => (2 * ((k : ℝ) + 1) - u)⁻¹
  have himg : φ '' Ioo (0 : ℝ) 1 = J (2 * k) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioo, J, φ]
    constructor
    · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
      have hd : 0 < 2 * ((k : ℝ) + 1) - u := by linarith [Nat.cast_nonneg (α := ℝ) k]
      constructor
      · rw [one_div, inv_lt_inv₀ (by positivity) hd]; push_cast; linarith
      · rw [one_div, inv_lt_inv₀ hd (by positivity)]; push_cast; linarith
    · rintro ⟨h1, h2⟩
      have hx0 : 0 < x := lt_trans (by positivity) h1
      have hlo : 2 * ((k : ℝ) + 1) - 1 < x⁻¹ := by
        rw [one_div, lt_inv_comm₀ hx0 (by positivity)] at h2; push_cast at h2; linarith
      have hhi : x⁻¹ < 2 * ((k : ℝ) + 1) := by
        rw [one_div, inv_lt_comm₀ (by positivity) hx0] at h1; push_cast at h1; linarith
      refine ⟨2 * ((k : ℝ) + 1) - x⁻¹, ⟨by linarith, by linarith⟩, ?_⟩
      have : 2 * ((k : ℝ) + 1) - (2 * ((k : ℝ) + 1) - x⁻¹) = x⁻¹ := by ring
      rw [this, inv_inv]
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt φ (1 / (2 * ((k : ℝ) + 1) - u) ^ 2) (Ioo (0 : ℝ) 1) u := by
    intro u hu
    have hd : 2 * ((k : ℝ) + 1) - u ≠ 0 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith [hu.2]
    have hsub : HasDerivAt (fun t : ℝ => 2 * ((k : ℝ) + 1) - t) (-1) u := by
      rw [show (-1 : ℝ) = 0 - 1 by ring]
      exact (hasDerivAt_const u (2 * ((k : ℝ) + 1))).sub (hasDerivAt_id' u)
    have hinv := hsub.inv hd
    have hval : -(-1 : ℝ) / (2 * ((k : ℝ) + 1) - u) ^ 2 = 1 / (2 * ((k : ℝ) + 1) - u) ^ 2 := by ring
    rw [hval] at hinv
    exact hinv.hasDerivWithinAt
  have hinj : Set.InjOn φ (Ioo (0 : ℝ) 1) := by
    intro u _ v _ huv
    have := inv_injective huv
    linarith
  rw [← himg, MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  simp only [smul_eq_mul, one_div, φ]
  rw [abs_of_nonneg (by positivity)]

private lemma change_of_var_odd (k : ℕ) (F : ℝ → ℝ) :
    ∫ x in J (2 * k + 1), F x =
      ∫ u in Ioo (0 : ℝ) 1, (1 / (2 * ((k : ℝ) + 1) + u) ^ 2) * F (1 / (2 * ((k : ℝ) + 1) + u)) := by
  let ψ : ℝ → ℝ := fun u => (2 * ((k : ℝ) + 1) + u)⁻¹
  have himg : ψ '' Ioo (0 : ℝ) 1 = J (2 * k + 1) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioo, J, ψ]
    constructor
    · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
      have hd : 0 < 2 * ((k : ℝ) + 1) + u := by linarith [Nat.cast_nonneg (α := ℝ) k]
      constructor
      · rw [one_div, inv_lt_inv₀ (by positivity) hd]; push_cast; linarith
      · rw [one_div, inv_lt_inv₀ hd (by positivity)]; push_cast; linarith
    · rintro ⟨h1, h2⟩
      have hx0 : 0 < x := lt_trans (by positivity) h1
      have hlo : 2 * ((k : ℝ) + 1) < x⁻¹ := by
        rw [one_div, lt_inv_comm₀ hx0 (by positivity)] at h2; push_cast at h2; linarith
      have hhi : x⁻¹ < 2 * ((k : ℝ) + 1) + 1 := by
        rw [one_div, inv_lt_comm₀ (by positivity) hx0] at h1; push_cast at h1; linarith
      refine ⟨x⁻¹ - 2 * ((k : ℝ) + 1), ⟨by linarith, by linarith⟩, ?_⟩
      have : 2 * ((k : ℝ) + 1) + (x⁻¹ - 2 * ((k : ℝ) + 1)) = x⁻¹ := by ring
      rw [this, inv_inv]
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt ψ (-(1 / (2 * ((k : ℝ) + 1) + u) ^ 2)) (Ioo (0 : ℝ) 1) u := by
    intro u hu
    have hd : 2 * ((k : ℝ) + 1) + u ≠ 0 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith [hu.1]
    have hadd : HasDerivAt (fun t : ℝ => 2 * ((k : ℝ) + 1) + t) 1 u :=
      (hasDerivAt_id' u).const_add (2 * ((k : ℝ) + 1))
    have hinv := hadd.inv hd
    have hval : -(1 : ℝ) / (2 * ((k : ℝ) + 1) + u) ^ 2 = -(1 / (2 * ((k : ℝ) + 1) + u) ^ 2) := by ring
    rw [hval] at hinv
    exact hinv.hasDerivWithinAt
  have hinj : Set.InjOn ψ (Ioo (0 : ℝ) 1) := by
    intro u _ v _ huv
    have := inv_injective huv
    linarith
  rw [← himg, MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  simp only [smul_eq_mul, one_div, ψ, abs_neg]
  rw [abs_of_nonneg (by positivity)]

private lemma integrableOn_cone {g : ℝ → ℝ} (hg : InCone g) :
    IntegrableOn g (Ioo (0 : ℝ) 1) volume := by
  refine IntegrableOn.of_bound (by simp) hg.1.aestronglyMeasurable (g 1) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hb := hg.bound ⟨hx.1.le, hx.2.le⟩
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

private lemma integrableOn_cone_mul_E {g : ℝ → ℝ} (hg : InCone g) (t : ℕ) :
    IntegrableOn (fun x => g x * E t x) (Ioo (0 : ℝ) 1) volume := by
  refine IntegrableOn.of_bound (by simp) (hg.1.mul (E_measurable t)).aestronglyMeasurable (g 1 * t) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hb := hg.bound ⟨hx.1.le, hx.2.le⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb.1]
  exact mul_le_mul hb.2 (E_abs_le t x) (abs_nonneg _) (hg.2.1 1 ⟨zero_le_one, le_rfl⟩)

private lemma integral_mul_E_succ {g : ℝ → ℝ} (hg : InCone g) (t : ℕ) :
    ∫ x in (0 : ℝ)..1, g x * E (t + 1) x =
      (∫ x in (0 : ℝ)..1, g x) + ∫ u in (0 : ℝ)..1, Lstar g u * E t u := by
  rw [intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hrest : volume.restrict (Ioo (0 : ℝ) 1) = volume.restrict (⋃ n : ℕ, J n) :=
    (MeasureTheory.Measure.restrict_congr_set iUnion_J_ae_eq).symm
  have hint_gE : IntegrableOn (fun x => g x * E (t + 1) x) (⋃ n : ℕ, J n) volume := by
    rw [IntegrableOn, ← hrest]; exact integrableOn_cone_mul_E hg (t + 1)
  have hint_g : IntegrableOn g (⋃ n : ℕ, J n) volume := by
    rw [IntegrableOn, ← hrest]; exact integrableOn_cone hg
  have hsum_gE := MeasureTheory.hasSum_integral_iUnion J_measurable J_pairwise_disjoint hint_gE
  have hsum_g := MeasureTheory.hasSum_integral_iUnion J_measurable J_pairwise_disjoint hint_g
  have hpair_sum : ∀ {F : ℕ → ℝ}, Summable F →
      ∑' n : ℕ, F n = ∑' k : ℕ, (F (2 * k) + F (2 * k + 1)) := by
    intro F hF
    have hev : Summable (fun k : ℕ => F (2 * k)) :=
      hF.comp_injective (fun a b (h : 2 * a = 2 * b) => by omega)
    have hod : Summable (fun k : ℕ => F (2 * k + 1)) :=
      hF.comp_injective (fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega)
    rw [hev.tsum_add hod, tsum_even_add_odd hev hod]
  have hLHS : ∫ x in Ioo (0 : ℝ) 1, g x * E (t + 1) x =
      ∑' k : ℕ, ((∫ x in J (2 * k), g x * E (t + 1) x) +
                 ∫ x in J (2 * k + 1), g x * E (t + 1) x) := by
    rw [hrest, ← hsum_gE.tsum_eq, hpair_sum hsum_gE.summable]
  have hG : ∫ x in Ioo (0 : ℝ) 1, g x =
      ∑' k : ℕ, ((∫ x in J (2 * k), g x) + ∫ x in J (2 * k + 1), g x) := by
    rw [hrest, ← hsum_g.tsum_eq, hpair_sum hsum_g.summable]
  have hpair (k : ℕ) :
      (∫ x in J (2 * k), g x * E (t + 1) x) + (∫ x in J (2 * k + 1), g x * E (t + 1) x) =
      ((∫ x in J (2 * k), g x) + ∫ x in J (2 * k + 1), g x) +
        ∫ u in Ioo (0 : ℝ) 1, Lterm g k u * E t u := by
    have he1 : ∫ x in J (2 * k), g x * E (t + 1) x =
        ∫ x in J (2 * k), (g x + g x * E t (2 * ((k : ℝ) + 1) - x⁻¹)) := by
      refine MeasureTheory.setIntegral_congr_fun (J_measurable _) fun x hx => ?_
      rw [E_succ_on_J_even t k hx]; ring
    have he2 : ∫ x in J (2 * k + 1), g x * E (t + 1) x =
        ∫ x in J (2 * k + 1), (g x - g x * E t (x⁻¹ - 2 * ((k : ℝ) + 1))) := by
      refine MeasureTheory.setIntegral_congr_fun (J_measurable _) fun x hx => ?_
      rw [E_succ_on_J_odd t k hx]; ring
    have hJg1 : IntegrableOn g (J (2 * k)) volume :=
      (integrableOn_cone hg).mono_set (J_subset_Ioo _)
    have hJg2 : IntegrableOn g (J (2 * k + 1)) volume :=
      (integrableOn_cone hg).mono_set (J_subset_Ioo _)
    have hJe1 : IntegrableOn (fun x => g x * E t (2 * ((k : ℝ) + 1) - x⁻¹)) (J (2 * k)) volume := by
      have htot := (integrableOn_cone_mul_E hg (t + 1)).mono_set (J_subset_Ioo (2 * k))
      have hsub := htot.sub hJg1
      refine hsub.congr_fun (fun x hx => ?_) (J_measurable _)
      dsimp only [Pi.sub_apply]
      rw [E_succ_on_J_even t k hx]; ring
    have hJe2 : IntegrableOn (fun x => g x * E t (x⁻¹ - 2 * ((k : ℝ) + 1))) (J (2 * k + 1)) volume := by
      have htot := (integrableOn_cone_mul_E hg (t + 1)).mono_set (J_subset_Ioo (2 * k + 1))
      have hsub := hJg2.sub htot
      refine hsub.congr_fun (fun x hx => ?_) (J_measurable _)
      dsimp only [Pi.sub_apply]
      rw [E_succ_on_J_odd t k hx]; ring
    rw [he1, he2, MeasureTheory.integral_add hJg1 hJe1, MeasureTheory.integral_sub hJg2 hJe2]
    have hcov1 : ∫ x in J (2 * k), g x * E t (2 * ((k : ℝ) + 1) - x⁻¹) =
        ∫ u in Ioo (0 : ℝ) 1,
          (g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2) * E t u := by
      rw [change_of_var_even]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      have : 2 * ((k : ℝ) + 1) - (1 / (2 * ((k : ℝ) + 1) - u))⁻¹ = u := by
        rw [one_div, inv_inv]; ring
      rw [this]; ring
    have hcov2 : ∫ x in J (2 * k + 1), g x * E t (x⁻¹ - 2 * ((k : ℝ) + 1)) =
        ∫ u in Ioo (0 : ℝ) 1,
          (g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) + u) ^ 2) * E t u := by
      rw [change_of_var_odd]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      have : (1 / (2 * ((k : ℝ) + 1) + u))⁻¹ - 2 * ((k : ℝ) + 1) = u := by
        rw [one_div, inv_inv]; ring
      rw [this]; ring
    have hu1 : IntegrableOn (fun u =>
        (g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2) * E t u) (Ioo (0 : ℝ) 1) volume := by
      refine IntegrableOn.of_bound (by simp)
        ((((hg.1.comp (measurable_const.div (measurable_const.sub measurable_id))).div
          ((measurable_const.sub measurable_id).pow_const 2)).mul (E_measurable t)).aestronglyMeasurable)
        (g 1 * t) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
      have hb := hg.bound (inv_sub_mem k hu')
      have hd : 1 ≤ (2 * ((k : ℝ) + 1) - u) ^ 2 := by
        have := denom_pos_sub k hu'; nlinarith [Nat.cast_nonneg (α := ℝ) k]
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg hb.1, abs_of_nonneg (by positivity)]
      have hdiv : g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2 ≤ g 1 := by
        calc _ ≤ g (1 / (2 * ((k : ℝ) + 1) - u)) / 1 := div_le_div_of_nonneg_left hb.1 zero_lt_one hd
          _ = g (1 / (2 * ((k : ℝ) + 1) - u)) := div_one _
          _ ≤ g 1 := hb.2
      exact mul_le_mul hdiv (E_abs_le t u) (abs_nonneg _) (hg.2.1 1 ⟨zero_le_one, le_rfl⟩)
    have hu2 : IntegrableOn (fun u =>
        (g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) + u) ^ 2) * E t u) (Ioo (0 : ℝ) 1) volume := by
      refine IntegrableOn.of_bound (by simp)
        ((((hg.1.comp (measurable_const.div (measurable_const.add measurable_id))).div
          ((measurable_const.add measurable_id).pow_const 2)).mul (E_measurable t)).aestronglyMeasurable)
        (g 1 * t) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
      have hb := hg.bound (inv_add_mem k hu')
      have hd : 1 ≤ (2 * ((k : ℝ) + 1) + u) ^ 2 := by
        have := denom_pos_add k hu'; nlinarith [Nat.cast_nonneg (α := ℝ) k]
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg hb.1, abs_of_nonneg (by positivity)]
      have hdiv : g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) + u) ^ 2 ≤ g 1 := by
        calc _ ≤ g (1 / (2 * ((k : ℝ) + 1) + u)) / 1 := div_le_div_of_nonneg_left hb.1 zero_lt_one hd
          _ = g (1 / (2 * ((k : ℝ) + 1) + u)) := div_one _
          _ ≤ g 1 := hb.2
      exact mul_le_mul hdiv (E_abs_le t u) (abs_nonneg _) (hg.2.1 1 ⟨zero_le_one, le_rfl⟩)
    rw [hcov1, hcov2]
    have hsub_int : (∫ u in Ioo (0 : ℝ) 1,
        (g (1 / (2 * ((k : ℝ) + 1) - u)) / (2 * ((k : ℝ) + 1) - u) ^ 2) * E t u) -
      (∫ u in Ioo (0 : ℝ) 1,
        (g (1 / (2 * ((k : ℝ) + 1) + u)) / (2 * ((k : ℝ) + 1) + u) ^ 2) * E t u) =
      ∫ u in Ioo (0 : ℝ) 1, Lterm g k u * E t u := by
      rw [← MeasureTheory.integral_sub hu1 hu2]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
      simp [Lterm]; ring
    linarith
  have hg1_nn : 0 ≤ g 1 := hg.2.1 1 ⟨zero_le_one, le_rfl⟩
  have hsum_Lterm : Summable (fun k : ℕ => ∫ u in Ioo (0 : ℝ) 1, Lterm g k u * E t u) := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => g 1 * t / ((k : ℝ) + 1) ^ 2) ?_ ?_
    · simpa [div_eq_mul_inv, one_div] using summable_inv_succ_sq.mul_left (g 1 * t)
    · intro k
      have hbd : ∀ u ∈ Ioo (0 : ℝ) 1, ‖Lterm g k u * E t u‖ ≤ g 1 * t / ((k : ℝ) + 1) ^ 2 := by
        intro u hu
        have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Lterm_nonneg hg k hu')]
        calc Lterm g k u * |E t u|
            ≤ (g 1 / ((k : ℝ) + 1) ^ 2) * t :=
              mul_le_mul (Lterm_le hg k hu') (E_abs_le t u) (abs_nonneg _) (by positivity)
          _ = g 1 * t / ((k : ℝ) + 1) ^ 2 := by ring
      calc ‖∫ u in Ioo (0 : ℝ) 1, Lterm g k u * E t u‖
          ≤ (g 1 * t / ((k : ℝ) + 1) ^ 2) * (volume (Ioo (0 : ℝ) 1)).toReal :=
            MeasureTheory.norm_setIntegral_le_of_norm_le_const (by simp) hbd
        _ = g 1 * t / ((k : ℝ) + 1) ^ 2 := by simp
  have hsum_G : Summable (fun k : ℕ => (∫ x in J (2 * k), g x) + ∫ x in J (2 * k + 1), g x) :=
    (hsum_g.summable.comp_injective (fun _ _ h => by omega)).add
      (hsum_g.summable.comp_injective (fun _ _ h => by omega))
  have htsum_swap : ∫ u in Ioo (0 : ℝ) 1, Lstar g u * E t u =
      ∑' k : ℕ, ∫ u in Ioo (0 : ℝ) 1, Lterm g k u * E t u := by
    have hcongr : ∫ u in Ioo (0 : ℝ) 1, Lstar g u * E t u =
        ∫ u in Ioo (0 : ℝ) 1, ∑' k : ℕ, Lterm g k u * E t u := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      rw [Lstar, if_pos ⟨hu.1.le, hu.2.le⟩, ← tsum_mul_right]
    rw [hcongr]
    refine MeasureTheory.integral_tsum
      (fun k => ((Lterm_measurable hg.1 k).mul (E_measurable t)).aestronglyMeasurable) ?_
    have hbound_e : ∀ k : ℕ,
        ∫⁻ u in Ioo (0 : ℝ) 1, ‖Lterm g k u * E t u‖ₑ ∂volume ≤
          ENNReal.ofReal (g 1 * t / ((k : ℝ) + 1) ^ 2) := by
      intro k
      calc ∫⁻ u in Ioo (0 : ℝ) 1, ‖Lterm g k u * E t u‖ₑ ∂volume
          ≤ ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal (g 1 * t / ((k : ℝ) + 1) ^ 2) ∂volume := by
            refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo fun u hu => ?_
            have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
            rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (Lterm_nonneg hg k hu')]
            refine ENNReal.ofReal_le_ofReal ?_
            calc Lterm g k u * |E t u|
                ≤ (g 1 / ((k : ℝ) + 1) ^ 2) * t :=
                  mul_le_mul (Lterm_le hg k hu') (E_abs_le t u) (abs_nonneg _) (by positivity)
              _ = g 1 * t / ((k : ℝ) + 1) ^ 2 := by ring
        _ = ENNReal.ofReal (g 1 * t / ((k : ℝ) + 1) ^ 2) := by simp
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound_e) ?_)
    have hs : Summable (fun k : ℕ => g 1 * t / ((k : ℝ) + 1) ^ 2) := by
      simpa [div_eq_mul_inv, one_div] using summable_inv_succ_sq.mul_left (g 1 * t)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
    exact ENNReal.ofReal_lt_top
  rw [hLHS, hG, htsum_swap, ← hsum_G.tsum_add hsum_Lterm]
  congr 1; ext k
  exact hpair k

-- Step 4: Telescoping expansion of ∫ g * E t
private lemma integral_mul_E_eq_sum (t : ℕ) :
    ∀ {g : ℝ → ℝ}, InCone g →
      ∫ x in (0 : ℝ)..1, g x * E t x =
        ∑ j ∈ Finset.range t, ∫ x in (0 : ℝ)..1, (Lstar^[j] g) x := by
  induction t with
  | zero =>
    intro g _
    simp [E_zero]
  | succ t ih =>
    intro g hg
    rw [integral_mul_E_succ hg t, ih (Lstar_inCone hg), Finset.sum_range_succ']
    simp [Function.iterate_succ_apply, add_comm]

-- Step 5: Explicit subsolution f_m(u) = u / (m*(1-u) + 1)^2
private def f (m : ℕ) (u : ℝ) : ℝ := u / ((m : ℝ) * (1 - u) + 1) ^ 2

private lemma f_denom_pos (m : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    1 ≤ (m : ℝ) * (1 - u) + 1 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [hu.2]

private lemma f_hasDerivAt (m : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (f m) (((m : ℝ) * (1 - u) + 1 + 2 * (m : ℝ) * u) / ((m : ℝ) * (1 - u) + 1) ^ 3) u := by
  have hd : (m : ℝ) * (1 - u) + 1 ≠ 0 := by linarith [f_denom_pos m hu]
  have h1 : HasDerivAt (fun t : ℝ => (m : ℝ) * (1 - t) + 1) (-(m : ℝ)) u := by
    have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) u := by
      rw [show (-1 : ℝ) = 0 - 1 by ring]
      exact (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id' u)
    rw [show (-(m : ℝ)) = (m : ℝ) * (-1) by ring]
    exact (hsub.const_mul (m : ℝ)).add_const (1 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => ((m : ℝ) * (1 - t) + 1) ^ 2)
      (2 * ((m : ℝ) * (1 - u) + 1) * (-(m : ℝ))) u := by
    rw [show 2 * ((m : ℝ) * (1 - u) + 1) * (-(m : ℝ)) =
      ((2 : ℕ) : ℝ) * ((m : ℝ) * (1 - u) + 1) ^ (2 - 1) * (-(m : ℝ)) by norm_num]
    exact h1.pow 2
  have hq : HasDerivAt (f m)
      ((1 * ((m : ℝ) * (1 - u) + 1) ^ 2 - u * (2 * ((m : ℝ) * (1 - u) + 1) * (-(m : ℝ)))) /
        (((m : ℝ) * (1 - u) + 1) ^ 2) ^ 2) u :=
    (hasDerivAt_id' u).div h2 (pow_ne_zero 2 hd)
  have hval : (1 * ((m : ℝ) * (1 - u) + 1) ^ 2 - u * (2 * ((m : ℝ) * (1 - u) + 1) * (-(m : ℝ)))) /
        (((m : ℝ) * (1 - u) + 1) ^ 2) ^ 2 =
      ((m : ℝ) * (1 - u) + 1 + 2 * (m : ℝ) * u) / ((m : ℝ) * (1 - u) + 1) ^ 3 := by
    field_simp [hd]; ring
  rwa [hval] at hq

private lemma f_inCone (m : ℕ) : InCone (f m) := by
  refine ⟨?_, ?_, ?_⟩
  · exact measurable_id.div (((measurable_const.mul (measurable_const.sub measurable_id)).add measurable_const).pow_const 2)
  · intro u hu
    dsimp [f]
    have := f_denom_pos m hu
    have := hu.1
    positivity
  · refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact continuousOn_id.div
        (((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).add continuousOn_const).pow 2)
        (fun u hu => pow_ne_zero 2 (by linarith [f_denom_pos m hu]))
    · exact fun u hu => (f_hasDerivAt m (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' := interior_subset hu
      rw [(f_hasDerivAt m hu').deriv]
      have hd := f_denom_pos m hu'
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hnum : 0 ≤ (m : ℝ) * (1 - u) + 1 + 2 * (m : ℝ) * u := by nlinarith [hu'.1, hu'.2]
      positivity

private def c (k : ℕ) : ℝ := 1 + 12 / Real.sqrt ((k : ℝ) + 16)

private def hsub (k : ℕ) (u : ℝ) : ℝ := (1 / 528 : ℝ) * c k * f (k + 16) u

private lemma c_ge_one (k : ℕ) : 1 ≤ c k := by
  dsimp [c]
  have : 0 ≤ 12 / Real.sqrt ((k : ℝ) + 16) := by positivity
  linarith

private lemma c_le_four (k : ℕ) : c k ≤ 4 := by
  dsimp [c]
  have h4 : (4 : ℝ) ≤ Real.sqrt ((k : ℝ) + 16) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
    exact Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hdiv : 12 / Real.sqrt ((k : ℝ) + 16) ≤ 3 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

private lemma c_step (k : ℕ) :
    c (k + 1) ≤ c k * (1 - 1 / (((k : ℝ) + 17) * Real.sqrt ((k : ℝ) + 17))) := by
  set a : ℝ := Real.sqrt ((k : ℝ) + 16)
  set b : ℝ := Real.sqrt ((k : ℝ) + 17)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hb_pos : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have ha2 : a ^ 2 = (k : ℝ) + 16 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = (k : ℝ) + 17 := Real.sq_sqrt (by positivity)
  have hab_pos : 0 < a + b := by linarith
  have hsub_inv : 1 / a - 1 / b = 1 / (a * b * (a + b)) := by
    have hba : (b - a) * (a + b) = 1 := by nlinarith [ha2, hb2]
    field_simp [ha_pos.ne', hb_pos.ne', hab_pos.ne']
    linarith
  have hden : a * b * (a + b) ≤ 2 * (((k : ℝ) + 17) * b) := by
    have h1 : a + b ≤ 2 * b := by linarith
    have h2 : a * b ≤ b * b := mul_le_mul_of_nonneg_right hab hb_pos.le
    calc a * b * (a + b) ≤ (b * b) * (2 * b) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = 2 * (b ^ 2 * b) := by ring
      _ = 2 * (((k : ℝ) + 17) * b) := by rw [hb2]
  have hgap : 6 / (((k : ℝ) + 17) * b) ≤ c k - c (k + 1) := by
    have hce : c k - c (k + 1) = 12 * (1 / a - 1 / b) := by
      dsimp [c, a, b]
      rw [show ((k + 1 : ℕ) : ℝ) + 16 = (k : ℝ) + 17 by push_cast; ring]
      ring
    rw [hce, hsub_inv]
    have h1 : 12 / (2 * (((k : ℝ) + 17) * b)) ≤ 12 / (a * b * (a + b)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    have h2 : 12 * (1 / (a * b * (a + b))) = 12 / (a * b * (a + b)) := by ring
    have h3 : 12 / (2 * (((k : ℝ) + 17) * b)) = 6 / (((k : ℝ) + 17) * b) := by
      field_simp [hb_pos.ne']; ring
    linarith
  have hc4 : c k ≤ 4 := c_le_four k
  have hc_div : c k / (((k : ℝ) + 17) * b) ≤ 4 / (((k : ℝ) + 17) * b) :=
    div_le_div_of_nonneg_right hc4 (by positivity)
  have h46 : 4 / (((k : ℝ) + 17) * b) ≤ 6 / (((k : ℝ) + 17) * b) :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hkey : c k * (1 / (((k : ℝ) + 17) * b)) = c k / (((k : ℝ) + 17) * b) := by ring
  linarith

private lemma hsub_inCone (k : ℕ) : InCone (hsub k) := by
  have hc : 0 ≤ (1 / 528 : ℝ) * c k := by
    have := c_ge_one k; positivity
  exact (f_inCone (k + 16)).smul hc

private lemma base_cone : InCone (fun u => Lstar (fun _ => 1) u - hsub 0 u) := by
  have h1c : InCone (fun _ : ℝ => (1 : ℝ)) := ⟨measurable_const, fun _ _ => zero_le_one, monotoneOn_const⟩
  have hL1 : InCone (Lstar (fun _ => 1)) := Lstar_inCone h1c
  have h0c : InCone (hsub 0) := hsub_inCone 0
  have hmeas : Measurable (fun u => Lstar (fun _ => 1) u - hsub 0 u) := hL1.1.sub h0c.1
  have hmono : MonotoneOn (fun u => Lstar (fun _ => 1) u - hsub 0 u) (Icc (0 : ℝ) 1) := by
    let A : ℝ → ℝ := fun u => 1 / (2 - u) ^ 2 - hsub 0 u
    let B : ℝ → ℝ := fun u => -(1 / (2 + u) ^ 2)
    let R : ℝ → ℝ := fun u => ∑' k : ℕ, Lterm (fun _ => 1) (k + 1) u
    have hsplit : ∀ u ∈ Icc (0 : ℝ) 1, Lstar (fun _ => 1) u - hsub 0 u = A u + B u + R u := by
      intro u hu
      rw [Lstar, if_pos hu, (Lterm_summable h1c hu).tsum_eq_zero_add]
      dsimp [A, B, R, Lterm]
      ring
    have hA : MonotoneOn A (Icc (0 : ℝ) 1) := by
      have hAderiv : ∀ u ∈ Icc (0 : ℝ) 1,
          HasDerivAt A (2 / (2 - u) ^ 3 -
            ((1 / 528 : ℝ) * c 0) * ((16 * (1 - u) + 1 + 2 * 16 * u) / (16 * (1 - u) + 1) ^ 3)) u := by
        intro u hu
        have hd : 2 - u ≠ 0 := by linarith [hu.2]
        have hs : HasDerivAt (fun t : ℝ => 2 - t) (-1) u := by
          rw [show (-1 : ℝ) = 0 - 1 by ring]
          exact (hasDerivAt_const u (2 : ℝ)).sub (hasDerivAt_id' u)
        have h1 : HasDerivAt (fun t : ℝ => (2 - t) ^ 2) (2 * (2 - u) * (-1)) u := by
          rw [show 2 * (2 - u) * (-1) = ((2 : ℕ) : ℝ) * (2 - u) ^ (2 - 1) * (-1) by norm_num]
          exact hs.pow 2
        have hinv := (hasDerivAt_const u (1 : ℝ)).div h1 (pow_ne_zero 2 hd)
        have hval : (0 * (2 - u) ^ 2 - 1 * (2 * (2 - u) * -1)) / ((2 - u) ^ 2) ^ 2 =
            2 / (2 - u) ^ 3 := by field_simp [hd]; ring
        rw [hval] at hinv
        have hf0 := f_hasDerivAt 16 hu
        have hsub0 : HasDerivAt (hsub 0)
            (((1 / 528 : ℝ) * c 0) * ((16 * (1 - u) + 1 + 2 * 16 * u) / (16 * (1 - u) + 1) ^ 3)) u := by
          rw [show (16 * (1 - u) + 1 + 2 * 16 * u) / (16 * (1 - u) + 1) ^ 3 =
            (((16 : ℕ) : ℝ) * (1 - u) + 1 + 2 * ((16 : ℕ) : ℝ) * u) / (((16 : ℕ) : ℝ) * (1 - u) + 1) ^ 3 by norm_num]
          exact hf0.const_mul ((1 / 528 : ℝ) * c 0)
        exact hinv.sub hsub0
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
      · exact (continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
          (fun u hu => pow_ne_zero 2 (by dsimp only [Pi.sub_apply, id_eq]; linarith [hu.2]))).sub
          (continuousOn_const.mul (continuousOn_id.div
            (((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).add continuousOn_const).pow 2)
            (fun u hu => pow_ne_zero 2 (by linarith [f_denom_pos 16 hu]))))
      · exact fun u hu => (hAderiv u (interior_subset hu)).differentiableAt.differentiableWithinAt
      · intro u hu
        have hu' := interior_subset hu
        rw [(hAderiv u hu').deriv]
        have h2u_pos : 0 < 2 - u := by linarith [hu'.2]
        have h2u_le : 2 - u ≤ 2 := by linarith [hu'.1]
        have h1 : (1 / 4 : ℝ) ≤ 2 / (2 - u) ^ 3 := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith [sq_nonneg (2 - u)]
        have hc0 : c 0 ≤ 4 := c_le_four 0
        have hc0_nn : 0 ≤ c 0 := by linarith [c_ge_one 0]
        have hden1 : (1 : ℝ) ≤ 16 * (1 - u) + 1 := by linarith [hu'.2]
        have hden : (1 : ℝ) ≤ (16 * (1 - u) + 1) ^ 3 := by nlinarith [sq_nonneg (16 * (1 - u) + 1)]
        have hnum : 16 * (1 - u) + 1 + 2 * 16 * u ≤ 33 := by linarith [hu'.1, hu'.2]
        have hfrac : (16 * (1 - u) + 1 + 2 * 16 * u) / (16 * (1 - u) + 1) ^ 3 ≤ 33 := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        have hfrac_nn : 0 ≤ (16 * (1 - u) + 1 + 2 * 16 * u) / (16 * (1 - u) + 1) ^ 3 := by
          have : 0 ≤ 16 * (1 - u) + 1 + 2 * 16 * u := by linarith [hu'.1, hu'.2]
          positivity
        have hprod : ((1 / 528 : ℝ) * c 0) * ((16 * (1 - u) + 1 + 2 * 16 * u) / (16 * (1 - u) + 1) ^ 3) ≤ 1 / 4 := by
          calc _ ≤ ((1 / 528 : ℝ) * 4) * 33 := by
                refine mul_le_mul (by linarith) hfrac hfrac_nn (by positivity)
            _ = 1 / 4 := by norm_num
        linarith
    have hB : MonotoneOn B (Icc (0 : ℝ) 1) := by
      intro u hu v hv huv
      dsimp [B]
      have hu2 : 0 < 2 + u := by linarith [hu.1]
      have hle : (2 + u) ^ 2 ≤ (2 + v) ^ 2 := by nlinarith [hu.1, hv.1]
      have := one_div_le_one_div_of_le (by positivity) hle
      linarith
    have hR : MonotoneOn R (Icc (0 : ℝ) 1) := by
      intro u hu v hv huv
      dsimp [R]
      exact ((Lterm_summable h1c hu).comp_injective Nat.succ_injective).tsum_le_tsum
        (fun k => Lterm_monoOn h1c (k + 1) hu hv huv)
        ((Lterm_summable h1c hv).comp_injective Nat.succ_injective)
    intro u hu v hv huv
    dsimp only
    rw [hsplit u hu, hsplit v hv]
    exact add_le_add (add_le_add (hA hu hv huv) (hB hu hv huv)) (hR hu hv huv)
  refine ⟨hmeas, ?_, hmono⟩
  intro u hu
  have h0 : Lstar (fun _ => 1) 0 - hsub 0 0 = 0 := by
    rw [Lstar_zero]; simp [hsub, f]
  have := hmono ⟨le_rfl, zero_le_one⟩ hu hu.1
  linarith

private lemma f_step_monoOn (m : ℕ) (hm : 17 ≤ m) :
    MonotoneOn (fun u =>
      f (m - 1) (1 / (2 - u)) / (2 - u) ^ 2 -
        (1 - 1 / ((m : ℝ) * Real.sqrt (m : ℝ))) * f m u) (Icc (0 : ℝ) 1) := by
  let g : ℝ → ℝ := fun u =>
    f (m - 1) (1 / (2 - u)) / (2 - u) ^ 2 -
      (1 - 1 / ((m : ℝ) * Real.sqrt (m : ℝ))) * f m u
  have hm_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have h : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast (show m - 1 + 1 = m by omega)
    linarith
  have hsimp : ∀ u ∈ Icc (0 : ℝ) 1,
      f (m - 1) (1 / (2 - u)) / (2 - u) ^ 2 =
        1 / ((2 - u) * ((m : ℝ) * (1 - u) + 1) ^ 2) := by
    intro u hu
    have h2u : 2 - u ≠ 0 := by linarith [hu.2]
    dsimp [f]
    rw [hm_cast]
    field_simp [h2u]
    ring
  let g1 : ℝ → ℝ := fun u =>
    1 / ((2 - u) * ((m : ℝ) * (1 - u) + 1) ^ 2) -
      (1 - 1 / ((m : ℝ) * Real.sqrt (m : ℝ))) * f m u
  suffices hmono1 : MonotoneOn g1 (Icc (0 : ℝ) 1) by
    intro u hu v hv huv
    change g u ≤ g v
    have hu' : g u = g1 u := by dsimp [g, g1]; rw [hsimp u hu]
    have hv' : g v = g1 v := by dsimp [g, g1]; rw [hsimp v hv]
    rw [hu', hv']
    exact hmono1 hu hv huv
  set α : ℝ := 1 - 1 / ((m : ℝ) * Real.sqrt (m : ℝ))
  have hg1_deriv : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivAt g1
        (((((m : ℝ) * (1 - u) + 1) + 2 * (m : ℝ) * (2 - u)) /
            ((2 - u) ^ 2 * ((m : ℝ) * (1 - u) + 1) ^ 3)) -
          α * (((m : ℝ) * (1 - u) + 1 + 2 * (m : ℝ) * u) / ((m : ℝ) * (1 - u) + 1) ^ 3)) u := by
    intro u hu
    have h2u : 2 - u ≠ 0 := by linarith [hu.2]
    have hD : (m : ℝ) * (1 - u) + 1 ≠ 0 := by linarith [f_denom_pos m hu]
    have hsub1 : HasDerivAt (fun t : ℝ => 2 - t) (-1) u := by
      rw [show (-1 : ℝ) = 0 - 1 by ring]
      exact (hasDerivAt_const u (2 : ℝ)).sub (hasDerivAt_id' u)
    have hD1 : HasDerivAt (fun t : ℝ => (m : ℝ) * (1 - t) + 1) (-(m : ℝ)) u := by
      have hs : HasDerivAt (fun t : ℝ => 1 - t) (-1) u := by
        rw [show (-1 : ℝ) = 0 - 1 by ring]
        exact (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id' u)
      rw [show (-(m : ℝ)) = (m : ℝ) * (-1) by ring]
      exact (hs.const_mul (m : ℝ)).add_const (1 : ℝ)
    have hD2 : HasDerivAt (fun t : ℝ => ((m : ℝ) * (1 - t) + 1) ^ 2)
        (2 * ((m : ℝ) * (1 - u) + 1) * (-(m : ℝ))) u := by
      rw [show 2 * ((m : ℝ) * (1 - u) + 1) * (-(m : ℝ)) =
        ((2 : ℕ) : ℝ) * ((m : ℝ) * (1 - u) + 1) ^ (2 - 1) * (-(m : ℝ)) by norm_num]
      exact hD1.pow 2
    have hprod := hsub1.mul hD2
    have hinv := (hasDerivAt_const u (1 : ℝ)).div hprod (mul_ne_zero h2u (pow_ne_zero 2 hD))
    dsimp only [Pi.mul_apply] at hinv
    have hval : (0 * ((2 - u) * ((m : ℝ) * (1 - u) + 1) ^ 2) -
        1 * ((-1) * ((m : ℝ) * (1 - u) + 1) ^ 2 +
          (2 - u) * (2 * ((m : ℝ) * (1 - u) + 1) * -(m : ℝ)))) /
        ((2 - u) * ((m : ℝ) * (1 - u) + 1) ^ 2) ^ 2 =
      (((m : ℝ) * (1 - u) + 1) + 2 * (m : ℝ) * (2 - u)) /
        ((2 - u) ^ 2 * ((m : ℝ) * (1 - u) + 1) ^ 3) := by
      field_simp [h2u, hD]; ring
    rw [hval] at hinv
    exact hinv.sub ((f_hasDerivAt m hu).const_mul α)
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
  · refine (continuousOn_const.div
      ((continuousOn_const.sub continuousOn_id).mul
        (((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).add continuousOn_const).pow 2))
      (fun u hu => mul_ne_zero
        (by dsimp only [Pi.sub_apply, id_eq]; linarith [hu.2])
        (pow_ne_zero 2 (by dsimp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq]; linarith [f_denom_pos m hu])))).sub ?_
    exact continuousOn_const.mul (continuousOn_id.div
      (((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).add continuousOn_const).pow 2)
      (fun u hu => pow_ne_zero 2 (by linarith [f_denom_pos m hu])))
  · exact fun u hu => (hg1_deriv u (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' := interior_subset hu
    rw [(hg1_deriv u hu').deriv]
    set s : ℝ := 1 - u
    have hs0 : 0 ≤ s := by linarith [hu'.2]
    have hs1 : s ≤ 1 := by linarith [hu'.1]
    have h2u_pos : 0 < 2 - u := by linarith [hu'.2]
    have hD_pos : 0 < (m : ℝ) * (1 - u) + 1 := by linarith [f_denom_pos m hu']
    have hden_pos : 0 < (2 - u) ^ 2 * ((m : ℝ) * (1 - u) + 1) ^ 3 := by positivity
    rw [sub_nonneg]
    have hgoal : α * (((m : ℝ) * (1 - u) + 1 + 2 * (m : ℝ) * u) / ((m : ℝ) * (1 - u) + 1) ^ 3) =
        (α * (2 - u) ^ 2 * ((m : ℝ) * (1 - u) + 1 + 2 * (m : ℝ) * u)) /
          ((2 - u) ^ 2 * ((m : ℝ) * (1 - u) + 1) ^ 3) := by
      field_simp [h2u_pos.ne', hD_pos.ne']
    rw [hgoal]
    refine div_le_div_of_nonneg_right ?_ hden_pos.le
    have hm_pos : (0 : ℝ) < m := by positivity
    set r : ℝ := Real.sqrt (m : ℝ)
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hm_pos
    have hr2 : r ^ 2 = (m : ℝ) := Real.sq_sqrt hm_pos.le
    set t : ℝ := r * s
    have ht0 : 0 ≤ t := by positivity
    have hpoly : 0 ≤ (t - 1) ^ 2 * (t + 2) := by positivity
    have hcub : 0 ≤ (m : ℝ) * s ^ 3 - 3 * s + 2 / r := by
      have h1 : (m : ℝ) * s ^ 3 - 3 * s + 2 / r = ((t - 1) ^ 2 * (t + 2)) / r := by
        dsimp [t]
        field_simp [hr_pos.ne']
        nlinarith [hr2]
      rw [h1]; positivity
    have hs2 : s ^ 2 ≤ s := by nlinarith
    have hbase : 0 ≤ (m : ℝ) * s ^ 3 - 2 * s - s ^ 2 + 2 / r := by linarith
    have hfactor : 2 * (m : ℝ) ≤ (1 + s) ^ 2 * ((m : ℝ) * (2 - s) + 1) := by
      have h1 : 2 ≤ (1 + s) ^ 2 * (2 - s) := by nlinarith [sq_nonneg s]
      have h2 : 0 ≤ (1 + s) ^ 2 := by positivity
      nlinarith
    have hterm : 2 / r ≤ (1 / ((m : ℝ) * r)) * ((1 + s) ^ 2 * ((m : ℝ) * (2 - s) + 1)) := by
      calc 2 / r = (1 / ((m : ℝ) * r)) * (2 * (m : ℝ)) := by field_simp [hm_pos.ne', hr_pos.ne']
        _ ≤ (1 / ((m : ℝ) * r)) * ((1 + s) ^ 2 * ((m : ℝ) * (2 - s) + 1)) :=
          mul_le_mul_of_nonneg_left hfactor (by positivity)
    have hid : ((m : ℝ) * (1 - u) + 1 + 2 * (m : ℝ) * (2 - u)) -
        α * (2 - u) ^ 2 * ((m : ℝ) * (1 - u) + 1 + 2 * (m : ℝ) * u) =
        ((m : ℝ) * s ^ 3 - 2 * s - s ^ 2) +
          (1 / ((m : ℝ) * r)) * ((1 + s) ^ 2 * ((m : ℝ) * (2 - s) + 1)) := by
      dsimp [α, s]
      ring
    linarith

private lemma step_cone (k : ℕ) : InCone (fun u => Lstar (hsub k) u - hsub (k + 1) u) := by
  have hLk : InCone (Lstar (hsub k)) := Lstar_inCone (hsub_inCone k)
  have hk1 : InCone (hsub (k + 1)) := hsub_inCone (k + 1)
  have hmeas : Measurable (fun u => Lstar (hsub k) u - hsub (k + 1) u) := hLk.1.sub hk1.1
  set m : ℕ := k + 17
  set α : ℝ := 1 - 1 / ((m : ℝ) * Real.sqrt (m : ℝ))
  have hα_pos : 0 ≤ α := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hr1 : 1 ≤ Real.sqrt (m : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]; exact Real.sqrt_le_sqrt hm1
    have hmr : 1 ≤ (m : ℝ) * Real.sqrt (m : ℝ) := by nlinarith
    have : 1 / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr hmr
    linarith
  have hfk : InCone (f (k + 16)) := f_inCone (k + 16)
  have hfm : InCone (f m) := f_inCone m
  have hscale_L : ∀ u ∈ Icc (0 : ℝ) 1,
      Lstar (hsub k) u = ((1 / 528 : ℝ) * c k) * Lstar (f (k + 16)) u := by
    intro u hu
    rw [Lstar, Lstar, if_pos hu, if_pos hu, ← tsum_mul_left]
    congr 1; ext j
    dsimp [Lterm, hsub]; ring
  have hmono_f : MonotoneOn (fun u => Lstar (f (k + 16)) u - α * f m u) (Icc (0 : ℝ) 1) := by
    let A : ℝ → ℝ := fun u => f (k + 16) (1 / (2 - u)) / (2 - u) ^ 2 - α * f m u
    let B : ℝ → ℝ := fun u => -(f (k + 16) (1 / (2 + u)) / (2 + u) ^ 2)
    let R : ℝ → ℝ := fun u => ∑' j : ℕ, Lterm (f (k + 16)) (j + 1) u
    have hsplit : ∀ u ∈ Icc (0 : ℝ) 1,
        Lstar (f (k + 16)) u - α * f m u = A u + B u + R u := by
      intro u hu
      rw [Lstar, if_pos hu, (Lterm_summable hfk hu).tsum_eq_zero_add]
      dsimp [A, B, R, Lterm]
      ring
    have hA : MonotoneOn A (Icc (0 : ℝ) 1) := by
      have hm1 : m - 1 = k + 16 := by omega
      simpa [A, hm1, α] using f_step_monoOn m (by omega)
    have hB : MonotoneOn B (Icc (0 : ℝ) 1) := by
      intro u hu v hv huv
      dsimp [B]
      have hu2 : 0 < 2 + u := by linarith [hu.1]
      have hv2 : 0 < 2 + v := by linarith [hv.1]
      have h1 := hfk.2.2 (inv_add_mem 0 hv) (inv_add_mem 0 hu)
        (by simpa using one_div_le_one_div_of_le hu2 (by linarith : 2 + u ≤ 2 + v))
      have h2 : (2 + u) ^ 2 ≤ (2 + v) ^ 2 := by nlinarith [hu.1, hv.1]
      have hnn : 0 ≤ f (k + 16) (1 / (2 + v)) := by
        simpa using hfk.2.1 _ (inv_add_mem 0 hv)
      have hle : f (k + 16) (1 / (2 + v)) / (2 + v) ^ 2 ≤ f (k + 16) (1 / (2 + u)) / (2 + u) ^ 2 := by
        calc _ ≤ f (k + 16) (1 / (2 + v)) / (2 + u) ^ 2 :=
              div_le_div_of_nonneg_left hnn (by positivity) h2
          _ ≤ f (k + 16) (1 / (2 + u)) / (2 + u) ^ 2 :=
              div_le_div_of_nonneg_right (by simpa using h1) (by positivity)
      linarith
    have hR : MonotoneOn R (Icc (0 : ℝ) 1) := by
      intro u hu v hv huv
      dsimp [R]
      exact ((Lterm_summable hfk hu).comp_injective Nat.succ_injective).tsum_le_tsum
        (fun j => Lterm_monoOn hfk (j + 1) hu hv huv)
        ((Lterm_summable hfk hv).comp_injective Nat.succ_injective)
    intro u hu v hv huv
    dsimp only
    rw [hsplit u hu, hsplit v hv]
    exact add_le_add (add_le_add (hA hu hv huv) (hB hu hv huv)) (hR hu hv huv)
  have hmono : MonotoneOn (fun u => Lstar (hsub k) u - hsub (k + 1) u) (Icc (0 : ℝ) 1) := by
    have hc_gap : 0 ≤ (1 / 528 : ℝ) * (c k * α - c (k + 1)) := by
      have hcs := c_step k
      have hcast : ((m : ℝ)) = (k : ℝ) + 17 := by dsimp [m]; push_cast; ring
      have : c (k + 1) ≤ c k * α := by dsimp [α]; rw [hcast]; exact hcs
      linarith
    have hck_nn : 0 ≤ (1 / 528 : ℝ) * c k := by have := c_ge_one k; positivity
    intro u hu v hv huv
    have heq (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
        Lstar (hsub k) x - hsub (k + 1) x =
          ((1 / 528 : ℝ) * c k) * (Lstar (f (k + 16)) x - α * f m x) +
            ((1 / 528 : ℝ) * (c k * α - c (k + 1))) * f m x := by
      rw [hscale_L x hx]
      have hm_eq : k + 1 + 16 = m := by omega
      dsimp [hsub]
      rw [hm_eq]
      ring
    dsimp only
    rw [heq u hu, heq v hv]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hmono_f hu hv huv) hck_nn)
      (mul_le_mul_of_nonneg_left (hfm.2.2 hu hv huv) hc_gap)
  refine ⟨hmeas, ?_, hmono⟩
  intro u hu
  have h0 : Lstar (hsub k) 0 - hsub (k + 1) 0 = 0 := by
    rw [Lstar_zero]; simp [hsub, f]
  have := hmono ⟨le_rfl, zero_le_one⟩ hu hu.1
  linarith

private lemma iter_ge_hsub (k : ℕ) :
    InCone (fun u => (Lstar^[k + 1] (fun _ => 1)) u - hsub k u) := by
  have h1c : InCone (fun _ : ℝ => (1 : ℝ)) := ⟨measurable_const, fun _ _ => zero_le_one, monotoneOn_const⟩
  induction k with
  | zero => exact base_cone
  | succ k ih =>
    have h1 : InCone (Lstar^[k + 1] (fun _ => 1)) := Lstar_iter_inCone h1c (k + 1)
    have h2 : InCone (fun u => Lstar (Lstar^[k + 1] (fun _ => 1)) u - Lstar (hsub k) u) :=
      Lstar_mono_cone h1 (hsub_inCone k) ih
    have h3 : InCone (fun u => Lstar (hsub k) u - hsub (k + 1) u) := step_cone k
    have hsum := h2.add h3
    convert hsum using 1
    ext u
    rw [Function.iterate_succ_apply']
    ring

private lemma integral_f_ge (m : ℕ) (hm : 16 ≤ m) :
    1 / (8 * (m : ℝ)) ≤ ∫ u in (0 : ℝ)..1, f m u := by
  have hm_pos : (0 : ℝ) < m := by positivity
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  set a : ℝ := 1 - 1 / (m : ℝ)
  have ha0 : 0 ≤ a := by
    have : 1 / (m : ℝ) ≤ 1 := (div_le_one hm_pos).mpr (by linarith)
    linarith
  have ha1 : a ≤ 1 := by
    have : 0 ≤ 1 / (m : ℝ) := by positivity
    linarith
  have hint_f : IntervalIntegrable (f m) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr (integrableOn_cone (f_inCone m))
  have hint_f1 : IntervalIntegrable (f m) volume 0 a := hint_f.mono_set (by
    rw [Set.uIcc_of_le ha0, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc_right ha1)
  have hint_f2 : IntervalIntegrable (f m) volume a 1 := hint_f.mono_set (by
    rw [Set.uIcc_of_le ha1, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc_left ha0)
  have hsplit : ∫ u in (0 : ℝ)..1, f m u = (∫ u in (0 : ℝ)..a, f m u) + ∫ u in a..1, f m u :=
    (intervalIntegral.integral_add_adjacent_intervals hint_f1 hint_f2).symm
  have hpart1 : 0 ≤ ∫ u in (0 : ℝ)..a, f m u := by
    refine intervalIntegral.integral_nonneg ha0 fun u hu => ?_
    exact (f_inCone m).2.1 u ⟨hu.1, hu.2.trans ha1⟩
  have hpart2 : 1 / (8 * (m : ℝ)) ≤ ∫ u in a..1, f m u := by
    have hconst : ∫ _ in a..1, (1 / 8 : ℝ) = 1 / (8 * (m : ℝ)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      dsimp [a]; field_simp [hm_pos.ne']; ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_on ha1 intervalIntegrable_const hint_f2 fun u hu => ?_
    have hu_half : (1 / 2 : ℝ) ≤ u := by
      have : 1 / (m : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm2
      linarith [hu.1]
    have hden_le : (m : ℝ) * (1 - u) + 1 ≤ 2 := by
      have h1u : 1 - u ≤ 1 / (m : ℝ) := by linarith [hu.1]
      have hmul : (m : ℝ) * (1 - u) ≤ 1 := by
        calc (m : ℝ) * (1 - u) ≤ (m : ℝ) * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_left h1u hm_pos.le
          _ = 1 := mul_one_div_cancel hm_pos.ne'
      linarith
    have hden_pos : 0 < (m : ℝ) * (1 - u) + 1 := by linarith [f_denom_pos m ⟨ha0.trans hu.1, hu.2⟩]
    dsimp [f]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  linarith

private lemma harmonic_unbounded : ∀ B : ℝ, ∃ N : ℕ,
    B < ∑ k ∈ Finset.range N, 1 / (4224 * ((k : ℝ) + 16)) := by
  intro B
  by_contra h
  push Not at h
  have hsum : Summable (fun k : ℕ => 1 / (4224 * ((k : ℝ) + 16))) :=
    summable_of_sum_range_le (fun k => by positivity) h
  have hshift : Summable (fun k : ℕ => 1 / ((k : ℝ) + 16)) := by
    have h' := hsum.mul_left (4224 : ℝ)
    refine h'.congr fun k => ?_
    field_simp
  have hnat : Summable (fun n : ℕ => ((n : ℝ))⁻¹) := by
    rw [← summable_nat_add_iff 16]
    refine hshift.congr fun k => ?_
    simp [one_div]
  exact Real.not_summable_natCast_inv hnat

end

end OMA.P_Arxiv_2501_03234_H1

theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_4_4_R1.H1 := by
  intro B
  obtain ⟨N, hN⟩ := OMA.P_Arxiv_2501_03234_H1.harmonic_unbounded B
  refine ⟨N + 1, ?_⟩
  have h1c : OMA.P_Arxiv_2501_03234_H1.InCone (fun _ : ℝ => (1 : ℝ)) :=
    ⟨measurable_const, fun _ _ => zero_le_one, monotoneOn_const⟩
  have hEq : ∫ x in (0 : ℝ)..1, OMA.P_Arxiv_2501_03234_H1.E (N + 1) x =
      ∑ j ∈ Finset.range (N + 1),
        ∫ x in (0 : ℝ)..1, (OMA.P_Arxiv_2501_03234_H1.Lstar^[j] (fun _ => 1)) x := by
    simpa [one_mul] using OMA.P_Arxiv_2501_03234_H1.integral_mul_E_eq_sum (N + 1) h1c
  change B < ∫ x in (0 : ℝ)..1, OMA.P_Arxiv_2501_03234_H1.E (N + 1) x
  rw [hEq, Finset.sum_range_succ']
  have h0_nn : 0 ≤ ∫ x in (0 : ℝ)..1, (OMA.P_Arxiv_2501_03234_H1.Lstar^[0] (fun _ => 1)) x := by
    simp
  have hterm : ∀ k ∈ Finset.range N,
      1 / (4224 * ((k : ℝ) + 16)) ≤
        ∫ x in (0 : ℝ)..1, (OMA.P_Arxiv_2501_03234_H1.Lstar^[k + 1] (fun _ => 1)) x := by
    intro k _
    have hdiff := OMA.P_Arxiv_2501_03234_H1.iter_ge_hsub k
    have hL_cone : OMA.P_Arxiv_2501_03234_H1.InCone
        (OMA.P_Arxiv_2501_03234_H1.Lstar^[k + 1] (fun _ => 1)) :=
      OMA.P_Arxiv_2501_03234_H1.Lstar_iter_inCone h1c (k + 1)
    have hint_L : IntervalIntegrable
        (OMA.P_Arxiv_2501_03234_H1.Lstar^[k + 1] (fun _ => 1)) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
      exact OMA.P_Arxiv_2501_03234_H1.integrableOn_cone hL_cone
    have hint_f : IntervalIntegrable
        (fun u => (1 / 528 : ℝ) * OMA.P_Arxiv_2501_03234_H1.f (k + 16) u) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
      exact OMA.P_Arxiv_2501_03234_H1.integrableOn_cone
        ((OMA.P_Arxiv_2501_03234_H1.f_inCone (k + 16)).smul (by norm_num))
    have hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (1 / 528 : ℝ) * OMA.P_Arxiv_2501_03234_H1.f (k + 16) u ≤
          (OMA.P_Arxiv_2501_03234_H1.Lstar^[k + 1] (fun _ => 1)) u := by
      intro u hu
      have hge1 : 0 ≤ (OMA.P_Arxiv_2501_03234_H1.Lstar^[k + 1] (fun _ => 1)) u -
          OMA.P_Arxiv_2501_03234_H1.hsub k u := hdiff.2.1 u hu
      have hge2 : (1 / 528 : ℝ) * OMA.P_Arxiv_2501_03234_H1.f (k + 16) u ≤
          OMA.P_Arxiv_2501_03234_H1.hsub k u := by
        dsimp [OMA.P_Arxiv_2501_03234_H1.hsub]
        have hfnn := (OMA.P_Arxiv_2501_03234_H1.f_inCone (k + 16)).2.1 u hu
        have hc1 := OMA.P_Arxiv_2501_03234_H1.c_ge_one k
        nlinarith
      linarith
    have hmono := intervalIntegral.integral_mono_on zero_le_one hint_f hint_L hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    have hf_ge := OMA.P_Arxiv_2501_03234_H1.integral_f_ge (k + 16) (by omega)
    have hcast : ((k + 16 : ℕ) : ℝ) = (k : ℝ) + 16 := by push_cast; ring
    rw [hcast] at hf_ge
    calc 1 / (4224 * ((k : ℝ) + 16))
        = (1 / 528 : ℝ) * (1 / (8 * ((k : ℝ) + 16))) := by field_simp; ring
      _ ≤ (1 / 528 : ℝ) * ∫ u in (0 : ℝ)..1, OMA.P_Arxiv_2501_03234_H1.f (k + 16) u :=
          mul_le_mul_of_nonneg_left hf_ge (by norm_num)
      _ ≤ ∫ x in (0 : ℝ)..1, (OMA.P_Arxiv_2501_03234_H1.Lstar^[k + 1] (fun _ => 1)) x := hmono
  have hsum_le := Finset.sum_le_sum hterm
  linarith
