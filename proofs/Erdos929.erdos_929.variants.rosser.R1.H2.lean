import OMAReductions.R_Erdos929_erdos_929_variants_rosser_R1

-- Step Erdos929.erdos_929.variants.rosser.R1.H2: hypothesis H2 of reduction Erdos929.erdos_929.variants.rosser.R1
-- Credit: @loremcdmx
-- H2 := ∀ (T : Set ℕ) (m : ℕ), 0 < m →   (∀ n : ℕ, n+m∈T ↔ n∈T) → (T.HasPosDensity ↔ T.Nonempty)

namespace OMA.Aux

open Classical Filter Topology

lemma per_mul (T : Set ℕ) (m : ℕ) (hper : ∀ n : ℕ, n + m ∈ T ↔ n ∈ T) :
    ∀ j n : ℕ, n + j * m ∈ T ↔ n ∈ T := by
  intro j
  induction j with
  | zero => intro n; simp
  | succ j ih =>
    intro n
    have : n + (j + 1) * m = (n + j * m) + m := by ring
    rw [this, hper, ih]

lemma ncard_bridge (T : Set ℕ) (b : ℕ) :
    ((T ∩ Set.univ) ∩ Set.Iio b).ncard = Nat.count (fun n => n ∈ T) b := by
  classical
  have : (T ∩ Set.univ) ∩ Set.Iio b = (((Finset.range b).filter (fun n => n ∈ T) : Finset ℕ) : Set ℕ) := by
    ext x; simp [and_comm]
  rw [this, Set.ncard_coe_finset, Nat.count_eq_card_filter_range]

lemma ncard_univ (b : ℕ) : (Set.univ ∩ Set.Iio b : Set ℕ).ncard = b := by
  have : (Set.univ ∩ Set.Iio b : Set ℕ) = ((Finset.range b : Finset ℕ) : Set ℕ) := by
    ext x; simp
  rw [this, Set.ncard_coe_finset, Finset.card_range]

lemma pd_eq (T : Set ℕ) (b : ℕ) :
    T.partialDensity Set.univ b = (Nat.count (fun n => n ∈ T) b : ℝ) / b := by
  unfold Set.partialDensity
  rw [ncard_bridge, ncard_univ]

lemma count_mul (T : Set ℕ) (m : ℕ) (hper : ∀ n : ℕ, n + m ∈ T ↔ n ∈ T) (q : ℕ) :
    Nat.count (fun n => n ∈ T) (q * m) = q * Nat.count (fun n => n ∈ T) m := by
  classical
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : (q + 1) * m = q * m + m := by ring
    rw [h1, Nat.count_add, ih]
    have : (fun k => (q * m + k) ∈ T) = (fun n => n ∈ T) := by
      funext k
      apply propext
      rw [add_comm (q*m) k]
      exact per_mul T m hper q k
    simp only [this]
    ring

lemma has_density (T : Set ℕ) (m : ℕ) (hm : 0 < m) (hper : ∀ n : ℕ, n + m ∈ T ↔ n ∈ T) :
    T.HasDensity ((Nat.count (fun n => n ∈ T) m : ℝ) / m) Set.univ := by
  classical
  set c := Nat.count (fun n => n ∈ T) m with hc
  unfold Set.HasDensity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlow : Tendsto (fun b : ℕ => (c : ℝ) / m - c / b) atTop (𝓝 ((c : ℝ) / m - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
  have hup : Tendsto (fun b : ℕ => (c : ℝ) / m + c / b) atTop (𝓝 ((c : ℝ) / m + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [sub_zero] at hlow
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  all_goals
    filter_upwards [eventually_gt_atTop 0] with b hb
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    rw [pd_eq]
    set q := b / m with hq
    have h1 : q * m ≤ b := Nat.div_mul_le_self b m
    have h2 : b < (q + 1) * m := by
      have := Nat.lt_div_mul_add (a := b) hm
      rw [hq]; nlinarith [Nat.div_add_mod b m, Nat.mod_lt b hm]
    have hlo : q * c ≤ Nat.count (fun n => n ∈ T) b := by
      rw [← count_mul T m hper q]; exact Nat.count_monotone _ h1
    have hhi : Nat.count (fun n => n ∈ T) b ≤ (q + 1) * c := by
      rw [← count_mul T m hper (q+1)]; exact Nat.count_monotone _ h2.le
    have hloR : (q : ℝ) * c ≤ Nat.count (fun n => n ∈ T) b := by exact_mod_cast hlo
    have hhiR : (Nat.count (fun n => n ∈ T) b : ℝ) ≤ ((q : ℝ) + 1) * c := by exact_mod_cast hhi
    have h1R : (q : ℝ) * m ≤ b := by exact_mod_cast h1
    have h2R : (b : ℝ) < ((q : ℝ) + 1) * m := by exact_mod_cast h2
    have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  · have key : (c : ℝ) * b - m * c ≤ Nat.count (fun n => n ∈ T) b * m := by
      nlinarith [mul_le_mul_of_nonneg_right hloR hmR.le, mul_le_mul_of_nonneg_left h2R.le hcR]
    rw [div_sub_div _ _ hmR.ne' hbR.ne', div_le_div_iff₀ (by positivity) hbR]
    nlinarith [mul_le_mul_of_nonneg_right key hbR.le]
  · have key : (Nat.count (fun n => n ∈ T) b : ℝ) * m ≤ c * b + c * m := by
      nlinarith [mul_le_mul_of_nonneg_right hhiR hmR.le, mul_le_mul_of_nonneg_left h1R hcR]
    rw [div_add_div _ _ hmR.ne' hbR.ne', div_le_div_iff₀ hbR (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right key hbR.le]

end OMA.Aux

theorem OMA.solution : OMA.R_Erdos929_erdos_929_variants_rosser_R1.H2 := by
  classical
  intro T m hm hper
  constructor
  · rintro ⟨α, hα, hd⟩
    by_contra hne
    have hT : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst hT
    have : Filter.Tendsto (fun b : ℕ => (∅ : Set ℕ).partialDensity Set.univ b) Filter.atTop (nhds 0) := by
      have : (fun b : ℕ => (∅ : Set ℕ).partialDensity Set.univ b) = fun _ => 0 := by
        funext b; simp [Set.partialDensity]
      rw [this]; exact tendsto_const_nhds
    exact hα.ne' (tendsto_nhds_unique hd this)
  · rintro ⟨a, ha⟩
    have hmem : a % m ∈ T := by
      have := OMA.Aux.per_mul T m hper (a / m) (a % m)
      rw [Nat.mod_add_div'] at this
      exact this.mp ha
    have hc : 0 < Nat.count (fun n => n ∈ T) m :=
      by
        rw [Nat.count_eq_card_filter_range]
        exact Finset.card_pos.mpr ⟨a % m, by simp [Nat.mod_lt a hm, hmem]⟩
    refine ⟨_, ?_, OMA.Aux.has_density T m hm hper⟩
    have : (0:ℝ) < m := by exact_mod_cast hm
    have : (0:ℝ) < Nat.count (fun n => n ∈ T) m := by exact_mod_cast hc
    positivity
