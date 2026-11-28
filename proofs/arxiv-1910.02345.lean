import OMAStatements.S_arxiv_1910_02345
import Mathlib

namespace OMA.P_arxiv_1910_02345

open MeasureTheory Set Finset
open scoped BigOperators Pointwise

/-! ### Part 1: Finite Four Functions Theorem (Ahlswede-Daykin on finite grids) -/

private lemma four_functions_two {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (h11 : a₁ * b₁ ≤ c₁ * d₁) (h12 : a₁ * b₂ ≤ c₁ * d₂)
    (h21 : a₂ * b₁ ≤ c₁ * d₂) (h22 : a₂ * b₂ ≤ c₂ * d₂) :
    (a₁ + a₂) * (b₁ + b₂) ≤ (c₁ + c₂) * (d₁ + d₂) := by
  by_cases h0 : c₁ * d₂ = 0
  · have h12' : a₁ * b₂ = 0 := le_antisymm (h12.trans h0.le) (mul_nonneg ha₁ hb₂)
    have h21' : a₂ * b₁ = 0 := le_antisymm (h21.trans h0.le) (mul_nonneg ha₂ hb₁)
    have hc2d1 : 0 ≤ c₂ * d₁ := mul_nonneg hc₂ hd₁
    nlinarith
  · have hpos : 0 < c₁ * d₂ := lt_of_le_of_ne (mul_nonneg hc₁ hd₂) (Ne.symm h0)
    have hmul : (a₁ + a₂) * (b₁ + b₂) * (c₁ * d₂) ≤ (c₁ + c₂) * (d₁ + d₂) * (c₁ * d₂) := by
      have t1 : 0 ≤ (c₁ * d₂ - a₁ * b₂) * (c₁ * d₂ - a₂ * b₁) :=
        mul_nonneg (sub_nonneg.mpr h12) (sub_nonneg.mpr h21)
      have t2 : 0 ≤ (c₁ * d₁ - a₁ * b₁) * (c₁ * d₂) :=
        mul_nonneg (sub_nonneg.mpr h11) hpos.le
      have t3 : 0 ≤ (c₂ * d₂ - a₂ * b₂) * (c₁ * d₂) :=
        mul_nonneg (sub_nonneg.mpr h22) hpos.le
      have t4 : 0 ≤ c₁ * d₁ * (c₂ * d₂) - a₁ * b₁ * (a₂ * b₂) := by
        have := mul_le_mul h11 h22 (mul_nonneg ha₂ hb₂) (mul_nonneg hc₁ hd₁)
        linarith
      linarith [show (c₁ + c₂) * (d₁ + d₂) * (c₁ * d₂) - (a₁ + a₂) * (b₁ + b₂) * (c₁ * d₂) =
        (c₁ * d₂ - a₁ * b₂) * (c₁ * d₂ - a₂ * b₁) +
        (c₁ * d₁ - a₁ * b₁) * (c₁ * d₂) +
        (c₂ * d₂ - a₂ * b₂) * (c₁ * d₂) +
        (c₁ * d₁ * (c₂ * d₂) - a₁ * b₁ * (a₂ * b₂)) by ring]
    exact le_of_mul_le_mul_right hmul hpos

private lemma four_functions_fin :
    ∀ (n : ℕ) (a b c d : Fin n → ℝ),
      (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ c i) → (∀ i, 0 ≤ d i) →
      (∀ i j, a i * b j ≤ c (min i j) * d (max i j)) →
      (∑ i, a i) * (∑ j, b j) ≤ (∑ i, c i) * (∑ j, d j)
  | 0, _, _, _, _, _, _, _, _, _ => by simp
  | 1, a, b, c, d, _, _, _, _, h => by
      simpa using h 0 0
  | n + 2, a, b, c, d, ha, hb, hc, hd, h => by
      let collapse (f : Fin (n + 2) → ℝ) (i : Fin (n + 1)) : ℝ :=
        if i = Fin.last n then f (Fin.last n).castSucc + f (Fin.last (n + 1))
        else f i.castSucc
      have hsum : ∀ f : Fin (n + 2) → ℝ, ∑ i : Fin (n + 1), collapse f i = ∑ i : Fin (n + 2), f i := by
        intro f
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
        have h1 : ∀ i : Fin n, collapse f i.castSucc = f i.castSucc.castSucc := by
          intro i
          simp only [collapse, Fin.castSucc_ne_last, ↓reduceIte]
        simp only [h1, collapse, ↓reduceIte]
        ring
      have hnn : ∀ (f : Fin (n + 2) → ℝ), (∀ i, 0 ≤ f i) → ∀ i, 0 ≤ collapse f i := by
        intro f hf i
        simp only [collapse]
        split_ifs
        · exact add_nonneg (hf _) (hf _)
        · exact hf _
      have hle : ∀ i j : Fin (n + 1),
          collapse a i * collapse b j ≤ collapse c (min i j) * collapse d (max i j) := by
        intro i j
        by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n
        · subst hi; subst hj
          simp only [min_self, max_self, collapse, ↓reduceIte]
          have hlt : (Fin.last n).castSucc ≤ Fin.last (n + 1) := Fin.le_last _
          have h11 := h (Fin.last n).castSucc (Fin.last n).castSucc
          have h12 := h (Fin.last n).castSucc (Fin.last (n + 1))
          have h21 := h (Fin.last (n + 1)) (Fin.last n).castSucc
          have h22 := h (Fin.last (n + 1)) (Fin.last (n + 1))
          simp only [min_self, max_self, min_eq_left hlt, max_eq_right hlt,
            min_eq_right hlt, max_eq_left hlt] at h11 h12 h21 h22
          exact four_functions_two (ha _) (ha _) (hb _) (hb _) (hc _) (hc _) (hd _) (hd _)
            h11 h12 h21 h22
        · subst hi
          have hlt : j < Fin.last n := lt_of_le_of_ne (Fin.le_last j) hj
          have hmin : min (Fin.last n) j = j := min_eq_right (Fin.le_last j)
          have hmax : max (Fin.last n) j = Fin.last n := max_eq_left (Fin.le_last j)
          rw [hmin, hmax]
          simp only [collapse, ↓reduceIte, hj]
          have h1 := h (Fin.last n).castSucc j.castSucc
          have h2 := h (Fin.last (n + 1)) j.castSucc
          have hj1 : j.castSucc ≤ (Fin.last n).castSucc := Fin.castSucc_le_castSucc_iff.mpr hlt.le
          have hj2 : j.castSucc ≤ Fin.last (n + 1) := Fin.le_last _
          simp only [min_eq_right hj1, max_eq_left hj1, min_eq_right hj2, max_eq_left hj2] at h1 h2
          linarith
        · subst hj
          have hlt : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hi
          have hmin : min i (Fin.last n) = i := min_eq_left (Fin.le_last i)
          have hmax : max i (Fin.last n) = Fin.last n := max_eq_right (Fin.le_last i)
          rw [hmin, hmax]
          simp only [collapse, ↓reduceIte, hi]
          have h1 := h i.castSucc (Fin.last n).castSucc
          have h2 := h i.castSucc (Fin.last (n + 1))
          have hi1 : i.castSucc ≤ (Fin.last n).castSucc := Fin.castSucc_le_castSucc_iff.mpr hlt.le
          have hi2 : i.castSucc ≤ Fin.last (n + 1) := Fin.le_last _
          simp only [min_eq_left hi1, max_eq_right hi1, min_eq_left hi2, max_eq_right hi2] at h1 h2
          linarith
        · have hmin_ne : min i j ≠ Fin.last n := by
            intro heq
            have : i = Fin.last n := le_antisymm (Fin.le_last i) (heq ▸ min_le_left i j)
            exact hi this
          have hmax_ne : max i j ≠ Fin.last n := by
            rcases le_total i j with hij | hji
            · rwa [max_eq_right hij]
            · rwa [max_eq_left hji]
          simp only [collapse, hi, hj, hmin_ne, hmax_ne, ↓reduceIte]
          have hcast_min : (min i j).castSucc = min i.castSucc j.castSucc :=
            Monotone.map_min (fun _ _ h => Fin.castSucc_le_castSucc_iff.mpr h)
          have hcast_max : (max i j).castSucc = max i.castSucc j.castSucc :=
            Monotone.map_max (fun _ _ h => Fin.castSucc_le_castSucc_iff.mpr h)
          rw [hcast_min, hcast_max]
          exact h i.castSucc j.castSucc
      have ih := four_functions_fin (n + 1) (collapse a) (collapse b) (collapse c) (collapse d)
        (hnn a ha) (hnn b hb) (hnn c hc) (hnn d hd) hle
      rwa [hsum a, hsum b, hsum c, hsum d] at ih

private lemma four_functions_pi :
    ∀ (d m : ℕ) (a b c df : (Fin d → Fin m) → ℝ),
      (∀ x, 0 ≤ a x) → (∀ x, 0 ≤ b x) → (∀ x, 0 ≤ c x) → (∀ x, 0 ≤ df x) →
      (∀ x y, a x * b y ≤ c (x ⊓ y) * df (x ⊔ y)) →
      (∑ x, a x) * (∑ y, b y) ≤ (∑ x, c x) * (∑ y, df y)
  | 0, m, a, b, c, df, _, _, _, _, h => by
      simpa using h default default
  | d + 1, m, a, b, c, df, ha, hb, hc, hdf, h => by
      let A (i : Fin m) : ℝ := ∑ z : Fin d → Fin m, a (Fin.cons i z)
      let B (i : Fin m) : ℝ := ∑ z : Fin d → Fin m, b (Fin.cons i z)
      let C (i : Fin m) : ℝ := ∑ z : Fin d → Fin m, c (Fin.cons i z)
      let D (i : Fin m) : ℝ := ∑ z : Fin d → Fin m, df (Fin.cons i z)
      have hsum_eq : ∀ f : (Fin (d + 1) → Fin m) → ℝ,
          ∑ x : Fin (d + 1) → Fin m, f x = ∑ i : Fin m, ∑ z : Fin d → Fin m, f (Fin.cons i z) := by
        intro f
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d + 1) => Fin m)).symm _ _
          (fun x => by simp [Fin.consEquiv])
      have hle : ∀ i j : Fin m, A i * B j ≤ C (min i j) * D (max i j) := by
        intro i j
        refine four_functions_pi d m
          (fun z => a (Fin.cons i z)) (fun z => b (Fin.cons j z))
          (fun z => c (Fin.cons (min i j) z)) (fun z => df (Fin.cons (max i j) z))
          (fun z => ha _) (fun z => hb _) (fun z => hc _) (fun z => hdf _) ?_
        intro z w
        have hinf : (Fin.cons i z : Fin (d + 1) → Fin m) ⊓ Fin.cons j w =
            Fin.cons (min i j) (z ⊓ w) := by
          ext k
          refine Fin.cases ?_ ?_ k <;> simp
        have hsup : (Fin.cons i z : Fin (d + 1) → Fin m) ⊔ Fin.cons j w =
            Fin.cons (max i j) (z ⊔ w) := by
          ext k
          refine Fin.cases ?_ ?_ k <;> simp
        rw [← hinf, ← hsup]
        exact h (Fin.cons i z) (Fin.cons j w)
      rw [hsum_eq a, hsum_eq b, hsum_eq c, hsum_eq df]
      exact four_functions_fin m A B C D
        (fun i => Finset.sum_nonneg (fun z _ => ha _))
        (fun i => Finset.sum_nonneg (fun z _ => hb _))
        (fun i => Finset.sum_nonneg (fun z _ => hc _))
        (fun i => Finset.sum_nonneg (fun z _ => hdf _))
        hle

/-! ### Part 2: Grid Averaging and Continuous Four Functions Theorem -/

private def unitCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1

private def gridShift (d : ℕ) (h : ℝ) (N : ℕ) (k : Fin d → Fin (2 * N + 1)) : Fin d → ℝ :=
  fun i => h * ((k i : ℝ) - N)

private def gridBox (d : ℕ) (h : ℝ) (N : ℕ) (k : Fin d → Fin (2 * N + 1)) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i => Set.Ico (gridShift d h N k i) (gridShift d h N k i + h)

private def gridSum (d : ℕ) (h : ℝ) (N : ℕ) (g : (Fin d → ℝ) → ℝ) (v : Fin d → ℝ) : ℝ :=
  h ^ d * ∑ k : Fin d → Fin (2 * N + 1), g (h • v + gridShift d h N k)

private lemma measurableSet_unitCube (d : ℕ) : MeasurableSet (unitCube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

private lemma volume_unitCube (d : ℕ) : volume (unitCube d) = 1 := by
  simp [unitCube, Real.volume_pi_Ico]

private lemma measurableSet_gridBox (d : ℕ) (h : ℝ) (N : ℕ) (k : Fin d → Fin (2 * N + 1)) :
    MeasurableSet (gridBox d h N k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

private lemma volume_gridBox (d : ℕ) {h : ℝ} (hh : 0 ≤ h) (N : ℕ) (k : Fin d → Fin (2 * N + 1)) :
    volume (gridBox d h N k) = ENNReal.ofReal (h ^ d) := by
  simp [gridBox, Real.volume_pi_Ico, ENNReal.ofReal_pow hh]

private lemma gridBox_eq_image (d : ℕ) {h : ℝ} (hh : 0 < h) (N : ℕ)
    (k : Fin d → Fin (2 * N + 1)) :
    gridBox d h N k = (fun x => x + gridShift d h N k) '' (h • unitCube d) := by
  ext x
  simp only [gridBox, unitCube, Set.mem_univ_pi, Set.mem_Ico, Set.mem_image, Set.mem_smul_set]
  constructor
  · intro hx
    refine ⟨x - gridShift d h N k, ?_, sub_add_cancel x _⟩
    refine ⟨h⁻¹ • (x - gridShift d h N k), ?_, smul_inv_smul₀ hh.ne' _⟩
    intro i
    have hxi := hx i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hh.le) (sub_nonneg.mpr hxi.1)
    · rw [inv_mul_lt_iff₀ hh, mul_one]
      linarith
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩ i
    have hvi := hv i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · linarith [mul_nonneg hh.le hvi.1]
    · nlinarith

private lemma pairwise_disjoint_gridBox (d : ℕ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    Pairwise (Function.onFun Disjoint (gridBox d h N)) := by
  intro k₁ k₂ hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx₁ hx₂
  have hex : ∃ i, k₁ i ≠ k₂ i := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  rcases hex with ⟨i, hi⟩
  have h1 := hx₁ i (Set.mem_univ i)
  have h2 := hx₂ i (Set.mem_univ i)
  simp only [Set.mem_Ico, gridShift] at h1 h2
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hnat : (k₁ i : ℝ) + 1 ≤ (k₂ i : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.mp hlt)
    nlinarith
  · have hnat : (k₂ i : ℝ) + 1 ≤ (k₁ i : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.mp hgt)
    nlinarith

private lemma setIntegral_comp_smul_add (d : ℕ) {h : ℝ} (hh : 0 < h) (c : Fin d → ℝ)
    (g : (Fin d → ℝ) → ℝ) :
    h ^ d * ∫ v in unitCube d, g (h • v + c) =
      ∫ x in (fun y => y + c) '' (h • unitCube d), g x := by
  have h1 : ∫ v in unitCube d, g (h • v + c) =
      (h ^ d)⁻¹ * ∫ y in h • unitCube d, g (y + c) := by
    have := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Fin d → ℝ))
      (fun y => g (y + c)) (unitCube d) hh
    simpa [Module.finrank_fin_fun] using this
  have h2 : ∫ y in h • unitCube d, g (y + c) =
      ∫ x in (fun y => y + c) '' (h • unitCube d), g x := by
    let e : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) := MeasurableEquiv.addRight c
    have hmp : MeasurePreserving e volume volume := measurePreserving_add_right volume c
    have himg : e ⁻¹' ((fun y => y + c) '' (h • unitCube d)) = h • unitCube d := by
      ext y
      simp [e]
    calc ∫ y in h • unitCube d, g (y + c)
        = ∫ y in e ⁻¹' ((fun y => y + c) '' (h • unitCube d)), g (e y) := by rw [himg]; rfl
      _ = ∫ x in (fun y => y + c) '' (h • unitCube d), g x ∂(volume.map e) :=
          (setIntegral_map_equiv e g _).symm
      _ = ∫ x in (fun y => y + c) '' (h • unitCube d), g x := by rw [hmp.map_eq]
  rw [h1, h2, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hh.ne'), one_mul]

private lemma integrable_comp_smul_add (d : ℕ) {h : ℝ} (hh : 0 < h) (c : Fin d → ℝ)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g) :
    Integrable (fun v => g (h • v + c)) := by
  have h1 : Integrable (fun y => g (y + c)) := hg.comp_add_right c
  have h2 : Integrable (fun v => (fun y => g (y + c)) (h • v)) :=
    h1.comp_smul hh.ne'
  exact h2

private lemma integrableOn_gridSum (d : ℕ) {h : ℝ} (hh : 0 < h) (N : ℕ)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g) :
    IntegrableOn (gridSum d h N g) (unitCube d) := by
  unfold gridSum
  refine Integrable.const_mul ?_ _
  exact integrable_finsetSum _ fun k _ => (integrable_comp_smul_add d hh _ hg).integrableOn

private lemma setIntegral_gridSum (d : ℕ) {h : ℝ} (hh : 0 < h) (N : ℕ)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g) :
    ∫ v in unitCube d, gridSum d h N g v =
      ∫ x in ⋃ k : Fin d → Fin (2 * N + 1), gridBox d h N k, g x := by
  unfold gridSum
  rw [integral_const_mul, integral_finsetSum _ fun k _ =>
    (integrable_comp_smul_add d hh _ hg).integrableOn]
  rw [Finset.mul_sum]
  have hterm : ∀ k : Fin d → Fin (2 * N + 1),
      h ^ d * ∫ v in unitCube d, g (h • v + gridShift d h N k) =
        ∫ x in gridBox d h N k, g x := by
    intro k
    rw [gridBox_eq_image d hh N k]
    exact setIntegral_comp_smul_add d hh (gridShift d h N k) g
  simp_rw [hterm]
  rw [← integral_iUnion_fintype (fun k => measurableSet_gridBox d h N k)
    (pairwise_disjoint_gridBox d hh N) (fun k => hg.integrableOn)]

private lemma setIntegral_gridSum_le (d : ℕ) {h : ℝ} (hh : 0 < h) (N : ℕ)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g) (hnn : ∀ x, 0 ≤ g x) :
    ∫ v in unitCube d, gridSum d h N g v ≤ ∫ x, g x := by
  rw [setIntegral_gridSum d hh N hg]
  exact setIntegral_le_integral hg (ae_of_all _ hnn)

private lemma gridSum_nonneg (d : ℕ) {h : ℝ} (hh : 0 ≤ h) (N : ℕ)
    {g : (Fin d → ℝ) → ℝ} (hnn : ∀ x, 0 ≤ g x) (v : Fin d → ℝ) :
    0 ≤ gridSum d h N g v :=
  mul_nonneg (pow_nonneg hh d) (Finset.sum_nonneg fun _ _ => hnn _)

private lemma gridSum_four_functions (d : ℕ) {h : ℝ} (hh : 0 < h) (N : ℕ)
    {α β γ δ : (Fin d → ℝ) → ℝ}
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ x, 0 ≤ β x) (hγ : ∀ x, 0 ≤ γ x) (hδ : ∀ x, 0 ≤ δ x)
    (h4 : ∀ x y, α x * β y ≤ γ (x ⊓ y) * δ (x ⊔ y)) (v : Fin d → ℝ) :
    gridSum d h N α v * gridSum d h N β v ≤ gridSum d h N γ v * gridSum d h N δ v := by
  unfold gridSum
  have hhd : 0 ≤ h ^ d * h ^ d := mul_nonneg (pow_nonneg hh.le d) (pow_nonneg hh.le d)
  have hstep :
      (∑ k : Fin d → Fin (2 * N + 1), α (h • v + gridShift d h N k)) *
      (∑ k : Fin d → Fin (2 * N + 1), β (h • v + gridShift d h N k)) ≤
      (∑ k : Fin d → Fin (2 * N + 1), γ (h • v + gridShift d h N k)) *
      (∑ k : Fin d → Fin (2 * N + 1), δ (h • v + gridShift d h N k)) := by
    refine four_functions_pi d (2 * N + 1) _ _ _ _
      (fun _ => hα _) (fun _ => hβ _) (fun _ => hγ _) (fun _ => hδ _) ?_
    intro k₁ k₂
    have hinf : h • v + gridShift d h N (k₁ ⊓ k₂) =
        (h • v + gridShift d h N k₁) ⊓ (h • v + gridShift d h N k₂) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.inf_apply, smul_eq_mul, gridShift]
      have hm : Monotone (fun t : Fin (2 * N + 1) => h * v i + h * ((t : ℝ) - N)) := by
        intro a b hab
        have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        nlinarith
      exact hm.map_min
    have hsup : h • v + gridShift d h N (k₁ ⊔ k₂) =
        (h • v + gridShift d h N k₁) ⊔ (h • v + gridShift d h N k₂) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sup_apply, smul_eq_mul, gridShift]
      have hm : Monotone (fun t : Fin (2 * N + 1) => h * v i + h * ((t : ℝ) - N)) := by
        intro a b hab
        have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        nlinarith
      exact hm.map_max
    rw [hinf, hsup]
    exact h4 _ _
  calc (h ^ d * ∑ k, α (h • v + gridShift d h N k)) *
        (h ^ d * ∑ k, β (h • v + gridShift d h N k))
      = (h ^ d * h ^ d) * ((∑ k, α (h • v + gridShift d h N k)) *
          (∑ k, β (h • v + gridShift d h N k))) := by ring
    _ ≤ (h ^ d * h ^ d) * ((∑ k, γ (h • v + gridShift d h N k)) *
          (∑ k, δ (h • v + gridShift d h N k))) := mul_le_mul_of_nonneg_left hstep hhd
    _ = (h ^ d * ∑ k, γ (h • v + gridShift d h N k)) *
        (h ^ d * ∑ k, δ (h • v + gridShift d h N k)) := by ring

private lemma sqrt_mul_le_am_gm {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 < t) :
    Real.sqrt (x * y) ≤ (t * x + t⁻¹ * y) / 2 := by
  have h1 : 0 ≤ (t * x + t⁻¹ * y) / 2 := by positivity
  rw [← Real.sqrt_sq h1]
  apply Real.sqrt_le_sqrt
  have h2 : (t * x - t⁻¹ * y) ^ 2 ≥ 0 := sq_nonneg _
  have h3 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  nlinarith [show ((t * x + t⁻¹ * y) / 2) ^ 2 - x * y =
    ((t * x - t⁻¹ * y) / 2) ^ 2 + (t * t⁻¹ - 1) * x * y by ring]

private lemma sqrt_sub_le_sqrt_abs {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a - Real.sqrt b ≤ Real.sqrt |a - b| := by
  by_cases h : a ≤ b
  · have : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt h
    linarith [Real.sqrt_nonneg |a - b|]
  · push Not at h
    have hab : 0 ≤ a - b := sub_nonneg.mpr h.le
    rw [abs_of_nonneg hab]
    have hsq : Real.sqrt a ≤ Real.sqrt b + Real.sqrt (a - b) := by
      have hr : 0 ≤ Real.sqrt b + Real.sqrt (a - b) := by positivity
      rw [← Real.sqrt_sq hr]
      apply Real.sqrt_le_sqrt
      rw [add_sq, Real.sq_sqrt hb, Real.sq_sqrt hab]
      nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg (a - b)]
    linarith

private lemma sqrt_mul_sub_le {a b a₀ b₀ s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hs : 0 < s) :
    Real.sqrt (a₀ * b₀) - Real.sqrt (a * b) ≤
      (s⁻¹ * |a - a₀| + s * b₀ + s * a + s⁻¹ * |b - b₀|) / 2 := by
  rw [Real.sqrt_mul ha₀, Real.sqrt_mul ha]
  have h1 : Real.sqrt a₀ * Real.sqrt b₀ - Real.sqrt a * Real.sqrt b =
      (Real.sqrt a₀ - Real.sqrt a) * Real.sqrt b₀ + Real.sqrt a * (Real.sqrt b₀ - Real.sqrt b) := by
    ring
  rw [h1]
  have t1 : (Real.sqrt a₀ - Real.sqrt a) * Real.sqrt b₀ ≤
      (s⁻¹ * |a - a₀| + s * b₀) / 2 := by
    calc (Real.sqrt a₀ - Real.sqrt a) * Real.sqrt b₀
        ≤ Real.sqrt |a₀ - a| * Real.sqrt b₀ :=
          mul_le_mul_of_nonneg_right (sqrt_sub_le_sqrt_abs ha₀ ha) (Real.sqrt_nonneg _)
      _ = Real.sqrt (|a - a₀| * b₀) := by rw [abs_sub_comm, ← Real.sqrt_mul (abs_nonneg _)]
      _ ≤ (s⁻¹ * |a - a₀| + (s⁻¹)⁻¹ * b₀) / 2 :=
          sqrt_mul_le_am_gm (abs_nonneg _) hb₀ (inv_pos.mpr hs)
      _ = (s⁻¹ * |a - a₀| + s * b₀) / 2 := by rw [inv_inv]
  have t2 : Real.sqrt a * (Real.sqrt b₀ - Real.sqrt b) ≤
      (s * a + s⁻¹ * |b - b₀|) / 2 := by
    calc Real.sqrt a * (Real.sqrt b₀ - Real.sqrt b)
        ≤ Real.sqrt a * Real.sqrt |b₀ - b| :=
          mul_le_mul_of_nonneg_left (sqrt_sub_le_sqrt_abs hb₀ hb) (Real.sqrt_nonneg _)
      _ = Real.sqrt (a * |b - b₀|) := by rw [abs_sub_comm, ← Real.sqrt_mul ha]
      _ ≤ (s * a + s⁻¹ * |b - b₀|) / 2 :=
          sqrt_mul_le_am_gm ha (abs_nonneg _) hs
  linarith

private lemma exists_nonneg_compact_continuous_approx (d : ℕ)
    {f : (Fin d → ℝ) → ℝ} (hf : Integrable f) (hnn : ∀ x, 0 ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : (Fin d → ℝ) → ℝ,
      HasCompactSupport g ∧ Continuous g ∧ Integrable g ∧ (∀ x, 0 ≤ g x) ∧
      (∫ x, |f x - g x|) ≤ ε := by
  obtain ⟨g₀, hcs, hint, hcont, _⟩ := hf.exists_hasCompactSupport_integral_sub_le hε
  let g : (Fin d → ℝ) → ℝ := fun x => max (g₀ x) 0
  have hg_nn : ∀ x, 0 ≤ g x := fun x => le_max_right _ _
  have hg_cont : Continuous g := hcont.max continuous_const
  have hg_cs : HasCompactSupport g := by
    refine hcs.mono ?_
    intro x hx
    simp only [Function.mem_support, ne_eq, g] at hx ⊢
    intro h0
    apply hx
    simp [h0]
  have hg_int : Integrable g := hg_cont.integrable_of_hasCompactSupport hg_cs
  have hle : ∀ x, |f x - g x| ≤ ‖f x - g₀ x‖ := by
    intro x
    rw [Real.norm_eq_abs]
    simp only [g]
    by_cases h0 : 0 ≤ g₀ x
    · rw [max_eq_left h0]
    · push Not at h0
      rw [max_eq_right h0.le, sub_zero, abs_of_nonneg (hnn x), abs_of_nonneg (by linarith [hnn x])]
      linarith
  have hint_le : ∫ x, |f x - g x| ≤ ε := by
    calc ∫ x, |f x - g x|
        ≤ ∫ x, ‖f x - g₀ x‖ :=
          integral_mono (hf.sub hg_int).abs (hf.sub (hcont.integrable_of_hasCompactSupport hcs)).norm hle
      _ ≤ ε := hint
  exact ⟨g, hg_cs, hg_cont, hg_int, hg_nn, hint_le⟩

private lemma compact_support_gridSum_close (d : ℕ)
    {g : (Fin d → ℝ) → ℝ} (_hcs : HasCompactSupport g) (_hcont : Continuous g) (hg_int : Integrable g)
    {R : ℝ} (_hR : 0 < R) (hsupp : ∀ x, x ∈ tsupport g → ‖x‖ < R)
    {h : ℝ} (hh : 0 < h) (N : ℕ) (hNR : R ≤ h * N)
    {η : ℝ} (_hη : 0 ≤ η) (hosc : ∀ x y, ‖x - y‖ ≤ h → |g x - g y| ≤ η)
    {v : Fin d → ℝ} (hv : v ∈ unitCube d) :
    |gridSum d h N g v - ∫ x, g x| ≤ ((2 * (N : ℝ) + 1) * h) ^ d * η := by
  let U : Set (Fin d → ℝ) := ⋃ k : Fin d → Fin (2 * N + 1), gridBox d h N k
  have hcompl : ∀ x ∉ U, g x = 0 := by
    intro x hx
    by_contra hgx
    have hmem : x ∈ tsupport g := subset_tsupport g hgx
    have hnorm : ‖x‖ < R := hsupp x hmem
    apply hx
    rw [Set.mem_iUnion]
    have hcoord : ∀ i, - (h * N) ≤ x i ∧ x i < h * (N + 1) := by
      intro i
      have hi : |x i| ≤ ‖x‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
      have hiR : |x i| < R := lt_of_le_of_lt hi hnorm
      rw [abs_lt] at hiR
      constructor <;> nlinarith
    have hidx : ∀ i, ∃ k : Fin (2 * N + 1),
        h * ((k : ℝ) - N) ≤ x i ∧ x i < h * ((k : ℝ) - N) + h := by
      intro i
      let t : ℝ := x i / h + N
      have ht0 : 0 ≤ t := by
        have := (hcoord i).1
        have : - (N : ℝ) ≤ x i / h := by
          rw [le_div_iff₀ hh]; linarith
        linarith
      have htn : t < 2 * N + 1 := by
        have := (hcoord i).2
        have : x i / h < N + 1 := by
          rw [div_lt_iff₀ hh]; linarith
        linarith
      let m : ℕ := Nat.floor t
      have hm_lt : m < 2 * N + 1 := by
        have hfl : (m : ℝ) ≤ t := Nat.floor_le ht0
        exact_mod_cast lt_of_le_of_lt hfl htn
      refine ⟨⟨m, hm_lt⟩, ?_, ?_⟩
      · have hfl : (m : ℝ) ≤ x i / h + N := Nat.floor_le ht0
        have : ((m : ℝ) - N) * h ≤ x i := by
          rw [← le_div_iff₀ hh]; linarith
        linarith
      · have hfl : x i / h + N < (m : ℝ) + 1 := Nat.lt_floor_add_one t
        have : x i < ((m : ℝ) - N + 1) * h := by
          rw [← div_lt_iff₀ hh]; linarith
        linarith
    choose k hk using hidx
    refine ⟨k, ?_⟩
    intro i _
    exact hk i
  have hintU : ∫ x in U, g x = ∫ x, g x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
  rw [← hintU, integral_iUnion_fintype (fun k => measurableSet_gridBox d h N k)
    (pairwise_disjoint_gridBox d hh N) (fun k => hg_int.integrableOn)]
  unfold gridSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ k : Fin d → Fin (2 * N + 1),
      |h ^ d * g (h • v + gridShift d h N k) - ∫ x in gridBox d h N k, g x| ≤ h ^ d * η := by
    intro k
    have hvol : volume.real (gridBox d h N k) = h ^ d := by
      rw [Measure.real_def, volume_gridBox d hh.le N k, ENNReal.toReal_ofReal (pow_nonneg hh.le d)]
    have hbox_fin : volume (gridBox d h N k) ≠ ⊤ := by
      rw [volume_gridBox d hh.le N k]
      exact ENNReal.ofReal_ne_top
    have hconst : h ^ d * g (h • v + gridShift d h N k) =
        ∫ _ in gridBox d h N k, g (h • v + gridShift d h N k) := by
      rw [setIntegral_const, smul_eq_mul, hvol]
    have hint_c : IntegrableOn (fun _ : Fin d → ℝ => g (h • v + gridShift d h N k))
        (gridBox d h N k) := integrableOn_const hbox_fin
    rw [hconst, ← integral_sub hint_c hg_int.integrableOn]
    have hpt : ∀ x ∈ gridBox d h N k, |g (h • v + gridShift d h N k) - g x| ≤ η := by
      intro x hx
      apply hosc
      rw [pi_norm_le_iff_of_nonneg hh.le]
      intro i
      have hxi := hx i (Set.mem_univ i)
      have hvi := hv i (Set.mem_univ i)
      simp only [Set.mem_Ico] at hxi hvi
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
      rw [abs_le]
      constructor <;> nlinarith
    calc |∫ x in gridBox d h N k, (g (h • v + gridShift d h N k) - g x)|
        ≤ ∫ x in gridBox d h N k, |g (h • v + gridShift d h N k) - g x| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _ in gridBox d h N k, η := by
          refine setIntegral_mono_on ?_ ?_ (measurableSet_gridBox d h N k) hpt
          · exact (hint_c.sub hg_int.integrableOn).abs
          · exact integrableOn_const hbox_fin
      _ = h ^ d * η := by rw [setIntegral_const, smul_eq_mul, hvol]
  calc |∑ k : Fin d → Fin (2 * N + 1), (h ^ d * g (h • v + gridShift d h N k) - ∫ x in gridBox d h N k, g x)|
      ≤ ∑ k : Fin d → Fin (2 * N + 1), |h ^ d * g (h • v + gridShift d h N k) - ∫ x in gridBox d h N k, g x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d → Fin (2 * N + 1), (h ^ d * η) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = ((2 * (N : ℝ) + 1) * h) ^ d * η := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        rw [mul_pow]
        ring

private lemma four_functions_integral (d : ℕ)
    {α β γ δ : (Fin d → ℝ) → ℝ}
    (hα_nn : ∀ x, 0 ≤ α x) (hβ_nn : ∀ x, 0 ≤ β x) (hγ_nn : ∀ x, 0 ≤ γ x) (hδ_nn : ∀ x, 0 ≤ δ x)
    (hα_int : Integrable α) (hβ_int : Integrable β) (hγ_int : Integrable γ) (hδ_int : Integrable δ)
    (h4 : ∀ x y, α x * β y ≤ γ (x ⊓ y) * δ (x ⊔ y)) :
    (∫ x, α x) * (∫ y, β y) ≤ (∫ x, γ x) * (∫ y, δ y) := by
  have hIα : 0 ≤ ∫ x, α x := integral_nonneg hα_nn
  have hIβ : 0 ≤ ∫ x, β x := integral_nonneg hβ_nn
  have hIγ : 0 ≤ ∫ x, γ x := integral_nonneg hγ_nn
  have hIδ : 0 ≤ ∫ x, δ x := integral_nonneg hδ_nn
  suffices hmain : ∀ t : ℝ, 0 < t →
      Real.sqrt ((∫ x, α x) * (∫ y, β y)) ≤ (t * (∫ x, γ x) + t⁻¹ * (∫ y, δ y)) / 2 by
    have hsq : Real.sqrt ((∫ x, α x) * (∫ y, β y)) ≤ Real.sqrt ((∫ x, γ x) * (∫ y, δ y)) := by
      by_cases hγ0 : ∫ x, γ x = 0
      · have hle : ∀ ε : ℝ, 0 < ε → Real.sqrt ((∫ x, α x) * (∫ y, β y)) ≤ ε := by
          intro ε hε
          let t : ℝ := ((∫ y, δ y) + 1) / (2 * ε)
          have ht : 0 < t := by positivity
          have hm := hmain t ht
          rw [hγ0, mul_zero, zero_add] at hm
          have h1 : t⁻¹ * (∫ y, δ y) / 2 ≤ ε := by
            have hinv : t⁻¹ = (2 * ε) / ((∫ y, δ y) + 1) := by simp [t]
            rw [hinv]
            have hpos : 0 < (∫ y, δ y) + 1 := by linarith
            rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
            nlinarith
          linarith
        have h0 : Real.sqrt ((∫ x, α x) * (∫ y, β y)) ≤ 0 := by
          by_contra hgt
          push Not at hgt
          linarith [hle (Real.sqrt ((∫ x, α x) * (∫ y, β y)) / 2) (by linarith)]
        exact h0.trans (Real.sqrt_nonneg _)
      · by_cases hδ0 : ∫ y, δ y = 0
        · have hle : ∀ ε : ℝ, 0 < ε → Real.sqrt ((∫ x, α x) * (∫ y, β y)) ≤ ε := by
            intro ε hε
            let t : ℝ := 2 * ε / ((∫ x, γ x) + 1)
            have ht : 0 < t := by positivity
            have hm := hmain t ht
            rw [hδ0, mul_zero, add_zero] at hm
            have h1 : t * (∫ x, γ x) / 2 ≤ ε := by
              dsimp only [t]
              have hpos : 0 < (∫ x, γ x) + 1 := by linarith
              rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
              nlinarith
            linarith
          have h0 : Real.sqrt ((∫ x, α x) * (∫ y, β y)) ≤ 0 := by
            by_contra hgt
            push Not at hgt
            linarith [hle (Real.sqrt ((∫ x, α x) * (∫ y, β y)) / 2) (by linarith)]
          exact h0.trans (Real.sqrt_nonneg _)
        · have hγp : 0 < ∫ x, γ x := lt_of_le_of_ne hIγ (Ne.symm hγ0)
          have hδp : 0 < ∫ y, δ y := lt_of_le_of_ne hIδ (Ne.symm hδ0)
          let t : ℝ := Real.sqrt ((∫ y, δ y) / (∫ x, γ x))
          have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hδp hγp)
          have hm := hmain t ht
          have heq : (t * (∫ x, γ x) + t⁻¹ * (∫ y, δ y)) / 2 =
              Real.sqrt ((∫ x, γ x) * (∫ y, δ y)) := by
            have hsq1 : t * (∫ x, γ x) = Real.sqrt ((∫ x, γ x) * (∫ y, δ y)) := by
              rw [show t = Real.sqrt (∫ y, δ y) / Real.sqrt (∫ x, γ x) from Real.sqrt_div hδp.le _]
              have hsr : Real.sqrt (∫ x, γ x) ≠ 0 := (Real.sqrt_pos.mpr hγp).ne'
              rw [div_mul_eq_mul_div, div_eq_iff hsr, Real.sqrt_mul hγp.le]
              rw [mul_comm (Real.sqrt (∫ x, γ x)), mul_assoc, Real.mul_self_sqrt hγp.le]
            have hsq2 : t⁻¹ * (∫ y, δ y) = Real.sqrt ((∫ x, γ x) * (∫ y, δ y)) := by
              rw [show t = Real.sqrt (∫ y, δ y) / Real.sqrt (∫ x, γ x) from Real.sqrt_div hδp.le _]
              rw [inv_div]
              have hsr : Real.sqrt (∫ y, δ y) ≠ 0 := (Real.sqrt_pos.mpr hδp).ne'
              rw [div_mul_eq_mul_div, div_eq_iff hsr, Real.sqrt_mul hγp.le]
              rw [mul_assoc, Real.mul_self_sqrt hδp.le]
            linarith
          linarith
    have := mul_self_le_mul_self (Real.sqrt_nonneg _) hsq
    rwa [Real.mul_self_sqrt (mul_nonneg hIα hIβ), Real.mul_self_sqrt (mul_nonneg hIγ hIδ)] at this
  -- Now prove hmain: fix t > 0, prove for all ε > 0 that LHS ≤ RHS + ε.
  intro t ht
  apply le_of_forall_pos_le_add
  intro ε hε
  -- Step A: choose s > 0 small enough for the AM-GM error term
  let M : ℝ := (∫ x, α x) + (∫ y, β y) + 2
  have hM : 0 < M := by linarith
  let s : ℝ := min 1 (ε / (4 * M))
  have hs : 0 < s := lt_min zero_lt_one (by positivity)
  have hsM : s * M / 2 ≤ ε / 8 := by
    have : s ≤ ε / (4 * M) := min_le_right _ _
    have h1 : s * M ≤ ε / 4 := by
      calc s * M ≤ (ε / (4 * M)) * M := mul_le_mul_of_nonneg_right this hM.le
        _ = ε / 4 := by field_simp
    linarith
  -- Step B: choose δ₁ > 0 for L¹ approximation of α, β by compactly supported continuous α₀, β₀
  let δ₁ : ℝ := min (1 / 2) (s * ε / 8)
  have hδ₁ : 0 < δ₁ := lt_min (by norm_num) (by positivity)
  obtain ⟨α₀, hα₀_cs, hα₀_cont, hα₀_int, hα₀_nn, hα₀_err⟩ :=
    exists_nonneg_compact_continuous_approx d hα_int hα_nn hδ₁
  obtain ⟨β₀, hβ₀_cs, hβ₀_cont, hβ₀_int, hβ₀_nn, hβ₀_err⟩ :=
    exists_nonneg_compact_continuous_approx d hβ_int hβ_nn hδ₁
  have hIα₀ : 0 ≤ ∫ x, α₀ x := integral_nonneg hα₀_nn
  have hIβ₀ : 0 ≤ ∫ y, β₀ y := integral_nonneg hβ₀_nn
  have hdiff_Iα : |(∫ x, α x) - (∫ x, α₀ x)| ≤ δ₁ := by
    calc |(∫ x, α x) - (∫ x, α₀ x)|
        = |∫ x, (α x - α₀ x)| := by rw [← integral_sub hα_int hα₀_int]
      _ ≤ ∫ x, |α x - α₀ x| := abs_integral_le_integral_abs
      _ ≤ δ₁ := hα₀_err
  have hdiff_Iβ : |(∫ y, β y) - (∫ y, β₀ y)| ≤ δ₁ := by
    calc |(∫ y, β y) - (∫ y, β₀ y)|
        = |∫ y, (β y - β₀ y)| := by rw [← integral_sub hβ_int hβ₀_int]
      _ ≤ ∫ y, |β y - β₀ y| := abs_integral_le_integral_abs
      _ ≤ δ₁ := hβ₀_err
  -- Step C: find common support radius R > 0 for α₀ and β₀
  have hbd_α : Bornology.IsBounded (tsupport α₀) := hα₀_cs.isBounded
  have hbd_β : Bornology.IsBounded (tsupport β₀) := hβ₀_cs.isBounded
  obtain ⟨R₁, hR₁⟩ := hbd_α.subset_ball (0 : Fin d → ℝ)
  obtain ⟨R₂, hR₂⟩ := hbd_β.subset_ball (0 : Fin d → ℝ)
  let R : ℝ := max (max R₁ R₂) 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp_α : ∀ x ∈ tsupport α₀, ‖x‖ < R := by
    intro x hx
    have h1 : x ∈ Metric.ball (0 : Fin d → ℝ) R₁ := hR₁ hx
    rw [Metric.mem_ball, dist_zero_right] at h1
    exact lt_of_lt_of_le h1 (le_trans (le_max_left R₁ R₂) (le_max_left _ _))
  have hsupp_β : ∀ x ∈ tsupport β₀, ‖x‖ < R := by
    intro x hx
    have h1 : x ∈ Metric.ball (0 : Fin d → ℝ) R₂ := hR₂ hx
    rw [Metric.mem_ball, dist_zero_right] at h1
    exact lt_of_lt_of_le h1 (le_trans (le_max_right R₁ R₂) (le_max_left _ _))
  -- Step D: choose η > 0 and mesh h ∈ (0, 1] via uniform continuity of α₀, β₀
  let Cbox : ℝ := (2 * R + 5) ^ d
  have hCbox : 0 < Cbox := pow_pos (by linarith) d
  let δ₂ : ℝ := min (1 / 2) (s * ε / 8)
  have hδ₂ : 0 < δ₂ := lt_min (by norm_num) (by positivity)
  let η : ℝ := δ₂ / Cbox
  have hη : 0 < η := div_pos hδ₂ hCbox
  have huc_α : UniformContinuous α₀ := hα₀_cs.uniformContinuous_of_continuous hα₀_cont
  have huc_β : UniformContinuous β₀ := hβ₀_cs.uniformContinuous_of_continuous hβ₀_cont
  rw [Metric.uniformContinuous_iff] at huc_α huc_β
  obtain ⟨r₁, hr₁, hmod_α⟩ := huc_α η hη
  obtain ⟨r₂, hr₂, hmod_β⟩ := huc_β η hη
  let h : ℝ := min (min (r₁ / 2) (r₂ / 2)) 1
  have hh : 0 < h := lt_min (lt_min (half_pos hr₁) (half_pos hr₂)) zero_lt_one
  have hh1 : h ≤ 1 := min_le_right _ _
  have hosc_α : ∀ x y, ‖x - y‖ ≤ h → |α₀ x - α₀ y| ≤ η := by
    intro x y hxy
    have hd : dist x y < r₁ := by
      rw [dist_eq_norm]
      have : h ≤ r₁ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have := hmod_α hd
    rw [Real.dist_eq] at this
    exact this.le
  have hosc_β : ∀ x y, ‖x - y‖ ≤ h → |β₀ x - β₀ y| ≤ η := by
    intro x y hxy
    have hd : dist x y < r₂ := by
      rw [dist_eq_norm]
      have : h ≤ r₂ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    have := hmod_β hd
    rw [Real.dist_eq] at this
    exact this.le
  let N : ℕ := Nat.ceil (R / h) + 1
  have hNR : R ≤ h * N := by
    have h1 : R / h ≤ Nat.ceil (R / h) := Nat.le_ceil (R / h)
    have h2 : R ≤ h * (Nat.ceil (R / h) : ℝ) := by
      rw [div_le_iff₀ hh] at h1
      linarith
    have hNcast : (N : ℝ) = (Nat.ceil (R / h) : ℝ) + 1 := by simp [N]
    rw [hNcast]
    nlinarith
  have hbox_bound : ((2 * (N : ℝ) + 1) * h) ^ d ≤ Cbox := by
    apply pow_le_pow_left₀ (by positivity)
    have h1 : (Nat.ceil (R / h) : ℝ) < R / h + 1 := Nat.ceil_lt_add_one (div_nonneg hR.le hh.le)
    have h2 : (Nat.ceil (R / h) : ℝ) * h < R + h := by
      have := mul_lt_mul_of_pos_right h1 hh
      rw [add_mul, div_mul_cancel₀ _ hh.ne'] at this
      linarith
    have hNcast : (N : ℝ) = (Nat.ceil (R / h) : ℝ) + 1 := by simp [N]
    rw [hNcast]
    nlinarith
  -- Step E: pointwise and integral bounds on Q = unitCube d
  have hclose_α : ∀ v ∈ unitCube d, |gridSum d h N α₀ v - ∫ x, α₀ x| ≤ δ₂ := by
    intro v hv
    have h1 := compact_support_gridSum_close d hα₀_cs hα₀_cont hα₀_int hR hsupp_α hh N hNR hη.le hosc_α hv
    calc |gridSum d h N α₀ v - ∫ x, α₀ x|
        ≤ ((2 * (N : ℝ) + 1) * h) ^ d * η := h1
      _ ≤ Cbox * η := mul_le_mul_of_nonneg_right hbox_bound hη.le
      _ = δ₂ := mul_div_cancel₀ δ₂ hCbox.ne'
  have hclose_β : ∀ v ∈ unitCube d, |gridSum d h N β₀ v - ∫ y, β₀ y| ≤ δ₂ := by
    intro v hv
    have h1 := compact_support_gridSum_close d hβ₀_cs hβ₀_cont hβ₀_int hR hsupp_β hh N hNR hη.le hosc_β hv
    calc |gridSum d h N β₀ v - ∫ y, β₀ y|
        ≤ ((2 * (N : ℝ) + 1) * h) ^ d * η := h1
      _ ≤ Cbox * η := mul_le_mul_of_nonneg_right hbox_bound hη.le
      _ = δ₂ := mul_div_cancel₀ δ₂ hCbox.ne'
  -- Bound |gridSum α v - ∫ α| ≤ gridSum |α - α₀| v + δ₂ + δ₁
  have hdiff_pt : ∀ v ∈ unitCube d,
      Real.sqrt ((∫ x, α x) * (∫ y, β y)) -
        Real.sqrt (gridSum d h N α v * gridSum d h N β v) ≤
      (s⁻¹ * (gridSum d h N (fun x => |α x - α₀ x|) v + (δ₂ + δ₁)) +
       s * (∫ y, β y) +
       s * gridSum d h N α v +
       s⁻¹ * (gridSum d h N (fun y => |β y - β₀ y|) v + (δ₂ + δ₁))) / 2 := by
    intro v hv
    have hgs_α : |gridSum d h N α v - ∫ x, α x| ≤
        gridSum d h N (fun x => |α x - α₀ x|) v + (δ₂ + δ₁) := by
      have h1 : |gridSum d h N α v - gridSum d h N α₀ v| ≤
          gridSum d h N (fun x => |α x - α₀ x|) v := by
        unfold gridSum
        rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hh.le d), ← Finset.sum_sub_distrib]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hh.le d)
      have h2 := hclose_α v hv
      have h3 : |gridSum d h N α v - (∫ x, α x)| ≤
          |gridSum d h N α v - gridSum d h N α₀ v| +
          |gridSum d h N α₀ v - (∫ x, α₀ x)| +
          |(∫ x, α₀ x) - (∫ x, α x)| := by
        have ha1 := abs_add_le (gridSum d h N α v - gridSum d h N α₀ v) (gridSum d h N α₀ v - (∫ x, α₀ x))
        have ha2 := abs_add_le (gridSum d h N α v - (∫ x, α₀ x)) ((∫ x, α₀ x) - (∫ x, α x))
        have heq1 : (gridSum d h N α v - gridSum d h N α₀ v) + (gridSum d h N α₀ v - (∫ x, α₀ x)) =
          gridSum d h N α v - (∫ x, α₀ x) := by ring
        have heq2 : (gridSum d h N α v - (∫ x, α₀ x)) + ((∫ x, α₀ x) - (∫ x, α x)) =
          gridSum d h N α v - (∫ x, α x) := by ring
        rw [heq1] at ha1
        rw [heq2] at ha2
        linarith
      rw [abs_sub_comm (∫ x, α₀ x) (∫ x, α x)] at h3
      linarith
    have hgs_β : |gridSum d h N β v - (∫ y, β y)| ≤
        gridSum d h N (fun y => |β y - β₀ y|) v + (δ₂ + δ₁) := by
      have h1 : |gridSum d h N β v - gridSum d h N β₀ v| ≤
          gridSum d h N (fun y => |β y - β₀ y|) v := by
        unfold gridSum
        rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hh.le d), ← Finset.sum_sub_distrib]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hh.le d)
      have h2 := hclose_β v hv
      have h3 : |gridSum d h N β v - (∫ y, β y)| ≤
          |gridSum d h N β v - gridSum d h N β₀ v| +
          |gridSum d h N β₀ v - (∫ y, β₀ y)| +
          |(∫ y, β₀ y) - (∫ y, β y)| := by
        have hb1 := abs_add_le (gridSum d h N β v - gridSum d h N β₀ v) (gridSum d h N β₀ v - (∫ y, β₀ y))
        have hb2 := abs_add_le (gridSum d h N β v - (∫ y, β₀ y)) ((∫ y, β₀ y) - (∫ y, β y))
        have heq1 : (gridSum d h N β v - gridSum d h N β₀ v) + (gridSum d h N β₀ v - (∫ y, β₀ y)) =
          gridSum d h N β v - (∫ y, β₀ y) := by ring
        have heq2 : (gridSum d h N β v - (∫ y, β₀ y)) + ((∫ y, β₀ y) - (∫ y, β y)) =
          gridSum d h N β v - (∫ y, β y) := by ring
        rw [heq1] at hb1
        rw [heq2] at hb2
        linarith
      rw [abs_sub_comm (∫ y, β₀ y) (∫ y, β y)] at h3
      linarith
    have hsm := sqrt_mul_sub_le (gridSum_nonneg d hh.le N hα_nn v) (gridSum_nonneg d hh.le N hβ_nn v)
      hIα hIβ hs
    have hs_inv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    nlinarith
  -- Step F: Integrability on unitCube d of the sqrt term and error terms
  have hint_α : IntegrableOn (gridSum d h N α) (unitCube d) := integrableOn_gridSum d hh N hα_int
  have hint_β : IntegrableOn (gridSum d h N β) (unitCube d) := integrableOn_gridSum d hh N hβ_int
  have hint_γ : IntegrableOn (gridSum d h N γ) (unitCube d) := integrableOn_gridSum d hh N hγ_int
  have hint_δ : IntegrableOn (gridSum d h N δ) (unitCube d) := integrableOn_gridSum d hh N hδ_int
  have hint_errα : IntegrableOn (gridSum d h N (fun x => |α x - α₀ x|)) (unitCube d) :=
    integrableOn_gridSum d hh N (hα_int.sub hα₀_int).abs
  have hint_errβ : IntegrableOn (gridSum d h N (fun y => |β y - β₀ y|)) (unitCube d) :=
    integrableOn_gridSum d hh N (hβ_int.sub hβ₀_int).abs
  have hint_sqrt : IntegrableOn (fun v => Real.sqrt (gridSum d h N α v * gridSum d h N β v)) (unitCube d) := by
    have hdom : IntegrableOn (fun v => (gridSum d h N α v + gridSum d h N β v) / 2) (unitCube d) :=
      (hint_α.add hint_β).div_const 2
    refine hdom.mono' ?_ ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable
        (hint_α.aestronglyMeasurable.mul hint_β.aestronglyMeasurable)
    · filter_upwards with v
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have := sqrt_mul_le_am_gm (gridSum_nonneg d hh.le N hα_nn v) (gridSum_nonneg d hh.le N hβ_nn v) zero_lt_one
      simpa using this
  -- Step G: Integrate the upper bound and the lower bound over unitCube d
  have hQ_fin : volume (unitCube d) ≠ ⊤ := by rw [volume_unitCube]; exact ENNReal.one_ne_top
  have hQ_vol : volume.real (unitCube d) = 1 := by rw [Measure.real_def, volume_unitCube]; simp
  have hupper : ∫ v in unitCube d, Real.sqrt (gridSum d h N α v * gridSum d h N β v) ≤
      (t * (∫ x, γ x) + t⁻¹ * (∫ y, δ y)) / 2 := by
    have hpt_u : ∀ v ∈ unitCube d,
        Real.sqrt (gridSum d h N α v * gridSum d h N β v) ≤
          (t * gridSum d h N γ v + t⁻¹ * gridSum d h N δ v) / 2 := by
      intro v _
      calc Real.sqrt (gridSum d h N α v * gridSum d h N β v)
          ≤ Real.sqrt (gridSum d h N γ v * gridSum d h N δ v) :=
            Real.sqrt_le_sqrt (gridSum_four_functions d hh N hα_nn hβ_nn hγ_nn hδ_nn h4 v)
        _ ≤ (t * gridSum d h N γ v + t⁻¹ * gridSum d h N δ v) / 2 :=
            sqrt_mul_le_am_gm (gridSum_nonneg d hh.le N hγ_nn v) (gridSum_nonneg d hh.le N hδ_nn v) ht
    have hdom_u : IntegrableOn (fun v => (t * gridSum d h N γ v + t⁻¹ * gridSum d h N δ v) / 2) (unitCube d) :=
      ((hint_γ.const_mul t).add (hint_δ.const_mul t⁻¹)).div_const 2
    calc ∫ v in unitCube d, Real.sqrt (gridSum d h N α v * gridSum d h N β v)
        ≤ ∫ v in unitCube d, (t * gridSum d h N γ v + t⁻¹ * gridSum d h N δ v) / 2 :=
          setIntegral_mono_on hint_sqrt hdom_u (measurableSet_unitCube d) hpt_u
      _ = (t * (∫ v in unitCube d, gridSum d h N γ v) +
           t⁻¹ * (∫ v in unitCube d, gridSum d h N δ v)) / 2 := by
          rw [integral_div, integral_add (hint_γ.const_mul t) (hint_δ.const_mul t⁻¹),
            integral_const_mul, integral_const_mul]
      _ ≤ (t * (∫ x, γ x) + t⁻¹ * (∫ y, δ y)) / 2 := by
          have hγ_le := setIntegral_gridSum_le d hh N hγ_int hγ_nn
          have hδ_le := setIntegral_gridSum_le d hh N hδ_int hδ_nn
          have htinv : 0 < t⁻¹ := inv_pos.mpr ht
          nlinarith
  have hlower : Real.sqrt ((∫ x, α x) * (∫ y, β y)) -
      ∫ v in unitCube d, Real.sqrt (gridSum d h N α v * gridSum d h N β v) ≤ ε := by
    let errFn (v : Fin d → ℝ) : ℝ :=
      (s⁻¹ * (gridSum d h N (fun x => |α x - α₀ x|) v + (δ₂ + δ₁)) +
       s * (∫ y, β y) +
       s * gridSum d h N α v +
       s⁻¹ * (gridSum d h N (fun y => |β y - β₀ y|) v + (δ₂ + δ₁))) / 2
    have hint_const : ∀ c : ℝ, IntegrableOn (fun _ : Fin d → ℝ => c) (unitCube d) :=
      fun _ => integrableOn_const hQ_fin
    have hint_t1 : IntegrableOn (fun v => s⁻¹ * (gridSum d h N (fun x => |α x - α₀ x|) v + (δ₂ + δ₁))) (unitCube d) :=
      (hint_errα.add (hint_const _)).const_mul s⁻¹
    have hint_t2 : IntegrableOn (fun _ : Fin d → ℝ => s * (∫ y, β y)) (unitCube d) := hint_const _
    have hint_t3 : IntegrableOn (fun v => s * gridSum d h N α v) (unitCube d) := hint_α.const_mul s
    have hint_t4 : IntegrableOn (fun v => s⁻¹ * (gridSum d h N (fun y => |β y - β₀ y|) v + (δ₂ + δ₁))) (unitCube d) :=
      (hint_errβ.add (hint_const _)).const_mul s⁻¹
    have hint_errFn : IntegrableOn errFn (unitCube d) :=
      (((hint_t1.add hint_t2).add hint_t3).add hint_t4).div_const 2
    have hsub_int : ∫ v in unitCube d,
        (Real.sqrt ((∫ x, α x) * (∫ y, β y)) - Real.sqrt (gridSum d h N α v * gridSum d h N β v)) =
        Real.sqrt ((∫ x, α x) * (∫ y, β y)) -
          ∫ v in unitCube d, Real.sqrt (gridSum d h N α v * gridSum d h N β v) := by
      rw [integral_sub (hint_const _) hint_sqrt, setIntegral_const, smul_eq_mul, hQ_vol, one_mul]
    rw [← hsub_int]
    calc ∫ v in unitCube d,
          (Real.sqrt ((∫ x, α x) * (∫ y, β y)) - Real.sqrt (gridSum d h N α v * gridSum d h N β v))
        ≤ ∫ v in unitCube d, errFn v :=
          setIntegral_mono_on ((hint_const _).sub hint_sqrt) hint_errFn (measurableSet_unitCube d) hdiff_pt
      _ = (s⁻¹ * ((∫ v in unitCube d, gridSum d h N (fun x => |α x - α₀ x|) v) + (δ₂ + δ₁)) +
           s * (∫ y, β y) +
           s * (∫ v in unitCube d, gridSum d h N α v) +
           s⁻¹ * ((∫ v in unitCube d, gridSum d h N (fun y => |β y - β₀ y|) v) + (δ₂ + δ₁))) / 2 := by
          dsimp only [errFn]
          have hadd : ∀ {f g : (Fin d → ℝ) → ℝ},
              IntegrableOn f (unitCube d) → IntegrableOn g (unitCube d) →
              ∫ v in unitCube d, (f v + g v) = (∫ v in unitCube d, f v) + (∫ v in unitCube d, g v) :=
            fun hf hg => integral_add hf hg
          have hint_t12 : IntegrableOn (fun v =>
              s⁻¹ * (gridSum d h N (fun x => |α x - α₀ x|) v + (δ₂ + δ₁)) + s * (∫ y, β y)) (unitCube d) :=
            hint_t1.add hint_t2
          have hint_t123 : IntegrableOn (fun v =>
              (s⁻¹ * (gridSum d h N (fun x => |α x - α₀ x|) v + (δ₂ + δ₁)) + s * (∫ y, β y)) +
                s * gridSum d h N α v) (unitCube d) :=
            hint_t12.add hint_t3
          rw [integral_div,
            hadd hint_t123 hint_t4,
            hadd hint_t12 hint_t3,
            hadd hint_t1 hint_t2,
            integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
            hadd hint_errα (hint_const _),
            hadd hint_errβ (hint_const _)]
          simp only [setIntegral_const, smul_eq_mul, hQ_vol, one_mul]
      _ ≤ (s⁻¹ * (δ₁ + (δ₂ + δ₁)) + s * (∫ y, β y) + s * (∫ x, α x) +
           s⁻¹ * (δ₁ + (δ₂ + δ₁))) / 2 := by
          have he1 : ∫ v in unitCube d, gridSum d h N (fun x => |α x - α₀ x|) v ≤ δ₁ :=
            (setIntegral_gridSum_le d hh N (hα_int.sub hα₀_int).abs (fun _ => abs_nonneg _)).trans hα₀_err
          have he2 : ∫ v in unitCube d, gridSum d h N (fun y => |β y - β₀ y|) v ≤ δ₁ :=
            (setIntegral_gridSum_le d hh N (hβ_int.sub hβ₀_int).abs (fun _ => abs_nonneg _)).trans hβ₀_err
          have he3 : ∫ v in unitCube d, gridSum d h N α v ≤ ∫ x, α x :=
            setIntegral_gridSum_le d hh N hα_int hα_nn
          have hs_inv : 0 < s⁻¹ := inv_pos.mpr hs
          nlinarith
      _ ≤ ε := by
          have h1 : s⁻¹ * δ₁ ≤ ε / 8 := by
            have : δ₁ ≤ s * ε / 8 := min_le_right _ _
            calc s⁻¹ * δ₁ ≤ s⁻¹ * (s * ε / 8) := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hs.le)
              _ = ε / 8 := by field_simp
          have h2 : s⁻¹ * δ₂ ≤ ε / 8 := by
            have : δ₂ ≤ s * ε / 8 := min_le_right _ _
            calc s⁻¹ * δ₂ ≤ s⁻¹ * (s * ε / 8) := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hs.le)
              _ = ε / 8 := by field_simp
          have h3 : s * ((∫ x, α x) + (∫ y, β y)) / 2 ≤ ε / 8 := by
            have : (∫ x, α x) + (∫ y, β y) ≤ M := by dsimp only [M]; linarith
            have : s * ((∫ x, α x) + (∫ y, β y)) ≤ s * M := mul_le_mul_of_nonneg_left this hs.le
            linarith
          linarith
  linarith

/-! ### Part 3: Gaussian Kernel MTP₂ Property and Main Theorem -/

private lemma phi_nonneg (d : ℕ) (z : Fin d → ℝ) : 0 ≤ OMA.S_arxiv_1910_02345.φ d z := by
  unfold OMA.S_arxiv_1910_02345.φ
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

private lemma phi_le_const (d : ℕ) (z : Fin d → ℝ) :
    OMA.S_arxiv_1910_02345.φ d z ≤ (2 * Real.pi) ^ (-(d : ℝ) / 2) := by
  unfold OMA.S_arxiv_1910_02345.φ
  have h1 : Real.exp (-(∑ i, z i ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (z i)
    linarith
  calc (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(∑ i, z i ^ 2) / 2)
      ≤ (2 * Real.pi) ^ (-(d : ℝ) / 2) * 1 :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by positivity) _)
    _ = (2 * Real.pi) ^ (-(d : ℝ) / 2) := mul_one _

private lemma continuous_phi (d : ℕ) : Continuous (OMA.S_arxiv_1910_02345.φ d) := by
  unfold OMA.S_arxiv_1910_02345.φ
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  refine (Continuous.neg ?_).div_const 2
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2

private lemma sq_min_max_le (a b c d : ℝ) :
    (min a b - min c d) ^ 2 + (max a b - max c d) ^ 2 ≤ (a - c) ^ 2 + (b - d) ^ 2 := by
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · rw [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd]
  · rw [min_eq_left hab, max_eq_right hab, min_eq_right hdc, max_eq_left hdc]; nlinarith
  · rw [min_eq_right hba, max_eq_left hba, min_eq_left hcd, max_eq_right hcd]; nlinarith
  · rw [min_eq_right hba, max_eq_left hba, min_eq_right hdc, max_eq_left hdc]; nlinarith

private lemma phi_kernel_mtp2 (d : ℕ) (x x' y y' : Fin d → ℝ) :
    OMA.S_arxiv_1910_02345.φ d (x - y) * OMA.S_arxiv_1910_02345.φ d (x' - y') ≤
    OMA.S_arxiv_1910_02345.φ d ((x ⊓ x') - (y ⊓ y')) *
      OMA.S_arxiv_1910_02345.φ d ((x ⊔ x') - (y ⊔ y')) := by
  unfold OMA.S_arxiv_1910_02345.φ
  set C : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2)
  have hC : 0 ≤ C * C := mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have hlhs : C * Real.exp (-(∑ i, (x - y) i ^ 2) / 2) *
      (C * Real.exp (-(∑ i, (x' - y') i ^ 2) / 2)) =
      (C * C) * Real.exp (-(∑ i, ((x i - y i) ^ 2 + (x' i - y' i) ^ 2)) / 2) := by
    rw [show C * Real.exp (-(∑ i, (x - y) i ^ 2) / 2) * (C * Real.exp (-(∑ i, (x' - y') i ^ 2) / 2)) =
      (C * C) * (Real.exp (-(∑ i, (x - y) i ^ 2) / 2) * Real.exp (-(∑ i, (x' - y') i ^ 2) / 2)) by ring]
    rw [← Real.exp_add]
    congr 2
    simp only [Pi.sub_apply, Finset.sum_add_distrib]
    ring
  have hrhs : C * Real.exp (-(∑ i, ((x ⊓ x') - (y ⊓ y')) i ^ 2) / 2) *
      (C * Real.exp (-(∑ i, ((x ⊔ x') - (y ⊔ y')) i ^ 2) / 2)) =
      (C * C) * Real.exp (-(∑ i, ((min (x i) (x' i) - min (y i) (y' i)) ^ 2 +
        (max (x i) (x' i) - max (y i) (y' i)) ^ 2)) / 2) := by
    rw [show C * Real.exp (-(∑ i, ((x ⊓ x') - (y ⊓ y')) i ^ 2) / 2) *
        (C * Real.exp (-(∑ i, ((x ⊔ x') - (y ⊔ y')) i ^ 2) / 2)) =
      (C * C) * (Real.exp (-(∑ i, ((x ⊓ x') - (y ⊓ y')) i ^ 2) / 2) *
        Real.exp (-(∑ i, ((x ⊔ x') - (y ⊔ y')) i ^ 2) / 2)) by ring]
    rw [← Real.exp_add]
    congr 2
    simp only [Pi.sub_apply, Pi.inf_apply, Pi.sup_apply, Finset.sum_add_distrib]
    ring
  rw [hlhs, hrhs]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  have hsum : ∑ i, ((min (x i) (x' i) - min (y i) (y' i)) ^ 2 +
      (max (x i) (x' i) - max (y i) (y' i)) ^ 2) ≤
      ∑ i, ((x i - y i) ^ 2 + (x' i - y' i) ^ 2) :=
    Finset.sum_le_sum fun i _ => sq_min_max_le (x i) (x' i) (y i) (y' i)
  linarith

private lemma integrable_mul_phi (d : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : Integrable f) (x : Fin d → ℝ) :
    Integrable (fun y => f y * OMA.S_arxiv_1910_02345.φ d (x - y)) := by
  have h1 : Integrable (fun y => OMA.S_arxiv_1910_02345.φ d (x - y) * f y) := by
    refine hf.bdd_mul (c := (2 * Real.pi) ^ (-(d : ℝ) / 2)) ?_ ?_
    · exact ((continuous_phi d).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (phi_nonneg d _)]
      exact phi_le_const d _
  simpa [mul_comm] using h1

private theorem zartash_robeva :
    ∀ (d : ℕ) (f : (Fin d → ℝ) → ℝ), (∀ x, 0 ≤ f x) → Integrable f → ∫ x, f x = 1 →
      OMA.S_arxiv_1910_02345.MTP2 f →
      OMA.S_arxiv_1910_02345.MTP2 (OMA.S_arxiv_1910_02345.convGauss f) := by
  intro d f hf_nn hf_int _ hf_mtp2 x x'
  unfold OMA.S_arxiv_1910_02345.convGauss
  refine four_functions_integral d
    (fun y => mul_nonneg (hf_nn y) (phi_nonneg d (x - y)))
    (fun y => mul_nonneg (hf_nn y) (phi_nonneg d (x' - y)))
    (fun y => mul_nonneg (hf_nn y) (phi_nonneg d ((x ⊓ x') - y)))
    (fun y => mul_nonneg (hf_nn y) (phi_nonneg d ((x ⊔ x') - y)))
    (integrable_mul_phi d hf_int x)
    (integrable_mul_phi d hf_int x')
    (integrable_mul_phi d hf_int (x ⊓ x'))
    (integrable_mul_phi d hf_int (x ⊔ x'))
    ?_
  intro y y'
  have h1 : f y * f y' ≤ f (y ⊓ y') * f (y ⊔ y') := hf_mtp2 y y'
  have h2 : OMA.S_arxiv_1910_02345.φ d (x - y) * OMA.S_arxiv_1910_02345.φ d (x' - y') ≤
      OMA.S_arxiv_1910_02345.φ d ((x ⊓ x') - (y ⊓ y')) *
        OMA.S_arxiv_1910_02345.φ d ((x ⊔ x') - (y ⊔ y')) :=
    phi_kernel_mtp2 d x x' y y'
  calc (f y * OMA.S_arxiv_1910_02345.φ d (x - y)) *
        (f y' * OMA.S_arxiv_1910_02345.φ d (x' - y'))
      = (f y * f y') *
        (OMA.S_arxiv_1910_02345.φ d (x - y) * OMA.S_arxiv_1910_02345.φ d (x' - y')) := by ring
    _ ≤ (f (y ⊓ y') * f (y ⊔ y')) *
        (OMA.S_arxiv_1910_02345.φ d ((x ⊓ x') - (y ⊓ y')) *
          OMA.S_arxiv_1910_02345.φ d ((x ⊔ x') - (y ⊔ y'))) :=
        mul_le_mul h1 h2 (mul_nonneg (phi_nonneg d _) (phi_nonneg d _))
          (mul_nonneg (hf_nn _) (hf_nn _))
    _ = (f (y ⊓ y') * OMA.S_arxiv_1910_02345.φ d ((x ⊓ x') - (y ⊓ y'))) *
        (f (y ⊔ y') * OMA.S_arxiv_1910_02345.φ d ((x ⊔ x') - (y ⊔ y'))) := by ring

end OMA.P_arxiv_1910_02345

theorem OMA.solution : type_of% @OMA.S_arxiv_1910_02345.main :=
  OMA.P_arxiv_1910_02345.zartash_robeva
