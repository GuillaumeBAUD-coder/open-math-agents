import OMAReductions.R_Erdos1164_erdos_1164_R1_H2_R1

/-! Discounted first hitting probabilities for even axis points. The block independence
and binomial return estimates through u_even_ge are adapted from @koolkao,
Erdos1166.erdos_1166.variants.erdos_taylor.R1.H3. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos1165

namespace OMA.AxisGreen

/-- Partial sums of a step sequence. -/
def pos (y : ℕ → ℤ × ℤ) (t : ℕ) : ℤ × ℤ := ∑ i ∈ Finset.range t, y i

def sh (t : ℕ) (y : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ y (t + i)

def path {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (ω : Ω) : ℕ → ℤ × ℤ := fun i ↦ X i ω

/-- `A` depends only on the first `m` coordinates. -/
def Det (m : ℕ) (A : Set (ℕ → ℤ × ℤ)) : Prop :=
  ∀ y y' : ℕ → ℤ × ℤ, (∀ i < m, y i = y' i) → y ∈ A → y' ∈ A

lemma pos_shift (y : ℕ → ℤ × ℤ) (t s : ℕ) : pos y (t + s) = pos y t + pos (sh t y) s :=
  Finset.sum_range_add _ _ _

lemma pos_congr {y y' : ℕ → ℤ × ℤ} {m t : ℕ} (h : ∀ i < m, y i = y' i) (ht : t ≤ m) :
    pos y t = pos y' t :=
  Finset.sum_congr rfl fun i hi ↦ h i (by rw [Finset.mem_range] at hi; omega)

/-- extension by zero of a finite window -/
def ext (m : ℕ) (z : Fin m → ℤ × ℤ) : ℕ → ℤ × ℤ := fun i ↦ if h : i < m then z ⟨i, h⟩ else 0

lemma map_window {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (n j : ℕ) :
    Measure.map (fun ω (i : Fin n) ↦ X (j + i) ω) ℙ =
      Measure.pi (fun _ : Fin n ↦ Measure.map (X 0) ℙ) := by
  have hind : ProbabilityTheory.iIndepFun (fun i : Fin n ↦ X (j + i)) ℙ :=
    hX.indep.precomp (g := fun i : Fin n ↦ j + (i : ℕ)) fun a b h ↦ Fin.ext (by simpa using h)
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    fun i ↦ (hX.measurable _).aemeasurable).mp hind]
  congr 1
  funext i
  exact Eq.trans (hX.isUniform (j + i)) (Eq.symm (hX.isUniform 0))

lemma det_pre {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A)
    (j : ℕ) : {ω | sh j (path X ω) ∈ A} =
      (fun ω (i : Fin m) ↦ X (j + i) ω) ⁻¹' {z | ext m z ∈ A} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]
  · exact hA _ _ fun i hi ↦ by simp [ext, hi, sh, path]

lemma meas_window {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (m j : ℕ) :
    Measurable (fun ω (i : Fin m) ↦ X (j + i) ω) :=
  measurable_pi_iff.mpr fun _ ↦ hX.measurable _

lemma det_meas {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det m A) (j : ℕ) :
    MeasurableSet {ω | sh j (path X ω) ∈ A} := by
  rw [det_pre X hA j]
  exact meas_window hX m j (Set.to_countable _).measurableSet

lemma sh_zero (y : ℕ → ℤ × ℤ) : sh 0 y = y := funext fun i ↦ by simp [sh]

lemma path_eq {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) (A : Set (ℕ → ℤ × ℤ)) :
    {ω | path X ω ∈ A} = {ω | sh 0 (path X ω) ∈ A} := by
  simp only [sh_zero]

/-- fixed-time Markov property: shifting does not change probabilities -/
lemma prob_shift {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {m : ℕ} {A : Set (ℕ → ℤ × ℤ)}
    (hA : Det m A) (j : ℕ) :
    ℙ {ω | sh j (path X ω) ∈ A} = ℙ {ω | path X ω ∈ A} := by
  have hT : MeasurableSet {z : Fin m → ℤ × ℤ | ext m z ∈ A} := (Set.to_countable _).measurableSet
  rw [path_eq, det_pre X hA, det_pre X hA, ← Measure.map_apply (meas_window hX m j) hT,
    ← Measure.map_apply (meas_window hX m 0) hT, map_window hX, map_window hX]


lemma preA {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t : ℕ} {A : Set (ℕ → ℤ × ℤ)} (hA : Det t A) :
    {ω | path X ω ∈ A} = (fun ω (i : Finset.range t) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : i ∈ Finset.range t then z ⟨i, h⟩ else 0) ∈ A} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · exact hA _ _ fun i hi ↦ by simp [hi, path]
  · exact hA _ _ fun i hi ↦ by simp [hi, path]

lemma preB {Ω : Type} (X : ℕ → Ω → ℤ × ℤ) {t s : ℕ} {B : Set (ℕ → ℤ × ℤ)} (hB : Det s B) :
    {ω | sh t (path X ω) ∈ B} = (fun ω (i : Finset.Ico t (t + s)) ↦ X i ω) ⁻¹'
      {z | (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then z ⟨t + i, h⟩ else 0) ∈ B} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have key : ∀ i < s, sh t (path X ω) i =
      (fun i ↦ if h : t + i ∈ Finset.Ico t (t + s) then
        (fun (i : Finset.Ico t (t + s)) ↦ X i ω) ⟨t + i, h⟩ else 0) i := by
    intro i hi
    have hm : t + i ∈ Finset.Ico t (t + s) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    simp [hm, sh, path]
  constructor
  · exact hB _ _ key
  · exact hB _ _ fun i hi ↦ (key i hi).symm

/-- independence of disjoint blocks, combined with the Markov property -/
lemma prob_block {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) {t s : ℕ}
    {A B : Set (ℕ → ℤ × ℤ)} (hA : Det t A) (hB : Det s B) :
    ℙ {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      ℙ {ω | path X ω ∈ A} * ℙ {ω | path X ω ∈ B} := by
  have hdisj : Disjoint (Finset.range t) (Finset.Ico t (t + s)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at hb
    omega
  have hind := hX.indep.indepFun_finset (Finset.range t) (Finset.Ico t (t + s)) hdisj
    hX.measurable
  have hset : {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} =
      {ω | path X ω ∈ A} ∩ {ω | sh t (path X ω) ∈ B} := rfl
  rw [hset, ← prob_shift hX hB t, preA X hA, preB X hB]
  exact hind.measure_inter_preimage_eq_mul _ _ (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet


/-- number of `±1` paths of length `t` ending at `u` -/
def c : ℕ → ℤ → ℕ
  | 0, u => if u = 0 then 1 else 0
  | t + 1, u => c t (u - 1) + c t (u + 1)

lemma c_neg : ∀ (t : ℕ) (u : ℤ), u < -(t : ℤ) → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_neg t (u - 1) (by push_cast at h; omega), c_neg t (u + 1) (by push_cast at h; omega)]

lemma c_odd : ∀ (t : ℕ) (u : ℤ), ((t : ℤ) + u) % 2 = 1 → c t u = 0
  | 0, u, h => by simp [c]; omega
  | t + 1, u, h => by
    simp only [c]
    rw [c_odd t (u - 1) (by push_cast at h; omega), c_odd t (u + 1) (by push_cast at h; omega)]

lemma c_choose : ∀ (t i : ℕ), c t (2 * (i : ℤ) - t) = t.choose i
  | 0, i => by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [c]
    · simp [c, Nat.choose_eq_zero_of_lt h]; omega
  | t + 1, 0 => by
    simp only [c, Nat.choose_zero_right]
    rw [c_neg t _ (by push_cast; omega)]
    have := c_choose t 0
    simp only [Nat.choose_zero_right] at this
    rw [show (2 * ((0 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((0 : ℕ) : ℤ) - (t : ℤ) by
      push_cast; ring, this]
  | t + 1, i + 1 => by
    simp only [c, Nat.choose_succ_succ]
    have h1 := c_choose t i
    have h2 := c_choose t (i + 1)
    rw [show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) - 1) = 2 * (i : ℤ) - t by push_cast; ring,
      show (2 * ((i + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1) = 2 * ((i + 1 : ℕ) : ℤ) - t by
        push_cast; ring, h1, h2]

lemma c_even (j : ℕ) : c (2 * j) 0 = j.centralBinom := by
  have := c_choose (2 * j) j
  rw [show (2 * (j : ℤ) - ((2 * j : ℕ) : ℤ)) = 0 by push_cast; ring] at this
  rw [this, Nat.centralBinom_eq_two_mul_choose]

lemma c_odd0 (j : ℕ) : c (2 * j + 1) 0 = 0 := c_odd _ _ (by push_cast; omega)

/-- the 2D count factorizes after the 45 degree rotation -/
lemma c_step (t : ℕ) (a b : ℤ) :
    c (t + 1) (a + b) * c (t + 1) (a - b) =
      c t ((a - 1) + b) * c t ((a - 1) - b) + c t ((a + 1) + b) * c t ((a + 1) - b) +
      c t (a + (b - 1)) * c t (a - (b - 1)) + c t (a + (b + 1)) * c t (a - (b + 1)) := by
  simp only [c]
  rw [show a - 1 + b = a + b - 1 by ring, show a - 1 - b = a - b - 1 by ring,
    show a + 1 + b = a + b + 1 by ring, show a + 1 - b = a - b + 1 by ring,
    show a + (b - 1) = a + b - 1 by ring, show a - (b - 1) = a - b + 1 by ring,
    show a + (b + 1) = a + b + 1 by ring, show a - (b + 1) = a - b - 1 by ring]
  ring


def stepsF : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

lemma steps_eq : steps = (stepsF : Set (ℤ × ℤ)) := by
  simp [steps, stepsF]

lemma prob_step {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) (S : Set (ℤ × ℤ)) :
    ℙ (X k ⁻¹' S) = (4 : ℝ≥0∞)⁻¹ * Measure.count (steps ∩ S) := by
  have hu : Measure.map (X k) ℙ = ProbabilityTheory.cond Measure.count steps := hX.isUniform k
  rw [← Measure.map_apply (hX.measurable k) (Set.to_countable S).measurableSet, hu,
    ProbabilityTheory.cond_apply (Set.to_countable _).measurableSet, steps_eq,
    Measure.count_apply_finset]
  rfl

lemma prob_step_eq {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) {e : ℤ × ℤ} (he : e ∈ steps) :
    ℙ (X k ⁻¹' {e}) = (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_step hX, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr he),
    Measure.count_singleton, mul_one]

lemma prob_step_bad {Ω : Type} [MeasureSpace Ω] {X : ℕ → Ω → ℤ × ℤ}
    (hX : IsSimpleRandomWalkSteps X) (k : ℕ) : ℙ (X k ⁻¹' stepsᶜ) = 0 := by
  rw [prob_step hX, Set.inter_compl_self, measure_empty, mul_zero]

lemma det_pos (t : ℕ) (z : ℤ × ℤ) : Det t {y | pos y t = z} := fun y y' h hy ↦ by
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [← pos_congr h le_rfl, hy]

lemma det_zero (e : ℤ × ℤ) : Det 1 {y | y 0 = e} := fun y y' h hy ↦ by
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [← h 0 one_pos, hy]

lemma prob_pos_step {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (x e : ℤ × ℤ)
    (he : e ∈ steps) :
    ℙ {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}} =
      ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ := by
  rw [prob_block hX (det_pos t (x - e)) (det_zero e)]
  congr 1
  exact prob_step_eq hX 0 he

lemma pos_succ (y : ℕ → ℤ × ℤ) (t : ℕ) : pos y (t + 1) = pos y t + y t :=
  Finset.sum_range_succ _ _

/-- the return probability bound, in counting form -/
lemma prob_pos_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t ≤
      ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞)
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      simp only [c, add_zero, sub_self, if_true, mul_one, Nat.cast_one]
      exact prob_le_one
    · have : {ω | pos (path X ω) 0 = (a, b)} = ∅ := by
        ext ω
        simp only [pos, Finset.range_zero, Finset.sum_empty, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        exact fun h' ↦ h h'.symm
      rw [this, measure_empty]
      simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hsub : {ω | pos (path X ω) (t + 1) = x} ⊆
        (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ∪ X t ⁻¹' stepsᶜ := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, pos_succ] at hω
      by_cases hs : X t ω ∈ steps
      · have hx : pos (path X ω) t = x - X t ω := by rw [← hω]; simp [path]
        have hE : ω ∈ E (X t ω) := ⟨hx, rfl⟩
        simp only [steps, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with h | h | h | h <;> rw [h] at hE <;> simp [hE]
      · exact Or.inr hs
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) ≤
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      apply le_of_eq
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have hm : ℙ {ω | pos (path X ω) (t + 1) = x} ≤
        ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) := by
      refine (measure_mono hsub).trans ?_
      refine (measure_union_le _ _).trans ?_
      rw [prob_step_bad hX t, add_zero]
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      refine (measure_union_le _ _).trans ?_
      gcongr ?_ + _
      exact measure_union_le _ _
    calc ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1)
        ≤ (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) :=
          by gcongr
      _ = ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by ring
      _ ≤ ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
        gcongr
        · refine (hE _ h1).trans ?_
          have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h2).trans ?_
          have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h3).trans ?_
          have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
        · refine (hE _ h4).trans ?_
          have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_le hX t _ _
      _ = ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞) := by
        rw [c_step]; push_cast; ring


lemma cb_sq_le (j : ℕ) (hj : 1 ≤ j) :
    ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j ≤ 1 / (Real.pi * j) := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.le_W j
  have h1 : Real.pi * j / (2 * j + 1) ≤ (2 * (j : ℝ) + 1) / (2 * j + 2) * (Real.pi / 2) := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * (j : ℝ) + 1) * Real.pi * (2 * j + 1) =
        Real.pi * j * ((2 * j + 2) * 2) + Real.pi := by ring
    rw [this]
    linarith [Real.pi_pos]
  have h2 : Real.pi * j ≤ Real.Wallis.W j * (2 * j + 1) := by
    have := h1.trans hle
    rwa [div_le_iff₀ (by positivity)] at this
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc (j.centralBinom : ℝ) ^ 2 * (Real.pi * j)
      ≤ (j.centralBinom : ℝ) ^ 2 * (Real.Wallis.W j * (2 * j + 1)) := by gcongr
    _ = Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by ring

/-- return probability, as a real number -/
noncomputable def u {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = 0}).toReal

lemma prob_zero_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) :
    u X t * 4 ^ t ≤ (c t 0 : ℝ) ^ 2 := by
  have h := prob_pos_le hX t 0 0
  simp only [add_zero, sub_zero] at h
  change ℙ {ω | pos (path X ω) t = 0} * 4 ^ t ≤ _ at h
  have h' : (ℙ {ω | pos (path X ω) t = 0} * 4 ^ t).toReal ≤ ((c t 0 * c t 0 : ℕ) : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  unfold u
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4] at h'
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal * 4 ^ t ≤ ((c t 0 * c t 0 : ℕ) : ℝ) := h'
    _ = (c t 0 : ℝ) ^ 2 := by push_cast; ring

lemma u_nonneg {Ω : Type} [MeasureSpace Ω] (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : 0 ≤ u X t :=
  ENNReal.toReal_nonneg

lemma u_le_one {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : ℕ → Ω → ℤ × ℤ) (t : ℕ) : u X t ≤ 1 := by
  unfold u
  have : ℙ {ω | pos (path X ω) t = 0} ≤ 1 := prob_le_one
  calc (ℙ {ω | pos (path X ω) t = 0}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) this
    _ = 1 := by simp

lemma u_odd {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) : u X (2 * j + 1) = 0 := by
  have h := prob_zero_le hX (2 * j + 1)
  rw [c_odd0] at h
  have h0 := u_nonneg X (2 * j + 1)
  have hp : (0 : ℝ) < 4 ^ (2 * j + 1) := by positivity
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  nlinarith

lemma u_even {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (j : ℕ) (hj : 1 ≤ j) :
    u X (2 * j) ≤ 1 / (Real.pi * j) := by
  have h := prob_zero_le hX (2 * j)
  rw [c_even, pow_mul] at h
  norm_num at h
  refine le_trans ?_ (cb_sq_le j hj)
  rw [le_div_iff₀ (by positivity)]
  exact h

lemma u_le {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ} (hX : IsSimpleRandomWalkSteps X) (t : ℕ) (ht : 1 ≤ t) :
    u X t ≤ 2 / (Real.pi * t) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t
  · have hj : 1 ≤ j := by omega
    refine (u_even hX j hj).trans (le_of_eq ?_)
    have : (j : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  · rw [u_odd hX]
    positivity

lemma pos_zero (y : ℕ → ℤ × ℤ) : pos y 0 = 0 := by simp [pos]
variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma meas_block (hX : IsSimpleRandomWalkSteps X) {t s : ℕ} {A B : Set (ℕ → ℤ × ℤ)}
    (hA : Det t A) (hB : Det s B) :
    MeasurableSet {ω | path X ω ∈ A ∧ sh t (path X ω) ∈ B} := by
  have h1 : MeasurableSet {ω | path X ω ∈ A} := by rw [path_eq]; exact det_meas hX hA 0
  exact h1.inter (det_meas hX hB t)

/-- the return probability lower bound, in counting form -/
lemma prob_pos_ge (hX : IsSimpleRandomWalkSteps X) :
    ∀ (t : ℕ) (a b : ℤ), ((c t (a + b) * c t (a - b) : ℕ) : ℝ≥0∞) ≤
      ℙ {ω | pos (path X ω) t = (a, b)} * 4 ^ t
  | 0, a, b => by
    simp only [pow_zero, mul_one]
    by_cases h : (a, b) = 0
    · have ha : a = 0 := congrArg Prod.fst h
      have hb : b = 0 := congrArg Prod.snd h
      subst ha hb
      have : {ω | pos (path X ω) 0 = ((0 : ℤ), (0 : ℤ))} = Set.univ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, pos_zero]; rfl
      rw [this, measure_univ]
      simp [c]
    · have hc : c 0 (a + b) * c 0 (a - b) = 0 := by
        simp only [c]
        by_cases ha : a + b = 0
        · have : a - b ≠ 0 := by
            intro hb; apply h; ext <;> simp <;> omega
          simp [this]
        · simp [ha]
      rw [hc]; simp
  | t + 1, a, b => by
    set x : ℤ × ℤ := (a, b)
    let E : ℤ × ℤ → Set Ω := fun e ↦
      {ω | path X ω ∈ {y | pos y t = x - e} ∧ sh t (path X ω) ∈ {y | y 0 = e}}
    have hEm : ∀ e, MeasurableSet (E e) := fun e ↦ meas_block hX (det_pos t _) (det_zero e)
    have hsub : (((E (1, 0) ∪ E (-1, 0)) ∪ E (0, 1)) ∪ E (0, -1)) ⊆
        {ω | pos (path X ω) (t + 1) = x} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, pos_succ]
      have key : ∀ e, ω ∈ E e → pos (path X ω) t + path X ω t = x := by
        rintro e ⟨h1, h2⟩
        simp only [Set.mem_ofPred_eq] at h1 h2
        have : path X ω t = e := h2
        rw [h1, this]; abel
      rcases hω with ((h | h) | h) | h <;> exact key _ h
    have hd : ∀ e e', e ≠ e' → Disjoint (E e) (E e') := by
      intro e e' hne
      rw [Set.disjoint_left]
      rintro ω ⟨-, h1⟩ ⟨-, h2⟩
      exact hne ((show path X ω t = e from h1).symm.trans h2)
    have hsum : ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1)) ≤
        ℙ {ω | pos (path X ω) (t + 1) = x} := by
      refine le_trans (le_of_eq ?_) (measure_mono hsub)
      rw [measure_union _ (hEm _), measure_union _ (hEm _), measure_union _ (hEm _)]
      · exact hd _ _ (by decide)
      · exact Disjoint.union_left (hd _ _ (by decide)) (hd _ _ (by decide))
      · exact Disjoint.union_left (Disjoint.union_left (hd _ _ (by decide))
          (hd _ _ (by decide))) (hd _ _ (by decide))
    have hE : ∀ e ∈ steps, ℙ (E e) * 4 ^ (t + 1) =
        ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
      intro e he
      rw [prob_pos_step hX t x e he, pow_succ]
      calc ℙ {ω | pos (path X ω) t = x - e} * (4 : ℝ≥0∞)⁻¹ * (4 ^ t * 4)
          = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t * (4 * (4 : ℝ≥0∞)⁻¹) := by ring
        _ = ℙ {ω | pos (path X ω) t = x - e} * 4 ^ t := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have h1 : ((1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h2 : ((-1 : ℤ), (0 : ℤ)) ∈ steps := by simp [steps]
    have h3 : ((0 : ℤ), (1 : ℤ)) ∈ steps := by simp [steps]
    have h4 : ((0 : ℤ), (-1 : ℤ)) ∈ steps := by simp [steps]
    calc ((c (t + 1) (a + b) * c (t + 1) (a - b) : ℕ) : ℝ≥0∞)
        = ((c t ((a - 1) + b) * c t ((a - 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t ((a + 1) + b) * c t ((a + 1) - b) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b - 1)) * c t (a - (b - 1)) : ℕ) : ℝ≥0∞) +
          ((c t (a + (b + 1)) * c t (a - (b + 1)) : ℕ) : ℝ≥0∞) := by
          rw [c_step]; push_cast; ring
      _ ≤ ℙ (E (1, 0)) * 4 ^ (t + 1) + ℙ (E (-1, 0)) * 4 ^ (t + 1) +
          ℙ (E (0, 1)) * 4 ^ (t + 1) + ℙ (E (0, -1)) * 4 ^ (t + 1) := by
        rw [hE _ h1, hE _ h2, hE _ h3, hE _ h4]
        gcongr
        · have : x - (1, 0) = (a - 1, b) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (-1, 0) = (a + 1, b) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (0, 1) = (a, b - 1) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
        · have : x - (0, -1) = (a, b + 1) := by simp [x]
          rw [this]; exact prob_pos_ge hX t _ _
      _ = (ℙ (E (1, 0)) + ℙ (E (-1, 0)) + ℙ (E (0, 1)) + ℙ (E (0, -1))) * 4 ^ (t + 1) := by ring
      _ ≤ ℙ {ω | pos (path X ω) (t + 1) = x} * 4 ^ (t + 1) := by gcongr

open Real

lemma cb_sq_ge (j : ℕ) : 1 / (π * ((j : ℝ) + 1)) ≤ ((j.centralBinom : ℝ)) ^ 2 / 16 ^ j := by
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfac : ((2 * j).factorial : ℝ) = (j.centralBinom : ℝ) * (j.factorial : ℝ) ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
    rw [show 2 * j - j = j by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← h]
    push_cast; ring
  have hcb : (0 : ℝ) < (j.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos j
  have hW := Real.Wallis.W_eq_factorial_ratio j
  rw [hfac] at hW
  have hW2 : Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) = 16 ^ j := by
    rw [hW, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    rw [show (16 : ℝ) ^ j = 2 ^ (4 * j) by rw [pow_mul]; norm_num]
    ring
  have hle := Real.Wallis.W_le j
  have hpi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← hW2]
  calc Real.Wallis.W j * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1))
      ≤ π / 2 * ((j.centralBinom : ℝ) ^ 2 * (2 * j + 1)) := by gcongr
    _ ≤ (j.centralBinom : ℝ) ^ 2 * (π * ((j : ℝ) + 1)) := by nlinarith

lemma u_even_ge (hX : IsSimpleRandomWalkSteps X) (j : ℕ) :
    1 / (π * ((j : ℝ) + 1)) ≤ u X (2 * j) := by
  have h := prob_pos_ge hX (2 * j) 0 0
  simp only [add_zero, sub_zero] at h
  change _ ≤ ℙ {ω | pos (path X ω) (2 * j) = 0} * 4 ^ (2 * j) at h
  have h' : ((c (2 * j) 0 * c (2 * j) 0 : ℕ) : ℝ≥0∞).toReal ≤
      (ℙ {ω | pos (path X ω) (2 * j) = 0} * 4 ^ (2 * j)).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at h'
  simp only [ENNReal.toReal_natCast] at h'
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4, c_even, pow_mul] at h'
  norm_num at h'
  refine (cb_sq_ge j).trans ?_
  rw [div_le_iff₀ (by positivity)]
  unfold u
  nlinarith

noncomputable def p (X : ℕ → Ω → ℤ × ℤ) (z : ℤ × ℤ) (t : ℕ) : ℝ :=
  (ℙ {ω | pos (path X ω) t = z}).toReal

lemma axis_count (hX : IsSimpleRandomWalkSteps X) (a : ℤ) (t : ℕ) :
    p X (a, 0) t * 4 ^ t = (c t a : ℝ) ^ 2 := by
  have h := le_antisymm (prob_pos_le hX t a 0) (prob_pos_ge hX t a 0)
  have he := congrArg ENNReal.toReal h
  simp only [add_zero, sub_zero, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, Nat.cast_mul] at he
  change _ * _ ^ t = _ at he
  simpa only [p, show (4 : ℝ≥0∞).toReal = 4 by norm_num, pow_two] using he

lemma axis_max (hX : IsSimpleRandomWalkSteps X) {a : ℤ} (ha : 2 ∣ a) (t : ℕ) :
    p X (a, 0) t ≤ u X t := by
  have hc : c t a ≤ c t 0 := by
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t
    · by_cases h : a < -((2 * j : ℕ) : ℤ)
      · simp [c_neg _ _ h]
      · let i := ((a + (2 * j : ℕ)) / 2).toNat
        have hi : 2 * (i : ℤ) - (2 * j : ℕ) = a := by dsimp [i]; omega
        rw [← hi, c_choose, c_even]
        exact Nat.choose_le_centralBinom _ _
    · rw [c_odd (2 * j + 1) a (by push_cast; omega)]
      exact Nat.zero_le _
  have h0 : u X t * 4 ^ t = (c t 0 : ℝ) ^ 2 := axis_count hX 0 t
  apply le_of_mul_le_mul_right (a := (4 : ℝ) ^ t) ?_ (by positivity)
  rw [axis_count hX, h0]
  gcongr

lemma c_far : ∀ (t : ℕ) (a : ℤ), (t : ℤ) < |a| → c t a = 0
  | 0, a, h => by simp [c, abs_pos.mp (show 0 < |a| from h)]
  | t + 1, a, h => by
    simp only [c]
    rw [c_far t (a - 1) (by
      push_cast at h
      rcases lt_abs.mp h with hp | hn <;> apply lt_abs.mpr <;> omega),
      c_far t (a + 1) (by
      push_cast at h
      rcases lt_abs.mp h with hp | hn <;> apply lt_abs.mpr <;> omega), add_zero]

lemma axis_far (hX : IsSimpleRandomWalkSteps X) {t : ℕ} {a : ℤ} (ht : (t : ℤ) < |a|) :
    p X (a, 0) t = 0 := by
  have h := axis_count hX a t
  rw [c_far t a ht] at h
  simpa using h

def firstAt (z : ℤ × ℤ) (h : ℕ) : Set (ℕ → ℤ × ℤ) :=
  {y | pos y h = z ∧ ∀ j < h, pos y j ≠ z}

lemma det_first (z : ℤ × ℤ) (t : ℕ) : Det t (firstAt z t) :=
  fun _ _ h hy ↦ ⟨(pos_congr h le_rfl).symm.trans hy.1,
    fun j hj he ↦ hy.2 j hj ((pos_congr h hj.le).trans he)⟩

noncomputable def f (X : ℕ → Ω → ℤ × ℤ) (z : ℤ × ℤ) (h : ℕ) : ℝ :=
  (ℙ {ω | path X ω ∈ firstAt z h}).toReal

lemma renewal (hX : IsSimpleRandomWalkSteps X) (z : ℤ × ℤ) (t : ℕ) :
    p X z t = ∑ h ∈ Finset.range (t + 1), f X z h * u X (t - h) := by
  classical
  let E (h : ℕ) : Set Ω := {ω | path X ω ∈ firstAt z h ∧
    sh h (path X ω) ∈ {y | pos y (t - h) = 0}}
  have hd : Set.PairwiseDisjoint (↑(Finset.range (t + 1))) E := by
    intro h _ k _ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨hh, -⟩ ⟨hk, -⟩
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hk.2 h hlt hh.1
    · exact hh.2 k hlt hk.1
  have hU : {ω | pos (path X ω) t = z} = ⋃ h ∈ Finset.range (t + 1), E h := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · intro ht
      have hex : ∃ j, pos (path X ω) j = z := ⟨t, ht⟩
      let h := Nat.find hex
      have hh : pos (path X ω) h = z := Nat.find_spec hex
      have hle : h ≤ t := Nat.find_min' hex ht
      refine ⟨h, by omega, ⟨hh, fun j hj ↦ Nat.find_min hex hj⟩, ?_⟩
      have eq := pos_shift (path X ω) h (t - h)
      rw [Nat.add_sub_of_le hle, ht, hh] at eq
      exact add_left_cancel (show z + pos (sh h (path X ω)) (t - h) = z + 0 by simpa using eq.symm)
    · rintro ⟨h, hle, hh, hz⟩
      have eq := pos_shift (path X ω) h (t - h)
      rw [Nat.add_sub_of_le (by omega), hh.1, show pos (sh h (path X ω)) (t-h) = 0 from hz,
        add_zero] at eq
      exact eq
  unfold p
  rw [hU, measure_biUnion_finset hd (fun h _ ↦ meas_block hX (det_first z h) (det_pos (t-h) 0)),
    ENNReal.toReal_sum (fun h _ ↦ measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro h _
  change (ℙ {ω | path X ω ∈ firstAt z h ∧ sh h (path X ω) ∈ {y | pos y (t-h) = 0}}).toReal = _
  rw [prob_block hX (det_first z h) (det_pos (t-h) 0), ENNReal.toReal_mul]
  rfl

lemma weighted_summable {v : ℕ → ℝ} {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1)
    (hv : ∀ t, 0 ≤ v t) (hv1 : ∀ t, v t ≤ 1) : Summable (fun t ↦ s ^ t * v t) :=
  Summable.of_nonneg_of_le (fun t ↦ mul_nonneg (pow_nonneg hs t) (hv t))
    (fun t ↦ mul_le_of_le_one_right (pow_nonneg hs t) (hv1 t))
    (summable_geometric_of_lt_one hs hs1)

lemma prob_real_le_one (E : Set Ω) : (ℙ E).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) (prob_le_one (s := E))

noncomputable def green (X : ℕ → Ω → ℤ × ℤ) (s : ℝ) (z : ℤ × ℤ) : ℝ :=
  ∑' t, s ^ t * p X z t

lemma sum_p {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (z : ℤ × ℤ) :
    Summable (fun t ↦ s ^ t * p X z t) :=
  weighted_summable hs hs1 (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ prob_real_le_one _)

lemma green_renewal (hX : IsSimpleRandomWalkSteps X) (z : ℤ × ℤ) (hz : z ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    green X s z = (∑' k : ℕ, s ^ (k + 1) * f X z (k + 1)) * green X s 0 := by
  have hf : Summable (fun t ↦ s ^ t * f X z t) :=
    weighted_summable hs hs1 (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ prob_real_le_one _)
  have hzero : f X z 0 = 0 := by
    have he : {ω | path X ω ∈ firstAt z 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω h
      exact hz (h.1.symm.trans (pos_zero _))
    simp [f, he]
  have hshift := hf.tsum_eq_zero_add
  simp only [pow_zero, one_mul, hzero, zero_add] at hshift
  rw [← hshift]
  unfold green
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf.norm (sum_p (X := X) hs hs1 0).norm]
  apply tsum_congr
  intro t
  rw [renewal hX z t, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he : k + (t - k) = t := Nat.add_sub_of_le (by simpa using hk : k ≤ t)
  change s ^ t * (f X z k * u X (t-k)) = s ^ k * f X z k * (s ^ (t-k) * u X (t-k))
  calc _ = (s ^ k * s ^ (t-k)) * (f X z k * u X (t-k)) := by rw [← pow_add, he]
       _ = _ := by ring

lemma green_upper (hX : IsSimpleRandomWalkSteps X) {n : ℕ} (hn : 4 ≤ n) :
    green X (1 - 1 / (n : ℝ)) 0 ≤ 2 * log n := by
  let s : ℝ := 1 - 1 / n
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_iff₀ hn0]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr hn0]
  have hseries := hasSum_pow_div_log_of_abs_lt_one (show |s| < 1 by rwa [abs_of_nonneg hs])
  have hu := sum_p (X := X) hs hs1 0
  have hu' := (summable_nat_add_iff 1).mpr hu
  have htail : ∑' k : ℕ, s ^ (k + 1) * p X 0 (k+1) ≤ -log (1-s) := by
    rw [← hseries.tsum_eq]
    apply hu'.tsum_le_tsum _ hseries.summable
    intro k
    change s ^ (k+1) * u X (k+1) ≤ _
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
    refine (u_le hX (k+1) (by omega)).trans ?_
    rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [Real.pi_gt_three, mul_nonneg (show 0 ≤ π - 2 by linarith [Real.pi_gt_three])
      (show 0 ≤ (k : ℝ) by positivity)]
  have hlog : 1 ≤ log (n : ℝ) := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 4) hn4
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, log_pow] at h
    norm_num at h
    linarith [Real.log_two_gt_d9]
  have he : 1-s = (n : ℝ)⁻¹ := by simp [s, one_div]
  rw [he, log_inv, neg_neg] at htail
  change (∑' t, s ^ t * p X 0 t) ≤ _
  rw [hu.tsum_eq_zero_add]
  simp only [pow_zero, one_mul]
  linarith [show p X 0 0 ≤ 1 from prob_real_le_one _]

lemma green_gap (hX : IsSimpleRandomWalkSteps X) {n d : ℕ} (hd : 4 ≤ d) (hdn : d ≤ n)
    {a : ℤ} (ha : 2 ∣ a) (had : (d : ℤ) ≤ |a|) :
    log d ≤ 4 * π * (green X (1 - 1 / (n : ℝ)) 0 - green X (1 - 1 / (n : ℝ)) (a,0)) := by
  let s : ℝ := 1 - 1 / n
  let m := d / 4
  let D (t : ℕ) := s ^ t * p X 0 t - s ^ t * p X (a,0) t
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hd.trans hdn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_iff₀ hn0]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr hn0]
  have hD : Summable D := (sum_p (X := X) hs hs1 0).sub (sum_p hs hs1 (a,0))
  have hDpos (t : ℕ) : 0 ≤ D t :=
    sub_nonneg.mpr (mul_le_mul_of_nonneg_left (axis_max hX ha t) (pow_nonneg hs _))
  have hearly {j : ℕ} (hj : j ≤ m) : ((j : ℝ) + 1)⁻¹ ≤ 2 * π * D (2 * j) := by
    have ht : 2 * j < d := by dsimp [m] at hj; omega
    have hreach := axis_far hX ((show ((2*j : ℕ) : ℤ) < d by exact_mod_cast ht).trans_le had)
    have ht' : 4 * (j : ℝ) ≤ n := by exact_mod_cast (show 4*j ≤ n by dsimp [m] at hj; omega)
    have hpow : (1 / 2 : ℝ) ≤ s ^ (2*j) := by
      have hb := one_add_mul_le_pow (a := -(1 / (n : ℝ))) (by linarith : -2 ≤ -(1 / (n : ℝ))) (2*j)
      change _ ≤ (1 + -(1 / (n : ℝ))) ^ (2*j)
      apply le_trans _ hb
      push_cast
      field_simp
      linarith
    dsimp only [D]
    rw [hreach, mul_zero, sub_zero]
    have hlo := mul_le_mul hpow (u_even_ge hX j) (by positivity) (pow_nonneg hs _)
    change _ ≤ 2 * π * (s ^ (2*j) * u X (2*j))
    calc ((j : ℝ) + 1)⁻¹ = 2 * π * ((1/2) * (1 / (π * ((j:ℝ)+1)))) := by
          field_simp [Real.pi_ne_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  have hsub : ∑ j ∈ Finset.range (m+1), D (2*j) ≤ ∑' t, D t := by
    have he := hD.sum_le_tsum ((Finset.range (m+1)).image (fun j ↦ 2*j)) (fun t _ ↦ hDpos t)
    rwa [Finset.sum_image (by intro i _ j _ hij; dsimp at hij; omega)] at he
  have hH : (harmonic (m+1) : ℝ) ≤ 2 * π * ∑' t, D t := by
    calc (harmonic (m+1) : ℝ) = ∑ j ∈ Finset.range (m+1), ((j : ℝ)+1)⁻¹ := by
          simp [harmonic, Rat.cast_sum]
      _ ≤ ∑ j ∈ Finset.range (m+1), 2 * π * D (2*j) :=
          Finset.sum_le_sum fun j hj ↦ hearly (by simpa using hj)
      _ ≤ _ := by rw [← Finset.mul_sum]; gcongr
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hmsq : (d : ℝ) ≤ ((m:ℝ) + 2)^2 := by
    have hm : (d : ℝ) ≤ 4 * (m:ℝ) + 3 := by exact_mod_cast (show d ≤ 4*m+3 by dsimp [m]; omega)
    nlinarith [sq_nonneg (m:ℝ)]
  have hlog := log_le_log hdpos hmsq
  rw [log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hh := log_add_one_le_harmonic (m+1)
  push_cast at hh
  rw [show (m:ℝ) + 1 + 1 = (m:ℝ) + 2 by ring] at hh
  have hsum : (∑' t, D t) = green X s 0 - green X s (a,0) :=
    (sum_p hs hs1 0).tsum_sub (sum_p hs hs1 (a,0))
  rw [hsum] at hH
  change log d ≤ 4 * π * (green X s 0 - green X s (a,0))
  linarith only [hlog, hh, hH]

end OMA.AxisGreen

open OMA.AxisGreen Real

-- Credit: @MrSeizy
theorem OMA.solution : OMA.R_Erdos1164_erdos_1164_R1_H2_R1.H1 := by
  refine ⟨1 / (8 * π), by positivity, ?_⟩
  intro Ω _ _ X hX n d hd hdn a ha had
  let s : ℝ := 1 - 1 / n
  let z : ℤ × ℤ := (a,0)
  let F := ∑' k : ℕ, s ^ (k+1) * f X z (k+1)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hd.trans hdn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 ≤ s := by dsimp [s]; rw [sub_nonneg, div_le_iff₀ hn0]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith [one_div_pos.mpr hn0]
  have hz : z ≠ 0 := by
    intro he
    have h : a = 0 := congrArg Prod.fst he
    rw [h, abs_zero] at had
    omega
  have hr : green X s z = F * green X s 0 := green_renewal hX z hz hs hs1
  have hg : log d ≤ 4 * π * (green X s 0 - green X s z) := green_gap hX hd hdn ha had
  have hupper : green X s 0 ≤ 2 * log n := green_upper hX (hd.trans hdn)
  have hdlog : 0 < log (d:ℝ) := log_pos (by exact_mod_cast (show 1 < d by omega))
  have hnlog : 0 < log (n:ℝ) := log_pos (by linarith)
  rw [hr, ← one_sub_mul] at hg
  have hG : 0 ≤ green X s 0 := tsum_nonneg fun t ↦ mul_nonneg (pow_nonneg hs t) ENNReal.toReal_nonneg
  have hF : 0 ≤ 1-F := by
    by_contra! hneg
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4 * π by positivity)
      (mul_nonpos_of_nonpos_of_nonneg hneg.le hG)
    linarith
  have hbound := hg.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hupper hF)
    (show 0 ≤ 4 * π by positivity))
  change 1 / (8 * π) * log d / log n ≤ 1-F
  rw [div_le_iff₀ hnlog, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith
