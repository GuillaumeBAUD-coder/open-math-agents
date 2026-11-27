import OMAReductions.R_Erdos1164_erdos_1164_R1_H2_R1

-- Credit: @MrSeizy
/-!
For each finite set, discount its first-cover probability at time t by a factor of s^t.
Deleting a site lets us split a path at the first time it covers the remaining sites.
Block independence bounds the contribution from paths that visit the deleted site last.
Summing over the deleted site gives a recurrence in the size of the set.

The finite-window independence lemmas through prob_block are adapted from @koolkao's
proof of Erdos1166.erdos_1166.variants.erdos_taylor.R1.H1.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos1165

namespace OMA.DiscountedCover

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

abbrev Site := ℤ × ℤ
abbrev Walk := ℕ → Site

def doneBy (A : Finset Site) (t : ℕ) (y : Walk) : Prop :=
  ∀ z ∈ A, ∃ i ≤ t, pos y i = z

def first (A : Finset Site) (t : ℕ) : Set Walk :=
  {y | doneBy A t y ∧ ∀ i < t, ¬doneBy A i y}

def hit (z : Site) (t : ℕ) : Set Walk :=
  {y | pos y t = z ∧ ∀ i < t, pos y i ≠ z}

def lastAt (A : Finset Site) (z : Site) (t : ℕ) := first A t ∩ hit z t

def missing (B : Finset Site) (z : Site) (t : ℕ) : Set Walk :=
  {y | y ∈ first B t ∧ ∀ i ≤ t, pos y i ≠ z}

def endpoint (E : Set Walk) (w : Site) (t : ℕ) : Set Walk :=
  {y | y ∈ E ∧ pos y t = w}

lemma done_congr {A : Finset Site} {i t : ℕ} {y y' : Walk}
    (h : ∀ j < t, y j = y' j) (hi : i ≤ t) : doneBy A i y ↔ doneBy A i y' := by
  unfold doneBy
  constructor <;> intro hd z hz <;> obtain ⟨j, hj, he⟩ := hd z hz
  · exact ⟨j, hj, (pos_congr h (hj.trans hi)).symm.trans he⟩
  · exact ⟨j, hj, (pos_congr h (hj.trans hi)).trans he⟩

lemma det_first (A : Finset Site) (t : ℕ) : Det t (first A t) := by
  intro y y' h ⟨hd, he⟩
  exact ⟨(done_congr h le_rfl).mp hd, fun i hi hd' ↦
    he i hi ((done_congr h hi.le).mpr hd')⟩

lemma det_hit (z : Site) (t : ℕ) : Det t (hit z t) := by
  intro y y' h ⟨he, hn⟩
  exact ⟨(pos_congr h le_rfl).symm.trans he, fun i hi h' ↦
    hn i hi ((pos_congr h hi.le).trans h')⟩

lemma det_missing (B : Finset Site) (z : Site) (t : ℕ) : Det t (missing B z t) := by
  intro y y' h ⟨hf, hm⟩
  exact ⟨det_first B t y y' h hf, fun i hi he ↦ hm i hi ((pos_congr h hi).trans he)⟩

lemma det_endpoint {E : Set Walk} {t : ℕ} (hE : Det t E) (w : Site) :
    Det t (endpoint E w t) := by
  intro y y' h ⟨he, hp⟩
  exact ⟨hE _ _ h he, (pos_congr h le_rfl).symm.trans hp⟩

lemma exists_first {A : Finset Site} {t : ℕ} {y : Walk} (h : doneBy A t y) :
    ∃ i ≤ t, y ∈ first A i := by
  classical
  have hex : ∃ i, doneBy A i y := ⟨t, h⟩
  exact ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, fun _ ↦ Nat.find_min hex⟩

lemma first_endpoint {A : Finset Site} {t : ℕ} {y : Walk} (hf : y ∈ first A t) :
    pos y t ∈ insert 0 A := by
  classical
  cases t with
  | zero => simp [pos]
  | succ k =>
    have hn := hf.2 k (Nat.lt_succ_self k)
    unfold doneBy at hn
    push Not at hn
    obtain ⟨z, hz, hn⟩ := hn
    obtain ⟨i, hi, he⟩ := hf.1 z hz
    have : i = k + 1 := by by_contra hh; exact hn i (by omega) he
    subst i
    exact Finset.mem_insert_of_mem (he ▸ hz)

lemma exists_last {A : Finset Site} (ha : A.Nonempty) (h0 : 0 ∉ A) {t : ℕ} {y : Walk}
    (hf : y ∈ first A t) : ∃ z ∈ A, y ∈ lastAt A z t := by
  classical
  cases t with
  | zero =>
    obtain ⟨z, hz⟩ := ha
    obtain ⟨i, hi, he⟩ := hf.1 z hz
    have : z = 0 := by simpa [Nat.le_zero.mp hi, pos] using he.symm
    exact (h0 (this ▸ hz)).elim
  | succ k =>
    have hn := hf.2 k (Nat.lt_succ_self k)
    unfold doneBy at hn
    push Not at hn
    obtain ⟨z, hz, hn⟩ := hn
    obtain ⟨i, hi, he⟩ := hf.1 z hz
    have : i = k + 1 := by by_contra hh; exact hn i (by omega) he
    subst i
    exact ⟨z, hz, hf, he, fun i hi ↦ hn i (by omega)⟩

lemma first_split {A : Finset Site} {z : Site} (hz : z ∈ A) {t : ℕ} :
    first A t ⊆ (first (A.erase z) t \ missing (A.erase z) z t) ∪ lastAt A z t := by
  classical
  intro y hf
  have hb : doneBy (A.erase z) t y := fun x hx ↦ hf.1 x (Finset.mem_of_mem_erase hx)
  obtain ⟨j, hj, he⟩ := hf.1 z hz
  by_cases hl : y ∈ hit z t
  · exact Or.inr ⟨hf, hl⟩
  left
  have hprev : ∃ k < t, pos y k = z := by
    by_contra! hn
    exact hl ⟨by rwa [show t = j by by_contra h; exact hn j (by omega) he], hn⟩
  obtain ⟨k, hk, he'⟩ := hprev
  refine ⟨⟨hb, ?_⟩, fun hm ↦ hm.2 j hj he⟩
  intro i hi hd
  apply hf.2 (max i k) (max_lt hi hk)
  intro x hx
  by_cases h : x = z
  · exact ⟨k, le_max_right .., he'.trans h.symm⟩
  · obtain ⟨a, ha, he⟩ := hd x (Finset.mem_erase.mpr ⟨h, hx⟩)
    exact ⟨a, ha.trans (le_max_left ..), he⟩

/-- Split a cover ending at z at the first time it covered all sites other than z. -/
lemma last_blocks {A : Finset Site} {z : Site} (h0 : z ≠ 0) {r : ℕ} {y : Walk}
    (hl : y ∈ lastAt A z r) :
    ∃ t < r, ∃ w ∈ insert 0 (A.erase z), ∃ k < r, t + (k+1) = r ∧
      y ∈ endpoint (missing (A.erase z) z t) w t ∧ sh t y ∈ hit (z-w) (k+1) := by
  classical
  obtain ⟨hf, hp, hn⟩ := hl
  cases r with
  | zero => exact (h0 (by simpa [pos] using hp.symm)).elim
  | succ r =>
    have hb : doneBy (A.erase z) r y := by
      intro x hx
      obtain ⟨j, hj, he⟩ := hf.1 x (Finset.mem_of_mem_erase hx)
      exact ⟨j, by by_contra hh; have : j = r+1 := by omega
                   exact (Finset.ne_of_mem_erase hx) (he.symm.trans (this ▸ hp)), he⟩
    obtain ⟨t, ht, hft⟩ := exists_first hb
    have heq : t + (r-t+1) = r+1 := by omega
    refine ⟨t, by omega, pos y t, first_endpoint hft, r-t, by omega, heq,
      ⟨⟨hft, fun i hi ↦ hn i (by omega)⟩, rfl⟩, ?_, ?_⟩
    · rw [← heq, pos_shift] at hp
      exact eq_sub_of_add_eq' hp
    · intro i hi he
      apply hn (t+i) (by omega)
      rw [pos_shift, he, add_sub_cancel]

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {X : ℕ → Ω → Site}

noncomputable def pr (X : ℕ → Ω → Site) (E : Set Walk) : ℝ := (ℙ : Measure Ω).real (path X ⁻¹' E)

noncomputable def weight (X : ℕ → Ω → Site) (s : ℝ) (n : ℕ) (E : ℕ → Set Walk) : ℝ :=
  ∑ t ∈ Finset.range (n+1), s^t * pr X (E t)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma pr_nonneg (E : Set Walk) : 0 ≤ pr X E := measureReal_nonneg
lemma pr_le_one (E : Set Walk) : pr X E ≤ 1 := by
  unfold pr Measure.real
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (show (ℙ : Measure Ω) (path X ⁻¹' E) ≤ 1 from prob_le_one)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
lemma meas_pre (hX : IsSimpleRandomWalkSteps X) {t : ℕ} {E : Set Walk} (h : Det t E) :
    MeasurableSet (path X ⁻¹' E) := by
  simpa only [sh_zero, Set.preimage] using det_meas hX h 0

lemma pr_cover {ι : Type*} {I : Finset ι} {D : ι → Set Walk} {E : Set Walk}
    (h : ∀ y ∈ E, ∃ i ∈ I, y ∈ D i) : pr X E ≤ ∑ i ∈ I, pr X (D i) := by
  apply le_trans (b := (ℙ : Measure Ω).real (⋃ i ∈ I, path X ⁻¹' D i))
  · refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    simpa only [Set.mem_iUnion, exists_prop, Set.mem_preimage] using h _ hω
  · exact measureReal_biUnion_finset_le _ _

lemma weight_cover {ι : Type*} {I : Finset ι} {D : ι → Set Walk} {time : ι → ℕ}
    {E : ℕ → Set Walk} {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ r ≤ n, ∀ y ∈ E r, ∃ i ∈ I, time i = r ∧ y ∈ D i) :
    weight X s n E ≤ ∑ i ∈ I, s^(time i) * pr X (D i) := by
  classical
  calc
    _ ≤ ∑ r ∈ Finset.range (n+1), ∑ i ∈ I,
          if time i = r then s^(time i) * pr X (D i) else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      have hb : pr X (E r) ≤ ∑ i ∈ I.filter (fun i ↦ time i = r), pr X (D i) := by
        apply pr_cover
        intro y hy
        obtain ⟨i, hi, he, hd⟩ := h r (by simpa using hr) y hy
        exact ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩, hd⟩
      apply (mul_le_mul_of_nonneg_left hb (pow_nonneg hs r)).trans_eq
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with he <;> simp_all
    _ ≤ _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro i hi
      simp only [Finset.sum_ite_eq]
      split_ifs <;> first | rfl | exact mul_nonneg (pow_nonneg hs _) (pr_nonneg _)

lemma endpoint_sum (hX : IsSimpleRandomWalkSteps X) {t : ℕ} {E : Set Walk} (hE : Det t E)
    (W : Finset Site) (hc : ∀ y ∈ E, pos y t ∈ W) :
    ∑ w ∈ W, pr X (endpoint E w t) = pr X E := by
  classical
  unfold pr
  rw [← measureReal_biUnion_finset]
  · congr 1
    ext ω
    simp only [Set.mem_iUnion, exists_prop, Set.mem_preimage]
    exact ⟨fun ⟨_, _, he⟩ ↦ he.1, fun he ↦ ⟨_, hc _ he, he, rfl⟩⟩
  · intro a ha b hb hab
    exact Set.disjoint_left.mpr fun _ h₁ h₂ ↦ hab (h₁.2.symm.trans h₂.2)
  · exact fun w _ ↦ meas_pre hX (det_endpoint hE w)

lemma hit_sum (z : Site) {n : ℕ} {s q : ℝ} (hs : 0 ≤ s) (hs' : s < 1)
    (hq : q ≤ 1 - ∑' k : ℕ, s^(k+1) * pr X (hit z (k+1))) :
    ∑ k ∈ Finset.range n, s^(k+1) * pr X (hit z (k+1)) ≤ 1-q := by
  have hg := summable_geometric_of_lt_one hs hs'
  have hsm : Summable (fun k : ℕ ↦ s^(k+1) * pr X (hit z (k+1))) := by
    apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (pow_nonneg hs _) (pr_nonneg _))
      (f := fun k : ℕ ↦ s^k * s)
    · intro k
      rw [← pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hs _) (pr_le_one _)
    · exact hg.mul_right _
  exact (hsm.sum_le_tsum _ (fun _ _ ↦ mul_nonneg (pow_nonneg hs _) (pr_nonneg _))).trans
    (by linarith)

/-- The discounted weight of a final visit to the missing site is bounded by the
weight of eligible prefixes times the discounted hitting bound. -/
lemma last_bound (hX : IsSimpleRandomWalkSteps X) {A : Finset Site} {z : Site} (hz : z ≠ 0)
    {s q : ℝ} {n : ℕ} (hs : 0 ≤ s)
    (hh : ∀ w ∈ insert 0 (A.erase z),
      ∑ k ∈ Finset.range n, s^(k+1) * pr X (hit (z-w) (k+1)) ≤ 1-q) :
    weight X s n (lastAt A z) ≤ (1-q) * weight X s n (missing (A.erase z) z) := by
  classical
  let B := A.erase z
  let W := insert 0 B
  let R := Finset.range (n+1)
  let I := R ×ˢ (W ×ˢ Finset.range n)
  let D (i : ℕ × Site × ℕ) : Set Walk :=
    {y | y ∈ endpoint (missing B z i.1) i.2.1 i.1 ∧
      sh i.1 y ∈ hit (z-i.2.1) (i.2.2+1)}
  let time (i : ℕ × Site × ℕ) := i.1 + (i.2.2+1)
  have hcov : weight X s n (lastAt A z) ≤ ∑ i ∈ I, s^(time i) * pr X (D i) := by
    apply weight_cover hs
    intro r hr y hy
    obtain ⟨t, ht, w, hw, k, hk, he, hp⟩ := last_blocks hz hy
    refine ⟨(t,w,k), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_product.mpr ⟨hw, Finset.mem_range.mpr (hk.trans_le hr)⟩⟩, he, hp⟩
  refine hcov.trans ?_
  have hblock (t : ℕ) (w : Site) (k : ℕ) :
      pr X (D (t,w,k)) = pr X (endpoint (missing B z t) w t) * pr X (hit (z-w) (k+1)) := by
    unfold pr Measure.real
    rw [← ENNReal.toReal_mul]
    exact congrArg ENNReal.toReal (prob_block hX
      (det_endpoint (det_missing B z t) w) (det_hit (z-w) (k+1)))
  simp only [I, Finset.sum_product, time, hblock, pow_add]
  unfold weight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  calc
    _ = ∑ w ∈ W, (s^t * pr X (endpoint (missing B z t) w t)) *
          ∑ k ∈ Finset.range n, s^(k+1) * pr X (hit (z-w) (k+1)) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ ≤ ∑ w ∈ W, (s^t * pr X (endpoint (missing B z t) w t)) * (1-q) :=
      Finset.sum_le_sum fun w hw ↦ mul_le_mul_of_nonneg_left (hh w hw)
        (mul_nonneg (pow_nonneg hs _) (pr_nonneg _))
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, endpoint_sum hX (det_missing B z t) W
        (fun _ h ↦ first_endpoint h.1)]
      ring

/-- Covers ending at any other site also finish the erased set at the same time. -/
lemma split_bound (hX : IsSimpleRandomWalkSteps X) {A : Finset Site} {z : Site} (hz : z ∈ A)
    {s : ℝ} {n : ℕ} (hs : 0 ≤ s) :
    weight X s n (first A) + weight X s n (missing (A.erase z) z) ≤
      weight X s n (first (A.erase z)) + weight X s n (lastAt A z) := by
  unfold weight
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  rw [← mul_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
  let B := A.erase z
  have hsub : path X ⁻¹' first A t ⊆
      (path X ⁻¹' first B t \ path X ⁻¹' missing B z t) ∪ path X ⁻¹' lastAt A z t :=
    fun _ h ↦ first_split hz h
  have hm := (measureReal_mono (μ := (ℙ : Measure Ω)) hsub).trans (measureReal_union_le _ _)
  rw [measureReal_sdiff (μ := (ℙ : Measure Ω)) (s₁ := path X ⁻¹' first B t) (fun _ h ↦ h.1) (meas_pre hX (det_missing B z t))] at hm
  change pr X (first A t) ≤ pr X (first B t) - pr X (missing B z t) + pr X (lastAt A z t) at hm
  dsimp [B] at hm
  linarith

lemma sum_last (A : Finset Site) (ha : A.Nonempty) (h0 : 0 ∉ A) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    weight X s n (first A) ≤ ∑ z ∈ A, weight X s n (lastAt A z) := by
  unfold weight
  rw [Finset.sum_comm (s := A)]
  apply Finset.sum_le_sum
  intro t ht
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (pr_cover (fun _ h ↦ exists_last ha h0 h)) (pow_nonneg hs _)

/-- Sum the deletion inequalities over all possible last sites. -/
lemma recurrence (hX : IsSimpleRandomWalkSteps X) {A : Finset Site} (ha : A.Nonempty) (h0 : 0 ∉ A)
    {s q : ℝ} {n : ℕ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (hh : ∀ z ∈ A, ∀ w ∈ insert 0 (A.erase z),
      ∑ k ∈ Finset.range n, s^(k+1) * pr X (hit (z-w) (k+1)) ≤ 1-q) :
    ((A.card : ℝ) * (1-q) + q) * weight X s n (first A) ≤
      (1-q) * ∑ z ∈ A, weight X s n (first (A.erase z)) := by
  let F := weight X s n (first A)
  let L := fun z ↦ weight X s n (lastAt A z)
  have hi (z : Site) (hz : z ∈ A) :
      (1-q)*F + q*L z ≤ (1-q)*weight X s n (first (A.erase z)) := by
    have hl := last_bound hX (fun he ↦ h0 (he ▸ hz)) hs (hh z hz)
    have hd := mul_le_mul_of_nonneg_left (split_bound (n := n) hX hz hs) (sub_nonneg.mpr hq')
    dsimp [F,L]
    linarith only [hl, hd]
  have hsum := Finset.sum_le_sum hi
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hL := mul_le_mul_of_nonneg_left (sum_last (X := X) A ha h0 hs n) hq
  change q * F ≤ q * ∑ z ∈ A, L z at hL
  change (_ * _ + _) * F ≤ _
  linarith only [hsum, hL]

lemma weight_empty (s : ℝ) (n : ℕ) : weight X s n (first ∅) = 1 := by
  classical
  have h (t : ℕ) : first ∅ t = if t = 0 then Set.univ else ∅ := by
    ext y
    by_cases ht : t = 0
    · simp [ht, first, doneBy]
    · simp [ht, first, doneBy]
      exact ⟨0, Nat.pos_of_ne_zero ht⟩
  simp [weight, h, pr, apply_ite, Finset.sum_ite_eq', Measure.real]

lemma scalar_step {k q f : ℝ} (hk : 1 ≤ k) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (h : (k*(1-q)+q)*f ≤ (1-q)*k*Real.exp (-q*Real.log k)) :
    f ≤ Real.exp (-q*Real.log (k+1)) := by
  let e := Real.exp (-q*Real.log k)
  have hk0 : 0 < k := by linarith
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hc : 0 < k*(1-q)+q := by nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hq')]
  have hfac : (1-q)*k ≤ (k*(1-q)+q)*(1-q/k) := by
    field_simp [hk0.ne']
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg q)]
  have hf : f ≤ (1-q/k)*e := by
    apply le_of_mul_le_mul_left _ hc
    calc
      _ ≤ (1-q)*k*e := h
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hfac he
  have hstep : Real.log (k+1) - Real.log k ≤ 1/k := by
    rw [← Real.log_div (by linarith) hk0.ne']
    have hl := Real.log_le_sub_one_of_pos (show 0 < (k+1)/k by positivity)
    convert hl using 1
    field_simp
    ring
  calc
    f ≤ (1-q/k)*e := hf
    _ ≤ Real.exp (-(q/k))*e := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg _) he
    _ = Real.exp (-(q/k) + -q*Real.log k) := (Real.exp_add ..).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hstep hq
      simp only [div_eq_mul_inv, one_mul] at hh ⊢
      linarith only [hh]

lemma weight_bound (hX : IsSimpleRandomWalkSteps X) {S : Finset Site} (h0 : 0 ∉ S)
    {s q : ℝ} {n : ℕ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (hh : ∀ z ∈ S, ∀ w ∈ insert 0 S, w ≠ z →
      ∑ k ∈ Finset.range n, s^(k+1) * pr X (hit (z-w) (k+1)) ≤ 1-q) :
    weight X s n (first S) ≤ Real.exp (-q * Real.log ((S.card : ℝ)+1)) := by
  classical
  suffices H : ∀ A : Finset Site, A ⊆ S →
      weight X s n (first A) ≤ Real.exp (-q * Real.log ((A.card : ℝ)+1)) from H S (by rfl)
  intro A
  induction A using Finset.eraseInduction with
  | H A ih =>
    intro hA
    rcases A.eq_empty_or_nonempty with rfl | ha
    · simp [weight_empty]
    have h0A : 0 ∉ A := fun h ↦ h0 (hA h)
    have hrec := recurrence (n := n) hX ha h0A hs hq hq' (fun z hz w hw ↦ by
      apply hh z (hA hz) w
      · exact Finset.insert_subset_insert 0 (Finset.erase_subset _ _ |>.trans hA) hw
      · rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact fun he ↦ h0A (he ▸ hz)
        · exact Finset.ne_of_mem_erase hw')
    have he (z : Site) (hz : z ∈ A) :
        weight X s n (first (A.erase z)) ≤ Real.exp (-q*Real.log A.card) := by
      have h := ih z hz ((Finset.erase_subset _ _).trans hA)
      have hc : ((A.erase z).card : ℝ) + 1 = A.card := by
        exact_mod_cast Finset.card_erase_add_one hz
      rwa [hc] at h
    have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum he) (sub_nonneg.mpr hq')
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    apply scalar_step (by exact_mod_cast ha.card_pos) hq hq'
    simpa only [mul_assoc] using hrec.trans hsum

lemma remove_discount (A : Finset Site) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    s^n * pr X {y | doneBy A n y} ≤ weight X s n (first A) := by
  have hcov : pr X {y | doneBy A n y} ≤ ∑ t ∈ Finset.range (n+1), pr X (first A t) := by
    apply pr_cover
    intro y hy
    obtain ⟨t, ht, he⟩ := exists_first hy
    exact ⟨t, Finset.mem_range.mpr (by omega), he⟩
  apply (mul_le_mul_of_nonneg_left hcov (pow_nonneg hs _)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs hs' (by simpa using ht)) (pr_nonneg _)

lemma discount_quarter (n : ℕ) (hn : 2 ≤ n) : 1/4 ≤ (1 - (1 : ℝ)/n)^n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hs : 0 < 1 - (1 : ℝ)/n := sub_pos.mpr ((div_lt_one hp).mpr (by linarith))
  have hj := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1/2 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 0 ≤ 2/(n : ℝ) by positivity) (sub_nonneg.mpr ((div_le_one hp).mpr hn')) (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, mul_one] at hj
  rw [show 2/(n : ℝ)*(1/2) + (1-2/n) = 1-1/n by ring] at hj
  apply (Real.log_le_log_iff (by norm_num) (pow_pos hs _)).mp
  rw [show (1/4 : ℝ) = (1/2 : ℝ)^2 by norm_num, Real.log_pow, Real.log_pow]
  have hm := mul_le_mul_of_nonneg_left hj hp.le
  rw [← mul_assoc, show (n : ℝ) * (2/n) = 2 by field_simp] at hm
  exact_mod_cast hm

end OMA.DiscountedCover

open OMA.DiscountedCover

theorem OMA.solution : OMA.R_Erdos1164_erdos_1164_R1_H2_R1.H2 := by
  intro Ω _ _ X hX n hn S hS h0 q hq hq' hh
  let s := 1 - (1 : ℝ)/n
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hs : 0 ≤ s := sub_nonneg.mpr ((div_le_one hp).mpr (by linarith))
  have hs' : s < 1 := sub_lt_self _ (by positivity)
  have hW := weight_bound (n := n) hX h0 hs hq hq' (fun z hz w hw hne ↦
    hit_sum (X := X) (z-w) hs hs' (hh z hz w hw hne))
  let p := pr X {y | doneBy S n y}
  have hP : 1/4*p ≤ Real.exp (-q*Real.log ((S.card : ℝ)+1)) :=
    (mul_le_mul_of_nonneg_right (discount_quarter n hn) (pr_nonneg _)).trans
      ((remove_discount S n hs hs'.le).trans hW)
  have hc : 1 ≤ (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hlog := Real.log_nonneg hc
  have hlog' := Real.log_le_log (by linarith : 0 < (S.card : ℝ))
    (show (S.card : ℝ) ≤ S.card+1 by linarith)
  have hex : Real.exp (-q*Real.log ((S.card : ℝ)+1)) ≤
      Real.exp (-(q/2)*Real.log (S.card : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog' hq, mul_nonneg hq hlog]
  change p ≤ _
  linarith only [hP, hex]
