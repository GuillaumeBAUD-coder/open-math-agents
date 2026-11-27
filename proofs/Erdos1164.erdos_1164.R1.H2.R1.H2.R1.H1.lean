import OMAReductions.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1

-- Credit: @DomTheDeveloper

/-!
# Last-site inequality from discounted coverage

The finite-window and discounted first-cover argument is adapted, with attribution,
from @MrSeizy, PR #2489:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2489
That source credits @koolkao for its finite-window independence argument.

The finite-measure deletion identity is adapted from @marcusbuffett, PR #2820:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2820

The new step relates first-cover weights to geometric stopping by summation by
parts, then combines the two ingredients to prove the exact last-site inequality.
-/
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


end OMA.DiscountedCover

namespace OMA1164

open MeasureTheory

lemma counting {Ω ι : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    [DecidableEq ι] (U : Finset ι) (V : ι → Set Ω) (hV : ∀ x, MeasurableSet (V x)) :
    ∑ x ∈ U, (μ {ω | ∀ y ∈ U.erase x, ω ∈ V y}).toReal =
      U.card * (μ {ω | ∀ x ∈ U, ω ∈ V x}).toReal + (μ {ω | ∃! x, x ∈ U ∧ ω ∉ V x}).toReal := by
  set F : Set Ω := {ω | ∀ x ∈ U, ω ∈ V x} with hFdef
  set G : ι → Set Ω := fun x => {ω | ω ∉ V x ∧ ∀ y ∈ U.erase x, ω ∈ V y} with hGdef
  have hG : ∀ x, MeasurableSet (G x) := by
    intro x
    have h : G x = (V x)ᶜ ∩ ⋂ y ∈ U.erase x, V y := by
      ext ω
      simp [hGdef]
    rw [h]
    exact (hV x).compl.inter (Finset.measurableSet_biInter _ fun y _ => hV y)
  have hE : ∀ x ∈ U, {ω | ∀ y ∈ U.erase x, ω ∈ V y} = F ∪ G x := by
    intro x hx
    ext ω
    constructor
    · intro h
      by_cases hω : ω ∈ V x
      · left
        intro y hy
        by_cases hyx : y = x
        · rw [hyx]
          exact hω
        · exact h y (Finset.mem_erase.2 ⟨hyx, hy⟩)
      · right
        exact ⟨hω, h⟩
    · rintro (h | h)
      · intro y hy
        exact h y (Finset.mem_of_mem_erase hy)
      · exact h.2
  have hdisj : ∀ x ∈ U, Disjoint F (G x) := by
    intro x hx
    rw [Set.disjoint_left]
    intro ω hF hGx
    exact hGx.1 (hF x hx)
  have hEm : ∀ x ∈ U, (μ {ω | ∀ y ∈ U.erase x, ω ∈ V y}).toReal =
      (μ F).toReal + (μ (G x)).toReal := by
    intro x hx
    rw [hE x hx, measure_union (hdisj x hx) (hG x),
      ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  have hGs : {ω | ∃! x, x ∈ U ∧ ω ∉ V x} = ⋃ x ∈ U, G x := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨x, ⟨hxU, hx⟩, huniq⟩
      refine ⟨x, hxU, hx, fun y hy => ?_⟩
      by_contra hyV
      exact (Finset.ne_of_mem_erase hy) (huniq y ⟨Finset.mem_of_mem_erase hy, hyV⟩)
    · rintro ⟨x, hxU, hx, hall⟩
      refine ⟨x, ⟨hxU, hx⟩, ?_⟩
      rintro y ⟨hyU, hy⟩
      by_contra hne
      exact hy (hall y (Finset.mem_erase.2 ⟨hne, hyU⟩))
  have hpd : (↑U : Set ι).PairwiseDisjoint G := by
    intro x hx y hy hxy
    show Disjoint (G x) (G y)
    rw [Set.disjoint_left]
    intro ω hωx hωy
    exact hωx.1 (hωy.2 x (Finset.mem_erase.2 ⟨hxy, hx⟩))
  have hGm : (μ {ω | ∃! x, x ∈ U ∧ ω ∉ V x}).toReal = ∑ x ∈ U, (μ (G x)).toReal := by
    rw [hGs, measure_biUnion_finset hpd (fun x _ => hG x),
      ENNReal.toReal_sum (fun x _ => measure_ne_top μ _)]
  rw [Finset.sum_congr rfl hEm, Finset.sum_add_distrib, hGm, Finset.sum_const, nsmul_eq_mul]

end OMA1164



namespace OMA.DiscountedCover

def geometric (s : ℝ) (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  s^n * a n + (1-s) * ∑ k ∈ Finset.range n, s^k * a k

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {X : ℕ → Ω → Site}

lemma done_mono {A : Finset Site} {i j : ℕ} {y : Walk}
    (hij : i ≤ j) (h : doneBy A i y) : doneBy A j y := by
  intro z hz
  obtain ⟨k, hk, he⟩ := h z hz
  exact ⟨k, hk.trans hij, he⟩

lemma done_succ (hX : IsSimpleRandomWalkSteps X) (A : Finset Site) (n : ℕ) :
    pr X {y | doneBy A (n+1) y} =
      pr X {y | doneBy A n y} + pr X (first A (n+1)) := by
  have hset : {y | doneBy A (n+1) y} =
      {y | doneBy A n y} ∪ first A (n+1) := by
    ext y
    constructor
    · intro h
      by_cases hprev : doneBy A n y
      · exact Or.inl hprev
      · exact Or.inr ⟨h, fun i hi hd => hprev (done_mono (by omega) hd)⟩
    · rintro (h | h)
      · exact done_mono (Nat.le_succ n) h
      · exact h.1
  have hdisj : Disjoint (path X ⁻¹' {y | doneBy A n y})
      (path X ⁻¹' first A (n+1)) := by
    rw [Set.disjoint_left]
    intro ω h₁ h₂
    exact h₂.2 n (Nat.lt_succ_self n) h₁
  unfold pr Measure.real
  rw [hset, Set.preimage_union, measure_union hdisj (meas_pre hX (det_first A (n+1))),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

lemma weight_eq_geometric (hX : IsSimpleRandomWalkSteps X) (A : Finset Site) (s : ℝ) (n : ℕ) :
    weight X s n (first A) = geometric s n (fun k => pr X {y | doneBy A k y}) := by
  induction n with
  | zero =>
    simp [weight, geometric, first]
  | succ n ih =>
    have hstep := done_succ hX A n
    have hw : weight X s (n+1) (first A) =
        weight X s n (first A) + s^(n+1) * pr X (first A (n+1)) := by
      unfold weight
      rw [Finset.sum_range_succ]
    rw [hw, ih]
    unfold geometric
    rw [Finset.sum_range_succ, pow_succ]
    linear_combination -(s^n*s) * hstep

end OMA.DiscountedCover

open OMA.DiscountedCover

theorem OMA.solution : OMA.R_Erdos1164_erdos_1164_R1_H2_R1_H2_R1.H1 := by
  intro Ω _ _ X hX n hn S hS h0 q hq hq1 pairs
  classical
  let s : ℝ := 1 - 1 / (n : ℝ)
  let A (U : Finset Site) (k : ℕ) : ℝ := pr X {y | doneBy U k y}
  let B (U : Finset Site) (k : ℕ) : ℝ :=
    pr X {y | ∃! x : Site, x ∈ U ∧ ¬∃ j ≤ k, pos y j = x}
  let T (a : ℕ → ℝ) : ℝ := geometric s n a
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hs : 0 ≤ s := sub_nonneg.mpr ((div_le_one hp).mpr (by linarith))
  have hs1 : s < 1 := sub_lt_self _ (by positivity)
  have count (k : ℕ) : ∑ x ∈ S, A (S.erase x) k = S.card * A S k + B S k := by
    have hpos : ∀ j, Measurable (Erdos1165.position X j) := by
      intro j
      unfold Erdos1165.position
      exact Finset.measurable_sum _ (fun i _ => hX.measurable i)
    have hV : ∀ x : Site, MeasurableSet {ω : Ω | ∃ j ≤ k, Erdos1165.position X j ω = x} := by
      intro x
      have he : {ω : Ω | ∃ j ≤ k, Erdos1165.position X j ω = x} =
          ⋃ j : ℕ, ⋃ (_ : j ≤ k), Erdos1165.position X j ⁻¹' {x} := by
        ext ω
        simp
      rw [he]
      exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
        hpos j (measurableSet_singleton x)
    exact OMA1164.counting MeasureTheory.volume S
      (fun x => {ω : Ω | ∃ j ≤ k, Erdos1165.position X j ω = x}) hV
  have total : (∑ x ∈ S, T (A (S.erase x))) = S.card * T (A S) + T (B S) := by
    dsimp only [T, geometric]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_comm (s := S) (t := Finset.range n)]
    simp_rw [← Finset.mul_sum, count, mul_add, Finset.sum_add_distrib]
    have exchange : ∑ k ∈ Finset.range n, s^k * (S.card * A S k) =
        S.card * ∑ k ∈ Finset.range n, s^k * A S k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [exchange]
    ring
  have hrec := recurrence (n := n) hX hS h0 hs hq hq1 (fun z hz w hw => by
    apply hit_sum (X := X) (z-w) hs hs1
    apply pairs z hz w
    · exact Finset.insert_subset_insert 0 (Finset.erase_subset _ _) hw
    · rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact fun he => h0 (he ▸ hz)
      · exact Finset.ne_of_mem_erase hw')
  simp_rw [weight_eq_geometric hX] at hrec
  change ((S.card : ℝ) * (1-q) + q) * T (A S) ≤
      (1-q) * ∑ x ∈ S, T (A (S.erase x)) at hrec
  rw [total] at hrec
  have hB : 0 ≤ T (B S) := by
    dsimp only [T, geometric]
    exact add_nonneg (mul_nonneg (pow_nonneg hs _) (pr_nonneg _))
      (mul_nonneg (sub_nonneg.mpr hs1.le)
        (Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg hs _) (pr_nonneg _)))
  change q * T (A S) ≤ T (B S)
  nlinarith only [hrec, mul_nonneg hq hB]

