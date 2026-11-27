import FormalConjectures.ErdosProblems.«533»

/-!
# Lower bound `δ₃(5) ≥ 1/12` (Erdős Problem 533, LRSS21)

Self-contained Lean 4 proof of `Erdos533.erdos_533.variants.lrss_lower`, following the
complex-sphere construction of Liu, Reiher, Sharifzadeh, and Staden (2021):
1. Multiplicative Brunn-Minkowski via Hadwiger-Ohmann box splitting.
2. Two-set concentration on real unit spheres via truncated cones.
3. Spherical strip bound via Householder reflection and cylinder comparison.
4. Complex-sphere order-3 rotation graph (`K₅`-free, density `≥ 1/12 - ε`, triangle-free sets `≤ δn`).
5. Finite open-ball partition, 3-fold rotation averaging, and floor blow-up on `Fin n`.
-/

open Filter SimpleGraph Set MeasureTheory
open scoped ENNReal NNReal Pointwise Topology BigOperators RealInnerProductSpace

namespace Erdos533LRSS

/- ## Part 1: Multiplicative Brunn-Minkowski via Hadwiger-Ohmann -/

structure OpenBox (h : ℕ) where
  lo : Fin h → ℝ
  hi : Fin h → ℝ
  lt : ∀ i, lo i < hi i

namespace OpenBox

variable {h : ℕ}

def toSet (B : OpenBox h) : Set (Fin h → ℝ) :=
  Set.univ.pi fun i => Set.Ioo (B.lo i) (B.hi i)

def vol (B : OpenBox h) : ℝ :=
  ∏ i : Fin h, (B.hi i - B.lo i)

lemma vol_pos (B : OpenBox h) : 0 < B.vol :=
  Finset.prod_pos fun i _ => sub_pos.mpr (B.lt i)

lemma vol_nonneg (B : OpenBox h) : 0 ≤ B.vol :=
  B.vol_pos.le

lemma isOpen_toSet (B : OpenBox h) : IsOpen B.toSet :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

lemma volume_toSet (B : OpenBox h) : volume B.toSet = ENNReal.ofReal B.vol := by
  rw [toSet, MeasureTheory.volume_pi, Measure.pi_pi]
  simp only [Real.volume_Ioo]
  rw [vol, ENNReal.ofReal_prod_of_nonneg fun i _ => sub_nonneg.mpr (B.lt i).le]

def add (A B : OpenBox h) : OpenBox h where
  lo := fun i => A.lo i + B.lo i
  hi := fun i => A.hi i + B.hi i
  lt := fun i => add_lt_add (A.lt i) (B.lt i)

lemma add_toSet_subset (A B : OpenBox h) : (A.add B).toSet ⊆ A.toSet + B.toSet := by
  intro x hx
  have hcoord : ∀ i : Fin h,
      ∃ u v : ℝ, u ∈ Set.Ioo (A.lo i) (A.hi i) ∧ v ∈ Set.Ioo (B.lo i) (B.hi i) ∧ u + v = x i := by
    intro i
    have hxi := hx i (Set.mem_univ i)
    simp only [add, Set.mem_Ioo] at hxi
    set da := A.hi i - A.lo i
    set db := B.hi i - B.lo i
    have hda : 0 < da := sub_pos.mpr (A.lt i)
    have hdb : 0 < db := sub_pos.mpr (B.lt i)
    have hdab : 0 < da + db := add_pos hda hdb
    set t := (x i - A.lo i - B.lo i) / (da + db)
    have ht0 : 0 < t := div_pos (by linarith) hdab
    have ht1 : t < 1 := (div_lt_one hdab).mpr (by linarith)
    refine ⟨A.lo i + t * da, B.lo i + t * db, ?_, ?_, ?_⟩
    · constructor <;> nlinarith
    · constructor <;> nlinarith
    · have : t * (da + db) = x i - A.lo i - B.lo i := div_mul_cancel₀ _ hdab.ne'
      linarith
  choose u v hu hv huv using hcoord
  refine ⟨u, fun i _ => hu i, v, fun i _ => hv i, ?_⟩
  ext i
  exact huv i

lemma vol_add_ge (A B : OpenBox h) :
    (2 : ℝ) ^ h * Real.sqrt (A.vol * B.vol) ≤ (A.add B).vol := by
  have h1 : ∀ i : Fin h,
      2 * Real.sqrt ((A.hi i - A.lo i) * (B.hi i - B.lo i)) ≤
        (A.hi i + B.hi i) - (A.lo i + B.lo i) := by
    intro i
    have ha : 0 ≤ A.hi i - A.lo i := sub_nonneg.mpr (A.lt i).le
    have hb : 0 ≤ B.hi i - B.lo i := sub_nonneg.mpr (B.lt i).le
    have hsq : 0 ≤ (Real.sqrt (A.hi i - A.lo i) - Real.sqrt (B.hi i - B.lo i)) ^ 2 := sq_nonneg _
    rw [Real.sqrt_mul ha]
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
  have hprod :
      ∏ i : Fin h, (2 * Real.sqrt ((A.hi i - A.lo i) * (B.hi i - B.lo i))) ≤
        ∏ i : Fin h, ((A.hi i + B.hi i) - (A.lo i + B.lo i)) :=
    Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => h1 i)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hsqrt :
      ∏ i : Fin h, Real.sqrt ((A.hi i - A.lo i) * (B.hi i - B.lo i)) =
        Real.sqrt (A.vol * B.vol) := by
    rw [← Real.sqrt_prod _ (fun i _ => mul_nonneg (sub_nonneg.mpr (A.lt i).le) (sub_nonneg.mpr (B.lt i).le))]
    simp only [vol, Finset.prod_mul_distrib]
  rw [hsqrt] at hprod
  exact hprod

noncomputable def cutLeft (B : OpenBox h) (j : Fin h) (c : ℝ) : Option (OpenBox h) := by
  classical
  exact if hc : B.lo j < c then
    some ⟨B.lo, Function.update B.hi j (min (B.hi j) c), fun i => by
      by_cases hij : i = j
      · subst hij; simp [lt_min (B.lt i) hc]
      · simp [hij, B.lt i]⟩
  else none

noncomputable def cutRight (B : OpenBox h) (j : Fin h) (c : ℝ) : Option (OpenBox h) := by
  classical
  exact if hc : c < B.hi j then
    some ⟨Function.update B.lo j (max (B.lo j) c), B.hi, fun i => by
      by_cases hij : i = j
      · subst hij; simp [max_lt (B.lt i) hc]
      · simp [hij, B.lt i]⟩
  else none

lemma cutLeft_subset {B B' : OpenBox h} {j : Fin h} {c : ℝ}
    (hB' : B.cutLeft j c = some B') :
    B'.toSet ⊆ B.toSet ∧ ∀ x ∈ B'.toSet, x j < c := by
  classical
  simp only [cutLeft] at hB'
  split_ifs at hB' with hc
  cases hB'
  refine ⟨fun x hx i _ => ?_, fun x hx => ?_⟩
  · have hxi := hx i (Set.mem_univ i)
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self, Set.mem_Ioo] at hxi
      exact ⟨hxi.1, lt_of_lt_of_le hxi.2 (min_le_left _ _)⟩
    · simpa [Function.update_of_ne hij] using hxi
  · have hxj := hx j (Set.mem_univ j)
    simp only [Function.update_self, Set.mem_Ioo] at hxj
    exact lt_of_lt_of_le hxj.2 (min_le_right _ _)

lemma cutRight_subset {B B' : OpenBox h} {j : Fin h} {c : ℝ}
    (hB' : B.cutRight j c = some B') :
    B'.toSet ⊆ B.toSet ∧ ∀ x ∈ B'.toSet, c < x j := by
  classical
  simp only [cutRight] at hB'
  split_ifs at hB' with hc
  cases hB'
  refine ⟨fun x hx i _ => ?_, fun x hx => ?_⟩
  · have hxi := hx i (Set.mem_univ i)
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self, Set.mem_Ioo] at hxi
      exact ⟨lt_of_le_of_lt (le_max_left _ _) hxi.1, hxi.2⟩
    · simpa [Function.update_of_ne hij] using hxi
  · have hxj := hx j (Set.mem_univ j)
    simp only [Function.update_self, Set.mem_Ioo] at hxj
    exact lt_of_le_of_lt (le_max_right _ _) hxj.1

def restVol (B : OpenBox h) (j : Fin h) : ℝ :=
  ∏ i ∈ Finset.univ.erase j, (B.hi i - B.lo i)

lemma vol_eq_mul_restVol (B : OpenBox h) (j : Fin h) :
    B.vol = (B.hi j - B.lo j) * B.restVol j := by
  rw [vol, restVol, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]

def leftVolFn (B : OpenBox h) (j : Fin h) (c : ℝ) : ℝ :=
  max 0 (min (B.hi j) c - B.lo j) * B.restVol j

def rightVolFn (B : OpenBox h) (j : Fin h) (c : ℝ) : ℝ :=
  max 0 (B.hi j - max (B.lo j) c) * B.restVol j

lemma leftVolFn_eq_opt (B : OpenBox h) (j : Fin h) (c : ℝ) :
    (match B.cutLeft j c with | some B' => B'.vol | none => 0) = B.leftVolFn j c := by
  classical
  simp only [cutLeft, leftVolFn]
  split_ifs with hc
  · dsimp only
    rw [vol_eq_mul_restVol _ j]
    simp only [restVol, Function.update_self]
    have hrest : ∏ i ∈ Finset.univ.erase j, (Function.update B.hi j (min (B.hi j) c) i - B.lo i) =
        ∏ i ∈ Finset.univ.erase j, (B.hi i - B.lo i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hrest]
    have hpos : 0 ≤ min (B.hi j) c - B.lo j := by
      have := lt_min (B.lt j) hc; linarith
    rw [max_eq_right hpos]
  · dsimp only
    have hle : min (B.hi j) c - B.lo j ≤ 0 := by
      have : c ≤ B.lo j := not_lt.mp hc
      exact sub_nonpos.mpr (le_trans (min_le_right _ _) this)
    rw [max_eq_left hle, zero_mul]

lemma rightVolFn_eq_opt (B : OpenBox h) (j : Fin h) (c : ℝ) :
    (match B.cutRight j c with | some B' => B'.vol | none => 0) = B.rightVolFn j c := by
  classical
  simp only [cutRight, rightVolFn]
  split_ifs with hc
  · dsimp only
    rw [vol_eq_mul_restVol _ j]
    simp only [restVol, Function.update_self]
    have hrest : ∏ i ∈ Finset.univ.erase j, (B.hi i - Function.update B.lo j (max (B.lo j) c) i) =
        ∏ i ∈ Finset.univ.erase j, (B.hi i - B.lo i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hrest]
    have hpos : 0 ≤ B.hi j - max (B.lo j) c := by
      have := max_lt (B.lt j) hc; linarith
    rw [max_eq_right hpos]
  · dsimp only
    have hle : B.hi j - max (B.lo j) c ≤ 0 := by
      have : B.hi j ≤ c := not_lt.mp hc
      exact sub_nonpos.mpr (le_trans this (le_max_right _ _))
    rw [max_eq_left hle, zero_mul]

lemma leftVolFn_add_rightVolFn (B : OpenBox h) (j : Fin h) (c : ℝ) :
    B.leftVolFn j c + B.rightVolFn j c = B.vol := by
  rw [leftVolFn, rightVolFn, vol_eq_mul_restVol B j, ← add_mul]
  congr 1
  have hlt := B.lt j
  rcases le_total c (B.lo j) with h1 | h1
  · rw [min_eq_right (le_trans h1 hlt.le), max_eq_left (by linarith),
        max_eq_left h1, max_eq_right (by linarith)]
    ring
  · rcases le_total c (B.hi j) with h2 | h2
    · rw [min_eq_right h2, max_eq_right h1,
          max_eq_right (by linarith), max_eq_right (by linarith)]
      ring
    · rw [min_eq_left h2, max_eq_right (by linarith),
          max_eq_right (le_trans hlt.le h2), max_eq_left (by linarith)]
      ring

lemma continuous_leftVolFn (B : OpenBox h) (j : Fin h) :
    Continuous (B.leftVolFn j) := by
  unfold leftVolFn
  exact ((continuous_const.max ((continuous_const.min continuous_id).sub continuous_const)).mul
    continuous_const)

lemma disjoint_sep {A B : OpenBox h} (hdisj : Disjoint A.toSet B.toSet) :
    ∃ j : Fin h, A.hi j ≤ B.lo j ∨ B.hi j ≤ A.lo j := by
  by_contra hall
  push Not at hall
  let x : Fin h → ℝ := fun i => (max (A.lo i) (B.lo i) + min (A.hi i) (B.hi i)) / 2
  have hlt : ∀ i, max (A.lo i) (B.lo i) < min (A.hi i) (B.hi i) := fun i =>
    max_lt (lt_min (A.lt i) (hall i).2) (lt_min (hall i).1 (B.lt i))
  have hxA : x ∈ A.toSet := fun i _ => by
    have := hlt i
    dsimp only [x]
    constructor
    · linarith [le_max_left (A.lo i) (B.lo i)]
    · linarith [min_le_left (A.hi i) (B.hi i)]
  have hxB : x ∈ B.toSet := fun i _ => by
    have := hlt i
    dsimp only [x]
    constructor
    · linarith [le_max_right (A.lo i) (B.lo i)]
    · linarith [min_le_right (A.hi i) (B.hi i)]
  exact Set.disjoint_left.mp hdisj hxA hxB

end OpenBox

def boxUnion {h : ℕ} (S : List (OpenBox h)) : Set (Fin h → ℝ) :=
  ⋃ B ∈ S, B.toSet

def boxVolSum {h : ℕ} (S : List (OpenBox h)) : ℝ :=
  (S.map OpenBox.vol).sum

noncomputable def cutLeftList {h : ℕ} (S : List (OpenBox h)) (j : Fin h) (c : ℝ) : List (OpenBox h) :=
  S.filterMap fun B => B.cutLeft j c

noncomputable def cutRightList {h : ℕ} (S : List (OpenBox h)) (j : Fin h) (c : ℝ) : List (OpenBox h) :=
  S.filterMap fun B => B.cutRight j c

lemma isOpen_boxUnion {h : ℕ} (S : List (OpenBox h)) : IsOpen (boxUnion S) :=
  isOpen_biUnion fun B _ => B.isOpen_toSet

lemma boxVolSum_nonneg {h : ℕ} (S : List (OpenBox h)) : 0 ≤ boxVolSum S := by
  unfold boxVolSum
  exact List.sum_nonneg fun x hx => by
    rcases List.mem_map.mp hx with ⟨B, _, rfl⟩
    exact B.vol_nonneg

lemma boxVolSum_pos {h : ℕ} {S : List (OpenBox h)} (hS : S ≠ []) : 0 < boxVolSum S := by
  cases S with
  | nil => contradiction
  | cons B rest =>
    have hrest := boxVolSum_nonneg rest
    simp only [boxVolSum, List.map_cons, List.sum_cons] at hrest ⊢
    linarith [B.vol_pos]

lemma boxVolSum_cutLeft_eq {h : ℕ} (S : List (OpenBox h)) (j : Fin h) (c : ℝ) :
    boxVolSum (cutLeftList S j c) = (S.map fun B => B.leftVolFn j c).sum := by
  induction S with
  | nil => simp [boxVolSum, cutLeftList]
  | cons B rest ih =>
    simp only [boxVolSum, cutLeftList, List.filterMap_cons, List.map_cons, List.sum_cons] at ih ⊢
    have hB := B.leftVolFn_eq_opt j c
    cases hopt : B.cutLeft j c with
    | none =>
      rw [hopt] at hB
      simp only [← hB, zero_add]
      exact ih
    | some B' =>
      rw [hopt] at hB
      simp only [List.map_cons, List.sum_cons, ← hB]
      rw [ih]

lemma boxVolSum_cutRight_eq {h : ℕ} (S : List (OpenBox h)) (j : Fin h) (c : ℝ) :
    boxVolSum (cutRightList S j c) = (S.map fun B => B.rightVolFn j c).sum := by
  induction S with
  | nil => simp [boxVolSum, cutRightList]
  | cons B rest ih =>
    simp only [boxVolSum, cutRightList, List.filterMap_cons, List.map_cons, List.sum_cons] at ih ⊢
    have hB := B.rightVolFn_eq_opt j c
    cases hopt : B.cutRight j c with
    | none =>
      rw [hopt] at hB
      simp only [← hB, zero_add]
      exact ih
    | some B' =>
      rw [hopt] at hB
      simp only [List.map_cons, List.sum_cons, ← hB]
      rw [ih]

lemma boxVolSum_cut_add {h : ℕ} (S : List (OpenBox h)) (j : Fin h) (c : ℝ) :
    boxVolSum (cutLeftList S j c) + boxVolSum (cutRightList S j c) = boxVolSum S := by
  rw [boxVolSum_cutLeft_eq, boxVolSum_cutRight_eq]
  induction S with
  | nil => simp [boxVolSum]
  | cons B rest ih =>
    simp only [boxVolSum, List.map_cons, List.sum_cons] at ih ⊢
    linarith [B.leftVolFn_add_rightVolFn j c]

lemma cutLeftList_length_le {h : ℕ} (S : List (OpenBox h)) (j : Fin h) (c : ℝ) :
    (cutLeftList S j c).length ≤ S.length := by
  induction S with
  | nil => simp [cutLeftList]
  | cons B rest ih =>
    simp only [cutLeftList, List.filterMap_cons, List.length_cons] at ih ⊢
    cases B.cutLeft j c <;> simp <;> omega

lemma cutRightList_length_le {h : ℕ} (S : List (OpenBox h)) (j : Fin h) (c : ℝ) :
    (cutRightList S j c).length ≤ S.length := by
  induction S with
  | nil => simp [cutRightList]
  | cons B rest ih =>
    simp only [cutRightList, List.filterMap_cons, List.length_cons] at ih ⊢
    cases B.cutRight j c <;> simp <;> omega

lemma cutLeftList_length_lt {h : ℕ} {S : List (OpenBox h)} {B : OpenBox h} {j : Fin h} {c : ℝ}
    (hB : B ∈ S) (hc : c ≤ B.lo j) : (cutLeftList S j c).length < S.length := by
  induction S with
  | nil => cases hB
  | cons X rest ih =>
    simp only [cutLeftList, List.filterMap_cons, List.length_cons]
    rcases List.mem_cons.mp hB with rfl | hmem
    · have hnone : OpenBox.cutLeft B j c = none := by
        classical
        simp [OpenBox.cutLeft, not_lt.mpr hc]
      rw [hnone]
      dsimp only
      have hle : (List.filterMap (fun B => B.cutLeft j c) rest).length ≤ rest.length :=
        cutLeftList_length_le rest j c
      omega
    · have hlt : (List.filterMap (fun B => B.cutLeft j c) rest).length < rest.length := ih hmem
      cases OpenBox.cutLeft X j c
      · dsimp only; omega
      · dsimp only; simp only [List.length_cons]; omega

lemma cutRightList_length_lt {h : ℕ} {S : List (OpenBox h)} {B : OpenBox h} {j : Fin h} {c : ℝ}
    (hB : B ∈ S) (hc : B.hi j ≤ c) : (cutRightList S j c).length < S.length := by
  induction S with
  | nil => cases hB
  | cons X rest ih =>
    simp only [cutRightList, List.filterMap_cons, List.length_cons]
    rcases List.mem_cons.mp hB with rfl | hmem
    · have hnone : OpenBox.cutRight B j c = none := by
        classical
        simp [OpenBox.cutRight, not_lt.mpr hc]
      rw [hnone]
      dsimp only
      have hle : (List.filterMap (fun B => B.cutRight j c) rest).length ≤ rest.length :=
        cutRightList_length_le rest j c
      omega
    · have hlt : (List.filterMap (fun B => B.cutRight j c) rest).length < rest.length := ih hmem
      cases OpenBox.cutRight X j c
      · dsimp only; omega
      · dsimp only; simp only [List.length_cons]; omega

lemma cutLeftList_pairwise {h : ℕ} {S : List (OpenBox h)} (hP : S.Pairwise (fun A B => Disjoint A.toSet B.toSet))
    (j : Fin h) (c : ℝ) :
    (cutLeftList S j c).Pairwise (fun A B => Disjoint A.toSet B.toSet) := by
  induction S with
  | nil => simp [cutLeftList]
  | cons X rest ih =>
    rw [List.pairwise_cons] at hP
    simp only [cutLeftList, List.filterMap_cons]
    cases hopt : OpenBox.cutLeft X j c with
    | none => exact ih hP.2
    | some X' =>
      rw [List.pairwise_cons]
      refine ⟨fun Y' hY' => ?_, ih hP.2⟩
      rcases List.mem_filterMap.mp hY' with ⟨Y, hY, hYopt⟩
      exact (hP.1 Y hY).mono (OpenBox.cutLeft_subset hopt).1 (OpenBox.cutLeft_subset hYopt).1

lemma cutRightList_pairwise {h : ℕ} {S : List (OpenBox h)} (hP : S.Pairwise (fun A B => Disjoint A.toSet B.toSet))
    (j : Fin h) (c : ℝ) :
    (cutRightList S j c).Pairwise (fun A B => Disjoint A.toSet B.toSet) := by
  induction S with
  | nil => simp [cutRightList]
  | cons X rest ih =>
    rw [List.pairwise_cons] at hP
    simp only [cutRightList, List.filterMap_cons]
    cases hopt : OpenBox.cutRight X j c with
    | none => exact ih hP.2
    | some X' =>
      rw [List.pairwise_cons]
      refine ⟨fun Y' hY' => ?_, ih hP.2⟩
      rcases List.mem_filterMap.mp hY' with ⟨Y, hY, hYopt⟩
      exact (hP.1 Y hY).mono (OpenBox.cutRight_subset hopt).1 (OpenBox.cutRight_subset hYopt).1

lemma boxUnion_cutLeft_subset {h : ℕ} (S : List (OpenBox h)) (j : Fin h) (c : ℝ) :
    boxUnion (cutLeftList S j c) ⊆ boxUnion S ∧ ∀ x ∈ boxUnion (cutLeftList S j c), x j < c := by
  constructor
  · intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨B', hB', hxB'⟩
    rcases List.mem_filterMap.mp hB' with ⟨B, hB, hopt⟩
    exact Set.mem_iUnion₂.mpr ⟨B, hB, (OpenBox.cutLeft_subset hopt).1 hxB'⟩
  · intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨B', hB', hxB'⟩
    rcases List.mem_filterMap.mp hB' with ⟨B, _, hopt⟩
    exact (OpenBox.cutLeft_subset hopt).2 x hxB'

lemma boxUnion_cutRight_subset {h : ℕ} (S : List (OpenBox h)) (j : Fin h) (c : ℝ) :
    boxUnion (cutRightList S j c) ⊆ boxUnion S ∧ ∀ x ∈ boxUnion (cutRightList S j c), c < x j := by
  constructor
  · intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨B', hB', hxB'⟩
    rcases List.mem_filterMap.mp hB' with ⟨B, hB, hopt⟩
    exact Set.mem_iUnion₂.mpr ⟨B, hB, (OpenBox.cutRight_subset hopt).1 hxB'⟩
  · intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨B', hB', hxB'⟩
    rcases List.mem_filterMap.mp hB' with ⟨B, _, hopt⟩
    exact (OpenBox.cutRight_subset hopt).2 x hxB'

lemma exists_cut_vol {h : ℕ} (S : List (OpenBox h)) (j : Fin h) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ boxVolSum S) :
    ∃ c : ℝ, boxVolSum (cutLeftList S j c) = v := by
  let f : ℝ → ℝ := fun c => (S.map fun B => B.leftVolFn j c).sum
  have hf_eq : ∀ c, boxVolSum (cutLeftList S j c) = f c := fun c => boxVolSum_cutLeft_eq S j c
  have hf_cont : Continuous f := by
    have : ∀ L : List (OpenBox h), Continuous (fun c => (L.map fun B => B.leftVolFn j c).sum) := by
      intro L
      induction L with
      | nil => simp [continuous_const]
      | cons B rest ih =>
        simp only [List.map_cons, List.sum_cons]
        exact (B.continuous_leftVolFn j).add ih
    exact this S
  let lo0 : ℝ := S.foldl (fun acc B => min acc (B.lo j)) 0
  let hi0 : ℝ := S.foldl (fun acc B => max acc (B.hi j)) 0
  have hlo : ∀ B ∈ S, lo0 ≤ B.lo j := by
    have hfold : ∀ (L : List (OpenBox h)) (init : ℝ),
        (L.foldl (fun acc B => min acc (B.lo j)) init) ≤ init ∧
        ∀ B ∈ L, (L.foldl (fun acc B => min acc (B.lo j)) init) ≤ B.lo j := by
      intro L
      induction L with
      | nil => intro init; exact ⟨le_rfl, fun _ h => by cases h⟩
      | cons X rest ih =>
        intro init
        rcases ih (min init (X.lo j)) with ⟨h1, h2⟩
        refine ⟨le_trans h1 (min_le_left _ _), fun B hB => ?_⟩
        rcases List.mem_cons.mp hB with rfl | hmem
        · exact le_trans h1 (min_le_right _ _)
        · exact h2 B hmem
    exact (hfold S 0).2
  have hhi : ∀ B ∈ S, B.hi j ≤ hi0 := by
    have hfold : ∀ (L : List (OpenBox h)) (init : ℝ),
        init ≤ (L.foldl (fun acc B => max acc (B.hi j)) init) ∧
        ∀ B ∈ L, B.hi j ≤ (L.foldl (fun acc B => max acc (B.hi j)) init) := by
      intro L
      induction L with
      | nil => intro init; exact ⟨le_rfl, fun _ h => by cases h⟩
      | cons X rest ih =>
        intro init
        rcases ih (max init (X.hi j)) with ⟨h1, h2⟩
        refine ⟨le_trans (le_max_left _ _) h1, fun B hB => ?_⟩
        rcases List.mem_cons.mp hB with rfl | hmem
        · exact le_trans (le_max_right _ _) h1
        · exact h2 B hmem
    exact (hfold S 0).2
  have hlo_le_hi : lo0 ≤ hi0 := by
    cases S with
    | nil => simp [lo0, hi0]
    | cons B _ => exact le_trans (hlo B (List.mem_cons_self ..)) (le_trans (B.lt j).le (hhi B (List.mem_cons_self ..)))
  have hflo : f lo0 = 0 := by
    have : ∀ L : List (OpenBox h), (∀ B ∈ L, lo0 ≤ B.lo j) → (L.map fun B => B.leftVolFn j lo0).sum = 0 := by
      intro L hL
      induction L with
      | nil => simp
      | cons B rest ih =>
        simp only [List.map_cons, List.sum_cons]
        have hB : B.leftVolFn j lo0 = 0 := by
          unfold OpenBox.leftVolFn
          have h1 := hL B (List.mem_cons_self ..)
          rw [min_eq_right (le_trans h1 (B.lt j).le), max_eq_left (by linarith), zero_mul]
        rw [hB, zero_add]
        exact ih fun X hX => hL X (List.mem_cons_of_mem _ hX)
    exact this S hlo
  have hfhi : f hi0 = boxVolSum S := by
    have : ∀ L : List (OpenBox h), (∀ B ∈ L, B.hi j ≤ hi0) → (L.map fun B => B.leftVolFn j hi0).sum = boxVolSum L := by
      intro L hL
      induction L with
      | nil => simp [boxVolSum]
      | cons B rest ih =>
        simp only [boxVolSum, List.map_cons, List.sum_cons] at ih ⊢
        have hB : B.leftVolFn j hi0 = B.vol := by
          rw [OpenBox.leftVolFn, OpenBox.vol_eq_mul_restVol B j]
          have h1 := hL B (List.mem_cons_self ..)
          rw [min_eq_left h1, max_eq_right (sub_nonneg.mpr (B.lt j).le)]
        rw [hB, ih fun X hX => hL X (List.mem_cons_of_mem _ hX)]
    exact this S hhi
  have hv_mem : v ∈ Set.Icc (f lo0) (f hi0) := by rw [hflo, hfhi]; exact ⟨hv0, hv1⟩
  obtain ⟨c, _, hfc⟩ := intermediate_value_Icc hlo_le_hi hf_cont.continuousOn hv_mem
  exact ⟨c, (hf_eq c).trans hfc⟩

lemma box_brunn_minkowski_aux {h : ℕ} :
    ∀ N : ℕ, ∀ (A B : List (OpenBox h)),
      A.length + B.length ≤ N →
      A.Pairwise (fun P Q => Disjoint P.toSet Q.toSet) →
      B.Pairwise (fun P Q => Disjoint P.toSet Q.toSet) →
      ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt (boxVolSum A * boxVolSum B)) ≤
        volume (boxUnion A + boxUnion B) := by
  intro N
  induction N with
  | zero =>
    intro A B hlen _ _
    have hA : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hA, boxVolSum]
  | succ N ih =>
    intro A B hlen hPA hPB
    by_cases hA0 : A = []
    · simp [hA0, boxVolSum]
    by_cases hB0 : B = []
    · simp [hB0, boxVolSum]
    by_cases hA1 : A.length = 1
    · by_cases hB1 : B.length = 1
      · rcases List.length_eq_one_iff.mp hA1 with ⟨P, rfl⟩
        rcases List.length_eq_one_iff.mp hB1 with ⟨Q, rfl⟩
        have hsub : (P.add Q).toSet ⊆ boxUnion [P] + boxUnion [Q] := by
          simpa [boxUnion] using P.add_toSet_subset Q
        calc
          ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt (boxVolSum [P] * boxVolSum [Q]))
              = ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt (P.vol * Q.vol)) := by simp [boxVolSum]
          _ ≤ ENNReal.ofReal (P.add Q).vol := ENNReal.ofReal_le_ofReal (P.vol_add_ge Q)
          _ = volume (P.add Q).toSet := (P.add Q).volume_toSet.symm
          _ ≤ volume (boxUnion [P] + boxUnion [Q]) := measure_mono hsub
      · have hcomm : boxUnion A + boxUnion B = boxUnion B + boxUnion A := add_comm _ _
        have hmul : boxVolSum A * boxVolSum B = boxVolSum B * boxVolSum A := mul_comm _ _
        rw [hcomm, hmul]
        obtain ⟨P, Q, rest, rfl⟩ : ∃ P Q rest, B = P :: Q :: rest := by
          cases B with
          | nil => contradiction
          | cons P tail =>
            cases tail with
            | nil => simp at hB1
            | cons Q rest => exact ⟨P, Q, rest, rfl⟩
        rw [List.pairwise_cons] at hPB
        have hPQ : Disjoint P.toSet Q.toSet := hPB.1 Q (List.mem_cons_self ..)
        obtain ⟨j, hsep⟩ := OpenBox.disjoint_sep hPQ
        have hPB' : (P :: Q :: rest).Pairwise (fun X Y => Disjoint X.toSet Y.toSet) :=
          List.pairwise_cons.mpr hPB
        obtain ⟨c, hL_lt, hR_lt⟩ :
            ∃ c : ℝ, (cutLeftList (P :: Q :: rest) j c).length < (P :: Q :: rest).length ∧
              (cutRightList (P :: Q :: rest) j c).length < (P :: Q :: rest).length := by
          rcases hsep with h1 | h1
          · exact ⟨P.hi j,
              cutLeftList_length_lt (List.mem_cons_of_mem _ (List.mem_cons_self ..)) h1,
              cutRightList_length_lt (List.mem_cons_self ..) le_rfl⟩
          · exact ⟨Q.hi j,
              cutLeftList_length_lt (List.mem_cons_self ..) h1,
              cutRightList_length_lt (List.mem_cons_of_mem _ (List.mem_cons_self ..)) le_rfl⟩
        let BL := cutLeftList (P :: Q :: rest) j c
        let BR := cutRightList (P :: Q :: rest) j c
        have hvB : 0 < boxVolSum (P :: Q :: rest) := boxVolSum_pos (by simp)
        let lam := boxVolSum BL / boxVolSum (P :: Q :: rest)
        have hlam0 : 0 ≤ lam := div_nonneg (boxVolSum_nonneg BL) hvB.le
        have hlam1 : lam ≤ 1 := (div_le_one hvB).mpr (by
          linarith [boxVolSum_cut_add (P :: Q :: rest) j c, boxVolSum_nonneg BR])
        obtain ⟨c', hc'⟩ := exists_cut_vol A j (mul_nonneg hlam0 (boxVolSum_nonneg A))
          (by nlinarith [boxVolSum_nonneg A])
        let AL := cutLeftList A j c'
        let AR := cutRightList A j c'
        have hAL_eq : boxVolSum AL = lam * boxVolSum A := hc'
        have hAR_eq : boxVolSum AR = (1 - lam) * boxVolSum A := by
          linarith [boxVolSum_cut_add A j c']
        have hBL_eq : boxVolSum BL = lam * boxVolSum (P :: Q :: rest) := by
          dsimp [lam]; exact (div_mul_cancel₀ _ hvB.ne').symm
        have hBR_eq : boxVolSum BR = (1 - lam) * boxVolSum (P :: Q :: rest) := by
          linarith [boxVolSum_cut_add (P :: Q :: rest) j c]
        have hBL_len : BL.length < (P :: Q :: rest).length := hL_lt
        have hBR_len : BR.length < (P :: Q :: rest).length := hR_lt
        have hAL_len : AL.length ≤ A.length := cutLeftList_length_le A j c'
        have hAR_len : AR.length ≤ A.length := cutRightList_length_le A j c'
        have hL_ind := ih BL AL (by omega)
          (cutLeftList_pairwise hPB' j c) (cutLeftList_pairwise hPA j c')
        have hR_ind := ih BR AR (by omega)
          (cutRightList_pairwise hPB' j c) (cutRightList_pairwise hPA j c')
        have hsubL : boxUnion BL + boxUnion AL ⊆ boxUnion (P :: Q :: rest) + boxUnion A :=
          Set.add_subset_add (boxUnion_cutLeft_subset _ j c).1 (boxUnion_cutLeft_subset _ j c').1
        have hsubR : boxUnion BR + boxUnion AR ⊆ boxUnion (P :: Q :: rest) + boxUnion A :=
          Set.add_subset_add (boxUnion_cutRight_subset _ j c).1 (boxUnion_cutRight_subset _ j c').1
        have hdisj : Disjoint (boxUnion BL + boxUnion AL) (boxUnion BR + boxUnion AR) := by
          rw [Set.disjoint_left]
          rintro x ⟨b1, hb1, a1, ha1, rfl⟩ ⟨b2, hb2, a2, ha2, heq⟩
          have h1 := (boxUnion_cutLeft_subset _ j c).2 b1 hb1
          have h2 := (boxUnion_cutLeft_subset _ j c').2 a1 ha1
          have h3 := (boxUnion_cutRight_subset _ j c).2 b2 hb2
          have h4 := (boxUnion_cutRight_subset _ j c').2 a2 ha2
          have hj : (b1 + a1) j = (b2 + a2) j := congrArg (fun f => f j) heq.symm
          simp only [Pi.add_apply] at hj
          linarith
        have hmR : MeasurableSet (boxUnion BR + boxUnion AR) :=
          ((isOpen_boxUnion BR).add_right).measurableSet
        have hvol_add : volume (boxUnion BL + boxUnion AL) + volume (boxUnion BR + boxUnion AR) ≤
            volume (boxUnion (P :: Q :: rest) + boxUnion A) := by
          rw [← measure_union hdisj hmR]
          exact measure_mono (Set.union_subset hsubL hsubR)
        have hsqL : Real.sqrt (boxVolSum BL * boxVolSum AL) =
            lam * Real.sqrt (boxVolSum (P :: Q :: rest) * boxVolSum A) := by
          rw [hBL_eq, hAL_eq]
          have : lam * boxVolSum (P :: Q :: rest) * (lam * boxVolSum A) =
              lam ^ 2 * (boxVolSum (P :: Q :: rest) * boxVolSum A) := by ring
          rw [this, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hlam0]
        have hsqR : Real.sqrt (boxVolSum BR * boxVolSum AR) =
            (1 - lam) * Real.sqrt (boxVolSum (P :: Q :: rest) * boxVolSum A) := by
          rw [hBR_eq, hAR_eq]
          have : (1 - lam) * boxVolSum (P :: Q :: rest) * ((1 - lam) * boxVolSum A) =
              (1 - lam) ^ 2 * (boxVolSum (P :: Q :: rest) * boxVolSum A) := by ring
          rw [this, Real.sqrt_mul (sq_nonneg (1 - lam)), Real.sqrt_sq (by linarith)]
        have hsum_real :
            (2 : ℝ) ^ h * Real.sqrt (boxVolSum BL * boxVolSum AL) +
              (2 : ℝ) ^ h * Real.sqrt (boxVolSum BR * boxVolSum AR) =
              (2 : ℝ) ^ h * Real.sqrt (boxVolSum (P :: Q :: rest) * boxVolSum A) := by
          rw [hsqL, hsqR]; ring
        calc
          ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt (boxVolSum (P :: Q :: rest) * boxVolSum A))
              = ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt (boxVolSum BL * boxVolSum AL)) +
                ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt (boxVolSum BR * boxVolSum AR)) := by
                rw [← ENNReal.ofReal_add (by positivity) (by positivity), hsum_real]
          _ ≤ volume (boxUnion BL + boxUnion AL) + volume (boxUnion BR + boxUnion AR) :=
                add_le_add hL_ind hR_ind
          _ ≤ volume (boxUnion (P :: Q :: rest) + boxUnion A) := hvol_add
    · obtain ⟨P, Q, rest, rfl⟩ : ∃ P Q rest, A = P :: Q :: rest := by
        cases A with
        | nil => contradiction
        | cons P tail =>
          cases tail with
          | nil => simp at hA1
          | cons Q rest => exact ⟨P, Q, rest, rfl⟩
      rw [List.pairwise_cons] at hPA
      have hPQ : Disjoint P.toSet Q.toSet := hPA.1 Q (List.mem_cons_self ..)
      obtain ⟨j, hsep⟩ := OpenBox.disjoint_sep hPQ
      have hPA' : (P :: Q :: rest).Pairwise (fun X Y => Disjoint X.toSet Y.toSet) :=
        List.pairwise_cons.mpr hPA
      obtain ⟨c, hL_lt, hR_lt⟩ :
          ∃ c : ℝ, (cutLeftList (P :: Q :: rest) j c).length < (P :: Q :: rest).length ∧
            (cutRightList (P :: Q :: rest) j c).length < (P :: Q :: rest).length := by
        rcases hsep with h1 | h1
        · exact ⟨P.hi j,
            cutLeftList_length_lt (List.mem_cons_of_mem _ (List.mem_cons_self ..)) h1,
            cutRightList_length_lt (List.mem_cons_self ..) le_rfl⟩
        · exact ⟨Q.hi j,
            cutLeftList_length_lt (List.mem_cons_self ..) h1,
            cutRightList_length_lt (List.mem_cons_of_mem _ (List.mem_cons_self ..)) le_rfl⟩
      let AL := cutLeftList (P :: Q :: rest) j c
      let AR := cutRightList (P :: Q :: rest) j c
      have hvA : 0 < boxVolSum (P :: Q :: rest) := boxVolSum_pos (by simp)
      let lam := boxVolSum AL / boxVolSum (P :: Q :: rest)
      have hlam0 : 0 ≤ lam := div_nonneg (boxVolSum_nonneg AL) hvA.le
      have hlam1 : lam ≤ 1 := (div_le_one hvA).mpr (by
        linarith [boxVolSum_cut_add (P :: Q :: rest) j c, boxVolSum_nonneg AR])
      obtain ⟨c', hc'⟩ := exists_cut_vol B j (mul_nonneg hlam0 (boxVolSum_nonneg B))
        (by nlinarith [boxVolSum_nonneg B])
      let BL := cutLeftList B j c'
      let BR := cutRightList B j c'
      have hBL_eq : boxVolSum BL = lam * boxVolSum B := hc'
      have hBR_eq : boxVolSum BR = (1 - lam) * boxVolSum B := by
        linarith [boxVolSum_cut_add B j c']
      have hAL_eq : boxVolSum AL = lam * boxVolSum (P :: Q :: rest) := by
        dsimp [lam]; exact (div_mul_cancel₀ _ hvA.ne').symm
      have hAR_eq : boxVolSum AR = (1 - lam) * boxVolSum (P :: Q :: rest) := by
        linarith [boxVolSum_cut_add (P :: Q :: rest) j c]
      have hAL_len : AL.length < (P :: Q :: rest).length := hL_lt
      have hAR_len : AR.length < (P :: Q :: rest).length := hR_lt
      have hBL_len : BL.length ≤ B.length := cutLeftList_length_le B j c'
      have hBR_len : BR.length ≤ B.length := cutRightList_length_le B j c'
      have hL_ind := ih AL BL (by omega)
        (cutLeftList_pairwise hPA' j c) (cutLeftList_pairwise hPB j c')
      have hR_ind := ih AR BR (by omega)
        (cutRightList_pairwise hPA' j c) (cutRightList_pairwise hPB j c')
      have hsubL : boxUnion AL + boxUnion BL ⊆ boxUnion (P :: Q :: rest) + boxUnion B :=
        Set.add_subset_add (boxUnion_cutLeft_subset _ j c).1 (boxUnion_cutLeft_subset _ j c').1
      have hsubR : boxUnion AR + boxUnion BR ⊆ boxUnion (P :: Q :: rest) + boxUnion B :=
        Set.add_subset_add (boxUnion_cutRight_subset _ j c).1 (boxUnion_cutRight_subset _ j c').1
      have hdisj : Disjoint (boxUnion AL + boxUnion BL) (boxUnion AR + boxUnion BR) := by
        rw [Set.disjoint_left]
        rintro x ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, heq⟩
        have h1 := (boxUnion_cutLeft_subset _ j c).2 a1 ha1
        have h2 := (boxUnion_cutLeft_subset _ j c').2 b1 hb1
        have h3 := (boxUnion_cutRight_subset _ j c).2 a2 ha2
        have h4 := (boxUnion_cutRight_subset _ j c').2 b2 hb2
        have hj : (a1 + b1) j = (a2 + b2) j := congrArg (fun f => f j) heq.symm
        simp only [Pi.add_apply] at hj
        linarith
      have hmR : MeasurableSet (boxUnion AR + boxUnion BR) :=
        ((isOpen_boxUnion AR).add_right).measurableSet
      have hvol_add : volume (boxUnion AL + boxUnion BL) + volume (boxUnion AR + boxUnion BR) ≤
          volume (boxUnion (P :: Q :: rest) + boxUnion B) := by
        rw [← measure_union hdisj hmR]
        exact measure_mono (Set.union_subset hsubL hsubR)
      have hsqL : Real.sqrt (boxVolSum AL * boxVolSum BL) =
          lam * Real.sqrt (boxVolSum (P :: Q :: rest) * boxVolSum B) := by
        rw [hAL_eq, hBL_eq]
        have : lam * boxVolSum (P :: Q :: rest) * (lam * boxVolSum B) =
            lam ^ 2 * (boxVolSum (P :: Q :: rest) * boxVolSum B) := by ring
        rw [this, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hlam0]
      have hsqR : Real.sqrt (boxVolSum AR * boxVolSum BR) =
          (1 - lam) * Real.sqrt (boxVolSum (P :: Q :: rest) * boxVolSum B) := by
        rw [hAR_eq, hBR_eq]
        have : (1 - lam) * boxVolSum (P :: Q :: rest) * ((1 - lam) * boxVolSum B) =
            (1 - lam) ^ 2 * (boxVolSum (P :: Q :: rest) * boxVolSum B) := by ring
        rw [this, Real.sqrt_mul (sq_nonneg (1 - lam)), Real.sqrt_sq (by linarith)]
      have hsum_real :
          (2 : ℝ) ^ h * Real.sqrt (boxVolSum AL * boxVolSum BL) +
            (2 : ℝ) ^ h * Real.sqrt (boxVolSum AR * boxVolSum BR) =
            (2 : ℝ) ^ h * Real.sqrt (boxVolSum (P :: Q :: rest) * boxVolSum B) := by
        rw [hsqL, hsqR]; ring
      calc
        ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt (boxVolSum (P :: Q :: rest) * boxVolSum B))
            = ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt (boxVolSum AL * boxVolSum BL)) +
              ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt (boxVolSum AR * boxVolSum BR)) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity), hsum_real]
        _ ≤ volume (boxUnion AL + boxUnion BL) + volume (boxUnion AR + boxUnion BR) :=
              add_le_add hL_ind hR_ind
        _ ≤ volume (boxUnion (P :: Q :: rest) + boxUnion B) := hvol_add

lemma exists_grid_cover {h : ℕ} {K : Set (Fin h → ℝ)} (hK : IsCompact K) {s : ℝ} (hs : 0 < s) :
    ∃ L : List (OpenBox h),
      L.Pairwise (fun P Q => Disjoint P.toSet Q.toSet) ∧
      volume K ≤ ENNReal.ofReal (boxVolSum L) ∧
      ∀ x ∈ boxUnion L, ∃ y ∈ K, dist x y ≤ s := by
  classical
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Fin h → ℝ)
  set M : ℤ := ⌈max R 0 / s⌉ + 1
  let boxZ : (Fin h → ℤ) → OpenBox h := fun z =>
    ⟨fun i => s * (z i : ℝ), fun i => s * ((z i : ℝ) + 1), fun i => by nlinarith⟩
  let closedZ : (Fin h → ℤ) → Set (Fin h → ℝ) := fun z =>
    Set.univ.pi fun i => Set.Icc (s * (z i : ℝ)) (s * ((z i : ℝ) + 1))
  let gridFinset : Finset (Fin h → ℤ) :=
    Fintype.piFinset fun _ : Fin h => Finset.Icc (-M) M
  let F : Finset (Fin h → ℤ) := gridFinset.filter fun z => (K ∩ closedZ z).Nonempty
  let L : List (OpenBox h) := F.toList.map boxZ
  refine ⟨L, ?_, ?_, ?_⟩
  · have hnd : F.toList.Nodup := Finset.nodup_toList F
    rw [List.pairwise_map]
    refine hnd.imp_of_mem fun {z₁ z₂} _ _ hne => ?_
    have hne_i : ∃ i : Fin h, z₁ i ≠ z₂ i := Function.ne_iff.mp hne
    rcases hne_i with ⟨i, hi⟩
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have h1 := hx₁ i (Set.mem_univ i)
    have h2 := hx₂ i (Set.mem_univ i)
    simp only [boxZ, Set.mem_Ioo] at h1 h2
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have hle : (z₁ i : ℝ) + 1 ≤ (z₂ i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt
      nlinarith
    · have hle : (z₂ i : ℝ) + 1 ≤ (z₁ i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hgt
      nlinarith
  · have hK_sub : K ⊆ ⋃ z ∈ F, closedZ z := by
      intro x hx
      let z : Fin h → ℤ := fun i => ⌊x i / s⌋
      have hx_closed : x ∈ closedZ z := fun i _ => by
        simp only [Set.mem_Icc, z]
        constructor
        · have h1 := (le_div_iff₀ hs).mp (Int.floor_le (x i / s))
          linarith
        · have h2 := (div_le_iff₀ hs).mp (Int.lt_floor_add_one (x i / s)).le
          linarith
      have hz_grid : z ∈ gridFinset := by
        rw [Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_Icc]
        have hxb : dist x 0 ≤ R := Metric.mem_closedBall.mp (hR hx)
        have hxi : |x i| ≤ R := by
          have := dist_le_pi_dist x 0 i
          simp only [Pi.zero_apply, Real.dist_eq, sub_zero] at this
          exact le_trans this hxb
        have hxi' : |x i| ≤ max R 0 := le_trans hxi (le_max_left _ _)
        have hle_R : x i / s ≤ max R 0 / s :=
          div_le_div_of_nonneg_right (le_trans (le_abs_self _) hxi') hs.le
        have hge_R : -(max R 0 / s) ≤ x i / s := by
          rw [← neg_div]
          exact div_le_div_of_nonneg_right (by linarith [neg_abs_le (x i)]) hs.le
        have hceil := Int.le_ceil (max R 0 / s)
        have h1 : z i ≤ M := by
          have : (z i : ℝ) ≤ (M : ℝ) := by
            have := Int.floor_le (x i / s)
            push_cast [M]
            linarith
          exact_mod_cast this
        have h2 : -M ≤ z i := by
          have : ((-M : ℤ) : ℝ) < (z i : ℝ) + 1 := by
            have := Int.lt_floor_add_one (x i / s)
            push_cast [M]
            linarith
          have : -M < z i + 1 := by exact_mod_cast this
          omega
        exact ⟨h2, h1⟩
      have hzF : z ∈ F := Finset.mem_filter.mpr ⟨hz_grid, ⟨x, hx, hx_closed⟩⟩
      exact Set.mem_biUnion hzF hx_closed
    have hvol_closed : ∀ z : Fin h → ℤ, volume (closedZ z) = ENNReal.ofReal (boxZ z).vol := by
      intro z
      rw [← (boxZ z).volume_toSet]
      dsimp only [closedZ, OpenBox.toSet]
      rw [MeasureTheory.volume_pi, Measure.pi_pi, Measure.pi_pi]
      simp [boxZ, Real.volume_Icc, Real.volume_Ioo]
    have hsum_eq : (∑ z ∈ F, (boxZ z).vol) = boxVolSum L := by
      rw [boxVolSum, show L = F.toList.map boxZ from rfl, List.map_map]
      change (F.val.map fun z => (boxZ z).vol).sum = (F.toList.map fun z => (boxZ z).vol).sum
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
    calc
      volume K ≤ volume (⋃ z ∈ F, closedZ z) := measure_mono hK_sub
      _ ≤ ∑ z ∈ F, volume (closedZ z) := measure_biUnion_finset_le F closedZ
      _ = ∑ z ∈ F, ENNReal.ofReal (boxZ z).vol := Finset.sum_congr rfl fun z _ => hvol_closed z
      _ = ENNReal.ofReal (∑ z ∈ F, (boxZ z).vol) :=
            (ENNReal.ofReal_sum_of_nonneg fun z _ => (boxZ z).vol_nonneg).symm
      _ = ENNReal.ofReal (boxVolSum L) := by rw [hsum_eq]
  · intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨B, hB, hxB⟩
    rcases List.mem_map.mp hB with ⟨z, hzL, rfl⟩
    have hzF : z ∈ F := Finset.mem_toList.mp hzL
    rcases (Finset.mem_filter.mp hzF).2 with ⟨y, hyK, hyZ⟩
    refine ⟨y, hyK, ?_⟩
    rw [dist_pi_le_iff hs.le]
    intro i
    have h1 := hxB i (Set.mem_univ i)
    have h2 := hyZ i (Set.mem_univ i)
    simp only [boxZ, Set.mem_Ioo] at h1
    simp only [closedZ, Set.mem_Icc] at h2
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith

lemma compact_brunn_minkowski_pi {h : ℕ} {K₁ K₂ : Set (Fin h → ℝ)}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt ((volume K₁).toReal * (volume K₂).toReal)) ≤
      volume (K₁ + K₂) := by
  have hK12 : IsCompact (K₁ + K₂) := hK₁.add hK₂
  let T : ℕ → Set (Fin h → ℝ) := fun m =>
    Metric.cthickening (2 / ((m : ℝ) + 1)) (K₁ + K₂)
  have hT_meas : ∀ m, NullMeasurableSet (T m) volume := fun m =>
    Metric.isClosed_cthickening.nullMeasurableSet
  have hT_anti : Antitone T := by
    intro m n hmn
    apply Metric.cthickening_mono
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    exact div_le_div_of_nonneg_left (by norm_num) hm hmn'
  have hT_fin : ∃ m, volume (T m) ≠ ∞ :=
    ⟨0, (hK12.cthickening).measure_lt_top.ne⟩
  have hT_inter : (⋂ m, T m) = K₁ + K₂ := by
    ext x
    simp only [Set.mem_iInter, T, Metric.mem_cthickening_iff]
    constructor
    · intro hx
      have hinf : Metric.infEDist x (K₁ + K₂) = 0 := by
        refine le_antisymm ?_ bot_le
        refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
        rw [zero_add]
        have hε_pos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
        obtain ⟨m, hm⟩ := exists_nat_gt (2 / (ε : ℝ))
        have hle : 2 / ((m : ℝ) + 1) ≤ (ε : ℝ) := by
          have hm1 : 2 / (ε : ℝ) < (m : ℝ) + 1 := lt_trans hm (lt_add_one _)
          have hmul : 2 < ((m : ℝ) + 1) * (ε : ℝ) := by
            have := (div_lt_iff₀ hε_pos).mp hm1
            linarith
          exact (div_le_iff₀ (by positivity)).mpr (by linarith)
        exact le_trans (hx m) (le_trans (ENNReal.ofReal_le_ofReal hle) (by simp))
      rw [← hK12.isClosed.closure_eq, Metric.mem_closure_iff_infEDist_zero]
      exact hinf
    · intro hx m
      exact (Metric.mem_cthickening_iff).mp (Metric.self_subset_cthickening (K₁ + K₂) hx)
  have hbound : ∀ m : ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt ((volume K₁).toReal * (volume K₂).toReal)) ≤
        volume (T m) := by
    intro m
    set s : ℝ := 1 / ((m : ℝ) + 1)
    have hs : 0 < s := by positivity
    obtain ⟨L₁, hP₁, hV₁, hD₁⟩ := exists_grid_cover hK₁ hs
    obtain ⟨L₂, hP₂, hV₂, hD₂⟩ := exists_grid_cover hK₂ hs
    have hsub : boxUnion L₁ + boxUnion L₂ ⊆ T m := by
      rintro x ⟨u, hu, v, hv, rfl⟩
      obtain ⟨y₁, hy₁, hd₁⟩ := hD₁ u hu
      obtain ⟨y₂, hy₂, hd₂⟩ := hD₂ v hv
      have hdist : dist (u + v) (y₁ + y₂) ≤ 2 / ((m : ℝ) + 1) := by
        calc
          dist (u + v) (y₁ + y₂) ≤ dist u y₁ + dist v y₂ := dist_add_add_le u v y₁ y₂
          _ ≤ s + s := add_le_add hd₁ hd₂
          _ = 2 / ((m : ℝ) + 1) := by ring
      exact Metric.mem_cthickening_of_dist_le (u + v) (y₁ + y₂) _ _ (Set.add_mem_add hy₁ hy₂) hdist
    have hle1 : (volume K₁).toReal ≤ boxVolSum L₁ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hV₁
      rwa [ENNReal.toReal_ofReal (boxVolSum_nonneg L₁)] at this
    have hle2 : (volume K₂).toReal ≤ boxVolSum L₂ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hV₂
      rwa [ENNReal.toReal_ofReal (boxVolSum_nonneg L₂)] at this
    calc
      ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt ((volume K₁).toReal * (volume K₂).toReal))
          ≤ ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt (boxVolSum L₁ * boxVolSum L₂)) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (mul_le_mul hle1 hle2 ENNReal.toReal_nonneg (boxVolSum_nonneg L₁)))
              (by positivity)
      _ ≤ volume (boxUnion L₁ + boxUnion L₂) :=
            box_brunn_minkowski_aux (L₁.length + L₂.length) L₁ L₂ le_rfl hP₁ hP₂
      _ ≤ volume (T m) := measure_mono hsub
  have htend := MeasureTheory.tendsto_measure_iInter_atTop hT_meas hT_anti hT_fin
  rw [hT_inter] at htend
  exact ge_of_tendsto htend (Filter.Eventually.of_forall hbound)

lemma compact_brunn_minkowski_euclidean {h : ℕ}
    {K₁ K₂ : Set (EuclideanSpace ℝ (Fin h))} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt ((volume K₁).toReal * (volume K₂).toReal)) ≤
      volume (K₁ + K₂) := by
  let e := (MeasurableEquiv.toLp 2 (Fin h → ℝ)).symm
  have hmp : MeasurePreserving e volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin h)
  have hcont : Continuous e := PiLp.continuous_ofLp 2 _
  have himg_vol : ∀ S : Set (EuclideanSpace ℝ (Fin h)), volume (e '' S) = volume S := by
    intro S
    rw [← e.preimage_symm, hmp.symm.measure_preimage_emb e.symm.measurableEmbedding]
  have himg_add : e '' (K₁ + K₂) = e '' K₁ + e '' K₂ := by
    ext z
    constructor
    · rintro ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a + b, Set.add_mem_add ha hb, rfl⟩
  rw [← himg_vol K₁, ← himg_vol K₂, ← himg_vol (K₁ + K₂), himg_add]
  exact compact_brunn_minkowski_pi (hK₁.image hcont) (hK₂.image hcont)

/- ## Part 2: Two-Set Concentration on the Real Unit Sphere -/

abbrev RealSphere (h : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin h)) 1

lemma realSphere_two_set_far {h : ℕ} (hh : 0 < h)
    {A B : Set (RealSphere h)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {d : ℝ} (hd : 1 ≤ d)
    (hAq : ENNReal.ofReal ((d / 2) ^ h) * volume.toSphere (Set.univ : Set (RealSphere h)) <
      volume.toSphere A)
    (hBq : ENNReal.ofReal ((d / 2) ^ h) * volume.toSphere (Set.univ : Set (RealSphere h)) <
      volume.toSphere B) :
    ∃ a ∈ A, ∃ b ∈ B, d < dist a b := by
  let E := EuclideanSpace ℝ (Fin h)
  let V : ℝ≥0∞ := volume (Metric.ball (0 : E) 1)
  haveI : Nonempty (Fin h) := Fin.pos_iff_nonempty.mp hh
  have hV_pos : 0 < V := Metric.measure_ball_pos volume 0 one_pos
  have hV_top : V ≠ ∞ := measure_ball_lt_top.ne
  have hV_real_pos : 0 < V.toReal := ENNReal.toReal_pos hV_pos.ne' hV_top
  obtain ⟨KA, hKAA, hKA, hKAq⟩ := hA.exists_lt_isCompact hAq
  obtain ⟨KB, hKBB, hKB, hKBq⟩ := hB.exists_lt_isCompact hBq
  let OA : Set E := Set.Ioo (0 : ℝ) 1 • ((↑) '' KA)
  let OB : Set E := Set.Ioo (0 : ℝ) 1 • ((↑) '' KB)
  let CA : Set E := Set.Icc (0 : ℝ) 1 • ((↑) '' KA)
  let CB : Set E := Set.Icc (0 : ℝ) 1 • ((↑) '' KB)
  have hCA : IsCompact CA := isCompact_Icc.smul_set (hKA.image continuous_subtype_val)
  have hCB : IsCompact CB := isCompact_Icc.smul_set (hKB.image continuous_subtype_val)
  have htotal : volume.toSphere (Set.univ : Set (RealSphere h)) = (h : ℝ≥0∞) * V := by
    simp [E, V, RealSphere, Measure.toSphere_apply_univ]
  have hOAK : volume.toSphere KA = (h : ℝ≥0∞) * volume OA := by
    rw [Measure.toSphere_apply' volume hKA.measurableSet]
    simp only [OA, E, finrank_euclideanSpace_fin]
  have hOBK : volume.toSphere KB = (h : ℝ≥0∞) * volume OB := by
    rw [Measure.toSphere_apply' volume hKB.measurableSet]
    simp only [OB, E, finrank_euclideanSpace_fin]
  have hOA_gt : ENNReal.ofReal ((d / 2) ^ h) * V < volume OA := by
    by_contra hle
    have hle' := not_lt.mp hle
    have hmul : (h : ℝ≥0∞) * volume OA ≤ (h : ℝ≥0∞) * (ENNReal.ofReal ((d / 2) ^ h) * V) := by
      gcongr
    apply not_lt_of_ge hmul
    simpa [htotal, hOAK, mul_left_comm, mul_assoc] using hKAq
  have hOB_gt : ENNReal.ofReal ((d / 2) ^ h) * V < volume OB := by
    by_contra hle
    have hle' := not_lt.mp hle
    have hmul : (h : ℝ≥0∞) * volume OB ≤ (h : ℝ≥0∞) * (ENNReal.ofReal ((d / 2) ^ h) * V) := by
      gcongr
    apply not_lt_of_ge hmul
    simpa [htotal, hOBK, mul_left_comm, mul_assoc] using hKBq
  have hCA_gt : ENNReal.ofReal ((d / 2) ^ h) * V < volume CA :=
    hOA_gt.trans_le (measure_mono (Set.smul_subset_smul_right Set.Ioo_subset_Icc_self))
  have hCB_gt : ENNReal.ofReal ((d / 2) ^ h) * V < volume CB :=
    hOB_gt.trans_le (measure_mono (Set.smul_subset_smul_right Set.Ioo_subset_Icc_self))
  by_contra hfar
  push Not at hfar
  have hsub : CA + (-CB) ⊆ Metric.closedBall (0 : E) d := by
    rintro z ⟨x, ⟨r, hr, a, ⟨a', ha', rfl⟩, rfl⟩, y, hy, rfl⟩
    rcases Set.mem_neg.mp hy with ⟨s, hs, b, ⟨b', hb', rfl⟩, hby⟩
    dsimp only at hby ⊢
    have hy_eq : y = -(s • (b' : E)) := by rw [← neg_eq_iff_eq_neg.mpr hby]
    rw [hy_eq, ← sub_eq_add_neg, Metric.mem_closedBall, dist_zero_right]
    have ha_norm : ‖(a' : E)‖ = 1 := by simpa [RealSphere] using a'.2
    have hb_norm : ‖(b' : E)‖ = 1 := by simpa [RealSphere] using b'.2
    have hab : ‖(a' : E) - (b' : E)‖ ≤ d := by
      simpa [Subtype.dist_eq, dist_eq_norm] using hfar a' (hKAA ha') b' (hKBB hb')
    have hsq_ab : ‖(a' : E) - (b' : E)‖ ^ 2 ≤ d ^ 2 := by nlinarith [norm_nonneg ((a' : E) - (b' : E))]
    have hinner_ab : ‖(a' : E) - (b' : E)‖ ^ 2 = 2 - 2 * ⟪(a' : E), (b' : E)⟫ := by
      rw [norm_sub_sq_real, ha_norm, hb_norm]; ring
    have hsq_z : ‖r • (a' : E) - s • (b' : E)‖ ^ 2 =
        (r - s) ^ 2 + r * s * ‖(a' : E) - (b' : E)‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_of_nonneg hr.1, Real.norm_of_nonneg hs.1,
          ha_norm, hb_norm, real_inner_smul_left, real_inner_smul_right, hinner_ab]
      ring
    have hle_d2 : ‖r • (a' : E) - s • (b' : E)‖ ^ 2 ≤ d ^ 2 := by
      rw [hsq_z]
      have h1 : (r - s) ^ 2 + r * s * ‖(a' : E) - (b' : E)‖ ^ 2 ≤ (r - s) ^ 2 + r * s * d ^ 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq_ab (mul_nonneg hr.1 hs.1))
      have h2 : (r - s) ^ 2 ≤ 1 - r * s := by
        rcases le_total r s with hrs | hsr <;> nlinarith [hr.1, hr.2, hs.1, hs.2]
      have hd2 : 1 ≤ d ^ 2 := by nlinarith
      nlinarith [hr.1, hr.2, hs.1, hs.2]
    have hd0 : 0 ≤ d := by linarith
    nlinarith [norm_nonneg (r • (a' : E) - s • (b' : E))]
  have hneg : volume (-CB) = volume CB := Measure.measure_neg volume CB
  have hBM := compact_brunn_minkowski_euclidean hCA hCB.neg
  rw [hneg] at hBM
  have hCA_real : (d / 2) ^ h * V.toReal < (volume CA).toReal := by
    have := ENNReal.toReal_strict_mono hCA.measure_lt_top.ne hCA_gt
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hCB_real : (d / 2) ^ h * V.toReal < (volume CB).toReal := by
    have := ENNReal.toReal_strict_mono hCB.measure_lt_top.ne hCB_gt
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hsqrt_gt : d ^ h * V.toReal < (2 : ℝ) ^ h * Real.sqrt ((volume CA).toReal * (volume CB).toReal) := by
    have hprod_gt : ((d / 2) ^ h * V.toReal) ^ 2 < (volume CA).toReal * (volume CB).toReal := by
      rw [sq]
      exact mul_lt_mul'' hCA_real hCB_real (by positivity) (by positivity)
    have hsq : (d / 2) ^ h * V.toReal < Real.sqrt ((volume CA).toReal * (volume CB).toReal) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ (d / 2) ^ h * V.toReal)]
      exact Real.sqrt_lt_sqrt (by positivity) hprod_gt
    have h2 : (2 : ℝ) ^ h * ((d / 2) ^ h * V.toReal) = d ^ h * V.toReal := by
      rw [← mul_assoc, ← mul_pow]; ring
    rw [← h2]
    exact mul_lt_mul_of_pos_left hsq (by positivity)
  have hball_vol : volume (Metric.closedBall (0 : E) d) = ENNReal.ofReal (d ^ h) * V := by
    have hd0 : 0 < d := by linarith
    have hsmul : Metric.closedBall (0 : E) d = d • Metric.closedBall (0 : E) 1 := by
      ext x
      simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_smul_set]
      constructor
      · intro hx
        refine ⟨d⁻¹ • x, ?_, smul_inv_smul₀ hd0.ne' x⟩
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd0.le)]
        exact (inv_mul_le_iff₀ hd0).mpr (by simpa using hx)
      · rintro ⟨y, hy, rfl⟩
        rw [norm_smul, Real.norm_of_nonneg hd0.le]
        nlinarith
    rw [hsmul, Measure.addHaar_smul_of_nonneg volume hd0.le, finrank_euclideanSpace_fin]
    have hcb : volume (Metric.closedBall (0 : E) 1) = V := by
      simp only [V, E, EuclideanSpace.volume_closedBall, EuclideanSpace.volume_ball]
    rw [hcb]
  have hle_vol : ENNReal.ofReal ((2 : ℝ) ^ h * Real.sqrt ((volume CA).toReal * (volume CB).toReal)) ≤
      ENNReal.ofReal (d ^ h) * V :=
    hBM.trans ((measure_mono hsub).trans hball_vol.le)
  have hle_real := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV_top) hle_vol
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hle_real
  linarith

/- ## Part 3: Spherical Strip Bound via Householder Reflection & Cylinders -/

lemma exists_isometry_to_single0 {m : ℕ} (u : EuclideanSpace ℝ (Fin (m + 1))) (hu : ‖u‖ = 1) :
    ∃ L : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
      L u = EuclideanSpace.single 0 (1 : ℝ) :=
  ⟨Submodule.reflection (ℝ ∙ (u - EuclideanSpace.single 0 (1 : ℝ)))ᗮ,
    Submodule.reflection_sub (by simp [hu])⟩

lemma toSphere_preimage_linearIsometry {h : ℕ}
    (L : EuclideanSpace ℝ (Fin h) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    {s : Set (RealSphere h)} (hs : MeasurableSet s) :
    let f : RealSphere h → RealSphere h := fun x => ⟨L x, by simp [RealSphere, x.2]⟩
    volume.toSphere (f ⁻¹' s) = volume.toSphere s := by
  intro f
  have hf_cont : Continuous f := Continuous.subtype_mk (L.continuous.comp continuous_subtype_val) _
  have hpre_meas : MeasurableSet (f ⁻¹' s) := hs.preimage hf_cont.measurable
  rw [Measure.toSphere_apply' volume hpre_meas, Measure.toSphere_apply' volume hs]
  congr 1
  have hmp : MeasurePreserving L volume volume := L.measurePreserving
  have hpre_cone : L ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) =
      Set.Ioo (0 : ℝ) 1 • ((↑) '' (f ⁻¹' s)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨r, hr, y, ⟨y', hy', rfl⟩, hxy⟩
      dsimp only at hxy
      refine ⟨r, hr, L.symm y', ⟨⟨L.symm y', by simp [RealSphere, y'.2]⟩, ?_, rfl⟩, ?_⟩
      · simp only [Set.mem_preimage, f]
        convert hy' using 1
        ext; simp
      · apply L.injective
        rw [map_smul, LinearIsometryEquiv.apply_symm_apply, hxy]
    · rintro ⟨r, hr, y, ⟨y', hy', rfl⟩, rfl⟩
      dsimp only
      refine ⟨r, hr, L y', ⟨f y', hy', rfl⟩, ?_⟩
      exact (map_smul L r (y' : EuclideanSpace ℝ (Fin h))).symm
  rw [← hpre_cone, hmp.measure_preimage_emb L.toHomeomorph.measurableEmbedding]

lemma realSphere_strip_e0_le {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    volume.toSphere {x : RealSphere (m + 1) | |(x : EuclideanSpace ℝ (Fin (m + 1))) 0| ≤ t} ≤
      ENNReal.ofReal (4 * t * Real.sqrt ((m + 1 : ℕ) : ℝ)) *
        volume.toSphere (Set.univ : Set (RealSphere (m + 1))) := by
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let S : Set (RealSphere (m + 1)) := {x | |(x : E) 0| ≤ t}
  have hS_meas : MeasurableSet S :=
    (isClosed_le ((continuous_apply 0).comp ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)).abs
      continuous_const).measurableSet
  let C : Set E := Set.Ioo (0 : ℝ) 1 • ((↑) '' S)
  let B : Set E := Metric.ball (0 : E) 1
  let e1 := (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm
  let e2 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  let φ : E ≃ᵐ ℝ × (Fin m → ℝ) := e1.trans e2
  have hmp : MeasurePreserving φ volume (volume.prod volume) :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (m + 1))).trans
      (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0)
  have hφ_vol : ∀ U : Set E, volume U = (volume.prod volume) (φ '' U) := by
    intro U
    rw [← φ.preimage_symm, hmp.symm.measure_preimage_emb φ.symm.measurableEmbedding]
  let Bm : ℝ → Set (Fin m → ℝ) := fun R => {v | ∑ j : Fin m, (v j) ^ 2 < R ^ 2}
  have hC_sub : φ '' C ⊆ Set.Icc (-t) t ×ˢ Bm 1 := by
    rintro _ ⟨y, ⟨r, hr, x, ⟨x', hx', rfl⟩, rfl⟩, rfl⟩
    dsimp only
    have hx_norm : ‖(x' : E)‖ = 1 := by simp [RealSphere]
    have hnorm_sq : ∑ i : Fin (m + 1), ((r • (x' : E)) i) ^ 2 < 1 := by
      have h1 : ‖r • (x' : E)‖ = r := by rw [norm_smul, Real.norm_of_nonneg hr.1.le, hx_norm, mul_one]
      have h2 : ∑ i : Fin (m + 1), ‖(r • (x' : E)) i‖ ^ 2 = ‖r • (x' : E)‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      have h3 : ∑ i : Fin (m + 1), ((r • (x' : E)) i) ^ 2 = ‖r • (x' : E)‖ ^ 2 := by
        rw [← h2]
        apply Finset.sum_congr rfl
        intro i _
        rw [Real.norm_eq_abs, sq_abs]
      rw [h3, h1]; nlinarith [hr.1, hr.2]
    rw [Fin.sum_univ_succ] at hnorm_sq
    refine ⟨?_, ?_⟩
    · simp only [φ, e1, e2, MeasurableEquiv.trans_apply, MeasurableEquiv.piFinSuccAbove_apply,
        Set.mem_Icc]
      have hx0 : |(x' : E) 0| ≤ t := hx'
      have hy0 : |(r • (x' : E)) 0| ≤ t := by
        simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr.1]
        nlinarith [hr.2, abs_nonneg ((x' : E) 0)]
      exact abs_le.mp hy0
    · simp only [φ, e1, e2, MeasurableEquiv.trans_apply, MeasurableEquiv.piFinSuccAbove_apply,
        Bm, one_pow]
      have hsq0 : 0 ≤ ((r • (x' : E)) 0) ^ 2 := sq_nonneg _
      have heq_sum : ∑ j : Fin m, ((r • (x' : E)) (Fin.succAbove 0 j)) ^ 2 =
          ∑ j : Fin m, ((r • (x' : E)) j.succ) ^ 2 := by
        apply Finset.sum_congr rfl; intro j _; rfl
      change ∑ j : Fin m, ((r • (x' : E)) (Fin.succAbove 0 j)) ^ 2 < 1
      linarith
  have hC_vol : volume C ≤ ENNReal.ofReal (2 * t) * volume (Bm 1) := by
    rw [hφ_vol C]
    calc
      (volume.prod volume) (φ '' C) ≤ (volume.prod volume) (Set.Icc (-t) t ×ˢ Bm 1) :=
        measure_mono hC_sub
      _ = volume (Set.Icc (-t) t) * volume (Bm 1) := Measure.prod_prod _ _
      _ = ENNReal.ofReal (2 * t) * volume (Bm 1) := by rw [Real.volume_Icc]; ring_nf
  set r : ℝ := 1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))
  have hr_pos : 0 < r := by positivity
  have hr2 : r ^ 2 = 1 / (4 * ((m : ℝ) + 1)) := by
    simp only [r, div_pow, one_pow, mul_pow, Nat.cast_add, Nat.cast_one,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
    ring
  have hr2_le : r ^ 2 ≤ 1 / 4 := by
    rw [hr2]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have h1mr2_pos : 0 < 1 - r ^ 2 := by linarith
  set R : ℝ := Real.sqrt (1 - r ^ 2)
  have hR_pos : 0 < R := Real.sqrt_pos.mpr h1mr2_pos
  have hB_sup : Set.Ioo (-r) r ×ˢ Bm R ⊆ φ '' B := by
    rintro ⟨a, v⟩ ⟨ha, hv⟩
    refine ⟨φ.symm (a, v), ?_, φ.apply_symm_apply _⟩
    simp only [B, Metric.mem_ball, dist_zero_right]
    have hnorm_sq : ‖φ.symm (a, v)‖ ^ 2 = a ^ 2 + ∑ j : Fin m, (v j) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_succ]
      have h0 : (φ.symm (a, v)).ofLp 0 = a := by
        change (Fin.cons a v : Fin (m + 1) → ℝ) 0 = a
        simp
      have hs : ∀ j : Fin m, (φ.symm (a, v)).ofLp j.succ = v j := fun j => by
        change (Fin.cons a v : Fin (m + 1) → ℝ) j.succ = v j
        simp
      simp [Real.norm_eq_abs, sq_abs, h0, hs]
    have ha2 : a ^ 2 < r ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hr_pos]
      exact abs_lt.mpr ha
    have hv2 : ∑ j : Fin m, (v j) ^ 2 < 1 - r ^ 2 := by
      have : ∑ j : Fin m, (v j) ^ 2 < R ^ 2 := hv
      rwa [Real.sq_sqrt h1mr2_pos.le] at this
    have hlt1 : ‖φ.symm (a, v)‖ ^ 2 < 1 := by linarith
    nlinarith [norm_nonneg (φ.symm (a, v))]
  have hBmR_eq : Bm R = R • Bm 1 := by
    ext v
    simp only [Bm, Set.mem_smul_set, one_pow]
    constructor
    · intro hv
      refine ⟨R⁻¹ • v, ?_, smul_inv_smul₀ hR_pos.ne' v⟩
      change ∑ j : Fin m, ((R⁻¹ • v) j) ^ 2 < 1
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR_pos
      calc
        (R⁻¹) ^ 2 * ∑ j : Fin m, (v j) ^ 2 < (R⁻¹) ^ 2 * R ^ 2 :=
          mul_lt_mul_of_pos_left hv (by positivity)
        _ = 1 := by rw [inv_pow, inv_mul_cancel₀ hR2.ne']
    · rintro ⟨w, hw, rfl⟩
      change ∑ j : Fin m, ((R • w) j) ^ 2 < R ^ 2
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR_pos
      have hw' : ∑ j : Fin m, (w j) ^ 2 < 1 := hw
      nlinarith
  have hRm_ge : (1 / 2 : ℝ) ≤ R ^ m := by
    have hbern : 1 + (m : ℝ) * (-r ^ 2) ≤ (1 + (-r ^ 2)) ^ m :=
      one_add_mul_le_pow (by linarith) m
    have h1 : (m : ℝ) * r ^ 2 ≤ 1 / 4 := by
      rw [hr2, mul_div_assoc', mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h34 : (1 / 4 : ℝ) ≤ (1 - r ^ 2) ^ m := by
      have heq1 : 1 + (m : ℝ) * (-r ^ 2) = 1 - (m : ℝ) * r ^ 2 := by ring
      have heq2 : 1 + (-r ^ 2) = 1 - r ^ 2 := by ring
      rw [heq1, heq2] at hbern
      linarith
    have hRm : R ^ m = Real.sqrt ((1 - r ^ 2) ^ m) := by
      rw [← Real.sqrt_sq (pow_nonneg hR_pos.le m), ← pow_mul, mul_comm m 2, pow_mul,
          Real.sq_sqrt h1mr2_pos.le]
    rw [hRm]
    have hsqrt14 : (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsqrt14]
    exact Real.sqrt_le_sqrt h34
  have hB_vol : ENNReal.ofReal (1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))) * volume (Bm 1) ≤ volume B := by
    rw [hφ_vol B]
    have hsmul_vol : volume (Bm R) = ENNReal.ofReal (R ^ m) * volume (Bm 1) := by
      rw [hBmR_eq, Measure.addHaar_smul_of_nonneg volume hR_pos.le, Module.finrank_fin_fun]
    have hprod_le : volume (Set.Ioo (-r) r) * volume (Bm R) ≤ (volume.prod volume) (φ '' B) := by
      rw [← Measure.prod_prod]
      exact measure_mono hB_sup
    rw [Real.volume_Ioo, show r - -r = 2 * r by ring, hsmul_vol, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)] at hprod_le
    refine le_trans ?_ hprod_le
    gcongr
    have : 2 * r * (1 / 2) = 1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ)) := by simp only [r]; ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left hRm_ge (by positivity)
  have hC_le_B : volume C ≤ ENNReal.ofReal (4 * t * Real.sqrt ((m + 1 : ℕ) : ℝ)) * volume B := by
    have hmul : ENNReal.ofReal (4 * t * Real.sqrt ((m + 1 : ℕ) : ℝ)) *
        ENNReal.ofReal (1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))) = ENNReal.ofReal (2 * t) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hsq_pos : (0 : ℝ) < Real.sqrt ((m + 1 : ℕ) : ℝ) := by positivity
      field_simp [hsq_pos.ne']
      ring
    calc
      volume C ≤ ENNReal.ofReal (2 * t) * volume (Bm 1) := hC_vol
      _ = ENNReal.ofReal (4 * t * Real.sqrt ((m + 1 : ℕ) : ℝ)) *
            (ENNReal.ofReal (1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))) * volume (Bm 1)) := by
            rw [← mul_assoc, hmul]
      _ ≤ ENNReal.ofReal (4 * t * Real.sqrt ((m + 1 : ℕ) : ℝ)) * volume B := by gcongr
  rw [Measure.toSphere_apply' volume hS_meas, Measure.toSphere_apply_univ]
  simp only [finrank_euclideanSpace_fin]
  calc
    ((m + 1 : ℕ) : ℝ≥0∞) * volume C
        ≤ ((m + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (4 * t * Real.sqrt ((m + 1 : ℕ) : ℝ)) * volume B) := by
          gcongr
    _ = ENNReal.ofReal (4 * t * Real.sqrt ((m + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ≥0∞) * volume B) := by
          ring

lemma realSphere_strip_le {m : ℕ} (hm : 1 ≤ m)
    (u : EuclideanSpace ℝ (Fin (m + 1))) (hu : ‖u‖ = 1) {t : ℝ} (ht : 0 < t) :
    volume.toSphere {x : RealSphere (m + 1) | |⟪u, (x : EuclideanSpace ℝ (Fin (m + 1)))⟫| ≤ t} ≤
      ENNReal.ofReal (4 * t * Real.sqrt ((m + 1 : ℕ) : ℝ)) *
        volume.toSphere (Set.univ : Set (RealSphere (m + 1))) := by
  obtain ⟨L, hLu⟩ := exists_isometry_to_single0 u hu
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let S0 : Set (RealSphere (m + 1)) := {y | |(y : E) 0| ≤ t}
  have hS0_meas : MeasurableSet S0 :=
    (isClosed_le ((continuous_apply 0).comp ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)).abs
      continuous_const).measurableSet
  have heq : {x : RealSphere (m + 1) | |⟪u, (x : E)⟫| ≤ t} =
      (fun x : RealSphere (m + 1) => (⟨L x, by simp [RealSphere, x.2]⟩ : RealSphere (m + 1))) ⁻¹' S0 := by
    ext x
    simp only [Set.mem_preimage, S0]
    have hinner : ⟪u, (x : E)⟫ = (L x) 0 := by
      rw [← L.inner_map_map u x, hLu, real_inner_comm]
      simpa using (EuclideanSpace.inner_single_right (0 : Fin (m + 1)) (1 : ℝ) (L x))
    change |⟪u, (x : E)⟫| ≤ t ↔ |(L x) 0| ≤ t
    rw [hinner]
  rw [heq, toSphere_preimage_linearIsometry L hS0_meas]
  exact realSphere_strip_e0_le hm ht

/- ## Part 4: Complex Sphere, Order-3 Rotation, Geometry & K₅-Freeness -/

abbrev ComplexSpace (k : ℕ) := EuclideanSpace ℂ (Fin (k + 1))
abbrev ComplexSphere (k : ℕ) := Metric.sphere (0 : ComplexSpace k) 1

noncomputable def rho : ℂ := ⟨-(1 / 2), Real.sqrt 3 / 2⟩

lemma rho_re : rho.re = -(1 / 2) := rfl
lemma rho_im : rho.im = Real.sqrt 3 / 2 := rfl

lemma rho_sq : rho ^ 2 = ⟨-(1 / 2), -(Real.sqrt 3 / 2)⟩ := by
  apply Complex.ext
  · simp [sq, rho, Complex.mul_re]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · simp [sq, rho, Complex.mul_im]; ring

lemma rho_cube : rho ^ 3 = 1 := by
  rw [pow_succ, rho_sq]
  apply Complex.ext
  · simp [rho, Complex.mul_re]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · simp [rho, Complex.mul_im]; ring

lemma one_add_rho_add_sq : (1 : ℂ) + rho + rho ^ 2 = 0 := by
  rw [rho_sq]
  apply Complex.ext <;> simp [rho] <;> ring

lemma star_rho : starRingEnd ℂ rho = rho ^ 2 := by
  rw [rho_sq]
  apply Complex.ext <;> simp [rho]

lemma star_rho_sq : starRingEnd ℂ (rho ^ 2) = rho := by
  rw [← star_rho, starRingEnd_self_apply]

lemma norm_rho : ‖rho‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  have : rho.re * rho.re + rho.im * rho.im = 1 := by
    simp only [rho_re, rho_im]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [this, Real.sqrt_one]

lemma norm_rho_sq : ‖rho ^ 2‖ = 1 := by
  rw [norm_pow, norm_rho, one_pow]

lemma norm_rho_pow (n : ℕ) : ‖rho ^ n‖ = 1 := by
  rw [norm_pow, norm_rho, one_pow]

lemma norm_one_sub_rho : ‖(1 : ℂ) - rho‖ = Real.sqrt 3 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.one_re, rho_re, Complex.sub_im, Complex.one_im, rho_im]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

lemma norm_one_sub_rho_sq : ‖(1 : ℂ) - rho ^ 2‖ = Real.sqrt 3 := by
  rw [← star_rho, show (1 : ℂ) - starRingEnd ℂ rho = starRingEnd ℂ ((1 : ℂ) - rho) by simp,
      Complex.norm_conj, norm_one_sub_rho]

noncomputable def complexToReal (k : ℕ) :
    ComplexSpace k ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ((k + 1) + (k + 1))) :=
  { toFun := fun z => WithLp.toLp 2 fun idx : Fin ((k + 1) + (k + 1)) =>
      if h : idx.1 < k + 1 then (z ⟨idx.1, h⟩).re else (z ⟨idx.1 - (k + 1), by omega⟩).im
    map_add' := fun x y => by
      ext idx
      simp only [PiLp.toLp_apply, PiLp.add_apply]
      split_ifs <;> simp
    map_smul' := fun r x => by
      ext idx
      simp only [RingHom.id_apply, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
      split_ifs <;> simp [Complex.real_smul]
    invFun := fun x => WithLp.toLp 2 fun i => ⟨x ⟨i.1, by omega⟩, x ⟨i.1 + (k + 1), by omega⟩⟩
    left_inv := fun z => by
      ext i
      have h1 : i.1 < k + 1 := i.2
      have h2 : ¬ (i.1 + (k + 1) < k + 1) := by omega
      apply Complex.ext
      · simp [h1]
      · simp [h2]
    right_inv := fun x => by
      ext idx
      dsimp only
      split_ifs with h
      · exact congrArg x.ofLp (Fin.ext rfl)
      · exact congrArg x.ofLp (Fin.ext (by dsimp only; omega))
    norm_map' := fun z => by
      change ‖(WithLp.toLp 2 fun idx : Fin ((k + 1) + (k + 1)) =>
          if h : idx.1 < k + 1 then (z ⟨idx.1, h⟩).re else (z ⟨idx.1 - (k + 1), by omega⟩).im)‖ = ‖z‖
      have hsq : ‖(WithLp.toLp 2 fun idx : Fin ((k + 1) + (k + 1)) =>
          if h : idx.1 < k + 1 then (z ⟨idx.1, h⟩).re else (z ⟨idx.1 - (k + 1), by omega⟩).im)‖ ^ 2 = ‖z‖ ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
            EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
            Fin.sum_univ_add]
        simp only [Real.norm_eq_abs, sq_abs]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have h1 : (Fin.castAdd (k + 1) i).1 < k + 1 := i.2
        have h2 : ¬ (Fin.natAdd (k + 1) i).1 < k + 1 := by simp only [Fin.val_natAdd]; omega
        have hsub : (Fin.natAdd (k + 1) i).1 - (k + 1) = i.1 := by simp only [Fin.val_natAdd]; omega
        simp only [h1, h2, ↓reduceDIte]
        rw [show (⟨(Fin.castAdd (k + 1) i).1, h1⟩ : Fin (k + 1)) = i by ext; simp]
        rw [show (⟨(Fin.natAdd (k + 1) i).1 - (k + 1), _⟩ : Fin (k + 1)) = i by ext; exact hsub]
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      nlinarith [norm_nonneg z, norm_nonneg (WithLp.toLp 2 fun idx : Fin ((k + 1) + (k + 1)) =>
        if h : idx.1 < k + 1 then (z ⟨idx.1, h⟩).re else (z ⟨idx.1 - (k + 1), by omega⟩).im)] }

lemma complexToReal_inner_eq_re (k : ℕ) (x y : ComplexSpace k) :
    ⟪complexToReal k x, complexToReal k y⟫ = (inner ℂ x y).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_add, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h1 : (Fin.castAdd (k + 1) i).1 < k + 1 := i.2
  have h2 : ¬ (Fin.natAdd (k + 1) i).1 < k + 1 := by simp only [Fin.val_natAdd]; omega
  have hsub : (Fin.natAdd (k + 1) i).1 - (k + 1) = i.1 := by simp only [Fin.val_natAdd]; omega
  have hcast : ∀ z : ComplexSpace k, (complexToReal k z).ofLp (Fin.castAdd (k + 1) i) = (z i).re := fun z => by
    change (if h : (Fin.castAdd (k + 1) i).1 < k + 1 then (z ⟨(Fin.castAdd (k + 1) i).1, h⟩).re
      else (z ⟨(Fin.castAdd (k + 1) i).1 - (k + 1), _⟩).im) = (z i).re
    rw [dif_pos h1, show (⟨(Fin.castAdd (k + 1) i).1, h1⟩ : Fin (k + 1)) = i by ext; simp]
  have hnat : ∀ z : ComplexSpace k, (complexToReal k z).ofLp (Fin.natAdd (k + 1) i) = (z i).im := fun z => by
    change (if h : (Fin.natAdd (k + 1) i).1 < k + 1 then (z ⟨(Fin.natAdd (k + 1) i).1, h⟩).re
      else (z ⟨(Fin.natAdd (k + 1) i).1 - (k + 1), _⟩).im) = (z i).im
    rw [dif_neg h2, show (⟨(Fin.natAdd (k + 1) i).1 - (k + 1), _⟩ : Fin (k + 1)) = i by ext; exact hsub]
  change (complexToReal k y).ofLp (Fin.castAdd (k + 1) i) * (complexToReal k x).ofLp (Fin.castAdd (k + 1) i) +
      (complexToReal k y).ofLp (Fin.natAdd (k + 1) i) * (complexToReal k x).ofLp (Fin.natAdd (k + 1) i) =
      (y i * starRingEnd ℂ (x i)).re
  rw [hcast, hcast, hnat, hnat]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

noncomputable def sphereToReal (k : ℕ) : ComplexSphere k ≃ₜ RealSphere ((k + 1) + (k + 1)) where
  toFun := fun x => ⟨complexToReal k x, by simp [RealSphere, x.2]⟩
  invFun := fun y => ⟨(complexToReal k).symm y, by simp [ComplexSphere, y.2]⟩
  left_inv := fun x => by ext; simp
  right_inv := fun y => by ext; simp
  continuous_toFun := Continuous.subtype_mk ((complexToReal k).continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk ((complexToReal k).symm.continuous.comp continuous_subtype_val) _

lemma dist_sphereToReal (k : ℕ) (x y : ComplexSphere k) :
    dist (sphereToReal k x) (sphereToReal k y) = dist x y := by
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  change ‖complexToReal k (x : ComplexSpace k) - complexToReal k (y : ComplexSpace k)‖ =
    ‖(x : ComplexSpace k) - (y : ComplexSpace k)‖
  rw [← map_sub, LinearIsometryEquiv.norm_map]

noncomputable def complexProb (k : ℕ) (A : Set (ComplexSphere k)) : ℝ :=
  (volume.toSphere (sphereToReal k '' A)).toReal /
    (volume.toSphere (Set.univ : Set (RealSphere ((k + 1) + (k + 1))))).toReal

lemma realSphere_univ_pos (k : ℕ) :
    0 < (volume.toSphere (Set.univ : Set (RealSphere ((k + 1) + (k + 1))))).toReal := by
  haveI : Nonempty (Fin ((k + 1) + (k + 1))) := ⟨⟨0, by omega⟩⟩
  have h1 : volume.toSphere (Set.univ : Set (RealSphere ((k + 1) + (k + 1)))) ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    exact mul_ne_zero (by simp) (Metric.measure_ball_pos volume 0 one_pos).ne'
  have h2 : volume.toSphere (Set.univ : Set (RealSphere ((k + 1) + (k + 1)))) ≠ ∞ :=
    measure_ne_top _ _
  exact ENNReal.toReal_pos h1 h2

lemma complexProb_nonneg (k : ℕ) (A : Set (ComplexSphere k)) : 0 ≤ complexProb k A :=
  div_nonneg ENNReal.toReal_nonneg (realSphere_univ_pos k).le

lemma complexProb_univ (k : ℕ) : complexProb k Set.univ = 1 := by
  unfold complexProb
  rw [Set.image_univ, (sphereToReal k).surjective.range_eq]
  exact div_self (realSphere_univ_pos k).ne'

lemma complexProb_mono (k : ℕ) {A B : Set (ComplexSphere k)} (h : A ⊆ B) :
    complexProb k A ≤ complexProb k B := by
  unfold complexProb
  exact div_le_div_of_nonneg_right
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.image_mono h)))
    (realSphere_univ_pos k).le

lemma complexProb_union_le (k : ℕ) (A B : Set (ComplexSphere k)) :
    complexProb k (A ∪ B) ≤ complexProb k A + complexProb k B := by
  unfold complexProb
  rw [← add_div, Set.image_union]
  apply div_le_div_of_nonneg_right _ (realSphere_univ_pos k).le
  have h1 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top volume.toSphere _, measure_ne_top volume.toSphere _⟩)
    (measure_union_le (μ := volume.toSphere) (sphereToReal k '' A) (sphereToReal k '' B))
  rwa [ENNReal.toReal_add (measure_ne_top volume.toSphere _) (measure_ne_top volume.toSphere _)] at h1

lemma complexProb_biUnion_finset_le {ι : Type*} (k : ℕ) (s : Finset ι) (f : ι → Set (ComplexSphere k)) :
    complexProb k (⋃ i ∈ s, f i) ≤ ∑ i ∈ s, complexProb k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [complexProb]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    linarith [complexProb_union_le k (f a) (⋃ i ∈ s, f i)]

lemma complexProb_biUnion_finset_eq {ι : Type*} (k : ℕ) (s : Finset ι) (f : ι → Set (ComplexSphere k))
    (hm : ∀ i ∈ s, MeasurableSet (f i))
    (hd : Set.Pairwise (s : Set ι) fun i j => Disjoint (f i) (f j)) :
    complexProb k (⋃ i ∈ s, f i) = ∑ i ∈ s, complexProb k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [complexProb]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    have hdisj : Disjoint (sphereToReal k '' f a) (sphereToReal k '' (⋃ i ∈ s, f i)) := by
      rw [Set.disjoint_image_iff (sphereToReal k).injective, Set.disjoint_iUnion₂_right]
      intro i hi
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    have hmeas_rest : MeasurableSet (sphereToReal k '' (⋃ i ∈ s, f i)) := by
      rw [← (sphereToReal k).preimage_symm]
      exact (MeasurableSet.biUnion s.countable_toSet fun i hi =>
        hm i (Finset.mem_insert_of_mem hi)).preimage (sphereToReal k).symm.continuous.measurable
    have hadd : complexProb k (f a ∪ ⋃ i ∈ s, f i) = complexProb k (f a) + complexProb k (⋃ i ∈ s, f i) := by
      unfold complexProb
      rw [← add_div, Set.image_union, measure_union hdisj hmeas_rest,
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [hadd, ih (fun i hi => hm i (Finset.mem_insert_of_mem hi))
      (hd.mono (Finset.coe_subset.mpr (Finset.subset_insert a s)))]

lemma complexProb_smul_unit (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    {A : Set (ComplexSphere k)} (hA : MeasurableSet A) :
    let rot : ComplexSphere k → ComplexSphere k := fun x => ⟨u • (x : ComplexSpace k), by
      simp [ComplexSphere, norm_smul, hu, x.2]⟩
    complexProb k (rot '' A) = complexProb k A := by
  intro rot
  have hu_mul : starRingEnd ℂ u * u = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu]; norm_num
  have hu_mul' : u * starRingEnd ℂ u = 1 := by rw [mul_comm, hu_mul]
  let L_C : ComplexSpace k ≃ₗᵢ[ℝ] ComplexSpace k :=
    { toFun := fun z => u • z
      map_add' := smul_add u
      map_smul' := fun r z => by
        simp only [RingHom.id_apply]
        rw [smul_comm]
      invFun := fun z => (starRingEnd ℂ u) • z
      left_inv := fun z => by dsimp only; rw [smul_smul, hu_mul, one_smul]
      right_inv := fun z => by dsimp only; rw [smul_smul, hu_mul', one_smul]
      norm_map' := fun z => by change ‖u • z‖ = ‖z‖; rw [norm_smul, hu, one_mul] }
  let L_R := ((complexToReal k).symm.trans L_C).trans (complexToReal k)
  have hLR_apply : ∀ z : ComplexSpace k, L_R (complexToReal k z) = complexToReal k (u • z) := fun z => by
    simp only [L_R, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]; rfl
  have himg : sphereToReal k '' (rot '' A) =
      (fun y : RealSphere ((k + 1) + (k + 1)) => (⟨L_R.symm y, by simp [RealSphere, y.2]⟩ : RealSphere _)) ⁻¹'
        (sphereToReal k '' A) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨a, ha, ?_⟩
      ext : 1
      change complexToReal k (a : ComplexSpace k) = L_R.symm (complexToReal k (u • (a : ComplexSpace k)))
      rw [← hLR_apply, LinearIsometryEquiv.symm_apply_apply]
    · rintro ⟨a, ha, hya⟩
      refine ⟨rot a, ⟨a, ha, rfl⟩, ?_⟩
      ext : 1
      have hya' : complexToReal k (a : ComplexSpace k) = L_R.symm (y : EuclideanSpace ℝ _) :=
        congrArg Subtype.val hya
      have hy_eq : (y : EuclideanSpace ℝ _) = L_R (complexToReal k (a : ComplexSpace k)) := by
        rw [hya', LinearIsometryEquiv.apply_symm_apply]
      change complexToReal k (u • (a : ComplexSpace k)) = (y : EuclideanSpace ℝ _)
      rw [hy_eq, hLR_apply]
  have hA_R : MeasurableSet (sphereToReal k '' A) := by
    rw [← (sphereToReal k).preimage_symm]
    exact hA.preimage (sphereToReal k).symm.continuous.measurable
  unfold complexProb
  rw [himg, toSphere_preimage_linearIsometry L_R.symm hA_R]

def rotationClose {k : ℕ} (d : ℝ) (x y : ComplexSphere k) : Prop :=
  ‖(x : ComplexSpace k) - rho • (y : ComplexSpace k)‖ ≤ d ∨
    ‖(x : ComplexSpace k) - rho ^ 2 • (y : ComplexSpace k)‖ ≤ d

lemma rotationClose_irrefl {k : ℕ} {d : ℝ} (hd : d < Real.sqrt 3) (x : ComplexSphere k) :
    ¬ rotationClose d x x := by
  have hx : ‖(x : ComplexSpace k)‖ = 1 := by simpa [ComplexSphere] using x.2
  rintro (h | h)
  · have h1 : ‖(x : ComplexSpace k) - rho • (x : ComplexSpace k)‖ = Real.sqrt 3 := by
      rw [show (x : ComplexSpace k) - rho • (x : ComplexSpace k) = ((1 : ℂ) - rho) • (x : ComplexSpace k) by
            rw [sub_smul, one_smul], norm_smul, norm_one_sub_rho, hx, mul_one]
    linarith
  · have h2 : ‖(x : ComplexSpace k) - rho ^ 2 • (x : ComplexSpace k)‖ = Real.sqrt 3 := by
      rw [show (x : ComplexSpace k) - rho ^ 2 • (x : ComplexSpace k) = ((1 : ℂ) - rho ^ 2) • (x : ComplexSpace k) by
            rw [sub_smul, one_smul], norm_smul, norm_one_sub_rho_sq, hx, mul_one]
    linarith

lemma norm_sub_rho_symm {k : ℕ} (x y : ComplexSpace k) :
    ‖x - rho • y‖ = ‖y - rho ^ 2 • x‖ := by
  have h1 : ‖rho ^ 2 • (x - rho • y)‖ = ‖x - rho • y‖ := by
    rw [norm_smul, norm_rho_sq, one_mul]
  rw [← h1, smul_sub, smul_smul, show rho ^ 2 * rho = 1 by rw [← pow_succ, rho_cube], one_smul,
      norm_sub_rev]

lemma rotationClose_symm {k : ℕ} {d : ℝ} {x y : ComplexSphere k}
    (h : rotationClose d x y) : rotationClose d y x := by
  rcases h with h | h
  · right; rwa [← norm_sub_rho_symm]
  · left; rwa [norm_sub_rho_symm]

lemma rotationClose_smul_rho_pow {k : ℕ} {d : ℝ} (q : Fin 3) {x y : ComplexSphere k}
    (h : rotationClose d x y) :
    rotationClose d
      ⟨rho ^ q.1 • (x : ComplexSpace k), by simp [ComplexSphere, norm_smul, norm_rho, x.2]⟩
      ⟨rho ^ q.1 • (y : ComplexSpace k), by simp [ComplexSphere, norm_smul, norm_rho, y.2]⟩ := by
  rcases h with h | h
  · left
    change ‖rho ^ q.1 • (x : ComplexSpace k) - rho • (rho ^ q.1 • (y : ComplexSpace k))‖ ≤ d
    rw [smul_comm rho (rho ^ q.1), ← smul_sub, norm_smul, norm_rho_pow, one_mul]
    exact h
  · right
    change ‖rho ^ q.1 • (x : ComplexSpace k) - rho ^ 2 • (rho ^ q.1 • (y : ComplexSpace k))‖ ≤ d
    rw [smul_comm (rho ^ 2) (rho ^ q.1), ← smul_sub, norm_smul, norm_rho_pow, one_mul]
    exact h

lemma complexSphere_three_close {k : ℕ} {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {A : Set (ComplexSphere k)} (hA : MeasurableSet A)
    (hA_big : 3 * (1 - η / 2) ^ ((k + 1) + (k + 1)) < complexProb k A) :
    ∃ a₀ ∈ A, ∃ a₁ ∈ A, ∃ a₂ ∈ A,
      rotationClose (4 * Real.sqrt η) a₀ a₁ ∧
      rotationClose (4 * Real.sqrt η) a₀ a₂ ∧
      rotationClose (4 * Real.sqrt η) a₁ a₂ := by
  set h : ℕ := (k + 1) + (k + 1)
  set d₀ : ℝ := 2 - η
  have hd₀_ge1 : 1 ≤ d₀ := by linarith
  have hd₀_half : d₀ / 2 = 1 - η / 2 := by ring
  have h1m_nonneg : 0 ≤ 1 - η / 2 := by linarith
  let rot1 : ComplexSphere k → ComplexSphere k := fun a =>
    ⟨(-rho) • (a : ComplexSpace k), by simp [ComplexSphere, norm_smul, norm_rho, a.2]⟩
  let rot2 : ComplexSphere k → ComplexSphere k := fun a =>
    ⟨(-rho ^ 2) • (a : ComplexSpace k), by simp [ComplexSphere, norm_smul, norm_rho, a.2]⟩
  let B₁ : Set (ComplexSphere k) := {x | ∃ a ∈ A, d₀ < dist (rot1 a) x}
  let B₂ : Set (ComplexSphere k) := {x | ∃ a ∈ A, d₀ < dist (rot2 a) x}
  have hB₁_open : IsOpen B₁ := by
    have : B₁ = ⋃ a ∈ A, {x | d₀ < dist (rot1 a) x} := by ext x; simp [B₁]
    rw [this]
    exact isOpen_biUnion fun a _ => isOpen_lt continuous_const (continuous_const.dist continuous_id)
  have hB₂_open : IsOpen B₂ := by
    have : B₂ = ⋃ a ∈ A, {x | d₀ < dist (rot2 a) x} := by ext x; simp [B₂]
    rw [this]
    exact isOpen_biUnion fun a _ => isOpen_lt continuous_const (continuous_const.dist continuous_id)
  have hcompl_le : ∀ (u : ℂ) (hu : ‖u‖ = 1) (B : Set (ComplexSphere k)),
      IsOpen B →
      (∀ a ∈ A, ∀ x ∈ Bᶜ, dist (⟨u • (a : ComplexSpace k), by simp [ComplexSphere, norm_smul, hu, a.2]⟩ : ComplexSphere k) x ≤ d₀) →
      complexProb k Bᶜ ≤ (1 - η / 2) ^ h := by
    intro u hu B hBo hno
    by_contra hgt
    have hgt' := not_le.mp hgt
    let rotU : ComplexSphere k → ComplexSphere k := fun a =>
      ⟨u • (a : ComplexSpace k), by simp [ComplexSphere, norm_smul, hu, a.2]⟩
    have hrotU_prob : complexProb k (rotU '' A) = complexProb k A := complexProb_smul_unit k u hu hA
    have h1_big : (d₀ / 2) ^ h < complexProb k (rotU '' A) := by
      rw [hrotU_prob, hd₀_half]
      have : 0 ≤ (1 - η / 2) ^ h := pow_nonneg h1m_nonneg h
      linarith
    have h2_big : (d₀ / 2) ^ h < complexProb k Bᶜ := by rwa [hd₀_half]
    have hUpos := realSphere_univ_pos k
    have hto_lt : ∀ {S : Set (ComplexSphere k)}, (d₀ / 2) ^ h < complexProb k S →
        ENNReal.ofReal ((d₀ / 2) ^ h) * volume.toSphere (Set.univ : Set (RealSphere h)) <
          volume.toSphere (sphereToReal k '' S) := by
      intro S hS
      unfold complexProb at hS
      have hmul : (d₀ / 2) ^ h * (volume.toSphere (Set.univ : Set (RealSphere h))).toReal <
          (volume.toSphere (sphereToReal k '' S)).toReal :=
        (lt_div_iff₀ hUpos).mp hS
      have htop : ENNReal.ofReal ((d₀ / 2) ^ h) * volume.toSphere (Set.univ : Set (RealSphere h)) ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
      rw [← ENNReal.toReal_lt_toReal htop (measure_ne_top _ _),
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      exact hmul
    have hu_mul : starRingEnd ℂ u * u = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu]; norm_num
    have hu_mul' : u * starRingEnd ℂ u = 1 := by rw [mul_comm, hu_mul]
    have hA_R : MeasurableSet (sphereToReal k '' (rotU '' A)) := by
      rw [← (sphereToReal k).preimage_symm]
      let L_inv : ComplexSphere k → ComplexSphere k := fun x =>
        ⟨(starRingEnd ℂ u) • (x : ComplexSpace k), by simp [ComplexSphere, norm_smul, hu, x.2]⟩
      have hrot_eq : rotU '' A = L_inv ⁻¹' A := by
        ext x
        simp only [Set.mem_image, Set.mem_preimage, rotU, L_inv]
        constructor
        · rintro ⟨a, ha, rfl⟩
          convert ha using 1
          ext : 1; simp [smul_smul, hu_mul]
        · intro hx
          refine ⟨L_inv x, hx, ?_⟩
          ext : 1; simp [L_inv, smul_smul, hu_mul']
      rw [hrot_eq]
      have hL_cont : Continuous L_inv :=
        Continuous.subtype_mk (continuous_subtype_val.const_smul (starRingEnd ℂ u)) _
      exact (hA.preimage hL_cont.measurable).preimage (sphereToReal k).symm.continuous.measurable
    have hB_R : MeasurableSet (sphereToReal k '' Bᶜ) := by
      rw [← (sphereToReal k).preimage_symm]
      exact hBo.isClosed_compl.measurableSet.preimage (sphereToReal k).symm.continuous.measurable
    obtain ⟨xR, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, yR, ⟨b, hb, rfl⟩, hfar⟩ :=
      realSphere_two_set_far (by omega : 0 < h) hA_R hB_R hd₀_ge1 (hto_lt h1_big) (hto_lt h2_big)
    rw [dist_sphereToReal] at hfar
    exact not_lt_of_ge (hno a ha b hb) hfar
  have hB₁c : complexProb k B₁ᶜ ≤ (1 - η / 2) ^ h :=
    hcompl_le (-rho) (by rw [norm_neg, norm_rho]) B₁ hB₁_open (fun a ha x hx => by
      by_contra hlt; exact hx ⟨a, ha, not_le.mp hlt⟩)
  have hB₂c : complexProb k B₂ᶜ ≤ (1 - η / 2) ^ h :=
    hcompl_le (-rho ^ 2) (by rw [norm_neg, norm_rho_sq]) B₂ hB₂_open (fun a ha x hx => by
      by_contra hlt; exact hx ⟨a, ha, not_le.mp hlt⟩)
  have hne : (A ∩ B₁ ∩ B₂).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hsub : A ⊆ B₁ᶜ ∪ B₂ᶜ := by
      intro x hx
      by_contra hnot
      rw [Set.mem_union, not_or, Set.mem_compl_iff, Set.mem_compl_iff, not_not, not_not] at hnot
      have : x ∈ A ∩ B₁ ∩ B₂ := ⟨⟨hx, hnot.1⟩, hnot.2⟩
      rw [hemp] at this; exact this
    have hle := (complexProb_mono k hsub).trans (complexProb_union_le k B₁ᶜ B₂ᶜ)
    have hpos_pow : 0 ≤ (1 - η / 2) ^ h := pow_nonneg h1m_nonneg h
    linarith
  obtain ⟨a₀, ⟨ha₀, ⟨a₁, ha₁, hfar₁⟩⟩, ⟨a₂, ha₂, hfar₂⟩⟩ := hne
  have hclose_of_far : ∀ (u : ℂ) (hu : ‖u‖ = 1) (x y : ComplexSphere k),
      d₀ < dist (⟨(-u) • (x : ComplexSpace k), by simp [ComplexSphere, norm_smul, hu, x.2]⟩ : ComplexSphere k) y →
      ‖(y : ComplexSpace k) - u • (x : ComplexSpace k)‖ ≤ 2 * Real.sqrt η := by
    intro u hu x y hfar
    have hfar' : d₀ < ‖(y : ComplexSpace k) + u • (x : ComplexSpace k)‖ := by
      have : dist (⟨(-u) • (x : ComplexSpace k), by simp [ComplexSphere, norm_smul, hu]⟩ : ComplexSphere k) y =
          ‖(y : ComplexSpace k) + u • (x : ComplexSpace k)‖ := by
        simp only [Subtype.dist_eq, dist_eq_norm, neg_smul, neg_sub_left, norm_neg, add_comm]
      rwa [← this]
    have hy1 : ‖(y : ComplexSpace k)‖ = 1 := by simpa [ComplexSphere] using y.2
    have hux1 : ‖u • (x : ComplexSpace k)‖ = 1 := by
      rw [norm_smul, hu, one_mul]; simpa [ComplexSphere] using x.2
    have hpar : ‖(y : ComplexSpace k) + u • (x : ComplexSpace k)‖ ^ 2 +
        ‖(y : ComplexSpace k) - u • (x : ComplexSpace k)‖ ^ 2 = 4 := by
      have := parallelogram_law_with_norm ℂ (y : ComplexSpace k) (u • (x : ComplexSpace k))
      rw [hy1, hux1] at this
      nlinarith
    have hsq : ‖(y : ComplexSpace k) - u • (x : ComplexSpace k)‖ ^ 2 ≤ 4 * η := by
      have : d₀ ^ 2 < ‖(y : ComplexSpace k) + u • (x : ComplexSpace k)‖ ^ 2 := by nlinarith
      nlinarith [sq_nonneg η]
    have hle : ‖(y : ComplexSpace k) - u • (x : ComplexSpace k)‖ ≤ Real.sqrt (4 * η) :=
      Real.le_sqrt_of_sq_le hsq
    have h4 : Real.sqrt (4 * η) = 2 * Real.sqrt η := by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rwa [h4] at hle
  have hc1 : ‖(a₀ : ComplexSpace k) - rho • (a₁ : ComplexSpace k)‖ ≤ 2 * Real.sqrt η :=
    hclose_of_far rho norm_rho a₁ a₀ hfar₁
  have hc2 : ‖(a₀ : ComplexSpace k) - rho ^ 2 • (a₂ : ComplexSpace k)‖ ≤ 2 * Real.sqrt η :=
    hclose_of_far (rho ^ 2) norm_rho_sq a₂ a₀ hfar₂
  have hc12 : ‖(a₁ : ComplexSpace k) - rho • (a₂ : ComplexSpace k)‖ ≤ 4 * Real.sqrt η := by
    have h1' : ‖(a₁ : ComplexSpace k) - rho ^ 2 • (a₀ : ComplexSpace k)‖ ≤ 2 * Real.sqrt η := by
      rwa [← norm_sub_rho_symm]
    have h2' : ‖rho ^ 2 • (a₀ : ComplexSpace k) - rho • (a₂ : ComplexSpace k)‖ ≤ 2 * Real.sqrt η := by
      have heq : rho ^ 2 • (a₀ : ComplexSpace k) - rho • (a₂ : ComplexSpace k) =
          rho ^ 2 • ((a₀ : ComplexSpace k) - rho ^ 2 • (a₂ : ComplexSpace k)) := by
        rw [smul_sub, smul_smul, show rho ^ 2 * rho ^ 2 = rho by
          calc rho ^ 2 * rho ^ 2 = rho ^ 3 * rho := by ring
            _ = rho := by rw [rho_cube, one_mul]]
      rw [heq, norm_smul, norm_rho_sq, one_mul]
      exact hc2
    calc
      ‖(a₁ : ComplexSpace k) - rho • (a₂ : ComplexSpace k)‖
          = ‖((a₁ : ComplexSpace k) - rho ^ 2 • (a₀ : ComplexSpace k)) +
              (rho ^ 2 • (a₀ : ComplexSpace k) - rho • (a₂ : ComplexSpace k))‖ := by abel_nf
      _ ≤ ‖(a₁ : ComplexSpace k) - rho ^ 2 • (a₀ : ComplexSpace k)‖ +
            ‖rho ^ 2 • (a₀ : ComplexSpace k) - rho • (a₂ : ComplexSpace k)‖ := norm_add_le _ _
      _ ≤ 2 * Real.sqrt η + 2 * Real.sqrt η := add_le_add h1' h2'
      _ = 4 * Real.sqrt η := by ring
  refine ⟨a₀, ha₀, a₁, ha₁, a₂, ha₂, ?_, ?_, ?_⟩
  · left; linarith [Real.sqrt_nonneg η]
  · right; linarith [Real.sqrt_nonneg η]
  · left; exact hc12

lemma same_rotation_not_adjacent {k : ℕ} {d : ℝ} (hd : 3 * d < Real.sqrt 3)
    {u v x : ComplexSphere k} {q : Fin 2}
    (hu : ‖(u : ComplexSpace k) - rho ^ (q.1 + 1) • (x : ComplexSpace k)‖ ≤ d)
    (hv : ‖(v : ComplexSpace k) - rho ^ (q.1 + 1) • (x : ComplexSpace k)‖ ≤ d)
    (huv : rotationClose d u v) : False := by
  have huv_close : ‖(u : ComplexSpace k) - (v : ComplexSpace k)‖ ≤ 2 * d := by
    calc
      ‖(u : ComplexSpace k) - (v : ComplexSpace k)‖
          = ‖((u : ComplexSpace k) - rho ^ (q.1 + 1) • (x : ComplexSpace k)) -
              ((v : ComplexSpace k) - rho ^ (q.1 + 1) • (x : ComplexSpace k))‖ := by abel_nf
      _ ≤ ‖(u : ComplexSpace k) - rho ^ (q.1 + 1) • (x : ComplexSpace k)‖ +
            ‖(v : ComplexSpace k) - rho ^ (q.1 + 1) • (x : ComplexSpace k)‖ := norm_sub_le _ _
      _ ≤ d + d := add_le_add hu hv
      _ = 2 * d := by ring
  have hv1 : ‖(v : ComplexSpace k)‖ = 1 := by simpa [ComplexSphere] using v.2
  rcases huv with h | h
  · have h3 : Real.sqrt 3 = ‖(v : ComplexSpace k) - rho • (v : ComplexSpace k)‖ := by
      rw [show (v : ComplexSpace k) - rho • (v : ComplexSpace k) = ((1 : ℂ) - rho) • (v : ComplexSpace k) by
            rw [sub_smul, one_smul], norm_smul, norm_one_sub_rho, hv1, mul_one]
    have htri : ‖(v : ComplexSpace k) - rho • (v : ComplexSpace k)‖ ≤
        ‖(v : ComplexSpace k) - (u : ComplexSpace k)‖ + ‖(u : ComplexSpace k) - rho • (v : ComplexSpace k)‖ := by
      simpa [sub_add_sub_cancel] using norm_add_le ((v : ComplexSpace k) - (u : ComplexSpace k))
        ((u : ComplexSpace k) - rho • (v : ComplexSpace k))
    rw [norm_sub_rev (v : ComplexSpace k) (u : ComplexSpace k)] at htri
    linarith
  · have h3 : Real.sqrt 3 = ‖(v : ComplexSpace k) - rho ^ 2 • (v : ComplexSpace k)‖ := by
      rw [show (v : ComplexSpace k) - rho ^ 2 • (v : ComplexSpace k) = ((1 : ℂ) - rho ^ 2) • (v : ComplexSpace k) by
            rw [sub_smul, one_smul], norm_smul, norm_one_sub_rho_sq, hv1, mul_one]
    have htri : ‖(v : ComplexSpace k) - rho ^ 2 • (v : ComplexSpace k)‖ ≤
        ‖(v : ComplexSpace k) - (u : ComplexSpace k)‖ + ‖(u : ComplexSpace k) - rho ^ 2 • (v : ComplexSpace k)‖ := by
      simpa [sub_add_sub_cancel] using norm_add_le ((v : ComplexSpace k) - (u : ComplexSpace k))
        ((u : ComplexSpace k) - rho ^ 2 • (v : ComplexSpace k))
    rw [norm_sub_rev (v : ComplexSpace k) (u : ComplexSpace k)] at htri
    linarith

lemma no_four_rotationClose {k : ℕ} {d : ℝ} (hd : 3 * d < Real.sqrt 3)
    {x₀ x₁ x₂ x₃ : ComplexSphere k}
    (h10 : rotationClose d x₁ x₀) (h20 : rotationClose d x₂ x₀) (h30 : rotationClose d x₃ x₀)
    (h12 : rotationClose d x₁ x₂) (h13 : rotationClose d x₁ x₃) (h23 : rotationClose d x₂ x₃) :
    False := by
  rcases h10 with h1a | h1b <;> rcases h20 with h2a | h2b <;> rcases h30 with h3a | h3b
  · exact same_rotation_not_adjacent hd (q := 0) (by simpa using h1a) (by simpa using h2a) h12
  · exact same_rotation_not_adjacent hd (q := 0) (by simpa using h1a) (by simpa using h2a) h12
  · exact same_rotation_not_adjacent hd (q := 0) (by simpa using h1a) (by simpa using h3a) h13
  · exact same_rotation_not_adjacent hd (q := 1) (by simpa using h2b) (by simpa using h3b) h23
  · exact same_rotation_not_adjacent hd (q := 0) (by simpa using h2a) (by simpa using h3a) h23
  · exact same_rotation_not_adjacent hd (q := 1) (by simpa using h1b) (by simpa using h3b) h13
  · exact same_rotation_not_adjacent hd (q := 1) (by simpa using h1b) (by simpa using h2b) h12
  · exact same_rotation_not_adjacent hd (q := 1) (by simpa using h1b) (by simpa using h2b) h12

lemma triangle_sum_norm_le {k : ℕ} {d : ℝ} (hd : 3 * d < Real.sqrt 3)
    {x₀ x₁ x₂ : ComplexSphere k}
    (h10 : rotationClose d x₁ x₀) (h20 : rotationClose d x₂ x₀) (h12 : rotationClose d x₁ x₂) :
    ‖(x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)‖ ≤ 2 * d := by
  have hzero : (x₀ : ComplexSpace k) + rho • (x₀ : ComplexSpace k) + rho ^ 2 • (x₀ : ComplexSpace k) = 0 := by
    rw [show (x₀ : ComplexSpace k) + rho • (x₀ : ComplexSpace k) + rho ^ 2 • (x₀ : ComplexSpace k) =
      ((1 : ℂ) + rho + rho ^ 2) • (x₀ : ComplexSpace k) by
        rw [add_smul, add_smul, one_smul], one_add_rho_add_sq, zero_smul]
  rcases h10 with h1a | h1b <;> rcases h20 with h2a | h2b
  · exact False.elim (same_rotation_not_adjacent hd (q := 0) (by simpa using h1a) (by simpa using h2a) h12)
  · calc
      ‖(x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)‖
          = ‖((x₁ : ComplexSpace k) - rho • (x₀ : ComplexSpace k)) +
              ((x₂ : ComplexSpace k) - rho ^ 2 • (x₀ : ComplexSpace k))‖ := by
            congr 1
            have : ((x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)) -
              (((x₁ : ComplexSpace k) - rho • (x₀ : ComplexSpace k)) +
                ((x₂ : ComplexSpace k) - rho ^ 2 • (x₀ : ComplexSpace k))) =
              (x₀ : ComplexSpace k) + rho • (x₀ : ComplexSpace k) + rho ^ 2 • (x₀ : ComplexSpace k) := by abel
            rw [sub_eq_zero.mp (this.trans hzero)]
      _ ≤ ‖(x₁ : ComplexSpace k) - rho • (x₀ : ComplexSpace k)‖ +
            ‖(x₂ : ComplexSpace k) - rho ^ 2 • (x₀ : ComplexSpace k)‖ := norm_add_le _ _
      _ ≤ d + d := add_le_add h1a h2b
      _ = 2 * d := by ring
  · calc
      ‖(x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)‖
          = ‖((x₁ : ComplexSpace k) - rho ^ 2 • (x₀ : ComplexSpace k)) +
              ((x₂ : ComplexSpace k) - rho • (x₀ : ComplexSpace k))‖ := by
            congr 1
            have : ((x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)) -
              (((x₁ : ComplexSpace k) - rho ^ 2 • (x₀ : ComplexSpace k)) +
                ((x₂ : ComplexSpace k) - rho • (x₀ : ComplexSpace k))) =
              (x₀ : ComplexSpace k) + rho • (x₀ : ComplexSpace k) + rho ^ 2 • (x₀ : ComplexSpace k) := by abel
            rw [sub_eq_zero.mp (this.trans hzero)]
      _ ≤ ‖(x₁ : ComplexSpace k) - rho ^ 2 • (x₀ : ComplexSpace k)‖ +
            ‖(x₂ : ComplexSpace k) - rho • (x₀ : ComplexSpace k)‖ := norm_add_le _ _
      _ ≤ d + d := add_le_add h1b h2a
      _ = 2 * d := by ring
  · exact False.elim (same_rotation_not_adjacent hd (q := 1) (by simpa using h1b) (by simpa using h2b) h12)

def inMainSector (a : ℂ) : Prop :=
  0 ≤ a.im ∧ 0 ≤ (-rho ^ 2 * a).im

def awayFromStrips (t : ℝ) (a : ℂ) : Prop :=
  ∀ j : Fin 3, t ≤ |(rho ^ j.1 * a).im|

def crossClose {k : ℕ} (t : ℝ) (x y : ComplexSphere k) : Prop :=
  inMainSector (inner ℂ (x : ComplexSpace k) (y : ComplexSpace k)) ∧
    awayFromStrips t (inner ℂ (x : ComplexSpace k) (y : ComplexSpace k))

lemma exists_rho_inMainSector (a : ℂ) : ∃ q : Fin 3, inMainSector (rho ^ q.1 * a) := by
  have hsum : a.im + (rho * a).im + (rho ^ 2 * a).im = 0 := by
    have : (a + rho * a + rho ^ 2 * a).im = 0 := by
      rw [show a + rho * a + rho ^ 2 * a = (1 + rho + rho ^ 2) * a by ring, one_add_rho_add_sq, zero_mul,
          Complex.zero_im]
    simpa [Complex.add_im] using this
  have h1 : (-rho ^ 2 * (rho * a)).im = -a.im := by
    rw [show -rho ^ 2 * (rho * a) = -(rho ^ 3 * a) by ring, rho_cube, one_mul, Complex.neg_im]
  have h2 : (-rho ^ 2 * (rho ^ 2 * a)).im = -(rho * a).im := by
    rw [show -rho ^ 2 * (rho ^ 2 * a) = -(rho ^ 3 * (rho * a)) by ring, rho_cube, one_mul, Complex.neg_im]
  have h0 : (-rho ^ 2 * a).im = -(rho ^ 2 * a).im := by
    rw [neg_mul, Complex.neg_im]
  by_cases ha : 0 ≤ a.im
  · by_cases hc : (rho ^ 2 * a).im ≤ 0
    · exact ⟨0, by simp only [inMainSector, Fin.val_zero, pow_zero, one_mul, h0]; exact ⟨ha, by linarith⟩⟩
    · have hb : (rho * a).im ≤ 0 := by linarith
      exact ⟨2, by simp only [inMainSector, Fin.val_two, h2]; exact ⟨by linarith, by linarith⟩⟩
  · by_cases hb : 0 ≤ (rho * a).im
    · exact ⟨1, by simp only [inMainSector, Fin.val_one, pow_one, h1]; exact ⟨hb, by linarith⟩⟩
    · have hc : 0 ≤ (rho ^ 2 * a).im := by linarith
      exact ⟨2, by simp only [inMainSector, Fin.val_two, h2]; exact ⟨hc, by linarith⟩⟩

lemma awayFromStrips_rho_pow {t : ℝ} {a : ℂ} (q : Fin 3) (h : awayFromStrips t a) :
    awayFromStrips t (rho ^ q.1 * a) := by
  intro j
  have hmod : rho ^ j.1 * (rho ^ q.1 * a) = rho ^ ((j.1 + q.1) % 3) * a := by
    rw [← mul_assoc, ← pow_add]
    congr 1
    have hdiv : j.1 + q.1 = 3 * ((j.1 + q.1) / 3) + (j.1 + q.1) % 3 := (Nat.div_add_mod _ 3).symm
    conv_lhs => rw [hdiv, pow_add, pow_mul, rho_cube, one_pow, one_mul]
  rw [hmod]
  exact h ⟨(j.1 + q.1) % 3, Nat.mod_lt _ (by norm_num)⟩

lemma no_three_two_K5 {k : ℕ} {d t : ℝ} (hd0 : 0 ≤ d) (hd : 3 * d < Real.sqrt 3) (hdt : d ^ 2 < 3 * t)
    {x₀ x₁ x₂ y₀ y₁ : ComplexSphere k}
    (hx10 : rotationClose d x₁ x₀) (hx20 : rotationClose d x₂ x₀) (hx12 : rotationClose d x₁ x₂)
    (hy01 : rotationClose d y₀ y₁)
    (h00 : crossClose t x₀ y₀) (h01 : crossClose t x₀ y₁)
    (h10 : crossClose t x₁ y₀) (h11 : crossClose t x₁ y₁)
    (h20 : crossClose t x₂ y₀) (h21 : crossClose t x₂ y₁) : False := by
  have haux : ∀ {y y' : ComplexSphere k},
      ‖(y : ComplexSpace k) - rho ^ 2 • (y' : ComplexSpace k)‖ ≤ d →
      crossClose t x₀ y → crossClose t x₀ y' →
      crossClose t x₁ y → crossClose t x₁ y' →
      crossClose t x₂ y → crossClose t x₂ y' → False := by
    intro y y' hyy' c0 c0' c1 c1' c2 c2'
    let e : ComplexSpace k := (y : ComplexSpace k) - rho ^ 2 • (y' : ComplexSpace k)
    have hpt : ∀ {x : ComplexSphere k}, crossClose t x y → crossClose t x y' →
        2 * t ≤ (inner ℂ (x : ComplexSpace k) e).im := by
      intro x hxy hxy'
      have h1 : t ≤ (inner ℂ (x : ComplexSpace k) (y : ComplexSpace k)).im := by
        have habs := hxy.2 0
        simp only [Fin.val_zero, pow_zero, one_mul] at habs
        rwa [abs_of_nonneg hxy.1.1] at habs
      have h2 : t ≤ (-rho ^ 2 * inner ℂ (x : ComplexSpace k) (y' : ComplexSpace k)).im := by
        have habs := hxy'.2 2
        simp only [Fin.val_two] at habs
        have heq : |(rho ^ 2 * inner ℂ (x : ComplexSpace k) (y' : ComplexSpace k)).im| =
            |(-rho ^ 2 * inner ℂ (x : ComplexSpace k) (y' : ComplexSpace k)).im| := by
          rw [neg_mul, Complex.neg_im, abs_neg]
        rw [heq, abs_of_nonneg hxy'.1.2] at habs
        exact habs
      have hlin : inner ℂ (x : ComplexSpace k) e =
          inner ℂ (x : ComplexSpace k) (y : ComplexSpace k) +
            (-rho ^ 2) * inner ℂ (x : ComplexSpace k) (y' : ComplexSpace k) := by
        simp only [e, inner_sub_right, inner_smul_right]; ring
      rw [hlin, Complex.add_im]
      linarith
    have hs : 6 * t ≤ (inner ℂ ((x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)) e).im := by
      simp only [inner_add_left, Complex.add_im]
      linarith [hpt c0 c0', hpt c1 c1', hpt c2 c2']
    have him : (inner ℂ ((x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)) e).im ≤
        ‖inner ℂ ((x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)) e‖ :=
      le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
    have hcs : ‖inner ℂ ((x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)) e‖ ≤
        ‖(x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)‖ * ‖e‖ :=
      norm_inner_le_norm _ _
    have hsum_le := triangle_sum_norm_le hd hx10 hx20 hx12
    have hmul : ‖(x₀ : ComplexSpace k) + (x₁ : ComplexSpace k) + (x₂ : ComplexSpace k)‖ * ‖e‖ ≤ (2 * d) * d :=
      mul_le_mul hsum_le hyy' (norm_nonneg e) (by linarith)
    linarith
  rcases hy01 with h | h
  · rw [norm_sub_rho_symm] at h
    exact haux h h01 h00 h11 h10 h21 h20
  · exact haux h h00 h01 h10 h11 h20 h21

lemma no_two_three_K5 {k : ℕ} {d t : ℝ} (hd0 : 0 ≤ d) (hd : 3 * d < Real.sqrt 3) (hdt : d ^ 2 < 3 * t)
    {x₀ x₁ y₀ y₁ y₂ : ComplexSphere k}
    (hx01 : rotationClose d x₀ x₁)
    (hy10 : rotationClose d y₁ y₀) (hy20 : rotationClose d y₂ y₀) (hy12 : rotationClose d y₁ y₂)
    (h00 : crossClose t x₀ y₀) (h10 : crossClose t x₁ y₀)
    (h01 : crossClose t x₀ y₁) (h11 : crossClose t x₁ y₁)
    (h02 : crossClose t x₀ y₂) (h12 : crossClose t x₁ y₂) : False := by
  have haux : ∀ {x x' : ComplexSphere k},
      ‖(x : ComplexSpace k) - rho • (x' : ComplexSpace k)‖ ≤ d →
      crossClose t x y₀ → crossClose t x' y₀ →
      crossClose t x y₁ → crossClose t x' y₁ →
      crossClose t x y₂ → crossClose t x' y₂ → False := by
    intro x x' hxx' c0 c0' c1 c1' c2 c2'
    let e : ComplexSpace k := (x : ComplexSpace k) - rho • (x' : ComplexSpace k)
    have hpt : ∀ {y : ComplexSphere k}, crossClose t x y → crossClose t x' y →
        2 * t ≤ (inner ℂ e (y : ComplexSpace k)).im := by
      intro y hxy hx'y
      have h1 : t ≤ (inner ℂ (x : ComplexSpace k) (y : ComplexSpace k)).im := by
        have habs := hxy.2 0
        simp only [Fin.val_zero, pow_zero, one_mul] at habs
        rwa [abs_of_nonneg hxy.1.1] at habs
      have h2 : t ≤ (-rho ^ 2 * inner ℂ (x' : ComplexSpace k) (y : ComplexSpace k)).im := by
        have habs := hx'y.2 2
        simp only [Fin.val_two] at habs
        have heq : |(rho ^ 2 * inner ℂ (x' : ComplexSpace k) (y : ComplexSpace k)).im| =
            |(-rho ^ 2 * inner ℂ (x' : ComplexSpace k) (y : ComplexSpace k)).im| := by
          rw [neg_mul, Complex.neg_im, abs_neg]
        rw [heq, abs_of_nonneg hx'y.1.2] at habs
        exact habs
      have hlin : inner ℂ e (y : ComplexSpace k) =
          inner ℂ (x : ComplexSpace k) (y : ComplexSpace k) +
            (-rho ^ 2) * inner ℂ (x' : ComplexSpace k) (y : ComplexSpace k) := by
        simp only [e, inner_sub_left, inner_smul_left, star_rho]; ring
      rw [hlin, Complex.add_im]
      linarith
    have hs : 6 * t ≤ (inner ℂ e ((y₀ : ComplexSpace k) + (y₁ : ComplexSpace k) + (y₂ : ComplexSpace k))).im := by
      simp only [inner_add_right, Complex.add_im]
      linarith [hpt c0 c0', hpt c1 c1', hpt c2 c2']
    have him : (inner ℂ e ((y₀ : ComplexSpace k) + (y₁ : ComplexSpace k) + (y₂ : ComplexSpace k))).im ≤
        ‖inner ℂ e ((y₀ : ComplexSpace k) + (y₁ : ComplexSpace k) + (y₂ : ComplexSpace k))‖ :=
      le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
    have hcs : ‖inner ℂ e ((y₀ : ComplexSpace k) + (y₁ : ComplexSpace k) + (y₂ : ComplexSpace k))‖ ≤
        ‖e‖ * ‖(y₀ : ComplexSpace k) + (y₁ : ComplexSpace k) + (y₂ : ComplexSpace k)‖ :=
      norm_inner_le_norm _ _
    have hsum_le := triangle_sum_norm_le hd hy10 hy20 hy12
    have hmul : ‖e‖ * ‖(y₀ : ComplexSpace k) + (y₁ : ComplexSpace k) + (y₂ : ComplexSpace k)‖ ≤ d * (2 * d) :=
      mul_le_mul hxx' hsum_le (norm_nonneg _) hd0
    linarith
  rcases hx01 with h | h
  · exact haux h h00 h10 h01 h11 h02 h12
  · rw [← norm_sub_rho_symm] at h
    exact haux h h10 h00 h11 h01 h12 h02

def baseGraph {k m : ℕ} (d t : ℝ) (hd : d < Real.sqrt 3)
    (cL cR : Fin m → ComplexSphere k) : SimpleGraph (Fin m ⊕ Fin m) where
  Adj := fun u v => match u, v with
    | Sum.inl i, Sum.inl j => rotationClose d (cL i) (cL j)
    | Sum.inr i, Sum.inr j => rotationClose d (cR i) (cR j)
    | Sum.inl i, Sum.inr j => crossClose t (cL i) (cR j)
    | Sum.inr i, Sum.inl j => crossClose t (cL j) (cR i)
  symm := ⟨fun u v huv => by
    cases u <;> cases v <;> simp only at huv ⊢
    · exact rotationClose_symm huv
    · exact huv
    · exact huv
    · exact rotationClose_symm huv⟩
  loopless := ⟨fun u hu => by
    cases u <;> simp only at hu
    · exact rotationClose_irrefl hd _ hu
    · exact rotationClose_irrefl hd _ hu⟩

lemma baseGraph_cliqueFree_five {k m : ℕ} {d t : ℝ}
    (hd0 : 0 ≤ d) (hd : 3 * d < Real.sqrt 3) (hdt : d ^ 2 < 3 * t)
    (cL cR : Fin m → ComplexSphere k) :
    (baseGraph d t (by linarith) cL cR).CliqueFree 5 := by
  classical
  intro S hS
  rw [SimpleGraph.isNClique_iff] at hS
  rcases hS with ⟨hcliq, hcard⟩
  let SL : Finset (Fin m) := Finset.univ.filter fun i => Sum.inl i ∈ S
  let SR : Finset (Fin m) := Finset.univ.filter fun j => Sum.inr j ∈ S
  have hsum_card : SL.card + SR.card = S.card := by
    have hdisj : Disjoint (SL.map Function.Embedding.inl) (SR.map Function.Embedding.inr) := by
      rw [Finset.disjoint_left]
      intro u huL huR
      rcases Finset.mem_map.mp huL with ⟨_, _, rfl⟩
      rcases Finset.mem_map.mp huR with ⟨_, _, h⟩
      cases h
    have hunion : SL.map Function.Embedding.inl ∪ SR.map Function.Embedding.inr = S := by
      ext u
      cases u with
      | inl i => simp [SL]
      | inr j => simp [SR]
    rw [← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
  have hSL_lt4 : SL.card ≤ 3 := by
    by_contra h4
    have h4' : 4 ≤ SL.card := by omega
    obtain ⟨T, hTSL, hT4⟩ := Finset.exists_subset_card_eq h4'
    rw [Finset.card_eq_succ] at hT4
    obtain ⟨i0, T3, hi0, rfl, hT3⟩ := hT4
    rw [Finset.card_eq_three] at hT3
    obtain ⟨i1, i2, i3, h12, h13, h23, rfl⟩ := hT3
    have hmem : ∀ i ∈ ({i0, i1, i2, i3} : Finset (Fin m)), Sum.inl i ∈ S := fun i hi =>
      (Finset.mem_filter.mp (hTSL (by simpa using hi))).2
    have h01 : i0 ≠ i1 := fun h => hi0 (by simp [h])
    have h02 : i0 ≠ i2 := fun h => hi0 (by simp [h])
    have h03 : i0 ≠ i3 := fun h => hi0 (by simp [h])
    have hadj : ∀ {a b : Fin m}, a ∈ ({i0, i1, i2, i3} : Finset (Fin m)) →
        b ∈ ({i0, i1, i2, i3} : Finset (Fin m)) → a ≠ b → rotationClose d (cL a) (cL b) :=
      fun ha hb hab => hcliq (Finset.mem_coe.mpr (hmem _ ha)) (Finset.mem_coe.mpr (hmem _ hb)) (by simp [hab])
    exact no_four_rotationClose hd
      (hadj (by simp) (by simp) h01.symm) (hadj (by simp) (by simp) h02.symm)
      (hadj (by simp) (by simp) h03.symm) (hadj (by simp) (by simp) h12)
      (hadj (by simp) (by simp) h13) (hadj (by simp) (by simp) h23)
  have hSR_lt4 : SR.card ≤ 3 := by
    by_contra h4
    have h4' : 4 ≤ SR.card := by omega
    obtain ⟨T, hTSR, hT4⟩ := Finset.exists_subset_card_eq h4'
    rw [Finset.card_eq_succ] at hT4
    obtain ⟨i0, T3, hi0, rfl, hT3⟩ := hT4
    rw [Finset.card_eq_three] at hT3
    obtain ⟨i1, i2, i3, h12, h13, h23, rfl⟩ := hT3
    have hmem : ∀ i ∈ ({i0, i1, i2, i3} : Finset (Fin m)), Sum.inr i ∈ S := fun i hi =>
      (Finset.mem_filter.mp (hTSR (by simpa using hi))).2
    have h01 : i0 ≠ i1 := fun h => hi0 (by simp [h])
    have h02 : i0 ≠ i2 := fun h => hi0 (by simp [h])
    have h03 : i0 ≠ i3 := fun h => hi0 (by simp [h])
    have hadj : ∀ {a b : Fin m}, a ∈ ({i0, i1, i2, i3} : Finset (Fin m)) →
        b ∈ ({i0, i1, i2, i3} : Finset (Fin m)) → a ≠ b → rotationClose d (cR a) (cR b) :=
      fun ha hb hab => hcliq (Finset.mem_coe.mpr (hmem _ ha)) (Finset.mem_coe.mpr (hmem _ hb)) (by simp [hab])
    exact no_four_rotationClose hd
      (hadj (by simp) (by simp) h01.symm) (hadj (by simp) (by simp) h02.symm)
      (hadj (by simp) (by simp) h03.symm) (hadj (by simp) (by simp) h12)
      (hadj (by simp) (by simp) h13) (hadj (by simp) (by simp) h23)
  have hcases : (SL.card = 3 ∧ SR.card = 2) ∨ (SL.card = 2 ∧ SR.card = 3) := by omega
  rcases hcases with ⟨hL3, hR2⟩ | ⟨hL2, hR3⟩
  · rw [Finset.card_eq_three] at hL3
    rw [Finset.card_eq_two] at hR2
    obtain ⟨i0, i1, i2, h01, h02, h12, hSL_eq⟩ := hL3
    obtain ⟨j0, j1, hj01, hSR_eq⟩ := hR2
    have hmL : ∀ i ∈ ({i0, i1, i2} : Finset (Fin m)), Sum.inl i ∈ S := fun i hi => by
      have h : i ∈ SL := hSL_eq.symm ▸ hi
      exact (Finset.mem_filter.mp h).2
    have hmR : ∀ j ∈ ({j0, j1} : Finset (Fin m)), Sum.inr j ∈ S := fun j hj => by
      have h : j ∈ SR := hSR_eq.symm ▸ hj
      exact (Finset.mem_filter.mp h).2
    exact no_three_two_K5 hd0 hd hdt
      (hcliq (Finset.mem_coe.mpr (hmL i1 (by simp))) (Finset.mem_coe.mpr (hmL i0 (by simp))) (by simp [h01.symm]))
      (hcliq (Finset.mem_coe.mpr (hmL i2 (by simp))) (Finset.mem_coe.mpr (hmL i0 (by simp))) (by simp [h02.symm]))
      (hcliq (Finset.mem_coe.mpr (hmL i1 (by simp))) (Finset.mem_coe.mpr (hmL i2 (by simp))) (by simp [h12]))
      (hcliq (Finset.mem_coe.mpr (hmR j0 (by simp))) (Finset.mem_coe.mpr (hmR j1 (by simp))) (by simp [hj01]))
      (hcliq (Finset.mem_coe.mpr (hmL i0 (by simp))) (Finset.mem_coe.mpr (hmR j0 (by simp))) (by simp))
      (hcliq (Finset.mem_coe.mpr (hmL i0 (by simp))) (Finset.mem_coe.mpr (hmR j1 (by simp))) (by simp))
      (hcliq (Finset.mem_coe.mpr (hmL i1 (by simp))) (Finset.mem_coe.mpr (hmR j0 (by simp))) (by simp))
      (hcliq (Finset.mem_coe.mpr (hmL i1 (by simp))) (Finset.mem_coe.mpr (hmR j1 (by simp))) (by simp))
      (hcliq (Finset.mem_coe.mpr (hmL i2 (by simp))) (Finset.mem_coe.mpr (hmR j0 (by simp))) (by simp))
      (hcliq (Finset.mem_coe.mpr (hmL i2 (by simp))) (Finset.mem_coe.mpr (hmR j1 (by simp))) (by simp))
  · rw [Finset.card_eq_two] at hL2
    rw [Finset.card_eq_three] at hR3
    obtain ⟨i0, i1, hi01, hSL_eq⟩ := hL2
    obtain ⟨j0, j1, j2, h01, h02, h12, hSR_eq⟩ := hR3
    have hmL : ∀ i ∈ ({i0, i1} : Finset (Fin m)), Sum.inl i ∈ S := fun i hi => by
      have h : i ∈ SL := hSL_eq.symm ▸ hi
      exact (Finset.mem_filter.mp h).2
    have hmR : ∀ j ∈ ({j0, j1, j2} : Finset (Fin m)), Sum.inr j ∈ S := fun j hj => by
      have h : j ∈ SR := hSR_eq.symm ▸ hj
      exact (Finset.mem_filter.mp h).2
    exact no_two_three_K5 hd0 hd hdt
      (hcliq (Finset.mem_coe.mpr (hmL i0 (by simp))) (Finset.mem_coe.mpr (hmL i1 (by simp))) (by simp [hi01]))
      (hcliq (Finset.mem_coe.mpr (hmR j1 (by simp))) (Finset.mem_coe.mpr (hmR j0 (by simp))) (by simp [h01.symm]))
      (hcliq (Finset.mem_coe.mpr (hmR j2 (by simp))) (Finset.mem_coe.mpr (hmR j0 (by simp))) (by simp [h02.symm]))
      (hcliq (Finset.mem_coe.mpr (hmR j1 (by simp))) (Finset.mem_coe.mpr (hmR j2 (by simp))) (by simp [h12]))
      (hcliq (Finset.mem_coe.mpr (hmL i0 (by simp))) (Finset.mem_coe.mpr (hmR j0 (by simp))) (by simp))
      (hcliq (Finset.mem_coe.mpr (hmL i1 (by simp))) (Finset.mem_coe.mpr (hmR j0 (by simp))) (by simp))
      (hcliq (Finset.mem_coe.mpr (hmL i0 (by simp))) (Finset.mem_coe.mpr (hmR j1 (by simp))) (by simp))
      (hcliq (Finset.mem_coe.mpr (hmL i1 (by simp))) (Finset.mem_coe.mpr (hmR j1 (by simp))) (by simp))
      (hcliq (Finset.mem_coe.mpr (hmL i0 (by simp))) (Finset.mem_coe.mpr (hmR j2 (by simp))) (by simp))
      (hcliq (Finset.mem_coe.mpr (hmL i1 (by simp))) (Finset.mem_coe.mpr (hmR j2 (by simp))) (by simp))

lemma complexSphere_strip_le (k : ℕ) (x : ComplexSphere k) (j : Fin 3) {t : ℝ} (ht : 0 < t) :
    complexProb k {y : ComplexSphere k | |(rho ^ j.1 * inner ℂ (x : ComplexSpace k) (y : ComplexSpace k)).im| ≤ t} ≤
      4 * t * Real.sqrt (((k + 1) + (k + 1) : ℕ) : ℝ) := by
  let c : ℂ := Complex.I * starRingEnd ℂ (rho ^ j.1)
  have hc : ‖c‖ = 1 := by simp [c, norm_rho]
  let u : EuclideanSpace ℝ (Fin ((k + 1) + (k + 1))) := complexToReal k (c • (x : ComplexSpace k))
  have hu : ‖u‖ = 1 := by
    simp only [u, LinearIsometryEquiv.norm_map, norm_smul, hc, one_mul]
    simpa [ComplexSphere] using x.2
  have hval : ∀ y : ComplexSphere k,
      (rho ^ j.1 * inner ℂ (x : ComplexSpace k) (y : ComplexSpace k)).im =
        ⟪u, (sphereToReal k y : EuclideanSpace ℝ _)⟫ := by
    intro y
    change (rho ^ j.1 * inner ℂ (x : ComplexSpace k) (y : ComplexSpace k)).im =
      ⟪complexToReal k (c • (x : ComplexSpace k)), complexToReal k (y : ComplexSpace k)⟫
    rw [complexToReal_inner_eq_re, inner_smul_left]
    have hconj : starRingEnd ℂ c = -Complex.I * rho ^ j.1 := by
      simp [c]
    rw [hconj, mul_assoc, neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]
  have himg : sphereToReal k '' {y : ComplexSphere k | |(rho ^ j.1 * inner ℂ (x : ComplexSpace k) (y : ComplexSpace k)).im| ≤ t} =
      {z : RealSphere ((k + 1) + (k + 1)) | |⟪u, (z : EuclideanSpace ℝ _)⟫| ≤ t} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change |⟪u, (sphereToReal k y : EuclideanSpace ℝ _)⟫| ≤ t
      rw [← hval y]
      exact hy
    · intro hz
      refine ⟨(sphereToReal k).symm z, ?_, (sphereToReal k).apply_symm_apply z⟩
      change |(rho ^ j.1 * inner ℂ (x : ComplexSpace k) ((sphereToReal k).symm z : ComplexSpace k)).im| ≤ t
      rw [hval, (sphereToReal k).apply_symm_apply z]
      exact hz
  unfold complexProb
  rw [himg]
  have hm : 1 ≤ k + 1 + k := by omega
  have hstrip := realSphere_strip_le (m := k + 1 + k) hm u hu ht
  have htoReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hstrip
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at htoReal
  exact (div_le_iff₀ (realSphere_univ_pos k)).mpr (by simpa [Nat.add_assoc] using htoReal)

/- ## Part 5: Finite Partition, 3-Fold Averaging, and Blow-Up on `Fin n` -/

lemma exists_sphere_partition (k : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ (m : ℕ) (c : Fin m → ComplexSphere k) (cell : Fin m → Set (ComplexSphere k)),
      0 < m ∧
      (∀ i, MeasurableSet (cell i)) ∧
      (∀ i, ∀ x ∈ cell i, dist x (c i) < r) ∧
      (Set.Pairwise Set.univ fun i j => Disjoint (cell i) (cell j)) ∧
      (⋃ i : Fin m, cell i) = Set.univ := by
  classical
  have hcomp : IsCompact (Set.univ : Set (ComplexSphere k)) := by
    have : IsCompact (Metric.sphere (0 : ComplexSpace k) 1) := isCompact_sphere 0 1
    exact isCompact_iff_isCompact_univ.mp this
  obtain ⟨F, hF⟩ := hcomp.elim_finite_subcover (fun x : ComplexSphere k => Metric.ball x r)
    (fun _ => Metric.isOpen_ball) (fun x _ => Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self hr⟩)
  have hne : F.Nonempty := by
    let p : ComplexSphere k := ⟨EuclideanSpace.single 0 1, by simp [ComplexSphere]⟩
    have hp := hF (Set.mem_univ p)
    rcases Set.mem_iUnion₂.mp hp with ⟨q, hq, _⟩
    exact ⟨q, hq⟩
  let e := F.equivFin
  let m := F.card
  let c : Fin m → ComplexSphere k := fun i => (e.symm i).1
  let cell : Fin m → Set (ComplexSphere k) := fun i =>
    Metric.ball (c i) r \ ⋃ (j : Fin m) (_ : j < i), Metric.ball (c j) r
  refine ⟨m, c, cell, Finset.card_pos.mpr hne, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Metric.isOpen_ball.measurableSet.diff
      (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => Metric.isOpen_ball.measurableSet)
  · intro i x hx
    exact Metric.mem_ball.mp hx.1
  · intro i _ j _ hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hxj.2 (Set.mem_iUnion₂.mpr ⟨i, hlt, hxi.1⟩)
    · exact hxi.2 (Set.mem_iUnion₂.mpr ⟨j, hgt, hxj.1⟩)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hxF : ∃ i : Fin m, x ∈ Metric.ball (c i) r := by
      rcases Set.mem_iUnion₂.mp (hF (Set.mem_univ x)) with ⟨q, hq, hxq⟩
      exact ⟨e ⟨q, hq⟩, by simpa [c] using hxq⟩
    let Sx : Finset (Fin m) := Finset.univ.filter fun i => x ∈ Metric.ball (c i) r
    have hSx : Sx.Nonempty := by
      rcases hxF with ⟨i, hi⟩; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let i0 := Sx.min' hSx
    refine ⟨i0, (Finset.mem_filter.mp (Finset.min'_mem Sx hSx)).2, ?_⟩
    intro hmem
    rcases Set.mem_iUnion₂.mp hmem with ⟨j, hj, hxj⟩
    have hj_mem : j ∈ Sx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩
    exact not_lt_of_ge (Finset.min'_le Sx j hj_mem) hj

set_option maxHeartbeats 1600000 in
open scoped Classical in
theorem lrss_lower_proof (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 5 ∧
        (∀ S : Finset (Fin n),
            G.CliqueFreeOn (S : Set (Fin n)) 3 → (S.card : ℝ) ≤ δ * n) ∧
        (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ G.edgeFinset.card := by
  classical
  set ε₀ : ℝ := min ε (1 / 12)
  set δ₀ : ℝ := min δ (1 / 12)
  have hε₀_pos : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀_le : ε₀ ≤ ε := min_le_left _ _
  have hε₀_le12 : ε₀ ≤ 1 / 12 := min_le_right _ _
  have hδ₀_pos : 0 < δ₀ := lt_min hδ (by norm_num)
  have hδ₀_le : δ₀ ≤ δ := min_le_left _ _
  have hδ₀_le12 : δ₀ ≤ 1 / 12 := min_le_right _ _
  -- Choose dimension k large enough that spherical concentration beats δ₀ / 3
  set B : ℝ := (384 / ε₀) * (Real.log (9 / δ₀) + 1)
  obtain ⟨k, hk⟩ := exists_nat_gt (B ^ 2)
  set h : ℕ := (k + 1) + (k + 1)
  have hh_ge2 : (2 : ℝ) ≤ (h : ℝ) := by
    have : 2 ≤ h := by omega
    exact_mod_cast this
  have hsq_h_pos : 0 < Real.sqrt (h : ℝ) := by positivity
  have hsq_h_gt : B < Real.sqrt (h : ℝ) := by
    have h1 : B ^ 2 < (h : ℝ) := by
      have : (k : ℝ) < (h : ℝ) := by
        have : k < h := by omega
        exact_mod_cast this
      linarith
    by_cases hB : 0 ≤ B
    · rw [← Real.sqrt_sq hB]
      exact Real.sqrt_lt_sqrt (sq_nonneg B) h1
    · linarith
  set t : ℝ := ε₀ / (6 * Real.sqrt (h : ℝ))
  have ht_pos : 0 < t := by positivity
  set d : ℝ := Real.sqrt (2 * t)
  have hd_pos : 0 < d := Real.sqrt_pos.mpr (by linarith)
  have hd_sq : d ^ 2 = 2 * t := Real.sq_sqrt (by linarith)
  have hdt : d ^ 2 < 3 * t := by linarith
  have hd_small : 3 * d < Real.sqrt 3 := by
    have ht_lt : t < 1 / 72 := by
      have hsq2 : (1 : ℝ) < Real.sqrt (h : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
      calc
        t = ε₀ / (6 * Real.sqrt (h : ℝ)) := rfl
        _ ≤ (1 / 12) / (6 * Real.sqrt (h : ℝ)) := div_le_div_of_nonneg_right hε₀_le12 (by positivity)
        _ < (1 / 12) / (6 * 1) := div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)
        _ = 1 / 72 := by norm_num
    have h9d2 : (3 * d) ^ 2 < 3 := by
      rw [mul_pow, hd_sq]; linarith
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 3 * d)]
    exact Real.sqrt_lt_sqrt (by positivity) h9d2
  set η : ℝ := (d / 8) ^ 2
  have hη_pos : 0 < η := by positivity
  have hη_lt1 : η < 1 := by
    have : d < 1 := by
      have : Real.sqrt 3 < 3 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    have : d / 8 < 1 / 8 := by linarith
    dsimp only [η]
    nlinarith
  have h4sqrt_η : 4 * Real.sqrt η = d / 2 := by
    rw [show η = (d / 8) ^ 2 from rfl, Real.sqrt_sq (by positivity)]; ring
  have hconc_bound : 3 * (1 - η / 2) ^ h < δ₀ / 3 := by
    have hexp_step : (1 - η / 2) ^ h ≤ Real.exp (-(h : ℝ) * (η / 2)) := by
      have h1 : 1 - η / 2 ≤ Real.exp (-(η / 2)) := by
        linarith [Real.add_one_le_exp (-(η / 2))]
      calc
        (1 - η / 2) ^ h ≤ (Real.exp (-(η / 2))) ^ h := pow_le_pow_left₀ (by linarith) h1 h
        _ = Real.exp ((h : ℝ) * -(η / 2)) := (Real.exp_nat_mul _ h).symm
        _ = Real.exp (-(h : ℝ) * (η / 2)) := by congr 1; ring
    have hη_val : (h : ℝ) * (η / 2) = ε₀ * Real.sqrt (h : ℝ) / 384 := by
      have h1 : η = t / 32 := by
        simp only [η, div_pow, hd_sq]; ring
      rw [h1]
      have hdiv : (h : ℝ) / Real.sqrt (h : ℝ) = Real.sqrt (h : ℝ) := Real.div_sqrt
      simp only [t]
      calc
        (h : ℝ) * (ε₀ / (6 * Real.sqrt (h : ℝ)) / 32 / 2)
            = ((h : ℝ) / Real.sqrt (h : ℝ)) * (ε₀ / 384) := by ring
        _ = Real.sqrt (h : ℝ) * (ε₀ / 384) := by rw [hdiv]
        _ = ε₀ * Real.sqrt (h : ℝ) / 384 := by ring
    have hlog_lt : Real.log (9 / δ₀) < (h : ℝ) * (η / 2) := by
      rw [hη_val]
      have hmul := mul_lt_mul_of_pos_left hsq_h_gt (by positivity : 0 < ε₀ / 384)
      have hB_eq : (ε₀ / 384) * B = Real.log (9 / δ₀) + 1 := by
        simp only [B]; field_simp [hε₀_pos.ne']
      rw [hB_eq] at hmul
      linarith
    have hexp_lt : Real.exp (-(h : ℝ) * (η / 2)) < δ₀ / 9 := by
      have h1 : 9 / δ₀ < Real.exp ((h : ℝ) * (η / 2)) := by
        rw [← Real.exp_log (by positivity : 0 < 9 / δ₀)]
        exact Real.exp_lt_exp.mpr hlog_lt
      rw [show -(h : ℝ) * (η / 2) = -((h : ℝ) * (η / 2)) by ring, Real.exp_neg]
      have hpos_e : 0 < Real.exp ((h : ℝ) * (η / 2)) := Real.exp_pos _
      rw [inv_lt_iff_one_lt_mul₀' hpos_e]
      have h2 := (div_lt_iff₀ hδ₀_pos).mp h1
      linarith
    linarith
  -- Choose net radius r
  set r : ℝ := min (d / 4) (t / 2)
  have hr_pos : 0 < r := lt_min (by positivity) (by positivity)
  have hr_d : 2 * r ≤ d / 2 := by linarith [min_le_left (d / 4) (t / 2)]
  have hr_t : r ≤ t := by linarith [min_le_right (d / 4) (t / 2)]
  obtain ⟨m, c, cell, hm_pos, hcell_meas, hcell_rad, hcell_disj, hcell_cover⟩ :=
    exists_sphere_partition k hr_pos
  let w : Fin m → ℝ := fun i => complexProb k (cell i)
  have hw_nonneg : ∀ i, 0 ≤ w i := fun i => complexProb_nonneg k (cell i)
  have hw_sum : ∑ i : Fin m, w i = 1 := by
    have h1 := complexProb_biUnion_finset_eq k Finset.univ cell (fun i _ => hcell_meas i)
      (fun i _ j _ hij => hcell_disj (Set.mem_univ i) (Set.mem_univ j) hij)
    simp only [Finset.mem_univ, Set.iUnion_true] at h1
    rw [← h1, hcell_cover, complexProb_univ]
  -- Weight of cells avoiding the strips for each fixed i
  have hrobust_i : ∀ i : Fin m,
      1 - 4 * ε₀ ≤ ∑ j ∈ Finset.univ.filter (fun j => awayFromStrips t (inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k))), w j := by
    intro i
    let good : Finset (Fin m) := Finset.univ.filter fun j =>
      awayFromStrips t (inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k))
    let bad : Finset (Fin m) := Finset.univ \ good
    have hsum_split : ∑ j ∈ good, w j + ∑ j ∈ bad, w j = 1 := by
      rw [← hw_sum]
      exact Finset.sum_add_sum_compl good w
    let stripSet : Fin 3 → Set (ComplexSphere k) := fun q =>
      {y : ComplexSphere k | |(rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (y : ComplexSpace k)).im| ≤ 2 * t}
    have hbad_sub : (⋃ j ∈ bad, cell j) ⊆ ⋃ q : Fin 3, stripSet q := by
      intro y hy
      rcases Set.mem_iUnion₂.mp hy with ⟨j, hj_bad, hy_cell⟩
      have hnot_good : ¬ awayFromStrips t (inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k)) := by
        intro hg
        exact (Finset.mem_sdiff.mp hj_bad).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
      unfold awayFromStrips at hnot_good
      push Not at hnot_good
      rcases hnot_good with ⟨q, hq⟩
      refine Set.mem_iUnion.mpr ⟨q, ?_⟩
      change |(rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (y : ComplexSpace k)).im| ≤ 2 * t
      have hdiff : |(rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (y : ComplexSpace k)).im -
          (rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k)).im| ≤ r := by
        have heq : (rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (y : ComplexSpace k)).im -
            (rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k)).im =
            (rho ^ q.1 * inner ℂ (c i : ComplexSpace k) ((y : ComplexSpace k) - (c j : ComplexSpace k))).im := by
          rw [inner_sub_right, mul_sub, Complex.sub_im]
        rw [heq]
        calc
          |(rho ^ q.1 * inner ℂ (c i : ComplexSpace k) ((y : ComplexSpace k) - (c j : ComplexSpace k))).im|
              ≤ ‖rho ^ q.1 * inner ℂ (c i : ComplexSpace k) ((y : ComplexSpace k) - (c j : ComplexSpace k))‖ :=
                Complex.abs_im_le_norm _
          _ = ‖inner ℂ (c i : ComplexSpace k) ((y : ComplexSpace k) - (c j : ComplexSpace k))‖ := by
                rw [norm_mul, norm_rho_pow, one_mul]
          _ ≤ ‖(c i : ComplexSpace k)‖ * ‖(y : ComplexSpace k) - (c j : ComplexSpace k)‖ :=
                norm_inner_le_norm _ _
          _ = dist y (c j) := by
                have hci : ‖(c i : ComplexSpace k)‖ = 1 := by simpa [ComplexSphere] using (c i).2
                rw [hci, one_mul, Subtype.dist_eq, dist_eq_norm]
          _ ≤ r := (hcell_rad j y hy_cell).le
      have htri : |(rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (y : ComplexSpace k)).im| ≤
          |(rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k)).im| +
          |(rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (y : ComplexSpace k)).im -
            (rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k)).im| := by
        have := abs_add_le (rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k)).im
          ((rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (y : ComplexSpace k)).im -
            (rho ^ q.1 * inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k)).im)
        simpa [add_sub_cancel] using this
      linarith
    have hbad_eq : ∑ j ∈ bad, w j = complexProb k (⋃ j ∈ bad, cell j) :=
      (complexProb_biUnion_finset_eq k bad cell (fun j _ => hcell_meas j)
        (fun a _ b _ hab => hcell_disj (Set.mem_univ a) (Set.mem_univ b) hab)).symm
    have hbad_le : ∑ j ∈ bad, w j ≤ 4 * ε₀ := by
      have h1 : complexProb k (⋃ q : Fin 3, stripSet q) ≤ ∑ q : Fin 3, complexProb k (stripSet q) := by
        simpa using complexProb_biUnion_finset_le k Finset.univ stripSet
      have h2 : ∑ q : Fin 3, complexProb k (stripSet q) ≤ ∑ _q : Fin 3, (4 * (2 * t) * Real.sqrt (h : ℝ)) :=
        Finset.sum_le_sum fun q _ => complexSphere_strip_le k (c i) q (by linarith)
      have h3 : (∑ _q : Fin 3, (4 * (2 * t) * Real.sqrt (h : ℝ))) = 4 * ε₀ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, t]
        field_simp [hsq_h_pos.ne']
        ring
      rw [hbad_eq]
      exact (complexProb_mono k hbad_sub).trans (h1.trans (h2.trans_eq h3))
    linarith
  -- 3-fold rotation averaging to pick q₀ : Fin 3 with cross weight ≥ (1 - 4 * ε₀) / 3
  let rotC : Fin 3 → Fin m → ComplexSphere k := fun q j =>
    ⟨rho ^ q.1 • (c j : ComplexSpace k), by simp [ComplexSphere, norm_smul, norm_rho]⟩
  let cWeight : Fin 3 → ℝ := fun q =>
    ∑ i : Fin m, ∑ j : Fin m, if crossClose t (c i) (rotC q j) then w i * w j else 0
  have hsum_q : 1 - 4 * ε₀ ≤ ∑ q : Fin 3, cWeight q := by
    have hpair : ∀ i j : Fin m,
        awayFromStrips t (inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k)) →
        w i * w j ≤ ∑ q : Fin 3, if crossClose t (c i) (rotC q j) then w i * w j else 0 := by
      intro i j hij
      obtain ⟨q, hq⟩ := exists_rho_inMainSector (inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k))
      have hcr : crossClose t (c i) (rotC q j) := by
        refine ⟨?_, ?_⟩
        · simpa [rotC, inner_smul_right] using hq
        · simpa [rotC, inner_smul_right] using awayFromStrips_rho_pow q hij
      have hle := Finset.single_le_sum
        (f := fun q' : Fin 3 => if crossClose t (c i) (rotC q' j) then w i * w j else 0)
        (fun q' _ => by split_ifs; exact mul_nonneg (hw_nonneg i) (hw_nonneg j); exact le_rfl)
        (Finset.mem_univ q)
      simpa [hcr] using hle
    have hswap : ∑ q : Fin 3, cWeight q =
        ∑ i : Fin m, ∑ j : Fin m, ∑ q : Fin 3, if crossClose t (c i) (rotC q j) then w i * w j else 0 := by
      simp only [cWeight]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    rw [hswap]
    calc
      1 - 4 * ε₀ = ∑ i : Fin m, w i * (1 - 4 * ε₀) := by rw [← Finset.sum_mul, hw_sum, one_mul]
      _ ≤ ∑ i : Fin m, w i * ∑ j ∈ Finset.univ.filter (fun j => awayFromStrips t (inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k))), w j :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrobust_i i) (hw_nonneg i)
      _ = ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => awayFromStrips t (inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k))), w i * w j := by
            apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin m, ∑ j : Fin m, ∑ q : Fin 3, if crossClose t (c i) (rotC q j) then w i * w j else 0 := by
            apply Finset.sum_le_sum; intro i _
            calc
              ∑ j ∈ Finset.univ.filter (fun j => awayFromStrips t (inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k))), w i * w j
                  ≤ ∑ j ∈ Finset.univ.filter (fun j => awayFromStrips t (inner ℂ (c i : ComplexSpace k) (c j : ComplexSpace k))),
                      ∑ q : Fin 3, if crossClose t (c i) (rotC q j) then w i * w j else 0 :=
                    Finset.sum_le_sum fun j hj => hpair i j (Finset.mem_filter.mp hj).2
              _ ≤ ∑ j : Fin m, ∑ q : Fin 3, if crossClose t (c i) (rotC q j) then w i * w j else 0 :=
                    Finset.sum_le_univ_sum_of_nonneg fun j => Finset.sum_nonneg fun q _ => by
                      split_ifs
                      · exact mul_nonneg (hw_nonneg i) (hw_nonneg j)
                      · exact le_rfl
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : Fin 3, (1 - 4 * ε₀) / 3 ≤ cWeight q₀ := by
    by_contra hall
    push Not at hall
    have hlt : ∑ q : Fin 3, cWeight q < ∑ _q : Fin 3, ((1 - 4 * ε₀) / 3) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun q _ => hall q
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hlt
    linarith
  -- Any triangle-free subset of cells in c has total weight ≤ δ₀ / 3
  have htf_weight : ∀ I : Finset (Fin m),
      (∀ i₀ ∈ I, ∀ i₁ ∈ I, ∀ i₂ ∈ I,
        ¬ (rotationClose d (c i₀) (c i₁) ∧ rotationClose d (c i₀) (c i₂) ∧ rotationClose d (c i₁) (c i₂))) →
      ∑ i ∈ I, w i ≤ δ₀ / 3 := by
    intro I hI
    by_contra hgt
    have hgt' := not_le.mp hgt
    let U : Set (ComplexSphere k) := ⋃ i ∈ I, cell i
    have hU_meas : MeasurableSet U := MeasurableSet.biUnion I.countable_toSet fun i _ => hcell_meas i
    have hU_prob : complexProb k U = ∑ i ∈ I, w i :=
      complexProb_biUnion_finset_eq k I cell (fun i _ => hcell_meas i)
        (fun a _ b _ hab => hcell_disj (Set.mem_univ a) (Set.mem_univ b) hab)
    have hU_big : 3 * (1 - η / 2) ^ h < complexProb k U := by linarith
    obtain ⟨a₀, ha₀, a₁, ha₁, a₂, ha₂, h01, h02, h12⟩ :=
      complexSphere_three_close hη_pos hη_lt1 hU_meas hU_big
    rcases Set.mem_iUnion₂.mp ha₀ with ⟨i₀, hi₀, ha₀c⟩
    rcases Set.mem_iUnion₂.mp ha₁ with ⟨i₁, hi₁, ha₁c⟩
    rcases Set.mem_iUnion₂.mp ha₂ with ⟨i₂, hi₂, ha₂c⟩
    have hlift : ∀ {a b : ComplexSphere k} {ia ib : Fin m},
        a ∈ cell ia → b ∈ cell ib → rotationClose (4 * Real.sqrt η) a b →
        rotationClose d (c ia) (c ib) := by
      intro a b ia ib ha hb hab
      have hda : ‖(c ia : ComplexSpace k) - (a : ComplexSpace k)‖ ≤ r := by
        rw [norm_sub_rev]; simpa [Subtype.dist_eq, dist_eq_norm] using (hcell_rad ia a ha).le
      have hdb : ‖(b : ComplexSpace k) - (c ib : ComplexSpace k)‖ ≤ r := by
        simpa [Subtype.dist_eq, dist_eq_norm] using (hcell_rad ib b hb).le
      rcases hab with h | h
      · left
        have ht1 := norm_add_le
          (((c ia : ComplexSpace k) - (a : ComplexSpace k)) + ((a : ComplexSpace k) - rho • (b : ComplexSpace k)))
          (rho • ((b : ComplexSpace k) - (c ib : ComplexSpace k)))
        have ht2 := norm_add_le
          ((c ia : ComplexSpace k) - (a : ComplexSpace k))
          ((a : ComplexSpace k) - rho • (b : ComplexSpace k))
        have heq : (c ia : ComplexSpace k) - rho • (c ib : ComplexSpace k) =
            ((c ia : ComplexSpace k) - (a : ComplexSpace k)) +
              ((a : ComplexSpace k) - rho • (b : ComplexSpace k)) +
              rho • ((b : ComplexSpace k) - (c ib : ComplexSpace k)) := by
          rw [smul_sub]; abel
        rw [heq]
        rw [norm_smul, norm_rho, one_mul] at ht1
        linarith [h4sqrt_η, hr_d]
      · right
        have ht1 := norm_add_le
          (((c ia : ComplexSpace k) - (a : ComplexSpace k)) + ((a : ComplexSpace k) - rho ^ 2 • (b : ComplexSpace k)))
          (rho ^ 2 • ((b : ComplexSpace k) - (c ib : ComplexSpace k)))
        have ht2 := norm_add_le
          ((c ia : ComplexSpace k) - (a : ComplexSpace k))
          ((a : ComplexSpace k) - rho ^ 2 • (b : ComplexSpace k))
        have heq : (c ia : ComplexSpace k) - rho ^ 2 • (c ib : ComplexSpace k) =
            ((c ia : ComplexSpace k) - (a : ComplexSpace k)) +
              ((a : ComplexSpace k) - rho ^ 2 • (b : ComplexSpace k)) +
              rho ^ 2 • ((b : ComplexSpace k) - (c ib : ComplexSpace k)) := by
          rw [smul_sub]; abel
        rw [heq]
        rw [norm_smul, norm_rho_sq, one_mul] at ht1
        linarith [h4sqrt_η, hr_d]
    exact hI i₀ hi₀ i₁ hi₁ i₂ hi₂ ⟨hlift ha₀c ha₁c h01, hlift ha₀c ha₂c h02, hlift ha₁c ha₂c h12⟩
  -- Now construct G on Fin n for all sufficiently large n
  let cL := c
  let cR := rotC q₀
  let baseG := baseGraph d t (by linarith) cL cR
  have hbase5 : baseG.CliqueFree 5 := baseGraph_cliqueFree_five hd_pos.le hd_small hdt cL cR
  rw [eventually_atTop]
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((m : ℝ) / (2 * ε₀ / 3))
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt ((2 * (m : ℝ) + 1) / (2 * δ₀ / 3))
  refine ⟨max N₁ N₂ + 1, fun n hn => ?_⟩
  let a : Fin m → ℕ := fun i => ⌊w i * ((n : ℝ) / 2)⌋₊
  have ha_le : ∀ i, (a i : ℝ) ≤ w i * ((n : ℝ) / 2) := fun i =>
    Nat.floor_le (mul_nonneg (hw_nonneg i) (by positivity))
  have ha_gt : ∀ i, w i * ((n : ℝ) / 2) - 1 < (a i : ℝ) := fun i => by
    have := Nat.lt_floor_add_one (w i * ((n : ℝ) / 2))
    linarith
  let M : ℕ := ∑ i : Fin m, a i
  have h2M_le : 2 * M ≤ n := by
    have hM_real : (M : ℝ) ≤ (n : ℝ) / 2 := by
      calc
        (M : ℝ) = ∑ i : Fin m, (a i : ℝ) := by simp [M]
        _ ≤ ∑ i : Fin m, w i * ((n : ℝ) / 2) := Finset.sum_le_sum fun i _ => ha_le i
        _ = (n : ℝ) / 2 := by rw [← Finset.sum_mul, hw_sum, one_mul]
    have : ((2 * M : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h2M_ge : (n : ℝ) - 2 * (m : ℝ) ≤ (2 * M : ℕ) := by
    have hM_ge : (n : ℝ) / 2 - (m : ℝ) ≤ (M : ℝ) := by
      calc
        (n : ℝ) / 2 - (m : ℝ) = ∑ i : Fin m, (w i * ((n : ℝ) / 2) - 1) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum, one_mul, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ ∑ i : Fin m, (a i : ℝ) := Finset.sum_le_sum fun i _ => (ha_gt i).le
        _ = (M : ℝ) := by simp [M]
    push_cast
    linarith
  let Assigned := (Σ i : Fin m, Fin (a i)) ⊕ (Σ j : Fin m, Fin (a j))
  have hcardA : Fintype.card Assigned = 2 * M := by
    simp only [Assigned, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, M]; ring
  let emb : Assigned ↪ Fin n :=
    (Fintype.equivFin Assigned).toEmbedding.trans (Fin.castLEEmb (hcardA.symm ▸ h2M_le))
  let proj : Assigned → Fin m ⊕ Fin m := fun p => match p with
    | Sum.inl ⟨i, _⟩ => Sum.inl i
    | Sum.inr ⟨j, _⟩ => Sum.inr j
  let G : SimpleGraph (Fin n) :=
    { Adj := fun u v => ∃ p q : Assigned, emb p = u ∧ emb q = v ∧ baseG.Adj (proj p) (proj q)
      symm := ⟨fun u v ⟨p, q, hp, hq, hadj⟩ => ⟨q, p, hq, hp, hadj.symm⟩⟩
      loopless := ⟨fun u ⟨p, q, hp, hq, hadj⟩ => by
        have hpq : p = q := emb.injective (hp.trans hq.symm)
        subst hpq
        exact baseG.loopless.irrefl _ hadj⟩ }
  refine ⟨G, ?_, ?_, ?_⟩
  · -- G.CliqueFree 5
    intro T hT
    rw [SimpleGraph.isNClique_iff] at hT
    rcases hT with ⟨hTcliq, hTcard⟩
    have hin_range : ∀ u ∈ T, ∃ p : Assigned, emb p = u := by
      intro u hu
      have hne : (T.erase u).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hu, hTcard]; norm_num
      obtain ⟨v, hv⟩ := hne
      have huv : G.Adj u v := hTcliq hu (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv).symm
      rcases huv with ⟨p, _, hp, _, _⟩
      exact ⟨p, hp⟩
    let T_base : Finset (Fin m ⊕ Fin m) :=
      Finset.univ.filter fun x => ∃ p : Assigned, proj p = x ∧ emb p ∈ T
    have hcard_base : 5 ≤ T_base.card := by
      choose f hf using fun u (hu : u ∈ T) => hin_range u hu
      let g : {u // u ∈ T} → Fin m ⊕ Fin m := fun u => proj (f u.1 u.2)
      have hg_inj : Function.Injective g := by
        intro u₁ u₂ heq
        by_contra hne
        have hadj : G.Adj u₁.1 u₂.1 := hTcliq u₁.2 u₂.2 (fun h => hne (Subtype.ext h))
        rcases hadj with ⟨p₁, p₂, hp₁, hp₂, hbase_adj⟩
        have h1 : p₁ = f u₁.1 u₁.2 := emb.injective (hp₁.trans (hf u₁.1 u₁.2).symm)
        have h2 : p₂ = f u₂.1 u₂.2 := emb.injective (hp₂.trans (hf u₂.1 u₂.2).symm)
        subst h1; subst h2
        have heq' : proj (f u₁.1 u₁.2) = proj (f u₂.1 u₂.2) := heq
        rw [heq'] at hbase_adj
        exact baseG.loopless.irrefl _ hbase_adj
      have hmaps : ∀ u : {u // u ∈ T}, g u ∈ T_base := fun u =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, f u.1 u.2, rfl, (hf u.1 u.2).symm ▸ u.2⟩
      have hle : (Finset.univ : Finset {u // u ∈ T}).card ≤ T_base.card :=
        Finset.card_le_card_of_injOn g (fun u _ => hmaps u) (fun u₁ _ u₂ _ h => hg_inj h)
      have hcard_univ : (Finset.univ : Finset {u // u ∈ T}).card = 5 := by simp [hTcard]
      exact hcard_univ ▸ hle
    obtain ⟨T5, hT5_sub, hT5_card⟩ := Finset.exists_subset_card_eq hcard_base
    apply hbase5 T5
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, hT5_card⟩
    intro x hx y hy hxy
    obtain ⟨p, rfl, hpT⟩ := (Finset.mem_filter.mp (hT5_sub hx)).2
    obtain ⟨q, rfl, hqT⟩ := (Finset.mem_filter.mp (hT5_sub hy)).2
    have hpq_ne : emb p ≠ emb q := fun h => hxy (congrArg proj (emb.injective h))
    rcases hTcliq hpT hqT hpq_ne with ⟨p', q', hp', hq', hadj⟩
    have h1 : p' = p := emb.injective hp'
    have h2 : q' = q := emb.injective hq'
    subst h1; subst h2
    exact hadj
  · -- Every triangle-free set S has S.card ≤ δ * n
    intro S hS
    let SL := S.filter fun u => ∃ i x, emb (Sum.inl ⟨i, x⟩) = u
    let SR := S.filter fun u => ∃ j y, emb (Sum.inr ⟨j, y⟩) = u
    let Srem := S.filter fun u => u ∉ Set.range emb
    have hS_sub : S ⊆ SL ∪ SR ∪ Srem := by
      intro u hu
      by_cases hmem : u ∈ Set.range emb
      · rcases hmem with ⟨p, rfl⟩
        cases p with
        | inl px => exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, px.1, px.2, rfl⟩))
        | inr py => exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, py.1, py.2, rfl⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, hmem⟩)
    have hS_card_le : S.card ≤ SL.card + SR.card + Srem.card :=
      (Finset.card_le_card hS_sub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    -- Bound Srem.card ≤ n - 2 * M ≤ 2 * m
    have hrem_le : (Srem.card : ℝ) ≤ 2 * (m : ℝ) := by
      let imgA : Finset (Fin n) := Finset.univ.map emb
      have hdisj : Disjoint Srem imgA := by
        rw [Finset.disjoint_left]
        intro u hu himg
        rcases Finset.mem_map.mp himg with ⟨p, _, rfl⟩
        exact (Finset.mem_filter.mp hu).2 ⟨p, rfl⟩
      have hle : Srem.card + imgA.card ≤ n := by
        rw [← Finset.card_union_of_disjoint hdisj]
        exact le_trans (Finset.card_le_univ _) (by simp)
      have himg_card : imgA.card = 2 * M := by rw [Finset.card_map, Finset.card_univ, hcardA]
      have h1 : (Srem.card : ℝ) + ((2 * M : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (himg_card ▸ hle)
      linarith
    -- Bound SL.card ≤ (δ₀ / 6) * n
    let IL : Finset (Fin m) := Finset.univ.filter fun i => ∃ x : Fin (a i), emb (Sum.inl ⟨i, x⟩) ∈ S
    have hIL_tf : ∀ i₀ ∈ IL, ∀ i₁ ∈ IL, ∀ i₂ ∈ IL,
        ¬ (rotationClose d (c i₀) (c i₁) ∧ rotationClose d (c i₀) (c i₂) ∧ rotationClose d (c i₁) (c i₂)) := by
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ ⟨h01, h02, h12⟩
      obtain ⟨x₀, hx₀⟩ := (Finset.mem_filter.mp hi₀).2
      obtain ⟨x₁, hx₁⟩ := (Finset.mem_filter.mp hi₁).2
      obtain ⟨x₂, hx₂⟩ := (Finset.mem_filter.mp hi₂).2
      let u₀ := emb (Sum.inl ⟨i₀, x₀⟩)
      let u₁ := emb (Sum.inl ⟨i₁, x₁⟩)
      let u₂ := emb (Sum.inl ⟨i₂, x₂⟩)
      have ha01 : G.Adj u₀ u₁ := ⟨Sum.inl ⟨i₀, x₀⟩, Sum.inl ⟨i₁, x₁⟩, rfl, rfl, h01⟩
      have ha02 : G.Adj u₀ u₂ := ⟨Sum.inl ⟨i₀, x₀⟩, Sum.inl ⟨i₂, x₂⟩, rfl, rfl, h02⟩
      have ha12 : G.Adj u₁ u₂ := ⟨Sum.inl ⟨i₁, x₁⟩, Sum.inl ⟨i₂, x₂⟩, rfl, rfl, h12⟩
      have hne01 : u₀ ≠ u₁ := G.ne_of_adj ha01
      have hne02 : u₀ ≠ u₂ := G.ne_of_adj ha02
      have hne12 : u₁ ≠ u₂ := G.ne_of_adj ha12
      apply hS (t := ({u₀, u₁, u₂} : Finset (Fin n)))
      · intro u hu
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
        rcases hu with rfl | rfl | rfl <;> assumption
      · rw [SimpleGraph.isNClique_iff]
        refine ⟨?_, Finset.card_eq_three.mpr ⟨u₀, u₁, u₂, hne01, hne02, hne12, rfl⟩⟩
        intro u hu v hv huv
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
        · exact absurd rfl huv
        · exact ha01
        · exact ha02
        · exact ha01.symm
        · exact absurd rfl huv
        · exact ha12
        · exact ha02.symm
        · exact ha12.symm
        · exact absurd rfl huv
    have hSL_le : (SL.card : ℝ) ≤ (δ₀ / 6) * (n : ℝ) := by
      have hsubL : SL ⊆ IL.biUnion fun i => Finset.univ.map ⟨fun x : Fin (a i) => emb (Sum.inl ⟨i, x⟩),
          fun x y h => by
            have := emb.injective h
            cases this; rfl⟩ := by
        intro u hu
        rcases Finset.mem_filter.mp hu with ⟨huS, i, x, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, huS⟩,
          Finset.mem_map.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
      have hcardL : SL.card ≤ ∑ i ∈ IL, a i := by
        calc
          SL.card ≤ (IL.biUnion _).card := Finset.card_le_card hsubL
          _ ≤ ∑ i ∈ IL, (Finset.univ.map _).card := Finset.card_biUnion_le
          _ = ∑ i ∈ IL, a i := by simp
      calc
        (SL.card : ℝ) ≤ ∑ i ∈ IL, (a i : ℝ) := by exact_mod_cast hcardL
        _ ≤ ∑ i ∈ IL, w i * ((n : ℝ) / 2) := Finset.sum_le_sum fun i _ => ha_le i
        _ = (∑ i ∈ IL, w i) * ((n : ℝ) / 2) := (Finset.sum_mul _ _ _).symm
        _ ≤ (δ₀ / 3) * ((n : ℝ) / 2) := mul_le_mul_of_nonneg_right (htf_weight IL hIL_tf) (by positivity)
        _ = (δ₀ / 6) * (n : ℝ) := by ring
    -- Bound SR.card ≤ (δ₀ / 6) * n (cR is just a rho^q₀ rotation of c)
    let IR : Finset (Fin m) := Finset.univ.filter fun j => ∃ y : Fin (a j), emb (Sum.inr ⟨j, y⟩) ∈ S
    have hIR_tf : ∀ j₀ ∈ IR, ∀ j₁ ∈ IR, ∀ j₂ ∈ IR,
        ¬ (rotationClose d (c j₀) (c j₁) ∧ rotationClose d (c j₀) (c j₂) ∧ rotationClose d (c j₁) (c j₂)) := by
      intro j₀ hj₀ j₁ hj₁ j₂ hj₂ ⟨h01, h02, h12⟩
      obtain ⟨y₀, hy₀⟩ := (Finset.mem_filter.mp hj₀).2
      obtain ⟨y₁, hy₁⟩ := (Finset.mem_filter.mp hj₁).2
      obtain ⟨y₂, hy₂⟩ := (Finset.mem_filter.mp hj₂).2
      let u₀ := emb (Sum.inr ⟨j₀, y₀⟩)
      let u₁ := emb (Sum.inr ⟨j₁, y₁⟩)
      let u₂ := emb (Sum.inr ⟨j₂, y₂⟩)
      have ha01 : G.Adj u₀ u₁ := ⟨Sum.inr ⟨j₀, y₀⟩, Sum.inr ⟨j₁, y₁⟩, rfl, rfl, rotationClose_smul_rho_pow q₀ h01⟩
      have ha02 : G.Adj u₀ u₂ := ⟨Sum.inr ⟨j₀, y₀⟩, Sum.inr ⟨j₂, y₂⟩, rfl, rfl, rotationClose_smul_rho_pow q₀ h02⟩
      have ha12 : G.Adj u₁ u₂ := ⟨Sum.inr ⟨j₁, y₁⟩, Sum.inr ⟨j₂, y₂⟩, rfl, rfl, rotationClose_smul_rho_pow q₀ h12⟩
      have hne01 : u₀ ≠ u₁ := G.ne_of_adj ha01
      have hne02 : u₀ ≠ u₂ := G.ne_of_adj ha02
      have hne12 : u₁ ≠ u₂ := G.ne_of_adj ha12
      apply hS (t := ({u₀, u₁, u₂} : Finset (Fin n)))
      · intro u hu
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
        rcases hu with rfl | rfl | rfl <;> assumption
      · rw [SimpleGraph.isNClique_iff]
        refine ⟨?_, Finset.card_eq_three.mpr ⟨u₀, u₁, u₂, hne01, hne02, hne12, rfl⟩⟩
        intro u hu v hv huv
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
        · exact absurd rfl huv
        · exact ha01
        · exact ha02
        · exact ha01.symm
        · exact absurd rfl huv
        · exact ha12
        · exact ha02.symm
        · exact ha12.symm
        · exact absurd rfl huv
    have hSR_le : (SR.card : ℝ) ≤ (δ₀ / 6) * (n : ℝ) := by
      have hsubR : SR ⊆ IR.biUnion fun j => Finset.univ.map ⟨fun y : Fin (a j) => emb (Sum.inr ⟨j, y⟩),
          fun x y h => by
            have := emb.injective h
            cases this; rfl⟩ := by
        intro u hu
        rcases Finset.mem_filter.mp hu with ⟨huS, j, y, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, huS⟩,
          Finset.mem_map.mpr ⟨y, Finset.mem_univ _, rfl⟩⟩
      have hcardR : SR.card ≤ ∑ j ∈ IR, a j := by
        calc
          SR.card ≤ (IR.biUnion _).card := Finset.card_le_card hsubR
          _ ≤ ∑ j ∈ IR, (Finset.univ.map _).card := Finset.card_biUnion_le
          _ = ∑ j ∈ IR, a j := by simp
      calc
        (SR.card : ℝ) ≤ ∑ j ∈ IR, (a j : ℝ) := by exact_mod_cast hcardR
        _ ≤ ∑ j ∈ IR, w j * ((n : ℝ) / 2) := Finset.sum_le_sum fun j _ => ha_le j
        _ = (∑ j ∈ IR, w j) * ((n : ℝ) / 2) := (Finset.sum_mul _ _ _).symm
        _ ≤ (δ₀ / 3) * ((n : ℝ) / 2) := mul_le_mul_of_nonneg_right (htf_weight IR hIR_tf) (by positivity)
        _ = (δ₀ / 6) * (n : ℝ) := by ring
    have hn_big2 : 2 * (m : ℝ) ≤ (2 * δ₀ / 3) * (n : ℝ) := by
      have hn_gt : (2 * (m : ℝ) + 1) / (2 * δ₀ / 3) < (n : ℝ) := by
        have h1 : (N₂ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_right N₁ N₂) (Nat.le_of_succ_le hn)
        linarith
      have hmul := (div_lt_iff₀ (by positivity : 0 < 2 * δ₀ / 3)).mp hn_gt
      linarith
    have hS_real : (S.card : ℝ) ≤ (SL.card : ℝ) + (SR.card : ℝ) + (Srem.card : ℝ) := by
      exact_mod_cast hS_card_le
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hδn : δ₀ * (n : ℝ) ≤ δ * (n : ℝ) := mul_le_mul_of_nonneg_right hδ₀_le hn_nonneg
    linarith
  · -- Edge count: (1 / 12 - ε) * n^2 ≤ G.edgeFinset.card
    let crossPairs : Finset ((Σ i : Fin m, Fin (a i)) × (Σ j : Fin m, Fin (a j))) :=
      Finset.univ.filter fun p => crossClose t (cL p.1.1) (cR p.2.1)
    let edgeOf : ((Σ i : Fin m, Fin (a i)) × (Σ j : Fin m, Fin (a j))) → Sym2 (Fin n) :=
      fun p => s(emb (Sum.inl p.1), emb (Sum.inr p.2))
    have hedge_inj : Function.Injective edgeOf := by
      intro p₁ p₂ h
      have h' : s(emb (Sum.inl p₁.1), emb (Sum.inr p₁.2)) = s(emb (Sum.inl p₂.1), emb (Sum.inr p₂.2)) := h
      rw [Sym2.eq_iff] at h'
      rcases h' with ⟨h1, h2⟩ | ⟨h1, _⟩
      · have hp1 : (Sum.inl p₁.1 : Assigned) = Sum.inl p₂.1 := emb.injective h1
        have hp2 : (Sum.inr p₁.2 : Assigned) = Sum.inr p₂.2 := emb.injective h2
        exact Prod.ext (Sum.inl.inj hp1) (Sum.inr.inj hp2)
      · exact nomatch (emb.injective h1 : (Sum.inl p₁.1 : Assigned) = Sum.inr p₂.2)
    have hcross_eq : (crossPairs.card : ℝ) =
        ∑ i : Fin m, ∑ j : Fin m, if crossClose t (cL i) (cR j) then (a i : ℝ) * (a j : ℝ) else 0 := by
      have hnat : crossPairs.card =
          ∑ i : Fin m, ∑ j : Fin m, if crossClose t (cL i) (cR j) then a i * a j else 0 := by
        simp only [crossPairs, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_sigma]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        split_ifs <;> simp
      rw [hnat]
      push_cast
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> simp
    have hterm_ge : ∀ i j : Fin m,
        (w i * w j) * ((n : ℝ) ^ 2 / 4) - (w i + w j) * ((n : ℝ) / 2) ≤ (a i : ℝ) * (a j : ℝ) := by
      intro i j
      have hi1 := ha_gt i
      have hj1 := ha_gt j
      have ha0 : (0 : ℝ) ≤ (a i : ℝ) := Nat.cast_nonneg _
      have hb0 : (0 : ℝ) ≤ (a j : ℝ) := Nat.cast_nonneg _
      have hab0 : 0 ≤ (a i : ℝ) * (a j : ℝ) := mul_nonneg ha0 hb0
      have hwi : 0 ≤ w i * ((n : ℝ) / 2) := mul_nonneg (hw_nonneg i) (by positivity)
      have hwj : 0 ≤ w j * ((n : ℝ) / 2) := mul_nonneg (hw_nonneg j) (by positivity)
      by_cases hi_ge : 1 ≤ w i * ((n : ℝ) / 2)
      · by_cases hj_ge : 1 ≤ w j * ((n : ℝ) / 2)
        · have hmul : (w i * ((n : ℝ) / 2) - 1) * (w j * ((n : ℝ) / 2) - 1) ≤ (a i : ℝ) * (a j : ℝ) :=
            mul_le_mul hi1.le hj1.le (by linarith) ha0
          have hid : (w i * w j) * ((n : ℝ) ^ 2 / 4) - (w i + w j) * ((n : ℝ) / 2) =
              (w i * ((n : ℝ) / 2) - 1) * (w j * ((n : ℝ) / 2) - 1) - 1 := by ring
          linarith
        · have hneg : (w i * ((n : ℝ) / 2)) * (w j * ((n : ℝ) / 2) - 1) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hwi (by linarith)
          have hid : (w i * w j) * ((n : ℝ) ^ 2 / 4) - (w i + w j) * ((n : ℝ) / 2) =
              (w i * ((n : ℝ) / 2)) * (w j * ((n : ℝ) / 2) - 1) - w j * ((n : ℝ) / 2) := by ring
          linarith
      · have hneg : (w i * ((n : ℝ) / 2) - 1) * (w j * ((n : ℝ) / 2)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hwj
        have hid : (w i * w j) * ((n : ℝ) ^ 2 / 4) - (w i + w j) * ((n : ℝ) / 2) =
            (w i * ((n : ℝ) / 2) - 1) * (w j * ((n : ℝ) / 2)) - w i * ((n : ℝ) / 2) := by ring
        linarith
    have hsum_cross_ge : cWeight q₀ * ((n : ℝ) ^ 2 / 4) - (m : ℝ) * (n : ℝ) ≤ (crossPairs.card : ℝ) := by
      rw [hcross_eq]
      have h1 : ∑ i : Fin m, ∑ j : Fin m,
            (if crossClose t (cL i) (cR j) then (w i * w j) * ((n : ℝ) ^ 2 / 4) else 0) -
          ∑ i : Fin m, ∑ j : Fin m, ((w i + w j) * ((n : ℝ) / 2)) ≤
          ∑ i : Fin m, ∑ j : Fin m, if crossClose t (cL i) (cR j) then (a i : ℝ) * (a j : ℝ) else 0 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum; intro i _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum; intro j _
        split_ifs
        · exact hterm_ge i j
        · have : 0 ≤ (w i + w j) * ((n : ℝ) / 2) := mul_nonneg (add_nonneg (hw_nonneg i) (hw_nonneg j)) (by positivity)
          linarith
      have h2 : ∑ i : Fin m, ∑ j : Fin m,
            (if crossClose t (cL i) (cR j) then (w i * w j) * ((n : ℝ) ^ 2 / 4) else 0) =
          cWeight q₀ * ((n : ℝ) ^ 2 / 4) := by
        simp only [cWeight, cL, cR, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        split_ifs <;> ring
      have h3 : ∑ i : Fin m, ∑ j : Fin m, ((w i + w j) * ((n : ℝ) / 2)) = (m : ℝ) * (n : ℝ) := by
        have hsplit : ∀ i j : Fin m, (w i + w j) * ((n : ℝ) / 2) = w i * ((n : ℝ) / 2) + w j * ((n : ℝ) / 2) :=
          fun i j => add_mul _ _ _
        simp_rw [hsplit, Finset.sum_add_distrib]
        have hleft : ∑ i : Fin m, ∑ _j : Fin m, w i * ((n : ℝ) / 2) = (m : ℝ) * ((n : ℝ) / 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.mul_sum, ← Finset.sum_mul, hw_sum, one_mul]
        have hright : ∑ _i : Fin m, ∑ j : Fin m, w j * ((n : ℝ) / 2) = (m : ℝ) * ((n : ℝ) / 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.sum_mul, hw_sum, one_mul]
        rw [hleft, hright]; ring
      rw [h2, h3] at h1
      exact h1
    have hn_big1 : (m : ℝ) * (n : ℝ) ≤ (2 * ε₀ / 3) * (n : ℝ) ^ 2 := by
      have hn_gt : (m : ℝ) / (2 * ε₀ / 3) < (n : ℝ) := by
        have h1 : (N₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left N₁ N₂) (Nat.le_of_succ_le hn)
        linarith
      have hmul := (div_lt_iff₀ (by positivity : 0 < 2 * ε₀ / 3)).mp hn_gt
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      calc
        (m : ℝ) * (n : ℝ) ≤ ((n : ℝ) * (2 * ε₀ / 3)) * (n : ℝ) := mul_le_mul_of_nonneg_right hmul.le hn0
        _ = (2 * ε₀ / 3) * (n : ℝ) ^ 2 := by ring
    have hq_mul : ((1 - 4 * ε₀) / 3) * ((n : ℝ) ^ 2 / 4) ≤ cWeight q₀ * ((n : ℝ) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right hq₀ (by positivity)
    have hε_mul : (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ (1 / 12 - ε₀) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hε₀_le]) (sq_nonneg (n : ℝ))
    have hq_alg : ((1 - 4 * ε₀) / 3) * ((n : ℝ) ^ 2 / 4) - (2 * ε₀ / 3) * (n : ℝ) ^ 2 =
        (1 / 12 - ε₀) * (n : ℝ) ^ 2 := by ring
    have hstep : (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ (crossPairs.card : ℝ) := by
      calc
        (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ (1 / 12 - ε₀) * (n : ℝ) ^ 2 := hε_mul
        _ = ((1 - 4 * ε₀) / 3) * ((n : ℝ) ^ 2 / 4) - (2 * ε₀ / 3) * (n : ℝ) ^ 2 := hq_alg.symm
        _ ≤ cWeight q₀ * ((n : ℝ) ^ 2 / 4) - (m : ℝ) * (n : ℝ) := sub_le_sub hq_mul hn_big1
        _ ≤ (crossPairs.card : ℝ) := hsum_cross_ge
    refine hstep.trans ?_
    have hcard_le : crossPairs.card ≤ G.edgeFinset.card :=
      Finset.card_le_card_of_injOn edgeOf
        (fun p hp => by
          rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
          exact ⟨Sum.inl p.1, Sum.inr p.2, rfl, rfl, (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2⟩)
        (fun _ _ _ _ h => hedge_inj h)
    rw [Nat.cast_le]
    convert hcard_le

end Erdos533LRSS

theorem OMA.solution : type_of% @Erdos533.erdos_533.variants.lrss_lower :=
  Erdos533LRSS.lrss_lower_proof
