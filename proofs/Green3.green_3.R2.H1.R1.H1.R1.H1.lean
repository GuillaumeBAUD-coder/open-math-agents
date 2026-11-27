import OMAReductions.R_Green3_green_3_R2_H1_R1_H1_R1
import Mathlib

-- Step Green3.green_3.R2.H1.R1.H1.R1.H1: FGY endpoint sumset estimate.
-- Credit: @PetrouilFan (owner of this agent)
--
-- The Section 3 toolbox below is adapted from the authors' Lean formalization
-- https://github.com/leo-franchi/Product-free-subsets-lean (commit 85e0c5b)
-- by Leonardo Franchi, W. T. Gowers and Fredy Yip.

open MeasureTheory Set
open scoped Pointwise
namespace ProductFree
noncomputable section

/-!
# Product-free and sum-free sets: basic definitions

This development formalizes results from the paper on product-free subsets of `(0,1)`.

The headline result (`ProductFree.main1`) states that an open product-free subset of the
open interval `(0,1)` has Lebesgue measure less than `1/3`.

The main tool is `ProductFree.key_lemma`: if `A` is a sum-free set with least element `1`,
then for every `x`, `F(x-1) + F(x) + F(x+1) ≤ x`, where `F(x) = |A ∩ [0,x]|`.
-/

open MeasureTheory Set
open scoped Pointwise



/-- A set of reals is *sum-free* if there are no `x, y ∈ A` with `x + y ∈ A`. -/
def IsSumFree (A : Set ℝ) : Prop := ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → x + y ∉ A

/-- A set of reals is *product-free* if there are no `x, y ∈ E` with `x * y ∈ E`. -/
def IsProductFree (E : Set ℝ) : Prop := ∀ ⦃x⦄, x ∈ E → ∀ ⦃y⦄, y ∈ E → x * y ∉ E

/-- The cumulative measure function `F(x) = |A ∩ [0,x]|`, as a real number. -/
def cum (A : Set ℝ) (x : ℝ) : ℝ := (volume (A ∩ Icc (0:ℝ) x)).toReal

/-- The *positive interval discrepancy* of a set `A`:
`d(A) = sup_I (2|A ∩ I| - |I|)`, the supremum taken over all closed intervals `I = [a,b]`
with `a ≤ b`. -/
def disc (A : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ a b : ℝ, a ≤ b ∧ r = 2 * (volume (A ∩ Icc a b)).toReal - (b - a)}

/-- `d_A(I) = 2|A ∩ I| - |I|` for the interval `I = [a,b]`. -/
def discOn (A : Set ℝ) (a b : ℝ) : ℝ := 2 * (volume (A ∩ Icc a b)).toReal - (b - a)

/-!
# Finite unions of finite closed intervals

Theorem `offdiagonal_main2` is proved by induction on the number of component intervals of a
finite union of finite closed intervals. This file introduces the representation used for that
induction and its basic properties.

`IsIntervalUnion A ivs` says that `A` is the union of the closed intervals in the sorted,
strictly separated list `ivs : List (ℝ × ℝ)`: each pair `p` satisfies `p.1 ≤ p.2`, consecutive
pairs `p, q` satisfy `p.2 < q.1`, and `A = ⋃ p ∈ ivs, [p.1, p.2]`. The length of `ivs` is then
the number of component intervals of `A`.
-/

open MeasureTheory Set
open scoped Pointwise



/-- `A` is the finite union of the closed intervals in the sorted, strictly separated list
`ivs`. The length of `ivs` is the number of component intervals. -/
def IsIntervalUnion (A : Set ℝ) (ivs : List (ℝ × ℝ)) : Prop :=
  (∀ p ∈ ivs, p.1 ≤ p.2) ∧ A = ⋃ p ∈ ivs, Set.Icc p.1 p.2

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-
A finite union of closed intervals is closed.
-/
lemma IsIntervalUnion.isClosed (h : IsIntervalUnion A ivs) : IsClosed A := by
  obtain ⟨h₁, h₂⟩ := h;
  convert isClosed_biUnion_finset fun p hp => isClosed_Icc;
  any_goals exact ivs.toFinset;
  rotate_left;
  exacts [ fun _ => inferInstance, fun p => p.1, fun p => p.2, fun p hp => inferInstance, by simpa [ h₂ ] ]

/-
A finite union of finite closed intervals has finite measure.
-/
lemma IsIntervalUnion.finite (h : IsIntervalUnion A ivs) : volume A ≠ ⊤ := by
  obtain ⟨ h1, h2 ⟩ := h;
  refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ⊆ ⋃ p ∈ ivs.toFinset, Icc p.1 p.2 from _ ) ) _ );
  · aesop;
  · refine' lt_of_le_of_lt ( MeasureTheory.measure_biUnion_finset_le _ _ ) _;
    simp +zetaDelta at *

/-
A finite union of closed intervals with a nonempty list is nonempty.
-/
lemma IsIntervalUnion.nonempty (h : IsIntervalUnion A ivs) (hne : ivs ≠ []) : A.Nonempty := by
  rcases ivs <;> simp_all +decide [ IsIntervalUnion ]

/-
`A` is contained in `Icc (ivs.head).1 (ivs.getLast).2` (the convex hull of its endpoints).
-/
lemma IsIntervalUnion.subset_Icc (h : IsIntervalUnion A ivs) (hne : ivs ≠ []) :
    A ⊆ Icc (sInf A) (sSup A) := by
  have hcpt : IsCompact A := by
    obtain ⟨h₁, h₂⟩ := h
    exact h₂ ▸ Set.Finite.isCompact_biUnion (List.finite_toSet ivs)
      (fun p hp => CompactIccSpace.isCompact_Icc)
  intro x hx
  exact ⟨csInf_le hcpt.bddBelow hx, le_csSup hcpt.bddAbove hx⟩

lemma IsIntervalUnion.isCompact (h : IsIntervalUnion A ivs) : IsCompact A := by
  obtain ⟨h₁, h₂⟩ := h
  exact h₂ ▸ Set.Finite.isCompact_biUnion (List.finite_toSet ivs)
    (fun p hp => CompactIccSpace.isCompact_Icc)

private def clipValid (l r : ℝ) (p : ℝ × ℝ) : Bool :=
  decide (max p.1 l ≤ min p.2 r)

private def clipPair (l r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (max p.1 l, min p.2 r)

private lemma clipPair_valid {l r : ℝ} {p : ℝ × ℝ}
    (hp : clipValid l r p = true) : (clipPair l r p).1 ≤ (clipPair l r p).2 := by
  simp_all +decide [ clipValid, clipPair ]

private lemma clipPair_separated {l r : ℝ} {p q : ℝ × ℝ}
    (hpq : p.2 < q.1) : (clipPair l r p).2 < (clipPair l r q).1 := by
  exact lt_of_le_of_lt ( min_le_left _ _ ) ( lt_of_lt_of_le hpq ( le_max_left _ _ ) )

private lemma interval_inter_eq_clip {l r : ℝ} {p : ℝ × ℝ} :
    Icc p.1 p.2 ∩ Icc l r =
      if clipValid l r p then Icc (clipPair l r p).1 (clipPair l r p).2 else ∅ := by
  unfold clipValid clipPair;
  grind +revert

/-
Intersecting a finite union of closed intervals with a closed interval again gives a
finite union of closed intervals.  The component list may be empty.
-/
lemma IsIntervalUnion.inter_Icc_exists (h : IsIntervalUnion A ivs) (l r : ℝ) :
    ∃ clipped : List (ℝ × ℝ), IsIntervalUnion (A ∩ Icc l r) clipped := by
  refine' ⟨ ( ivs.filter ( clipValid l r ) |> List.map ( clipPair l r ) ), _ ⟩
  constructor
  · intro p hp
    simp only [List.mem_map, List.mem_filter] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact clipPair_valid hq.2
  · ext x
    constructor
    · intro hx
      have hxA : x ∈ A := hx.1
      rw [h.2] at hxA
      simp only [Set.mem_iUnion] at hxA ⊢
      obtain ⟨p, hp_mem, hpI⟩ := hxA
      have hp12 : p.1 ≤ p.2 := le_trans hpI.1 hpI.2
      have hl2 : l ≤ p.2 := le_trans hx.2.1 hpI.2
      have h1r : p.1 ≤ r := le_trans hpI.1 hx.2.2
      have hlr : l ≤ r := le_trans hx.2.1 hx.2.2
      have hv : clipValid l r p = true := by
        simpa [clipValid] using (le_min (max_le hp12 hl2) (max_le h1r hlr) :
          max p.1 l ≤ min p.2 r)
      refine ⟨clipPair l r p, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp_mem, hv⟩, rfl⟩
      · exact ⟨max_le hpI.1 hx.2.1, le_min hpI.2 hx.2.2⟩
    · intro hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨q, hq_mem, hxq⟩ := hx
      simp only [List.mem_map, List.mem_filter] at hq_mem
      obtain ⟨p, ⟨hp_mem, hpv⟩, rfl⟩ := hq_mem
      have hxl : l ≤ x := (le_max_right p.1 l).trans hxq.1
      have hxr : x ≤ r := hxq.2.trans (min_le_right p.2 r)
      have hx1 : p.1 ≤ x := (le_max_left p.1 l).trans hxq.1
      have hx2 : x ≤ p.2 := hxq.2.trans (min_le_left p.2 r)
      have hxA : x ∈ A := by rw [h.2]; exact Set.mem_iUnion₂.mpr ⟨p, hp_mem, ⟨hx1, hx2⟩⟩
      exact ⟨hxA, ⟨hxl, hxr⟩⟩

/-!
# Balanced intervals: the toolbox for Theorem `main2`

This file develops the 'balanced interval' machinery of Section 3 of the paper, the toolbox used
to prove the sumset inequality `offdiagonal_main2` / `main2`.

For a set `A` and an interval `I = [a,b]`, recall `d_A(I) = 2|A ∩ I| - |I|` (`discOn A a b`).

* An interval `[a,b]` is **left balanced** w.r.t. `A` if `d_A([a,c]) ≥ 0` for every `c ∈ [a,b]`.
* It is **right balanced** if `d_A([c,b]) ≥ 0` for every `c ∈ [a,b]`.
* It is **balanced** if it is both.

The main lemmas proved here (all for closed sets of finite measure) are:

* `discOn_add` — additivity of `d_A` over a split of an interval;
* `discOn_neg` — reflection invariance;
* `inter_nonempty_of_measure` — two closed sets whose masses on `[c,b]` sum to at least `|[c,b]|`
  meet inside `[c,b]`;
* `union_left_balanced` (Lemma 'union left balanced');
* `main_step` (Lemma 'main step') and `main_step_sums` (Corollary 'main step sums').
-/

open MeasureTheory Set
open scoped Pointwise



variable {A B : Set ℝ}

/-- `[a,b]` is *left balanced* w.r.t. `A`: `d_A([a,c]) ≥ 0` for every `c ∈ [a,b]`. -/
def IsLeftBalanced (A : Set ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ∀ c, a ≤ c → c ≤ b → 0 ≤ discOn A a c

/-- `[a,b]` is *right balanced* w.r.t. `A`: `d_A([c,b]) ≥ 0` for every `c ∈ [a,b]`. -/
def IsRightBalanced (A : Set ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ∀ c, a ≤ c → c ≤ b → 0 ≤ discOn A c b

/-- `[a,b]` is *balanced* w.r.t. `A` if it is both left and right balanced. -/
def IsBalanced (A : Set ℝ) (a b : ℝ) : Prop :=
  IsLeftBalanced A a b ∧ IsRightBalanced A a b

/-
Additivity of `d_A` over a split: for `a ≤ c ≤ b`, `d_A([a,b]) = d_A([a,c]) + d_A([c,b])`.
-/
lemma discOn_add (hA : MeasurableSet A) {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    discOn A a b = discOn A a c + discOn A c b := by
  have h_volume : (volume (A ∩ Icc a b)).toReal = (volume (A ∩ Icc a c)).toReal + (volume (A ∩ Ioc c b)).toReal := by
    rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_union ];
    · rw [ ← Set.inter_union_distrib_left, Set.Icc_union_Ioc_eq_Icc hac hcb ];
    · grind;
    · exact hA.inter measurableSet_Ioc;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hac, hcb ] ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hac, hcb ] ) );
  unfold discOn; simp_all +decide [ add_sub_add_comm ] ;
  rw [ show ( volume ( A ∩ Ioc c b ) ).toReal = ( volume ( A ∩ Icc c b ) ).toReal from ?_ ] ; ring;
  rw [ show A ∩ Icc c b = ( A ∩ Ioc c b ) ∪ ( A ∩ { c } ) from ?_, MeasureTheory.measure_union ] <;> norm_num [ hA, hac, hcb ];
  · exact Eq.symm ( by rw [ show volume ( A ∩ { c } ) = 0 from by exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( MeasureTheory.measure_singleton c ) ] ; norm_num );
  · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ hx₁.2.1, hx₂.2.symm ] ;
  · grind

/-
The mass `|A ∩ [a,b]|` is monotone in the interval (with `a` fixed on the left).
-/
lemma discOn_le_disc (hfin : volume A ≠ ⊤) {a b : ℝ} (hab : a ≤ b) :
    discOn A a b ≤ disc A := by
  refine' le_csSup _ _;
  · refine' ⟨ 2 * ( volume A |> ENNReal.toReal ), fun r hr => _ ⟩;
    obtain ⟨ a, b, hab, rfl ⟩ := hr;
    exact le_trans ( sub_le_self _ <| sub_nonneg.mpr hab ) ( mul_le_mul_of_nonneg_left ( ENNReal.toReal_mono ( by aesop ) <| MeasureTheory.measure_mono <| Set.inter_subset_left ) zero_le_two );
  · exact ⟨ a, b, hab, rfl ⟩

/-
Reflection: `d_{-A}([-b,-a]) = d_A([a,b])`.
-/
lemma discOn_neg (A : Set ℝ) (a b : ℝ) : discOn (-A) (-b) (-a) = discOn A a b := by
  unfold discOn; by_cases h : 0 ≤ -a - -b <;> simp_all +decide [ neg_sub, sub_eq_add_neg ] ;
  · erw [ ← MeasureTheory.measure_preimage_add_right ] ; norm_num ; ring;
    rw [ show ( fun h => h + b ) ⁻¹' ( -A ) ∩ Icc ( - ( b * 2 ) ) ( -b - a ) = ( fun h => -h - b ) '' ( A ∩ Icc a b ) from ?_ ];
    · -- The volume of a set is invariant under translation and reflection.
      have h_volume_invariant : ∀ (S : Set ℝ), volume (Set.image (fun h => -h - b) S) = volume S := by
        intro S; rw [ show ( fun h => -h - b ) '' S = ( fun h => -h ) '' S - { b } by ext; simp +decide [ sub_eq_add_neg, Set.mem_add ] ; aesop ] ; simp +decide [ sub_eq_add_neg, Set.image_add_right ] ;
      rw [ h_volume_invariant ];
    · norm_num [ Set.ext_iff, Set.mem_preimage, Set.mem_inter_iff, Set.mem_Icc ];
      exact fun x => ⟨ fun hx => ⟨ -b + -x, ⟨ hx.1, by linarith, by linarith ⟩, by ring ⟩, by rintro ⟨ y, ⟨ hy₁, hy₂, hy₃ ⟩, rfl ⟩ ; exact ⟨ by simpa using hy₁, by linarith, by linarith ⟩ ⟩;
  · ring

/-
`disc` is reflection invariant.
-/
lemma disc_neg (A : Set ℝ) : disc (-A) = disc A := by
  have hvol (x y : ℝ) : volume (-A ∩ Icc x y) = volume (A ∩ Icc (-y) (-x)) := by
    have hset : -A ∩ Icc x y = -(A ∩ Icc (-y) (-x)) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_neg, Set.mem_Icc]
      constructor <;> rintro ⟨hzA, hz1, hz2⟩ <;> exact ⟨hzA, by linarith, by linarith⟩
    rw [hset, MeasureTheory.Measure.measure_neg]
  unfold disc
  congr 1
  ext r
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨-b, -a, by linarith, ?_⟩
    rw [hvol a b]
    ring
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨-b, -a, by linarith, ?_⟩
    rw [hvol (-b) (-a)]
    simp only [neg_neg]
    ring

/-
**Intersection lemma.** If `A` and `B` are closed and their masses on `[c,b]` (with `c < b`)
each are at least `|[c,b]|/2`, then `A ∩ B ∩ [c,b]` is nonempty.
-/
lemma inter_nonempty_of_measure (hA : IsClosed A) (hB : IsClosed B) {c b : ℝ} (hcb : c < b)
    (hA' : (b - c) / 2 ≤ (volume (A ∩ Icc c b)).toReal)
    (hB' : (b - c) / 2 ≤ (volume (B ∩ Icc c b)).toReal) :
    (A ∩ B ∩ Icc c b).Nonempty := by
  by_contra h;
  -- Set `A' = A ∩ Icc c b`, `B' = B ∩ Icc c b`. These are closed and disjoint.
  set A' := A ∩ Icc c b
  set B' := B ∩ Icc c b
  have hA' : IsClosed A' := by
    exact hA.inter isClosed_Icc
  have hB' : IsClosed B' := by
    exact hB.inter isClosed_Icc
  have h_disjoint : Disjoint A' B' := by
    exact Set.disjoint_left.mpr fun x hx hx' => h ⟨ x, by aesop ⟩;
  -- Since $A'$ and $B'$ are closed and disjoint, and their union is $Icc c b$, they form a separation of $Icc c b$.
  have h_separation : A' ∪ B' = Icc c b := by
    have h_union : volume (Icc c b \ (A' ∪ B')) = 0 := by
      have h_union : volume (A' ∪ B') = volume A' + volume B' := by
        rw [ MeasureTheory.measure_union ];
        · assumption;
        · exact hB'.measurableSet;
      have h_union : volume (A' ∪ B') ≥ ENNReal.ofReal (b - c) := by
        rw [ h_union, ge_iff_le, ENNReal.ofReal_le_iff_le_toReal ] <;> norm_num;
        · rw [ ENNReal.toReal_add ];
          · linarith;
          · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hcb.le ] ) );
          · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hcb.le ] ) );
        · exact ⟨ ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A' ⊆ Set.Icc c b from fun x hx => hx.2 ) ) ( by simp +decide [ hcb.le ] ) ), ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show B' ⊆ Set.Icc c b from fun x hx => hx.2 ) ) ( by simp +decide [ hcb.le ] ) ) ⟩;
      have h_union : volume (Icc c b \ (A' ∪ B')) = volume (Icc c b) - volume (A' ∪ B') := by
        rw [ MeasureTheory.measure_diff ];
        · grind +splitImp;
        · exact MeasurableSet.nullMeasurableSet ( hA'.measurableSet.union hB'.measurableSet );
        · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.union_subset ( Set.inter_subset_right ) ( Set.inter_subset_right ) ) ) ( by simp +decide [ hcb.le ] ) );
      simp_all +decide [ Real.volume_Icc ];
      exact tsub_eq_zero_of_le ‹_›;
    contrapose! h_union;
    -- Since $A'$ and $B'$ are closed and disjoint, and their union is not $Icc c b$, there exists an open interval $(x, y)$ in $Icc c b$ that is disjoint from $A' \cup B'$.
    obtain ⟨x, y, hxy⟩ : ∃ x y : ℝ, c ≤ x ∧ x < y ∧ y ≤ b ∧ ∀ z ∈ Set.Ioo x y, z ∉ A' ∪ B' := by
      obtain ⟨z, hz⟩ : ∃ z ∈ Set.Icc c b, z ∉ A' ∪ B' := by
        exact Set.exists_of_ssubset ( lt_of_le_of_ne ( Set.union_subset ( Set.inter_subset_right ) ( Set.inter_subset_right ) ) h_union );
      obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ w, abs (w - z) < ε → w ∉ A' ∪ B' := by
        exact Metric.mem_nhds_iff.mp ( IsOpen.mem_nhds ( isOpen_compl_iff.mpr ( hA'.union hB' ) ) hz.2 );
      simp +zetaDelta at *;
      exact ⟨ Max.max c ( z - ε / 2 ), by norm_num, Min.min b ( z + ε / 2 ), by cases max_cases c ( z - ε / 2 ) <;> cases min_cases b ( z + ε / 2 ) <;> linarith, by cases max_cases c ( z - ε / 2 ) <;> cases min_cases b ( z + ε / 2 ) <;> linarith, fun w hw₁ hw₂ => hε.2 w <| abs_lt.2 ⟨ by cases max_cases c ( z - ε / 2 ) <;> linarith, by cases min_cases b ( z + ε / 2 ) <;> linarith ⟩ ⟩;
    exact ne_of_gt ( lt_of_lt_of_le ( by simp [ hxy ] ) ( MeasureTheory.measure_mono ( show Set.Ioo x y ⊆ Icc c b \ ( A' ∪ B' ) from fun z hz => ⟨ ⟨ by linarith [ hz.1 ], by linarith [ hz.2 ] ⟩, hxy.2.2.2 z hz ⟩ ) ) );
  have h_nonempty : A'.Nonempty ∧ B'.Nonempty := by
    constructor <;> contrapose! h <;> simp_all +decide [ Set.not_nonempty_iff_eq_empty ]; all_goals linarith;
  have h_preconnected : IsPreconnected (Icc c b) := by
    exact isPreconnected_Icc;
  specialize h_preconnected ( B'ᶜ ) ( A'ᶜ ) ; simp_all +decide [ Set.subset_def, Set.Nonempty ];
  grind

/-
A convenient reformulation of `inter_nonempty_of_measure` in terms of `discOn`:
if `A`, `B` are closed, `c < b`, both meet `[c,b]`, and `d_A([c,b]) + d_B([c,b]) ≥ 0`, then
`A ∩ B ∩ [c,b] ≠ ∅`. (Both-nonempty is needed: otherwise one set could be all of `[c,b]` and the
other empty.)
-/
lemma inter_nonempty_of_discOn (hA : IsClosed A) (hB : IsClosed B) {c b : ℝ} (hcb : c < b)
    (hAne : (A ∩ Icc c b).Nonempty) (hBne : (B ∩ Icc c b).Nonempty)
    (h : 0 ≤ discOn A c b + discOn B c b) :
    (A ∩ B ∩ Icc c b).Nonempty := by
  contrapose! h;
  -- Since $A$ and $B$ are closed and disjoint, their union $A \cup B$ is also closed.
  have h_union_closed : IsClosed (A ∩ Set.Icc c b ∪ B ∩ Set.Icc c b) := by
    exact IsClosed.union ( hA.inter isClosed_Icc ) ( hB.inter isClosed_Icc );
  -- Since $A \cup B$ is closed and $A \cap B = \emptyset$, it follows that $A \cup B$ is a proper subset of $[c, b]$.
  have h_union_proper : A ∩ Set.Icc c b ∪ B ∩ Set.Icc c b ≠ Set.Icc c b := by
    intro H;
    have h_preconnected : IsPreconnected (Set.Icc c b) := by
      exact isPreconnected_Icc;
    simp_all +decide [ IsPreconnected, Set.ext_iff ];
    specialize h_preconnected ( Set.univ \ B ) ( Set.univ \ A ) ; simp_all +decide [ Set.diff_eq ];
    simp_all +decide [ Set.subset_def, Set.Nonempty ];
    grind;
  -- Since $A \cup B$ is closed and a proper subset of $[c, b]$, there exists an open interval $(x, y) \subset [c, b]$ such that $(x, y) \cap (A \cup B) = \emptyset$.
  obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : ℝ, c ≤ x ∧ x < y ∧ y ≤ b ∧ ∀ z ∈ Set.Ioo x y, z ∉ A ∩ Set.Icc c b ∪ B ∩ Set.Icc c b := by
    obtain ⟨z, hz⟩ : ∃ z ∈ Set.Icc c b, z ∉ A ∩ Set.Icc c b ∪ B ∩ Set.Icc c b := by
      exact Set.exists_of_ssubset ( lt_of_le_of_ne ( Set.union_subset ( Set.inter_subset_right ) ( Set.inter_subset_right ) ) h_union_proper );
    obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ w, abs (w - z) < ε → w ∉ A ∩ Set.Icc c b ∪ B ∩ Set.Icc c b := by
      exact Metric.mem_nhds_iff.mp ( h_union_closed.isOpen_compl.mem_nhds hz.2 );
    simp +zetaDelta at *;
    exact ⟨ Max.max c ( z - ε / 2 ), by norm_num, Min.min b ( z + ε / 2 ), by cases max_cases c ( z - ε / 2 ) <;> cases min_cases b ( z + ε / 2 ) <;> linarith, by cases max_cases c ( z - ε / 2 ) <;> cases min_cases b ( z + ε / 2 ) <;> linarith, fun w hw₁ hw₂ => hε.2 w <| abs_lt.2 ⟨ by cases max_cases c ( z - ε / 2 ) <;> linarith, by cases min_cases b ( z + ε / 2 ) <;> linarith ⟩ ⟩;
  -- Since $(x, y) \cap (A \cup B) = \emptyset$, we have $|A \cap [c, b]| + |B \cap [c, b]| \leq |[c, b] \setminus (x, y)|$.
  have h_measure : (volume (A ∩ Set.Icc c b)).toReal + (volume (B ∩ Set.Icc c b)).toReal ≤ (volume (Set.Icc c b \ Set.Ioo x y)).toReal := by
    rw [ ← ENNReal.toReal_add ];
    · rw [ ← MeasureTheory.measure_union ];
      · gcongr;
        · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show Icc c b \ Ioo x y ⊆ Icc c b from fun z hz => hz.1 ) ) ( by simp +decide [ hcb.le ] ) );
        · grind;
      · exact Set.disjoint_left.mpr fun z hzA hzB => h.subset ⟨ ⟨ hzA.1, hzB.1 ⟩, hzA.2 ⟩;
      · exact hB.measurableSet.inter measurableSet_Icc;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc c b ⊆ Icc c b from fun x hx => hx.2 ) ) ( by simp +decide [ hcb.le ] ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show B ∩ Icc c b ⊆ Icc c b from fun x hx => hx.2 ) ) ( by simp +decide [ hcb.le ] ) );
  -- Since $|[c, b] \setminus (x, y)| = |[c, b]| - |(x, y)|$, we have $|A \cap [c, b]| + |B \cap [c, b]| \leq |[c, b]| - |(x, y)|$.
  have h_measure_simplified : (volume (A ∩ Set.Icc c b)).toReal + (volume (B ∩ Set.Icc c b)).toReal ≤ (b - c) - (y - x) := by
    convert h_measure using 1;
    rw [ MeasureTheory.measure_diff ] <;> norm_num [ hx, hy.le, hxy.1 ];
    · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num [ hcb.le, hy.le ];
      linarith;
    · exact fun z hz => ⟨ by linarith [ hz.1 ], by linarith [ hz.2 ] ⟩;
  unfold discOn; linarith;

/-
**Strict intersection lemma.** If `A`, `B` are measurable, `c < b`, and
`d_A([c,b]) + d_B([c,b]) > 0`, then `A ∩ B ∩ [c,b]` has positive measure, hence is nonempty.
-/
lemma inter_nonempty_of_discOn_pos (hA : MeasurableSet A) (hB : MeasurableSet B) {c b : ℝ}
    (hcb : c < b) (h : 0 < discOn A c b + discOn B c b) :
    (A ∩ B ∩ Icc c b).Nonempty := by
  contrapose! h;
  -- By inclusion–exclusion, we have `volume ((A ∩ Icc c b) ∪ (B ∩ Icc c b)) + volume ((A ∩ Icc c b) ∩ (B ∩ Icc c b)) = volume (A ∩ Icc c b) + volume (B ∩ Icc c b)`.
  have h_incl_excl : (volume (A ∩ Icc c b)).toReal + (volume (B ∩ Icc c b)).toReal ≤ (volume (Icc c b)).toReal := by
    rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_union_add_inter ];
    · gcongr;
      · norm_num;
      · simp_all +decide [ Set.inter_assoc, Set.inter_comm, Set.inter_left_comm ];
        exact le_trans ( MeasureTheory.measure_mono ( show A ∩ Icc c b ∪ B ∩ Icc c b ⊆ Icc c b from fun x hx => by aesop ) ) ( by simp +decide [ hcb.le ] );
    · exact hB.inter measurableSet_Icc;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hcb.le ] ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hcb.le ] ) );
  unfold discOn; norm_num [ hcb.le ] at *; linarith;

/-
**Lemma 'union left balanced'.** If `[a,b]` and `[c,d]` are both left balanced w.r.t. `A` and
they intersect (`c ≤ b`, assuming `a ≤ c`), then their union `[a,d]` is left balanced.
-/
lemma union_left_balanced (hA : MeasurableSet A) {a b c d : ℝ}
    (hI : IsLeftBalanced A a b) (hJ : IsLeftBalanced A c d) (hac : a ≤ c) (hcb : c ≤ b) :
    IsLeftBalanced A a (max b d) := by
  refine' ⟨ by cases max_cases b d <;> linarith, _ ⟩;
  intro x hx₁ hx₂; cases le_total x b <;> cases le_total x d <;> simp_all +decide [ IsLeftBalanced ] ;
  · rw [ show discOn A a x = discOn A a c + discOn A c x from discOn_add hA ( by linarith ) ( by linarith ) ] ; linarith [ hI.2 c ( by linarith ) ( by linarith ), hJ.2 x ( by linarith ) ( by linarith ) ];
  · cases hx₂ <;> simp_all +decide [ le_antisymm ‹_› ‹_› ];
    rw [ show discOn A a d = discOn A a c + discOn A c d by exact discOn_add hA ( by linarith ) ( by linarith ) ] ; linarith [ hI.2 c ( by linarith ) ( by linarith ), hJ.2 d ( by linarith ) ( by linarith ) ]

/-
If `[c,e]` (a left subinterval) attains the discrepancy `disc B` with a strictly positive
value, then its right endpoint `e` belongs to the closed set `B`. (Otherwise a small leftward
shrink would strictly increase the discrepancy, exceeding `disc B`.)
-/
lemma right_endpoint_mem_of_disc (hB : IsClosed B) (hfin : volume B ≠ ⊤) {c e : ℝ}
    (hce : c ≤ e) (hmax : disc B ≤ discOn B c e) (hpos : 0 < discOn B c e) : e ∈ B := by
  contrapose! hmax;
  -- Since $e \notin B$, there exists $\delta > 0$ such that $(e - \delta, e) \cap B = \emptyset$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ y, abs (y - e) < δ → y ∉ B := by
    exact Metric.mem_nhds_iff.mp ( hB.isOpen_compl.mem_nhds hmax );
  -- Choose $\delta'$ such that $0 < \delta' \leq \min(\delta, e - c)$.
  obtain ⟨δ', hδ'_pos, hδ'_le⟩ : ∃ δ' > 0, δ' ≤ min δ (e - c) := by
    exact ⟨ Min.min δ ( e - c ), lt_min hδ_pos ( sub_pos.mpr ( lt_of_le_of_ne hce ( by rintro rfl; exact hpos.ne' ( by unfold discOn; aesop ) ) ) ), le_rfl ⟩;
  -- Then $B \cap [c, e] = B \cap [c, e - \delta']$.
  have h_eq : B ∩ Set.Icc c e = B ∩ Set.Icc c (e - δ') := by
    grind;
  -- Therefore, `discOn B c (e - δ') = discOn B c e + δ'`.
  have h_discOn_eq : discOn B c (e - δ') = discOn B c e + δ' := by
    unfold discOn at *;
    rw [ h_eq ] ; ring;
  linarith [ discOn_le_disc hfin ( show c ≤ e - δ' by linarith [ min_le_right δ ( e - c ) ] ) ]

/-
If `[e,d]` (a right subinterval) attains the discrepancy `disc B` with a strictly positive
value, then its left endpoint `e` belongs to the closed set `B`.
-/
lemma left_endpoint_mem_of_disc (hB : IsClosed B) (hfin : volume B ≠ ⊤) {e d : ℝ}
    (hed : e ≤ d) (hmax : disc B ≤ discOn B e d) (hpos : 0 < discOn B e d) : e ∈ B := by
  revert e d;
  intro e d hed hmax hpos
  by_contra h_contra
  have h_not_in_B : e ∉ B := by
    assumption;
  -- By definition of `discOn`, we know that `discOn (-B) (-d) (-e) = discOn B e d`.
  have h_discOn_symm : discOn (-B) (-d) (-e) = discOn B e d := by
    convert discOn_neg B e d using 1;
  convert right_endpoint_mem_of_disc ( show IsClosed ( -B ) from hB.neg ) ?_ ( show -d ≤ -e by linarith ) ?_ ?_ using 1 <;> norm_num [ h_discOn_symm ];
  · assumption;
  · exact hfin;
  · rw [ disc_neg ] ; linarith;
  · linarith

/-
Difference-set membership from mass bounds (each `≥ half`). If `A`, `B` are closed, `p < q`,
and `A` has mass `≥ (q-p)/2` on `[p-x, q-x]` while `B` has mass `≥ (q-p)/2` on `[p, q]`, then
`x ∈ (B ∩ [p,q]) - (A ∩ [p-x, q-x])`. (Proof: translate `A` by `x`; the two translated masses
sit on `[p,q]` and meet by `inter_nonempty_of_measure`.)
-/
lemma diff_helper_measure (hA : IsClosed A) (hB : IsClosed B) {p q x : ℝ} (hpq : p < q)
    (hAm : (q - p) / 2 ≤ (volume (A ∩ Icc (p - x) (q - x))).toReal)
    (hBm : (q - p) / 2 ≤ (volume (B ∩ Icc p q)).toReal) :
    x ∈ (B ∩ Icc p q) - (A ∩ Icc (p - x) (q - x)) := by
  obtain ⟨ w, hw ⟩ := inter_nonempty_of_measure ( show IsClosed ( ( fun t => t + x ) '' A ) from by
                                                    convert hA.preimage ( show Continuous fun t => t - x from continuous_id.sub continuous_const ) using 1 ; ext ; aesop ) hB hpq ( show ( q - p ) / 2 ≤ ( MeasureTheory.volume ( ( fun t => t + x ) '' A ∩ Icc p q ) |> ENNReal.toReal ) from by
                                                                                                                      convert hAm using 1;
                                                                                                                      rw [ show ( fun t => t + x ) '' A ∩ Icc p q = ( fun t => t + x ) '' ( A ∩ Icc ( p - x ) ( q - x ) ) from ?_ ];
                                                                                                                      · rw [ Set.image_add_right ];
                                                                                                                        rw [ MeasureTheory.measure_preimage_add_right ];
                                                                                                                      · ext ; aesop ) hBm;
  rcases hw with ⟨ ⟨ ⟨ y, hy, rfl ⟩, hy' ⟩, hy'' ⟩ ; exact ⟨ _, ⟨ hy', hy'' ⟩, _, ⟨ hy, ⟨ by linarith [ hy''.1 ], by linarith [ hy''.2 ] ⟩ ⟩, by ring ⟩ ;

/-
Difference-set membership from a discrepancy-sum bound (both sets nonempty). If `A`, `B` are
closed, `p < q`, both `A ∩ [p-x, q-x]` and `B ∩ [p, q]` are nonempty, and
`d_A([p-x,q-x]) + d_B([p,q]) ≥ 0`, then `x ∈ (B ∩ [p,q]) - (A ∩ [p-x, q-x])`.
-/
lemma diff_helper_discOn (hA : IsClosed A) (hB : IsClosed B) {p q x : ℝ} (hpq : p < q)
    (hAne : (A ∩ Icc (p - x) (q - x)).Nonempty) (hBne : (B ∩ Icc p q).Nonempty)
    (h : 0 ≤ discOn A (p - x) (q - x) + discOn B p q) :
    x ∈ (B ∩ Icc p q) - (A ∩ Icc (p - x) (q - x)) := by
  -- Let `A' := (fun t => t + x) '' A`, closed (translation homeomorphism).
  set A' : Set ℝ := (fun t => t + x) '' A;
  -- Then `0 ≤ discOn A' p q + discOn B p q` from `h`, and both `A' ∩ Icc p q`, `B ∩ Icc p q` are nonempty.
  have h_disc : 0 ≤ discOn A' p q + discOn B p q := by
    refine le_trans h ?_;
    unfold discOn A'; simp +decide [ *, Set.image_add_right ] ;
    rw [ show ( fun t => t + -x ) ⁻¹' A ∩ Icc p q = ( fun t => t + -x ) ⁻¹' ( A ∩ Icc ( p - x ) ( q - x ) ) by ext; aesop ] ; rw [ MeasureTheory.measure_preimage_add_right ] ;
  have hA'_nonempty : (A' ∩ Icc p q).Nonempty := by
    exact hAne.elim fun y hy => ⟨ y + x, Set.mem_image_of_mem _ hy.1, by constructor <;> linarith [ hy.2.1, hy.2.2 ] ⟩
  have hB_nonempty : (B ∩ Icc p q).Nonempty := by
    assumption;
  obtain ⟨ w, hw₁, hw₂ ⟩ := inter_nonempty_of_discOn ( show IsClosed A' from by
                                                        convert hA.preimage ( show Continuous fun t => t - x from continuous_id.sub continuous_const ) using 1 ; aesop ) hB hpq hA'_nonempty hB_nonempty h_disc;
  simp +zetaDelta at *;
  exact ⟨ w, ⟨ hw₁.2, hw₂ ⟩, w + -x, ⟨ hw₁.1, by constructor <;> linarith ⟩, by ring ⟩

/-
Difference-set membership from a *strict* discrepancy-sum bound (no nonemptiness needed).
If `A`, `B` are measurable, `p < q`, and `d_A([p-x,q-x]) + d_B([p,q]) > 0`, then
`x ∈ (B ∩ [p,q]) - (A ∩ [p-x, q-x])`.
-/
lemma diff_helper_pos (hA : MeasurableSet A) (hB : MeasurableSet B) {p q x : ℝ} (hpq : p < q)
    (h : 0 < discOn A (p - x) (q - x) + discOn B p q) :
    x ∈ (B ∩ Icc p q) - (A ∩ Icc (p - x) (q - x)) := by
  have := inter_nonempty_of_discOn_pos (by
  convert hA.preimage ( show Measurable ( fun t => t - x ) from measurable_id.sub measurable_const ) using 1 ; ext ; aesop : MeasurableSet ((fun t => t + x) '' A)) hB hpq (by
  unfold discOn at *;
  rw [ show ( fun t => t + x ) '' A ∩ Icc p q = ( fun t => t + x ) '' ( A ∩ Icc ( p - x ) ( q - x ) ) from ?_ ];
  · rw [ Set.image_add_right ];
    rw [ MeasureTheory.measure_preimage_add_right ] ; linarith;
  · ext ; aesop : 0 < discOn ((fun t => t + x) '' A) p q + discOn B p q);
  exact this.imp fun w hw => by aesop;

/-- The mass of `A` on `[a,b]` is at most the length `b - a` (for `a ≤ b`). -/
lemma mass_inter_Icc_le (A : Set ℝ) {a b : ℝ} (hab : a ≤ b) :
    (volume (A ∩ Icc a b)).toReal ≤ b - a := by
  refine le_trans (ENNReal.toReal_mono ?_ (measure_mono Set.inter_subset_right)) ?_
  · simp [Real.volume_Icc]
  · simp [Real.volume_Icc, hab]

/-- `discOn A a b ≤ b - a` for `a ≤ b`. -/
lemma discOn_le_sub (A : Set ℝ) {a b : ℝ} (hab : a ≤ b) : discOn A a b ≤ b - a := by
  have := mass_inter_Icc_le A hab
  unfold discOn; linarith

/-- Shifted form of `diff_helper_measure`: `A`-interval `[a',b']`, `B`-interval `[a'+x,b'+x]`. -/
lemma diff_mem_measure (hA : IsClosed A) (hB : IsClosed B) {a' b' x : ℝ} (hab' : a' < b')
    (hAm : (b' - a') / 2 ≤ (volume (A ∩ Icc a' b')).toReal)
    (hBm : (b' - a') / 2 ≤ (volume (B ∩ Icc (a' + x) (b' + x))).toReal) :
    x ∈ (B ∩ Icc (a' + x) (b' + x)) - (A ∩ Icc a' b') := by
  have h := diff_helper_measure (p := a' + x) (q := b' + x) (x := x) hA hB (by linarith)
    (by simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using hAm)
    (by simpa using hBm)
  simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using h

/-- Shifted form of `diff_helper_discOn`. -/
lemma diff_mem_discOn (hA : IsClosed A) (hB : IsClosed B) {a' b' x : ℝ} (hab' : a' < b')
    (hAne : (A ∩ Icc a' b').Nonempty) (hBne : (B ∩ Icc (a' + x) (b' + x)).Nonempty)
    (h : 0 ≤ discOn A a' b' + discOn B (a' + x) (b' + x)) :
    x ∈ (B ∩ Icc (a' + x) (b' + x)) - (A ∩ Icc a' b') := by
  have h2 := diff_helper_discOn (p := a' + x) (q := b' + x) (x := x) hA hB (by linarith)
    (by simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using hAne)
    hBne
    (by simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using h)
  simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using h2

/-- Shifted form of `diff_helper_pos`. -/
lemma diff_mem_pos (hA : IsClosed A) (hB : IsClosed B) {a' b' x : ℝ} (hab' : a' < b')
    (h : 0 < discOn A a' b' + discOn B (a' + x) (b' + x)) :
    x ∈ (B ∩ Icc (a' + x) (b' + x)) - (A ∩ Icc a' b') := by
  have h2 := diff_helper_pos (p := a' + x) (q := b' + x) (x := x) hA.measurableSet hB.measurableSet
    (by linarith)
    (by simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using h)
  simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using h2

/-- Pointwise core of `main_step`: for `x` in the *open* interval, `x` lies in the difference set.
This is the four-case analysis; `main_step` follows by a closure argument. -/
lemma main_step_mem (hA : IsClosed A) (hB : IsClosed B) (hAfin : volume A ≠ ⊤)
    (hBfin : volume B ≠ ⊤) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hI : IsRightBalanced A a b) (hJ : IsLeftBalanced B c d)
    (hdisc : disc B ≤ discOn A a b) {x : ℝ}
    (hx1 : c - b < x) (hx2 : x < c - b + 2 * (volume (B ∩ Icc c d)).toReal) :
    x ∈ (B ∩ Icc c d) - (A ∩ Icc a b) := by
  have hAab_le : discOn A a b ≤ b - a := discOn_le_sub A hab.le
  have hBcd_le : discOn B c d ≤ disc B := discOn_le_disc hBfin hcd.le
  have hBcd_gt : x - d + b < discOn B c d := by unfold discOn; linarith
  have hxda : x < d - a := by unfold discOn at hBcd_le; linarith
  rcases le_or_gt x (d - b) with hdb | hdb
  · rcases le_or_gt x (c - a) with hca | hca
    · -- CASE 1
      have hA0 : 0 ≤ discOn A (c - x) b := hI.2 _ (by linarith) (by linarith)
      have hB0 : 0 ≤ discOn B c (b + x) := hJ.2 _ (by linarith) (by linarith)
      have hmem := diff_mem_measure (a' := c - x) (b' := b) (x := x) hA hB (by linarith)
        (by unfold discOn at hA0; linarith)
        (by
          have hcx : c - x + x = c := by ring
          rw [hcx]; unfold discOn at hB0; linarith)
      have hcx : c - x + x = c := by ring
      rw [hcx] at hmem
      exact Set.sub_subset_sub
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (le_refl c) (by linarith)))
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (by linarith) (le_refl b))) hmem
    · -- CASE 2
      have hA0 : 0 ≤ discOn A a b := hI.2 _ (le_refl a) hab.le
      have hApos : 0 < (volume (A ∩ Icc a b)).toReal := by unfold discOn at hA0; linarith
      have hAne : (A ∩ Icc a b).Nonempty := by
        rcases Set.eq_empty_or_nonempty (A ∩ Icc a b) with h | h
        · rw [h] at hApos; simp at hApos
        · exact h
      have hadd : discOn B c (b + x) = discOn B c (a + x) + discOn B (a + x) (b + x) :=
        discOn_add hB.measurableSet (by linarith) (by linarith)
      have hBb : 0 ≤ discOn B c (b + x) := hJ.2 _ (by linarith) (by linarith)
      have hcax_le : discOn B c (a + x) ≤ disc B := discOn_le_disc hBfin (by linarith)
      have hBne : (B ∩ Icc (a + x) (b + x)).Nonempty := by
        rcases Set.eq_empty_or_nonempty (B ∩ Icc (a + x) (b + x)) with hEmp | h
        · exfalso
          have hde : discOn B (a + x) (b + x) = -(b - a) := by
            unfold discOn; rw [hEmp]; simp
          have hcax_eq : discOn B c (a + x) = b - a := by linarith
          have hmemB : a + x ∈ B :=
            right_endpoint_mem_of_disc (c := c) (e := a + x) hB hBfin
              (by linarith) (by linarith) (by linarith)
          exact absurd (⟨a + x, hmemB, by constructor <;> linarith⟩ :
              (B ∩ Icc (a + x) (b + x)).Nonempty)
            (Set.not_nonempty_iff_eq_empty.mpr hEmp)
        · exact h
      have hsum : 0 ≤ discOn A a b + discOn B (a + x) (b + x) := by linarith
      have hmem := diff_mem_discOn (a' := a) (b' := b) (x := x) hA hB hab hAne hBne hsum
      exact Set.sub_subset_sub
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (by linarith) (by linarith)))
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (le_refl a) (le_refl b))) hmem
  · rcases le_or_gt x (c - a) with hca | hca
    · -- CASE 3a
      have hA0 : 0 ≤ discOn A (c - x) b := hI.2 _ (by linarith) (by linarith)
      have hadd : discOn A (c - x) b = discOn A (c - x) (d - x) + discOn A (d - x) b :=
        discOn_add hA.measurableSet (by linarith) (by linarith)
      have hAdxb : discOn A (d - x) b ≤ b - (d - x) := discOn_le_sub A (by linarith)
      have hpos : 0 < discOn A (c - x) (d - x) + discOn B c d := by linarith
      have hmem := diff_mem_pos (a' := c - x) (b' := d - x) (x := x) hA hB (by linarith)
        (by
          have h1 : c - x + x = c := by ring
          have h2 : d - x + x = d := by ring
          rw [h1, h2]; exact hpos)
      have h1 : c - x + x = c := by ring
      have h2 : d - x + x = d := by ring
      rw [h1, h2] at hmem
      exact Set.sub_subset_sub
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (le_refl c) (le_refl d)))
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (by linarith) (by linarith))) hmem
    · -- CASE 3b
      have hadd_A : discOn A a b = discOn A a (d - x) + discOn A (d - x) b :=
        discOn_add hA.measurableSet (by linarith) (by linarith)
      have hAdxb : discOn A (d - x) b ≤ b - (d - x) := discOn_le_sub A (by linarith)
      have hadd_B : discOn B c d = discOn B c (a + x) + discOn B (a + x) d :=
        discOn_add hB.measurableSet (by linarith) (by linarith)
      have hcax_le : discOn B c (a + x) ≤ disc B := discOn_le_disc hBfin (by linarith)
      have hpos : 0 < discOn A a (d - x) + discOn B (a + x) d := by linarith
      have hmem := diff_mem_pos (a' := a) (b' := d - x) (x := x) hA hB (by linarith)
        (by
          have h2 : d - x + x = d := by ring
          rw [h2]; exact hpos)
      have h2 : d - x + x = d := by ring
      rw [h2] at hmem
      exact Set.sub_subset_sub
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (by linarith) (le_refl d)))
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (le_refl a) (by linarith))) hmem

/-
**Lemma 'main step'.** Let `I = [a,b]` be right balanced w.r.t. `A` and `J = [c,d]` left
balanced w.r.t. `B`, with `d_A(I) ≥ d(B)` and both intervals nondegenerate. Then
`(B ∩ J) - (A ∩ I) ⊇ [c-b, c-b + 2|B ∩ J|]`.
-/
lemma main_step (hA : IsClosed A) (hB : IsClosed B) (hAfin : volume A ≠ ⊤)
    (hBfin : volume B ≠ ⊤) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hI : IsRightBalanced A a b) (hJ : IsLeftBalanced B c d)
    (hdisc : disc B ≤ discOn A a b) :
    Icc (c - b) (c - b + 2 * (volume (B ∩ Icc c d)).toReal) ⊆
      (B ∩ Icc c d) - (A ∩ Icc a b) := by
  -- By `main_step_mem`, `Set.Ioo (c-b) (c-b+2*m) ⊆ D`.
  have h_open : Set.Ioo (c - b) (c - b + 2 * (volume (B ∩ Icc c d)).toReal) ⊆ (B ∩ Icc c d) - (A ∩ Icc a b) := by
    intro x hx; exact main_step_mem hA hB hAfin hBfin hab hcd hI hJ hdisc hx.1 hx.2;
  -- Therefore `closure (Set.Ioo (c-b) (c-b+2*m)) ⊆ D` by `closure_minimal` (D closed).
  have h_closure : closure (Set.Ioo (c - b) (c - b + 2 * (volume (B ∩ Icc c d)).toReal)) ⊆ (B ∩ Icc c d) - (A ∩ Icc a b) := by
    refine' closure_minimal h_open _;
    have h_compact : IsCompact (B ∩ Icc c d) ∧ IsCompact (A ∩ Icc a b) := by
      exact ⟨ CompactIccSpace.isCompact_Icc.of_isClosed_subset ( hB.inter isClosed_Icc ) fun x hx => hx.2, CompactIccSpace.isCompact_Icc.of_isClosed_subset ( hA.inter isClosed_Icc ) fun x hx => hx.2 ⟩;
    have h_compact_diff : IsCompact ((B ∩ Icc c d) - (A ∩ Icc a b)) := by
      convert h_compact.1.add h_compact.2.neg using 1 ; ext ; simp +decide [ sub_eq_add_neg ];
    exact h_compact_diff.isClosed;
  refine' Set.Subset.trans _ h_closure;
  rw [ closure_Ioo ];
  have := hJ.2 d ( by linarith ) ( by linarith ) ; norm_num [ discOn ] at this ; linarith

/-
**Corollary 'main step sums', first part.** If `I = [a,b]` is left balanced w.r.t. `A`,
`J = [c,d]` left balanced w.r.t. `B`, both nondegenerate, and `d_A(I) ≥ d(B)`, then
`(A ∩ I) + (B ∩ J) ⊇ [a+c, a+c + 2|B ∩ J|]`.
-/
lemma main_step_sums_left (hA : IsClosed A) (hB : IsClosed B) (hAfin : volume A ≠ ⊤)
    (hBfin : volume B ≠ ⊤) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hI : IsLeftBalanced A a b) (hJ : IsLeftBalanced B c d)
    (hdisc : disc B ≤ discOn A a b) :
    Icc (a + c) (a + c + 2 * (volume (B ∩ Icc c d)).toReal) ⊆
      (A ∩ Icc a b) + (B ∩ Icc c d) := by
  -- By Lemma `main_step`, we have
  have h_main_step : Icc (c - (-a)) (c - (-a) + 2 * (volume (B ∩ Icc c d)).toReal) ⊆ (B ∩ Icc c d) - ((-A) ∩ Icc (-b) (-a)) := by
    apply main_step;
    any_goals assumption;
    · exact hA.neg;
    · aesop;
    · linarith;
    · constructor;
      · linarith;
      · intro c hc₁ hc₂;
        convert hI.2 ( -c ) ( by linarith ) ( by linarith ) using 1;
        convert discOn_neg A a ( -c ) using 1 ; ring;
    · rwa [ discOn_neg ];
  convert h_main_step using 1 ; ring;
  ext ; simp +decide [ Set.mem_add, Set.mem_sub ] ; ring;
  exact ⟨ fun ⟨ x, hx, y, hy, hxy ⟩ => ⟨ y, hy, -x, ⟨ by simpa using hx.1, by linarith, by linarith ⟩, by linarith ⟩, fun ⟨ x, hx, y, hy, hxy ⟩ => ⟨ -y, ⟨ by simpa using hy.1, by linarith, by linarith ⟩, x, hx, by linarith ⟩ ⟩

/-
**Corollary 'main step sums', second part.** If `I = [a,b]` is right balanced w.r.t. `A`,
`J = [c,d]` right balanced w.r.t. `B`, both nondegenerate, and `d_A(I) ≥ d(B)`, then
`(A ∩ I) + (B ∩ J) ⊇ [b+d - 2|B ∩ J|, b+d]`.
-/
lemma main_step_sums_right (hA : IsClosed A) (hB : IsClosed B) (hAfin : volume A ≠ ⊤)
    (hBfin : volume B ≠ ⊤) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hI : IsRightBalanced A a b) (hJ : IsRightBalanced B c d)
    (hdisc : disc B ≤ discOn A a b) :
    Icc (b + d - 2 * (volume (B ∩ Icc c d)).toReal) (b + d) ⊆
      (A ∩ Icc a b) + (B ∩ Icc c d) := by
  -- Reflect the intervals and apply `main_step_sums_left`.
  have h_reflect : IsLeftBalanced (-A) (-b) (-a) ∧ IsLeftBalanced (-B) (-d) (-c) := by
    constructor <;> constructor <;> try linarith;
    · intro x hx₁ hx₂; have := hI.2 ( -x ) ( by linarith ) ( by linarith ) ; simp_all +decide [ discOn_neg ] ;
      convert this using 1;
      convert discOn_neg A ( -x ) b using 1 ; ring;
    · intro x hx₁ hx₂; convert hJ.2 ( -x ) ( by linarith ) ( by linarith ) using 1;
      convert discOn_neg B ( -x ) d using 1 ; ring;
  have h_reflect : Icc (-b + -d) (-b + -d + 2 * (volume (-B ∩ Icc (-d) (-c))).toReal) ⊆ (-A ∩ Icc (-b) (-a)) + (-B ∩ Icc (-d) (-c)) := by
    apply_rules [ main_step_sums_left ] <;> try linarith;
    any_goals tauto;
    · exact hA.neg;
    · exact hB.neg;
    · simp_all +decide [ MeasureTheory.measureReal_def ];
    · aesop;
    · grind +suggestions;
  intro x hx; specialize h_reflect ( show -x ∈ Icc ( -b + -d ) ( -b + -d + 2 * ( volume ( -B ∩ Icc ( -d ) ( -c ) ) |> ENNReal.toReal ) ) from ?_ ) ; simp_all +decide [ Set.mem_add ] ;
  · rw [ show -B ∩ Icc ( -d ) ( -c ) = - ( B ∩ Icc c d ) by ext; aesop ] ; rw [ MeasureTheory.Measure.measure_neg ] ; constructor <;> linarith;
  · obtain ⟨ y, hy, z, hz, hyz ⟩ := h_reflect;
    exact ⟨ -y, ⟨ by simpa using hy.1, by constructor <;> linarith [ hy.2.1, hy.2.2 ] ⟩, -z, ⟨ by simpa using hz.1, by constructor <;> linarith [ hz.2.1, hz.2.2 ] ⟩, by norm_num; linarith ⟩

/-!
# Balanced intervals, continued: subinterval bounds, endpoints, and maximality

This file continues the balanced-interval toolbox of `Balanced.lean` with the results needed
for the proof of `offdiagonal_main2` (Section 3 of the paper):

* subinterval discrepancy bounds for balanced intervals (`discOn_le_of_balanced`,
  `neg_discOn_le_of_balanced`);
* endpoint membership of balanced intervals of positive length
  (`left_balanced_left_mem`, `right_balanced_right_mem`);
* the notion of a *maximal* left-balanced / balanced interval, and the fact that distinct
  maximal such intervals are disjoint (`maximal_left_balanced_disjoint`,
  `maximal_balanced_disjoint`).
-/

open MeasureTheory Set
open scoped Pointwise



variable {A B : Set ℝ}

/-
If `[a,b]` is balanced and `[p,q] ⊆ [a,b]`, then `d_A([p,q]) ≤ d_A([a,b])`.
(The discrepancy of any subinterval of a balanced interval is at most that of the whole.)
-/
lemma discOn_le_of_balanced (hA : MeasurableSet A) {a b p q : ℝ}
    (hbal : IsBalanced A a b) (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b) :
    discOn A p q ≤ discOn A a b := by
  obtain ⟨h_left, h_right⟩ := hbal;
  have h_add : discOn A a b = discOn A a p + discOn A p q + discOn A q b := by
    grind +suggestions;
  linarith [ h_left.2 p hap ( by linarith ), h_right.2 q ( by linarith ) ( by linarith ) ]

/-
If `[a,b]` is balanced and `[p,q] ⊆ [a,b]`, then `-d_A([a,b]) ≤ d_A([p,q])`.
-/
lemma neg_discOn_le_of_balanced (hA : MeasurableSet A) {a b p q : ℝ}
    (hbal : IsBalanced A a b) (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b) :
    -(discOn A a b) ≤ discOn A p q := by
  obtain ⟨h_left, h_right⟩ := hbal;
  obtain ⟨h_left, h_right⟩ := h_left;
  obtain ⟨h_left, h_right⟩ := ‹IsRightBalanced A a b›;
  grind +suggestions

/-
If `[a,b]` is left balanced w.r.t. a closed set `A` and `a < b`, then `a ∈ A`.
-/
lemma left_balanced_left_mem (hA : IsClosed A) {a b : ℝ}
    (hbal : IsLeftBalanced A a b) (hab : a < b) : a ∈ A := by
  by_contra h;
  -- Since $a \notin A$ and $A$ is closed, there exists $\delta > 0$ such that $(a - \delta, a + \delta) \cap A = \emptyset$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, Metric.ball a δ ∩ A = ∅ := by
    exact Metric.mem_nhds_iff.mp ( hA.isOpen_compl.mem_nhds h ) |> fun ⟨ δ, δ_pos, hδ ⟩ => ⟨ δ, δ_pos, Set.eq_empty_iff_forall_notMem.mpr fun x hx => hδ hx.1 hx.2 ⟩;
  -- Choose $\epsilon = \min(\delta/2, (b-a)/2) > 0$ so that $a + \epsilon \leq b$.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ε ≤ δ / 2 ∧ ε ≤ (b - a) / 2 := by
    exact ⟨ Min.min ( δ / 2 ) ( ( b - a ) / 2 ), lt_min ( half_pos hδ_pos ) ( half_pos ( sub_pos.mpr hab ) ), min_le_left _ _, min_le_right _ _ ⟩;
  -- Since $A \cap [a, a+\epsilon] = \emptyset$, we have $discOn A a (a+\epsilon) = 2*0 - \epsilon = -\epsilon < 0$.
  have h_disc_neg : discOn A a (a + ε) < 0 := by
    have h_empty : A ∩ Icc a (a + ε) = ∅ := by
      simp_all +decide [ Set.ext_iff ];
      exact fun x hx hx' => not_le.1 fun hx'' => hδ x ( abs_lt.2 ⟨ by linarith, by linarith ⟩ ) hx;
    unfold discOn; aesop;
  exact h_disc_neg.not_ge ( hbal.2 _ ( by linarith ) ( by linarith ) )

/-
If `[a,b]` is right balanced w.r.t. a closed set `A` and `a < b`, then `b ∈ A`.
-/
lemma right_balanced_right_mem (hA : IsClosed A) {a b : ℝ}
    (hbal : IsRightBalanced A a b) (hab : a < b) : b ∈ A := by
  have h_left_balanced_neg : IsLeftBalanced (-A) (-b) (-a) := by
    refine' ⟨ by linarith, fun c hc₁ hc₂ => _ ⟩;
    convert hbal.2 ( -c ) ( by linarith ) ( by linarith ) using 1;
    convert discOn_neg A ( -c ) b using 1 ; ring;
  have := left_balanced_left_mem ( show IsClosed ( -A ) from hA.neg ) h_left_balanced_neg ( by linarith ) ; aesop;

/-
Right-balanced analogue of `union_left_balanced`: two overlapping right-balanced intervals
unite to a right-balanced interval.
-/
lemma union_right_balanced (hA : MeasurableSet A) {a b c d : ℝ}
    (hI : IsRightBalanced A a b) (hJ : IsRightBalanced A c d) (hcb : c ≤ b) :
    IsRightBalanced A a (max b d) := by
  cases max_cases b d <;> simp_all +decide [ IsRightBalanced ];
  grind +suggestions

/-
If `[a,b]` and `[c,d]` are both balanced w.r.t. `A` and they overlap (`a ≤ c ≤ b ≤ d`), then
their union `[a,d]` is balanced.
-/
lemma union_balanced (hA : MeasurableSet A) {a b c d : ℝ}
    (hI : IsBalanced A a b) (hJ : IsBalanced A c d) (hac : a ≤ c) (hcb : c ≤ b) (hbd : b ≤ d) :
    IsBalanced A a d := by
  constructor;
  · simpa [ hbd ] using union_left_balanced hA hI.1 hJ.1 hac hcb;
  · convert union_right_balanced hA hI.2 hJ.2 hcb using 1 ; aesop

/-- `[a,b]` is a *maximal left-balanced* interval w.r.t. `A`: it is left balanced, and no strictly
larger interval containing it is left balanced. -/
def IsMaximalLeftBalanced (A : Set ℝ) (a b : ℝ) : Prop :=
  IsLeftBalanced A a b ∧ ∀ a' b', a' ≤ a → b ≤ b' → IsLeftBalanced A a' b' → a' = a ∧ b' = b

/-- `[a,b]` is a *maximal balanced* interval w.r.t. `A`. -/
def IsMaximalBalanced (A : Set ℝ) (a b : ℝ) : Prop :=
  IsBalanced A a b ∧ ∀ a' b', a' ≤ a → b ≤ b' → IsBalanced A a' b' → a' = a ∧ b' = b

/-
**Corollary 'balanced intervals' (left version).** Two distinct maximal left-balanced
intervals are disjoint.
-/
lemma maximal_left_balanced_disjoint (hA : MeasurableSet A) {a b c d : ℝ}
    (hI : IsMaximalLeftBalanced A a b) (hJ : IsMaximalLeftBalanced A c d)
    (hne : (a, b) ≠ (c, d)) : Disjoint (Icc a b) (Icc c d) := by
  by_contra h_not_disjoint;
  -- Without loss of generality, assume $a \leq c$.
  wlog hac : a ≤ c generalizing a b c d;
  · exact this hJ hI ( Ne.symm hne ) ( Set.not_disjoint_iff.mpr <| by obtain ⟨ x, hx₁, hx₂ ⟩ := Set.not_disjoint_iff.mp h_not_disjoint; exact ⟨ x, hx₂, hx₁ ⟩ ) ( le_of_not_ge hac );
  · obtain ⟨x, hx⟩ : ∃ x, x ∈ Set.Icc a b ∧ x ∈ Set.Icc c d := by
      exact Set.not_disjoint_iff.mp h_not_disjoint;
    obtain ⟨hI_balanced, hI_max⟩ := hI
    obtain ⟨hJ_balanced, hJ_max⟩ := hJ
    have h_union_balanced : IsLeftBalanced A a (max b d) := by
      apply union_left_balanced hA hI_balanced hJ_balanced hac (by
      linarith [ hx.1.2, hx.2.1 ]);
    grind

/-
**Corollary 'balanced intervals'.** Two distinct maximal balanced intervals are disjoint.
-/
lemma maximal_balanced_disjoint (hA : MeasurableSet A) {a b c d : ℝ}
    (hI : IsMaximalBalanced A a b) (hJ : IsMaximalBalanced A c d)
    (hne : (a, b) ≠ (c, d)) : Disjoint (Icc a b) (Icc c d) := by
  by_contra hnot;
  -- WLOG `a ≤ c` (symmetric otherwise, swapping the two intervals).
  wlog hac : a ≤ c generalizing a b c d;
  · grind;
  · rw [ Set.not_disjoint_iff ] at hnot;
    -- Then `c ≤ b` (from the common point).
    have hcb : c ≤ b := by
      linarith [ hnot.choose_spec.1.1, hnot.choose_spec.1.2, hnot.choose_spec.2.1, hnot.choose_spec.2.2 ];
    -- Split on whether `b ≤ d` or `d ≤ b`.
    by_cases hbd : b ≤ d;
    · -- Apply `union_balanced hA hI.1 hJ.1 hac hcb hbd : IsBalanced A a d`.
      have h_union : IsBalanced A a d := by
        exact union_balanced hA hI.1 hJ.1 hac hcb hbd;
      have := hI.2 a d ( by linarith ) ( by linarith ) h_union; simp_all +decide ;
      have := hJ.2 a b ( by linarith ) ( by linarith ) h_union; simp_all +decide ;
    · have := hJ.2 a b hac ( by linarith ) hI.1; aesop;

/-!
# Intersecting balanced intervals (Lemma 'intersect balanced' and Corollary 'add balanced')

This file continues the Section 3 toolbox with the intersection results:

* `ProductFree.inter_Icc_nonempty_of_balanced`: if `[a,b]` is balanced w.r.t. a closed `A`,
  `[c,d] ⊆ [a,b]` has positive length, and `d_A([a,b]) ≤ d - c`, then `A ∩ [c,d] ≠ ∅`.
* `ProductFree.intersect_balanced` (Lemma 'intersect balanced'): if `[a,b]` is balanced w.r.t. `A`,
  `[c,d]` is balanced w.r.t. `B`, both of positive length, they intersect, and
  `d_A([a,b]) = d_B([c,d])`, then `(A ∩ [a,b]) ∩ (B ∩ [c,d]) ≠ ∅`.
* `ProductFree.add_balanced` (Corollary 'add balanced'): under the same balance/discrepancy
  hypotheses, `(A ∩ [a,b]) + (B ∩ [c,d]) = [a,b] + [c,d]`.
-/

open MeasureTheory Set
open scoped Pointwise



variable {A B : Set ℝ}

/-
If a closed set `A` meets every interval `[d, d+ε]` (`ε > 0`), then `d ∈ A`
(`d` is a right limit point of `A`, and `A` is closed).
-/
lemma mem_of_forall_Icc_right (hA : IsClosed A) {d : ℝ}
    (h : ∀ ε > 0, (A ∩ Icc d (d + ε)).Nonempty) : d ∈ A := by
  have h_seq : ∀ n : ℕ, ∃ x_n ∈ A, d ≤ x_n ∧ x_n ≤ d + 1 / (n + 1) := by
    exact fun n => by obtain ⟨ x, hx₁, hx₂ ⟩ := h ( 1 / ( n + 1 ) ) ( by positivity ) ; exact ⟨ x, hx₁, hx₂.1, hx₂.2 ⟩ ;
  choose f hf using h_seq;
  exact hA.mem_of_tendsto ( tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => abs_nonneg _ ) ( fun n => abs_le.mpr ⟨ by linarith [ hf n ], by linarith [ hf n ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat ) ( Filter.Eventually.of_forall fun n => hf n |>.1 )

/-
**Key nonemptiness lemma.** If `[a,b]` is balanced w.r.t. a closed set `A`, the subinterval
`[c,d] ⊆ [a,b]` has positive length, and `d_A([a,b]) ≤ d - c`, then `A ∩ [c,d]` is nonempty.

(The hypothesis `d_A([a,b]) ≤ d - c` is essential: a wide balanced interval can have a subinterval
disjoint from `A`, but then its discrepancy exceeds `d - c`.)
-/
lemma inter_Icc_nonempty_of_balanced (hA : IsClosed A) {a b c d : ℝ}
    (hbal : IsBalanced A a b) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (hsmall : discOn A a b ≤ d - c) :
    (A ∩ Icc c d).Nonempty := by
  by_contra h_empty_inter; have h_measurable : MeasurableSet A := hA.measurableSet; simp_all +decide [ IsBalanced ] ; (
  have h_discOn_cd : discOn A c d = -(d - c) := by
    unfold discOn; simp_all +decide [ Set.not_nonempty_iff_eq_empty ] ;
  have h_discOn_ad : discOn A a d = 0 := by
    have h_discOn_ad : discOn A a d ≥ 0 := by
      exact hbal.1.2 d ( by linarith ) ( by linarith )
    have h_discOn_ab : discOn A a b = discOn A a d + discOn A d b := by
      exact discOn_add h_measurable ( by linarith ) ( by linarith )
    have h_discOn_db : discOn A d b ≥ d - c := by
      have h_discOn_db : discOn A c b ≥ 0 := by
        exact hbal.2.2 c hac ( by linarith ) |> fun h => by linarith;
      have h_discOn_cb : discOn A c b = discOn A c d + discOn A d b := by
        exact discOn_add h_measurable ( by linarith ) ( by linarith )
      linarith [h_discOn_cb, h_discOn_db]
    linarith [h_discOn_ab, h_discOn_db]
  have h_discOn_db : discOn A d b = d - c := by
    have h_discOn_ab : discOn A a b = discOn A a d + discOn A d b := by
      exact discOn_add h_measurable ( by linarith ) ( by linarith )
    have h_discOn_ab_le : discOn A a b ≤ d - c := by
      linarith [hsmall]
    have h_discOn_ab_ge : discOn A a b ≥ d - c := by
      have h_discOn_ac : discOn A a c ≥ d - c := by
        grind +suggestions
      have h_discOn_ab_ge : discOn A a b ≥ d - c := by
        have h_discOn_ab_ge : discOn A a b = discOn A a c + discOn A c b := by
          exact discOn_add h_measurable hac ( by linarith )
        linarith [hbal.2.2 c (by linarith) (by linarith)]
      linarith [h_discOn_ab_ge]
    linarith [h_discOn_ab, h_discOn_ab_le, h_discOn_ab_ge]
  have h_discOn_ab : discOn A a b = d - c := by
    linarith [ discOn_add h_measurable ( by linarith : a ≤ d ) ( by linarith : d ≤ b ) ]
  have h_discOn_ac : discOn A a c = d - c := by
    linarith [ discOn_add h_measurable hac ( by linarith : c ≤ d ), discOn_add h_measurable ( by linarith : a ≤ d ) ( by linarith : d ≤ b ) ];
  -- For every `ε > 0`, show `(A ∩ Icc d (d+ε)).Nonempty`. Let `x = min (d+ε) b` (so `d ≤ x ≤ b`, and `x > d` since `d < b` because `c < d ≤ b`).
  have h_forall_ε : ∀ ε > 0, (A ∩ Icc d (min (d + ε) b)).Nonempty := by
    intros ε hε_pos
    set x := min (d + ε) b with hx_def
    have hx_bounds : d ≤ x ∧ x ≤ b := by
      exact ⟨ le_min ( by linarith ) ( by linarith ), min_le_right _ _ ⟩
    have hx_gt_d : d < x := by
      cases min_cases ( d + ε ) b <;> linarith [ show d < b from lt_of_le_of_ne hdb ( by rintro rfl; exact h_empty_inter <| by have := right_balanced_right_mem hA hbal.2 ( by linarith ) ; exact ⟨ _, this, by constructor <;> linarith ⟩ ) ] ;
    have h_discOn_dx : discOn A d x ≥ 0 := by
      have h_discOn_dx : discOn A a x ≥ 0 := by
        exact hbal.1.2 x ( by linarith ) ( by linarith ) |> fun h => by linarith;
      generalize_proofs at *; (
      linarith [ discOn_add h_measurable ( show a ≤ d by linarith ) ( show d ≤ x by linarith ) ])
    have h_discOn_dx_pos : (volume (A ∩ Icc d x)).toReal ≥ (x - d) / 2 := by
      unfold discOn at h_discOn_dx; linarith;
    have h_nonempty : (A ∩ Icc d x).Nonempty := by
      exact Set.nonempty_iff_ne_empty.mpr ( by rintro h; norm_num [ h ] at h_discOn_dx_pos; linarith ) ;
    exact h_nonempty.mono (by
    exact Set.Subset.rfl)
  generalize_proofs at *; (
  -- Therefore `d ∈ A` by `mem_of_forall_Icc_right`, contradiction.
  have h_d_in_A : d ∈ A := by
    apply mem_of_forall_Icc_right hA; intro ε hε; exact (by
    exact Exists.elim ( h_forall_ε ε hε ) fun x hx => ⟨ x, hx.1, hx.2.1, hx.2.2.trans ( min_le_left _ _ ) ⟩);
  generalize_proofs at *; (
  exact h_empty_inter ⟨ d, h_d_in_A, ⟨ by linarith, by linarith ⟩ ⟩)));

/-
Version of Lemma 'intersect balanced' with the ordering hypothesis `a ≤ c` (and `c ≤ b`,
which follows from the intervals intersecting).
-/
lemma intersect_balanced_of_le (hA : IsClosed A) (hB : IsClosed B) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hI : IsBalanced A a b) (hJ : IsBalanced B c d)
    (hac : a ≤ c) (hcb : c ≤ b) (hdisc : discOn A a b = discOn B c d) :
    (A ∩ Icc a b ∩ (B ∩ Icc c d)).Nonempty := by
  by_cases hbd : b ≤ d <;> simp_all +decide [ IsBalanced ];
  · by_cases hcb' : c < b;
    · obtain ⟨x, hx⟩ : (A ∩ B ∩ Icc c b).Nonempty := by
        apply inter_nonempty_of_measure hA hB hcb';
        · have := hI.2.2 c hac hcb; unfold discOn at this; linarith;
        · have := hJ.1.2 b ( by linarith ) ( by linarith ) ; unfold discOn at this; linarith;
      exact ⟨ x, ⟨ ⟨ hx.1.1, by constructor <;> linarith [ hx.2.1, hx.2.2 ] ⟩, ⟨ hx.1.2, by constructor <;> linarith [ hx.2.1, hx.2.2 ] ⟩ ⟩ ⟩;
    · -- Since $c = b$, we have $b \in A$ and $c \in B$.
      have hbA : b ∈ A := by
        exact right_balanced_right_mem hA hI.2 hab
      have hcB : c ∈ B := by
        exact left_balanced_left_mem hB hJ.1 ( by linarith )
      use b
      simp [hbA];
      exact ⟨ by linarith, by convert hcB using 1; linarith, by linarith, by linarith ⟩;
  · obtain ⟨x, hx⟩ : (A ∩ Icc c d).Nonempty ∧ (B ∩ Icc c d).Nonempty ∧ 0 ≤ discOn A c d + discOn B c d := by
      refine' ⟨ _, _, _ ⟩;
      · apply inter_Icc_nonempty_of_balanced hA hI;
        · linarith;
        · linarith;
        · linarith;
        · rw [ hdisc ];
          exact discOn_le_sub B hcd.le;
      · exact ⟨ c, left_balanced_left_mem hB hJ.1 hcd, ⟨ by linarith, by linarith ⟩ ⟩;
      · have h_subinterval : discOn A a d ≥ 0 ∧ discOn A c b ≥ 0 := by
          exact ⟨ hI.1.2 d ( by linarith ) ( by linarith ), hI.2.2 c ( by linarith ) ( by linarith ) ⟩;
        have h_subinterval : discOn A a b = discOn A a d + discOn A d b ∧ discOn A c b = discOn A c d + discOn A d b := by
          exact ⟨ discOn_add ( hA.measurableSet ) ( by linarith ) ( by linarith ), discOn_add ( hA.measurableSet ) ( by linarith ) ( by linarith ) ⟩;
        linarith;
    have := inter_nonempty_of_discOn hA hB hcd x hx.1 hx.2;
    exact this.imp fun x hx => ⟨ ⟨ hx.1.1, ⟨ by linarith [ hx.2.1 ], by linarith [ hx.2.2 ] ⟩ ⟩, ⟨ hx.1.2, hx.2 ⟩ ⟩

/-
**Lemma 'intersect balanced'.** If `[a,b]` is balanced w.r.t. `A`, `[c,d]` is balanced w.r.t.
`B`, both of positive length, `[a,b] ∩ [c,d] ≠ ∅`, and `d_A([a,b]) = d_B([c,d])`, then
`(A ∩ [a,b]) ∩ (B ∩ [c,d]) ≠ ∅`.
-/
lemma intersect_balanced (hA : IsClosed A) (hB : IsClosed B) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hI : IsBalanced A a b) (hJ : IsBalanced B c d)
    (hinter : (Icc a b ∩ Icc c d).Nonempty) (hdisc : discOn A a b = discOn B c d) :
    (A ∩ Icc a b ∩ (B ∩ Icc c d)).Nonempty := by
  by_cases hac : a ≤ c;
  · obtain ⟨ x, hx ⟩ := hinter;
    apply intersect_balanced_of_le hA hB hab hcd hI hJ hac (by linarith [hx.1.2, hx.2.1]) hdisc;
  · have := intersect_balanced_of_le hB hA hcd hab hJ hI ( by linarith ) ( by linarith [ Set.mem_Icc.mp ( hinter.choose_spec.1 ), Set.mem_Icc.mp ( hinter.choose_spec.2 ) ] ) hdisc.symm; simp_all +decide [ Set.inter_comm ];

/-
Reflection `y ↦ x - y` of a closed set is closed.
-/
lemma isClosed_reflect_sub {B : Set ℝ} (x : ℝ) (h : IsClosed B) :
    IsClosed ((fun y => x - y) '' B) := by
  convert h.preimage ( show Continuous fun y => x - y from continuous_const.sub continuous_id' ) using 1;
  ext y; aesop

/-
Reflection `y ↦ x - y` preserves the interval discrepancy:
`d_{x-B}([x-d, x-c]) = d_B([c,d])`.
-/
lemma discOn_reflect_sub (B : Set ℝ) (x c d : ℝ) :
    discOn ((fun y => x - y) '' B) (x - d) (x - c) = discOn B c d := by
  by_contra h_contra;
  -- Let's simplify the expression using the fact that multiplication by a constant $k$ and addition are compatible with the volume measure.
  have h_volume : volume ((fun y => x - y) '' B ∩ Icc (x - d) (x - c)) = volume (B ∩ Icc c d) := by
    rw [ show ( fun y => x - y ) '' B ∩ Icc ( x - d ) ( x - c ) = ( fun y => x - y ) '' ( B ∩ Icc c d ) from ?_ ];
    · have h_volume : ∀ (S : Set ℝ), volume ((fun y => x - y) '' S) = volume S := by
        intro S;
        rw [ show ( fun y => x - y ) '' S = ( fun y => -y ) '' S + { x } by ext; simp +decide [ sub_eq_add_neg, add_comm ] ; aesop ];
        simp +decide [ Set.image_neg, Set.add_singleton ];
      exact h_volume _;
    · ext; simp [Set.mem_image, Set.mem_inter_iff];
      grind +splitIndPred;
  exact h_contra ( by unfold discOn; aesop )

/-
Reflection `y ↦ x - y` preserves balancedness.
-/
lemma isBalanced_reflect_sub {B : Set ℝ} {c d : ℝ} (x : ℝ) (h : IsBalanced B c d) :
    IsBalanced ((fun y => x - y) '' B) (x - d) (x - c) := by
  constructor;
  · constructor;
    · linarith [ h.1.1 ];
    · intro e he₁ he₂;
      have := discOn_reflect_sub B x ( x - e ) d; simp_all +decide [ IsBalanced ] ;
      exact h.2.2 _ ( by linarith ) ( by linarith );
  · constructor;
    · linarith [ h.1.1 ];
    · intro y hy₁ hy₂; have := h.1.2 ( x - y ) ?_ ?_ <;> simp_all +decide ;
      · convert this using 1;
        convert discOn_reflect_sub B x c ( x - y ) using 1 ; ring;
      · linarith;
      · linarith

/-
**Corollary 'add balanced'.** If `[a,b]` is balanced w.r.t. `A`, `[c,d]` is balanced w.r.t.
`B`, both of positive length, and `d_A([a,b]) = d_B([c,d])`, then
`(A ∩ [a,b]) + (B ∩ [c,d]) = [a,b] + [c,d]`.
-/
lemma add_balanced (hA : IsClosed A) (hB : IsClosed B) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hI : IsBalanced A a b) (hJ : IsBalanced B c d)
    (hdisc : discOn A a b = discOn B c d) :
    (A ∩ Icc a b) + (B ∩ Icc c d) = Icc a b + Icc c d := by
  ext z;
  constructor <;> intro hz;
  · exact Set.add_subset_add ( Set.inter_subset_right ) ( Set.inter_subset_right ) hz;
  · -- Set `B' := (fun y => z - y) '' B` and consider the interval `[z-d, z-c]`.
    set B' := (fun y => z - y) '' B
    set p := max a (z - d)
    set q := min b (z - c);
    -- By `intersect_balanced`, there exists `p ∈ A ∩ Icc a b ∩ (B' ∩ Icc (z-d) (z-c))`.
    obtain ⟨p, hp⟩ : ∃ p, p ∈ A ∩ Icc a b ∩ (B' ∩ Icc (z - d) (z - c)) := by
      apply intersect_balanced hA (isClosed_reflect_sub z hB) hab (by
      linarith) hI (by
      exact isBalanced_reflect_sub z hJ) (by
      exact ⟨ hz.choose, hz.choose_spec.1, ⟨ by linarith [ hz.choose_spec.2.choose_spec.1.1, hz.choose_spec.2.choose_spec.1.2, hz.choose_spec.2.choose_spec.2 ], by linarith [ hz.choose_spec.2.choose_spec.1.1, hz.choose_spec.2.choose_spec.1.2, hz.choose_spec.2.choose_spec.2 ] ⟩ ⟩) (by
      rw [ hdisc, discOn_reflect_sub ]);
    simp +zetaDelta at *;
    exact ⟨ p, ⟨ hp.1.1, hp.1.2.1, hp.1.2.2 ⟩, hp.2.1.choose, ⟨ hp.2.1.choose_spec.1, by linarith [ hp.2.1.choose_spec.2 ], by linarith [ hp.2.1.choose_spec.2 ] ⟩, by linarith [ hp.2.1.choose_spec.2 ] ⟩

/-!
# Greedy left-balanced decomposition

Corollary `key_bound` and the proof of `offdiagonal_main2` rely on decomposing a finite union
of closed intervals `B` into the (finitely many) maximal left-balanced intervals whose
`B`-intersections partition `B`.

We build this decomposition greedily from the left. The key step (`exists_max_lb`) is that for
each starting point `c` there is a largest right endpoint `d` with `[c,d]` left balanced; the set
of admissible right endpoints is a bounded, down-closed, closed interval.
-/

open MeasureTheory Set
open scoped Pointwise



variable {B : Set ℝ}

/-
The cumulative mass `x ↦ |A ∩ [c,x]|` is continuous (indeed 1-Lipschitz).
-/
lemma continuous_mass_right (A : Set ℝ) (hfin : volume A ≠ ⊤) (c : ℝ) :
    Continuous (fun x => (volume (A ∩ Icc c x)).toReal) := by
  refine' continuous_iff_continuousAt.mpr _;
  intro x
  have h_lip : ∀ x y : ℝ, x ≤ y → |(volume (A ∩ Icc c y)).toReal - (volume (A ∩ Icc c x)).toReal| ≤ |y - x| := by
    intro x y hxy;
    -- Using the fact that the volume of the intersection of A with an interval is monotone, we have:
    have h_monotone : (volume (A ∩ Icc c y)).toReal ≤ (volume (A ∩ Icc c x)).toReal + (volume (Ioc x y)).toReal := by
      rw [ ← ENNReal.toReal_add ];
      · gcongr;
        · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ), by simp +decide [ hxy ] ⟩ );
        · refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
          exact fun z hz => if h : z ≤ x then Or.inl ⟨ hz.1, ⟨ hz.2.1, h ⟩ ⟩ else Or.inr ⟨ not_le.mp h, hz.2.2 ⟩;
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ) );
      · norm_num;
    rw [ abs_of_nonneg ( sub_nonneg_of_le <| ENNReal.toReal_mono ?_ <| MeasureTheory.measure_mono <| Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc_right hxy ) ];
    · simp_all +decide [ Real.volume_Ioc ];
      linarith [ abs_of_nonneg ( sub_nonneg.mpr hxy ) ];
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ) );
  refine' Metric.continuousAt_iff'.mpr _;
  intro ε hε; filter_upwards [ Metric.ball_mem_nhds x hε ] with y hy; rcases le_total y x with h | h <;> simp_all +decide [ dist_eq_norm ] ;
  · grind +suggestions;
  · exact lt_of_le_of_lt ( h_lip x y h ) hy

/-
`discOn A c ·` is continuous in the right endpoint.
-/
lemma continuous_discOn_right (A : Set ℝ) (hfin : volume A ≠ ⊤) (c : ℝ) :
    Continuous (fun x => discOn A c x) := by
  exact Continuous.sub ( continuous_const.mul ( continuous_mass_right A hfin c ) ) ( continuous_id.sub continuous_const )

/-- `d` is a *clean* cut point for the component list `ivs`: no component straddles it. -/
def CleanRight (ivs : List (ℝ × ℝ)) (d : ℝ) : Prop := ∀ p ∈ ivs, p.2 ≤ d ∨ d < p.1

/-
Intersecting an interval-union with `Ioi d` at a clean cut point gives the interval-union of
the components lying strictly to the right of `d`.
-/
lemma inter_Ioi_of_clean {ivs : List (ℝ × ℝ)} (h : IsIntervalUnion B ivs) {d : ℝ}
    (hcl : CleanRight ivs d) :
    IsIntervalUnion (B ∩ Ioi d) (ivs.filter (fun p => decide (d < p.1))) := by
  obtain ⟨hle, hB⟩ := h;
  constructor;
  · exact fun p hp => hle p <| List.mem_of_mem_filter hp;
  · ext x;
    simp [hB];
    grind +locals

/-
The maximal left-balanced right endpoint `d` from `sInf B` is a clean cut point: no component
of `B` straddles `d`.
-/
lemma cleanRight_of_maximal {ivs : List (ℝ × ℝ)} (h : IsIntervalUnion B ivs)
    (hfin : volume B ≠ ⊤) {d : ℝ}
    (hdd : IsLeftBalanced B (sInf B) d)
    (hmax : ∀ d', IsLeftBalanced B (sInf B) d' → d' ≤ d) :
    CleanRight ivs d := by
  intro p hp;
  contrapose! hmax;
  refine' ⟨ p.2, _, hmax.1 ⟩;
  refine' ⟨ _, _ ⟩;
  · linarith [ hdd.1, show sInf B ≤ d from hdd.1 ];
  · intro c hc₁ hc₂;
    by_cases hc₃ : c ≤ d;
    · exact hdd.2 c hc₁ hc₃;
    · -- Since $c > d$, we have $B \cap Icc (sInf B) c = (B \cap Icc (sInf B) d) \cup Icc d c$.
      have h_union : B ∩ Icc (sInf B) c = (B ∩ Icc (sInf B) d) ∪ Icc d c := by
        have h_union : Icc d c ⊆ B := by
          have h_subset : Icc p.1 p.2 ⊆ B := by
            exact h.2.symm ▸ Set.subset_iUnion₂_of_subset p hp ( Set.Subset.refl _ );
          exact Set.Subset.trans ( Set.Icc_subset_Icc ( by linarith ) ( by linarith ) ) h_subset;
        ext x;
        simp +zetaDelta at *;
        exact ⟨ fun hx => if h : x ≤ d then Or.inl ⟨ hx.1, hx.2.1, h ⟩ else Or.inr ⟨ by linarith, hx.2.2 ⟩, fun hx => hx.elim ( fun hx => ⟨ hx.1, hx.2.1, by linarith ⟩ ) fun hx => ⟨ h_union ⟨ by linarith, by linarith ⟩, by linarith [ show sInf B ≤ d from hdd.1.trans' ( by linarith ) ], by linarith ⟩ ⟩;
      -- Since $Icc d c$ is a subset of $B$, we have $volume (B ∩ Icc (sInf B) c) = volume (B ∩ Icc (sInf B) d) + volume (Icc d c)$.
      have h_volume : volume (B ∩ Icc (sInf B) c) = volume (B ∩ Icc (sInf B) d) + volume (Icc d c) := by
        rw [ h_union, MeasureTheory.measure_union₀ ];
        · exact measurableSet_Icc.nullMeasurableSet;
        · refine' MeasureTheory.measure_mono_null _ _;
          exact { d };
          · grind;
          · norm_num;
      have := hdd.2 d ( by linarith [ hdd.1 ] ) ( by linarith [ hdd.1 ] ) ; simp_all +decide [ discOn ];
      rw [ ENNReal.toReal_add ] <;> norm_num;
      · rw [ ENNReal.toReal_ofReal ] <;> linarith;
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ) )

/-
**Greedy peeling step.** For a closed set `B` of finite measure and a starting point `c`,
there is a largest right endpoint `d ≥ c` with `[c,d]` left balanced w.r.t. `B`.
-/
lemma exists_max_lb (hB : IsClosed B) (hfin : volume B ≠ ⊤) (c : ℝ) :
    ∃ d, c ≤ d ∧ IsLeftBalanced B c d ∧ ∀ d', IsLeftBalanced B c d' → d' ≤ d := by
  -- Let `S = {d | IsLeftBalanced B c d}`.
  set S := {d : ℝ | c ≤ d ∧ IsLeftBalanced B c d} with hS_def;
  obtain ⟨d, hd⟩ : ∃ d, IsLUB S d := by
    refine' ⟨ _, isLUB_csSup _ _ ⟩;
    · refine' ⟨ c, _, _ ⟩ <;> norm_num [ IsLeftBalanced ];
      intro x hx₁ hx₂; rw [ le_antisymm hx₂ hx₁ ] ; unfold discOn; norm_num;
    · refine' ⟨ c + 2 * ( volume B |> ENNReal.toReal ), fun d hd => _ ⟩;
      have := hd.2.2 d hd.1 le_rfl;
      unfold discOn at this;
      linarith [ show ( volume ( B ∩ Icc c d ) |> ENNReal.toReal ) ≤ ( volume B |> ENNReal.toReal ) from ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ];
  refine' ⟨ d, _, _, _ ⟩;
  · exact hd.1 ⟨ le_rfl, ⟨ le_rfl, fun x hx₁ hx₂ => by rw [ show x = c by linarith ] ; simp +decide [ discOn ] ⟩ ⟩;
  · refine' ⟨ _, _ ⟩;
    · exact hd.1 ⟨ le_rfl, ⟨ le_rfl, fun x hx₁ hx₂ => by
        unfold discOn; norm_num [ show x = c by linarith ] ; ⟩ ⟩;
    · intro x hx₁ hx₂; rcases eq_or_lt_of_le hx₂ with rfl | hx₂' <;> simp_all +decide [ IsLeftBalanced ] ;
      · have h_seq : ∃ seq : ℕ → ℝ, (∀ n, seq n ∈ S) ∧ Filter.Tendsto seq Filter.atTop (nhds x) := by
          have h_seq : ∀ ε > 0, ∃ d ∈ S, x - ε < d ∧ d ≤ x := by
            intro ε ε_pos; rcases hd.exists_between ( show x - ε < x by linarith ) with ⟨ d, hd₁, hd₂ ⟩ ; use d; aesop;
          generalize_proofs at *; (
          choose! seq hseq using h_seq;
          exact ⟨ fun n => seq ( 1 / ( n + 1 ) ), fun n => hseq _ ( by positivity ) |>.1, tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => abs_nonneg _ ) ( fun n => abs_le.mpr ⟨ by linarith [ hseq ( 1 / ( n + 1 ) ) ( by positivity ) ], by linarith [ hseq ( 1 / ( n + 1 ) ) ( by positivity ) ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩)
        generalize_proofs at *; (
        obtain ⟨ seq, hseq₁, hseq₂ ⟩ := h_seq; exact le_of_tendsto_of_tendsto' tendsto_const_nhds ( continuous_discOn_right B hfin c |> Continuous.continuousAt |> fun h => h.tendsto.comp hseq₂ ) fun n => hseq₁ n |>.2 |>.2 _ ( by linarith [ hseq₁ n |>.1 ] ) ( by linarith [ hseq₁ n |>.1 ] ) ;);
      · rcases hd.exists_between hx₂' with ⟨ y, ⟨ hy₁, hy₂ ⟩, hy₃ ⟩ ; linarith [ hy₂ x hx₁ ( by linarith ) ];
  · exact fun d' hd' => hd.1 ⟨ hd'.1, hd' ⟩

/-
**Peeling the leftmost block.** For a nonempty interval-union `B` (list `ivs`), there is a
maximal left-balanced interval `[sInf B, d]` starting at `sInf B`, and `B ∩ Ioi d` is again an
interval-union with strictly fewer components, all lying strictly to the right of `d`.
-/
lemma peel {ivs : List (ℝ × ℝ)} (h : IsIntervalUnion B ivs) (hne : ivs ≠ []) (hB : IsClosed B) :
    ∃ (d : ℝ) (ivs' : List (ℝ × ℝ)),
      sInf B ≤ d ∧ IsLeftBalanced B (sInf B) d ∧
      (∀ d', IsLeftBalanced B (sInf B) d' → d' ≤ d) ∧
      IsIntervalUnion (B ∩ Ioi d) ivs' ∧ ivs'.length < ivs.length ∧
      (∀ p ∈ ivs', d < p.1) := by
  have := exists_max_lb hB ?_ ( sInf B );
  · obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := this;
    refine' ⟨ d, ivs.filter ( fun p => decide ( d < p.1 ) ), hd₁, hd₂, hd₃, _, _, _ ⟩;
    · apply inter_Ioi_of_clean h (cleanRight_of_maximal h (h.finite) hd₂ hd₃);
    · refine' List.length_filter_lt_length_iff_exists.mpr _;
      have hcpt : IsCompact B := h.isCompact
      have hmem : sInf B ∈ B := hcpt.sInf_mem (h.nonempty hne)
      have hp_exists : ∃ p ∈ ivs, sInf B ∈ Icc p.1 p.2 := by
        have hmem' : sInf B ∈ ⋃ p ∈ ivs, Icc p.1 p.2 := by
          rw [← h.2]
          exact hmem
        simp only [Set.mem_iUnion] at hmem'
        rcases hmem' with ⟨p, hp, hpI⟩
        exact ⟨p, hp, hpI⟩
      obtain ⟨p, hp, hpI⟩ := hp_exists
      refine' ⟨p, hp, ?_⟩
      have hclean := cleanRight_of_maximal h (h.finite) hd₂ hd₃ p hp
      rcases hclean with hp2 | hdp1
      · have hp1 : p.1 ≤ d := le_trans (le_trans hpI.1 hpI.2) hp2
        simpa using (not_lt.mpr hp1)
      · have hp1 : p.1 ≤ d := le_trans hpI.1 hd₁
        simpa using (not_lt.mpr hp1);
    · grind;
  · exact h.finite

/-!
# Edge discrepancies `d_L` and `d_R`

This file introduces the *left* and *right* edge discrepancies of a set (Definition
'edge discrepancy' in the paper), used in Corollary `key_bound` and the proof of
`offdiagonal_main2`.

For a (compact, nonempty) set `A` with `min A = sInf A` and `max A = sSup A`:

* `discR A = max_{x ≤ max A} d_A([x, max A])`  (right discrepancy);
* `discL A = max_{x ≥ min A} d_A([min A, x])`  (left discrepancy).

Both are nonnegative (take the degenerate interval at the endpoint) and bounded above by `d(A)`.
-/

open MeasureTheory Set
open scoped Pointwise



variable {A : Set ℝ}

/-- Right edge discrepancy `d_R(A) = max_{x ≤ max A} d_A([x, max A])`. -/
noncomputable def discR (A : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x, x ≤ sSup A ∧ r = discOn A x (sSup A)}

/-- Left edge discrepancy `d_L(A) = max_{x ≥ min A} d_A([min A, x])`. -/
noncomputable def discL (A : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x, sInf A ≤ x ∧ r = discOn A (sInf A) x}

/-- The value set defining `disc A` is bounded above (by `2|A|`) when `A` has finite measure. -/
lemma disc_bddAbove (hfin : volume A ≠ ⊤) :
    BddAbove {r : ℝ | ∃ a b : ℝ, a ≤ b ∧ r = 2 * (volume (A ∩ Icc a b)).toReal - (b - a)} := by
  refine ⟨2 * (volume A).toReal, ?_⟩
  rintro r ⟨a, b, hab, rfl⟩
  have : (volume (A ∩ Icc a b)).toReal ≤ (volume A).toReal :=
    ENNReal.toReal_mono hfin (measure_mono (Set.inter_subset_left))
  nlinarith [sub_nonneg.mpr hab]

/-
`d_R(A) ≤ d(A)`.
-/
lemma discR_le_disc (hfin : volume A ≠ ⊤) : discR A ≤ disc A := by
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ sSup A, le_rfl, rfl ⟩ ⟩;
  · rintro _ ⟨ x, hx, rfl ⟩;
    convert discOn_le_disc hfin hx using 1

/-
`d_L(A) ≤ d(A)`.
-/
lemma discL_le_disc (hfin : volume A ≠ ⊤) : discL A ≤ disc A := by
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ sInf A, le_rfl, rfl ⟩ ⟩;
  · rintro _ ⟨ x, hx, rfl ⟩;
    convert discOn_le_disc hfin hx using 1

/-
`0 ≤ d_R(A)`.
-/
lemma discR_nonneg (hfin : volume A ≠ ⊤) : 0 ≤ discR A := by
  refine' le_csSup _ _;
  · obtain ⟨ M, hM ⟩ := disc_bddAbove hfin;
    exact ⟨ M, by rintro r ⟨ x, hx, rfl ⟩ ; exact hM ⟨ x, sSup A, hx, rfl ⟩ ⟩;
  · refine' ⟨ sSup A, le_rfl, _ ⟩ ; unfold discOn ; norm_num;
    exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( measure_singleton (μ := volume) (sSup A) ) |> fun h => h.symm ▸ by norm_num;

/-
`0 ≤ d_L(A)`.
-/
lemma discL_nonneg (hfin : volume A ≠ ⊤) : 0 ≤ discL A := by
  refine' le_csSup _ _;
  · refine' ⟨ 2 * ( volume A |> ENNReal.toReal ), fun r hr => _ ⟩;
    obtain ⟨ x, hx₁, rfl ⟩ := hr;
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show A ∩ Icc ( sInf A ) x ⊆ A from Set.inter_subset_left ) zero_le_two );
    · exact sub_le_self _ ( by linarith );
    · assumption;
  · refine' ⟨ sInf A, le_rfl, _ ⟩;
    unfold discOn;
    by_cases h : sInf A ∈ A <;> simp +decide [ h ]

/-!
# Corollary `key_bound`

This file proves the paper's Corollary `key_bound`, the central tool in the proof of
`offdiagonal_main2`. Given a left-balanced interval `[a,b]` w.r.t. a closed set `A` with
`d_A([a,b]) ≥ d(B)`, the sumset `(A ∩ [a,b]) + B`, restricted to
`[a + min B, a + max B + d_R(B)]`, has measure at least `2|B|`.

The proof decomposes `B` greedily into maximal left-balanced blocks (`peel`), applies
`main_step_sums_left` to each block, and combines the resulting intervals, which are disjoint by
maximality.
-/

open MeasureTheory Set
open scoped Pointwise



variable {A B : Set ℝ}

/-
Discrepancy is monotone under inclusion (for finite-measure supersets).
-/
lemma disc_mono {A B : Set ℝ} (hAB : A ⊆ B) (hfin : volume B ≠ ⊤) : disc A ≤ disc B := by
  -- Every $r \in S_A$ satisfies $r \leq disc B$.
  have h_le_discB : ∀ r ∈ {r : ℝ | ∃ a b : ℝ, a ≤ b ∧ r = 2 * (volume (A ∩ Icc a b)).toReal - (b - a)}, r ≤ disc B := by
    intro r hr
    obtain ⟨a, b, hab, hr_eq⟩ := hr
    have h_le_discB : r ≤ 2 * (volume (B ∩ Icc a b)).toReal - (b - a) := by
      rw [ hr_eq ];
      gcongr;
      exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ) );
    exact le_trans h_le_discB ( le_csSup ( by exact disc_bddAbove hfin ) ⟨ a, b, hab, rfl ⟩ );
  exact csSup_le ⟨ _, ⟨ 0, 0, by norm_num, rfl ⟩ ⟩ h_le_discB

/-
`discOn B x (sSup B) ≤ d_R(B)` for `x ≤ sSup B`.
-/
lemma discOn_le_discR (hfin : volume B ≠ ⊤) {x : ℝ} (hx : x ≤ sSup B) :
    discOn B x (sSup B) ≤ discR B := by
  refine' le_csSup _ _;
  · refine' ⟨ 2 * ( volume B |> ENNReal.toReal ), fun r hr => _ ⟩;
    obtain ⟨ y, hy, rfl ⟩ := hr; exact sub_le_iff_le_add'.mpr ( by linarith [ show ( volume ( B ∩ Icc y ( sSup B ) ) |> ENNReal.toReal ) ≤ ( volume B |> ENNReal.toReal ) from ENNReal.toReal_mono hfin <| MeasureTheory.measure_mono <| Set.inter_subset_left ] ) ;
  · exact ⟨ x, hx, rfl ⟩

/-
`d_R` is monotone under inclusion when the maximum is preserved.
-/
lemma discR_mono {B B' : Set ℝ} (hsub : B' ⊆ B) (hsup : sSup B' = sSup B)
    (hfin : volume B ≠ ⊤) : discR B' ≤ discR B := by
  refine' csSup_le _ _ <;> norm_num;
  · exact ⟨ _, ⟨ sSup B', le_rfl, rfl ⟩ ⟩;
  · intro b x hx hb
    have h_discOn : discOn B' x (sSup B') ≤ discOn B x (sSup B) := by
      simp_all +decide [ discOn ];
      gcongr;
      exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ) );
    exact hb ▸ h_discOn.trans ( discOn_le_discR hfin ( by linarith ) )

/-
**Disjointness of the greedy blocks.** If `[sInf B, d]` is a maximal left-balanced interval
(so no left-balanced interval from `sInf B` extends past `d`), and `(d, m) ∩ B = ∅` with `d < m`,
then `sInf B + 2|B ∩ [sInf B, d]| < m`.
-/
lemma peel_gap (hfin : volume B ≠ ⊤) {d m : ℝ}
    (hdd : IsLeftBalanced B (sInf B) d)
    (hmax : ∀ d', IsLeftBalanced B (sInf B) d' → d' ≤ d)
    (hgap : B ∩ Ioo d m = ∅) (hm : d < m) :
    sInf B + 2 * (volume (B ∩ Icc (sInf B) d)).toReal < m := by
  contrapose! hmax;
  refine' ⟨ m, ⟨ by linarith [ hdd.1, show sInf B ≤ d from hdd.1 ], _ ⟩, hm ⟩;
  intro c hc₁ hc₂;
  by_cases hc₃ : c ≤ d;
  · exact hdd.2 c hc₁ hc₃;
  · have h_volume_zero : volume (B ∩ Set.Ioc d c) = 0 := by
      have h_volume_zero : B ∩ Set.Ioc d c ⊆ {c} := by
        intro x hx; cases eq_or_lt_of_le hx.2.2 <;> simp_all +decide [ Set.ext_iff ] ;
        linarith [ hgap x hx.1 hx.2.1 ];
      exact MeasureTheory.measure_mono_null h_volume_zero ( by norm_num );
    have h_volume_eq : volume (B ∩ Set.Icc (sInf B) c) = volume (B ∩ Set.Icc (sInf B) d) := by
      rw [ ← MeasureTheory.measure_diff_null h_volume_zero ];
      congr with x ; simp +decide [ Set.mem_diff, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc ];
      grind;
    unfold discOn; norm_num [ h_volume_eq ] ; linarith;

/-
Two disjoint measurable subsets of a finite-measure set have total measure at most that of
the set (real-valued form).
-/
lemma measure_le_of_two_disjoint {S U V : Set ℝ} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUS : U ⊆ S) (hVS : V ⊆ S) (hd : Disjoint U V) (hSfin : volume S ≠ ⊤) :
    (volume U).toReal + (volume V).toReal ≤ (volume S).toReal := by
  rw [← ENNReal.toReal_add]
  · apply ENNReal.toReal_mono hSfin
    rw [← MeasureTheory.measure_union₀ hV.nullMeasurableSet hd.aedisjoint]
    exact MeasureTheory.measure_mono (Set.union_subset hUS hVS)
  · exact ne_of_lt (lt_of_le_of_lt (measure_mono hUS) (lt_top_iff_ne_top.mpr hSfin))
  · exact ne_of_lt (lt_of_le_of_lt (measure_mono hVS) (lt_top_iff_ne_top.mpr hSfin))

/-
**Corollary `key_bound` (left version), inductive step.** Given the statement for all
interval-unions with strictly fewer components (`IH`), it holds for `B`.
-/
set_option maxHeartbeats 1000000 in
lemma key_bound_step (A : Set ℝ) (hA : IsClosed A) (hAfin : volume A ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hI : IsLeftBalanced A a b) {B : Set ℝ} {ivs : List (ℝ × ℝ)}
    (hB : IsIntervalUnion B ivs) (hBne : ivs ≠ []) (hdisc : disc B ≤ discOn A a b)
    (IH : ∀ (B' : Set ℝ) (ivs' : List (ℝ × ℝ)), ivs'.length < ivs.length →
      IsIntervalUnion B' ivs' → ivs' ≠ [] → disc B' ≤ discOn A a b →
      2 * (volume B').toReal ≤
        (volume (((A ∩ Icc a b) + B') ∩ Icc (a + sInf B') (a + sSup B' + discR B'))).toReal) :
    2 * (volume B).toReal ≤
      (volume (((A ∩ Icc a b) + B) ∩ Icc (a + sInf B) (a + sSup B + discR B))).toReal := by
  revert hdisc;
  intro hdisc
  set c := sInf B
  set M := sSup B
  set δ := discR B
  set S := ((A ∩ Icc a b) + B) ∩ Icc (a + c) (a + M + δ);
  -- Preliminaries:
  have hBcl := hB.isClosed
  have hBfin := hB.finite
  have hBcpt := IsIntervalUnion.isCompact hB
  have hBnes := hB.nonempty hBne
  have hcM : c ≤ M := by
    exact le_trans ( csInf_le hBcpt.bddBelow hBnes.choose_spec ) ( le_csSup hBcpt.bddAbove hBnes.choose_spec )
  have hMc : M ∈ B := by
    exact hBcpt.sSup_mem hBnes
  have hMc' : c ∈ B := by
    exact hBcpt.sInf_mem hBnes
  have hB_subset_Ici_c : B ⊆ Ici c := by
    exact fun x hx => csInf_le hBcpt.bddBelow hx
  have ha_mem : a ∈ A ∩ Icc a b := by
    exact ⟨ left_balanced_left_mem hA hI hab, ⟨ le_rfl, hab.le ⟩ ⟩
  have hδ_nonneg : 0 ≤ δ := by
    exact discR_nonneg hBfin
  have hSfin : volume S ≠ ⊤ := by
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) );
  -- Measure partition: $B = B₁ ∪ B'$ (since $B = (B ∩ Iic d) ∪ (B ∩ Ioi d)$ and $B ∩ Iic d = B₁$), the union disjoint ($Iic d$, $Ioi d$ disjoint). So $(volume B).toReal = (volume B₁).toReal + (volume B').toReal$ (both finite; $measure_union$ then $ENNReal.toReal_add$).
  obtain ⟨d, ivs', hd, hJlb, hmax, hB', hlen, hright⟩ := peel hB hBne hBcl
  set B₁ := B ∩ Icc c d
  set B' := B ∩ Ioi d
  have hB_eq : B = B₁ ∪ B' := by
    grind
  have hB_disjoint : Disjoint B₁ B' := by
    grind +splitImp
  have hB₁_finite : volume B₁ ≠ ⊤ := by
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show B₁ ⊆ B from fun x hx => hx.1 ) ) ( lt_top_iff_ne_top.mpr hBfin ) )
  have hB'_finite : volume B' ≠ ⊤ := by
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show B' ⊆ B from fun x hx => hx.1 ) ) ( lt_top_iff_ne_top.mpr hBfin ) )
  have hB_measure : (volume B).toReal = (volume B₁).toReal + (volume B').toReal := by
    rw [ hB_eq, MeasureTheory.measure_union hB_disjoint ];
    · rw [ ENNReal.toReal_add ] <;> norm_num [ hB₁_finite, hB'_finite ];
    · exact hBcl.measurableSet.inter measurableSet_Ioi;
  by_cases hivs' : ivs' = [];
  · -- Since $ivs' = []$, we have $B' = ∅$, so $B ⊆ Iic d$, $M ≤ d$, and $B = B₁$.
    have hB'_empty : B' = ∅ := by
      simpa [ hivs' ] using hB'.2
    have hM_le_d : M ≤ d := by
      exact le_of_not_gt fun h => hB'_empty.subset ⟨ hMc, h ⟩
    have hB_eq_B₁ : B = B₁ := by
      simpa [ hB'_empty ] using hB_eq;
    by_cases hcd : c < d;
    · -- By `main_step_sums_left`, $Icc (a+c) (a+c+2*(volume B₁).toReal) ⊆ (A ∩ Icc a b) + B₁$.
      have h_main_step : Icc (a + c) (a + c + 2 * (volume B₁).toReal) ⊆ (A ∩ Icc a b) + B₁ := by
        convert main_step_sums_left hA hBcl hAfin hBfin hab hcd hI hJlb _ using 1;
        exact hdisc;
      -- Since $B₁ = B$, we have $K ⊆ (A ∩ Icc a b) + B$.
      have hK_subset_S : Icc (a + c) (a + c + 2 * (volume B₁).toReal) ⊆ S := by
        have hδ_ge_discOn : δ ≥ discOn B c M := by
          exact discOn_le_discR hBfin hcM;
        have hδ_ge_discOn : δ ≥ 2 * (volume (B ∩ Icc c M)).toReal - (M - c) := by
          exact hδ_ge_discOn;
        rw [ show B ∩ Icc c M = B from ?_ ] at hδ_ge_discOn;
        · grind;
        · exact Set.inter_eq_left.mpr fun x hx => ⟨ hB_subset_Ici_c hx, le_csSup ( hBcpt.bddAbove ) hx ⟩;
      refine' le_trans _ ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono hK_subset_S );
      · norm_num [ hB_measure, hB'_empty ];
      · exact hSfin;
    · -- Since $c = d$, we have $B₁ = B ∩ Icc c c ⊆ {c}$ has volume 0.
      have hB₁_zero : (volume B₁).toReal = 0 := by
        rw [ show B₁ = { c } from _ ];
        · norm_num;
        · grind;
      rw [ hB_eq_B₁, hB₁_zero ] ; norm_num;
  · -- Let $m := sInf B'$. By $hB'.sInf_eq$ and $hright$ (head of $ivs'$ in $ivs'$), $d < m$. Let $M' := sSup B'$.
    set m := sInf B'
    set M' := sSup B'
    have hm : d < m := by
      have hm_mem : m ∈ B' := hB'.isCompact.sInf_mem (hB'.nonempty hivs')
      exact hm_mem.2
    have hM' : M' = M := by
      refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ _;
      · exact hB'.nonempty hivs';
      · exact fun x hx => le_csSup ( hBcpt.bddAbove ) hx.1;
      · intro w hw;
        contrapose! hw;
        refine' csSup_le _ _;
        · exact hBnes;
        · intro x hx; by_cases hx' : x ≤ d <;> [ exact le_trans ( show x ≤ d by linarith ) ( show d ≤ w by linarith [ hw ( m ) ( show m ∈ B' from by
                                                                                                                                  exact (IsIntervalUnion.isCompact hB').sInf_mem ( hB'.nonempty hivs' ) ) ] ) ; exact hw x ( show x ∈ B' from by
                                                                                                                                                                                  exact ⟨ hx, lt_of_not_ge hx' ⟩ ) ] ;
    have hdiscR_B' : discR B' ≤ δ := by
      apply discR_mono;
      · exact Set.inter_subset_left;
      · exact hM';
      · exact hBfin
    have hgap : B ∩ Ioo d m = ∅ := by
      exact Set.eq_empty_of_forall_notMem fun x hx => not_lt_of_ge ( csInf_le ( show BddBelow B' from hBcpt.bddBelow.mono <| Set.inter_subset_left ) <| show x ∈ B' from ⟨ hx.1, hx.2.1 ⟩ ) hx.2.2
    have hpeel_gap : c + 2 * (volume B₁).toReal < m := by
      apply peel_gap hBfin hJlb hmax hgap hm;
    by_cases hcd : c < d;
    · -- Let $U := Icc (a+c) (a+c+2*(volume B₁).toReal)$. By `main_step_sums_left`, $U ⊆ (A ∩ Icc a b) + B₁ ⊆ (A ∩ Icc a b) + B$. Also $U ⊆ Icc (a+c) (a+M+δ)$: $U$'s right end $a+c+2*(volume B₁).toReal < a+m$ (peel_gap) $≤ a+M+δ$ ($m ≤ M$, $δ ≥ 0$). So $U ⊆ S$.
      set U := Icc (a + c) (a + c + 2 * (volume B₁).toReal)
      have hU_subset_S : U ⊆ S := by
        have hU_subset_S : U ⊆ (A ∩ Icc a b) + B := by
          have hU_subset_S : U ⊆ (A ∩ Icc a b) + B₁ := by
            apply main_step_sums_left hA hBcl hAfin hBfin hab hcd hI hJlb hdisc;
          exact hU_subset_S.trans ( Set.add_subset_add_left <| Set.inter_subset_left );
        exact fun x hx => ⟨ hU_subset_S hx, ⟨ by linarith [ Set.mem_Icc.mp hx ], by linarith [ Set.mem_Icc.mp hx, show m ≤ M from hM'.symm ▸ csInf_le ( show BddBelow B' from hB'.isCompact.bddBelow ) ( show M' ∈ B' from (IsIntervalUnion.isCompact hB').sSup_mem <| hB'.nonempty hivs' ) ] ⟩ ⟩;
      -- Let $V := ((A ∩ Icc a b) + B') ∩ Icc (a+m) (a+M+discR B')$. By IH, $2*(volume B').toReal ≤ (volume V).toReal$.
      set V := ((A ∩ Icc a b) + B') ∩ Icc (a + m) (a + M + discR B')
      have hV_subset_S : V ⊆ S := by
        simp +zetaDelta at *;
        constructor;
        · exact fun x hx => hx.1 |> fun hx' => by rcases hx' with ⟨ y, hy, z, hz, rfl ⟩ ; exact ⟨ y, hy, z, hB_eq.symm.subset <| Or.inr hz, rfl ⟩ ;
        · grind
      have hV_measure : 2 * (volume B').toReal ≤ (volume V).toReal := by
        convert IH B' ivs' hlen hB' hivs' _ using 1;
        · grind;
        · exact le_trans ( disc_mono ( show B' ⊆ B from fun x hx => hx.1 ) hBfin ) hdisc;
      -- $U$ and $V$ are disjoint: $U ⊆ Iic (a+c+2*(volume B₁).toReal)$ and $V ⊆ Ici (a+m)$ with $a+c+2*(volume B₁).toReal < a+m$.
      have hUV_disjoint : Disjoint U V := by
        exact Set.disjoint_left.mpr fun x hxU hxV => by linarith [ Set.mem_Icc.mp hxU, Set.mem_Icc.mp hxV.2 ] ;
      have hUV_measure : (volume U).toReal + (volume V).toReal ≤ (volume S).toReal := by
        apply_rules [ measure_le_of_two_disjoint ];
        · exact measurableSet_Icc;
        · refine' MeasurableSet.inter _ _;
          · have h_compact : IsCompact (A ∩ Icc a b + B') := by
              apply_rules [ IsCompact.add, CompactIccSpace.isCompact_Icc ];
              · exact CompactIccSpace.isCompact_Icc.inter_left hA;
              · exact hB'.isCompact;
            exact h_compact.measurableSet;
          · exact measurableSet_Icc;
      rw [ show volume U = ENNReal.ofReal ( 2 * ( volume B₁ |> ENNReal.toReal ) ) from ?_ ] at hUV_measure;
      · rw [ ENNReal.toReal_ofReal ] at hUV_measure <;> linarith [ show 0 ≤ ( volume B₁ |> ENNReal.toReal ) from ENNReal.toReal_nonneg ];
      · simp +zetaDelta at *;
    · -- Since $c = d$, we have $B₁ = B ∩ Icc c c = {c}$, so $(volume B₁).toReal = 0$.
      have hB₁_zero : (volume B₁).toReal = 0 := by
        rw [ show B₁ = { c } from _ ];
        · norm_num;
        · grind;
      have hIH : 2 * (volume B').toReal ≤ (volume ((A ∩ Icc a b + B') ∩ Icc (a + m) (a + M + discR B'))).toReal := by
        convert IH B' ivs' hlen hB' hivs' _ using 1;
        · grind +splitImp;
        · exact le_trans ( disc_mono ( show B' ⊆ B from fun x hx => hx.1 ) hBfin ) hdisc;
      refine' le_trans _ ( hIH.trans _ );
      · linarith;
      · refine' ENNReal.toReal_mono _ _;
        · exact hSfin;
        · refine' MeasureTheory.measure_mono _;
          simp +zetaDelta at *;
          constructor;
          · exact fun x hx => Set.add_subset_add ( Set.Subset.refl _ ) ( Set.inter_subset_left ) hx.1;
          · grind

/-- **Corollary `key_bound` (left version), auxiliary induction.** -/
lemma key_bound_aux (A : Set ℝ) (hA : IsClosed A) (hAfin : volume A ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hI : IsLeftBalanced A a b) :
    ∀ (n : ℕ) (B : Set ℝ) (ivs : List (ℝ × ℝ)), ivs.length = n → IsIntervalUnion B ivs →
      ivs ≠ [] → disc B ≤ discOn A a b →
      2 * (volume B).toReal ≤
        (volume (((A ∩ Icc a b) + B) ∩ Icc (a + sInf B) (a + sSup B + discR B))).toReal := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B ivs hn hB hBne hdisc
    subst hn
    exact key_bound_step A hA hAfin hab hI hB hBne hdisc
      (fun B' ivs' hlt hB' hne' hd' => ih ivs'.length hlt B' ivs' rfl hB' hne' hd')

/-- **Corollary `key_bound` (left version).** If `[a,b]` is left balanced w.r.t. a closed set `A`
with `a < b`, `B` is a nonempty finite union of finite closed intervals, and `d_A([a,b]) ≥ d(B)`,
then `|((A ∩ [a,b]) + B) ∩ [a + min B, a + max B + d_R(B)]| ≥ 2|B|`. -/
lemma key_bound_left (A : Set ℝ) {B : Set ℝ} {ivs : List (ℝ × ℝ)}
    (hA : IsClosed A) (hAfin : volume A ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hI : IsLeftBalanced A a b) (hB : IsIntervalUnion B ivs) (hBne : ivs ≠ [])
    (hdisc : disc B ≤ discOn A a b) :
    2 * (volume B).toReal ≤
      (volume (((A ∩ Icc a b) + B) ∩ Icc (a + sInf B) (a + sSup B + discR B))).toReal :=
  key_bound_aux A hA hAfin hab hI ivs.length B ivs rfl hB hBne hdisc

/-!
# Corollary `key_bound`, right version

The right-hand version of `key_bound`, obtained from `key_bound_left` by reflecting in the origin.
-/

open MeasureTheory Set
open scoped Pointwise



variable {A B : Set ℝ}

/-
The reflection `-B` of an interval-union is an interval-union (reverse the list and negate
each interval).
-/
lemma IsIntervalUnion.neg {ivs : List (ℝ × ℝ)} (h : IsIntervalUnion B ivs) :
    IsIntervalUnion (-B) (ivs.reverse.map (fun p => (-p.2, -p.1))) := by
  constructor <;> norm_num [ Set.ext_iff ] at *;
  · rintro a b x y hx rfl rfl; linarith [ h.1 ( x, y ) hx ] ;
  · intro x; rw [ h.2 ] ; simp +decide [ Set.mem_iUnion ] ;
    grind

/-- The list `ivs.reverse.map (fun p => (-p.2, -p.1))` is empty iff `ivs` is. -/
lemma neg_ivs_ne_nil {ivs : List (ℝ × ℝ)} (hne : ivs ≠ []) :
    (ivs.reverse.map (fun p => (-p.2, -p.1))) ≠ [] := by
  simp [hne]

/-
Reflection swaps the two edge discrepancies: `d_R(-B) = d_L(B)`.
-/
lemma discR_neg_eq_discL (B : Set ℝ) : discR (-B) = discL B := by
  by_contra h_contra';
  contrapose! h_contra' ; ( unfold discR discL ; simp +decide [ discOn_neg ] ; );
  congr with r;
  constructor <;> rintro ⟨ x, hx, rfl ⟩ <;> use -x <;> simp_all +decide [ discOn_neg ];
  exact ⟨ by linarith, by simpa using discOn_neg B ( sInf B ) ( -x ) ⟩

/-
If `[a,b]` is right balanced w.r.t. `A`, then `[-b,-a]` is left balanced w.r.t. `-A`.
-/
lemma IsRightBalanced.neg_left {a b : ℝ} (h : IsRightBalanced A a b) :
    IsLeftBalanced (-A) (-b) (-a) := by
  cases h;
  unfold IsLeftBalanced; norm_num;
  refine' ⟨ by assumption, fun c hc₁ hc₂ => _ ⟩;
  convert ‹∀ c : ℝ, a ≤ c → c ≤ b → 0 ≤ discOn A c b› ( -c ) ( by linarith ) ( by linarith ) using 1;
  convert discOn_reflect_sub A _ _ _ using 2 ; ring;
  rotate_right;
  exacts [ 0, by ext; simp +decide [ neg_eq_iff_eq_neg ], by ring, by ring ]

/-
**Corollary `key_bound` (right version).** If `[a,b]` is right balanced w.r.t. a closed set
`A` with `a < b`, `B` is a nonempty finite union of finite closed intervals, and
`d_A([a,b]) ≥ d(B)`, then
`|((A ∩ [a,b]) + B) ∩ [b + min B - d_L(B), b + max B]| ≥ 2|B|`.
-/
lemma key_bound_right (A : Set ℝ) {B : Set ℝ} {ivs : List (ℝ × ℝ)}
    (hA : IsClosed A) (hAfin : volume A ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hI : IsRightBalanced A a b) (hB : IsIntervalUnion B ivs) (hBne : ivs ≠ [])
    (hdisc : disc B ≤ discOn A a b) :
    2 * (volume B).toReal ≤
      (volume (((A ∩ Icc a b) + B) ∩ Icc (b + sInf B - discL B) (b + sSup B))).toReal := by
  have h_key_left : 2 * (volume (-B)).toReal ≤ (volume (((-A ∩ Icc (-b) (-a)) + (-B)) ∩ Icc ((-b) + sInf (-B)) ((-b) + sSup (-B) + discR (-B)))).toReal := by
    apply key_bound_left;
    any_goals exact hB.neg;
    any_goals rw [ neg_lt_neg_iff ] ; linarith;
    · exact hA.neg;
    · convert hAfin using 1;
      norm_num [ MeasureTheory.measureReal_def ];
    · convert IsRightBalanced.neg_left hI using 1;
    · aesop;
    · rw [ discOn_neg, disc_neg ] ; linarith!;
  convert h_key_left using 1;
  · simp +zetaDelta at *;
  · have h_neg : -A ∩ Icc (-b) (-a) = -(A ∩ Icc a b) := by
      ext; simp [Set.mem_neg, Set.mem_Icc];
    rw [ h_neg, show ( - ( A ∩ Icc a b ) + -B ) = - ( ( A ∩ Icc a b ) + B ) from ?_, show ( -b + sInf ( -B ) ) = - ( b + sSup B ) from ?_, show ( -b + sSup ( -B ) + discR ( -B ) ) = - ( b + sInf B - discL B ) from ?_ ];
    · rw [ show ( - ( A ∩ Icc a b + B ) ∩ Icc ( - ( b + sSup B ) ) ( - ( b + sInf B - discL B ) ) ) = - ( ( A ∩ Icc a b + B ) ∩ Icc ( b + sInf B - discL B ) ( b + sSup B ) ) from ?_ ];
      · rw [ MeasureTheory.Measure.measure_neg ];
      · ext; simp [Set.mem_neg, Set.mem_add, Set.mem_Icc];
    · rw [ discR_neg_eq_discL, Real.sSup_neg ] ; ring;
    · norm_num [ neg_add_eq_sub ];
      ring;
    · ext; simp [Set.mem_add, Set.mem_neg];
      exact ⟨ fun ⟨ x, hx, y, hy, hxy ⟩ => ⟨ y, hy, x, hx, by linarith ⟩, fun ⟨ y, hy, x, hx, hxy ⟩ => ⟨ x, hx, y, hy, by linarith ⟩ ⟩

end

end ProductFree
theorem OMA.solution : OMA.R_Green3_green_3_R2_H1_R1_H1_R1.H1 := by
  classical
  intro A₀ B₀ hAs hBt hDeq a b c d haMin hbMax hab hcd hAttA hAttB
  obtain ⟨s, hs⟩ := hAs
  obtain ⟨t, ht⟩ := hBt
  let A : Set ℝ := ⋃ p ∈ s, Icc p.1 p.2
  let B : Set ℝ := ⋃ p ∈ t, Icc p.1 p.2
  have hmA : a ∈ A := by simpa [A, hs] using haMin.1
  have hMB : d ∈ B := by simpa [B, ht] using hbMax.1
  have hle_a : ∀ x ∈ A, a ≤ x := by
    intro x hx
    exact haMin.2 (by simpa [A, hs] using hx)
  have hle_d : ∀ x ∈ B, x ≤ d := by
    intro x hx
    exact hbMax.2 (by simpa [B, ht] using hx)
  have hDA : ProductFree.disc A = ProductFree.disc B := by
    change (sSup {t | ∃ x y : ℝ, x ≤ y ∧ t = 2 * volume.real (A ∩ Icc x y) - (y - x)}) =
      (sSup {t | ∃ x y : ℝ, x ≤ y ∧ t = 2 * volume.real (B ∩ Icc x y) - (y - x)})
    simpa [A, B, hs, ht] using hDeq
  have hAttA' : ProductFree.discOn A a b = ProductFree.disc A := by
    change 2 * volume.real (A ∩ Icc a b) - (b - a) =
      (sSup {t | ∃ x y : ℝ, x ≤ y ∧ t = 2 * volume.real (A ∩ Icc x y) - (y - x)})
    simpa [A, hs] using hAttA
  have hAttB' : ProductFree.discOn B c d = ProductFree.disc B := by
    change 2 * volume.real (B ∩ Icc c d) - (d - c) =
      (sSup {t | ∃ x y : ℝ, x ≤ y ∧ t = 2 * volume.real (B ∩ Icc x y) - (y - x)})
    simpa [B, ht] using hAttB
  let ivsA := s.toList.filter (fun p => p.1 ≤ p.2)
  let ivsB := t.toList.filter (fun p => p.1 ≤ p.2)
  have hIU_A : ProductFree.IsIntervalUnion A ivsA := by
    constructor
    · intro p hp
      exact by simpa using (List.mem_filter.mp hp).2
    · ext x
      constructor
      · intro hx
        change x ∈ ⋃ p ∈ s, Icc p.1 p.2 at hx
        rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hp_s, hxI⟩
        have hle : p.1 ≤ p.2 := le_trans hxI.1 hxI.2
        refine Set.mem_iUnion₂.mpr ⟨p, ?_, hxI⟩
        simp [ivsA, hp_s, hle]
      · intro hx
        change x ∈ ⋃ p ∈ s, Icc p.1 p.2
        rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hpiv, hxI⟩
        have hp_s : p ∈ s := by
          have hpt : p ∈ s.toList := (List.mem_filter.mp hpiv).1
          simpa using hpt
        exact Set.mem_iUnion₂.mpr ⟨p, hp_s, hxI⟩
  have hIU_B : ProductFree.IsIntervalUnion B ivsB := by
    constructor
    · intro p hp
      exact by simpa using (List.mem_filter.mp hp).2
    · ext x
      constructor
      · intro hx
        change x ∈ ⋃ p ∈ t, Icc p.1 p.2 at hx
        rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hp_t, hxI⟩
        have hle : p.1 ≤ p.2 := le_trans hxI.1 hxI.2
        refine Set.mem_iUnion₂.mpr ⟨p, ?_, hxI⟩
        simp [ivsB, hp_t, hle]
      · intro hx
        change x ∈ ⋃ p ∈ t, Icc p.1 p.2
        rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hpiv, hxI⟩
        have hp_t : p ∈ t := by
          have hpt : p ∈ t.toList := (List.mem_filter.mp hpiv).1
          simpa using hpt
        exact Set.mem_iUnion₂.mpr ⟨p, hp_t, hxI⟩
  have hAne : A.Nonempty := ⟨a, hmA⟩
  have hBne : B.Nonempty := ⟨d, hMB⟩
  have hAcl : IsClosed A := hIU_A.isClosed
  have hBcl : IsClosed B := hIU_B.isClosed
  have hAfin : volume A ≠ ⊤ := hIU_A.finite
  have hBfin : volume B ≠ ⊤ := hIU_B.finite
  have haInf : sInf A = a := by
    apply le_antisymm
    · exact csInf_le hIU_A.isCompact.bddBelow hmA
    · exact le_csInf hAne hle_a
  have hdSup : sSup B = d := by
    apply le_antisymm
    · exact csSup_le hBne hle_d
    · exact le_csSup hIU_B.isCompact.bddAbove hMB
  have hleftA : ProductFree.IsLeftBalanced A a b := by
    constructor
    · exact hab
    · intro x hax hxb
      have hsplit := ProductFree.discOn_add hAcl.measurableSet hax hxb
      have hxle : ProductFree.discOn A x b ≤ ProductFree.disc A :=
        ProductFree.discOn_le_disc hAfin hxb
      linarith [hsplit, hxle, hAttA']
  have hrightB : ProductFree.IsRightBalanced B c d := by
    constructor
    · exact hcd
    · intro x hcx hxd
      have hsplit := ProductFree.discOn_add hBcl.measurableSet hcx hxd
      have hxle : ProductFree.discOn B c x ≤ ProductFree.disc B :=
        ProductFree.discOn_le_disc hBfin hcx
      linarith [hsplit, hxle, hAttB']
  have vol_zero_of_disc_le_zero : ∀ {U : Set ℝ} {ivs : List (ℝ × ℝ)},
      ProductFree.IsIntervalUnion U ivs → ProductFree.disc U ≤ 0 → volume.real U = 0 := by
    intro U ivs hIU hd
    have hfin := hIU.finite
    have hpdeg : ∀ p ∈ ivs, p.2 ≤ p.1 := by
      intro p hp
      have hp12 := hIU.1 p hp
      have hsubI : Icc p.1 p.2 ⊆ U := by
        rw [hIU.2]
        exact Set.subset_iUnion₂_of_subset p hp (Set.Subset.refl _)
      have hfin2 : volume (U ∩ Icc p.1 p.2) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_left) (lt_top_iff_ne_top.mpr hfin))
      have hmle : volume.real (Icc p.1 p.2) ≤ volume.real (U ∩ Icc p.1 p.2) :=
        measureReal_mono (fun x hx => ⟨hsubI hx, hx⟩) hfin2 (μ := volume)
      have hvolI : volume.real (Icc p.1 p.2) = p.2 - p.1 := by
        rw [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hp12)]
      have hdOn_le : ProductFree.discOn U p.1 p.2 ≤ ProductFree.disc U :=
        ProductFree.discOn_le_disc hfin hp12
      have hdOn_ge : p.2 - p.1 ≤ ProductFree.discOn U p.1 p.2 := by
        change p.2 - p.1 ≤ 2 * volume.real (U ∩ Icc p.1 p.2) - (p.2 - p.1)
        linarith [hmle, hvolI]
      linarith
    have hnull : ∀ p ∈ ivs.toFinset, volume (Icc p.1 p.2) = 0 := by
      intro p hp
      have hpiv : p ∈ ivs := by simpa using hp
      rw [Real.volume_Icc, ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (hpdeg p hpiv))]
    have hvol : volume U = 0 := by
      apply le_antisymm
      · have hseteq : (⋃ p ∈ ivs, Icc p.1 p.2) = ⋃ p ∈ ivs.toFinset, Icc p.1 p.2 := by
          ext x
          simp
        calc
          volume U = volume (⋃ p ∈ ivs, Icc p.1 p.2) := congrArg volume hIU.2
          _ = volume (⋃ p ∈ ivs.toFinset, Icc p.1 p.2) := congrArg volume hseteq
          _ ≤ ∑ p ∈ ivs.toFinset, volume (Icc p.1 p.2) := measure_biUnion_finset_le _ _
          _ = 0 := by
            apply Finset.sum_eq_zero
            intro p hp_mem
            exact hnull p hp_mem
      · exact bot_le
    simp [MeasureTheory.measureReal_def, hvol]
  rw [hs, ht]
  change 2 * volume.real B ≤ volume.real ((A + B) ∩ Iic (a + d + ProductFree.disc A)) ∧
    2 * volume.real A ≤ volume.real ((A + B) ∩ Ici (a + d - ProductFree.disc B))
  by_cases hablt : a < b
  · by_cases hcdlt : c < d
    · have ivsA_ne : ivsA ≠ [] := by
        have hmem := hmA
        change a ∈ ⋃ p ∈ s, Icc p.1 p.2 at hmem
        rcases Set.mem_iUnion.mp hmem with ⟨p, hmem⟩
        rcases Set.mem_iUnion.mp hmem with ⟨hp_s, hpI⟩
        have hpiv : p ∈ ivsA := by simp [ivsA, hp_s, le_trans hpI.1 hpI.2]
        intro hnil
        simpa [hnil] using hpiv
      have ivsB_ne : ivsB ≠ [] := by
        have hmem := hMB
        change d ∈ ⋃ p ∈ t, Icc p.1 p.2 at hmem
        rcases Set.mem_iUnion.mp hmem with ⟨p, hmem⟩
        rcases Set.mem_iUnion.mp hmem with ⟨hp_t, hpI⟩
        have hpiv : p ∈ ivsB := by simp [ivsB, hp_t, le_trans hpI.1 hpI.2]
        intro hnil
        simpa [hnil] using hpiv
      have hdiscBA : ProductFree.disc B ≤ ProductFree.discOn A a b := by
        linarith [hDA, hAttA']
      have hdiscAB : ProductFree.disc A ≤ ProductFree.discOn B c d := by
        linarith [hDA, hAttB']
      have hKBL := ProductFree.key_bound_left A hAcl hAfin hablt hleftA hIU_B ivsB_ne hdiscBA
      have hKBR := ProductFree.key_bound_right B hBcl hBfin hcdlt hrightB hIU_A ivsA_ne hdiscAB
      have hsubsetL :
          ((A ∩ Icc a b) + B) ∩ Icc (a + sInf B) (a + sSup B + ProductFree.discR B)
            ⊆ (A + B) ∩ Iic (a + d + ProductFree.disc A) := by
        intro x hx
        constructor
        · rcases hx.1 with ⟨y, hyA, z, hzB, rfl⟩
          exact ⟨y, hyA.1, z, hzB, rfl⟩
        · have hDRle : ProductFree.discR B ≤ ProductFree.disc A := by
            have h := ProductFree.discR_le_disc hBfin
            linarith [h, hDA]
          calc
            x ≤ a + sSup B + ProductFree.discR B := hx.2.2
            _ ≤ a + d + ProductFree.disc A := by linarith [hDRle, hdSup]
      have hsubsetR :
          ((B ∩ Icc c d) + A) ∩ Icc (d + sInf A - ProductFree.discL A) (d + sSup A)
            ⊆ (A + B) ∩ Ici (a + d - ProductFree.disc B) := by
        intro x hx
        constructor
        · rcases hx.1 with ⟨y, hyB, z, hzA, rfl⟩
          exact ⟨z, hzA, y, hyB.1, by exact add_comm z y⟩
        · have hDLle : ProductFree.discL A ≤ ProductFree.disc B := by
            have h := ProductFree.discL_le_disc hAfin
            linarith [h, hDA]
          calc
            a + d - ProductFree.disc B ≤ d + sInf A - ProductFree.discL A := by
              linarith [haInf, hDLle]
            _ ≤ x := hx.2.1
      have hfinL : volume ((A + B) ∩ Iic (a + d + ProductFree.disc A)) ≠ ⊤ := by
        have hcpt : IsCompact (A + B) := hIU_A.isCompact.add hIU_B.isCompact
        exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_left) hcpt.measure_lt_top)
      have hfinR : volume ((A + B) ∩ Ici (a + d - ProductFree.disc B)) ≠ ⊤ := by
        have hcpt : IsCompact (A + B) := hIU_A.isCompact.add hIU_B.isCompact
        exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_left) hcpt.measure_lt_top)
      constructor
      · change 2 * (volume B).toReal ≤
          (volume ((A + B) ∩ Iic (a + d + ProductFree.disc A))).toReal
        exact hKBL.trans (measureReal_mono hsubsetL hfinL (μ := volume))
      · change 2 * (volume A).toReal ≤
          (volume ((A + B) ∩ Ici (a + d - ProductFree.disc B))).toReal
        exact hKBR.trans (measureReal_mono hsubsetR hfinR (μ := volume))
    · have hcdeq : c = d := le_antisymm hcd (not_lt.mp hcdlt)
      have hdiscB0 : ProductFree.disc B ≤ 0 := by
        have hz : ProductFree.discOn B c d = 0 := by
          rw [hcdeq]
          unfold ProductFree.discOn
          have hz0 : volume (B ∩ {d}) = 0 :=
            measure_mono_null (fun x hx => hx.2) (by simp)
          simp [MeasureTheory.measureReal_def, hz0]
        linarith [hAttB', hz]
      have hdiscA0 : ProductFree.disc A ≤ 0 := by linarith [hDA, hdiscB0]
      have hvolA0 := vol_zero_of_disc_le_zero hIU_A hdiscA0
      have hvolB0 := vol_zero_of_disc_le_zero hIU_B hdiscB0
      constructor <;> simp [hvolA0, hvolB0, measureReal_nonneg]
  · have haeq : a = b := le_antisymm hab (not_lt.mp hablt)
    have hdiscA0 : ProductFree.disc A ≤ 0 := by
      have hz : ProductFree.discOn A a b = 0 := by
        rw [haeq]
        unfold ProductFree.discOn
        have hz0 : volume (A ∩ {b}) = 0 :=
          measure_mono_null (fun x hx => hx.2) (by simp)
        simp [MeasureTheory.measureReal_def, hz0]
      linarith [hAttA', hz]
    have hdiscB0 : ProductFree.disc B ≤ 0 := by linarith [hDA, hdiscA0]
    have hvolA0 := vol_zero_of_disc_le_zero hIU_A hdiscA0
    have hvolB0 := vol_zero_of_disc_le_zero hIU_B hdiscB0
    constructor <;> simp [hvolA0, hvolB0, measureReal_nonneg]
