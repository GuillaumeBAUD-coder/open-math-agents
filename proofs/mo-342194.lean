import OMAStatements.S_mo_342194
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lemmas


noncomputable section

open scoped BigOperators ENNReal

namespace GoFiniteFiberL2

abbrev L2 (A : Type*) := ↥(lp (fun _ : A => ℂ) 2)

variable {A : Type*} [DecidableEq A]

def delta (a : A) : L2 A := lp.single 2 a 1

/-- Finite-fragment formulation of a uniform bound on every full fiber.
Unlike a bare Set.ncard inequality, this cannot hold vacuously on infinite fibers. -/
def FiniteFiberBound (T : A → A) (K : ℕ) : Prop :=
  ∀ (s : Finset A) (b : A), (s.filter (fun a => T a = b)).card ≤ K

lemma finiteFiberBound_of_finite (T : A → A) (K : ℕ)
    (hf : ∀ b, {a | T a = b}.Finite)
    (hcard : ∀ b, (hf b).toFinset.card ≤ K) : FiniteFiberBound T K := by
  intro s b
  apply (Finset.card_le_card ?_).trans (hcard b)
  intro a ha
  simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using
    (Finset.mem_filter.mp ha).2

lemma sum_comp_le (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K)
    (s : Finset A) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∑ a ∈ s, w (T a)) ≤ (K : ℝ) * ∑ b ∈ s.image T, w b := by
  have hf : ∀ a ∈ s, T a ∈ s.image T := fun a ha => Finset.mem_image_of_mem T ha
  rw [← Finset.sum_fiberwise_of_maps_to' hf w]
  calc
    (∑ b ∈ s.image T, ∑ a ∈ s with T a = b, w b) =
        ∑ b ∈ s.image T, ((s.filter (fun a => T a = b)).card : ℝ) * w b := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b ∈ s.image T, (K : ℝ) * w b := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_right _ (hw b)
      exact_mod_cast hT s b
    _ = (K : ℝ) * ∑ b ∈ s.image T, w b := by rw [Finset.mul_sum]

lemma pullback_square_sum_le (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K)
    (v : L2 A) (s : Finset A) :
    (∑ a ∈ s, ‖v (T a)‖ ^ 2) ≤ (K : ℝ) * ‖v‖ ^ 2 := by
  have hs : (∑ b ∈ s.image T, ‖v b‖ ^ 2) ≤ ‖v‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) v (s.image T)
  exact (sum_comp_le T K hT s (fun a => ‖v a‖ ^ 2) (fun a => sq_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg K))

lemma mem_pullback (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K) (v : L2 A) :
    Memℓp (fun a => v (T a)) 2 := by
  apply memℓp_gen' (C := (K : ℝ) * ‖v‖ ^ 2)
  intro s
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    pullback_square_sum_le T K hT v s

def pullbackLinear (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K) :
    L2 A →ₗ[ℂ] L2 A where
  toFun v := ⟨fun a => v (T a), mem_pullback T K hT v⟩
  map_add' v w := by ext a; rfl
  map_smul' c v := by ext a; rfl

lemma pullbackLinear_norm_le (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K)
    (v : L2 A) : ‖pullbackLinear T K hT v‖ ≤ Real.sqrt K * ‖v‖ := by
  apply lp.norm_le_of_forall_sum_le (p := 2) (by norm_num)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  intro s
  change (∑ a ∈ s, ‖v (T a)‖ ^ (2 : ℝ≥0∞).toReal) ≤
    (Real.sqrt (K : ℝ) * ‖v‖) ^ (2 : ℝ≥0∞).toReal
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg K)] using pullback_square_sum_le T K hT v s

def pullback (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K) : L2 A →L[ℂ] L2 A :=
  (pullbackLinear T K hT).mkContinuous (Real.sqrt K) (pullbackLinear_norm_le T K hT)

@[simp] lemma pullback_apply (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K)
    (v : L2 A) (a : A) : pullback T K hT v a = v (T a) := rfl

lemma norm_pullback_le (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K) :
    ‖pullback T K hT‖ ≤ Real.sqrt K :=
  (pullbackLinear T K hT).mkContinuous_norm_le (Real.sqrt_nonneg _)
    (pullbackLinear_norm_le T K hT)

def basisMap (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K) : L2 A →L[ℂ] L2 A :=
  (pullback T K hT).adjoint

lemma basisMap_delta (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K) (a : A) :
    basisMap T K hT (delta a) = delta (T a) := by
  apply lp.ext
  funext b
  have h := ContinuousLinearMap.adjoint_inner_right (pullback T K hT) (delta b) (delta a)
  simpa [basisMap, delta, lp.inner_single_left, lp.inner_single_right,
    RCLike.inner_apply, pullback_apply, lp.single_apply, Pi.single_apply, eq_comm] using h

lemma norm_basisMap_le (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K) :
    ‖basisMap T K hT‖ ≤ Real.sqrt K := by
  unfold basisMap
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact norm_pullback_le T K hT

/-- This useful coefficient identity only requires the actual basis action;
it does not depend on which bounded extension was used. -/
lemma adjoint_apply_of_delta (U : L2 A →L[ℂ] L2 A) (T : A → A)
    (hU : ∀ a, U (delta a) = delta (T a)) (v : L2 A) (a : A) :
    U.adjoint v a = v (T a) := by
  have h := ContinuousLinearMap.adjoint_inner_right U (delta a) v
  rw [hU a] at h
  simpa [delta, lp.inner_single_left, RCLike.inner_apply] using h

lemma basisMap_adjoint_apply (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K)
    (v : L2 A) (a : A) : (basisMap T K hT).adjoint v a = v (T a) :=
  adjoint_apply_of_delta _ T (basisMap_delta T K hT) v a

theorem exists_basisMap (T : A → A) (K : ℕ) (hT : FiniteFiberBound T K) :
    ∃ U : L2 A →L[ℂ] L2 A,
      (∀ a, U (delta a) = delta (T a)) ∧ ‖U‖ ≤ Real.sqrt K :=
  ⟨basisMap T K hT, basisMap_delta T K hT, norm_basisMap_le T K hT⟩

end GoFiniteFiberL2



namespace GoVacuumCommutant

open GoFiniteFiberL2

variable {A I : Type*} [DecidableEq A]

lemma clm_ext_delta (X Y : L2 A →L[ℂ] L2 A)
    (h : ∀ a, X (delta a) = Y (delta a)) : X = Y := by
  apply lp.ext_continuousLinearMap (p := 2) (by norm_num)
  intro a
  apply ContinuousLinearMap.ext
  intro z
  have hz : lp.single 2 a z = z • delta a := by
    simp [delta, ← lp.single_smul, smul_eq_mul]
  change X (lp.single 2 a z) = Y (lp.single 2 a z)
  rw [hz, map_smul, map_smul, h a]

lemma commute_apply (X Y : L2 A →L[ℂ] L2 A) (h : Commute X Y) (v : L2 A) :
    X (Y v) = Y (X v) := by
  have hv := congrArg (fun T : L2 A →L[ℂ] L2 A => T v) h.eq
  exact hv

lemma vacuum_in_joint_kernel (f : I → A → A) (e : A)
    (U : I → L2 A →L[ℂ] L2 A) (hU : ∀ i a, U i (delta a) = delta (f i a))
    (hno : ∀ i a, f i a ≠ e) (i : I) : (U i).adjoint (delta e) = 0 := by
  apply lp.ext
  funext a
  rw [adjoint_apply_of_delta (U i) (f i) (hU i)]
  simp [delta, lp.single_apply, Pi.single_apply, hno i a, (hno i a).symm]

lemma joint_kernel_eq_vacuum (f : I → A → A) (e : A)
    (U : I → L2 A →L[ℂ] L2 A) (hU : ∀ i a, U i (delta a) = delta (f i a))
    (hfixed : ∀ a, a ≠ e → ∃ i, f i a = a)
    (v : L2 A) (hv : ∀ i, (U i).adjoint v = 0) : v = v e • delta e := by
  apply lp.ext
  funext a
  by_cases he : a = e
  · subst a
    simp [delta, lp.single_apply, Pi.single_apply, smul_eq_mul]
  · obtain ⟨i, hi⟩ := hfixed a he
    have hc := adjoint_apply_of_delta (U i) (f i) (hU i) v a
    rw [hv i, hi] at hc
    have hva : v a = 0 := by simpa using hc.symm
    simp [delta, lp.single_apply, Pi.single_apply, he, hva]

lemma scalar_on_word (f : I → A → A) (e : A)
    (U : I → L2 A →L[ℂ] L2 A) (hU : ∀ i a, U i (delta a) = delta (f i a))
    (X : L2 A →L[ℂ] L2 A) (scalar : ℂ) (hXe : X (delta e) = scalar • delta e)
    (hcomm : ∀ i, Commute X (U i)) (w : List I) :
    X (delta (w.foldr f e)) = scalar • delta (w.foldr f e) := by
  induction w with
  | nil => exact hXe
  | cons i w ih =>
    change X (delta (f i (w.foldr f e))) = scalar • delta (f i (w.foldr f e))
    calc
      X (delta (f i (w.foldr f e))) = X (U i (delta (w.foldr f e))) :=
        congrArg X (hU i (w.foldr f e)).symm
      _ = U i (X (delta (w.foldr f e))) := commute_apply X (U i) (hcomm i) _
      _ = U i (scalar • delta (w.foldr f e)) := by rw [ih]
      _ = scalar • U i (delta (w.foldr f e)) := map_smul (U i) scalar _
      _ = scalar • delta (f i (w.foldr f e)) := by rw [hU i]

/-- Scalar commutant from combinatorial vacuum data. The joint-adjoint-kernel
and cyclicity arguments are proved here rather than assumed as Hilbert facts. -/
theorem scalar_commutant (f : I → A → A) (e : A)
    (U : I → L2 A →L[ℂ] L2 A) (hU : ∀ i a, U i (delta a) = delta (f i a))
    (hno : ∀ i a, f i a ≠ e)
    (hfixed : ∀ a, a ≠ e → ∃ i, f i a = a)
    (hbuild : ∀ a, ∃ w : List I, w.foldr f e = a)
    (X : L2 A →L[ℂ] L2 A)
    (hcomm : ∀ i, Commute X (U i) ∧ Commute X (U i).adjoint) :
    ∃ scalar : ℂ, X = scalar • ContinuousLinearMap.id ℂ (L2 A) := by
  have hker : ∀ i, (U i).adjoint (X (delta e)) = 0 := by
    intro i
    calc
      (U i).adjoint (X (delta e)) = X ((U i).adjoint (delta e)) :=
        (commute_apply X (U i).adjoint (hcomm i).2 (delta e)).symm
      _ = X 0 := by rw [vacuum_in_joint_kernel f e U hU hno i]
      _ = 0 := map_zero X
  let scalar : ℂ := X (delta e) e
  have hXe : X (delta e) = scalar • delta e :=
    joint_kernel_eq_vacuum f e U hU hfixed (X (delta e)) hker
  refine ⟨scalar, clm_ext_delta X (scalar • ContinuousLinearMap.id ℂ (L2 A)) ?_⟩
  intro a
  obtain ⟨w, hw⟩ := hbuild a
  change X (delta a) = scalar • delta a
  simpa only [hw] using scalar_on_word f e U hU X scalar hXe (fun i => (hcomm i).1) w

theorem exists_operators_scalar_commutant (f : I → A → A) (e : A) (K : ℕ)
    (hfinite : ∀ i, FiniteFiberBound (f i) K)
    (hno : ∀ i a, f i a ≠ e)
    (hfixed : ∀ a, a ≠ e → ∃ i, f i a = a)
    (hbuild : ∀ a, ∃ w : List I, w.foldr f e = a) :
    ∃ U : I → L2 A →L[ℂ] L2 A,
      (∀ i a, U i (delta a) = delta (f i a)) ∧
      ∀ X : L2 A →L[ℂ] L2 A,
        (∀ i, Commute X (U i) ∧ Commute X (U i).adjoint) →
        ∃ scalar : ℂ, X = scalar • ContinuousLinearMap.id ℂ (L2 A) := by
  let U : I → L2 A →L[ℂ] L2 A := fun i => basisMap (f i) K (hfinite i)
  have hU : ∀ i a, U i (delta a) = delta (f i a) :=
    fun i a => basisMap_delta (f i) K (hfinite i) a
  exact ⟨U, hU, fun X hcomm => scalar_commutant f e U hU hno hfixed hbuild X hcomm⟩

end GoVacuumCommutant

namespace OMA.S_mo_342194

/-- Stones may be removed, but retained stones keep their colors. -/
def IsSubposition (small large : Position) : Prop :=
  ∀ p, small p = none ∨ small p = large p

lemma neighbors_symm {p q : Point} (h : neighbors p q) : neighbors q p := by
  unfold neighbors at *
  rw [← neg_sub p.1 q.1, ← neg_sub p.2 q.2, Int.natAbs_neg, Int.natAbs_neg]
  exact h

lemma sameColorGraph_adj_iff (position : Position) (p q : Point) :
    (sameColorGraph position).Adj p q ↔ neighbors p q ∧ position p = position q := by
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ⟨neighbors_symm h.1, h.2.symm⟩
  · rintro ⟨hnear, hcolor⟩
    refine ⟨?_, Or.inl ⟨hnear, hcolor⟩⟩
    intro heq
    subst q
    simp [neighbors] at hnear

lemma reachable_color_eq {position : Position} {p q : Point}
    (h : (sameColorGraph position).Reachable p q) : position p = position q := by
  rcases h with ⟨walk⟩
  induction walk with
  | nil => rfl
  | cons hadj _ ih => exact ((sameColorGraph_adj_iff _ _ _).mp hadj).2.trans ih

lemma hasLiberty_of_reachable {position : Position} {p q : Point}
    (hpq : (sameColorGraph position).Reachable p q) (hq : hasLiberty position q) :
    hasLiberty position p := by
  rcases hq with ⟨s, t, hqs, hst, ht⟩
  exact ⟨s, t, hpq.trans hqs, hst, ht⟩

lemma hasLiberty_iff_of_reachable {position : Position} {p q : Point}
    (hpq : (sameColorGraph position).Reachable p q) :
    hasLiberty position p ↔ hasLiberty position q :=
  ⟨hasLiberty_of_reachable hpq.symm, hasLiberty_of_reachable hpq⟩

lemma reachable_of_color_retained {source target : Position} {p q : Point}
    (h : (sameColorGraph source).Reachable p q)
    (hkeep : ∀ r, source r = source p → target r = source r) :
    (sameColorGraph target).Reachable p q := by
  rcases h with ⟨walk⟩
  revert hkeep
  induction walk with
  | nil => intro _; exact .refl _
  | @cons u v w hadj walk ih =>
      intro hkeep
      have hcol := (sameColorGraph_adj_iff source u v).mp hadj
      have hkeepv : ∀ r, source r = source v → target r = source r :=
        fun r hr => hkeep r (hr.trans hcol.2.symm)
      have htarget : (sameColorGraph target).Adj u v := by
        apply (sameColorGraph_adj_iff target u v).mpr
        exact ⟨hcol.1, (hkeep u rfl).trans (hcol.2.trans (hkeepv v rfl).symm)⟩
      exact htarget.reachable.trans (ih hkeepv)

lemma IsSubposition.refl (position : Position) : IsSubposition position position :=
  fun _ => Or.inr rfl

lemma IsSubposition.trans {small middle large : Position}
    (hsm : IsSubposition small middle) (hml : IsSubposition middle large) :
    IsSubposition small large := by
  intro p
  rcases hsm p with h | h
  · exact Or.inl h
  · rcases hml p with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (h.trans h')

lemma IsSubposition.retained {small large : Position} (h : IsSubposition small large)
    {p : Point} (hp : small p ≠ none) : small p = large p :=
  (h p).resolve_left hp

lemma IsSubposition.empty {small large : Position} (h : IsSubposition small large)
    {p : Point} (hp : large p = none) : small p = none := by
  rcases h p with h' | h'
  · exact h'
  · exact h'.trans hp

lemma liberty_of_subposition_walk {small large : Position}
    (hsub : IsSubposition small large) {p q r : Point}
    (walk : (sameColorGraph large).Walk p q) (hqr : neighbors q r)
    (hr : small r = none) : small p ≠ none → hasLiberty small p := by
  induction walk with
  | nil =>
      intro _
      exact ⟨_, r, .refl _, hqr, hr⟩
  | @cons u v w hadj walk ih =>
      intro hu
      have hlarge := (sameColorGraph_adj_iff large u v).mp hadj
      by_cases hv : small v = none
      · exact ⟨u, v, .refl _, hlarge.1, hv⟩
      · have hsmall : small u = small v :=
          (hsub.retained hu).trans (hlarge.2.trans (hsub.retained hv).symm)
        have hsmallAdj : (sameColorGraph small).Adj u v :=
          (sameColorGraph_adj_iff small u v).mpr ⟨hlarge.1, hsmall⟩
        rcases ih hqr hv with ⟨s, t, hreach, hst, ht⟩
        exact ⟨s, t, hsmallAdj.reachable.trans hreach, hst, ht⟩

/-- Removing arbitrary stones preserves a liberty for every retained stone.
If an old path encounters a removed stone, that first removed stone is a new liberty. -/
lemma hasLiberty_of_subposition {small large : Position}
    (hsub : IsSubposition small large) {p : Point} (hp : small p ≠ none)
    (hlib : hasLiberty large p) : hasLiberty small p := by
  rcases hlib with ⟨q, r, ⟨walk⟩, hqr, hr⟩
  exact liberty_of_subposition_walk hsub walk hqr (hsub.empty hr) hp

lemma finite_of_subposition {small large : Position} (hsub : IsSubposition small large)
    (hfinite : {p : Point | large p ≠ none}.Finite) :
    {p : Point | small p ≠ none}.Finite := by
  apply hfinite.subset
  intro p hp hnone
  exact hp (hsub.empty hnone)

lemma admissible_of_subposition {small large : Position}
    (hsub : IsSubposition small large)
    (hlarge : ∀ p, large p ≠ none → hasLiberty large p) :
    ∀ p, small p ≠ none → hasLiberty small p := by
  intro p hp
  apply hasLiberty_of_subposition hsub hp
  apply hlarge p
  intro hnone
  exact hp (hsub.empty hnone)

lemma removeCaptured_eq_self {position : Position}
    (hadm : ∀ p, position p ≠ none → hasLiberty position p) (color : Bool) :
    removeCaptured position color = position := by
  classical
  funext p
  apply if_neg
  rintro ⟨hcolor, hnolib⟩
  apply hnolib (hadm p ?_)
  rw [hcolor]
  exact Option.some_ne_none color

lemma play_eq_update_of_admissible (position : Position) (color : Bool) (p : Point)
    (hp : position p = none)
    (hadm : ∀ q, Function.update position p (some color) q ≠ none →
      hasLiberty (Function.update position p (some color)) q) :
    play color p position = Function.update position p (some color) := by
  classical
  simp only [play, hp, if_pos, removeCaptured_eq_self hadm]

noncomputable def restrictPosition (target : Position) (s : Finset Point) : Position :=
  fun p => if p ∈ s then target p else none

lemma restrictPosition_subposition (target : Position) (s : Finset Point) :
    IsSubposition (restrictPosition target s) target := by
  classical
  intro p
  by_cases hp : p ∈ s
  · exact Or.inr (if_pos hp)
  · exact Or.inl (if_neg hp)

noncomputable def restrictAdmissible (target : AdmissiblePosition) (s : Finset Point) :
    AdmissiblePosition :=
  ⟨restrictPosition target.val s,
    finite_of_subposition (restrictPosition_subposition _ _) target.property.1,
    admissible_of_subposition (restrictPosition_subposition _ _) target.property.2⟩

lemma restrictPosition_empty (target : Position) :
    restrictPosition target ∅ = fun _ => none := by
  classical
  funext p
  simp [restrictPosition]

lemma restrictPosition_insert (target : Position) (s : Finset Point) (p : Point) :
    restrictPosition target (insert p s) = Function.update (restrictPosition target s) p
      (target p) := by
  classical
  funext q
  by_cases hqp : q = p
  · subst q
    simp [restrictPosition]
  · simp [restrictPosition, hqp]

lemma restriction_support_eq (target : AdmissiblePosition) :
    restrictAdmissible target target.property.1.toFinset = target := by
  classical
  apply Subtype.ext
  funext p
  by_cases hp : target.val p = none
  · simp [restrictAdmissible, restrictPosition, hp]
  · simp [restrictAdmissible, restrictPosition, hp]

end OMA.S_mo_342194

namespace OMA.S_mo_342194
noncomputable section

lemma removeCaptured_eq_self_of_ne {s : Position} {c : Bool} {p : Point}
    (h : s p ≠ some c) : removeCaptured s c p = s p := by
  simp [removeCaptured, h]

lemma removeCaptured_eq_self_of_liberty {s : Position} {c : Bool} {p : Point}
    (h : hasLiberty s p) : removeCaptured s c p = s p := by
  simp [removeCaptured, h]

lemma removeCaptured_subposition (s : Position) (c : Bool) (p : Point) :
    removeCaptured s c p = none ∨ removeCaptured s c p = s p := by
  classical
  simp only [removeCaptured]
  split_ifs <;> simp

lemma removeCaptured_eq_self_of_nonempty {s : Position} {c : Bool} {p : Point}
    (h : removeCaptured s c p ≠ none) : removeCaptured s c p = s p := by
  exact (removeCaptured_subposition s c p).resolve_left h

lemma removeCaptured_input_of_some {s : Position} {c r : Bool} {p : Point}
    (h : removeCaptured s c p = some r) : s p = some r := by
  have hn : removeCaptured s c p ≠ none := by rw [h]; simp
  exact (removeCaptured_eq_self_of_nonempty hn).symm.trans h

lemma removeCaptured_liberty_of_same {s : Position} {c : Bool} {p : Point}
    (h : removeCaptured s c p = some c) : hasLiberty s p := by
  classical
  have hs := removeCaptured_input_of_some h
  by_contra hl
  have : removeCaptured s c p = none := by simp [removeCaptured, hs, hl]
  rw [h] at this
  exact Option.some_ne_none c this

lemma removeCaptured_changed {s : Position} {c : Bool} {p : Point}
    (h : removeCaptured s c p ≠ s p) :
    s p = some c ∧ ¬ hasLiberty s p ∧ removeCaptured s c p = none := by
  classical
  by_cases hc : s p = some c ∧ ¬ hasLiberty s p
  · exact ⟨hc.1, hc.2, by simp [removeCaptured, hc]⟩
  · exact False.elim (h (by simp [removeCaptured, hc]))

lemma removeCaptured_other {s : Position} {c : Bool} {p : Point}
    (h : s p = some (!c)) : removeCaptured s c p = some (!c) := by
  apply (removeCaptured_eq_self_of_ne ?_).trans h
  rw [h]
  cases c <;> simp

lemma play_eq_self_of_occupied {s : Position} {c : Bool} {p : Point}
    (h : s p ≠ none) : play c p s = s := by
  simp [play, h]

lemma play_eq_removals_of_empty {s : Position} {c : Bool} {g : Point}
    (h : s g = none) :
    play c g s =
      removeCaptured (removeCaptured (Function.update s g (some c)) (!c)) c := by
  simp [play, h]

lemma removeCaptured_eq_none_iff (s : Position) (c : Bool) (p : Point) :
    removeCaptured s c p = none ↔ s p = none ∨ s p = some c ∧ ¬ hasLiberty s p := by
  classical
  by_cases h : s p = some c ∧ ¬ hasLiberty s p
  · simp [removeCaptured, h]
  · simp [removeCaptured, h]

lemma removeCaptured_finite {s : Position} (hs : {p : Point | s p ≠ none}.Finite)
    (c : Bool) : {p : Point | removeCaptured s c p ≠ none}.Finite := by
  apply hs.subset
  intro p hp
  change s p ≠ none
  change removeCaptured s c p ≠ none at hp
  rw [← removeCaptured_eq_self_of_nonempty hp]
  exact hp

lemma update_stone_finite {s : Position} (hs : {p : Point | s p ≠ none}.Finite)
    (c : Bool) (g : Point) :
    {p : Point | Function.update s g (some c) p ≠ none}.Finite := by
  classical
  apply (hs.insert g).subset
  intro p hp
  by_cases h : p = g
  · exact Or.inl h
  · apply Or.inr
    simpa [Function.update_of_ne h] using hp

lemma play_finite {s : Position} (hs : {p : Point | s p ≠ none}.Finite)
    (c : Bool) (g : Point) : {p : Point | play c g s p ≠ none}.Finite := by
  classical
  by_cases h : s g = none
  · rw [play_eq_removals_of_empty h]
    exact removeCaptured_finite (removeCaptured_finite (update_stone_finite hs c g) (!c)) c
  · rw [play_eq_self_of_occupied h]
    exact hs

lemma removeCaptured_isSubposition (s : Position) (c : Bool) :
    IsSubposition (removeCaptured s c) s :=
  removeCaptured_subposition s c

lemma removeCaptured_preserves_liberty {s : Position} {c : Bool} {p : Point}
    (hp : s p ≠ none) (hl : hasLiberty s p) :
    hasLiberty (removeCaptured s c) p := by
  apply hasLiberty_of_subposition (removeCaptured_isSubposition s c) _ hl
  rw [removeCaptured_eq_self_of_liberty hl]
  exact hp

lemma two_removals_admissible (s : Position) (c : Bool) :
    ∀ p, removeCaptured (removeCaptured s (!c)) c p ≠ none →
      hasLiberty (removeCaptured (removeCaptured s (!c)) c) p := by
  intro p hp
  let middle := removeCaptured s (!c)
  let final := removeCaptured middle c
  have hfinal : final p ≠ none := hp
  have hmiddle : middle p ≠ none := by
    intro h
    exact hfinal ((removeCaptured_isSubposition middle c).empty h)
  cases hcolor : final p with
  | none => exact False.elim (hfinal hcolor)
  | some r =>
      by_cases hr : r = c
      · have hl : hasLiberty middle p :=
          removeCaptured_liberty_of_same (hcolor.trans (congrArg some hr))
        exact hasLiberty_of_subposition (removeCaptured_isSubposition middle c) hfinal hl
      · have hr' : r = !c := by cases c <;> cases r <;> simp_all
        have hm : middle p = some (!c) := by
          have he := removeCaptured_eq_self_of_nonempty hfinal
          exact he.symm.trans (hcolor.trans (congrArg some hr'))
        have hl : hasLiberty s p := removeCaptured_liberty_of_same hm
        have hlm : hasLiberty middle p :=
          hasLiberty_of_subposition (removeCaptured_isSubposition s (!c)) hmiddle hl
        exact hasLiberty_of_subposition (removeCaptured_isSubposition middle c) hfinal hlm

lemma play_admissible {s : Position}
    (hs : ∀ p, s p ≠ none → hasLiberty s p) (c : Bool) (g : Point) :
    ∀ p, play c g s p ≠ none → hasLiberty (play c g s) p := by
  classical
  by_cases h : s g = none
  · rw [play_eq_removals_of_empty h]
    exact two_removals_admissible _ c
  · rw [play_eq_self_of_occupied h]
    exact hs

lemma finite_nonempty_has_liberty {s : Position}
    (hs : {p : Point | s p ≠ none}.Finite) (hne : ∃ p, s p ≠ none) :
    ∃ p, s p ≠ none ∧ hasLiberty s p := by
  obtain ⟨p, hp, hmax⟩ := Set.exists_max_image {p : Point | s p ≠ none}
    (fun p => p.1) hs hne
  let q : Point := (p.1 + 1, p.2)
  have hq : s q = none := by
    by_contra h
    have hm := hmax q h
    dsimp [q] at hm
    omega
  have hpq : neighbors p q := by
    have hsub : p.1 - (p.1 + 1) = (-1 : ℤ) := by omega
    simp [neighbors, q, hsub]
  exact ⟨p, hp, p, q, .refl _, hpq, hq⟩

lemma two_removals_nonempty {s : Position}
    (hs : {p : Point | s p ≠ none}.Finite) (hne : ∃ p, s p ≠ none) (c : Bool) :
    ∃ p, removeCaptured (removeCaptured s (!c)) c p ≠ none := by
  obtain ⟨p, hp, hl⟩ := finite_nonempty_has_liberty hs hne
  have hfirst : removeCaptured s (!c) p = s p :=
    removeCaptured_eq_self_of_liberty hl
  have hl' : hasLiberty (removeCaptured s (!c)) p :=
    removeCaptured_preserves_liberty hp hl
  refine ⟨p, ?_⟩
  rw [removeCaptured_eq_self_of_liberty hl', hfirst]
  exact hp

lemma play_nonempty (s : AdmissiblePosition) (c : Bool) (g : Point) :
    ∃ p, play c g s.val p ≠ none := by
  classical
  by_cases h : s.val g = none
  · rw [play_eq_removals_of_empty h]
    apply two_removals_nonempty (update_stone_finite s.property.1 c g) _ c
    exact ⟨g, by simp⟩
  · rw [play_eq_self_of_occupied h]
    exact ⟨g, h⟩

lemma play_ne_empty (s : AdmissiblePosition) (c : Bool) (g : Point) :
    play c g s.val ≠ fun _ => none := by
  intro h
  obtain ⟨p, hp⟩ := play_nonempty s c g
  exact hp (congrFun h p)

end
end OMA.S_mo_342194

namespace OMA.S_mo_342194

noncomputable def emptyAdmissible : AdmissiblePosition :=
  ⟨fun _ => none, by simp, by intro p hp; exact (hp rfl).elim⟩

/-- Every finite admissible target is obtained by placing only its own stones.
Every intermediate restriction is admissible, so no capture occurs in this construction. -/
theorem every_position_reachable
    (move : Bool → Point → AdmissiblePosition → AdmissiblePosition)
    (hmove : ∀ color p position, (move color p position).val = play color p position.val)
    (target : AdmissiblePosition) :
    ∃ steps : List (Bool × Point),
      steps.foldl (fun position step => move step.1 step.2 position) emptyAdmissible = target := by
  classical
  have horbit (s : Finset Point) :
      ∃ steps : List (Bool × Point),
        steps.foldl (fun position step => move step.1 step.2 position) emptyAdmissible =
          restrictAdmissible target s := by
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨[], ?_⟩
        apply Subtype.ext
        funext p
        simp [emptyAdmissible, restrictAdmissible, restrictPosition]
    | @insert p s hnot ih =>
        rcases ih with ⟨steps, hsteps⟩
        cases htp : target.val p with
        | none =>
            refine ⟨steps, hsteps.trans ?_⟩
            apply Subtype.ext
            funext q
            by_cases hqp : q = p
            · subst q
              simp [restrictAdmissible, restrictPosition, htp]
            · simp [restrictAdmissible, restrictPosition, hqp]
        | some color =>
            let current := restrictAdmissible target s
            have hempty : current.val p = none := by
              simp [current, restrictAdmissible, restrictPosition, hnot]
            have hupdate : Function.update current.val p (some color) =
                (restrictAdmissible target (insert p s)).val := by
              change Function.update (restrictPosition target.val s) p (some color) =
                restrictPosition target.val (insert p s)
              rw [restrictPosition_insert, htp]
            have hadm : ∀ q, Function.update current.val p (some color) q ≠ none →
                hasLiberty (Function.update current.val p (some color)) q := by
              rw [hupdate]
              exact (restrictAdmissible target (insert p s)).property.2
            have hstep : move color p current = restrictAdmissible target (insert p s) := by
              apply Subtype.ext
              rw [hmove, play_eq_update_of_admissible current.val color p hempty hadm, hupdate]
            refine ⟨steps ++ [(color, p)], ?_⟩
            rw [List.foldl_append]
            change move color p (steps.foldl (fun position step => move step.1 step.2 position)
              emptyAdmissible) = _
            rw [hsteps]
            exact hstep
  rcases horbit target.property.1.toFinset with ⟨steps, hsteps⟩
  exact ⟨steps, hsteps.trans (restriction_support_eq target)⟩

end OMA.S_mo_342194

namespace OMA.S_mo_342194
noncomputable section

lemma reachable_of_component_constant {source target : Position} {p q : Point}
    (h : (sameColorGraph source).Reachable p q)
    (hkeep : ∀ r, (sameColorGraph source).Reachable p r → target r = target p) :
    (sameColorGraph target).Reachable p q := by
  rcases h with ⟨walk⟩
  revert hkeep
  induction walk with
  | nil => intro _; exact .refl _
  | @cons u v w hadj walk ih =>
      intro hkeep
      have hcol := (sameColorGraph_adj_iff source u v).mp hadj
      have htargeteq : target u = target v := (hkeep v hadj.reachable).symm
      have hkeepv : ∀ r, (sameColorGraph source).Reachable v r → target r = target v :=
        fun r hr => (hkeep r (hadj.reachable.trans hr)).trans htargeteq
      have htarget : (sameColorGraph target).Adj u v :=
        (sameColorGraph_adj_iff target u v).mpr ⟨hcol.1, htargeteq⟩
      exact htarget.reachable.trans (ih hkeepv)

lemma removeCaptured_empty_adj_eq {s : Position} {c : Bool} {p q : Point}
    (h : (sameColorGraph (removeCaptured s c)).Adj p q)
    (hp : removeCaptured s c p = none) : s p = s q := by
  have hadj := (sameColorGraph_adj_iff _ p q).mp h
  have hq : removeCaptured s c q = none := hadj.2.symm.trans hp
  rcases (removeCaptured_eq_none_iff s c p).mp hp with hp0 | ⟨hpc, hpl⟩
  · rcases (removeCaptured_eq_none_iff s c q).mp hq with hq0 | ⟨hqc, hql⟩
    · exact hp0.trans hq0.symm
    · exact False.elim (hql ⟨q, p, .refl _, neighbors_symm hadj.1, hp0⟩)
  · rcases (removeCaptured_eq_none_iff s c q).mp hq with hq0 | ⟨hqc, _⟩
    · exact False.elim (hpl ⟨p, q, .refl _, hadj.1, hq0⟩)
    · exact hpc.trans hqc.symm

lemma removeCaptured_empty_reachable_eq {s : Position} {c : Bool} {p q : Point}
    (h : (sameColorGraph (removeCaptured s c)).Reachable p q)
    (hp : removeCaptured s c p = none) : s p = s q := by
  rcases h with ⟨walk⟩
  revert hp
  induction walk with
  | nil => intro _; rfl
  | @cons u v w hadj walk ih =>
      intro hu
      have hv : removeCaptured s c v = none :=
        ((sameColorGraph_adj_iff _ u v).mp hadj).2.symm.trans hu
      exact (removeCaptured_empty_adj_eq hadj hu).trans (ih hv)

lemma removeCaptured_removed_reachable {s : Position} {c : Bool} {p q : Point}
    (h : (sameColorGraph s).Reachable p q) (hp : s p = some c)
    (hl : ¬ hasLiberty s p) :
    (sameColorGraph (removeCaptured s c)).Reachable p q := by
  apply reachable_of_component_constant h
  intro r hr
  have hrc : s r = some c := (reachable_color_eq hr).symm.trans hp
  have hrl : ¬ hasLiberty s r := fun hlib => hl (hasLiberty_of_reachable hr hlib)
  simp [removeCaptured, hp, hl, hrc, hrl]

lemma update_retains_occupied {s : Position} {g p : Point} {v : Option Bool}
    (hg : s g = none) (hp : s p ≠ none) : Function.update s g v p = s p := by
  classical
  apply Function.update_of_ne
  intro h
  subst p
  exact hp hg

lemma update_other_color_input {s : Position} {c : Bool} {g p : Point}
    (h : Function.update s g (some c) p = some (!c)) : s p = some (!c) := by
  classical
  by_cases hp : p = g
  · subst p
    cases c <;> simp at h
  · simpa [Function.update_of_ne hp] using h

lemma placed_opponent_reachable {s : Position} {c : Bool} {g p q : Point}
    (hg : s g = none) (hp : s p = some (!c))
    (h : (sameColorGraph s).Reachable p q) :
    (sameColorGraph (Function.update s g (some c))).Reachable p q := by
  apply reachable_of_color_retained h
  intro r hr
  apply update_retains_occupied hg
  rw [hr, hp]
  simp

lemma opponent_deleted_hits_neighbor {s : Position} {c : Bool} {g p : Point}
    (hg : s g = none) (hs : ∀ r, s r ≠ none → hasLiberty s r)
    (hp : Function.update s g (some c) p = some (!c))
    (hl : ¬ hasLiberty (Function.update s g (some c)) p) :
    ∃ q, neighbors g q ∧ s q = some (!c) ∧
      (sameColorGraph (removeCaptured (Function.update s g (some c)) (!c))).Reachable p q := by
  classical
  have hsp : s p = some (!c) := update_other_color_input hp
  have hspne : s p ≠ none := by rw [hsp]; simp
  obtain ⟨q, r, hpq, hqr, hr⟩ := hs p hspne
  have hpq' := placed_opponent_reachable hg hsp hpq
  have hrg : r = g := by
    by_contra hne
    apply hl
    refine ⟨q, r, hpq', hqr, ?_⟩
    simpa [Function.update_of_ne hne] using hr
  subst r
  have hsq : s q = some (!c) := (reachable_color_eq hpq).symm.trans hsp
  exact ⟨q, neighbors_symm hqr, hsq,
    removeCaptured_removed_reachable hpq' hp hl⟩

lemma placed_then_opponent_keeps_own {s : Position} {c : Bool} {g p : Point}
    (hg : s g = none) (hp : s p = some c) :
    removeCaptured (Function.update s g (some c)) (!c) p = some c := by
  have ha : Function.update s g (some c) p = some c :=
    (update_retains_occupied hg (by rw [hp]; simp)).trans hp
  simpa using (removeCaptured_other (c := !c) (by simpa using ha))

lemma placed_then_opponent_at (s : Position) (c : Bool) (g : Point) :
    removeCaptured (Function.update s g (some c)) (!c) g = some c := by
  apply (removeCaptured_eq_self_of_ne ?_).trans (by simp)
  cases c <;> simp

lemma own_liberty_or_connected {s : Position} {c : Bool} {g p : Point}
    (hg : s g = none) (hs : ∀ r, s r ≠ none → hasLiberty s r)
    (hp : removeCaptured (Function.update s g (some c)) (!c) p = some c) :
    hasLiberty (removeCaptured (Function.update s g (some c)) (!c)) p ∨
      (sameColorGraph (removeCaptured (Function.update s g (some c)) (!c))).Reachable p g := by
  classical
  let middle := removeCaptured (Function.update s g (some c)) (!c)
  by_cases hpg : p = g
  · subst p
    exact Or.inr (.refl _)
  have ha : Function.update s g (some c) p = some c := removeCaptured_input_of_some hp
  have hsp : s p = some c := by simpa [Function.update_of_ne hpg] using ha
  have hspne : s p ≠ none := by rw [hsp]; simp
  obtain ⟨q, r, hpq, hqr, hr⟩ := hs p hspne
  have hpq' : (sameColorGraph middle).Reachable p q := by
    apply reachable_of_color_retained hpq
    intro v hv
    have hsv : s v = some c := hv.trans hsp
    exact (placed_then_opponent_keeps_own hg hsv).trans hsv.symm
  by_cases hrg : r = g
  · subst r
    apply Or.inr
    apply hpq'.trans
    apply SimpleGraph.Adj.reachable
    apply (sameColorGraph_adj_iff middle q g).mpr
    refine ⟨hqr, ?_⟩
    have hq : s q = some c := (reachable_color_eq hpq).symm.trans hsp
    exact (placed_then_opponent_keeps_own hg hq).trans (placed_then_opponent_at s c g).symm
  · apply Or.inl
    refine ⟨q, r, hpq', hqr, ?_⟩
    apply (removeCaptured_isSubposition (Function.update s g (some c)) (!c)).empty
    simpa [Function.update_of_ne hrg] using hr

end
end OMA.S_mo_342194

namespace OMA.S_mo_342194
noncomputable section

lemma own_stage_eq_self_of_survive {s : Position} {c : Bool} {g : Point}
    (hg : s g = none) (hs : ∀ p, s p ≠ none → hasLiberty s p)
    (h : removeCaptured (removeCaptured (Function.update s g (some c)) (!c)) c g = some c) :
    removeCaptured (removeCaptured (Function.update s g (some c)) (!c)) c =
      removeCaptured (Function.update s g (some c)) (!c) := by
  have hlg : hasLiberty (removeCaptured (Function.update s g (some c)) (!c)) g :=
    removeCaptured_liberty_of_same h
  funext p
  by_contra hp
  obtain ⟨hpc, hpl, _⟩ := removeCaptured_changed hp
  rcases own_liberty_or_connected hg hs hpc with hlib | hconn
  · exact hpl hlib
  · exact hpl (hasLiberty_of_reachable hconn hlg)

lemma opponent_stage_eq_self_of_suicide {s : Position} {c : Bool} {g : Point}
    (hg : s g = none) (hs : ∀ p, s p ≠ none → hasLiberty s p)
    (h : removeCaptured (removeCaptured (Function.update s g (some c)) (!c)) c g = none) :
    removeCaptured (Function.update s g (some c)) (!c) = Function.update s g (some c) := by
  let middle := removeCaptured (Function.update s g (some c)) (!c)
  have hno : ¬ hasLiberty middle g := by
    intro hl
    have he : removeCaptured middle c g = some c :=
      (removeCaptured_eq_self_of_liberty hl).trans (placed_then_opponent_at s c g)
    have : (some c : Option Bool) = none := he.symm.trans h
    exact Option.some_ne_none c this
  funext p
  by_contra hp
  obtain ⟨hpc, hpl, hpnone⟩ := removeCaptured_changed hp
  obtain ⟨q, hnear, _, hreach⟩ := opponent_deleted_hits_neighbor hg hs hpc hpl
  apply hno
  refine ⟨g, q, .refl _, hnear, ?_⟩
  exact (reachable_color_eq hreach).symm.trans hpnone

lemma own_deleted_connected {s : Position} {c : Bool} {g p : Point}
    (hg : s g = none) (hs : ∀ r, s r ≠ none → hasLiberty s r)
    (hp : removeCaptured (Function.update s g (some c)) (!c) p = some c)
    (hl : ¬ hasLiberty (removeCaptured (Function.update s g (some c)) (!c)) p) :
    (sameColorGraph (removeCaptured (Function.update s g (some c)) (!c))).Reachable p g :=
  (own_liberty_or_connected hg hs hp).resolve_left hl

lemma removeCaptured_injective_of_hits {a b : Position} {c : Bool} {Q : Point → Prop}
    (hout : removeCaptured a c = removeCaptured b c)
    (hprobe : ∀ q, Q q → a q = b q)
    (ha : ∀ p, a p = some c → ¬ hasLiberty a p →
      ∃ q, Q q ∧ a q = some c ∧ (sameColorGraph (removeCaptured a c)).Reachable p q)
    (hb : ∀ p, b p = some c → ¬ hasLiberty b p →
      ∃ q, Q q ∧ b q = some c ∧ (sameColorGraph (removeCaptured b c)).Reachable p q) :
    a = b := by
  funext p
  by_cases hp : removeCaptured a c p = none
  · have hp' : removeCaptured b c p = none := by rw [← hout]; exact hp
    rcases (removeCaptured_eq_none_iff a c p).mp hp with ha0 | ⟨hac, hal⟩
    · rcases (removeCaptured_eq_none_iff b c p).mp hp' with hb0 | ⟨hbc, hbl⟩
      · exact ha0.trans hb0.symm
      · obtain ⟨q, hq, hbq, hpath⟩ := hb p hbc hbl
        have hpath' : (sameColorGraph (removeCaptured a c)).Reachable p q := by
          rw [hout]
          exact hpath
        have he := removeCaptured_empty_reachable_eq hpath' hp
        have haq : a q = some c := (hprobe q hq).trans hbq
        exact he.trans (haq.trans hbc.symm)
    · obtain ⟨q, hq, haq, hpath⟩ := ha p hac hal
      have hpath' : (sameColorGraph (removeCaptured b c)).Reachable p q := by
        rw [← hout]
        exact hpath
      have he := removeCaptured_empty_reachable_eq hpath' hp'
      have hbq : b q = some c := (hprobe q hq).symm.trans haq
      exact hac.trans (hbq.symm.trans he.symm)
  · have hp' : removeCaptured b c p ≠ none := by rw [← hout]; exact hp
    exact (removeCaptured_eq_self_of_nonempty hp).symm.trans
      ((congrFun hout p).trans (removeCaptured_eq_self_of_nonempty hp'))

lemma removeCaptured_injective_of_connected {a b : Position} {c : Bool} {g : Point}
    (hout : removeCaptured a c = removeCaptured b c)
    (hag : a g = some c) (hbg : b g = some c)
    (ha : ∀ p, a p = some c → ¬ hasLiberty a p → (sameColorGraph a).Reachable p g)
    (hb : ∀ p, b p = some c → ¬ hasLiberty b p → (sameColorGraph b).Reachable p g) :
    a = b := by
  apply removeCaptured_injective_of_hits (Q := fun p => p = g) hout
  · intro q hq
    subst q
    exact hag.trans hbg.symm
  · intro p hpc hpl
    exact ⟨g, rfl, hag, removeCaptured_removed_reachable (ha p hpc hpl) hpc hpl⟩
  · intro p hpc hpl
    exact ⟨g, rfl, hbg, removeCaptured_removed_reachable (hb p hpc hpl) hpc hpl⟩

lemma play_local_injective {s t : Position} {c : Bool} {g : Point}
    (hs : ∀ p, s p ≠ none → hasLiberty s p)
    (ht : ∀ p, t p ≠ none → hasLiberty t p)
    (hout : play c g s = play c g t)
    (hg : s g = t g) (hnear : ∀ q, neighbors g q → s q = t q) : s = t := by
  classical
  by_cases hsg : s g = none
  · have htg : t g = none := hg.symm.trans hsg
    have hout' :
        removeCaptured (removeCaptured (Function.update s g (some c)) (!c)) c =
          removeCaptured (removeCaptured (Function.update t g (some c)) (!c)) c := by
      simpa only [play_eq_removals_of_empty hsg, play_eq_removals_of_empty htg] using hout
    let a := Function.update s g (some c)
    let b := Function.update t g (some c)
    have hag : a g = some c := by simp [a]
    have hbg : b g = some c := by simp [b]
    by_cases hsurv : removeCaptured (removeCaptured a (!c)) c g = some c
    · have hsurv' : removeCaptured (removeCaptured b (!c)) c g = some c := by
        rw [← hout']; exact hsurv
      have haself := own_stage_eq_self_of_survive hsg hs hsurv
      have hbself := own_stage_eq_self_of_survive htg ht hsurv'
      have he : removeCaptured a (!c) = removeCaptured b (!c) :=
        haself.symm.trans (hout'.trans hbself)
      have hab : a = b := by
        apply removeCaptured_injective_of_hits (Q := neighbors g) he
        · intro q hq
          by_cases hqg : q = g
          · subst q; exact hag.trans hbg.symm
          · simpa [a, b, Function.update_of_ne hqg] using hnear q hq
        · intro p hpc hpl
          obtain ⟨q, hq, hsq, hpath⟩ := opponent_deleted_hits_neighbor hsg hs hpc hpl
          exact ⟨q, hq, (update_retains_occupied hsg (by rw [hsq]; simp)).trans hsq, hpath⟩
        · intro p hpc hpl
          obtain ⟨q, hq, htq, hpath⟩ := opponent_deleted_hits_neighbor htg ht hpc hpl
          exact ⟨q, hq, (update_retains_occupied htg (by rw [htq]; simp)).trans htq, hpath⟩
      funext p
      by_cases hpg : p = g
      · subst p; exact hg
      · have heq := congrFun hab p
        simpa [a, b, Function.update_of_ne hpg] using heq
    · have houtg : removeCaptured (removeCaptured a (!c)) c g = none := by
        rcases removeCaptured_subposition (removeCaptured a (!c)) c g with h | h
        · exact h
        · exact False.elim (hsurv (h.trans (placed_then_opponent_at s c g)))
      have houtg' : removeCaptured (removeCaptured b (!c)) c g = none := by
        rw [← hout']; exact houtg
      have haself := opponent_stage_eq_self_of_suicide hsg hs houtg
      have hbself := opponent_stage_eq_self_of_suicide htg ht houtg'
      have hea : removeCaptured a (!c) = a := haself
      have heb : removeCaptured b (!c) = b := hbself
      have he : removeCaptured a c = removeCaptured b c := by
        simpa only [haself, hbself] using hout'
      have hab : a = b := by
        apply removeCaptured_injective_of_connected he hag hbg
        · intro p hpc hpl
          have hpc' : removeCaptured a (!c) p = some c := by rw [hea]; exact hpc
          have hpl' : ¬ hasLiberty (removeCaptured a (!c)) p := by rw [hea]; exact hpl
          have hc := own_deleted_connected hsg hs hpc' hpl'
          change (sameColorGraph (removeCaptured a (!c))).Reachable p g at hc
          simpa only [hea] using hc
        · intro p hpc hpl
          have hpc' : removeCaptured b (!c) p = some c := by rw [heb]; exact hpc
          have hpl' : ¬ hasLiberty (removeCaptured b (!c)) p := by rw [heb]; exact hpl
          have hc := own_deleted_connected htg ht hpc' hpl'
          change (sameColorGraph (removeCaptured b (!c))).Reachable p g at hc
          simpa only [heb] using hc
      funext p
      by_cases hpg : p = g
      · subst p; exact hg
      · have heq := congrFun hab p
        simpa [a, b, Function.update_of_ne hpg] using heq
  · have htg : t g ≠ none := by rw [← hg]; exact hsg
    simpa only [play_eq_self_of_occupied hsg, play_eq_self_of_occupied htg] using hout

end
end OMA.S_mo_342194

namespace OMA.S_mo_342194

lemma neighbors_four_cases {g q : Point} (h : neighbors g q) :
    q = (g.1 + 1, g.2) ∨ q = (g.1 - 1, g.2) ∨
      q = (g.1, g.2 + 1) ∨ q = (g.1, g.2 - 1) := by
  have hcases :
      ((g.1 - q.1).natAbs = 1 ∧ (g.2 - q.2).natAbs = 0) ∨
      ((g.1 - q.1).natAbs = 0 ∧ (g.2 - q.2).natAbs = 1) := by
    unfold neighbors at h
    omega
  rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hy0 := Int.natAbs_eq_zero.mp hy
    rcases Int.natAbs_eq_iff.mp hx with hx | hx
    · right; left
      apply Prod.ext <;> dsimp at * <;> omega
    · left
      apply Prod.ext <;> dsimp at * <;> omega
  · have hx0 := Int.natAbs_eq_zero.mp hx
    rcases Int.natAbs_eq_iff.mp hy with hy | hy
    · right; right; right
      apply Prod.ext <;> dsimp at * <;> omega
    · right; right; left
      apply Prod.ext <;> dsimp at * <;> omega

def localPoint (g : Point) (i : Fin 5) : Point :=
  match i.val with
  | 0 => g
  | 1 => (g.1 + 1, g.2)
  | 2 => (g.1 - 1, g.2)
  | 3 => (g.1, g.2 + 1)
  | _ => (g.1, g.2 - 1)

def localCode (g : Point) (position : AdmissiblePosition) : Fin 5 → Option Bool :=
  fun i => position.val (localPoint g i)

lemma localCode_eq_center {g : Point} {s t : AdmissiblePosition}
    (h : localCode g s = localCode g t) : s.val g = t.val g := by
  exact congrFun h 0

lemma localCode_eq_neighbors {g q : Point} {s t : AdmissiblePosition}
    (h : localCode g s = localCode g t) (hq : neighbors g q) : s.val q = t.val q := by
  rcases neighbors_four_cases hq with hq | hq | hq | hq
  · subst q
    exact congrFun h 1
  · subst q
    exact congrFun h 2
  · subst q
    exact congrFun h 3
  · subst q
    exact congrFun h 4

/-- A local-code injection on each fiber gives a uniform finite-fragment bound.
The codomain has3^5=243 elements, independently of the position support size. -/
lemma localCode_fiber_card_le [DecidableEq AdmissiblePosition] (g : Point)
    (move : AdmissiblePosition → AdmissiblePosition)
    (hinj : ∀ s t, move s = move t → localCode g s = localCode g t → s = t)
    (s : Finset AdmissiblePosition) (b : AdmissiblePosition) :
    (s.filter (fun a => move a = b)).card ≤ 243 := by
  classical
  have hbound : (s.filter (fun a => move a = b)).card ≤
      (Finset.univ : Finset (Fin 5 → Option Bool)).card := by
    apply Finset.card_le_card_of_injOn (localCode g)
    · intro a _
      exact Finset.mem_univ _
    · intro a ha a' ha' hcode
      apply hinj a a' _ hcode
      exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp ha').2.symm
  have hcard : (Finset.univ : Finset (Fin 5 → Option Bool)).card = 243 := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option,
      Fintype.card_bool, Fintype.card_fin]
    decide
  exact hcard ▸ hbound

end OMA.S_mo_342194

namespace OMA.S_mo_342194

noncomputable def goMove (color : Bool) (p : Point) (position : AdmissiblePosition) :
    AdmissiblePosition :=
  ⟨play color p position.val, play_finite position.property.1 color p,
    play_admissible position.property.2 color p⟩

lemma goMove_local_injective {color : Bool} {p : Point} {s t : AdmissiblePosition}
    (hout : goMove color p s = goMove color p t)
    (hcode : localCode p s = localCode p t) : s = t := by
  apply Subtype.ext
  apply play_local_injective s.property.2 t.property.2
    (congrArg Subtype.val hout) (localCode_eq_center hcode)
  intro q hq
  exact localCode_eq_neighbors hcode hq

lemma goMove_finiteFiberBound [DecidableEq AdmissiblePosition] (color : Bool) (p : Point) :
    GoFiniteFiberL2.FiniteFiberBound (goMove color p) 243 := by
  classical
  intro s b
  exact localCode_fiber_card_le p (goMove color p)
    (fun _ _ hout hcode => goMove_local_injective hout hcode) s b

lemma goMove_ne_empty (color : Bool) (p : Point) (position : AdmissiblePosition) :
    goMove color p position ≠ emptyAdmissible := by
  intro h
  exact play_ne_empty position color p (congrArg Subtype.val h)

lemma goMove_fixed_nonempty (position : AdmissiblePosition)
    (hne : position ≠ emptyAdmissible) :
    ∃ i : Bool × Point, goMove i.1 i.2 position = position := by
  classical
  have hex : ∃ p, position.val p ≠ none := by
    by_contra h
    apply hne
    apply Subtype.ext
    funext p
    by_contra hp
    exact h ⟨p, hp⟩
  obtain ⟨p, hp⟩ := hex
  refine ⟨(false, p), ?_⟩
  apply Subtype.ext
  exact play_eq_self_of_occupied hp

lemma goMove_build (position : AdmissiblePosition) :
    ∃ steps : List (Bool × Point),
      steps.foldr (fun step current => goMove step.1 step.2 current)
        emptyAdmissible = position := by
  obtain ⟨steps, hsteps⟩ := every_position_reachable goMove (fun _ _ _ => rfl) position
  refine ⟨steps.reverse, ?_⟩
  simpa only [List.foldr_reverse] using hsteps

/-- Exact original scalar-commutant statement, once the preceding concrete
Go fiber proof and generic Hilbert package have passed their separate audits. -/
theorem proof_main :
    ∃ (move : Bool → Point → AdmissiblePosition → AdmissiblePosition)
      (operators : Bool → Point → (PositionHilbert →L[ℂ] PositionHilbert)),
      (∀ color p position, (move color p position).val = play color p position.val) ∧
      (∀ color p position,
        operators color p (basisVector position) = basisVector (move color p position)) ∧
      ∀ candidate : PositionHilbert →L[ℂ] PositionHilbert,
        (∀ color p, Commute candidate (operators color p) ∧
          Commute candidate (operators color p).adjoint) →
        ∃ scalar : ℂ, candidate = scalar • ContinuousLinearMap.id ℂ PositionHilbert := by
  classical
  let f : (Bool × Point) → AdmissiblePosition → AdmissiblePosition :=
    fun i position => goMove i.1 i.2 position
  obtain ⟨U, hU, hscalar⟩ := GoVacuumCommutant.exists_operators_scalar_commutant
    f emptyAdmissible 243
    (fun i => goMove_finiteFiberBound i.1 i.2)
    (fun i position => goMove_ne_empty i.1 i.2 position)
    goMove_fixed_nonempty goMove_build
  refine ⟨goMove, (fun color p => U (color, p)), ?_, ?_, ?_⟩
  · exact fun _ _ _ => rfl
  · intro color p position
    exact hU (color, p) position
  · intro candidate hcomm
    exact hscalar candidate (fun i => hcomm i.1 i.2)

end OMA.S_mo_342194

theorem OMA.solution : type_of% @OMA.S_mo_342194.main :=
  _root_.OMA.S_mo_342194.proof_main
