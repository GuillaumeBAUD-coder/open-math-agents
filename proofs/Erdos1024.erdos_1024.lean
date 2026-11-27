import FormalConjectures.ErdosProblems.«1024»

-- Problem: Erdős Problem 1024
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1024.lean (declaration Erdos1024.erdos_1024)
-- Credit: @koolkao (the owner of the agent is credited as the solver)
--
-- Ported proof. The mathematics is due to K. T. Phelps and V. Rödl (Ars Combin. 1986). The Lean
-- formalization (authors listed there as Codex / GPT-5.6 Sol) is from github.com/plby/lean-proofs,
-- src/latest/ErdosProblems/Erdos1024 (Apache-2.0). Changes here: the 14 modules flattened into one file in
-- import order, namespace renamed to OMA1024, and a bridge from the upstream definition
-- Hypergraph.linearIndependenceNumber to the ported guaranteedIndependence added at the end.
-- ===== from plby module ErdosProblems.Erdos1024.LocalLemma =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

This is a cardinality-level local lemma for a uniform finite probability
space.  The hypothesis is phrased for the actual neighbor set occurring in
each conditioning family.  That slightly strengthened form avoids any
symmetry assumption on `dep` and is exactly what the two-event-type
application for Erdős Problem 1024 verifies.
-/

open scoped BigOperators

namespace OMA1024
namespace LocalLemma

variable {Omega ι : Type*}

/-- Uniform probability on a nonempty finite type. -/
noncomputable def uniformProbability [Fintype Omega] (s : Finset Omega) : ℝ :=
  (s.card : ℝ) / Fintype.card Omega

/-- Outcomes avoiding every event indexed by `S`. -/
def avoiding [Fintype Omega] [DecidableEq Omega] [DecidableEq ι]
    (event : ι → Finset Omega) (S : Finset ι) : Finset Omega :=
  Finset.univ.filter fun omega ↦ ∀ i ∈ S, omega ∉ event i

section Elementary

variable [Fintype Omega] [Nonempty Omega]

lemma card_pos : 0 < (Fintype.card Omega : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma uniformProbability_nonneg (s : Finset Omega) :
    0 ≤ uniformProbability s := by
  exact div_nonneg (by positivity) card_pos.le

lemma uniformProbability_mono {s t : Finset Omega} (hst : s ⊆ t) :
    uniformProbability s ≤ uniformProbability t := by
  unfold uniformProbability
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Finset.card_le_card hst) card_pos.le

lemma uniformProbability_univ :
    uniformProbability (Finset.univ : Finset Omega) = 1 := by
  simp [uniformProbability, ne_of_gt card_pos]

lemma uniformProbability_pos_iff_nonempty (s : Finset Omega) :
    0 < uniformProbability s ↔ s.Nonempty := by
  constructor
  · intro h
    rw [uniformProbability, div_pos_iff] at h
    rcases h with h | h
    · exact Finset.card_pos.mp (by exact_mod_cast h.1)
    · exfalso
      linarith [card_pos (Omega := Omega)]
  · intro hs
    exact div_pos (by exact_mod_cast hs.card_pos) card_pos

end Elementary

section Avoiding

variable [Fintype Omega] [DecidableEq Omega]
variable [DecidableEq ι]
variable (event : ι → Finset Omega)

@[simp] lemma avoiding_empty : avoiding event ∅ = Finset.univ := by
  ext
  simp [avoiding]

lemma avoiding_mono {S T : Finset ι} (hST : S ⊆ T) :
    avoiding event T ⊆ avoiding event S := by
  intro omega homega
  simp only [avoiding, Finset.mem_filter, Finset.mem_univ, true_and] at homega ⊢
  intro i hi
  exact homega i (hST hi)

lemma avoiding_insert (i : ι) (S : Finset ι) :
    avoiding event (insert i S) = avoiding event S \ event i := by
  ext omega
  simp [avoiding, and_comm]

lemma avoiding_partition (i : ι) (S : Finset ι) :
    avoiding event S =
      avoiding event (insert i S) ∪ (event i ∩ avoiding event S) := by
  ext omega
  by_cases h : omega ∈ event i <;> simp [avoiding, h]

lemma uniformProbability_avoiding_partition (i : ι) (S : Finset ι) :
    uniformProbability (avoiding event S) =
      uniformProbability (avoiding event (insert i S)) +
        uniformProbability (event i ∩ avoiding event S) := by
  rw [congrArg uniformProbability (avoiding_partition event i S)]
  unfold uniformProbability
  rw [Finset.card_union_of_disjoint]
  · push_cast
    ring
  · rw [Finset.disjoint_left]
    intro omega homegaAvoid homegaEvent
    rw [avoiding_insert] at homegaAvoid
    exact (Finset.mem_sdiff.mp homegaAvoid).2 (Finset.mem_inter.mp homegaEvent).1

end Avoiding

section Asymmetric

variable [Fintype Omega] [Nonempty Omega] [DecidableEq Omega]
variable [Finite ι] [DecidableEq ι]

/--
Finite asymmetric Lovász local lemma.

The hypothesis `h_event` is the usual local-lemma product criterion, stated
for the neighbors of `i` actually present in an arbitrary conditioning set
`S`.  `h_indep` says that event `i` is independent of simultaneous avoidance
of any collection of non-neighbors.
-/
theorem exists_avoiding_of_asymmetric
    (event : ι → Finset Omega) (dep : ι → ι → Prop) [DecidableRel dep]
    (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (h_event : ∀ i (S : Finset ι), i ∉ S →
      uniformProbability (event i) ≤
        x i * ∏ j ∈ S.filter (dep i), (1 - x j))
    (h_indep : ∀ i S, (∀ j ∈ S, ¬ dep i j) →
      uniformProbability (event i ∩ avoiding event S) =
        uniformProbability (event i) * uniformProbability (avoiding event S)) :
    ∃ omega : Omega, ∀ i, omega ∉ event i := by
  let := Fintype.ofFinite ι
  have hfactor0 (i : ι) : 0 ≤ 1 - x i := sub_nonneg.mpr (hx1 i).le
  /- The standard inductive conditional estimate, written without division
  so it remains meaningful before positivity of all denominators is known. -/
  have conditional : ∀ S : Finset ι, ∀ i ∉ S,
      uniformProbability (event i ∩ avoiding event S) ≤
        x i * uniformProbability (avoiding event S) := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      intro i hiS
      let N : Finset ι := S.filter (dep i)
      let F : Finset ι := S.filter fun j ↦ ¬ dep i j
      have hNF : S = N ∪ F := by
        ext j
        by_cases hj : dep i j <;> simp [N, F, hj]
      have hNsub : N ⊆ S := Finset.filter_subset _ _
      have hFsub : F ⊆ S := Finset.filter_subset _ _
      have hNFdisj : Disjoint N F := by
        rw [Finset.disjoint_left]
        intro j hjN hjF
        exact (Finset.mem_filter.mp hjF).2 (Finset.mem_filter.mp hjN).2
      have hF_nonNeighbor (j : ι) (hj : j ∈ F) : ¬ dep i j :=
        (Finset.mem_filter.mp hj).2
      have havoidSub : avoiding event S ⊆ avoiding event F :=
        avoiding_mono event hFsub
      have heventSub : event i ∩ avoiding event S ⊆
          event i ∩ avoiding event F :=
        Finset.inter_subset_inter (fun _ hmem ↦ hmem) havoidSub
      have hnum : uniformProbability (event i ∩ avoiding event S) ≤
          uniformProbability (event i) * uniformProbability (avoiding event F) := by
        calc
          uniformProbability (event i ∩ avoiding event S) ≤
              uniformProbability (event i ∩ avoiding event F) :=
            uniformProbability_mono heventSub
          _ = uniformProbability (event i) * uniformProbability (avoiding event F) :=
            h_indep i F hF_nonNeighbor
      /- Successively insert the neighbors in `T`.  At every insertion the
      strong induction hypothesis loses at most the corresponding factor
      `1 - x j`. -/
      have hproduct : ∀ T : Finset ι, T ⊆ N →
          (∏ j ∈ T, (1 - x j)) * uniformProbability (avoiding event F) ≤
            uniformProbability (avoiding event (T ∪ F)) := by
        intro T hTN
        induction T using Finset.induction with
        | empty =>
          simp
        | @insert j T hjT hT =>
          have hjN : j ∈ N := hTN (Finset.mem_insert_self j T)
          have hTN' : T ⊆ N := fun k hk ↦ hTN (Finset.mem_insert_of_mem hk)
          have hjF : j ∉ F := by
            exact fun h ↦ Finset.disjoint_left.mp hNFdisj hjN h
          have hjTF : j ∉ T ∪ F := by simp [hjT, hjF]
          have hTFsub : T ∪ F ⊆ S := by
            intro k hk
            rcases Finset.mem_union.mp hk with hk | hk
            · exact hNsub (hTN' hk)
            · exact hFsub hk
          have hstrictTF : T ∪ F ⊂ S := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨hTFsub, ?_⟩
            intro heq
            apply hjTF
            rw [heq]
            exact hNsub hjN
          have hcond := ih (T ∪ F) hstrictTF j hjTF
          have hstep : (1 - x j) * uniformProbability (avoiding event (T ∪ F)) ≤
              uniformProbability (avoiding event (insert j (T ∪ F))) := by
            have hpart := uniformProbability_avoiding_partition event j (T ∪ F)
            nlinarith
          calc
            (∏ k ∈ insert j T, (1 - x k)) *
                uniformProbability (avoiding event F) =
                (1 - x j) *
                  ((∏ k ∈ T, (1 - x k)) *
                    uniformProbability (avoiding event F)) := by
              rw [Finset.prod_insert hjT]
              ring
            _ ≤ (1 - x j) * uniformProbability (avoiding event (T ∪ F)) :=
              mul_le_mul_of_nonneg_left (hT hTN') (hfactor0 j)
            _ ≤ uniformProbability (avoiding event (insert j (T ∪ F))) := hstep
            _ = uniformProbability (avoiding event (insert j T ∪ F)) := by
              congr 2
              ext k
              simp
      have hprodN : (∏ j ∈ N, (1 - x j)) *
          uniformProbability (avoiding event F) ≤
            uniformProbability (avoiding event S) := by
        simpa [hNF] using hproduct N (fun _ hmem ↦ hmem)
      have hevent := h_event i S hiS
      change uniformProbability (event i) ≤
        x i * ∏ j ∈ N, (1 - x j) at hevent
      calc
        uniformProbability (event i ∩ avoiding event S) ≤
            uniformProbability (event i) * uniformProbability (avoiding event F) := hnum
        _ ≤ (x i * ∏ j ∈ N, (1 - x j)) *
              uniformProbability (avoiding event F) := by
            exact mul_le_mul_of_nonneg_right hevent
              (uniformProbability_nonneg (avoiding event F))
        _ = x i * ((∏ j ∈ N, (1 - x j)) *
              uniformProbability (avoiding event F)) := by ring
        _ ≤ x i * uniformProbability (avoiding event S) :=
          mul_le_mul_of_nonneg_left hprodN (hx0 i)
  have avoiding_pos : ∀ S : Finset ι,
      0 < uniformProbability (avoiding event S) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      rw [avoiding_empty, uniformProbability_univ]
      norm_num
    | @insert i S hi ih =>
      have hcond := conditional S i hi
      have hpart := uniformProbability_avoiding_partition event i S
      have hfactor : 0 < 1 - x i := sub_pos.mpr (hx1 i)
      nlinarith
  have hall := avoiding_pos (Finset.univ : Finset ι)
  have hnonempty : (avoiding event (Finset.univ : Finset ι)).Nonempty :=
    (uniformProbability_pos_iff_nonempty _).mp hall
  obtain ⟨omega, homega⟩ := hnonempty
  refine ⟨omega, fun i ↦ ?_⟩
  simp only [avoiding, Finset.mem_filter, Finset.mem_univ, true_and] at homega
  exact homega i trivial

end Asymmetric

end LocalLemma
end OMA1024


-- ===== from plby module ErdosProblems.Erdos1024.Cylinder =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

Events depending on disjoint coordinate sets are independent under the
uniform distribution on a finite function space.  The proof is an explicit
coordinate-mixing bijection, so no measure-theoretic product-space machinery
is needed.
-/

namespace OMA1024
namespace Cylinder

open LocalLemma

variable {Coordinate Value ι : Type*}

/-- Use `left` on coordinates in `S` and `right` elsewhere. -/
def mix [DecidableEq Coordinate] (S : Finset Coordinate)
    (left right : Coordinate → Value) : Coordinate → Value :=
  fun c ↦ if c ∈ S then left c else right c

@[simp] lemma mix_apply_of_mem [DecidableEq Coordinate]
    {S : Finset Coordinate} {left right : Coordinate → Value}
    {c : Coordinate} (hc : c ∈ S) :
    mix S left right c = left c := by
  simp [mix, hc]

@[simp] lemma mix_apply_of_not_mem [DecidableEq Coordinate]
    {S : Finset Coordinate} {left right : Coordinate → Value}
    {c : Coordinate} (hc : c ∉ S) :
    mix S left right c = right c := by
  simp [mix, hc]

/-- Membership of `A` is determined by the coordinates in `S`. -/
def DependsOn [DecidableEq Coordinate] [DecidableEq (Coordinate → Value)]
    (A : Finset (Coordinate → Value)) (S : Finset Coordinate) : Prop :=
  ∀ f g, (∀ c ∈ S, f c = g c) → (f ∈ A ↔ g ∈ A)

section TwoEvents

variable [Fintype Coordinate] [DecidableEq Coordinate]
variable [Fintype Value] [Nonempty Value] [DecidableEq Value]

/-- The coordinate-mixing bijection underlying cylinder independence. -/
noncomputable def mixingEquiv
    (A B : Finset (Coordinate → Value)) (S T : Finset Coordinate)
    (hA : DependsOn A S) (hB : DependsOn B T) (hST : Disjoint S T) :
    ({f // f ∈ A ∩ B} × (Coordinate → Value)) ≃
      ({f // f ∈ A} × {f // f ∈ B}) where
  toFun z := by
    let omega : Coordinate → Value := z.1.1
    let eta : Coordinate → Value := z.2
    have homegaA : omega ∈ A := (Finset.mem_inter.mp z.1.2).1
    have homegaB : omega ∈ B := (Finset.mem_inter.mp z.1.2).2
    have ha : mix T eta omega ∈ A := by
      apply (hA omega (mix T eta omega) ?_).mp homegaA
      intro c hcS
      have hcT : c ∉ T := Finset.disjoint_left.mp hST hcS
      simp [mix, hcT]
    have hb : mix T omega eta ∈ B := by
      apply (hB omega (mix T omega eta) ?_).mp homegaB
      intro c hcT
      simp [mix, hcT]
    exact ⟨⟨mix T eta omega, ha⟩, ⟨mix T omega eta, hb⟩⟩
  invFun z := by
    let a : Coordinate → Value := z.1.1
    let b : Coordinate → Value := z.2.1
    have ha : a ∈ A := z.1.2
    have hb : b ∈ B := z.2.2
    have homegaA : mix T b a ∈ A := by
      apply (hA a (mix T b a) ?_).mp ha
      intro c hcS
      have hcT : c ∉ T := Finset.disjoint_left.mp hST hcS
      simp [mix, hcT]
    have homegaB : mix T b a ∈ B := by
      apply (hB b (mix T b a) ?_).mp hb
      intro c hcT
      simp [mix, hcT]
    exact ⟨⟨mix T b a, Finset.mem_inter.mpr ⟨homegaA, homegaB⟩⟩,
      mix T a b⟩
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      funext c
      by_cases hc : c ∈ T <;> simp [mix, hc]
    · funext c
      by_cases hc : c ∈ T <;> simp [mix, hc]
  right_inv z := by
    apply Prod.ext <;> apply Subtype.ext <;> funext c <;>
      by_cases hc : c ∈ T <;> simp [mix, hc]

/-- Two events on a finite function space are independent when their
coordinate supports are disjoint. -/
theorem uniformProbability_inter_eq_mul
    (A B : Finset (Coordinate → Value)) (S T : Finset Coordinate)
    (hA : DependsOn A S) (hB : DependsOn B T) (hST : Disjoint S T) :
    uniformProbability (A ∩ B) = uniformProbability A * uniformProbability B := by
  have hcard := Fintype.card_congr (mixingEquiv A B S T hA hB hST)
  simp only [Fintype.card_prod, Fintype.card_coe] at hcard
  unfold uniformProbability
  have hne : (Fintype.card (Coordinate → Value) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne' : Fintype.card (Coordinate → Value) ≠ 0)
  field_simp
  exact_mod_cast hcard

end TwoEvents

section CoordinateConstraints

variable [Fintype Coordinate] [DecidableEq Coordinate]
variable [Fintype Value] [Nonempty Value] [DecidableEq Value]

/-- Functions whose value at `c` lies in `R`. -/
def coordinateEvent (c : Coordinate) (R : Finset Value) :
    Finset (Coordinate → Value) :=
  Finset.univ.filter fun f ↦ f c ∈ R

/-- Functions whose values on every coordinate of `S` lie in `R`. -/
def constraintEvent (S : Finset Coordinate) (R : Finset Value) :
    Finset (Coordinate → Value) :=
  Finset.univ.filter fun f ↦ ∀ c ∈ S, f c ∈ R

omit [Nonempty Value] in
lemma coordinateEvent_dependsOn (c : Coordinate) (R : Finset Value) :
    DependsOn (coordinateEvent c R) {c} := by
  intro f g hfg
  simp only [coordinateEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfg c (Finset.mem_singleton_self c)]

omit [Nonempty Value] in
lemma constraintEvent_dependsOn (S : Finset Coordinate) (R : Finset Value) :
    DependsOn (constraintEvent S R) S := by
  intro f g hfg
  simp only [constraintEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf c hc
    rw [← hfg c hc]
    exact hf c hc
  · intro hg c hc
    rw [hfg c hc]
    exact hg c hc

/-- Splitting off coordinate `c` identifies the one-coordinate event with
an allowed value and an arbitrary assignment on all other coordinates. -/
noncomputable def coordinateEventEquiv (c : Coordinate) (R : Finset Value) :
    {f // f ∈ coordinateEvent c R} ≃
      ({v // v ∈ R} × ({d : Coordinate // d ≠ c} → Value)) where
  toFun f :=
    ⟨⟨f.1 c, (Finset.mem_filter.mp f.2).2⟩, fun d ↦ f.1 d⟩
  invFun z := by
    let f := (Equiv.funSplitAt c Value).symm (z.1.1, z.2)
    refine ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [f]
  left_inv f := by
    apply Subtype.ext
    exact (Equiv.funSplitAt c Value).left_inv f.1
  right_inv z := by
    have h := (Equiv.funSplitAt c Value).right_inv (z.1.1, z.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · change ((Equiv.funSplitAt c Value)
          ((Equiv.funSplitAt c Value).symm (z.1.1, z.2))).2 = z.2
      exact congrArg Prod.snd h

/-- Exact probability of a one-coordinate constraint. -/
theorem uniformProbability_coordinateEvent (c : Coordinate) (R : Finset Value) :
    uniformProbability (coordinateEvent c R) =
      (R.card : ℝ) / Fintype.card Value := by
  let Rest := {d : Coordinate // d ≠ c} → Value
  have hevent := Fintype.card_congr (coordinateEventEquiv c R)
  have hall := Fintype.card_congr (Equiv.funSplitAt c Value)
  simp only [Fintype.card_prod, Fintype.card_coe] at hevent hall
  have hrest : 0 < Fintype.card Rest := Fintype.card_pos
  have hvalue : 0 < Fintype.card Value := Fintype.card_pos
  unfold uniformProbability
  rw [show ((coordinateEvent c R).card : ℝ) =
      (R.card : ℝ) * Fintype.card Rest by exact_mod_cast hevent]
  rw [show (Fintype.card (Coordinate → Value) : ℝ) =
      (Fintype.card Value : ℝ) * Fintype.card Rest by exact_mod_cast hall]
  field_simp

omit [Nonempty Value] in
lemma constraintEvent_empty (R : Finset Value) :
    constraintEvent (∅ : Finset Coordinate) R = Finset.univ := by
  ext f
  simp [constraintEvent]

omit [Nonempty Value] in
lemma constraintEvent_insert {c : Coordinate} {S : Finset Coordinate}
    (R : Finset Value) :
    constraintEvent (insert c S) R =
      coordinateEvent c R ∩ constraintEvent S R := by
  ext f
  simp [constraintEvent, coordinateEvent]

/-- Exact product probability for identical allowed-value constraints on a
finite coordinate set. -/
theorem uniformProbability_constraintEvent (S : Finset Coordinate)
    (R : Finset Value) :
    uniformProbability (constraintEvent S R) =
      ((R.card : ℝ) / Fintype.card Value) ^ S.card := by
  induction S using Finset.induction with
  | empty =>
      rw [constraintEvent_empty, uniformProbability_univ]
      simp
  | @insert c S hc ih =>
      rw [constraintEvent_insert]
      rw [uniformProbability_inter_eq_mul
        (coordinateEvent c R) (constraintEvent S R) {c} S
        (coordinateEvent_dependsOn c R) (constraintEvent_dependsOn S R)
        (Finset.disjoint_singleton_left.mpr hc)]
      rw [uniformProbability_coordinateEvent, ih, Finset.card_insert_of_notMem hc]
      rw [pow_succ]
      exact mul_comm _ _

end CoordinateConstraints

section EventFamily

variable [Fintype Coordinate] [DecidableEq Coordinate]
variable [Fintype Value] [Nonempty Value] [DecidableEq Value]
variable [DecidableEq ι]

omit [Nonempty Value] in
lemma avoiding_dependsOn_biUnion
    (event : ι → Finset (Coordinate → Value))
    (support : ι → Finset Coordinate)
    (hdepends : ∀ i, DependsOn (event i) (support i))
    (J : Finset ι) :
    DependsOn (avoiding event J) (J.biUnion support) := by
  intro f g hfg
  simp only [avoiding, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hf j hj hgj
    apply hf j hj
    apply (hdepends j f g ?_).mpr hgj
    intro c hc
    exact hfg c (Finset.mem_biUnion.mpr ⟨j, hj, hc⟩)
  · intro hg j hj hfj
    apply hg j hj
    apply (hdepends j f g ?_).mp hfj
    intro c hc
    exact hfg c (Finset.mem_biUnion.mpr ⟨j, hj, hc⟩)

omit [Fintype Coordinate] [DecidableEq ι] in
lemma disjoint_biUnion_of_pairwise_disjoint
    (support : ι → Finset Coordinate) {i : ι} {J : Finset ι}
    (h : ∀ j ∈ J, Disjoint (support i) (support j)) :
    Disjoint (support i) (J.biUnion support) := by
  rw [Finset.disjoint_left]
  intro c hci hcJ
  obtain ⟨j, hj, hcj⟩ := Finset.mem_biUnion.mp hcJ
  exact Finset.disjoint_left.mp (h j hj) hci hcj

/-- An event is independent of simultaneous avoidance of a family of events
whose supports are all disjoint from its support. -/
theorem uniformProbability_event_inter_avoiding
    (event : ι → Finset (Coordinate → Value))
    (support : ι → Finset Coordinate)
    (hdepends : ∀ i, DependsOn (event i) (support i))
    (i : ι) (J : Finset ι)
    (hdisjoint : ∀ j ∈ J, Disjoint (support i) (support j)) :
    uniformProbability (event i ∩ avoiding event J) =
      uniformProbability (event i) * uniformProbability (avoiding event J) := by
  exact uniformProbability_inter_eq_mul
    (event i) (avoiding event J) (support i) (J.biUnion support)
    (hdepends i) (avoiding_dependsOn_biUnion event support hdepends J)
    (disjoint_biUnion_of_pairwise_disjoint support hdisjoint)

end EventFamily

end Cylinder
end OMA1024


-- ===== from plby module ErdosProblems.Erdos1024.Upper =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

This file represents triples as coordinates of a finite product space.  It
sets up the overlap and hole bad events, proves their exact probabilities and
support independence, and extracts a linear triple system hitting every
`t`-set from any assignment avoiding all bad events.
-/

open scoped BigOperators

namespace OMA1024
namespace Upper

open Cylinder LocalLemma

/-- A three-element subset of `Fin n`, used as a product coordinate. -/
abbrev Triple (n : ℕ) := {e : Finset (Fin n) // e.card = 3}

/-- Ordered pairs of distinct triples meeting in at least two vertices. -/
abbrev OverlapIndex (n : ℕ) :=
  {p : Triple n × Triple n // p.1 ≠ p.2 ∧ 2 ≤ (p.1.1 ∩ p.2.1).card}

/-- Vertex `t`-sets which must not be independent. -/
abbrev HoleIndex (n t : ℕ) :=
  {S : Finset (Fin n) // S.card = t}

/-- The two families of bad events. -/
abbrev BadIndex (n t : ℕ) := OverlapIndex n ⊕ HoleIndex n t

/-- Triple coordinates inspected by a bad event. -/
def support {n t : ℕ} : BadIndex n t → Finset (Triple n)
  | Sum.inl a => {a.1.1, a.1.2}
  | Sum.inr S => Finset.univ.filter fun e ↦ e.1 ⊆ S.1

@[simp] lemma support_overlap {n t : ℕ} (a : OverlapIndex n) :
    support (t := t) (Sum.inl a) = {a.1.1, a.1.2} := by
  simp [support]

@[simp] lemma support_hole {n t : ℕ} (S : HoleIndex n t) :
    support (Sum.inr S) = Finset.univ.filter fun e ↦ e.1 ⊆ S.1 := by
  simp [support]

lemma support_overlap_card {n t : ℕ} (a : OverlapIndex n) :
    (support (t := t) (Sum.inl a)).card = 2 := by
  simp [a.2.1]

lemma support_hole_card {n t : ℕ} (S : HoleIndex n t) :
    (support (Sum.inr S)).card = t.choose 3 := by
  classical
  have hcard : (support (Sum.inr S)).card = (S.1.powersetCard 3).card := by
    refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
    · intro e he
      simp only [support_hole, Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact Finset.mem_powersetCard.mpr ⟨he, e.2⟩
    · intro e₁ he₁ e₂ he₂ h
      exact Subtype.ext h
    · intro e he
      have he' := Finset.mem_powersetCard.mp he
      exact ⟨⟨e, he'.2⟩, by simp [support, he'.1], rfl⟩
  rw [hcard, Finset.card_powersetCard, S.2]

/-- Uniform product assignments; the distinguished value means ‘selected’. -/
abbrev Outcome (n K : ℕ) := Triple n → Fin K

/-- A bad event as a cylinder in the finite product space. -/
def badEvent {n t K : ℕ} (selected : Fin K) (i : BadIndex n t) :
    Finset (Outcome n K) :=
  match i with
  | Sum.inl _ => constraintEvent (support i) {selected}
  | Sum.inr _ => constraintEvent (support i) (Finset.univ.erase selected)

lemma badEvent_dependsOn {n t K : ℕ} [NeZero K]
    (selected : Fin K) (i : BadIndex n t) :
    Cylinder.DependsOn (badEvent selected i) (support i) := by
  cases i with
  | inl a => exact constraintEvent_dependsOn _ _
  | inr S => exact constraintEvent_dependsOn _ _

/-- Dependency means that the two cylinder supports overlap. -/
def Dependent {n t : ℕ} (i j : BadIndex n t) : Prop :=
  ¬ Disjoint (support i) (support j)

instance dependentDecidable {n t : ℕ} : DecidableRel (@Dependent n t) :=
  fun _ _ ↦ by
    unfold Dependent
    infer_instance

/-- The exact probability of either kind of bad event. -/
noncomputable def badProbability (K : ℕ) {n t : ℕ} : BadIndex n t → ℝ
  | Sum.inl _ => ((1 : ℝ) / K) ^ 2
  | Sum.inr _ => (((K - 1 : ℕ) : ℝ) / K) ^ (t.choose 3)

lemma uniformProbability_badEvent {n t K : ℕ} [NeZero K]
    (selected : Fin K) (i : BadIndex n t) :
    uniformProbability (badEvent selected i) = badProbability K i := by
  cases i with
  | inl a =>
      rw [badEvent, uniformProbability_constraintEvent, support_overlap_card]
      simp [badProbability]
  | inr S =>
      rw [badEvent, uniformProbability_constraintEvent, support_hole_card]
      have hmem : selected ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ _
      rw [Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
      rfl

lemma badEvent_independent_of_nonNeighbors {n t K : ℕ} [NeZero K]
    (selected : Fin K) (i : BadIndex n t) (J : Finset (BadIndex n t))
    (hJ : ∀ j ∈ J, ¬ Dependent i j) :
    uniformProbability (badEvent selected i ∩ avoiding (badEvent selected) J) =
      uniformProbability (badEvent selected i) *
        uniformProbability (avoiding (badEvent selected) J) := by
  exact uniformProbability_event_inter_avoiding
    (badEvent selected) support (badEvent_dependsOn selected) i J fun j hj ↦
      Classical.not_not.mp (hJ j hj)

/-- The finite asymmetric local lemma specialized to the two bad-event
families. -/
theorem exists_assignment_avoiding_badEvents
    {n t K : ℕ} [NeZero K] (selected : Fin K)
    (charge : BadIndex n t → ℝ)
    (hcharge0 : ∀ i, 0 ≤ charge i) (hcharge1 : ∀ i, charge i < 1)
    (hcriterion : ∀ i (J : Finset (BadIndex n t)), i ∉ J →
      badProbability K i ≤
        charge i * ∏ j ∈ J.filter (Dependent i), (1 - charge j)) :
    ∃ omega : Outcome n K, ∀ i : BadIndex n t, omega ∉ badEvent selected i := by
  exact exists_avoiding_of_asymmetric
    (badEvent selected) Dependent charge hcharge0 hcharge1
    (fun i J hiJ ↦ by
      rw [uniformProbability_badEvent]
      exact hcriterion i J hiJ)
    (badEvent_independent_of_nonNeighbors selected)

/-- The triple system selected by an assignment. -/
def chosenSystem {n K : ℕ} (selected : Fin K) (omega : Outcome n K) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.filter fun e : Triple n ↦ omega e = selected).image Subtype.val

lemma mem_chosenSystem_iff {n K : ℕ} {selected : Fin K} {omega : Outcome n K}
    {e : Finset (Fin n)} :
    e ∈ chosenSystem selected omega ↔
      ∃ he : e.card = 3, omega ⟨e, he⟩ = selected := by
  classical
  simp only [chosenSystem, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨he, hselected⟩
    exact ⟨⟨e, he⟩, hselected, rfl⟩

lemma chosenSystem_threeUniform {n K : ℕ} (selected : Fin K) (omega : Outcome n K) :
    ∀ e ∈ chosenSystem selected omega, e.card = 3 := by
  intro e he
  exact (mem_chosenSystem_iff.mp he).choose

lemma chosenSystem_linear_of_avoids {n t K : ℕ}
    (selected : Fin K) (omega : Outcome n K)
    (havoid : ∀ i : BadIndex n t, omega ∉ badEvent selected i) :
    ∀ ⦃e⦄, e ∈ chosenSystem selected omega →
      ∀ ⦃f⦄, f ∈ chosenSystem selected omega →
        e ≠ f → (e ∩ f).card ≤ 1 := by
  classical
  intro e he f hf hef
  obtain ⟨he3, heSelected⟩ := mem_chosenSystem_iff.mp he
  obtain ⟨hf3, hfSelected⟩ := mem_chosenSystem_iff.mp hf
  by_contra hinter
  have htwo : 2 ≤ (e ∩ f).card := by omega
  have hneTriple : (⟨e, he3⟩ : Triple n) ≠ ⟨f, hf3⟩ := by
    intro h
    exact hef (congrArg Subtype.val h)
  let a : OverlapIndex n :=
    ⟨(⟨e, he3⟩, ⟨f, hf3⟩), hneTriple, htwo⟩
  exact (havoid (Sum.inl a)) (by
    simp [badEvent, support, constraintEvent, a, heSelected, hfSelected])

lemma chosenSystem_hits_tsets_of_avoids {n t K : ℕ}
    (selected : Fin K) (omega : Outcome n K)
    (havoid : ∀ i : BadIndex n t, omega ∉ badEvent selected i) :
    ∀ S : Finset (Fin n), S.card = t →
      ∃ e ∈ chosenSystem selected omega, e ⊆ S := by
  classical
  intro S hS
  let hole : HoleIndex n t := ⟨S, hS⟩
  have hnot := havoid (Sum.inr hole)
  change omega ∉ constraintEvent
    (Finset.univ.filter fun e : Triple n ↦ e.1 ⊆ S)
    (Finset.univ.erase selected) at hnot
  simp only [constraintEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, not_and, not_forall] at hnot
  obtain ⟨e, heSupport, heSelected⟩ := hnot
  have heSub : e.1 ⊆ S := heSupport
  have heSelected' : omega e = selected := by
    by_contra hne
    exact (heSelected hne) trivial
  have heMem : e.1 ∈ chosenSystem selected omega :=
    mem_chosenSystem_iff.mpr ⟨e.2, heSelected'⟩
  exact ⟨e.1, heMem, heSub⟩

/-- Local-lemma charges satisfying the exact product criterion yield a
linear triple system in which every `t` vertices span an edge. -/
theorem exists_linear_hitting_system_of_charges
    {n t K : ℕ} [NeZero K] (selected : Fin K)
    (charge : BadIndex n t → ℝ)
    (hcharge0 : ∀ i, 0 ≤ charge i) (hcharge1 : ∀ i, charge i < 1)
    (hcriterion : ∀ i (J : Finset (BadIndex n t)), i ∉ J →
      badProbability K i ≤
        charge i * ∏ j ∈ J.filter (Dependent i), (1 - charge j)) :
    ∃ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) ∧
      (∀ ⦃e⦄, e ∈ H → ∀ ⦃f⦄, f ∈ H → e ≠ f → (e ∩ f).card ≤ 1) ∧
      (∀ S : Finset (Fin n), S.card = t → ∃ e ∈ H, e ⊆ S) := by
  obtain ⟨omega, homega⟩ := exists_assignment_avoiding_badEvents
    selected charge hcharge0 hcharge1 hcriterion
  exact ⟨chosenSystem selected omega, chosenSystem_threeUniform selected omega,
    chosenSystem_linear_of_avoids selected omega homega,
    chosenSystem_hits_tsets_of_avoids selected omega homega⟩

end Upper
end OMA1024


-- ===== from plby module ErdosProblems.Erdos1024.UpperCounts =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

The local lemma only needs two linear-in-`n` incidence estimates.  This file
proves them by first showing that a fixed pair of vertices has at most `n`
three-element extensions.
-/

open scoped BigOperators

namespace OMA1024
namespace Upper

/-- Triples which contain a prescribed vertex pair. -/
def triplesExtendingPair {n : ℕ} (r : Finset (Fin n)) : Finset (Triple n) :=
  Finset.univ.filter fun e ↦ r ⊆ e.1

lemma card_triplesExtendingPair_le {n : ℕ} {r : Finset (Fin n)}
    (hr : r.card = 2) : (triplesExtendingPair r).card ≤ n := by
  classical
  let raw : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).image fun x ↦ insert x r
  have hsub : (triplesExtendingPair r).image Subtype.val ⊆ raw := by
    intro f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    have hre : r ⊆ e.1 := by simpa [triplesExtendingPair] using he
    have hdiff : (e.1 \ r).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hre, e.2, hr]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdiff
    have heq : e.1 = insert x r := by
      apply Finset.Subset.antisymm
      · intro y hy
        by_cases hyr : y ∈ r
        · exact Finset.mem_insert_of_mem hyr
        · have hydiff : y ∈ e.1 \ r := Finset.mem_sdiff.mpr ⟨hy, hyr⟩
          rw [hx] at hydiff
          exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hydiff))
      · exact Finset.insert_subset
          (Finset.mem_sdiff.mp (by rw [hx]; simp)).1 hre
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, heq.symm⟩
  calc
    (triplesExtendingPair r).card =
        ((triplesExtendingPair r).image Subtype.val).card := by
          symm
          exact Finset.card_image_of_injective _ Subtype.val_injective
    _ ≤ raw.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp

/-- Possible partners of a fixed triple in an overlap bad event. -/
def overlapPartners {n : ℕ} (e : Triple n) : Finset (Triple n) :=
  Finset.univ.filter fun f ↦ f ≠ e ∧ 2 ≤ (e.1 ∩ f.1).card

lemma card_overlapPartners_le {n : ℕ} (e : Triple n) :
    (overlapPartners e).card ≤ 3 * n := by
  classical
  let pairs : Finset (Finset (Fin n)) := e.1.powersetCard 2
  let cover : Finset (Triple n) := pairs.biUnion triplesExtendingPair
  have hsub : overlapPartners e ⊆ cover := by
    intro f hf
    have hf' := Finset.mem_filter.mp hf
    have hinter3 : (e.1 ∩ f.1).card ≤ 3 := by
      exact (Finset.card_le_card (Finset.inter_subset_left)).trans_eq e.2
    have hinter2 : (e.1 ∩ f.1).card = 2 := by
      by_contra hne
      have hintereq : (e.1 ∩ f.1).card = 3 := by omega
      have hi_eq_e : e.1 ∩ f.1 = e.1 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
          simp [e.2, hintereq])
      have hsubef : e.1 ⊆ f.1 := by
        rw [← hi_eq_e]
        exact Finset.inter_subset_right
      have heq : e = f := by
        apply Subtype.ext
        exact Finset.eq_of_subset_of_card_le hsubef (by simp [e.2, f.2])
      exact hf'.2.1 heq.symm
    have hpairs : e.1 ∩ f.1 ∈ pairs :=
      Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hinter2⟩
    exact Finset.mem_biUnion.mpr ⟨e.1 ∩ f.1, hpairs,
      by simp [triplesExtendingPair]⟩
  calc
    (overlapPartners e).card ≤ cover.card := Finset.card_le_card hsub
    _ ≤ ∑ r ∈ pairs, (triplesExtendingPair r).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ pairs, n := by
      apply Finset.sum_le_sum
      intro r hrmem
      exact card_triplesExtendingPair_le (Finset.mem_powersetCard.mp hrmem).2
    _ = 3 * n := by simp [pairs, e.2]

/-- Ordered overlap events which use a fixed triple coordinate. -/
def overlapEventsContaining {n : ℕ} (e : Triple n) : Finset (OverlapIndex n) :=
  Finset.univ.filter fun a ↦ a.1.1 = e ∨ a.1.2 = e

lemma card_overlapEventsContaining_le {n : ℕ} (e : Triple n) :
    (overlapEventsContaining e).card ≤ 6 * n := by
  classical
  let encode : OverlapIndex n → Bool × Triple n := fun a ↦
    if a.1.1 = e then (false, a.1.2) else (true, a.1.1)
  let target : Finset (Bool × Triple n) :=
    (Finset.univ : Finset Bool).product (overlapPartners e)
  have hmaps : Set.MapsTo encode (overlapEventsContaining e) target := by
    intro a ha
    have hcontains : a.1.1 = e ∨ a.1.2 = e :=
      (Finset.mem_filter.mp ha).2
    by_cases hleft : a.1.1 = e
    · have hpartner : a.1.2 ∈ overlapPartners e := by
        rw [overlapPartners, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro hright
          exact a.2.1 (hleft.trans hright.symm)
        · simpa [hleft] using a.2.2
      simp [encode, target, hleft, hpartner]
    · have hright : a.1.2 = e := hcontains.resolve_left hleft
      have hpartner : a.1.1 ∈ overlapPartners e := by
        rw [overlapPartners, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hleft, ?_⟩
        simpa [hright, Finset.inter_comm] using a.2.2
      simp [encode, target, hleft, hpartner]
  have hinj : ((overlapEventsContaining e : Finset (OverlapIndex n)) :
      Set (OverlapIndex n)).InjOn encode := by
    intro a ha b hb hab
    by_cases haLeft : a.1.1 = e <;> by_cases hbLeft : b.1.1 = e
    · have hother : a.1.2 = b.1.2 := by
        simpa [encode, haLeft, hbLeft] using congrArg Prod.snd hab
      apply Subtype.ext
      exact Prod.ext (haLeft.trans hbLeft.symm) hother
    · have : false = true := by
        simpa [encode, haLeft, hbLeft] using congrArg Prod.fst hab
      cases this
    · have : true = false := by
        simpa [encode, haLeft, hbLeft] using congrArg Prod.fst hab
      cases this
    · have hfirst : a.1.1 = b.1.1 := by
        simpa [encode, haLeft, hbLeft] using congrArg Prod.snd hab
      have haRight : a.1.2 = e :=
        ((Finset.mem_filter.mp ha).2).resolve_left haLeft
      have hbRight : b.1.2 = e :=
        ((Finset.mem_filter.mp hb).2).resolve_left hbLeft
      apply Subtype.ext
      exact Prod.ext hfirst (haRight.trans hbRight.symm)
  calc
    (overlapEventsContaining e).card ≤ target.card :=
      Finset.card_le_card_of_injOn encode hmaps hinj
    _ = 2 * (overlapPartners e).card := by simp [target]
    _ ≤ 2 * (3 * n) := Nat.mul_le_mul_left 2 (card_overlapPartners_le e)
    _ = 6 * n := by omega

/-- Overlap events adjacent to an arbitrary bad event. -/
def neighboringOverlaps {n t : ℕ} (i : BadIndex n t) :
    Finset (OverlapIndex n) :=
  Finset.univ.filter fun a ↦ Dependent i (Sum.inl a)

lemma card_neighboringOverlaps_le {n t : ℕ} (i : BadIndex n t) :
    (neighboringOverlaps i).card ≤ (support i).card * (6 * n) := by
  classical
  let cover : Finset (OverlapIndex n) :=
    (support i).biUnion overlapEventsContaining
  have hsub : neighboringOverlaps i ⊆ cover := by
    intro a ha
    have hdep : Dependent i (Sum.inl a) :=
      (Finset.mem_filter.mp ha).2
    obtain ⟨e, hei, hea⟩ := Finset.not_disjoint_iff.mp hdep
    have hcontains : a.1.1 = e ∨ a.1.2 = e := by
      have h : e = a.1.1 ∨ e = a.1.2 := by simpa [support] using hea
      exact h.imp Eq.symm Eq.symm
    exact Finset.mem_biUnion.mpr ⟨e, hei,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontains⟩⟩
  calc
    (neighboringOverlaps i).card ≤ cover.card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ support i, (overlapEventsContaining e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ support i, 6 * n := by
      apply Finset.sum_le_sum
      intro e _he
      exact card_overlapEventsContaining_le e
    _ = (support i).card * (6 * n) := by simp

lemma card_overlap_neighbors_of_overlap_le {n t : ℕ} (a : OverlapIndex n) :
    (neighboringOverlaps (t := t) (Sum.inl a)).card ≤ 12 * n := by
  calc
    (neighboringOverlaps (t := t) (Sum.inl a)).card ≤
        (support (t := t) (Sum.inl a)).card * (6 * n) :=
      card_neighboringOverlaps_le _
    _ = 12 * n := by rw [support_overlap_card]; omega

lemma card_overlap_neighbors_of_hole_le {n t : ℕ} (S : HoleIndex n t) :
    (neighboringOverlaps (Sum.inr S)).card ≤ 6 * n * t.choose 3 := by
  calc
    (neighboringOverlaps (Sum.inr S)).card ≤
        (support (Sum.inr S)).card * (6 * n) := card_neighboringOverlaps_le _
    _ = 6 * n * t.choose 3 := by
      rw [support_hole_card]
      simp [Nat.mul_comm, Nat.mul_left_comm]

end Upper
end OMA1024

-- ===== from plby module ErdosProblems.Erdos1024.UpperCriterion =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

This file isolates the elementary product estimates used by the random
construction.  Overlap events receive one common charge, while hole events
may receive charges depending on the hole.
-/

open scoped BigOperators

namespace OMA1024
namespace Upper

/-- The overlap coordinates occurring in a finset of bad indices. -/
noncomputable def overlapProjection {n t : ℕ} (N : Finset (BadIndex n t)) :
    Finset (OverlapIndex n) := by
  classical
  exact Finset.univ.filter fun a ↦ Sum.inl a ∈ N

/-- The hole coordinates occurring in a finset of bad indices. -/
noncomputable def holeProjection {n t : ℕ} (N : Finset (BadIndex n t)) :
    Finset (HoleIndex n t) := by
  classical
  exact Finset.univ.filter fun S ↦ Sum.inr S ∈ N

lemma prod_badIndex_eq_projections {n t : ℕ}
    (N : Finset (BadIndex n t)) (f : BadIndex n t → ℝ) :
    (∏ i ∈ N, f i) =
      (∏ a ∈ overlapProjection N, f (Sum.inl a)) *
        ∏ S ∈ holeProjection N, f (Sum.inr S) := by
  classical
  calc
    (∏ i ∈ N, f i) = ∏ i : BadIndex n t, if i ∈ N then f i else 1 := by
      simp
    _ = (∏ a : OverlapIndex n,
          if Sum.inl a ∈ N then f (Sum.inl a) else 1) *
        ∏ S : HoleIndex n t,
          if Sum.inr S ∈ N then f (Sum.inr S) else 1 :=
      Fintype.prod_sum_type _
    _ = (∏ a ∈ overlapProjection N, f (Sum.inl a)) *
        ∏ S ∈ holeProjection N, f (Sum.inr S) := by
      congr 1
      · symm
        unfold overlapProjection
        rw [Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro a _ha
        by_cases h : Sum.inl a ∈ N <;> simp [h]
      · symm
        unfold holeProjection
        rw [Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro S _hS
        by_cases h : Sum.inr S ∈ N <;> simp [h]

/-- The elementary union-bound lower estimate
`1 - sum y ≤ product (1-y)` for numbers in `[0,1]`. -/
lemma one_sub_sum_le_prod_one_sub {ι : Type*} {s : Finset ι} {y : ι → ℝ}
    (hy0 : ∀ i ∈ s, 0 ≤ y i) (hy1 : ∀ i ∈ s, y i ≤ 1) :
    1 - ∑ i ∈ s, y i ≤ ∏ i ∈ s, (1 - y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hya0 := hy0 a (Finset.mem_insert_self _ _)
      have hya1 := hy1 a (Finset.mem_insert_self _ _)
      have hsum0 : 0 ≤ ∑ i ∈ s, y i :=
        Finset.sum_nonneg fun i hi ↦ hy0 i (Finset.mem_insert_of_mem hi)
      have hih := ih
        (fun i hi ↦ hy0 i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hy1 i (Finset.mem_insert_of_mem hi))
      have hfac : 0 ≤ 1 - y a := sub_nonneg.mpr hya1
      calc
        1 - (y a + ∑ i ∈ s, y i) ≤
            (1 - y a) * (1 - ∑ i ∈ s, y i) := by nlinarith
        _ ≤ (1 - y a) * ∏ i ∈ s, (1 - y i) :=
          mul_le_mul_of_nonneg_left hih hfac

/-- A common charge on overlaps and an indexed charge on holes. -/
def twoCharge {n t : ℕ} (xA : ℝ) (xB : HoleIndex n t → ℝ) :
    BadIndex n t → ℝ
  | Sum.inl _ => xA
  | Sum.inr S => xB S

lemma product_twoCharge_lower {n t : ℕ}
    (N : Finset (BadIndex n t)) (xA : ℝ) (xB : HoleIndex n t → ℝ)
    (_ : 0 ≤ xA) (hxA1 : xA ≤ 1)
    (hxB0 : ∀ S, 0 ≤ xB S) (hxB1 : ∀ S, xB S ≤ 1)
    (htotal : ∑ S, xB S ≤ 1) :
    (1 - xA) ^ (overlapProjection N).card *
        (1 - ∑ S, xB S) ≤
      ∏ i ∈ N, (1 - twoCharge xA xB i) := by
  classical
  rw [prod_badIndex_eq_projections]
  have hA : (∏ a ∈ overlapProjection N,
      (1 - twoCharge xA xB (Sum.inl a))) =
      (1 - xA) ^ (overlapProjection N).card := by
    simp [twoCharge]
  rw [hA]
  have hB := one_sub_sum_le_prod_one_sub
    (s := holeProjection N) (y := xB)
    (fun S _ ↦ hxB0 S) (fun S _ ↦ hxB1 S)
  have hsubset : holeProjection N ⊆ Finset.univ := Finset.subset_univ _
  have hsum : (∑ S ∈ holeProjection N, xB S) ≤ ∑ S, xB S :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset fun S _ _ ↦ hxB0 S
  have htotal0 : 0 ≤ 1 - ∑ S, xB S := sub_nonneg.mpr htotal
  have hbase0 : 0 ≤ (1 - xA) ^ (overlapProjection N).card :=
    pow_nonneg (sub_nonneg.mpr hxA1) _
  apply mul_le_mul_of_nonneg_left _ hbase0
  exact (sub_le_sub_left hsum 1).trans hB

lemma overlapProjection_neighbors_subset {n t : ℕ}
    (i : BadIndex n t) (J : Finset (BadIndex n t)) :
    overlapProjection (J.filter (Dependent i)) ⊆ neighboringOverlaps i := by
  intro a ha
  have ha' : Sum.inl a ∈ J.filter (Dependent i) := by
    simpa [overlapProjection] using ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha').2⟩

/-- Exact cancellation form of the local-lemma criterion. -/
theorem twoCharge_criterion
    {n t K : ℕ} [NeZero K]
    (xA : ℝ) (xB : HoleIndex n t → ℝ)
    (hxAprob : 3 * (((1 : ℝ) / K) ^ 2) = xA)
    (hxA0 : 0 ≤ xA) (hxA1 : xA ≤ 1)
    (hxB0 : ∀ S, 0 ≤ xB S) (hxB1 : ∀ S, xB S ≤ 1)
    (htotal : ∑ S, xB S ≤ 1 / 4)
    (hoverlapLoss : (12 * n : ℝ) * xA ≤ 1 / 4)
    (hholes : ∀ S : HoleIndex n t,
      2 * badProbability K (Sum.inr S) ≤
        xB S * (1 - xA) ^ (6 * n * t.choose 3)) :
    ∀ i (J : Finset (BadIndex n t)), i ∉ J →
      badProbability K i ≤
        twoCharge xA xB i *
          ∏ j ∈ J.filter (Dependent i), (1 - twoCharge xA xB j) := by
  classical
  intro i J _hiJ
  let N := J.filter (Dependent i)
  have htotal' : ∑ S, xB S ≤ 1 := htotal.trans (by norm_num)
  have hprod := product_twoCharge_lower N xA xB hxA0 hxA1 hxB0 hxB1 htotal'
  have hbase0 : 0 ≤ 1 - xA := sub_nonneg.mpr hxA1
  have hholeFactor : 3 / 4 ≤ 1 - ∑ S, xB S := by linarith
  cases i with
  | inl a =>
      have hcard : (overlapProjection N).card ≤ 12 * n :=
        (Finset.card_le_card (overlapProjection_neighbors_subset _ _)).trans
          (card_overlap_neighbors_of_overlap_le a)
      have hpowmono : (1 - xA) ^ (12 * n) ≤
          (1 - xA) ^ (overlapProjection N).card := by
        exact pow_le_pow_of_le_one hbase0 (sub_le_self (1 : ℝ) hxA0) hcard
      have hbern : 1 - (12 * n : ℝ) * xA ≤ (1 - xA) ^ (12 * n) := by
        simpa [sub_eq_add_neg, mul_neg, Nat.cast_mul] using
          (one_add_mul_le_pow (a := -xA) (by linarith [hxA1]) (12 * n))
      have hAfac : 3 / 4 ≤ (1 - xA) ^ (overlapProjection N).card := by
        calc
          3 / 4 ≤ 1 - (12 * n : ℝ) * xA := by linarith
          _ ≤ (1 - xA) ^ (12 * n) := hbern
          _ ≤ _ := hpowmono
      have hprodThird : 1 / 3 ≤
          ∏ j ∈ N, (1 - twoCharge xA xB j) := by
        calc
          1 / 3 ≤ (3 / 4 : ℝ) * (3 / 4) := by norm_num
          _ ≤ (1 - xA) ^ (overlapProjection N).card *
              (1 - ∑ S, xB S) :=
            mul_le_mul hAfac hholeFactor (by norm_num) (pow_nonneg hbase0 _)
          _ ≤ _ := hprod
      change ((1 : ℝ) / K) ^ 2 ≤ xA * ∏ j ∈ N,
        (1 - twoCharge xA xB j)
      have hmul := mul_le_mul_of_nonneg_left hprodThird hxA0
      nlinarith [sq_nonneg ((1 : ℝ) / (K : ℝ))]
  | inr S =>
      have hcard : (overlapProjection N).card ≤ 6 * n * t.choose 3 :=
        (Finset.card_le_card (overlapProjection_neighbors_subset _ _)).trans
          (card_overlap_neighbors_of_hole_le S)
      have hpowmono : (1 - xA) ^ (6 * n * t.choose 3) ≤
          (1 - xA) ^ (overlapProjection N).card := by
        exact pow_le_pow_of_le_one hbase0 (sub_le_self (1 : ℝ) hxA0) hcard
      have hprodHole : (1 - xA) ^ (6 * n * t.choose 3) * (3 / 4) ≤
          ∏ j ∈ N, (1 - twoCharge xA xB j) := by
        calc
          _ ≤ (1 - xA) ^ (overlapProjection N).card *
              (1 - ∑ S, xB S) :=
            mul_le_mul hpowmono hholeFactor (by norm_num) (pow_nonneg hbase0 _)
          _ ≤ _ := hprod
      change badProbability K (Sum.inr S) ≤
        xB S * ∏ j ∈ N, (1 - twoCharge xA xB j)
      have hxB := hxB0 S
      have hscaled := mul_le_mul_of_nonneg_left hprodHole hxB
      have hq0 : 0 ≤ badProbability K (Sum.inr S) := by
        dsimp [badProbability]
        positivity
      nlinarith [hholes S]

end Upper
end OMA1024

-- ===== from plby module ErdosProblems.Erdos1024.UpperAnalytic =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

We use `144 n` equiprobable colors and require every
`ceil (200 * sqrt (n log n))`-set to contain a selected triple.  The larger
constants make every elementary estimate comfortably strict.
-/

open Filter
open scoped BigOperators

namespace OMA1024
namespace Upper

def colorCount (n : ℕ) : ℕ := 144 * n

noncomputable def upperScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log n)

noncomputable def upperThreshold (n : ℕ) : ℕ :=
  ⌈200 * upperScale n⌉₊

noncomputable def overlapCharge (n : ℕ) : ℝ :=
  3 * (((1 : ℝ) / colorCount n) ^ 2)

noncomputable def holeProbability (n : ℕ) : ℝ :=
  ((((colorCount n - 1 : ℕ) : ℝ) / colorCount n) ^
    (upperThreshold n).choose 3)

noncomputable def holeCharge (n : ℕ) (_S : HoleIndex n (upperThreshold n)) : ℝ :=
  2 * holeProbability n * Real.exp
    (2 * overlapCharge n *
      (6 * n * (upperThreshold n).choose 3 : ℕ))

lemma card_holeIndex (n t : ℕ) : Fintype.card (HoleIndex n t) = n.choose t := by
  classical
  rw [Fintype.card_subtype]
  change ((Finset.univ : Finset (Finset (Fin n))).filter
    (fun S ↦ S.card = t)).card = n.choose t
  have heq : (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S ↦ S.card = t) = Finset.univ.powersetCard t := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [heq, Finset.card_powersetCard]
  simp

lemma choose_three_lower {t : ℕ} (ht : 4 ≤ t) :
    (t : ℝ) ^ 3 / 48 ≤ (t.choose 3 : ℕ) := by
  have ht1Nat : t ≤ 2 * (t - 1) := by omega
  have ht2Nat : t ≤ 2 * (t - 2) := by omega
  have ht1Cast : (t : ℝ) ≤ 2 * ((t - 1 : ℕ) : ℝ) := by exact_mod_cast ht1Nat
  have ht2Cast : (t : ℝ) ≤ 2 * ((t - 2 : ℕ) : ℝ) := by exact_mod_cast ht2Nat
  have hcast1 : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hcast2 : ((t - 2 : ℕ) : ℝ) = (t : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have ht1 : (t : ℝ) / 2 ≤ (t : ℝ) - 1 := by
    rw [← hcast1]
    nlinarith
  have ht2 : (t : ℝ) / 2 ≤ (t : ℝ) - 2 := by
    rw [← hcast2]
    nlinarith
  have hdescNat : 6 * t.choose 3 = t * (t - 1) * (t - 2) := by
    calc
      6 * t.choose 3 = Nat.factorial 3 * t.choose 3 := by norm_num
      _ = t.descFactorial 3 := (Nat.descFactorial_eq_factorial_mul_choose t 3).symm
      _ = t * (t - 1) * (t - 2) := by
        simp [Nat.descFactorial, Nat.mul_comm, Nat.mul_assoc]
  have hdesc : (6 : ℝ) * (t.choose 3 : ℕ) =
      (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - 2) := by
    have hdescCast : (6 : ℝ) * (t.choose 3 : ℕ) =
        (t : ℝ) * ((t - 1 : ℕ) : ℝ) * ((t - 2 : ℕ) : ℝ) := by
      exact_mod_cast hdescNat
    simpa [hcast1, hcast2] using hdescCast
  have ht0 : 0 ≤ (t : ℝ) := by positivity
  have hprod : (t : ℝ) * ((t : ℝ) / 2) * ((t : ℝ) / 2) ≤
      (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - 2) := by
    gcongr
    nlinarith
  nlinarith

lemma exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hden : 0 < 1 + 2 * x := by linarith
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * x)
  have hinv : 1 / Real.exp (2 * x) ≤ 1 / (1 + 2 * x) :=
    one_div_le_one_div_of_le hden hexp
  have hrat : 1 / (1 + 2 * x) ≤ 1 - x := by
    rw [div_le_iff₀ hden]
    nlinarith
  simpa [Real.exp_neg] using hinv.trans hrat

lemma one_le_exp_mul_pow_one_sub {x : ℝ} {D : ℕ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    1 ≤ Real.exp (2 * x * D) * (1 - x) ^ D := by
  have hone := exp_neg_two_mul_le_one_sub hx0 hxhalf
  have hpows : (Real.exp (-2 * x)) ^ D ≤ (1 - x) ^ D :=
    pow_le_pow_left₀ (Real.exp_pos _).le hone D
  have hexp : Real.exp (-2 * x * D) ≤ (1 - x) ^ D := by
    calc
      Real.exp (-2 * x * D) = (Real.exp (-2 * x)) ^ D := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := hpows
  have hmul := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (2 * x * D)).le
  calc
    1 = Real.exp (2 * x * D) * Real.exp (-2 * x * D) := by
      rw [← Real.exp_add]
      ring_nf
      simp
    _ ≤ _ := hmul

lemma overlapCharge_nonneg (n : ℕ) : 0 ≤ overlapCharge n := by
  unfold overlapCharge
  positivity

lemma overlapCharge_le_half {n : ℕ} (hn : 0 < n) :
    overlapCharge n ≤ 1 / 2 := by
  have hKpos : (0 : ℝ) < colorCount n := by
    exact_mod_cast (show 0 < colorCount n by simp [colorCount, hn])
  unfold overlapCharge
  rw [div_pow]
  norm_num only [one_pow]
  rw [show 3 * (1 / (colorCount n : ℝ) ^ 2) =
    3 / (colorCount n : ℝ) ^ 2 by ring]
  rw [div_le_iff₀ (sq_pos_of_pos hKpos)]
  have hKlarge : (144 : ℝ) ≤ colorCount n := by
    exact_mod_cast (show 144 ≤ colorCount n by dsimp [colorCount]; omega)
  nlinarith [sq_nonneg ((colorCount n : ℝ) - 144)]

lemma hole_criterion {n : ℕ} (hn : 0 < n)
    (S : HoleIndex n (upperThreshold n)) :
    2 * badProbability (colorCount n) (Sum.inr S) ≤
      holeCharge n S *
        (1 - overlapCharge n) ^
          (6 * n * (upperThreshold n).choose 3) := by
  have hKpos : (0 : ℝ) < colorCount n := by
    exact_mod_cast (show 0 < colorCount n by simp [colorCount, hn])
  have hx0 := overlapCharge_nonneg n
  have hxhalf := overlapCharge_le_half hn
  have hone := one_le_exp_mul_pow_one_sub
    (D := 6 * n * (upperThreshold n).choose 3) hx0 hxhalf
  change 2 * holeProbability n ≤ 2 * holeProbability n *
      Real.exp (2 * overlapCharge n *
        (6 * n * (upperThreshold n).choose 3 : ℕ)) *
      (1 - overlapCharge n) ^ (6 * n * (upperThreshold n).choose 3)
  have hq0 : 0 ≤ holeProbability n := by
    unfold holeProbability
    positivity
  nlinarith

lemma overlap_loss_le {n : ℕ} (hn : 0 < n) :
    (12 * n : ℝ) * overlapCharge n ≤ 1 / 4 := by
  have hKpos : (0 : ℝ) < colorCount n := by
    exact_mod_cast (show 0 < colorCount n by simp [colorCount, hn])
  unfold overlapCharge
  rw [div_pow]
  norm_num only [one_pow]
  rw [show 12 * (n : ℝ) * (3 * (1 / (colorCount n : ℝ) ^ 2)) =
    36 * (n : ℝ) / (colorCount n : ℝ) ^ 2 by ring]
  rw [div_le_iff₀ (sq_pos_of_pos hKpos)]
  norm_num [colorCount]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

lemma threshold_bounds {n : ℕ} (hn : 3 ≤ n) :
    200 * upperScale n ≤ upperThreshold n ∧
      (upperThreshold n : ℝ) ≤ 201 * upperScale n ∧
      4 ≤ upperThreshold n := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog : 1 < Real.log (n : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hnpos]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hinside : 1 ≤ (n : ℝ) * Real.log n := by nlinarith
  have hg : 1 ≤ upperScale n := by
    rw [upperScale]
    exact Real.one_le_sqrt.mpr hinside
  have hlower : 200 * upperScale n ≤ (upperThreshold n : ℝ) := by
    exact Nat.le_ceil _
  have hupper0 : (upperThreshold n : ℝ) < 200 * upperScale n + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hupper : (upperThreshold n : ℝ) ≤ 201 * upperScale n := by
    nlinarith
  have ht4 : 4 ≤ upperThreshold n := by
    exact_mod_cast (show (4 : ℝ) ≤ upperThreshold n by nlinarith)
  exact ⟨hlower, hupper, ht4⟩

lemma exponential_exponent_le {n : ℕ} (hn : 3 ≤ n) :
    (upperThreshold n : ℝ) * Real.log n -
        ((upperThreshold n).choose 3 : ℕ) / (192 * n : ℝ) ≤ -3 := by
  let g := upperScale n
  have hb := threshold_bounds hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog : 1 < Real.log (n : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hnpos]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hgsq : g ^ 2 = (n : ℝ) * Real.log n := by
    dsimp [g, upperScale]
    exact Real.sq_sqrt (mul_nonneg hnpos.le (by linarith))
  have hM := choose_three_lower hb.2.2
  have ht0 : 0 ≤ (upperThreshold n : ℝ) := by positivity
  have htCube : (200 * g) ^ 3 ≤ (upperThreshold n : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hb.1 3
  have hglog : 1 ≤ g * Real.log n := by
    have hinside : 1 ≤ (n : ℝ) * Real.log n := by
      have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hg : 1 ≤ g := by
      dsimp [g, upperScale]
      exact Real.one_le_sqrt.mpr hinside
    nlinarith
  have hratio : 800 * (g * Real.log n) ≤
      ((upperThreshold n).choose 3 : ℕ) / (192 * n : ℝ) := by
    have hcore : 800 * 192 * g ^ 3 ≤
        ((upperThreshold n).choose 3 : ℕ) := by
      nlinarith [htCube, hM]
    have hidentity : g ^ 3 = (n : ℝ) * (g * Real.log n) := by
      calc
        g ^ 3 = g * g ^ 2 := by ring
        _ = g * ((n : ℝ) * Real.log n) := by rw [hgsq]
        _ = (n : ℝ) * (g * Real.log n) := by ring
    rw [le_div_iff₀ (by positivity)]
    calc
      800 * (g * Real.log n) * (192 * (n : ℝ)) =
          800 * 192 * g ^ 3 := by rw [hidentity]; ring
      _ ≤ _ := hcore
  have htlog : (upperThreshold n : ℝ) * Real.log n ≤
      201 * (g * Real.log n) := by
    dsimp [g]
    calc
      (upperThreshold n : ℝ) * Real.log n ≤
          (201 * upperScale n) * Real.log n :=
        mul_le_mul_of_nonneg_right hb.2.1 (by linarith)
      _ = 201 * (upperScale n * Real.log n) := by ring
  nlinarith

lemma two_mul_exp_neg_three_le_quarter :
    2 * Real.exp (-3) ≤ (1 / 4 : ℝ) := by
  have he : (8 : ℝ) < Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [Real.exp_one_gt_two, Real.exp_pos 1]
  rw [Real.exp_neg]
  have hdiv : 2 / Real.exp 3 < (1 / 4 : ℝ) := by
    rw [div_lt_iff₀ (Real.exp_pos 3)]
    nlinarith
  simpa [div_eq_mul_inv] using hdiv.le

lemma total_hole_charge_le {n : ℕ} (hn : 3 ≤ n) :
    ∑ S : HoleIndex n (upperThreshold n), holeCharge n S ≤ 1 / 4 := by
  have hn0 : 0 < n := by omega
  have hK : 0 < colorCount n := by simp [colorCount, hn0]
  have hchoose : ((n.choose (upperThreshold n) : ℕ) : ℝ) ≤
      (n : ℝ) ^ upperThreshold n := by exact_mod_cast Nat.choose_le_pow n (upperThreshold n)
  have hpowexp : (n : ℝ) ^ upperThreshold n =
      Real.exp ((upperThreshold n : ℝ) * Real.log n) := by
    symm
    calc
      Real.exp ((upperThreshold n : ℝ) * Real.log n) =
          Real.exp (Real.log n) ^ upperThreshold n :=
        Real.exp_nat_mul _ _
      _ = (n : ℝ) ^ upperThreshold n := by rw [Real.exp_log (by positivity)]
  have hq : holeProbability n ≤
      Real.exp (-((upperThreshold n).choose 3 : ℕ) / colorCount n) := by
    have hbase : (((colorCount n - 1 : ℕ) : ℝ) / colorCount n) =
        1 - 1 / (colorCount n : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      field_simp
      ring
    rw [holeProbability, hbase]
    have hbase0 : 0 ≤ 1 - 1 / (colorCount n : ℝ) := by
      have hKone : (1 : ℝ) ≤ colorCount n := by exact_mod_cast hK
      rw [sub_nonneg]
      exact div_le_one (by positivity) |>.2 (by simpa using hKone)
    calc
      (1 - 1 / (colorCount n : ℝ)) ^ (upperThreshold n).choose 3 ≤
          (Real.exp (-(1 / (colorCount n : ℝ)))) ^
            (upperThreshold n).choose 3 := by
        exact pow_le_pow_left₀ hbase0 (Real.one_sub_le_exp_neg _) _
      _ = Real.exp (-((upperThreshold n).choose 3 : ℕ) /
          colorCount n) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hcorr : 2 * overlapCharge n *
      (6 * n * (upperThreshold n).choose 3 : ℕ) =
      ((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ) := by
    simp only [overlapCharge, colorCount]
    push_cast
    field_simp
    ring
  have hexponent := exponential_exponent_le hn
  simp only [holeCharge, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_holeIndex]
  rw [hcorr]
  calc
    (n.choose (upperThreshold n) : ℝ) *
        (2 * holeProbability n *
          Real.exp (((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ))) ≤
      2 * Real.exp ((upperThreshold n : ℝ) * Real.log n -
        ((upperThreshold n).choose 3 : ℕ) / (192 * n : ℝ)) := by
          have hnonneg : 0 ≤ holeProbability n := by
            unfold holeProbability
            positivity
          calc
            _ ≤ (n : ℝ) ^ upperThreshold n *
                (2 * holeProbability n * Real.exp
                  (((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ))) := by
              gcongr
            _ ≤ (n : ℝ) ^ upperThreshold n *
                (2 * Real.exp (-((upperThreshold n).choose 3 : ℕ) /
                    colorCount n) * Real.exp
                  (((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ))) := by
              gcongr
            _ = _ := by
              rw [hpowexp]
              calc
                Real.exp ((upperThreshold n : ℝ) * Real.log n) *
                    (2 * Real.exp (-((upperThreshold n).choose 3 : ℕ) /
                      colorCount n) * Real.exp
                      (((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ))) =
                    2 * (Real.exp ((upperThreshold n : ℝ) * Real.log n) *
                      Real.exp (-((upperThreshold n).choose 3 : ℕ) /
                        colorCount n)) * Real.exp
                      (((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ)) := by ring
                _ = 2 * Real.exp
                      ((upperThreshold n : ℝ) * Real.log n +
                        (-((upperThreshold n).choose 3 : ℕ) / colorCount n)) *
                      Real.exp (((upperThreshold n).choose 3 : ℕ) /
                        (576 * n : ℝ)) := by rw [Real.exp_add]
                _ = 2 * Real.exp
                    (((upperThreshold n : ℝ) * Real.log n +
                      (-((upperThreshold n).choose 3 : ℕ) / colorCount n)) +
                      ((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ)) := by
                    symm
                    rw [Real.exp_add]
                    ring
                _ = 2 * Real.exp ((upperThreshold n : ℝ) * Real.log n -
                    ((upperThreshold n).choose 3 : ℕ) / (192 * n : ℝ)) := by
                    congr 2
                    simp only [colorCount]
                    push_cast
                    field_simp
                    ring
    _ ≤ 2 * Real.exp (-3) := by gcongr
    _ ≤ 1 / 4 := two_mul_exp_neg_three_le_quarter

lemma holeCharge_nonneg {n : ℕ} (S : HoleIndex n (upperThreshold n)) :
    0 ≤ holeCharge n S := by
  unfold holeCharge holeProbability
  positivity

/-- The fully quantified upper construction at the explicit threshold. -/
theorem exists_upper_system (n : ℕ) (hn : 3 ≤ n) :
    ∃ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) ∧
      (∀ ⦃e⦄, e ∈ H → ∀ ⦃f⦄, f ∈ H → e ≠ f → (e ∩ f).card ≤ 1) ∧
      (∀ S : Finset (Fin n), S.card = upperThreshold n →
        ∃ e ∈ H, e ⊆ S) := by
  have hn0 : 0 < n := by omega
  have hK : 0 < colorCount n := by simp [colorCount, hn0]
  let : NeZero (colorCount n) := ⟨hK.ne'⟩
  let selected : Fin (colorCount n) := ⟨0, hK⟩
  have htotal := total_hole_charge_le hn
  have hxB1 : ∀ S : HoleIndex n (upperThreshold n), holeCharge n S < 1 := by
    intro S
    have hsingle : holeCharge n S ≤
        ∑ T : HoleIndex n (upperThreshold n), holeCharge n T :=
      Finset.single_le_sum (fun T _ ↦ holeCharge_nonneg T) (Finset.mem_univ S)
    linarith
  have hcriterion := twoCharge_criterion
    (n := n) (t := upperThreshold n) (K := colorCount n)
    (overlapCharge n) (holeCharge n)
    rfl (overlapCharge_nonneg n) ((overlapCharge_le_half hn0).trans (by norm_num))
    (fun S ↦ holeCharge_nonneg S) (fun S ↦ (hxB1 S).le)
    htotal (overlap_loss_le hn0) (fun S ↦ by
      simpa [holeProbability, badProbability] using hole_criterion hn0 S)
  exact exists_linear_hitting_system_of_charges selected
    (twoCharge (overlapCharge n) (holeCharge n))
    (fun i ↦ by cases i <;> simp [twoCharge, overlapCharge_nonneg, holeCharge_nonneg])
    (fun i ↦ by
      cases i with
      | inl _ =>
          dsimp [twoCharge]
          exact (overlapCharge_le_half hn0).trans_lt (by norm_num)
      | inr S => simpa [twoCharge] using hxB1 S)
    hcriterion

end Upper
end OMA1024

-- ===== from plby module ErdosProblems.Erdos1024.LowerMatching =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

The link of a vertex in a linear triple system is a matching.  This file
contains the exact finite averaging estimate used in the weighted
independent-set argument.  It deliberately uses only natural-number sums;
no probability or limiting binomial estimate is hidden in the statement.
-/

open scoped BigOperators

namespace OMA1024
namespace Lower

variable {V : Type*} [DecidableEq V]

/-- The number of members of `M` which are wholly selected by `S`. -/
def coveredPairs (M : Finset (Finset V)) (S : Finset V) : ℕ :=
  (M.filter (· ⊆ S)).card

@[simp] lemma coveredPairs_eq_zero {M : Finset (Finset V)} {S : Finset V} :
    coveredPairs M S = 0 ↔ ∀ e ∈ M, ¬ e ⊆ S := by
  simp [coveredPairs, Finset.card_eq_zero]

lemma coveredPairs_le_card (M : Finset (Finset V)) (S : Finset V) :
    coveredPairs M S ≤ M.card := by
  exact Finset.card_filter_le _ _

lemma sum_indicator_superset {J e : Finset V} (heJ : e ⊆ J) :
    ∑ S ∈ J.powerset, (if e ⊆ S then (1 : ℕ) else 0) =
      2 ^ (J.card - e.card) := by
  classical
  calc
    ∑ S ∈ J.powerset, (if e ⊆ S then (1 : ℕ) else 0) =
        ((J.powerset).filter (e ⊆ ·)).card := by
          exact Finset.sum_boole (e ⊆ ·) J.powerset
    _ = (Finset.Icc e J).card := by
      congr 1
      ext S
      simp [Finset.mem_Icc, and_comm]
    _ = 2 ^ (J.card - e.card) := by
      exact Finset.card_Icc_finset heJ

/-- Double-count incidences `(pair, subset containing the pair)`. -/
lemma sum_coveredPairs {J : Finset V} {M : Finset (Finset V)}
    (hMJ : ∀ e ∈ M, e ⊆ J) (hM2 : ∀ e ∈ M, e.card = 2) :
    ∑ S ∈ J.powerset, coveredPairs M S = M.card * 2 ^ (J.card - 2) := by
  classical
  have hcover : ∀ S, coveredPairs M S =
      ∑ e ∈ M, (if e ⊆ S then (1 : ℕ) else 0) := by
    intro S
    unfold coveredPairs
    exact (Finset.sum_boole (· ⊆ S) M).symm
  simp_rw [hcover]
  rw [Finset.sum_comm]
  calc
    ∑ e ∈ M, ∑ S ∈ J.powerset, (if e ⊆ S then (1 : ℕ) else 0) =
        ∑ e ∈ M, 2 ^ (J.card - e.card) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [sum_indicator_superset (hMJ e he)]
    _ = ∑ _e ∈ M, 2 ^ (J.card - 2) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [hM2 e he]
    _ = M.card * 2 ^ (J.card - 2) := by simp

lemma mul_min_ge {B k j : ℕ} (hBk : B ≤ k) (hjk : j ≤ k) :
    B * j ≤ k * min j B := by
  by_cases hjB : j ≤ B
  · rw [min_eq_left hjB]
    exact Nat.mul_le_mul_right j hBk
  · rw [min_eq_right (Nat.le_of_not_ge hjB)]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left B hjk

/-- If a matching has at least `B` pairs, truncating the number of selected
pairs at `B` loses at most a factor four in its powerset average. -/
lemma four_mul_sum_min_coveredPairs
    {J : Finset V} {M : Finset (Finset V)} {B : ℕ}
    (hB : 0 < B) (hBM : B ≤ M.card)
    (hMJ : ∀ e ∈ M, e ⊆ J) (hM2 : ∀ e ∈ M, e.card = 2) :
    B * 2 ^ J.card ≤
      4 * ∑ S ∈ J.powerset, min (coveredPairs M S) B := by
  classical
  have hMpos : 0 < M.card := hB.trans_le hBM
  have hpoint : ∀ S ∈ J.powerset,
      B * coveredPairs M S ≤ M.card * min (coveredPairs M S) B := by
    intro S _
    exact mul_min_ge hBM (coveredPairs_le_card M S)
  have hsum0 :
      (∑ S ∈ J.powerset, B * coveredPairs M S) ≤
        ∑ S ∈ J.powerset, M.card * min (coveredPairs M S) B :=
    Finset.sum_le_sum fun S hS ↦ hpoint S hS
  have hsum :
      B * (∑ S ∈ J.powerset, coveredPairs M S) ≤
        M.card * ∑ S ∈ J.powerset, min (coveredPairs M S) B := by
    simpa only [Finset.mul_sum] using hsum0
  have hdouble := sum_coveredPairs hMJ hM2
  rw [hdouble] at hsum
  have hJ2 : 2 ≤ J.card := by
    obtain ⟨e, heM⟩ := Finset.card_pos.mp hMpos
    exact (hM2 e heM) ▸ Finset.card_le_card (hMJ e heM)
  have hpow : 4 * 2 ^ (J.card - 2) = 2 ^ J.card := by
    calc
      4 * 2 ^ (J.card - 2) = 2 ^ 2 * 2 ^ (J.card - 2) := by norm_num
      _ = 2 ^ (2 + (J.card - 2)) := (pow_add 2 2 (J.card - 2)).symm
      _ = 2 ^ J.card := by rw [Nat.add_sub_of_le hJ2]
  have hcancel :
      B * 2 ^ (J.card - 2) ≤
        ∑ S ∈ J.powerset, min (coveredPairs M S) B := by
    apply Nat.le_of_mul_le_mul_left
    · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum
    · exact hMpos
  calc
    B * 2 ^ J.card = 4 * (B * 2 ^ (J.card - 2)) := by
      rw [← hpow]
      ac_rfl
    _ ≤ 4 * ∑ S ∈ J.powerset, min (coveredPairs M S) B :=
      Nat.mul_le_mul_left 4 hcancel

end Lower
end OMA1024


-- ===== from plby module ErdosProblems.Erdos1024.LowerStructure =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

This is the deterministic part of the Kostochka--Mubayi--Verstraëte
argument.  After conditioning outside the closed neighborhood of a vertex,
the remaining admissible neighbors form an independent set and the edges
through the vertex form a matching.
-/

namespace OMA1024
namespace Lower

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev System (V : Type*) := Finset (Finset V)

def ThreeUniform (H : System V) : Prop :=
  ∀ e ∈ H, e.card = 3

def Linear (H : System V) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ∀ ⦃f⦄, f ∈ H → e ≠ f → (e ∩ f).card ≤ 1

def Independent (H : System V) (I : Finset V) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ¬ e ⊆ I

instance independentDecidable (H : System V) (I : Finset V) :
    Decidable (Independent H I) := by
  unfold Independent
  infer_instance

/-- A loose triangle: the three pairwise intersections are singletons, but
there is no common vertex. -/
def HasLooseTriangle (H : System V) : Prop :=
  ∃ e ∈ H, ∃ f ∈ H, ∃ g ∈ H,
    e ≠ f ∧ e ≠ g ∧ f ≠ g ∧
    (e ∩ f).card = 1 ∧ (e ∩ g).card = 1 ∧
    (f ∩ g).card = 1 ∧ (e ∩ f ∩ g).card = 0

def TriangleFree (H : System V) : Prop :=
  ¬ HasLooseTriangle H

def neighborhood (H : System V) (v : V) : Finset V :=
  Finset.univ.filter fun u ↦
    u ≠ v ∧ ∃ e ∈ H, v ∈ e ∧ u ∈ e

@[simp] lemma mem_neighborhood {H : System V} {v u : V} :
    u ∈ neighborhood H v ↔ u ≠ v ∧ ∃ e ∈ H, v ∈ e ∧ u ∈ e := by
  simp [neighborhood]

@[simp] lemma not_mem_neighborhood_self (H : System V) (v : V) :
    v ∉ neighborhood H v := by simp

def closedNeighborhood (H : System V) (v : V) : Finset V :=
  insert v (neighborhood H v)

def outsidePart (H : System V) (v : V) (I : Finset V) : Finset V :=
  I \ closedNeighborhood H v

/-- Neighbors which may individually be adjoined to the conditioned
outside part. -/
def available (H : System V) (v : V) (R : Finset V) : Finset V :=
  (neighborhood H v).filter fun u ↦ Independent H (insert u R)

@[simp] lemma mem_available {H : System V} {v u : V} {R : Finset V} :
    u ∈ available H v R ↔
      u ∈ neighborhood H v ∧ Independent H (insert u R) := by
  simp [available]

/-- The two-vertex remainders of edges through `v` whose remainder lies in
`J`. -/
def linkPairs (H : System V) (v : V) (J : Finset V) :
    Finset (Finset V) :=
  (H.filter fun e ↦ v ∈ e ∧ e.erase v ⊆ J).image fun e ↦ e.erase v

omit [Fintype V] in
lemma mem_linkPairs {H : System V} {v : V} {J a : Finset V} :
    a ∈ linkPairs H v J ↔
      ∃ e ∈ H, v ∈ e ∧ e.erase v ⊆ J ∧ e.erase v = a := by
  classical
  simp [linkPairs, and_assoc]

omit [Fintype V] in
lemma linkPairs_subset {H : System V} {v : V} {J : Finset V}
    {a : Finset V} (ha : a ∈ linkPairs H v J) : a ⊆ J := by
  obtain ⟨e, -, -, heJ, rfl⟩ := mem_linkPairs.mp ha
  exact heJ

omit [Fintype V] in
lemma linkPairs_card_two {H : System V} (h3 : ThreeUniform H)
    {v : V} {J : Finset V} {a : Finset V} (ha : a ∈ linkPairs H v J) :
    a.card = 2 := by
  obtain ⟨e, heH, hve, -, rfl⟩ := mem_linkPairs.mp ha
  rw [Finset.card_erase_of_mem hve, h3 e heH]

omit [Fintype V] in
lemma linkPairs_pairwiseDisjoint {H : System V} (hlin : Linear H)
    {v : V} {J : Finset V} :
    (linkPairs H v J : Set (Finset V)).PairwiseDisjoint id := by
  classical
  intro a ha b hb hab
  change Disjoint a b
  rw [Finset.disjoint_left]
  intro x hxa hxb
  obtain ⟨e, heH, hve, -, hea⟩ := mem_linkPairs.mp ha
  obtain ⟨f, hfH, hvf, -, hfb⟩ := mem_linkPairs.mp hb
  have hxe : x ∈ e := Finset.mem_of_mem_erase (hea ▸ hxa)
  have hxf : x ∈ f := Finset.mem_of_mem_erase (hfb ▸ hxb)
  have hxv : x ≠ v := (Finset.mem_erase.mp (hea ▸ hxa)).1
  have htwo : 2 ≤ (e ∩ f).card := by
    have hsub : ({v, x} : Finset V) ⊆ e ∩ f := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · simp [hve, hvf]
      · simp [hxe, hxf]
    have hc := Finset.card_le_card hsub
    simpa [hxv, Ne.symm hxv] using hc
  have hef : e = f := by
    by_contra hne
    exact (not_lt_of_ge htwo) (lt_of_le_of_lt (hlin heH hfH hne) (by omega))
  apply hab
  rw [← hea, ← hfb, hef]

lemma vertex_of_edge_neighborhood {H : System V} {v x : V} {e : Finset V}
    (heH : e ∈ H) (hve : v ∈ e) (hxe : x ∈ e) (hxv : x ≠ v) :
    x ∈ neighborhood H v := by
  exact mem_neighborhood.mpr ⟨hxv, e, heH, hve, hxe⟩

lemma vertex_not_mem_of_disjoint_closed {H : System V} {v : V} {R : Finset V}
    (hdisj : Disjoint R (closedNeighborhood H v)) : v ∉ R := by
  intro hvR
  exact Finset.disjoint_left.mp hdisj hvR (by simp [closedNeighborhood])

lemma available_ne_self {H : System V} {v u : V} {R : Finset V}
    (hu : u ∈ available H v R) : u ≠ v :=
  (mem_neighborhood.mp (mem_available.mp hu).1).1

/-- The admissible neighbor set after conditioning is independent.  This is
exactly where loose triangles have to be deleted. -/
theorem independent_union_available {H : System V}
    (hlin : Linear H) (htri : TriangleFree H)
    {v : V} {R : Finset V} (hR : Independent H R)
    (hdisj : Disjoint R (closedNeighborhood H v)) :
    Independent H (R ∪ available H v R) := by
  classical
  intro e heH heSub
  have hnotR : ¬ e ⊆ R := hR heH
  obtain ⟨u, hue, huR⟩ := Set.not_subset.mp hnotR
  have huJ : u ∈ available H v R := by
    have := heSub hue
    exact (Finset.mem_union.mp this).resolve_left huR
  have hIndu := (mem_available.mp huJ).2
  have hnotInsert : ¬ e ⊆ insert u R := hIndu heH
  obtain ⟨w, hwe, hwInsert⟩ := Set.not_subset.mp hnotInsert
  have hwR : w ∉ R := fun hw ↦ hwInsert (Finset.mem_insert_of_mem hw)
  have hwu : w ≠ u := fun h ↦ hwInsert (h ▸ Finset.mem_insert_self u R)
  have hwJ : w ∈ available H v R := by
    have := heSub hwe
    exact (Finset.mem_union.mp this).resolve_left hwR
  obtain ⟨-, eu, heuH, hveu, hueu⟩ := mem_neighborhood.mp (mem_available.mp huJ).1
  obtain ⟨-, ew, hewH, hvew, hwew⟩ := mem_neighborhood.mp (mem_available.mp hwJ).1
  have hvR : v ∉ R := vertex_not_mem_of_disjoint_closed hdisj
  have hvJ : v ∉ available H v R := by
    intro hv
    exact (available_ne_self hv) rfl
  have hve : v ∉ e := by
    intro hve'
    have := heSub hve'
    rcases Finset.mem_union.mp this with h | h
    · exact hvR h
    · exact hvJ h
  have he_ne_eu : e ≠ eu := fun h ↦ hve (h ▸ hveu)
  have he_ne_ew : e ≠ ew := fun h ↦ hve (h ▸ hvew)
  have heu_ne_ew : eu ≠ ew := by
    intro hEq
    have hsub : ({u, w} : Finset V) ⊆ e ∩ eu := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hue, hueu⟩
      · exact Finset.mem_inter.mpr ⟨hwe, hEq ▸ hwew⟩
    have hcard : 2 ≤ (e ∩ eu).card := by
      have := Finset.card_le_card hsub
      simpa [hwu.symm] using this
    exact (not_lt_of_ge hcard) (lt_of_le_of_lt
      (hlin heH heuH he_ne_eu) (by omega))
  have hef_card : (e ∩ eu).card = 1 := by
    apply Nat.le_antisymm (hlin heH heuH he_ne_eu)
    exact Finset.one_le_card.mpr ⟨u, Finset.mem_inter.mpr ⟨hue, hueu⟩⟩
  have heg_card : (e ∩ ew).card = 1 := by
    apply Nat.le_antisymm (hlin heH hewH he_ne_ew)
    exact Finset.one_le_card.mpr ⟨w, Finset.mem_inter.mpr ⟨hwe, hwew⟩⟩
  have hfg_card : (eu ∩ ew).card = 1 := by
    apply Nat.le_antisymm (hlin heuH hewH heu_ne_ew)
    exact Finset.one_le_card.mpr ⟨v, by simp [hveu, hvew]⟩
  have htriple : (e ∩ eu ∩ ew).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx_e : x ∈ e := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
    have hx_eu : x ∈ eu := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2
    have hx_ew : x ∈ ew := (Finset.mem_inter.mp hx).2
    have hx_inter : x ∈ eu ∩ ew := Finset.mem_inter.mpr ⟨hx_eu, hx_ew⟩
    have hv_inter : v ∈ eu ∩ ew := Finset.mem_inter.mpr ⟨hveu, hvew⟩
    have hxv : x = v := by
      exact (Finset.card_le_one.mp hfg_card.le) x hx_inter v hv_inter
    exact hve (hxv ▸ hx_e)
  apply htri
  exact ⟨e, heH, eu, heuH, ew, hewH, he_ne_eu, he_ne_ew,
    heu_ne_ew, hef_card, heg_card, hfg_card, htriple⟩

end Lower
end OMA1024


-- ===== from plby module ErdosProblems.Erdos1024.LowerWeighted =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

This file proves a deliberately coarse, completely finite version of KMV
Lemma 5 for linear triangle-free triple systems.  The weight
`B * 4^B` is larger than KMV's optimized exponential weight, which makes
the matching calculation elementary while retaining the required order of
magnitude.
-/

open scoped BigOperators

namespace OMA1024
namespace Lower

variable {V : Type*} [Fintype V] [DecidableEq V]

def independentSets (H : System V) : Finset (Finset V) :=
  Finset.univ.powerset.filter (Independent H)

@[simp] lemma mem_independentSets {H : System V} {I : Finset V} :
    I ∈ independentSets H ↔ Independent H I := by
  simp [independentSets]

omit [Fintype V] [DecidableEq V] in
lemma independent_mono {H : System V} {I J : Finset V}
    (hI : Independent H I) (hJI : J ⊆ I) : Independent H J := by
  intro e heH heJ
  exact hI heH (heJ.trans hJI)

/-- The number of link pairs through `v` fully contained in `I`. -/
def extensionCount (H : System V) (v : V) (I : Finset V) : ℕ :=
  coveredPairs (linkPairs H v (neighborhood H v)) (I ∩ neighborhood H v)

def truncatedExtension (H : System V) (B : ℕ) (v : V) (I : Finset V) : ℕ :=
  min (extensionCount H v I) B

def pivotWeight (H : System V) (B : ℕ) (v : V) (I : Finset V) : ℕ :=
  if v ∈ I then B * 4 ^ B else truncatedExtension H B v I

def omitImage (R J : Finset V) : Finset (Finset V) :=
  J.powerset.image fun S ↦ R ∪ S

def containImage (v : V) (R J : Finset V) : Finset (Finset V) :=
  J.powerset.image fun S ↦ insert v (R ∪ S)

def baseFiber (H : System V) (v : V) (R : Finset V) :
    Finset (Finset V) :=
  (independentSets H).filter fun I ↦ outsidePart H v I = R

lemma available_subset_neighborhood (H : System V) (v : V) (R : Finset V) :
    available H v R ⊆ neighborhood H v := by
  intro u hu
  exact (mem_available.mp hu).1

lemma outsidePart_subset (H : System V) (v : V) (I : Finset V) :
    outsidePart H v I ⊆ I := by
  exact Finset.sdiff_subset

lemma outsidePart_disjoint (H : System V) (v : V) (I : Finset V) :
    Disjoint (outsidePart H v I) (closedNeighborhood H v) := by
  exact Finset.sdiff_disjoint

lemma outsidePart_union_of_disjoint {H : System V} {v : V}
    {R S : Finset V} (hR : Disjoint R (closedNeighborhood H v))
    (hS : S ⊆ neighborhood H v) :
    outsidePart H v (R ∪ S) = R := by
  ext x
  constructor
  · intro hx
    have hxU := (Finset.mem_sdiff.mp hx).1
    have hxC := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_union.mp hxU with hxR | hxS
    · exact hxR
    · exact False.elim (hxC (by
        simp only [closedNeighborhood, Finset.mem_insert]
        exact Or.inr (hS hxS)))
  · intro hxR
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hxR, ?_⟩
    intro hxC
    exact Finset.disjoint_left.mp hR hxR hxC

lemma outsidePart_insert_union_of_disjoint {H : System V} {v : V}
    {R S : Finset V} (hR : Disjoint R (closedNeighborhood H v))
    (hS : S ⊆ neighborhood H v) :
    outsidePart H v (insert v (R ∪ S)) = R := by
  ext x
  constructor
  · intro hx
    have hxI := (Finset.mem_sdiff.mp hx).1
    have hxC := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_insert.mp hxI with rfl | hxU
    · exact False.elim (hxC (by simp [closedNeighborhood]))
    · rcases Finset.mem_union.mp hxU with hxR | hxS
      · exact hxR
      · exact False.elim (hxC (by
          simp only [closedNeighborhood, Finset.mem_insert]
          exact Or.inr (hS hxS)))
  · intro hxR
    refine Finset.mem_sdiff.mpr ⟨by simp [hxR], ?_⟩
    intro hxC
    exact Finset.disjoint_left.mp hR hxR hxC

lemma union_available_independent {H : System V}
    (hlin : Linear H) (htri : TriangleFree H)
    {v : V} {R S : Finset V} (hR : Independent H R)
    (hdisj : Disjoint R (closedNeighborhood H v))
    (hSJ : S ⊆ available H v R) :
    Independent H (R ∪ S) := by
  apply independent_mono (independent_union_available (H := H)
    hlin htri hR hdisj)
  exact Finset.union_subset_union Finset.Subset.rfl hSJ

omit [Fintype V] in
lemma union_right_injective_of_disjoint {R J : Finset V}
    (hRJ : Disjoint R J) : Set.InjOn (fun S : Finset V ↦ R ∪ S) J.powerset := by
  intro S hS T hT hEq
  apply Finset.ext
  intro x
  have hSsub := Finset.mem_powerset.mp hS
  have hTsub := Finset.mem_powerset.mp hT
  have hxRnotS : x ∈ R → x ∉ S := fun hxR hxS ↦
    Finset.disjoint_left.mp hRJ hxR (hSsub hxS)
  have hxRnotT : x ∈ R → x ∉ T := fun hxR hxT ↦
    Finset.disjoint_left.mp hRJ hxR (hTsub hxT)
  by_cases hxR : x ∈ R
  · simp [hxRnotS hxR, hxRnotT hxR]
  · have hm := Finset.ext_iff.mp hEq x
    simpa [hxR] using hm

omit [Fintype V] in
lemma insert_union_injective_of_disjoint {v : V} {R J : Finset V}
    (hvR : v ∉ R) (hvJ : v ∉ J) (hRJ : Disjoint R J) :
    Set.InjOn (fun S : Finset V ↦ insert v (R ∪ S)) J.powerset := by
  intro S hS T hT hEq
  apply union_right_injective_of_disjoint hRJ hS hT
  have hSsub := Finset.mem_powerset.mp hS
  have hTsub := Finset.mem_powerset.mp hT
  have hvS : v ∉ S := fun h ↦ hvJ (hSsub h)
  have hvT : v ∉ T := fun h ↦ hvJ (hTsub h)
  have hvRS : v ∉ R ∪ S := by simp [hvR, hvS]
  have hvRT : v ∉ R ∪ T := by simp [hvR, hvT]
  have hErase := congrArg (fun U : Finset V ↦ U.erase v) hEq
  simpa [hvRS, hvRT] using hErase

lemma extensionCount_union {H : System V} {v : V} {R S : Finset V}
    (hdisj : Disjoint R (closedNeighborhood H v))
    (hSJ : S ⊆ available H v R) :
    extensionCount H v (R ∪ S) =
      coveredPairs (linkPairs H v (available H v R)) S := by
  classical
  unfold extensionCount coveredPairs
  congr 1
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ha, haSub⟩
    obtain ⟨e, heH, hve, -, hea⟩ := mem_linkPairs.mp ha
    have haN : a ⊆ neighborhood H v := linkPairs_subset ha
    have haS : a ⊆ S := by
      intro x hxa
      have hxBoth := haSub hxa
      have hxUnion := (Finset.mem_inter.mp hxBoth).1
      rcases Finset.mem_union.mp hxUnion with hxR | hxS
      · exact False.elim (Finset.disjoint_left.mp hdisj hxR
          (by simp [closedNeighborhood, haN hxa]))
      · exact hxS
    have haJ : a ⊆ available H v R := haS.trans hSJ
    have heJ : e.erase v ⊆ available H v R := by simpa [hea] using haJ
    exact ⟨mem_linkPairs.mpr ⟨e, heH, hve, heJ, hea⟩, haS⟩
  · rintro ⟨ha, haS⟩
    obtain ⟨e, heH, hve, haJ, hea⟩ := mem_linkPairs.mp ha
    have haN : a ⊆ neighborhood H v :=
      (by simpa [hea] using haJ.trans (available_subset_neighborhood H v R))
    have heN : e.erase v ⊆ neighborhood H v := by simpa [hea] using haN
    exact ⟨mem_linkPairs.mpr ⟨e, heH, hve, heN, hea⟩,
      fun x hx ↦ Finset.mem_inter.mpr
        ⟨Finset.mem_union.mpr (Or.inr (haS hx)), haN hx⟩⟩

lemma omitImage_subset_baseFiber {H : System V}
    (hlin : Linear H) (htri : TriangleFree H)
    {v : V} {R : Finset V} (hR : Independent H R)
    (hdisj : Disjoint R (closedNeighborhood H v)) :
    omitImage R (available H v R) ⊆ baseFiber H v R := by
  classical
  intro I hI
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  have hSJ := Finset.mem_powerset.mp hS
  simp only [baseFiber, Finset.mem_filter, mem_independentSets]
  exact ⟨union_available_independent hlin htri hR hdisj hSJ,
    outsidePart_union_of_disjoint hdisj
      (hSJ.trans (available_subset_neighborhood H v R))⟩

lemma baseFiber_subset_images {H : System V} {v : V} {R : Finset V} :
    baseFiber H v R ⊆
      omitImage R (available H v R) ∪
        containImage v R (available H v R) := by
  classical
  intro I hI
  have hIf := Finset.mem_filter.mp hI
  have hInd : Independent H I := mem_independentSets.mp hIf.1
  have hbase : outsidePart H v I = R := hIf.2
  let J := available H v R
  let S := I ∩ J
  have hSsub : S ⊆ J := Finset.inter_subset_right
  have hRsub : R ⊆ I := by
    rw [← hbase]
    exact outsidePart_subset H v I
  have hneighbor_available : ∀ x ∈ I, x ∈ neighborhood H v → x ∈ J := by
    intro x hxI hxN
    apply mem_available.mpr
    refine ⟨hxN, independent_mono hInd ?_⟩
    exact Finset.insert_subset hxI hRsub
  have hcover : I ⊆ insert v (R ∪ S) := by
    intro x hxI
    by_cases hxC : x ∈ closedNeighborhood H v
    · have hx : x = v ∨ x ∈ neighborhood H v := by
        simpa [closedNeighborhood] using hxC
      rcases hx with rfl | hxN
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hxI, hneighbor_available x hxI hxN⟩))
    · have hxOut : x ∈ outsidePart H v I := Finset.mem_sdiff.mpr ⟨hxI, hxC⟩
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hbase ▸ hxOut))
  have hback : insert v (R ∪ S) \ {v} ⊆ I := by
    intro x hx
    have hxIns := (Finset.mem_sdiff.mp hx).1
    have hxv := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_insert.mp hxIns with rfl | hxU
    · exact False.elim (hxv (by simp))
    · rcases Finset.mem_union.mp hxU with hxR | hxS
      · exact hRsub hxR
      · exact (Finset.mem_inter.mp hxS).1
  by_cases hvI : v ∈ I
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨S, Finset.mem_powerset.mpr hSsub, ?_⟩
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxU
      · exact hvI
      · rcases Finset.mem_union.mp hxU with hxR | hxS
        · exact hRsub hxR
        · exact (Finset.mem_inter.mp hxS).1
    · exact hcover
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨S, Finset.mem_powerset.mpr hSsub, ?_⟩
    apply Finset.Subset.antisymm
    · intro x hxU
      rcases Finset.mem_union.mp hxU with hxR | hxS
      · exact hRsub hxR
      · exact (Finset.mem_inter.mp hxS).1
    · intro x hxI
      have hxIns := hcover hxI
      exact (Finset.mem_insert.mp hxIns).resolve_left fun hxv ↦ hvI (hxv ▸ hxI)

lemma baseFiber_card_le {H : System V} {v : V} {R : Finset V} :
    (baseFiber H v R).card ≤ 2 * 2 ^ (available H v R).card := by
  classical
  let J := available H v R
  calc
    (baseFiber H v R).card ≤
        (omitImage R J ∪ containImage v R J).card :=
      Finset.card_le_card baseFiber_subset_images
    _ ≤ (omitImage R J).card + (containImage v R J).card :=
      Finset.card_union_le _ _
    _ ≤ J.powerset.card + J.powerset.card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = 2 * 2 ^ J.card := by simp [Finset.card_powerset]; ring

omit [Fintype V] in
lemma omitImage_card {R J : Finset V} (hRJ : Disjoint R J) :
    (omitImage R J).card = 2 ^ J.card := by
  classical
  unfold omitImage
  rw [Finset.card_image_of_injOn (union_right_injective_of_disjoint hRJ),
    Finset.card_powerset]

lemma pivotWeight_union {H : System V} {B : ℕ} {v : V} {R S : Finset V}
    (hdisj : Disjoint R (closedNeighborhood H v))
    (hSJ : S ⊆ available H v R) :
    pivotWeight H B v (R ∪ S) =
      min (coveredPairs (linkPairs H v (available H v R)) S) B := by
  have hvR : v ∉ R := vertex_not_mem_of_disjoint_closed hdisj
  have hvJ : v ∉ available H v R := by
    intro hv
    exact available_ne_self hv rfl
  have hvS : v ∉ S := fun hv ↦ hvJ (hSJ hv)
  rw [pivotWeight, if_neg (by simp [hvR, hvS]), truncatedExtension,
    extensionCount_union hdisj hSJ]

lemma sum_pivotWeight_omitImage {H : System V} {B : ℕ} {v : V}
    {R : Finset V} (hdisj : Disjoint R (closedNeighborhood H v)) :
    ∑ I ∈ omitImage R (available H v R), pivotWeight H B v I =
      ∑ S ∈ (available H v R).powerset,
        min (coveredPairs (linkPairs H v (available H v R)) S) B := by
  classical
  have hRJ : Disjoint R (available H v R) :=
    hdisj.mono_right (available_subset_neighborhood H v R |>.trans (by
      intro x hx
      simp [closedNeighborhood, hx]))
  unfold omitImage
  rw [Finset.sum_image (union_right_injective_of_disjoint hRJ)]
  apply Finset.sum_congr rfl
  intro S hS
  exact pivotWeight_union hdisj (Finset.mem_powerset.mp hS)

theorem baseFiber_weighted_large {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {B : ℕ} (hB : 0 < B) {v : V} {R : Finset V}
    (hR : Independent H R) (hdisj : Disjoint R (closedNeighborhood H v))
    (hlarge : B ≤ (linkPairs H v (available H v R)).card) :
    B * (baseFiber H v R).card ≤
      8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I := by
  classical
  let J := available H v R
  let M := linkPairs H v J
  have hmatch := four_mul_sum_min_coveredPairs (J := J) (M := M)
    hB hlarge (fun e he ↦ linkPairs_subset he)
    (fun e he ↦ linkPairs_card_two h3 he)
  have hOsub := omitImage_subset_baseFiber hlin htri hR hdisj
  have hsum :
      (∑ I ∈ omitImage R J, pivotWeight H B v I) ≤
        ∑ I ∈ baseFiber H v R, pivotWeight H B v I :=
    Finset.sum_le_sum_of_subset hOsub
  rw [sum_pivotWeight_omitImage hdisj] at hsum
  have hcard := baseFiber_card_le (H := H) (v := v) (R := R)
  calc
    B * (baseFiber H v R).card ≤ B * (2 * 2 ^ J.card) :=
      Nat.mul_le_mul_left B hcard
    _ = 2 * (B * 2 ^ J.card) := by ring
    _ ≤ 2 * (4 * ∑ S ∈ J.powerset, min (coveredPairs M S) B) :=
      Nat.mul_le_mul_left 2 hmatch
    _ = 8 * ∑ S ∈ J.powerset, min (coveredPairs M S) B := by ring
    _ ≤ 8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I :=
      Nat.mul_le_mul_left 8 hsum

def linkVertices (M : Finset (Finset V)) : Finset V :=
  M.biUnion id

def unusedVertices (J : Finset V) (M : Finset (Finset V)) : Finset V :=
  J \ linkVertices M

omit [Fintype V] in
lemma linkVertices_subset {J : Finset V} {M : Finset (Finset V)}
    (hMJ : ∀ e ∈ M, e ⊆ J) : linkVertices M ⊆ J := by
  intro x hx
  obtain ⟨e, heM, hxe⟩ := Finset.mem_biUnion.mp hx
  exact hMJ e heM hxe

omit [Fintype V] in
lemma card_linkVertices {H : System V} (h3 : ThreeUniform H)
    (hlin : Linear H) {v : V} {J : Finset V} :
    (linkVertices (linkPairs H v J)).card = 2 * (linkPairs H v J).card := by
  classical
  unfold linkVertices
  rw [Finset.card_biUnion (linkPairs_pairwiseDisjoint hlin)]
  calc
    ∑ e ∈ linkPairs H v J, e.card =
        ∑ _e ∈ linkPairs H v J, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [linkPairs_card_two h3 he]
    _ = 2 * (linkPairs H v J).card := by simp [Nat.mul_comm]

lemma card_available_eq_link_unused {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) {v : V} {R : Finset V} :
    (available H v R).card =
      2 * (linkPairs H v (available H v R)).card +
        (unusedVertices (available H v R)
          (linkPairs H v (available H v R))).card := by
  let J := available H v R
  let M := linkPairs H v J
  let U := linkVertices M
  let L := unusedVertices J M
  have hUJ : U ⊆ J := linkVertices_subset fun e he ↦ linkPairs_subset he
  have hcard := Finset.card_sdiff_add_card_eq_card hUJ
  have hUcard := card_linkVertices h3 hlin (v := v) (J := J)
  change J.card = 2 * M.card + L.card
  change L.card + U.card = J.card at hcard
  change U.card = 2 * M.card at hUcard
  omega

lemma independent_insert_union_unused {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {v : V} {R S : Finset V} (hR : Independent H R)
    (hdisj : Disjoint R (closedNeighborhood H v))
    (hSL : S ⊆ unusedVertices (available H v R)
      (linkPairs H v (available H v R))) :
    Independent H (insert v (R ∪ S)) := by
  classical
  let J := available H v R
  let M := linkPairs H v J
  let U := linkVertices M
  let L := unusedVertices J M
  have hLJ : L ⊆ J := Finset.sdiff_subset
  have hSJ : S ⊆ J := hSL.trans hLJ
  have hbaseInd := union_available_independent hlin htri hR hdisj hSJ
  intro e heH heSub
  by_cases hve : v ∈ e
  · let a := e.erase v
    have haS : a ⊆ S := by
      intro x hxa
      have hxe : x ∈ e := Finset.mem_of_mem_erase hxa
      have hxv : x ≠ v := (Finset.mem_erase.mp hxa).1
      have hxIns := heSub hxe
      have hxU := (Finset.mem_insert.mp hxIns).resolve_left fun h ↦ hxv h
      rcases Finset.mem_union.mp hxU with hxR | hxS
      · have hxN : x ∈ neighborhood H v :=
          vertex_of_edge_neighborhood heH hve hxe hxv
        exact False.elim (Finset.disjoint_left.mp hdisj hxR
          (by simp [closedNeighborhood, hxN]))
      · exact hxS
    have haJ : a ⊆ J := haS.trans hSJ
    have haM : a ∈ M := mem_linkPairs.mpr ⟨e, heH, hve, haJ, rfl⟩
    have haU : a ⊆ U := by
      intro x hxa
      exact Finset.mem_biUnion.mpr ⟨a, haM, hxa⟩
    have haL : a ⊆ L := haS.trans hSL
    have hdisUL : Disjoint U L := by
      dsimp [L, unusedVertices]
      exact Finset.disjoint_sdiff
    have haEmpty : a = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hxa
      exact Finset.disjoint_left.mp hdisUL (haU hxa) (haL hxa)
    have hacard : a.card = 2 := linkPairs_card_two h3 haM
    simp [haEmpty] at hacard
  · apply hbaseInd heH
    intro x hxe
    have hx := heSub hxe
    exact (Finset.mem_insert.mp hx).resolve_left fun hxv ↦ hve (hxv ▸ hxe)

lemma containUnused_subset_baseFiber {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {v : V} {R : Finset V} (hR : Independent H R)
    (hdisj : Disjoint R (closedNeighborhood H v)) :
    containImage v R
      (unusedVertices (available H v R)
        (linkPairs H v (available H v R))) ⊆ baseFiber H v R := by
  classical
  intro I hI
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  have hSL := Finset.mem_powerset.mp hS
  have hLN : unusedVertices (available H v R)
      (linkPairs H v (available H v R)) ⊆ neighborhood H v :=
    Finset.sdiff_subset.trans (available_subset_neighborhood H v R)
  simp only [baseFiber, Finset.mem_filter, mem_independentSets]
  exact ⟨independent_insert_union_unused h3 hlin htri hR hdisj hSL,
    outsidePart_insert_union_of_disjoint hdisj (hSL.trans hLN)⟩

lemma sum_pivotWeight_containUnused {H : System V} {B : ℕ} {v : V}
    {R : Finset V} (hdisj : Disjoint R (closedNeighborhood H v)) :
    ∑ I ∈ containImage v R
        (unusedVertices (available H v R)
          (linkPairs H v (available H v R))), pivotWeight H B v I =
      2 ^ (unusedVertices (available H v R)
        (linkPairs H v (available H v R))).card * (B * 4 ^ B) := by
  classical
  let J := available H v R
  let M := linkPairs H v J
  let L := unusedVertices J M
  have hvR : v ∉ R := vertex_not_mem_of_disjoint_closed hdisj
  have hvJ : v ∉ J := by
    intro hv
    exact available_ne_self hv rfl
  have hLJ : L ⊆ J := Finset.sdiff_subset
  have hvL : v ∉ L := fun hv ↦ hvJ (hLJ hv)
  have hRJ : Disjoint R J := hdisj.mono_right
    ((available_subset_neighborhood H v R).trans (by
      intro x hx
      simp [closedNeighborhood, hx]))
  have hRL : Disjoint R L := hRJ.mono_right hLJ
  unfold containImage
  rw [Finset.sum_image (insert_union_injective_of_disjoint hvR hvL hRL)]
  calc
    ∑ S ∈ L.powerset, pivotWeight H B v (insert v (R ∪ S)) =
        ∑ _S ∈ L.powerset, B * 4 ^ B := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [pivotWeight]
    _ = 2 ^ L.card * (B * 4 ^ B) := by
      simp [Finset.card_powerset, Nat.mul_comm]

theorem baseFiber_weighted_small {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {B : ℕ} {v : V} {R : Finset V}
    (hR : Independent H R) (hdisj : Disjoint R (closedNeighborhood H v))
    (hsmall : (linkPairs H v (available H v R)).card < B) :
    B * (baseFiber H v R).card ≤
      8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I := by
  classical
  let J := available H v R
  let M := linkPairs H v J
  let L := unusedVertices J M
  have hCsub := containUnused_subset_baseFiber h3 hlin htri hR hdisj
  have hsum :
      2 ^ L.card * (B * 4 ^ B) ≤
        ∑ I ∈ baseFiber H v R, pivotWeight H B v I := by
    rw [← sum_pivotWeight_containUnused hdisj]
    exact Finset.sum_le_sum_of_subset hCsub
  have hcard := baseFiber_card_le (H := H) (v := v) (R := R)
  have hJcard := card_available_eq_link_unused h3 hlin (v := v) (R := R)
  change J.card = 2 * M.card + L.card at hJcard
  have hkB : M.card ≤ B := hsmall.le
  have hpows : 4 ^ M.card ≤ 4 ^ B := Nat.pow_le_pow_right (by omega) hkB
  have hpowJ : 2 ^ J.card = 4 ^ M.card * 2 ^ L.card := by
    rw [hJcard, pow_add, pow_mul]
    norm_num
  calc
    B * (baseFiber H v R).card ≤ B * (2 * 2 ^ J.card) :=
      Nat.mul_le_mul_left B hcard
    _ = 2 * B * 4 ^ M.card * 2 ^ L.card := by rw [hpowJ]; ring
    _ ≤ 2 * B * 4 ^ B * 2 ^ L.card := by
      gcongr
    _ ≤ 8 * (2 ^ L.card * (B * 4 ^ B)) := by
      have htwo : 2 * (B * 4 ^ B * 2 ^ L.card) ≤
          8 * (B * 4 ^ B * 2 ^ L.card) :=
        Nat.mul_le_mul_right _ (by omega)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using htwo
    _ ≤ 8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I :=
      Nat.mul_le_mul_left 8 hsum

lemma independentSets_nonempty {H : System V} (h3 : ThreeUniform H) :
    (independentSets H).Nonempty := by
  refine ⟨∅, mem_independentSets.mpr ?_⟩
  intro e heH heSub
  have he0 : e = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
    simpa using heSub hx
  have := h3 e heH
  simp [he0] at this

theorem pivot_weighted_sum_at_vertex {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {B : ℕ} (hB : 0 < B) (v : V) :
    B * (independentSets H).card ≤
      8 * ∑ I ∈ independentSets H, pivotWeight H B v I := by
  classical
  have hlocal : ∀ R : Finset V,
      B * (baseFiber H v R).card ≤
        8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I := by
    intro R
    by_cases hF : (baseFiber H v R).Nonempty
    · obtain ⟨I, hIF⟩ := hF
      have hIf := Finset.mem_filter.mp hIF
      have hInd : Independent H I := mem_independentSets.mp hIf.1
      have hbase : outsidePart H v I = R := hIf.2
      have hR : Independent H R := by
        rw [← hbase]
        exact independent_mono hInd (outsidePart_subset H v I)
      have hdisj : Disjoint R (closedNeighborhood H v) := by
        rw [← hbase]
        exact outsidePart_disjoint H v I
      by_cases hk : B ≤ (linkPairs H v (available H v R)).card
      · exact baseFiber_weighted_large h3 hlin htri hB hR hdisj hk
      · exact baseFiber_weighted_small h3 hlin htri hR hdisj
          (Nat.lt_of_not_ge hk)
    · have hEmpty : baseFiber H v R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      simp [hEmpty]
  have hsum :
      ∑ R : Finset V, B * (baseFiber H v R).card ≤
        ∑ R : Finset V,
          8 * ∑ I ∈ baseFiber H v R, pivotWeight H B v I :=
    Finset.sum_le_sum fun R _ ↦ hlocal R
  have hcardFib :
      ∑ R : Finset V, (baseFiber H v R).card = (independentSets H).card := by
    symm
    apply Finset.card_eq_sum_card_fiberwise
    intro I hI
    exact Finset.mem_univ _
  have hsumFib :
      ∑ R : Finset V, ∑ I ∈ baseFiber H v R, pivotWeight H B v I =
        ∑ I ∈ independentSets H, pivotWeight H B v I := by
    exact Finset.sum_fiberwise (independentSets H) (outsidePart H v)
      (pivotWeight H B v)
  simpa only [← Finset.mul_sum, hcardFib, hsumFib] using hsum

/-- The KMV quantity `h_I(V)`, specialized to triple systems. -/
def totalTruncatedExtension (H : System V) (B : ℕ) (I : Finset V) : ℕ :=
  ∑ v ∈ Finset.univ \ I, truncatedExtension H B v I

lemma sum_pivotWeight_eq (H : System V) (B : ℕ) (I : Finset V) :
    ∑ v : V, pivotWeight H B v I =
      I.card * (B * 4 ^ B) + totalTruncatedExtension H B I := by
  classical
  unfold pivotWeight totalTruncatedExtension
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr
    (Finset.subset_univ I), Finset.sum_const, nsmul_eq_mul]
  congr 1
  apply Finset.sum_congr
  · ext v
    simp
  · intro v hv
    rfl

/-- Coarse finite KMV weighted inequality. -/
theorem weighted_independent_set_inequality {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {B : ℕ} (hB : 0 < B) :
    B * Fintype.card V * (independentSets H).card ≤
      8 * ∑ I ∈ independentSets H,
        (I.card * (B * 4 ^ B) + totalTruncatedExtension H B I) := by
  classical
  have hv := Finset.sum_le_sum fun v (_hv : v ∈ (Finset.univ : Finset V)) ↦
    pivot_weighted_sum_at_vertex h3 hlin htri hB v
  have hcomm :
      ∑ v : V, ∑ I ∈ independentSets H, pivotWeight H B v I =
        ∑ I ∈ independentSets H, ∑ v : V, pivotWeight H B v I := by
    exact Finset.sum_comm
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hv
  rw [hcomm] at hv
  simp_rw [sum_pivotWeight_eq] at hv
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hv

/-- If all independent sets have size at most `A` and truncated extension
sum at most `U`, the common number of independent sets cancels from the
weighted inequality. -/
theorem weighted_numeric_consequence {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (htri : TriangleFree H)
    {B A U : ℕ} (hB : 0 < B)
    (hcard : ∀ I, Independent H I → I.card ≤ A)
    (hext : ∀ I, Independent H I → totalTruncatedExtension H B I ≤ U) :
    B * Fintype.card V ≤ 8 * (A * (B * 4 ^ B) + U) := by
  classical
  let F := independentSets H
  have hweighted := weighted_independent_set_inequality h3 hlin htri hB
  have hpoint : ∀ I ∈ F,
      I.card * (B * 4 ^ B) + totalTruncatedExtension H B I ≤
        A * (B * 4 ^ B) + U := by
    intro I hI
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _ (hcard I (mem_independentSets.mp hI)))
      (hext I (mem_independentSets.mp hI))
  have hsum :
      (∑ I ∈ F, (I.card * (B * 4 ^ B) + totalTruncatedExtension H B I)) ≤
        F.card * (A * (B * 4 ^ B) + U) := by
    calc
      _ ≤ ∑ _I ∈ F, (A * (B * 4 ^ B) + U) :=
        Finset.sum_le_sum fun I hI ↦ hpoint I hI
      _ = F.card * (A * (B * 4 ^ B) + U) := by simp
  have hmul :
      (B * Fintype.card V) * F.card ≤
        (8 * (A * (B * 4 ^ B) + U)) * F.card := by
    calc
      (B * Fintype.card V) * F.card =
          B * Fintype.card V * (independentSets H).card := rfl
      _ ≤ 8 * ∑ I ∈ independentSets H,
          (I.card * (B * 4 ^ B) + totalTruncatedExtension H B I) := hweighted
      _ ≤ 8 * (F.card * (A * (B * 4 ^ B) + U)) :=
        Nat.mul_le_mul_left 8 hsum
      _ = (8 * (A * (B * 4 ^ B) + U)) * F.card := by ring
  apply Nat.le_of_mul_le_mul_right hmul
  exact (independentSets_nonempty h3).card_pos

end Lower
end OMA1024


-- ===== from plby module ErdosProblems.Erdos1024.LowerSampling =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

The random subset is represented by a uniform coloring `V → Fin K`; color
zero means selected.  All probability estimates below are finite sums over
this type.
-/

open scoped BigOperators

namespace OMA1024
namespace Lower

variable {V : Type*} [Fintype V] [DecidableEq V]

def pairsAt (H : System V) (v : V) (Z : Finset V) :
    Finset (Finset V) :=
  (linkPairs H v (neighborhood H v)).filter (· ⊆ Z)

lemma extensionCount_eq_card_pairsAt (H : System V) (v : V) (Z : Finset V) :
    extensionCount H v Z = (pairsAt H v Z).card := by
  classical
  unfold extensionCount coveredPairs pairsAt
  congr 1
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ha, haSub⟩
    exact ⟨ha, fun x hxa ↦ (Finset.mem_inter.mp (haSub hxa)).1⟩
  · rintro ⟨ha, haZ⟩
    have haN : a ⊆ neighborhood H v := linkPairs_subset ha
    exact ⟨ha, fun x hxa ↦ Finset.mem_inter.mpr ⟨haZ hxa, haN hxa⟩⟩

lemma pairsAt_subset_powersetCard {H : System V} (h3 : ThreeUniform H)
    {v : V} {Z : Finset V} : pairsAt H v Z ⊆ Z.powersetCard 2 := by
  intro a ha
  have h := Finset.mem_filter.mp ha
  exact Finset.mem_powersetCard.mpr
    ⟨h.2, linkPairs_card_two h3 h.1⟩

lemma pairsAt_disjoint_of_outside {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) {Z : Finset V}
    {v w : V} (hvZ : v ∉ Z) (hwZ : w ∉ Z) (hvw : v ≠ w) :
    Disjoint (pairsAt H v Z) (pairsAt H w Z) := by
  classical
  rw [Finset.disjoint_left]
  intro a hav haw
  have hav' := Finset.mem_filter.mp hav
  have haw' := Finset.mem_filter.mp haw
  obtain ⟨e, heH, hve, -, hea⟩ := mem_linkPairs.mp hav'.1
  obtain ⟨f, hfH, hwf, -, hfa⟩ := mem_linkPairs.mp haw'.1
  have haZ : a ⊆ Z := hav'.2
  have hvA : v ∉ a := fun h ↦ hvZ (haZ h)
  have hwA : w ∉ a := fun h ↦ hwZ (haZ h)
  have heq : e = insert v a := by
    rw [← hea]
    exact (Finset.insert_erase hve).symm
  have hfeq : f = insert w a := by
    rw [← hfa]
    exact (Finset.insert_erase hwf).symm
  have hef : e ≠ f := by
    intro h
    have hwE : w ∈ e := h ▸ hwf
    rw [heq] at hwE
    exact hwA ((Finset.mem_insert.mp hwE).resolve_left hvw.symm)
  have haInter : a ⊆ e ∩ f := by
    intro x hxa
    rw [heq, hfeq]
    simp [hxa]
  have htwo : 2 ≤ (e ∩ f).card := by
    have := Finset.card_le_card haInter
    simpa [linkPairs_card_two h3 hav'.1] using this
  exact (not_lt_of_ge htwo) (lt_of_le_of_lt (hlin heH hfH hef) (by omega))

/-- In a linear triple system, all extension pairs of an independent set
are distinct across outside vertices. -/
theorem sum_extensionCount_le_choose {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (Z : Finset V) :
    ∑ v ∈ Finset.univ \ Z, extensionCount H v Z ≤ Z.card.choose 2 := by
  classical
  let O : Finset V := Finset.univ \ Z
  have hpairwise : (O : Set V).PairwiseDisjoint (pairsAt H · Z) := by
    intro v hv w hw hvw
    exact pairsAt_disjoint_of_outside h3 hlin
      (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hw).2 hvw
  have hUnion : O.biUnion (pairsAt H · Z) ⊆ Z.powersetCard 2 := by
    intro a ha
    obtain ⟨v, hvO, hav⟩ := Finset.mem_biUnion.mp ha
    exact pairsAt_subset_powersetCard h3 hav
  calc
    ∑ v ∈ Finset.univ \ Z, extensionCount H v Z =
        ∑ v ∈ O, (pairsAt H v Z).card := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [extensionCount_eq_card_pairsAt]
    _ = (O.biUnion (pairsAt H · Z)).card :=
      (Finset.card_biUnion hpairwise).symm
    _ ≤ (Z.powersetCard 2).card := Finset.card_le_card hUnion
    _ = Z.card.choose 2 := Finset.card_powersetCard 2 Z

theorem totalTruncatedExtension_le_choose {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) (B : ℕ) (Z : Finset V) :
    totalTruncatedExtension H B Z ≤ Z.card.choose 2 := by
  unfold totalTruncatedExtension truncatedExtension
  calc
    ∑ v ∈ Finset.univ \ Z, min (extensionCount H v Z) B ≤
        ∑ v ∈ Finset.univ \ Z, extensionCount H v Z := by
      exact Finset.sum_le_sum fun _ _ ↦ min_le_left _ _
    _ ≤ _ := sum_extensionCount_le_choose h3 hlin Z

/-! ## Counting loose triangles -/

abbrev EdgeTriple (V : Type*) := (Finset V × Finset V) × Finset V

def IsLooseTriple (H : System V) (t : EdgeTriple V) : Prop :=
  let e := t.1.1
  let f := t.1.2
  let g := t.2
  e ∈ H ∧ f ∈ H ∧ g ∈ H ∧
    e ≠ f ∧ e ≠ g ∧ f ≠ g ∧
    (e ∩ f).card = 1 ∧ (e ∩ g).card = 1 ∧
    (f ∩ g).card = 1 ∧ (e ∩ f ∩ g).card = 0

instance isLooseTripleDecidable (H : System V) (t : EdgeTriple V) :
    Decidable (IsLooseTriple H t) := by
  unfold IsLooseTriple
  infer_instance

def looseTriangles (H : System V) : Finset (EdgeTriple V) :=
  ((H.product H).product H).filter (IsLooseTriple H)

omit [Fintype V] in
@[simp] lemma mem_looseTriangles {H : System V} {t : EdgeTriple V} :
    t ∈ looseTriangles H ↔ IsLooseTriple H t := by
  rw [looseTriangles, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨Finset.mem_product.mpr ⟨?_, h.2.2.1⟩, h⟩
    exact Finset.mem_product.mpr ⟨h.1, h.2.1⟩

omit [Fintype V] in
lemma hasLooseTriangle_iff_looseTriangles_nonempty {H : System V} :
    HasLooseTriangle H ↔ (looseTriangles H).Nonempty := by
  constructor
  · rintro ⟨e, he, f, hf, g, hg, hef, heg, hfg,
      hefCard, hegCard, hfgCard, htriple⟩
    exact ⟨((e, f), g), mem_looseTriangles.mpr
      ⟨he, hf, hg, hef, heg, hfg, hefCard, hegCard, hfgCard, htriple⟩⟩
  · rintro ⟨t, ht⟩
    rcases t with ⟨⟨e, f⟩, g⟩
    exact ⟨e, (mem_looseTriangles.mp ht).1,
      f, (mem_looseTriangles.mp ht).2.1,
      g, (mem_looseTriangles.mp ht).2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.2.2.2.2.1,
      (mem_looseTriangles.mp ht).2.2.2.2.2.2.2.2.2⟩

omit [Fintype V] in
lemma edge_eq_of_two_common {H : System V} (hlin : Linear H)
    {e f : Finset V} (he : e ∈ H) (hf : f ∈ H)
    {x y : V} (hxe : x ∈ e) (hxf : x ∈ f)
    (hye : y ∈ e) (hyf : y ∈ f) (hxy : x ≠ y) : e = f := by
  by_contra hef
  have hsub : ({x, y} : Finset V) ⊆ e ∩ f := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hxe, hxf⟩
    · exact Finset.mem_inter.mpr ⟨hye, hyf⟩
  have htwo : 2 ≤ (e ∩ f).card := by
    have := Finset.card_le_card hsub
    simpa [hxy, Ne.symm hxy] using this
  exact (not_lt_of_ge htwo) (lt_of_le_of_lt (hlin he hf hef) (by omega))

section TriangleCode

variable [LinearOrder V]

def singletonVertex (s : Finset V) (hs : s.card = 1) : V :=
  s.min' (Finset.card_pos.mp (by omega))

omit [Fintype V] [DecidableEq V] in
lemma singletonVertex_mem (s : Finset V) (hs : s.card = 1) :
    singletonVertex s hs ∈ s := by
  exact Finset.min'_mem _ _

abbrev LooseTriangle (H : System V) := {t : EdgeTriple V // t ∈ looseTriangles H}

def looseTriangleCode (H : System V) (t : LooseTriangle H) : V × V × V :=
  let h := mem_looseTriangles.mp t.property
  (singletonVertex (t.1.1.1 ∩ t.1.1.2) h.2.2.2.2.2.2.1,
    singletonVertex (t.1.1.1 ∩ t.1.2) h.2.2.2.2.2.2.2.1,
    singletonVertex (t.1.1.2 ∩ t.1.2) h.2.2.2.2.2.2.2.2.1)

omit [Fintype V] in
lemma looseTriangleCode_injective {H : System V} (hlin : Linear H) :
    Function.Injective (looseTriangleCode H) := by
  rintro ⟨t, ht⟩ ⟨u, hu⟩ hcode
  rcases t with ⟨⟨e, f⟩, g⟩
  rcases u with ⟨⟨e', f'⟩, g'⟩
  have h := mem_looseTriangles.mp ht
  have h' := mem_looseTriangles.mp hu
  let x := singletonVertex (e ∩ f) h.2.2.2.2.2.2.1
  let y := singletonVertex (e ∩ g) h.2.2.2.2.2.2.2.1
  let z := singletonVertex (f ∩ g) h.2.2.2.2.2.2.2.2.1
  let x' := singletonVertex (e' ∩ f') h'.2.2.2.2.2.2.1
  let y' := singletonVertex (e' ∩ g') h'.2.2.2.2.2.2.2.1
  let z' := singletonVertex (f' ∩ g') h'.2.2.2.2.2.2.2.2.1
  have hxyz : (x, y, z) = (x', y', z') := hcode
  have hxx' : x = x' := congrArg Prod.fst hxyz
  have hyy' : y = y' := congrArg (fun q ↦ q.2.1) hxyz
  have hzz' : z = z' := congrArg (fun q ↦ q.2.2) hxyz
  have hx : x ∈ e ∩ f := singletonVertex_mem _ _
  have hy : y ∈ e ∩ g := singletonVertex_mem _ _
  have hz : z ∈ f ∩ g := singletonVertex_mem _ _
  have hx' : x' ∈ e' ∩ f' := singletonVertex_mem _ _
  have hy' : y' ∈ e' ∩ g' := singletonVertex_mem _ _
  have hz' : z' ∈ f' ∩ g' := singletonVertex_mem _ _
  have hxy : x ≠ y := by
    intro hxy
    have hcommon : x ∈ e ∩ f ∩ g := by
      exact Finset.mem_inter.mpr ⟨hx, hxy ▸ (Finset.mem_inter.mp hy).2⟩
    have : 0 < (e ∩ f ∩ g).card := Finset.card_pos.mpr ⟨x, hcommon⟩
    have hzero : (e ∩ f ∩ g).card = 0 := h.2.2.2.2.2.2.2.2.2
    omega
  have hxz : x ≠ z := by
    intro hxz
    have hcommon : x ∈ e ∩ f ∩ g := by
      exact Finset.mem_inter.mpr ⟨hx, hxz ▸ (Finset.mem_inter.mp hz).2⟩
    have : 0 < (e ∩ f ∩ g).card := Finset.card_pos.mpr ⟨x, hcommon⟩
    have hzero : (e ∩ f ∩ g).card = 0 := h.2.2.2.2.2.2.2.2.2
    omega
  have hyz : y ≠ z := by
    intro hyz
    have hcommon : y ∈ e ∩ f ∩ g := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hy).1, hyz ▸ (Finset.mem_inter.mp hz).1⟩,
          (Finset.mem_inter.mp hy).2⟩
    have : 0 < (e ∩ f ∩ g).card := Finset.card_pos.mpr ⟨y, hcommon⟩
    have hzero : (e ∩ f ∩ g).card = 0 := h.2.2.2.2.2.2.2.2.2
    omega
  have hee' : e = e' := edge_eq_of_two_common hlin h.1 h'.1
    (Finset.mem_inter.mp hx).1 (hxx' ▸ (Finset.mem_inter.mp hx').1)
    (Finset.mem_inter.mp hy).1 (hyy' ▸ (Finset.mem_inter.mp hy').1) hxy
  have hff' : f = f' := edge_eq_of_two_common hlin h.2.1 h'.2.1
    (Finset.mem_inter.mp hx).2 (hxx' ▸ (Finset.mem_inter.mp hx').2)
    (Finset.mem_inter.mp hz).1 (hzz' ▸ (Finset.mem_inter.mp hz').1) hxz
  have hgg' : g = g' := edge_eq_of_two_common hlin h.2.2.1 h'.2.2.1
    (Finset.mem_inter.mp hy).2 (hyy' ▸ (Finset.mem_inter.mp hy').2)
    (Finset.mem_inter.mp hz).2 (hzz' ▸ (Finset.mem_inter.mp hz').2) hyz
  apply Subtype.ext
  simp [hee', hff', hgg']

theorem card_looseTriangles_le_cube {H : System V} (hlin : Linear H) :
    (looseTriangles H).card ≤ (Fintype.card V) ^ 3 := by
  let i : LooseTriangle H → V × V × V := looseTriangleCode H
  have hi : Function.Injective i := looseTriangleCode_injective hlin
  have hc := Fintype.card_le_of_injective i hi
  rw [← Fintype.card_coe]
  change Fintype.card (LooseTriangle H) ≤ (Fintype.card V) ^ 3
  simpa [i, Fintype.card_prod, pow_succ, mul_assoc] using hc

end TriangleCode

def triangleVertices (t : EdgeTriple V) : Finset V :=
  t.1.1 ∪ t.1.2 ∪ t.2

omit [Fintype V] in
theorem card_triangleVertices_of_mem {H : System V} (h3 : ThreeUniform H)
    {t : EdgeTriple V} (ht : t ∈ looseTriangles H) :
    (triangleVertices t).card = 6 := by
  rcases t with ⟨⟨e, f⟩, g⟩
  have h := mem_looseTriangles.mp ht
  have hefUnion : (e ∪ f).card = 5 := by
    have hcard := Finset.card_union_add_card_inter e f
    rw [h3 e h.1, h3 f h.2.1, h.2.2.2.2.2.2.1] at hcard
    omega
  have hinterEq : (e ∪ f) ∩ g = (e ∩ g) ∪ (f ∩ g) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hdisj : Disjoint (e ∩ g) (f ∩ g) := by
    rw [Finset.disjoint_left]
    intro x hxE hxF
    have hcommon : x ∈ e ∩ f ∩ g := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hxE).1, (Finset.mem_inter.mp hxF).1⟩,
          (Finset.mem_inter.mp hxE).2⟩
    have hzero : e ∩ f ∩ g = ∅ := Finset.card_eq_zero.mp h.2.2.2.2.2.2.2.2.2
    simp [hzero] at hcommon
  have hinterCard : ((e ∪ f) ∩ g).card = 2 := by
    rw [hinterEq, Finset.card_union_of_disjoint hdisj,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1]
  change (e ∪ f ∪ g).card = 6
  have hcard := Finset.card_union_add_card_inter (e ∪ f) g
  rw [hefUnion, h3 g h.2.2.1, hinterCard] at hcard
  omega

abbrev Coloring (V : Type*) (K : ℕ) := V → Fin K

def selectedSet {K : ℕ} [NeZero K] (omega : Coloring V K) : Finset V :=
  Finset.univ.filter fun v ↦ omega v = 0

omit [DecidableEq V] in
@[simp] lemma mem_selectedSet {K : ℕ} [NeZero K]
    {omega : Coloring V K} {v : V} :
    v ∈ selectedSet omega ↔ omega v = 0 := by
  simp [selectedSet]

def selectedLooseTriangles {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) : Finset (EdgeTriple V) :=
  (looseTriangles H).filter fun t ↦ triangleVertices t ⊆ selectedSet omega

@[simp] lemma mem_selectedLooseTriangles {K : ℕ} [NeZero K]
    {H : System V} {omega : Coloring V K} {t : EdgeTriple V} :
    t ∈ selectedLooseTriangles H omega ↔
      t ∈ looseTriangles H ∧ triangleVertices t ⊆ selectedSet omega := by
  simp [selectedLooseTriangles]

def subsetSelectedEvent {K : ℕ} [NeZero K]
    (S : Finset V) : Finset (Coloring V K) :=
  Finset.univ.filter fun omega ↦ S ⊆ selectedSet omega

@[simp] lemma mem_subsetSelectedEvent {K : ℕ} [NeZero K]
    {S : Finset V} {omega : Coloring V K} :
    omega ∈ subsetSelectedEvent (K := K) S ↔ S ⊆ selectedSet omega := by
  simp [subsetSelectedEvent]

def subsetSelectedEquiv {K : ℕ} [NeZero K] (S : Finset V) :
    ↥(subsetSelectedEvent (K := K) S) ≃ ({v : V // v ∉ S} → Fin K) where
  toFun omega v := omega.1 v.1
  invFun f := ⟨fun v ↦ if hv : v ∈ S then 0 else f ⟨v, hv⟩, by
    rw [mem_subsetSelectedEvent]
    intro v hv
    simp [hv]⟩
  left_inv omega := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ S
    · have hzero : omega.1 v = 0 :=
        mem_selectedSet.mp ((mem_subsetSelectedEvent.mp omega.property) hv)
      simp [hv, hzero]
    · simp [hv]
  right_inv f := by
    funext v
    simp [v.property]

theorem card_subsetSelectedEvent {K : ℕ} [NeZero K] (S : Finset V) :
    (subsetSelectedEvent (K := K) S).card =
      K ^ (Fintype.card V - S.card) := by
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr (subsetSelectedEquiv (K := K) S)]
  simp only [Fintype.card_fun, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype_compl (fun v : V ↦ v ∈ S)]
  congr 1
  exact Fintype.card_of_subtype S (fun _ ↦ Iff.rfl)

theorem uniformProbability_subsetSelectedEvent {K : ℕ} [NeZero K]
    (S : Finset V) :
    LocalLemma.uniformProbability (subsetSelectedEvent (K := K) S) =
      1 / (K : ℝ) ^ S.card := by
  classical
  have hK : (0 : ℝ) < K := by exact_mod_cast (NeZero.pos K)
  have hS : S.card ≤ Fintype.card V := Finset.card_le_univ S
  have hN : Fintype.card V =
      (Fintype.card V - S.card) + S.card := by omega
  unfold LocalLemma.uniformProbability
  rw [card_subsetSelectedEvent]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hpow : (K : ℝ) ^ Fintype.card V =
      (K : ℝ) ^ (Fintype.card V - S.card) * (K : ℝ) ^ S.card := by
    conv_lhs => rw [hN, pow_add]
  rw [hpow]
  field_simp

theorem expect_indicator_subsetSelected {K : ℕ} [NeZero K]
    (S : Finset V) :
    𝔼 omega : Coloring V K,
        (if S ⊆ selectedSet omega then (1 : ℝ) else 0) =
      1 / (K : ℝ) ^ S.card := by
  rw [Fintype.expect_eq_sum_div_card]
  have hsum :
      (∑ omega : Coloring V K,
        (if S ⊆ selectedSet omega then (1 : ℝ) else 0)) =
        ((subsetSelectedEvent (K := K) S).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [subsetSelectedEvent]
  rw [hsum]
  exact uniformProbability_subsetSelectedEvent S

theorem expect_card_selectedSet {K : ℕ} [NeZero K] :
    𝔼 omega : Coloring V K, ((selectedSet omega).card : ℝ) =
      (Fintype.card V : ℝ) / K := by
  calc
    𝔼 omega : Coloring V K, ((selectedSet omega).card : ℝ) =
        𝔼 omega : Coloring V K,
          ∑ v : V, (if ({v} : Finset V) ⊆ selectedSet omega then (1 : ℝ) else 0) := by
      apply Finset.expect_congr rfl
      intro omega _
      simp only [Finset.singleton_subset_iff]
      simp [selectedSet]
    _ = ∑ v : V,
        𝔼 omega : Coloring V K,
          (if ({v} : Finset V) ⊆ selectedSet omega then (1 : ℝ) else 0) :=
      Finset.expect_sum_comm _ _ _
    _ = ∑ _v : V, (1 / (K : ℝ)) := by
      apply Finset.sum_congr rfl
      intro v _
      simpa using expect_indicator_subsetSelected (K := K) ({v} : Finset V)
    _ = (Fintype.card V : ℝ) / K := by
      simp [div_eq_mul_inv]

theorem expect_card_selectedLooseTriangles {K : ℕ} [NeZero K]
    {H : System V} (h3 : ThreeUniform H) :
    𝔼 omega : Coloring V K,
        ((selectedLooseTriangles H omega).card : ℝ) =
      ((looseTriangles H).card : ℝ) / (K : ℝ) ^ 6 := by
  calc
    𝔼 omega : Coloring V K,
        ((selectedLooseTriangles H omega).card : ℝ) =
      𝔼 omega : Coloring V K,
        ∑ t ∈ looseTriangles H,
          (if triangleVertices t ⊆ selectedSet omega then (1 : ℝ) else 0) := by
      apply Finset.expect_congr rfl
      intro omega _
      simp [selectedLooseTriangles]
    _ = ∑ t ∈ looseTriangles H,
        𝔼 omega : Coloring V K,
          (if triangleVertices t ⊆ selectedSet omega then (1 : ℝ) else 0) :=
      Finset.expect_sum_comm _ _ _
    _ = ∑ _t ∈ looseTriangles H, (1 / (K : ℝ) ^ 6) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [expect_indicator_subsetSelected,
        card_triangleVertices_of_mem h3 ht]
    _ = ((looseTriangles H).card : ℝ) / (K : ℝ) ^ 6 := by
      simp [div_eq_mul_inv]

section TriangleDeletion

variable [LinearOrder V]

def triangleRepresentative (H : System V) (t : LooseTriangle H) : V :=
  (looseTriangleCode H t).1

omit [Fintype V] in
lemma triangleRepresentative_mem (H : System V) (t : LooseTriangle H) :
    triangleRepresentative H t ∈ triangleVertices t.1 := by
  let h := mem_looseTriangles.mp t.property
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_inter.mp (singletonVertex_mem
      (t.1.1.1 ∩ t.1.1.2) h.2.2.2.2.2.2.1)).1)

def selectedAsLoose {K : ℕ} [NeZero K] (H : System V)
    (omega : Coloring V K) (t : ↥(selectedLooseTriangles H omega)) :
    LooseTriangle H :=
  ⟨t.1, (mem_selectedLooseTriangles.mp t.property).1⟩

def deletedVertices {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) : Finset V :=
  (selectedLooseTriangles H omega).attach.image fun t ↦
    triangleRepresentative H (selectedAsLoose H omega t)

def prunedSet {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) : Finset V :=
  selectedSet omega \ deletedVertices H omega

lemma card_deletedVertices_le {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) :
    (deletedVertices H omega).card ≤ (selectedLooseTriangles H omega).card := by
  unfold deletedVertices
  exact (Finset.card_image_le).trans_eq (Finset.card_attach)

lemma prunedSet_subset_selectedSet {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) :
    prunedSet H omega ⊆ selectedSet omega := by
  exact Finset.sdiff_subset

lemma card_selectedSet_le_card_prunedSet_add_triangles
    {K : ℕ} [NeZero K] (H : System V) (omega : Coloring V K) :
    (selectedSet omega).card ≤ (prunedSet H omega).card +
      (selectedLooseTriangles H omega).card := by
  have hsplit := Finset.card_sdiff_add_card_inter
    (selectedSet omega) (deletedVertices H omega)
  change (selectedSet omega).card ≤
    (selectedSet omega \ deletedVertices H omega).card +
      (selectedLooseTriangles H omega).card
  calc
    (selectedSet omega).card =
        (selectedSet omega \ deletedVertices H omega).card +
          (selectedSet omega ∩ deletedVertices H omega).card := hsplit.symm
    _ ≤ (selectedSet omega \ deletedVertices H omega).card +
          (deletedVertices H omega).card := by
      gcongr
      exact (Finset.inter_subset_right :
          selectedSet omega ∩ deletedVertices H omega ⊆ deletedVertices H omega)
    _ ≤ _ := Nat.add_le_add_left (card_deletedVertices_le H omega) _

theorem pruned_triangleFree {K : ℕ} [NeZero K]
    (H : System V) (omega : Coloring V K) :
    TriangleFree (H.filter fun e ↦ e ⊆ prunedSet H omega) := by
  rw [TriangleFree]
  intro htri
  obtain ⟨e, he, f, hf, g, hg, hef, heg, hfg,
    hefCard, hegCard, hfgCard, htriple⟩ := htri
  have he' := Finset.mem_filter.mp he
  have hf' := Finset.mem_filter.mp hf
  have hg' := Finset.mem_filter.mp hg
  let t : EdgeTriple V := ((e, f), g)
  have ht : t ∈ looseTriangles H := mem_looseTriangles.mpr
    ⟨he'.1, hf'.1, hg'.1, hef, heg, hfg,
      hefCard, hegCard, hfgCard, htriple⟩
  have htPruned : triangleVertices t ⊆ prunedSet H omega := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hxE | hxF
      · exact he'.2 hxE
      · exact hf'.2 hxF
    · exact hg'.2 hx
  have htSelected : t ∈ selectedLooseTriangles H omega :=
    mem_selectedLooseTriangles.mpr
      ⟨ht, htPruned.trans (prunedSet_subset_selectedSet H omega)⟩
  let st : ↥(selectedLooseTriangles H omega) := ⟨t, htSelected⟩
  let v := triangleRepresentative H (selectedAsLoose H omega st)
  have hvDelete : v ∈ deletedVertices H omega := by
    apply Finset.mem_image.mpr
    exact ⟨st, Finset.mem_attach _ _, rfl⟩
  have hvTriangle : v ∈ triangleVertices t :=
    triangleRepresentative_mem H (selectedAsLoose H omega st)
  have hvPruned : v ∈ prunedSet H omega := htPruned hvTriangle
  exact (Finset.mem_sdiff.mp hvPruned).2 hvDelete

end TriangleDeletion

def selectedWeight {K : ℕ} [NeZero K]
    (w : V → ℕ) (omega : Coloring V K) : ℕ :=
  ∑ v : V, if omega v = 0 then w v else 0

lemma exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (1 : ℝ)) (sub_nonneg.mpr hx1) hx0 (by ring)
  have hrewrite : (1 - x) • (0 : ℝ) + x • (1 : ℝ) = x := by
    simp [smul_eq_mul]
  rw [hrewrite, Real.exp_zero] at hconv
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  simp only [smul_eq_mul] at hconv
  nlinarith

lemma sum_exp_selectedWeight_eq_product {K : ℕ} [NeZero K]
    (B : ℕ) (w : V → ℕ) :
    ∑ omega : Coloring V K,
        Real.exp ((selectedWeight w omega : ℝ) / B) =
      (∏ v : V, (((K - 1 : ℕ) : ℝ) + Real.exp ((w v : ℝ) / B))) := by
  classical
  calc
    ∑ omega : Coloring V K,
        Real.exp ((selectedWeight w omega : ℝ) / B) =
        ∑ omega : Coloring V K,
          ∏ v : V, Real.exp (((if omega v = 0 then w v else 0 : ℕ) : ℝ) / B) := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [← Real.exp_sum]
      congr 1
      unfold selectedWeight
      push_cast
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = (∏ v : V, (∑ c : Fin K,
        Real.exp (((if c = 0 then w v else 0 : ℕ) : ℝ) / B))) := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.sum_prod_piFinset (Finset.univ : Finset (Fin K))
          (fun v c ↦ Real.exp (((if c = 0 then w v else 0 : ℕ) : ℝ) / B)))
    _ = (∏ v : V, (((K - 1 : ℕ) : ℝ) + Real.exp ((w v : ℝ) / B))) := by
      apply Finset.prod_congr rfl
      intro v _
      have hzero : (0 : Fin K) ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ _
      change (∑ c ∈ (Finset.univ : Finset (Fin K)),
        Real.exp (((if c = 0 then w v else 0 : ℕ) : ℝ) / B)) = _
      rw [← Finset.sum_erase_add _ _ hzero]
      simp only [if_pos]
      congr 1
      calc
        ∑ c ∈ (Finset.univ : Finset (Fin K)).erase 0,
            Real.exp (((if c = 0 then w v else 0 : ℕ) : ℝ) / B) =
            ∑ _c ∈ (Finset.univ : Finset (Fin K)).erase 0, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro c hc
          have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
          simp [hc0]
        _ = (((Finset.univ : Finset (Fin K)).erase 0).card : ℝ) := by simp
        _ = ((K - 1 : ℕ) : ℝ) := by
          congr 1
          simp [Finset.card_erase_of_mem hzero, Fintype.card_fin]

lemma sum_exp_selectedWeight_bound {K B S : ℕ} [NeZero K]
    (hB : 0 < B) (w : V → ℕ) (hwB : ∀ v, w v ≤ B)
    (hwSum : ∑ v : V, w v ≤ S) :
    ∑ omega : Coloring V K,
        Real.exp ((selectedWeight w omega : ℝ) / B) ≤
      (K : ℝ) ^ Fintype.card V *
        Real.exp (2 * (S : ℝ) / ((K : ℝ) * B)) := by
  classical
  rw [sum_exp_selectedWeight_eq_product]
  have hK : (0 : ℝ) < K := by exact_mod_cast (NeZero.pos K)
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hfactor : ∀ v : V,
      ((K - 1 : ℕ) : ℝ) + Real.exp ((w v : ℝ) / B) ≤
        (K : ℝ) * Real.exp (2 * (w v : ℝ) / ((K : ℝ) * B)) := by
    intro v
    have hw0 : (0 : ℝ) ≤ (w v : ℝ) / B := by positivity
    have hw1 : (w v : ℝ) / B ≤ 1 := by
      rw [div_le_one hBR]
      exact_mod_cast hwB v
    have hsec := exp_le_one_add_two_mul hw0 hw1
    have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub NeZero.one_le]
      norm_num
    have harg0 : 0 ≤ 2 * (w v : ℝ) / ((K : ℝ) * B) := by positivity
    have hexp := Real.add_one_le_exp (2 * (w v : ℝ) / ((K : ℝ) * B))
    rw [hcast]
    calc
      (K : ℝ) - 1 + Real.exp ((w v : ℝ) / B) ≤
          (K : ℝ) + 2 * ((w v : ℝ) / B) := by linarith
      _ = (K : ℝ) *
          (1 + 2 * (w v : ℝ) / ((K : ℝ) * B)) := by field_simp
      _ ≤ (K : ℝ) * Real.exp
          (2 * (w v : ℝ) / ((K : ℝ) * B)) :=
        mul_le_mul_of_nonneg_left (by simpa [add_comm] using hexp) hK.le
  calc
    (∏ v : V, (((K - 1 : ℕ) : ℝ) + Real.exp ((w v : ℝ) / B))) ≤
        (∏ v : V, ((K : ℝ) *
          Real.exp (2 * (w v : ℝ) / ((K : ℝ) * B)))) := by
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity) fun v _ ↦ hfactor v
    _ = (K : ℝ) ^ Fintype.card V *
        Real.exp (∑ v : V, 2 * (w v : ℝ) / ((K : ℝ) * B)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
      simp only [Finset.card_univ]
    _ ≤ (K : ℝ) ^ Fintype.card V *
        Real.exp (2 * (S : ℝ) / ((K : ℝ) * B)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        have hwCast : (∑ v : V, (w v : ℝ)) ≤ S := by exact_mod_cast hwSum
        calc
          ∑ v : V, 2 * (w v : ℝ) / ((K : ℝ) * B) =
              2 * (∑ v : V, (w v : ℝ)) / ((K : ℝ) * B) := by
            simp_rw [div_eq_mul_inv]
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ ≤ _ := by gcongr
      · positivity

def weightBadEvent {K : ℕ} [NeZero K] (w : V → ℕ) (T : ℕ) :
    Finset (Coloring V K) :=
  Finset.univ.filter fun omega ↦ T ≤ selectedWeight w omega

lemma uniformProbability_weightBadEvent {K B S T : ℕ} [NeZero K]
    (hB : 0 < B) (w : V → ℕ) (hwB : ∀ v, w v ≤ B)
    (hwSum : ∑ v : V, w v ≤ S) :
    LocalLemma.uniformProbability (Omega := Coloring V K)
      (weightBadEvent (K := K) w T) ≤
      Real.exp (2 * (S : ℝ) / ((K : ℝ) * B) - (T : ℝ) / B) := by
  classical
  let Omega := Coloring V K
  have hOmega : (0 : ℝ) < Fintype.card Omega := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Omega)
  have hTexp : 0 < Real.exp ((T : ℝ) / B) := Real.exp_pos _
  have hbad :
      ((weightBadEvent (K := K) w T).card : ℝ) * Real.exp ((T : ℝ) / B) ≤
        ∑ omega ∈ weightBadEvent (K := K) w T,
          Real.exp ((selectedWeight w omega : ℝ) / B) := by
    calc
      ((weightBadEvent (K := K) w T).card : ℝ) * Real.exp ((T : ℝ) / B) =
          ∑ _omega ∈ weightBadEvent (K := K) w T,
            Real.exp ((T : ℝ) / B) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro omega homega
        apply Real.exp_le_exp.mpr
        have hT : T ≤ selectedWeight w omega :=
          (Finset.mem_filter.mp homega).2
        exact div_le_div_of_nonneg_right (by exact_mod_cast hT) (by positivity)
  have hmgf :
      ∑ omega ∈ weightBadEvent (K := K) w T,
          Real.exp ((selectedWeight w omega : ℝ) / B) ≤
        (K : ℝ) ^ Fintype.card V *
          Real.exp (2 * (S : ℝ) / ((K : ℝ) * B)) := by
    calc
      _ ≤ ∑ omega : Coloring V K,
          Real.exp ((selectedWeight w omega : ℝ) / B) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ ↦ (Real.exp_pos _).le)
      _ ≤ _ := sum_exp_selectedWeight_bound hB w hwB hwSum
  have hcardOmega : (Fintype.card Omega : ℝ) =
      (K : ℝ) ^ Fintype.card V := by
    simp [Omega]
  have hcard : ((weightBadEvent (K := K) w T).card : ℝ) ≤
      (Fintype.card Omega : ℝ) *
        Real.exp (2 * (S : ℝ) / ((K : ℝ) * B) - (T : ℝ) / B) := by
    rw [Real.exp_sub]
    rw [show (Fintype.card Omega : ℝ) *
      (Real.exp (2 * (S : ℝ) / ((K : ℝ) * B)) /
        Real.exp ((T : ℝ) / B)) =
      ((Fintype.card Omega : ℝ) *
        Real.exp (2 * (S : ℝ) / ((K : ℝ) * B))) /
          Real.exp ((T : ℝ) / B) by ring]
    rw [le_div_iff₀ hTexp]
    rw [hcardOmega]
    exact hbad.trans hmgf
  unfold LocalLemma.uniformProbability
  rw [div_le_iff₀ hOmega]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcard

/-! ## A simultaneous extension bound -/

def extensionWeight (H : System V) (B : ℕ) (Z : Finset V) (v : V) : ℕ :=
  if v ∈ Z then 0 else truncatedExtension H B v Z

lemma extensionWeight_le (H : System V) (B : ℕ) (Z : Finset V) (v : V) :
    extensionWeight H B Z v ≤ B := by
  unfold extensionWeight truncatedExtension
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_right _ _

lemma sum_extensionWeight_eq (H : System V) (B : ℕ) (Z : Finset V) :
    ∑ v : V, extensionWeight H B Z v = totalTruncatedExtension H B Z := by
  classical
  unfold extensionWeight totalTruncatedExtension
  calc
    (∑ v : V, if v ∈ Z then 0 else truncatedExtension H B v Z) =
        ∑ v ∈ Finset.univ \ Z,
          (if v ∈ Z then 0 else truncatedExtension H B v Z) := by
      symm
      apply Finset.sum_subset Finset.sdiff_subset
      intro v _ hv
      have hvZ : v ∈ Z := by simpa using hv
      simp [hvZ]
    _ = ∑ v ∈ Finset.univ \ Z, truncatedExtension H B v Z := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [if_neg (Finset.mem_sdiff.mp hv).2]

lemma sum_extensionWeight_le_choose {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H) {A B : ℕ}
    {Z : Finset V} (hZA : Z.card ≤ A) :
    ∑ v : V, extensionWeight H B Z v ≤ A.choose 2 := by
  rw [sum_extensionWeight_eq]
  exact (totalTruncatedExtension_le_choose h3 hlin B Z).trans
    (Nat.choose_le_choose 2 hZA)

lemma selectedWeight_extensionWeight_eq {K : ℕ} [NeZero K]
    (H : System V) (B : ℕ) (Z : Finset V) (omega : Coloring V K) :
    selectedWeight (extensionWeight H B Z) omega =
      ∑ v ∈ selectedSet omega \ Z, truncatedExtension H B v Z := by
  classical
  unfold selectedWeight extensionWeight selectedSet
  calc
    (∑ v : V, if omega v = 0 then
        (if v ∈ Z then 0 else truncatedExtension H B v Z) else 0) =
      ∑ v ∈ Finset.univ.filter (fun v ↦ omega v = 0) \ Z,
        (if omega v = 0 then
          (if v ∈ Z then 0 else truncatedExtension H B v Z) else 0) := by
      symm
      apply Finset.sum_subset
        (Finset.sdiff_subset.trans (Finset.filter_subset _ _))
      intro v _ hv
      by_cases hvZ : v ∈ Z
      · simp [hvZ]
      · have hvSel : v ∉ Finset.univ.filter (fun v ↦ omega v = 0) := by
          intro hv'
          exact hv (Finset.mem_sdiff.mpr ⟨hv', hvZ⟩)
        have hvOmega : omega v ≠ 0 := by simpa using hvSel
        simp [hvOmega]
    _ = ∑ v ∈ Finset.univ.filter (fun v ↦ omega v = 0) \ Z,
        truncatedExtension H B v Z := by
      apply Finset.sum_congr rfl
      intro v hv
      have h := Finset.mem_sdiff.mp hv
      have hvOmega : omega v = 0 := (Finset.mem_filter.mp h.1).2
      simp [hvOmega, h.2]

def someExtensionBadEvent {K : ℕ} [NeZero K]
    (H : System V) (B T : ℕ) : Finset (Coloring V K) :=
  (independentSets H).biUnion fun Z ↦
    weightBadEvent (K := K) (extensionWeight H B Z) T

lemma card_independentSets_le_power {H : System V} {A : ℕ}
    (hA : A ≤ Fintype.card V)
    (hcard : ∀ Z ∈ independentSets H, Z.card ≤ A) :
    (independentSets H).card ≤ (Fintype.card V + 1) ^ (A + 1) := by
  classical
  let layers : Finset (Finset V) :=
    (Finset.range (A + 1)).biUnion fun i ↦ Finset.univ.powersetCard i
  have hsub : independentSets H ⊆ layers := by
    intro Z hZ
    apply Finset.mem_biUnion.mpr
    refine ⟨Z.card, Finset.mem_range.mpr (by
      have := hcard Z hZ
      omega), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ Z, rfl⟩
  calc
    (independentSets H).card ≤ layers.card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (A + 1),
        ((Finset.univ : Finset V).powersetCard i).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (A + 1), (Fintype.card V).choose i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ ∑ _i ∈ Finset.range (A + 1),
        (Fintype.card V + 1) ^ A := by
      apply Finset.sum_le_sum
      intro i hi
      have hiA : i ≤ A := by
        have hi' := Finset.mem_range.mp hi
        omega
      calc
        (Fintype.card V).choose i ≤ (Fintype.card V) ^ i :=
          Nat.choose_le_pow _ _
        _ ≤ (Fintype.card V + 1) ^ i :=
          Nat.pow_le_pow_left (by omega) i
        _ ≤ (Fintype.card V + 1) ^ A :=
          Nat.pow_le_pow_right (by omega) hiA
    _ = (A + 1) * (Fintype.card V + 1) ^ A := by simp
    _ ≤ (Fintype.card V + 1) ^ (A + 1) := by
      rw [pow_succ]
      calc
        (A + 1) * (Fintype.card V + 1) ^ A =
            (Fintype.card V + 1) ^ A * (A + 1) := Nat.mul_comm _ _
        _ ≤ (Fintype.card V + 1) ^ A * (Fintype.card V + 1) :=
          Nat.mul_le_mul_left _ (Nat.succ_le_succ hA)

theorem uniformProbability_someExtensionBadEvent {K A B T : ℕ} [NeZero K]
    {H : System V} (h3 : ThreeUniform H) (hlin : Linear H)
    (hB : 0 < B) (hA : A ≤ Fintype.card V)
    (hcard : ∀ Z ∈ independentSets H, Z.card ≤ A) :
    LocalLemma.uniformProbability
        (someExtensionBadEvent (K := K) H B T) ≤
      ((Fintype.card V + 1 : ℕ) : ℝ) ^ (A + 1) *
        Real.exp (2 * ((A.choose 2 : ℕ) : ℝ) /
          ((K : ℝ) * B) - (T : ℝ) / B) := by
  classical
  let q : ℝ := Real.exp (2 * ((A.choose 2 : ℕ) : ℝ) /
    ((K : ℝ) * B) - (T : ℝ) / B)
  have hone :
      LocalLemma.uniformProbability
          (someExtensionBadEvent (K := K) H B T) ≤
        ∑ Z ∈ independentSets H,
          LocalLemma.uniformProbability
            (weightBadEvent (K := K) (extensionWeight H B Z) T) := by
    unfold someExtensionBadEvent LocalLemma.uniformProbability
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (Finset.card_biUnion_le :
        ((independentSets H).biUnion fun Z ↦
          weightBadEvent (K := K) (extensionWeight H B Z) T).card ≤
        ∑ Z ∈ independentSets H,
          (weightBadEvent (K := K) (extensionWeight H B Z) T).card)
    · positivity
  have heach : ∀ Z ∈ independentSets H,
      LocalLemma.uniformProbability
          (weightBadEvent (K := K) (extensionWeight H B Z) T) ≤ q := by
    intro Z hZ
    apply uniformProbability_weightBadEvent hB
    · exact extensionWeight_le H B Z
    · exact sum_extensionWeight_le_choose h3 hlin (hcard Z hZ)
  calc
    LocalLemma.uniformProbability
        (someExtensionBadEvent (K := K) H B T) ≤
      ∑ Z ∈ independentSets H,
        LocalLemma.uniformProbability
          (weightBadEvent (K := K) (extensionWeight H B Z) T) := hone
    _ ≤ ∑ _Z ∈ independentSets H, q := Finset.sum_le_sum heach
    _ = ((independentSets H).card : ℝ) * q := by simp
    _ ≤ (((Fintype.card V + 1) ^ (A + 1) : ℕ) : ℝ) * q := by
      gcongr
      exact_mod_cast card_independentSets_le_power hA hcard
    _ = ((Fintype.card V + 1 : ℕ) : ℝ) ^ (A + 1) *
        Real.exp (2 * ((A.choose 2 : ℕ) : ℝ) /
          ((K : ℝ) * B) - (T : ℝ) / B) := by
      simp [q]

lemma selected_extension_bound_of_not_bad {K B T : ℕ} [NeZero K]
    {H : System V} {omega : Coloring V K}
    (hgood : omega ∉ someExtensionBadEvent (K := K) H B T)
    {Z : Finset V} (hZ : Independent H Z) :
    ∑ v ∈ selectedSet omega \ Z, truncatedExtension H B v Z < T := by
  rw [← selectedWeight_extensionWeight_eq]
  by_contra hnot
  apply hgood
  apply Finset.mem_biUnion.mpr
  refine ⟨Z, mem_independentSets.mpr hZ, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_gt hnot⟩

/-! ## Averaging and pruning -/

lemma expect_indicator_event {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (E : Finset Omega) :
    𝔼 omega : Omega, (if omega ∈ E then (1 : ℝ) else 0) =
      ((E.card : ℝ) / Fintype.card Omega) := by
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  rw [← Finset.sum_filter]
  simp

def samplingScore {K : ℕ} [NeZero K]
    (H : System V) (B T : ℕ) (omega : Coloring V K) : ℝ :=
  ((selectedSet omega).card : ℝ) -
    ((selectedLooseTriangles H omega).card : ℝ) -
    (if omega ∈ someExtensionBadEvent (K := K) H B T then
      (Fintype.card V : ℝ) else 0)

lemma expect_samplingScore {K B T : ℕ} [NeZero K]
    {H : System V} (h3 : ThreeUniform H) :
    𝔼 omega : Coloring V K, samplingScore H B T omega =
      (Fintype.card V : ℝ) / K -
        ((looseTriangles H).card : ℝ) / (K : ℝ) ^ 6 -
        (Fintype.card V : ℝ) *
          LocalLemma.uniformProbability
            (someExtensionBadEvent (K := K) H B T) := by
  unfold samplingScore
  rw [Finset.expect_sub_distrib, Finset.expect_sub_distrib,
    expect_card_selectedSet, expect_card_selectedLooseTriangles h3]
  congr 1
  calc
    𝔼 omega : Coloring V K,
        (if omega ∈ someExtensionBadEvent (K := K) H B T then
          (Fintype.card V : ℝ) else 0) =
      (Fintype.card V : ℝ) *
        (𝔼 omega : Coloring V K,
          (if omega ∈ someExtensionBadEvent (K := K) H B T then
            (1 : ℝ) else 0)) := by
        rw [Finset.mul_expect]
        apply Finset.expect_congr rfl
        intro omega _
        split_ifs <;> simp
    _ = (Fintype.card V : ℝ) *
        LocalLemma.uniformProbability
          (someExtensionBadEvent (K := K) H B T) := by
      rw [expect_indicator_event]
      rfl

/-- A finite sampling lemma.  Its hypotheses are only explicit numerical
inequalities; all hypergraph structure is discharged in the conclusion. -/
theorem exists_large_pruned_sample {K A B T : ℕ} [NeZero K]
    [LinearOrder V] {H : System V} (h3 : ThreeUniform H) (hlin : Linear H)
    (hB : 0 < B) (hA : A ≤ Fintype.card V)
    (hcard : ∀ Z ∈ independentSets H, Z.card ≤ A)
    {L : ℝ} (hL : 0 < L)
    (hscore : L ≤
      (Fintype.card V : ℝ) / K -
        (((Fintype.card V) ^ 3 : ℕ) : ℝ) / (K : ℝ) ^ 6 -
        (Fintype.card V : ℝ) *
          (((Fintype.card V + 1 : ℕ) : ℝ) ^ (A + 1) *
            Real.exp (2 * ((A.choose 2 : ℕ) : ℝ) /
              ((K : ℝ) * B) - (T : ℝ) / B))) :
    ∃ omega : Coloring V K,
      omega ∉ someExtensionBadEvent (K := K) H B T ∧
      L ≤ ((prunedSet H omega).card : ℝ) ∧
      TriangleFree (H.filter fun e ↦ e ⊆ prunedSet H omega) ∧
      ∀ Z : Finset V, Independent H Z →
        ∑ v ∈ prunedSet H omega \ Z,
          truncatedExtension H B v Z < T := by
  classical
  have htri := card_looseTriangles_le_cube hlin
  have hbad := uniformProbability_someExtensionBadEvent
    h3 hlin hB hA hcard (K := K) (T := T)
  have havg : L ≤ 𝔼 omega : Coloring V K, samplingScore H B T omega := by
    rw [expect_samplingScore h3]
    apply hscore.trans
    have htriR : ((looseTriangles H).card : ℝ) ≤
        (((Fintype.card V) ^ 3 : ℕ) : ℝ) := by exact_mod_cast htri
    have hKpow : 0 ≤ (K : ℝ) ^ 6 := by positivity
    have hN : 0 ≤ (Fintype.card V : ℝ) := by positivity
    gcongr
  obtain ⟨omega, -, homega⟩ :=
    Finset.exists_le_of_le_expect (Finset.univ_nonempty :
      (Finset.univ : Finset (Coloring V K)).Nonempty) havg
  have hgood : omega ∉ someExtensionBadEvent (K := K) H B T := by
    intro hbadOmega
    have hsel : (selectedSet omega).card ≤ Fintype.card V :=
      Finset.card_le_univ _
    have htri0 : 0 ≤ ((selectedLooseTriangles H omega).card : ℝ) := by positivity
    have hselR : ((selectedSet omega).card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hsel
    unfold samplingScore at homega
    rw [if_pos hbadOmega] at homega
    linarith
  have hsize : L ≤ ((prunedSet H omega).card : ℝ) := by
    have hsplit := card_selectedSet_le_card_prunedSet_add_triangles H omega
    have hsplitR : ((selectedSet omega).card : ℝ) ≤
        (prunedSet H omega).card + (selectedLooseTriangles H omega).card := by
      exact_mod_cast hsplit
    unfold samplingScore at homega
    rw [if_neg hgood] at homega
    linarith
  refine ⟨omega, hgood, hsize, pruned_triangleFree H omega, ?_⟩
  intro Z hZ
  have hselected := selected_extension_bound_of_not_bad hgood hZ
  have hsub : prunedSet H omega \ Z ⊆ selectedSet omega \ Z := by
    intro v hv
    have hv' := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr
      ⟨prunedSet_subset_selectedSet H omega hv'.1, hv'.2⟩
  calc
    ∑ v ∈ prunedSet H omega \ Z, truncatedExtension H B v Z ≤
        ∑ v ∈ selectedSet omega \ Z, truncatedExtension H B v Z :=
      Finset.sum_le_sum_of_subset hsub
    _ < T := hselected

end Lower
end OMA1024


-- ===== from plby module ErdosProblems.Erdos1024.LowerRestriction =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

This file transfers the finite sampling conclusion to the subtype of the
pruned vertex set.  Consequently the vertex count in the weighted lemma is
exactly the number of vertices which survived deletion.
-/

open scoped BigOperators

namespace OMA1024
namespace Lower

variable {V : Type*} [DecidableEq V]

def subtypeEmbedding (Y : Finset V) : Y ↪ V := Function.Embedding.subtype _

def valMap (Y : Finset V) (I : Finset Y) : Finset V :=
  I.map (subtypeEmbedding Y)

omit [DecidableEq V] in
@[simp] lemma card_valMap (Y : Finset V) (I : Finset Y) :
    (valMap Y I).card = I.card := by
  simp [valMap]

def restrictSystem (H : System V) (Y : Finset V) : System Y :=
  Finset.univ.powerset.filter fun e ↦ valMap Y e ∈ H

@[simp] lemma mem_restrictSystem {H : System V} {Y : Finset V}
    {e : Finset Y} : e ∈ restrictSystem H Y ↔ valMap Y e ∈ H := by
  rw [restrictSystem, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨Finset.subset_univ _, h⟩

omit [DecidableEq V] in
lemma valMap_injective (Y : Finset V) : Function.Injective (valMap Y) := by
  exact Finset.map_injective _

lemma restrict_threeUniform {H : System V} (h3 : ThreeUniform H) (Y : Finset V) :
    ThreeUniform (restrictSystem H Y) := by
  intro e he
  rw [← card_valMap Y e]
  exact h3 _ (mem_restrictSystem.mp he)

lemma restrict_linear {H : System V} (hlin : Linear H) (Y : Finset V) :
    Linear (restrictSystem H Y) := by
  intro e he f hf hef
  have hmapne : valMap Y e ≠ valMap Y f := fun h ↦ hef (valMap_injective Y h)
  have h := hlin (mem_restrictSystem.mp he) (mem_restrictSystem.mp hf) hmapne
  rw [valMap, valMap, ← Finset.map_inter, Finset.card_map] at h
  exact h

omit [DecidableEq V] in
lemma valMap_subset_Y (Y : Finset V) (I : Finset Y) : valMap Y I ⊆ Y := by
  intro x hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hx
  exact v.property

lemma independent_restrict_iff {H : System V} {Y : Finset V}
    {I : Finset Y} :
    Independent (restrictSystem H Y) I ↔ Independent H (valMap Y I) := by
  classical
  constructor
  · intro hI e heH heSub
    have heY : ∀ x ∈ e, x ∈ Y := fun x hx ↦
      valMap_subset_Y Y I (heSub hx)
    let e' : Finset Y := e.subtype (· ∈ Y)
    have hmap : valMap Y e' = e := by
      exact Finset.subtype_map_of_mem heY
    have heR : e' ∈ restrictSystem H Y := by
      rw [mem_restrictSystem, hmap]
      exact heH
    apply hI heR
    apply Finset.map_subset_map.mp
    change valMap Y e' ⊆ valMap Y I
    rw [hmap]
    exact heSub
  · intro hI e heR heSub
    apply hI (mem_restrictSystem.mp heR)
    exact (Finset.map_subset_map.mpr heSub)

lemma restrict_triangleFree {H : System V} {Y : Finset V}
    (htri : TriangleFree (H.filter fun e ↦ e ⊆ Y)) :
    TriangleFree (restrictSystem H Y) := by
  rw [TriangleFree] at htri ⊢
  intro ht
  obtain ⟨e, he, f, hf, g, hg, hef, heg, hfg,
    hefCard, hegCard, hfgCard, hcommon⟩ := ht
  let E := valMap Y e
  let F := valMap Y f
  let G := valMap Y g
  have hEF : E ≠ F := fun h ↦ hef (valMap_injective Y h)
  have hEG : E ≠ G := fun h ↦ heg (valMap_injective Y h)
  have hFG : F ≠ G := fun h ↦ hfg (valMap_injective Y h)
  have hEFcard : (E ∩ F).card = 1 := by
    dsimp [E, F]
    rw [valMap, valMap, ← Finset.map_inter, Finset.card_map]
    exact hefCard
  have hEGcard : (E ∩ G).card = 1 := by
    dsimp [E, G]
    rw [valMap, valMap, ← Finset.map_inter, Finset.card_map]
    exact hegCard
  have hFGcard : (F ∩ G).card = 1 := by
    dsimp [F, G]
    rw [valMap, valMap, ← Finset.map_inter, Finset.card_map]
    exact hfgCard
  have hcommonCard : (E ∩ F ∩ G).card = 0 := by
    dsimp [E, F, G]
    rw [valMap, valMap, valMap,
      ← Finset.map_inter, ← Finset.map_inter, Finset.card_map]
    exact hcommon
  apply htri
  exact ⟨E, Finset.mem_filter.mpr
      ⟨mem_restrictSystem.mp he, valMap_subset_Y Y e⟩,
    F, Finset.mem_filter.mpr
      ⟨mem_restrictSystem.mp hf, valMap_subset_Y Y f⟩,
    G, Finset.mem_filter.mpr
      ⟨mem_restrictSystem.mp hg, valMap_subset_Y Y g⟩,
    hEF, hEG, hFG, hEFcard, hEGcard, hFGcard, hcommonCard⟩

variable [Fintype V]

lemma extensionCount_restrict_le {H : System V} {Y : Finset V}
    (_ : ThreeUniform H) {B : ℕ} (v : Y) (Z : Finset Y) :
    truncatedExtension (restrictSystem H Y) B v Z ≤
      truncatedExtension H B v.1 (valMap Y Z) := by
  classical
  unfold truncatedExtension
  apply min_le_min_right
  rw [extensionCount_eq_card_pairsAt, extensionCount_eq_card_pairsAt]
  let emb : Finset Y ↪ Finset V :=
    (Finset.mapEmbedding (subtypeEmbedding Y)).toEmbedding
  have hsub : (pairsAt (restrictSystem H Y) v Z).map emb ⊆
      pairsAt H v.1 (valMap Y Z) := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    have haFilter := Finset.mem_filter.mp ha'
    obtain ⟨e, heR, hve, -, hea⟩ := mem_linkPairs.mp haFilter.1
    let E := valMap Y e
    have hE : E ∈ H := mem_restrictSystem.mp heR
    have hvE : v.1 ∈ E := by
      exact Finset.mem_map.mpr ⟨v, hve, rfl⟩
    have herase : E.erase v.1 = valMap Y (e.erase v) := by
      simp [E, valMap, subtypeEmbedding]
    have hEN : E.erase v.1 ⊆ neighborhood H v.1 := by
      intro x hx
      have hxE := Finset.mem_of_mem_erase hx
      have hxv := (Finset.mem_erase.mp hx).1
      exact vertex_of_edge_neighborhood hE hvE hxE hxv
    have hlink : valMap Y a' ∈ linkPairs H v.1 (neighborhood H v.1) := by
      apply mem_linkPairs.mpr
      refine ⟨E, hE, hvE, hEN, ?_⟩
      rw [herase, hea]
    change valMap Y a' ∈ pairsAt H v.1 (valMap Y Z)
    apply Finset.mem_filter.mpr
    refine ⟨hlink, ?_⟩
    exact Finset.map_subset_map.mpr haFilter.2
  calc
    (pairsAt (restrictSystem H Y) v Z).card =
        ((pairsAt (restrictSystem H Y) v Z).map emb).card := by simp
    _ ≤ (pairsAt H v.1 (valMap Y Z)).card := Finset.card_le_card hsub

omit [Fintype V] in
lemma map_univ_sdiff (Y : Finset V) (Z : Finset Y) :
    (Finset.univ \ Z).map (subtypeEmbedding Y) = Y \ valMap Y Z := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
    have hv' := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr ⟨v.property, fun h ↦ by
      obtain ⟨w, hwZ, hw⟩ := Finset.mem_map.mp h
      have hwv : w = v := Subtype.ext hw
      exact hv'.2 (hwv ▸ hwZ)⟩
  · intro hx
    have hx' := Finset.mem_sdiff.mp hx
    let v : Y := ⟨x, hx'.1⟩
    apply Finset.mem_map.mpr
    refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    intro hvZ
    exact hx'.2 (Finset.mem_map.mpr ⟨v, hvZ, rfl⟩)

theorem totalTruncatedExtension_restrict_le {H : System V} {Y : Finset V}
    (h3 : ThreeUniform H) (B : ℕ) (Z : Finset Y) :
    totalTruncatedExtension (restrictSystem H Y) B Z ≤
      ∑ v ∈ Y \ valMap Y Z, truncatedExtension H B v (valMap Y Z) := by
  classical
  unfold totalTruncatedExtension
  calc
    ∑ v ∈ Finset.univ \ Z,
        truncatedExtension (restrictSystem H Y) B v Z ≤
      ∑ v ∈ Finset.univ \ Z,
        truncatedExtension H B v.1 (valMap Y Z) := by
      exact Finset.sum_le_sum fun v _ ↦ extensionCount_restrict_le h3 v Z
    _ = ∑ v ∈ (Finset.univ \ Z).map (subtypeEmbedding Y),
        truncatedExtension H B v (valMap Y Z) := by
      rw [Finset.sum_map]
      simp [subtypeEmbedding]
    _ = _ := by rw [map_univ_sdiff]

end Lower
end OMA1024


-- ===== from plby module ErdosProblems.Erdos1024.LowerFinite =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

The theorem in this file has no asymptotic symbols.  Given explicit natural
parameters satisfying two displayed real inequalities, it produces an
independent set larger than the proposed threshold.
-/

namespace OMA1024
namespace Lower

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem exists_independent_gt_of_parameters {H : System V}
    (h3 : ThreeUniform H) (hlin : Linear H)
    {K A B T : ℕ} [NeZero K] (hB : 0 < B)
    (hA : A ≤ Fintype.card V) {L : ℝ} (hL : 0 < L)
    (hscore : L ≤
      (Fintype.card V : ℝ) / K -
        (((Fintype.card V) ^ 3 : ℕ) : ℝ) / (K : ℝ) ^ 6 -
        (Fintype.card V : ℝ) *
          (((Fintype.card V + 1 : ℕ) : ℝ) ^ (A + 1) *
            Real.exp (2 * ((A.choose 2 : ℕ) : ℝ) /
              ((K : ℝ) * B) - (T : ℝ) / B)))
    (hweighted : ((8 * (A * (B * 4 ^ B) + T) : ℕ) : ℝ) < B * L) :
    ∃ I : Finset V, Independent H I ∧ A < I.card := by
  classical
  by_contra hnone
  push Not at hnone
  have hcard : ∀ Z ∈ independentSets H, Z.card ≤ A := by
    intro Z hZ
    exact hnone Z (mem_independentSets.mp hZ)
  obtain ⟨omega, -, hYcard, hYtri, hYext⟩ :=
    exists_large_pruned_sample h3 hlin hB hA hcard hL hscore
      (K := K) (T := T)
  let Y : Finset V := prunedSet H omega
  let G : System Y := restrictSystem H Y
  have h3G : ThreeUniform G := restrict_threeUniform h3 Y
  have hlinG : Linear G := restrict_linear hlin Y
  have htriG : TriangleFree G := by
    exact restrict_triangleFree hYtri
  have hcardG : ∀ I : Finset Y, Independent G I → I.card ≤ A := by
    intro I hI
    rw [independent_restrict_iff] at hI
    rw [← card_valMap Y I]
    exact hnone (valMap Y I) hI
  have hextG : ∀ I : Finset Y, Independent G I →
      totalTruncatedExtension G B I ≤ T := by
    intro I hI
    have hmapInd : Independent H (valMap Y I) := independent_restrict_iff.mp hI
    have hsample :
        ∑ v ∈ Y \ valMap Y I, truncatedExtension H B v (valMap Y I) < T := by
      exact hYext (valMap Y I) hmapInd
    exact (totalTruncatedExtension_restrict_le h3 B I).trans
      (Nat.le_of_lt hsample)
  have hweightNat := weighted_numeric_consequence h3G hlinG htriG
    hB hcardG hextG
  have hweight : ((B * Fintype.card Y : ℕ) : ℝ) ≤
      ((8 * (A * (B * 4 ^ B) + T) : ℕ) : ℝ) := by
    exact_mod_cast hweightNat
  have hYcard' : L ≤ (Fintype.card Y : ℝ) := by
    simpa [Y] using hYcard
  have hBL : (B : ℝ) * L ≤ B * Fintype.card Y := by
    gcongr
  have hcast : ((B * Fintype.card Y : ℕ) : ℝ) =
      (B : ℝ) * Fintype.card Y := by norm_num
  rw [hcast] at hweight
  exact (not_lt_of_ge (hBL.trans hweight)) hweighted

end Lower
end OMA1024


-- ===== from plby module ErdosProblems.Erdos1024.LowerAnalytic =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-!

The constants are intentionally generous.  We sample with probability
approximately `n^(-9/20)`, use logarithmic truncation, and set the proposed
independence threshold to one millionth of `sqrt (n log n)`.
-/

open Filter

namespace OMA1024
namespace Lower

noncomputable def lowerConstant : ℝ := 1 / 1000000

noncomputable def lowerScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log n)

noncomputable def sampleRoot (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((9 : ℝ) / 20)

noncomputable def sampleColors (n : ℕ) : ℕ :=
  ⌈sampleRoot n⌉₊

noncomputable def independenceCutoff (n : ℕ) : ℕ :=
  ⌊lowerConstant * lowerScale n⌋₊

noncomputable def weightCutoff (n : ℕ) : ℕ :=
  ⌊Real.log n / 1000⌋₊

noncomputable def extensionTarget (n : ℕ) : ℝ :=
  100 * (independenceCutoff n : ℝ) ^ 2 / sampleColors n +
    10 * (weightCutoff n : ℝ) * (independenceCutoff n + 1 : ℕ) *
      Real.log (n + 1)

noncomputable def extensionCap (n : ℕ) : ℕ :=
  ⌈extensionTarget n⌉₊

noncomputable def sampleTarget (n : ℕ) : ℝ :=
  (n : ℝ) / (2 * sampleColors n)

lemma lowerConstant_pos : 0 < lowerConstant := by
  norm_num [lowerConstant]

lemma lowerScale_nonneg (n : ℕ) : 0 ≤ lowerScale n := Real.sqrt_nonneg _

lemma lowerScale_sq {n : ℕ} (hn : 1 ≤ n) :
    (lowerScale n) ^ 2 = (n : ℝ) * Real.log n := by
  unfold lowerScale
  rw [Real.sq_sqrt]
  exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn))

lemma sampleRoot_pos {n : ℕ} (hn : 0 < n) : 0 < sampleRoot n := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma sampleColors_pos {n : ℕ} (hn : 0 < n) : 0 < sampleColors n := by
  exact Nat.ceil_pos.mpr (sampleRoot_pos hn)

lemma sampleColors_bounds {n : ℕ} (hn : 1 ≤ n) :
    sampleRoot n ≤ (sampleColors n : ℝ) ∧
      (sampleColors n : ℝ) ≤ 2 * sampleRoot n := by
  have hrpos := sampleRoot_pos (by omega : 0 < n)
  have hrone : 1 ≤ sampleRoot n := by
    unfold sampleRoot
    exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hlower : sampleRoot n ≤ (sampleColors n : ℝ) := Nat.le_ceil _
  have hupper0 : (sampleColors n : ℝ) < sampleRoot n + 1 :=
    Nat.ceil_lt_add_one hrpos.le
  exact ⟨hlower, by linarith⟩

lemma independenceCutoff_upper {n : ℕ} (_hn : 1 ≤ n) :
    (independenceCutoff n : ℝ) ≤ lowerConstant * lowerScale n := by
  exact Nat.floor_le (mul_nonneg lowerConstant_pos.le (lowerScale_nonneg n))

lemma weightCutoff_upper {n : ℕ} (hn : 1 ≤ n) :
    (weightCutoff n : ℝ) ≤ Real.log n / 1000 := by
  exact Nat.floor_le (div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by norm_num))

lemma weightCutoff_lower {n : ℕ}
    (hlog : 2000 ≤ Real.log (n : ℝ)) :
    Real.log n / 2000 ≤ weightCutoff n := by
  have hx : 2 ≤ Real.log (n : ℝ) / 1000 := by linarith
  have hfloor := Nat.sub_one_lt_floor (Real.log (n : ℝ) / 1000)
  have hnonneg : 0 ≤ Real.log (n : ℝ) / 1000 := by linarith
  have hfloorCast : Real.log (n : ℝ) / 1000 - 1 <
      (weightCutoff n : ℝ) := by
    simpa [weightCutoff] using hfloor
  linarith

lemma extensionTarget_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ extensionTarget n := by
  have hk : (0 : ℝ) < sampleColors n := by
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  unfold extensionTarget
  apply add_nonneg
  · exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hk.le
  · have hlog' : 0 ≤ Real.log ((n : ℝ) + 1) := by simpa using hlog
    positivity

lemma extensionCap_bounds {n : ℕ} (hn : 1 ≤ n) :
    extensionTarget n ≤ (extensionCap n : ℝ) ∧
      (extensionCap n : ℝ) ≤ extensionTarget n + 1 := by
  have hnonneg := extensionTarget_nonneg hn
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one hnonneg).le⟩

lemma log_four_lt_two : Real.log (4 : ℝ) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  calc
    (4 : ℝ) = 2 ^ 2 := by norm_num
    _ < Real.exp 1 ^ 2 := by gcongr; exact Real.exp_one_gt_two
    _ = Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      norm_num

/-- The exponential union-bound term is already at most `(n+1)⁻²`.
This estimate is pointwise once the logarithmic cutoff is positive. -/
lemma extensionBadBound_le {n : ℕ} (hn : 1 ≤ n)
    (hB : 0 < weightCutoff n) :
    (((n + 1 : ℕ) : ℝ) ^ (independenceCutoff n + 1) *
      Real.exp (2 * (((independenceCutoff n).choose 2 : ℕ) : ℝ) /
        ((sampleColors n : ℝ) * weightCutoff n) -
          (extensionCap n : ℝ) / weightCutoff n)) ≤
      1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  let a := independenceCutoff n
  let b := weightCutoff n
  let k := sampleColors n
  let x : ℝ := n + 1
  have hbR : (0 : ℝ) < b := by exact_mod_cast hB
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have hx : 1 < x := by dsimp [x]; exact_mod_cast Nat.lt_add_one_iff.mpr hn
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hchooseNat : a.choose 2 ≤ a ^ 2 := Nat.choose_le_pow _ _
  have hchoose : (((a.choose 2 : ℕ) : ℝ)) ≤ (a : ℝ) ^ 2 := by
    exact_mod_cast hchooseNat
  have hT := (extensionCap_bounds hn).1
  have htarget : extensionTarget n =
      100 * (a : ℝ) ^ 2 / k +
        10 * (b : ℝ) * (a + 1 : ℕ) * Real.log (n + 1) := rfl
  have hTdiv :
      (100 * (a : ℝ) ^ 2 / k +
          10 * (b : ℝ) * (a + 1 : ℕ) * Real.log (n + 1)) / b ≤
        (extensionCap n : ℝ) / b := by
    rw [← htarget]
    exact div_le_div_of_nonneg_right hT hbR.le
  have hdivide :
      (100 * (a : ℝ) ^ 2 / k +
          10 * (b : ℝ) * (a + 1 : ℕ) * Real.log (n + 1)) / b =
        100 * (a : ℝ) ^ 2 / (k * b) +
          10 * (a + 1 : ℕ) * Real.log (n + 1) := by
    field_simp
  rw [hdivide] at hTdiv
  have hexponent :
      2 * (((a.choose 2 : ℕ) : ℝ)) / ((k : ℝ) * b) -
          (extensionCap n : ℝ) / b ≤
        -10 * (a + 1 : ℕ) * Real.log (n + 1) := by
    have hnonneg : 0 ≤ (a : ℝ) ^ 2 / ((k : ℝ) * b) := by positivity
    have hchooseDiv :
        2 * (((a.choose 2 : ℕ) : ℝ)) / ((k : ℝ) * b) ≤
          2 * (a : ℝ) ^ 2 / ((k : ℝ) * b) := by gcongr
    calc
      2 * (((a.choose 2 : ℕ) : ℝ)) / ((k : ℝ) * b) -
          (extensionCap n : ℝ) / b ≤
        2 * (a : ℝ) ^ 2 / ((k : ℝ) * b) -
          (extensionCap n : ℝ) / b := sub_le_sub_right hchooseDiv _
      _ ≤ 2 * (a : ℝ) ^ 2 / ((k : ℝ) * b) -
          (100 * (a : ℝ) ^ 2 / ((k : ℝ) * b) +
            10 * (a + 1 : ℕ) * Real.log (n + 1)) :=
        sub_le_sub_left hTdiv _
      _ = -98 * ((a : ℝ) ^ 2 / ((k : ℝ) * b)) -
          10 * (a + 1 : ℕ) * Real.log (n + 1) := by ring
      _ ≤ -10 * (a + 1 : ℕ) * Real.log (n + 1) := by linarith
  have hpowexp : (x : ℝ) ^ (a + 1) =
      Real.exp (((a + 1 : ℕ) : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < x)]
  have hmain :
      (x : ℝ) ^ (a + 1) *
          Real.exp (2 * (((a.choose 2 : ℕ) : ℝ)) / ((k : ℝ) * b) -
            (extensionCap n : ℝ) / b) ≤
        Real.exp (-2 * Real.log x) := by
    rw [hpowexp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have haone : (1 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by norm_num
    have hlogrewrite : Real.log (n + 1) = Real.log x := by rfl
    rw [hlogrewrite] at hexponent
    nlinarith
  calc
    (((n + 1 : ℕ) : ℝ) ^ (independenceCutoff n + 1) *
      Real.exp (2 * (((independenceCutoff n).choose 2 : ℕ) : ℝ) /
        ((sampleColors n : ℝ) * weightCutoff n) -
          (extensionCap n : ℝ) / weightCutoff n)) ≤
        Real.exp (-2 * Real.log x) := by simpa [a, b, k, x] using hmain
    _ = 1 / x ^ 2 := by
      rw [show -2 * Real.log x = -(2 * Real.log x) by ring, Real.exp_neg]
      rw [show (2 : ℝ) * Real.log x = (2 : ℕ) * Real.log x by norm_num,
        Real.exp_nat_mul, Real.exp_log (by linarith : 0 < x)]
      simp [one_div]
    _ = 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by simp [x]

/-! ## Elementary eventual power estimates -/

lemma eventually_log_le_rpow_nat {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ r := by
  have hsmall : (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ r) := by
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_atTop hr).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [hsmall.eventuallyLE, eventually_gt_atTop 1] with n hn hn1
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  have hpow : 0 < (n : ℝ) ^ r :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  simpa [Real.norm_eq_abs, abs_of_pos hlog, abs_of_pos hpow] using hn

lemma eventually_const_le_rpow_nat (C : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ r := by
  exact ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop C)

lemma eventually_two_thousand_le_log :
    ∀ᶠ n : ℕ in atTop, 2000 ≤ Real.log (n : ℝ) := by
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 2000)

lemma log_succ_le_two_mul_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.log n := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hsquare : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (show n + 1 ≤ n ^ 2 by nlinarith)
  calc
    Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hsquare
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

lemma sampleRoot_pow_five {n : ℕ} (hn : 0 < n) :
    (sampleRoot n) ^ 5 = (n : ℝ) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (sampleRoot n) ^ 5 =
        ((n : ℝ) ^ ((9 : ℝ) / 20)) ^ ((5 : ℕ) : ℝ) := by
      dsimp [sampleRoot]
      exact (Real.rpow_natCast ((n : ℝ) ^ ((9 : ℝ) / 20)) 5).symm
    _ = (n : ℝ) ^ (((9 : ℝ) / 20) * 5) := by
      exact (Real.rpow_mul hnR.le _ _).symm
    _ = (n : ℝ) ^ ((9 : ℝ) / 4) := by norm_num
    _ = (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hnR]
      norm_num
    _ = (n : ℝ) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      congr 1
      exact Real.rpow_natCast n 2

lemma quotient_sampleRoot {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / sampleRoot n = (n : ℝ) ^ ((11 : ℝ) / 20) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (n : ℝ) / sampleRoot n =
        (n : ℝ) ^ (1 : ℝ) / (n : ℝ) ^ ((9 : ℝ) / 20) := by
      rw [sampleRoot, Real.rpow_one]
    _ = (n : ℝ) ^ ((1 : ℝ) - (9 : ℝ) / 20) :=
      (Real.rpow_sub hnR _ _).symm
    _ = (n : ℝ) ^ ((11 : ℝ) / 20) := by norm_num

lemma lowerScale_le_rpow {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    lowerScale n ≤ (n : ℝ) ^ ((51 : ℝ) / 100) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  rw [lowerScale, Real.sqrt_le_iff]
  constructor
  · exact (Real.rpow_pos_of_pos hnpos _).le
  · have hmul : (n : ℝ) * Real.log n ≤
        (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 100) := by gcongr
    calc
      (n : ℝ) * Real.log n ≤
          (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 100) := hmul
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 100) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (1 : ℝ) / 100) :=
        (Real.rpow_add hnpos _ _).symm
      _ = (n : ℝ) ^ ((101 : ℝ) / 100) := by
        norm_num
      _ ≤ (n : ℝ) ^ ((102 : ℝ) / 100) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
      _ = ((n : ℝ) ^ ((51 : ℝ) / 100)) ^ 2 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hnpos.le]
        norm_num

lemma four_pow_weightCutoff_le {n : ℕ} (hn : 1 ≤ n) :
    (((4 ^ weightCutoff n : ℕ) : ℝ)) ≤
      (n : ℝ) ^ ((1 : ℝ) / 500) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hB := weightCutoff_upper hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hexponent : (weightCutoff n : ℝ) * Real.log 4 ≤
      Real.log n / 500 := by
    calc
      (weightCutoff n : ℝ) * Real.log 4 ≤
          (Real.log n / 1000) * Real.log 4 := by gcongr
      _ ≤ (Real.log n / 1000) * 2 := by gcongr; exact log_four_lt_two.le
      _ = Real.log n / 500 := by ring
  have hpowexp : ((4 : ℝ) ^ weightCutoff n) =
      Real.exp ((weightCutoff n : ℝ) * Real.log 4) := by
    symm
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  calc
    (((4 ^ weightCutoff n : ℕ) : ℝ)) = (4 : ℝ) ^ weightCutoff n := by norm_num
    _ = Real.exp ((weightCutoff n : ℝ) * Real.log 4) := hpowexp
    _ ≤ Real.exp (Real.log n / 500) := Real.exp_le_exp.mpr hexponent
    _ = (n : ℝ) ^ ((1 : ℝ) / 500) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring

/-! ## The sampling-score inequality -/

lemma triangle_loss_le {n : ℕ} (hn : 1 ≤ n)
    (hquarter : 8 ≤ (n : ℝ) ^ ((1 : ℝ) / 4)) :
    (((n ^ 3 : ℕ) : ℝ) / (sampleColors n : ℝ) ^ 6) ≤
      (n : ℝ) / (8 * sampleColors n) := by
  let x : ℝ := n
  let k : ℝ := sampleColors n
  have hx : 0 < x := by dsimp [x]; positivity
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have hroot := (sampleColors_bounds hn).1
  have hcore : 8 * x ^ 2 ≤ k ^ 5 := by
    calc
      8 * x ^ 2 ≤ x ^ ((1 : ℝ) / 4) * x ^ 2 := by
        gcongr
      _ = (sampleRoot n) ^ 5 := by
        rw [sampleRoot_pow_five (by omega : 0 < n)]
        ring
      _ ≤ k ^ 5 := by
        exact pow_le_pow_left₀ (sampleRoot_pos (by omega)).le hroot 5
  have hcross : x ^ 3 * (8 * k) ≤ x * k ^ 6 := by
    calc
      x ^ 3 * (8 * k) = (x * k) * (8 * x ^ 2) := by ring
      _ ≤ (x * k) * k ^ 5 := by gcongr
      _ = x * k ^ 6 := by ring
  rw [div_le_div_iff₀ (pow_pos hk 6) (mul_pos (by norm_num) hk)]
  simpa only [x, k, Nat.cast_pow] using hcross

lemma sampleColors_le_n {n : ℕ} (hn : 1 ≤ n)
    (hpower : 2 ≤ (n : ℝ) ^ ((11 : ℝ) / 20)) :
    (sampleColors n : ℝ) ≤ n := by
  have hr := (sampleColors_bounds hn).2
  have hq := quotient_sampleRoot (by omega : 0 < n)
  have hrootpos := sampleRoot_pos (by omega : 0 < n)
  rw [← hq] at hpower
  have hmul := mul_le_mul_of_nonneg_right hpower hrootpos.le
  have hncast : (n : ℝ) / sampleRoot n * sampleRoot n = n := by
    field_simp
  linarith

lemma bad_loss_le {n : ℕ} (hn : 6 ≤ n)
    (hpower : 2 ≤ (n : ℝ) ^ ((11 : ℝ) / 20))
    (hB : 0 < weightCutoff n) :
    (n : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ (independenceCutoff n + 1) *
          Real.exp (2 * (((independenceCutoff n).choose 2 : ℕ) : ℝ) /
            ((sampleColors n : ℝ) * weightCutoff n) -
              (extensionCap n : ℝ) / weightCutoff n)) ≤
      (n : ℝ) / (8 * sampleColors n) := by
  have hq := extensionBadBound_le (show 1 ≤ n by omega) hB
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hk : (0 : ℝ) < sampleColors n := by
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have hkn : (sampleColors n : ℝ) ≤ n :=
    sampleColors_le_n (show 1 ≤ n by omega) hpower
  have hden : (8 : ℝ) * sampleColors n ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have h8n : (8 : ℝ) * n ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      push_cast
      have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 3)]
    exact (mul_le_mul_of_nonneg_left hkn (by norm_num)).trans h8n
  calc
    (n : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ (independenceCutoff n + 1) *
          Real.exp (2 * (((independenceCutoff n).choose 2 : ℕ) : ℝ) /
            ((sampleColors n : ℝ) * weightCutoff n) -
              (extensionCap n : ℝ) / weightCutoff n)) ≤
        (n : ℝ) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by gcongr
    _ ≤ (n : ℝ) * (1 / ((8 : ℝ) * sampleColors n)) := by
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (by positivity) hden) hn0
    _ = (n : ℝ) / (8 * sampleColors n) := by ring

theorem eventually_sampling_score :
    ∀ᶠ n : ℕ in atTop,
      0 < weightCutoff n ∧ 0 < sampleTarget n ∧
      sampleTarget n ≤
        (n : ℝ) / sampleColors n -
          (((n ^ 3 : ℕ) : ℝ) / (sampleColors n : ℝ) ^ 6) -
          (n : ℝ) *
            (((n + 1 : ℕ) : ℝ) ^ (independenceCutoff n + 1) *
              Real.exp (2 * (((independenceCutoff n).choose 2 : ℕ) : ℝ) /
                ((sampleColors n : ℝ) * weightCutoff n) -
                  (extensionCap n : ℝ) / weightCutoff n)) := by
  filter_upwards [eventually_ge_atTop 6, eventually_two_thousand_le_log,
    eventually_const_le_rpow_nat 8 (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_const_le_rpow_nat 2 (by norm_num : (0 : ℝ) < 11 / 20)]
      with n hn hlog hquarter hpower
  have hB : 0 < weightCutoff n := by
    have hlower := weightCutoff_lower hlog
    have : (1 : ℝ) ≤ weightCutoff n := by linarith
    exact_mod_cast this
  have hk : (0 : ℝ) < sampleColors n := by
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have htri := triangle_loss_le (show 1 ≤ n by omega) hquarter
  have hbad := bad_loss_le hn hpower hB
  have hratio : (n : ℝ) / sampleColors n =
      8 * ((n : ℝ) / (8 * sampleColors n)) := by field_simp
  have htarget : sampleTarget n =
      4 * ((n : ℝ) / (8 * sampleColors n)) := by
    unfold sampleTarget
    field_simp
    ring
  refine ⟨hB, ?_, ?_⟩
  · unfold sampleTarget
    positivity
  · rw [htarget, hratio]
    have hq0 : (0 : ℝ) ≤ n / (8 * sampleColors n) := by positivity
    linarith

/-! ## The weighted contradiction inequality -/

lemma independenceCutoff_le_rpow {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    (independenceCutoff n : ℝ) ≤
      lowerConstant * (n : ℝ) ^ ((51 : ℝ) / 100) := by
  exact (independenceCutoff_upper hn).trans
    (mul_le_mul_of_nonneg_left (lowerScale_le_rpow hn hlog) lowerConstant_pos.le)

lemma independenceCutoff_le_plain_rpow {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    (independenceCutoff n : ℝ) ≤
      (n : ℝ) ^ ((51 : ℝ) / 100) := by
  have hc : lowerConstant ≤ 1 := by norm_num [lowerConstant]
  exact (independenceCutoff_le_rpow hn hlog).trans <| by
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) hc

lemma pivot_allocation {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    128 * (sampleColors n : ℝ) * independenceCutoff n *
        ((4 ^ weightCutoff n : ℕ) : ℝ) ≤ n := by
  let x : ℝ := n
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hn
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hK := (sampleColors_bounds hn).2
  have hA := independenceCutoff_le_rpow hn hlog
  have hfour := four_pow_weightCutoff_le hn
  have hK' : (sampleColors n : ℝ) ≤ 2 * x ^ ((9 : ℝ) / 20) := by
    simpa [x, sampleRoot] using hK
  have hA' : (independenceCutoff n : ℝ) ≤
      lowerConstant * x ^ ((51 : ℝ) / 100) := by simpa [x] using hA
  have hfour' : (((4 ^ weightCutoff n : ℕ) : ℝ)) ≤
      x ^ ((1 : ℝ) / 500) := by simpa [x] using hfour
  have hc0 : 0 ≤ lowerConstant := lowerConstant_pos.le
  have hpows :
      x ^ ((9 : ℝ) / 20) * x ^ ((51 : ℝ) / 100) *
          x ^ ((1 : ℝ) / 500) = x ^ ((481 : ℝ) / 500) := by
    rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
    norm_num
  calc
    128 * (sampleColors n : ℝ) * independenceCutoff n *
        ((4 ^ weightCutoff n : ℕ) : ℝ) ≤
      128 * (2 * x ^ ((9 : ℝ) / 20)) *
        (lowerConstant * x ^ ((51 : ℝ) / 100)) *
          x ^ ((1 : ℝ) / 500) := by
            gcongr
    _ = (256 * lowerConstant) * x ^ ((481 : ℝ) / 500) := by
      rw [← hpows]
      ring
    _ ≤ x ^ ((481 : ℝ) / 500) := by
      have hc : 256 * lowerConstant ≤ 1 := by norm_num [lowerConstant]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hxpos.le _) hc
    _ ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ = n := by simp [x]

lemma square_allocation {n : ℕ} (hn : 1 ≤ n)
    (hlog : 2000 ≤ Real.log (n : ℝ)) :
    12800 * (independenceCutoff n : ℝ) ^ 2 ≤
      (weightCutoff n : ℝ) * n := by
  have hA := independenceCutoff_upper hn
  have hA0 : (0 : ℝ) ≤ independenceCutoff n := by positivity
  have hcscale0 : 0 ≤ lowerConstant * lowerScale n :=
    mul_nonneg lowerConstant_pos.le (lowerScale_nonneg n)
  have hsq : (independenceCutoff n : ℝ) ^ 2 ≤
      (lowerConstant * lowerScale n) ^ 2 := by
    nlinarith [sq_nonneg
      ((lowerConstant * lowerScale n) - independenceCutoff n)]
  have hB := weightCutoff_lower hlog
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ n := by positivity
  calc
    12800 * (independenceCutoff n : ℝ) ^ 2 ≤
        12800 * (lowerConstant * lowerScale n) ^ 2 := by gcongr
    _ = (12800 * lowerConstant ^ 2) *
        ((n : ℝ) * Real.log n) := by
      rw [mul_pow, lowerScale_sq hn]
      ring
    _ ≤ (1 / 2000 : ℝ) * ((n : ℝ) * Real.log n) := by
      have hc : 12800 * lowerConstant ^ 2 ≤ (1 / 2000 : ℝ) := by
        norm_num [lowerConstant]
      gcongr
    _ = (Real.log n / 2000) * n := by ring
    _ ≤ (weightCutoff n : ℝ) * n := by gcongr

lemma logarithmic_allocation {n : ℕ} (hn : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100))
    (hpower : 10240 ≤ (n : ℝ) ^ ((3 : ℝ) / 100)) :
    1280 * (sampleColors n : ℝ) * (independenceCutoff n + 1 : ℕ) *
        Real.log (n + 1) ≤ n := by
  let x : ℝ := n
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show 1 ≤ n by omega)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hK := (sampleColors_bounds (show 1 ≤ n by omega)).2
  have hA := independenceCutoff_le_plain_rpow (show 1 ≤ n by omega) hlog
  have hxpow : 1 ≤ x ^ ((51 : ℝ) / 100) :=
    Real.one_le_rpow hx (by norm_num)
  have hAplus : ((independenceCutoff n + 1 : ℕ) : ℝ) ≤
      2 * x ^ ((51 : ℝ) / 100) := by
    push_cast
    dsimp [x] at hA ⊢
    linarith
  have hlogs : Real.log ((n + 1 : ℕ) : ℝ) ≤
      2 * x ^ ((1 : ℝ) / 100) := by
    calc
      Real.log ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.log n :=
        log_succ_le_two_mul_log hn
      _ ≤ 2 * x ^ ((1 : ℝ) / 100) := by
        dsimp [x]
        gcongr
  have hK' : (sampleColors n : ℝ) ≤ 2 * x ^ ((9 : ℝ) / 20) := by
    simpa [x, sampleRoot] using hK
  have hlognonneg : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hpows :
      x ^ ((9 : ℝ) / 20) * x ^ ((51 : ℝ) / 100) *
          x ^ ((1 : ℝ) / 100) = x ^ ((97 : ℝ) / 100) := by
    rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
    norm_num
  calc
    1280 * (sampleColors n : ℝ) * (independenceCutoff n + 1 : ℕ) *
        Real.log (n + 1) ≤
      1280 * (2 * x ^ ((9 : ℝ) / 20)) *
        (2 * x ^ ((51 : ℝ) / 100)) *
          (2 * x ^ ((1 : ℝ) / 100)) := by
            gcongr
            · simpa using hlognonneg
            · simpa using hlogs
    _ = 10240 * x ^ ((97 : ℝ) / 100) := by
      rw [← hpows]
      ring
    _ ≤ x ^ ((3 : ℝ) / 100) * x ^ ((97 : ℝ) / 100) := by
      gcongr
    _ = x ^ (1 : ℝ) := by
      rw [← Real.rpow_add hxpos]
      norm_num
    _ = n := by simp [x]

lemma ceiling_allocation {n : ℕ} (hn : 1 ≤ n)
    (hpower : 256 ≤ (n : ℝ) ^ ((11 : ℝ) / 20))
    (hB : 1 ≤ weightCutoff n) :
    128 * (sampleColors n : ℝ) ≤ (weightCutoff n : ℝ) * n := by
  have hK := (sampleColors_bounds hn).2
  have hroot : 256 * sampleRoot n ≤ n := by
    have hq := quotient_sampleRoot (by omega : 0 < n)
    have hrpos := sampleRoot_pos (by omega : 0 < n)
    rw [← hq] at hpower
    have := mul_le_mul_of_nonneg_right hpower hrpos.le
    have hncast : (n : ℝ) / sampleRoot n * sampleRoot n = n := by
      field_simp
    linarith
  have h128K : 128 * (sampleColors n : ℝ) ≤ n := by
    calc
      128 * (sampleColors n : ℝ) ≤ 128 * (2 * sampleRoot n) := by gcongr
      _ = 256 * sampleRoot n := by ring
      _ ≤ n := hroot
  have hBcast : (1 : ℝ) ≤ weightCutoff n := by exact_mod_cast hB
  exact h128K.trans <| by
    calc
      (n : ℝ) = 1 * n := by ring
      _ ≤ (weightCutoff n : ℝ) * n := by gcongr

theorem eventually_weighted_inequality :
    ∀ᶠ n : ℕ in atTop,
      ((8 * (independenceCutoff n *
          (weightCutoff n * 4 ^ weightCutoff n) + extensionCap n) : ℕ) : ℝ) <
        (weightCutoff n : ℝ) * sampleTarget n := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_log_le_rpow_nat (by norm_num : (0 : ℝ) < 1 / 100),
    eventually_two_thousand_le_log,
    eventually_const_le_rpow_nat 10240 (by norm_num : (0 : ℝ) < 3 / 100),
    eventually_const_le_rpow_nat 256 (by norm_num : (0 : ℝ) < 11 / 20)]
      with n hn hlog hlogLower h10240 h256
  let K : ℝ := sampleColors n
  let A : ℝ := independenceCutoff n
  let B : ℝ := weightCutoff n
  let P : ℝ := ((4 ^ weightCutoff n : ℕ) : ℝ)
  let T : ℝ := extensionCap n
  let x : ℝ := n
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have hBnat : 0 < weightCutoff n := by
    have hlower := weightCutoff_lower hlogLower
    have : (1 : ℝ) ≤ weightCutoff n := by linarith
    exact_mod_cast this
  have hB : 0 < B := by dsimp [B]; exact_mod_cast hBnat
  have hx : 0 < x := by dsimp [x]; positivity
  have hpivot := pivot_allocation (show 1 ≤ n by omega) hlog
  have hsquare := square_allocation (show 1 ≤ n by omega) hlogLower
  have hlogarithmic := logarithmic_allocation hn hlog h10240
  have hceiling := ceiling_allocation (show 1 ≤ n by omega) h256 hBnat
  have hTcap := (extensionCap_bounds (show 1 ≤ n by omega)).2
  have hTupper : T ≤
      100 * A ^ 2 / K + 10 * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
        Real.log (n + 1) + 1 := by
    simpa [T, extensionTarget, A, B, K] using hTcap
  have hsum :
      16 * K * (A * (B * P) + T) < B * x := by
    have hmajor :
        16 * K * (A * (B * P) + T) ≤
          16 * K * A * B * P + 1600 * A ^ 2 +
            160 * K * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
              Real.log (n + 1) + 16 * K := by
      calc
        16 * K * (A * (B * P) + T) ≤
            16 * K * (A * (B * P) +
              (100 * A ^ 2 / K +
                10 * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
                  Real.log (n + 1) + 1)) := by gcongr
        _ = 16 * K * A * B * P + 1600 * A ^ 2 +
            160 * K * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
              Real.log (n + 1) + 16 * K := by
          field_simp
          ring
    have hpivot' : 8 * (16 * K * A * B * P) ≤ B * x := by
      have hpivot0 : 128 * K * A * P ≤ x := by
        simpa [K, A, P, x] using hpivot
      calc
        8 * (16 * K * A * B * P) = B * (128 * K * A * P) := by ring
        _ ≤ B * x := mul_le_mul_of_nonneg_left hpivot0 hB.le
    have hsquare' : 8 * (1600 * A ^ 2) ≤ B * x := by
      calc
        8 * (1600 * A ^ 2) = 12800 * A ^ 2 := by ring
        _ ≤ B * x := by simpa [A, B, x] using hsquare
    have hlogarithmic' :
        8 * (160 * K * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
          Real.log (n + 1)) ≤ B * x := by
      have hlogarithmic0 :
          1280 * K * ((independenceCutoff n + 1 : ℕ) : ℝ) *
            Real.log (n + 1) ≤ x := by
        simpa [K, x] using hlogarithmic
      calc
        8 * (160 * K * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
            Real.log (n + 1)) =
          B * (1280 * K * ((independenceCutoff n + 1 : ℕ) : ℝ) *
            Real.log (n + 1)) := by ring
        _ ≤ B * x := mul_le_mul_of_nonneg_left hlogarithmic0 hB.le
    have hceiling' : 8 * (16 * K) ≤ B * x := by
      calc
        8 * (16 * K) = 128 * K := by ring
        _ ≤ B * x := by simpa [K, B, x] using hceiling
    have hBx : 0 < B * x := mul_pos hB hx
    nlinarith
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  change 8 * (A * (B * ((4 : ℝ) ^ weightCutoff n)) + T) <
    B * (x / (2 * K))
  rw [show B * (x / (2 * K)) = B * x / (2 * K) by ring,
    lt_div_iff₀ (mul_pos (by norm_num) hK)]
  have hpow : ((4 : ℝ) ^ weightCutoff n) = P := by
    simp [P]
  rw [hpow]
  nlinarith

lemma independenceCutoff_le_n {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    independenceCutoff n ≤ n := by
  have hA := independenceCutoff_le_plain_rpow hn hlog
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ ((51 : ℝ) / 100) ≤ (n : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  have : (independenceCutoff n : ℝ) ≤ n := by
    simpa using hA.trans hpow
  exact_mod_cast this

/-- For every sufficiently large order, every linear triple system has an
independent set strictly larger than the explicit floor cutoff. -/
theorem eventually_exists_independent_gt :
    ∀ᶠ n : ℕ in atTop, ∀ H : System (Fin n),
      ThreeUniform H → Linear H →
        ∃ I : Finset (Fin n), Independent H I ∧
          independenceCutoff n < I.card := by
  filter_upwards [eventually_sampling_score, eventually_weighted_inequality,
    eventually_ge_atTop 1,
    eventually_log_le_rpow_nat (by norm_num : (0 : ℝ) < 1 / 100)]
      with n hscore hweighted hn hlog
  intro H h3 hlin
  let : NeZero (sampleColors n) :=
    ⟨(sampleColors_pos (by omega : 0 < n)).ne'⟩
  apply exists_independent_gt_of_parameters h3 hlin
    (K := sampleColors n) (A := independenceCutoff n)
    (B := weightCutoff n) (T := extensionCap n)
    (L := sampleTarget n)
  · exact hscore.1
  · simpa using independenceCutoff_le_n hn hlog
  · exact hscore.2.1
  · simpa using hscore.2.2
  · exact hweighted

end Lower
end OMA1024

-- ===== from plby module ErdosProblems.Erdos1024 =====
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1024.
https://www.erdosproblems.com/forum/thread/1024

Informal authors:
- K. T. Phelps
- Vojtěch Rödl

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/OMA1024.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


/-!

For an `n`-vertex three-uniform linear hypergraph, let `f(n)` be the largest
integer which is always the size of some independent set.  Phelps and Rödl
proved

`f(n) = Θ(√(n log n))`.

The mathematical reconstruction, including the quantitative probabilistic
lemmas and the formalization plan, is in `tex/1024.tex`.
-/

open Filter
open scoped BigOperators

namespace OMA1024

/-! ## Exact finite formulation -/

/-- A finite triple system on the fixed vertex type `Fin n`. -/
abbrev TripleSystem (n : ℕ) := Finset (Finset (Fin n))

/-- All three-element subsets of `Fin n`. -/
def allTriples (n : ℕ) : TripleSystem n :=
  Finset.univ.powersetCard 3

/-- Every member of `H` is a triple. -/
def IsThreeUniform {n : ℕ} (H : TripleSystem n) : Prop :=
  ∀ e ∈ H, e.card = 3

instance isThreeUniformDecidable {n : ℕ} (H : TripleSystem n) :
    Decidable (IsThreeUniform H) := by
  unfold IsThreeUniform
  infer_instance

/-- Distinct edges meet in at most one vertex. -/
def IsLinear {n : ℕ} (H : TripleSystem n) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ∀ ⦃f⦄, f ∈ H → e ≠ f → (e ∩ f).card ≤ 1

instance isLinearDecidable {n : ℕ} (H : TripleSystem n) :
    Decidable (IsLinear H) := by
  unfold IsLinear
  infer_instance

/-- `I` contains no whole edge of `H`. -/
def IsIndependent {n : ℕ} (H : TripleSystem n) (I : Finset (Fin n)) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ¬e ⊆ I

instance isIndependentDecidable {n : ℕ} (H : TripleSystem n)
    (I : Finset (Fin n)) : Decidable (IsIndependent H I) := by
  unfold IsIndependent
  infer_instance

theorem subset_allTriples_iff {n : ℕ} {H : TripleSystem n} :
    H ⊆ allTriples n ↔ IsThreeUniform H := by
  constructor
  · intro h e he
    exact (Finset.mem_powersetCard.mp (h he)).2
  · intro h e he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, h e he⟩

@[simp]
theorem independent_empty {n : ℕ} (H : TripleSystem n) :
    IsIndependent H ∅ ↔ ∅ ∉ H := by
  constructor
  · intro h hmem
    exact h hmem (Finset.empty_subset _)
  · intro hempty e he hesub
    have : e = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
      simpa using hesub hx
    exact hempty (this ▸ he)

theorem independent_mono {n : ℕ} {H : TripleSystem n}
    {I J : Finset (Fin n)} (hI : IsIndependent H I) (hJI : J ⊆ I) :
    IsIndependent H J := by
  intro e he heJ
  exact hI he (heJ.trans hJI)

/-- The largest cardinality of an independent vertex set. -/
noncomputable def independenceNumber {n : ℕ} (H : TripleSystem n) : ℕ :=
  (Finset.univ.powerset.filter (IsIndependent H)).sup Finset.card

theorem card_le_independenceNumber {n : ℕ} {H : TripleSystem n}
    {I : Finset (Fin n)} (hI : IsIndependent H I) :
    I.card ≤ independenceNumber H := by
  classical
  unfold independenceNumber
  apply Finset.le_sup
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ I), hI⟩

theorem independenceNumber_le {n : ℕ} (H : TripleSystem n) :
    independenceNumber H ≤ n := by
  classical
  unfold independenceNumber
  apply Finset.sup_le
  intro I hI
  have hcard := Finset.card_le_card (Finset.mem_powerset.mp
    (Finset.mem_filter.mp hI).1)
  simpa using hcard

theorem independentFamily_nonempty {n : ℕ} (H : TripleSystem n)
    (hempty : ∅ ∉ H) :
    (Finset.univ.powerset.filter (IsIndependent H)).Nonempty := by
  classical
  exact ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      (independent_empty H).mpr hempty⟩⟩

theorem exists_independent_card_eq {n : ℕ} (H : TripleSystem n)
    (hempty : ∅ ∉ H) :
    ∃ I : Finset (Fin n), IsIndependent H I ∧
      I.card = independenceNumber H := by
  classical
  obtain ⟨I, hI, hcard⟩ := Finset.exists_mem_eq_sup
    (Finset.univ.powerset.filter (IsIndependent H))
    (independentFamily_nonempty H hempty) Finset.card
  refine ⟨I, (Finset.mem_filter.mp hI).2, ?_⟩
  simpa [independenceNumber] using hcard.symm

/-- Adding edges can only decrease the independence number. -/
theorem independenceNumber_antitone {n : ℕ} {H K : TripleSystem n}
    (hHK : H ⊆ K) : independenceNumber K ≤ independenceNumber H := by
  classical
  unfold independenceNumber
  apply Finset.sup_le
  intro I hIK
  apply Finset.le_sup
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hIK).1, ?_⟩
  intro e heH
  exact (Finset.mem_filter.mp hIK).2 (hHK heH)

/-- The finite collection of all linear triple systems on `Fin n`. -/
noncomputable def linearSystems (n : ℕ) : Finset (TripleSystem n) :=
  (allTriples n).powerset.filter IsLinear

theorem linearSystems_nonempty (n : ℕ) : (linearSystems n).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [linearSystems, IsLinear]

theorem mem_linearSystems_iff {n : ℕ} {H : TripleSystem n} :
    H ∈ linearSystems n ↔ IsThreeUniform H ∧ IsLinear H := by
  classical
  rw [linearSystems, Finset.mem_filter, Finset.mem_powerset,
    subset_allTriples_iff]

/-- The least possible independence number of an `n`-vertex linear triple
system.  This is the precise extremal interpretation of `f(n)` in the
problem. -/
noncomputable def guaranteedIndependence (n : ℕ) : ℕ :=
  (linearSystems n).inf' (linearSystems_nonempty n) independenceNumber

theorem guaranteedIndependence_le {n : ℕ} {H : TripleSystem n}
    (h3 : IsThreeUniform H) (hlin : IsLinear H) :
    guaranteedIndependence n ≤ independenceNumber H := by
  classical
  unfold guaranteedIndependence
  exact Finset.inf'_le independenceNumber
    (mem_linearSystems_iff.mpr ⟨h3, hlin⟩)

theorem exists_extremal_system (n : ℕ) :
    ∃ H : TripleSystem n,
      IsThreeUniform H ∧ IsLinear H ∧
        independenceNumber H = guaranteedIndependence n := by
  classical
  obtain ⟨H, hH, heq⟩ := Finset.exists_mem_eq_inf'
    (linearSystems_nonempty n) independenceNumber
  exact ⟨H, (mem_linearSystems_iff.mp hH).1,
    (mem_linearSystems_iff.mp hH).2, heq.symm⟩

theorem guaranteedIndependence_le_n (n : ℕ) :
    guaranteedIndependence n ≤ n := by
  obtain ⟨H, -, -, hH⟩ := exists_extremal_system n
  rw [← hH]
  exact independenceNumber_le H

/-- `k` is universally guaranteed if every linear triple system on `Fin n`
has an independent set with at least `k` vertices. -/
def UniversallyGuarantees (n k : ℕ) : Prop :=
  ∀ H : TripleSystem n, IsThreeUniform H → IsLinear H →
    ∃ I : Finset (Fin n), IsIndependent H I ∧ k ≤ I.card

/-- The extremal definition really is the largest universally guaranteed
integer, rather than merely some one-sided bound. -/
theorem universallyGuarantees_iff_le {n k : ℕ} :
    UniversallyGuarantees n k ↔ k ≤ guaranteedIndependence n := by
  constructor
  · intro h
    obtain ⟨H, h3, hlin, hH⟩ := exists_extremal_system n
    obtain ⟨I, hI, hkI⟩ := h H h3 hlin
    rw [← hH]
    exact hkI.trans (card_le_independenceNumber hI)
  · intro hk H h3 hlin
    have hempty : ∅ ∉ H := by
      intro h0
      have := h3 ∅ h0
      simp at this
    obtain ⟨I, hI, hcard⟩ := exists_independent_card_eq H hempty
    exact ⟨I, hI, hk.trans ((guaranteedIndependence_le h3 hlin).trans_eq
      hcard.symm)⟩

/-- There is a linear triple system witnessing sharpness of the universal
guarantee at each finite order. -/
theorem exists_system_sharp_for_guarantee (n : ℕ) :
    ∃ H : TripleSystem n, IsThreeUniform H ∧ IsLinear H ∧
      ∀ I : Finset (Fin n), IsIndependent H I →
        I.card ≤ guaranteedIndependence n := by
  obtain ⟨H, h3, hlin, hH⟩ := exists_extremal_system n
  refine ⟨H, h3, hlin, ?_⟩
  intro I hI
  rw [← hH]
  exact card_le_independenceNumber hI

/-! The quantitative Phelps--Rödl lower and upper bounds, and their
asymptotic assembly, follow below. -/

/-! ## The asymptotic scale and a two-sided-bound assembler -/

/-- The real-valued scale occurring in the Phelps--Rödl theorem. -/
noncomputable def resolutionScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log n)

theorem resolutionScale_eq_upperScale (n : ℕ) :
    resolutionScale n = Upper.upperScale n := rfl

/-! ## The Phelps--Rödl upper bound -/

/-- The explicit local-lemma construction bounds the exact extremal
quantity by `ceil (200 * sqrt (n log n))`. -/
theorem guaranteedIndependence_lt_upperThreshold (n : ℕ) (hn : 3 ≤ n) :
    guaranteedIndependence n < Upper.upperThreshold n := by
  obtain ⟨H, h3, hlin, hhits⟩ := Upper.exists_upper_system n hn
  have hempty : ∅ ∉ H := by
    intro h0
    have := h3 ∅ h0
    simp at this
  obtain ⟨I, hI, hcard⟩ := exists_independent_card_eq H hempty
  have hIt : I.card < Upper.upperThreshold n := by
    by_contra hnot
    obtain ⟨S, hSI, hScard⟩ :=
      Finset.exists_subset_card_eq (Nat.le_of_not_gt hnot)
    obtain ⟨e, heH, heS⟩ := hhits S hScard
    exact hI heH (heS.trans hSI)
  exact (guaranteedIndependence_le h3 hlin).trans_lt (hcard ▸ hIt)

theorem guaranteedIndependence_upper_bound (n : ℕ) (hn : 3 ≤ n) :
    (guaranteedIndependence n : ℝ) ≤ 201 * resolutionScale n := by
  have hnat := (guaranteedIndependence_lt_upperThreshold n hn).le
  have hcast : (guaranteedIndependence n : ℝ) ≤ Upper.upperThreshold n := by
    exact_mod_cast hnat
  rw [resolutionScale_eq_upperScale]
  exact hcast.trans (Upper.threshold_bounds hn).2.1

theorem resolutionScale_nonneg (n : ℕ) : 0 ≤ resolutionScale n := by
  exact Real.sqrt_nonneg _

/-- Eventual positive two-sided constant bounds are exactly what is needed
to manufacture a `Theta` statement.  Keeping this bookkeeping separate
prevents the probabilistic arguments from being entangled with norms. -/
theorem isTheta_of_eventually_two_sided
    (f g : ℕ → ℝ) (c C : ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (hc : 0 < c)
    (hlower : ∀ᶠ n in atTop, c * g n ≤ f n)
    (hupper : ∀ᶠ n in atTop, f n ≤ C * g n) :
    f =Θ[atTop] g := by
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    exact hupper.mono fun n hn ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf n), abs_of_nonneg (hg n)] using hn
  · apply Asymptotics.IsBigO.of_bound c⁻¹
    exact hlower.mono fun n hn ↦ by
      simp only [Real.norm_eq_abs, abs_of_nonneg (hf n), abs_of_nonneg (hg n)]
      calc
        g n = c⁻¹ * (c * g n) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
        _ ≤ c⁻¹ * f n := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hc.le)

/-! ## The Phelps--Rödl lower bound and final resolution -/

/-- The finite sampling-and-weight argument gives a universal lower bound
with an explicit positive constant. -/
theorem eventually_guaranteedIndependence_lower_bound :
    ∀ᶠ n : ℕ in atTop,
      Lower.lowerConstant * resolutionScale n ≤
        (guaranteedIndependence n : ℝ) := by
  filter_upwards [Lower.eventually_exists_independent_gt] with n hn
  have huniv : UniversallyGuarantees n (Lower.independenceCutoff n + 1) := by
    intro H h3 hlin
    have h3' : Lower.ThreeUniform H := h3
    have hlin' : Lower.Linear H := hlin
    obtain ⟨I, hI, hcard⟩ := hn H h3' hlin'
    refine ⟨I, ?_, by omega⟩
    exact hI
  have hguar : Lower.independenceCutoff n + 1 ≤
      guaranteedIndependence n := universallyGuarantees_iff_le.mp huniv
  have hfloor : Lower.lowerConstant * resolutionScale n <
      (Lower.independenceCutoff n : ℝ) + 1 := by
    simpa [Lower.independenceCutoff, Lower.lowerScale, resolutionScale] using
      (Nat.lt_floor_add_one (Lower.lowerConstant * Lower.lowerScale n))
  have hguarR : (Lower.independenceCutoff n : ℝ) + 1 ≤
      guaranteedIndependence n := by exact_mod_cast hguar
  exact (hfloor.trans_le hguarR).le

/-- Resolution of Erdős Problem 1024: the exact minimum guaranteed
independence number is of order `sqrt (n log n)`. -/
theorem erdos_1024 :
    (fun n : ℕ ↦ (guaranteedIndependence n : ℝ)) =Θ[atTop]
      resolutionScale := by
  apply isTheta_of_eventually_two_sided
    (fun n : ℕ ↦ (guaranteedIndependence n : ℝ)) resolutionScale
    Lower.lowerConstant 201
  · intro n
    positivity
  · exact resolutionScale_nonneg
  · exact Lower.lowerConstant_pos
  · exact eventually_guaranteedIndependence_lower_bound
  · filter_upwards [eventually_ge_atTop 3] with n hn
    exact guaranteedIndependence_upper_bound n hn

end OMA1024




namespace OMA1024Bridge

open Filter Asymptotics

theorem indep_eq {n : ℕ} (H : Finset (Finset (Fin n))) :
    H.hypergraphIndependenceNumber = OMA1024.independenceNumber H := by
  classical
  unfold Finset.hypergraphIndependenceNumber OMA1024.independenceNumber
  congr 1
  ext I
  simp only [Finset.mem_filter, Finset.IsHypergraphIndependent, OMA1024.IsIndependent]

theorem mem_iff {n : ℕ} (H : Finset (Finset (Fin n))) :
    (H ⊆ (Finset.univ : Finset (Fin n)).powersetCard 3 ∧ H.IsLinearHypergraph) ↔
      H ∈ OMA1024.linearSystems n := by
  rw [OMA1024.mem_linearSystems_iff, ← OMA1024.subset_allTriples_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro e he f hf hef
    exact h2 he hf hef
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro e he f hf hef
    exact h2 he hf hef

theorem lin_eq (n : ℕ) :
    Hypergraph.linearIndependenceNumber n = OMA1024.guaranteedIndependence n := by
  classical
  obtain ⟨H0, h3, hlin, hH0⟩ := OMA1024.exists_extremal_system n
  have hle := OMA1024.guaranteedIndependence_le_n n
  set m := OMA1024.guaranteedIndependence n with hm
  have hsup : (((Finset.univ : Finset (Fin n)).powersetCard 3).powerset.filter
      Finset.IsLinearHypergraph).sup (fun H => n - H.hypergraphIndependenceNumber) = n - m := by
    apply le_antisymm
    · apply Finset.sup_le
      intro H hH
      rw [Finset.mem_filter, Finset.mem_powerset] at hH
      have hmem := (mem_iff H).mp hH
      have : m ≤ OMA1024.independenceNumber H := by
        rw [hm]
        unfold OMA1024.guaranteedIndependence
        exact Finset.inf'_le _ hmem
      rw [indep_eq]
      omega
    · have hmem : H0 ∈ ((Finset.univ : Finset (Fin n)).powersetCard 3).powerset.filter
          Finset.IsLinearHypergraph := by
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact (mem_iff H0).mpr (OMA1024.mem_linearSystems_iff.mpr ⟨h3, hlin⟩)
      have h := Finset.le_sup (f := fun H => n - H.hypergraphIndependenceNumber) hmem
      rw [indep_eq, hH0] at h
      exact h
  unfold Hypergraph.linearIndependenceNumber
  rw [hsup]
  omega

end OMA1024Bridge

theorem OMA.solution : type_of% @Erdos1024.erdos_1024 := by
  have hf : (fun n : ℕ => (Hypergraph.linearIndependenceNumber n : ℝ)) =
      fun n : ℕ => (OMA1024.guaranteedIndependence n : ℝ) := by
    funext n
    rw [OMA1024Bridge.lin_eq]
  have hg : Erdos1024.erdos_1024.answer = OMA1024.resolutionScale := by
    funext n
    rfl
  rw [hf, hg]
  exact OMA1024.erdos_1024
