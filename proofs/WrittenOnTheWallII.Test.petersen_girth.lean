import FormalConjectures.WrittenOnTheWallII.Test

/-!
# The Petersen graph has girth five

Triangles and nondegenerate four-cycles are excluded by finite checks in the
kernel. An explicit five-cycle supplies the matching upper bound.
The original complete proof is by @ashnewmanjones; this version simplifies
its square exclusion and verifies the five-cycle in a single kernel check.
-/

open SimpleGraph

lemma OMA.petersen_no_triangle (a b c : PetersenVertex) :
    petersenGraph.Adj a b → petersenGraph.Adj b c → ¬ petersenGraph.Adj c a := by
  revert a b c; decide +kernel

lemma OMA.petersen_no_square (a b c d : PetersenVertex) :
    petersenGraph.Adj a b → petersenGraph.Adj b c → petersenGraph.Adj c d →
      petersenGraph.Adj d a → b ≠ d → a = c := by
  revert a b c d
  simp only [Subtype.ext_iff]
  decide +kernel

lemma OMA.petersen_five_le_length {a : PetersenVertex} (w : petersenGraph.Walk a a)
    (hw : w.IsCycle) : 5 ≤ w.length := by
  have h3 := hw.three_le_length
  by_contra hlt
  rw [not_le] at hlt
  rcases w with _ | ⟨h1, w⟩
  · simp at h3
  rcases w with _ | ⟨h2, w⟩
  · simp at h3
  rcases w with _ | ⟨h3', w⟩
  · simp at h3
  rcases w with _ | ⟨h4, w⟩
  · exact OMA.petersen_no_triangle _ _ _ h1 h2 h3'
  rcases w with _ | ⟨h5, w⟩
  · have hnd := hw.support_nodup
    simp [Walk.support_cons] at hnd
    have hac := OMA.petersen_no_square _ _ _ _ h1 h2 h3' h4 (by tauto)
    subst hac
    simp at hnd
  · simp at hlt
    omega

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.petersen_girth := by
  let a : PetersenVertex := ⟨{0, 1}, by decide⟩
  let b : PetersenVertex := ⟨{2, 3}, by decide⟩
  let c : PetersenVertex := ⟨{0, 4}, by decide⟩
  let d : PetersenVertex := ⟨{1, 2}, by decide⟩
  let e : PetersenVertex := ⟨{3, 4}, by decide⟩
  let cycle : petersenGraph.Walk a a :=
    .cons (show petersenGraph.Adj a b by decide) <|
    .cons (show petersenGraph.Adj b c by decide) <|
    .cons (show petersenGraph.Adj c d by decide) <|
    .cons (show petersenGraph.Adj d e by decide) <|
    .cons (show petersenGraph.Adj e a by decide) .nil
  have hcycle : cycle.IsCycle := by
    rw [Walk.isCycle_def, Walk.isTrail_def]
    decide +kernel
  have hg : petersenGraph.egirth = 5 := by
    refine le_antisymm (egirth_le_length hcycle) ?_
    rw [le_egirth]
    exact fun a w hw => by exact_mod_cast OMA.petersen_five_le_length w hw
  change petersenGraph.girth = 5
  rw [girth, hg]
  rfl
