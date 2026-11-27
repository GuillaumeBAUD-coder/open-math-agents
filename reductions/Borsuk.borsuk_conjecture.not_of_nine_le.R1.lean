import FormalConjectures.Wikipedia.BorsukConjecture

-- Credit: @marcusbuffett
/-!
Corollary 7.1 of *A nine-dimensional counterexample to Borsuk's covering
assertion* (2026). The translated rank-one projectors have squared radius
3/4 and squared diameter 2. An equilateral set in the extra coordinates
forces one additional covering set per new vertex.
-/
namespace OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1

open Metric Bornology Borsuk Finset
open scoped EuclideanGeometry

/-- The spherical nine-dimensional obstruction, centered at the translated
scalar matrix I/4. -/
def H1 : Prop :=
  ∃ X : Set (EuclideanSpace ℝ (Fin 9)), X.Nontrivial ∧
    (∀ x ∈ X, ‖x‖^2 = 3/4) ∧ ediam X = ENNReal.ofReal (Real.sqrt 2) ∧
    ¬ HasBorsukCover 10 X

/-- Isometrically include the original space and put k equidistant new
points in its orthogonal complement, at diameter distance from the sphere. -/
def H2 : Prop :=
  ∀ k : ℕ, ∃ f : EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin (9+k)),
    ∃ q : Fin k → EuclideanSpace ℝ (Fin (9+k)), Isometry f ∧
    (∀ i j, i ≠ j → dist (q i) (q j) = Real.sqrt 2) ∧
    (∀ x : EuclideanSpace ℝ (Fin 9), ‖x‖^2 = 3/4 → ∀ i, dist (f x) (q i) = Real.sqrt 2)

theorem main : H1 → H2 → type_of% @Borsuk.borsuk_conjecture.not_of_nine_le := by
  classical
  rintro ⟨X,hX,sphere,diamX,obstruction⟩ extension n hn hB
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨f,q,hf,apart,cross⟩ := extension k
  let D := ENNReal.ofReal (Real.sqrt 2)
  let Y := f '' X ∪ Set.range q
  have cross' (x) (hx : x ∈ X) (i) : edist (f x) (q i) = D := by
    rw [edist_dist, cross x (sphere x hx)]
  have apart' (i j) (h : i ≠ j) : edist (q i) (q j) = D := by
    rw [edist_dist, apart i j h]
  have upper : ediam Y ≤ D := by
    apply ediam_le
    rintro _ (⟨x,hx,rfl⟩ | ⟨i,rfl⟩) _ (⟨y,hy,rfl⟩ | ⟨j,rfl⟩)
    · rw [hf.edist_eq]
      exact (edist_le_ediam_of_mem hx hy).trans diamX.le
    · exact (cross' x hx j).le
    · rw [edist_comm]; exact (cross' y hy i).le
    · by_cases h : i = j
      · simp [h]
      · exact (apart' i j h).le
  have hbdd : IsBounded Y := isBounded_iff_ediam_ne_top.mpr
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top upper)
  have hnt : Y.Nontrivial := (hX.image hf.injective).mono Set.subset_union_left
  obtain ⟨U,cover,small⟩ := hB Y hbdd hnt
  have hsmall (j) : ediam (U j) < D := (small j).trans_le upper
  have chosen (i : Fin k) : ∃ j, q i ∈ U j :=
    Set.mem_iUnion.mp (cover (Or.inr ⟨i,rfl⟩))
  choose color memColor using chosen
  have inj : Function.Injective color := by
    intro i j hij
    by_contra h
    have both : q i ∈ U (color j) := hij ▸ memColor i
    exact (hsmall _).not_ge ((apart' i j h) ▸ edist_le_ediam_of_mem both (memColor j))
  let L := (univ : Finset (Fin (9+k+1))) \ univ.image color
  have size : L.card = 10 := by
    dsimp [L]
    rw [card_sdiff_of_subset (subset_univ _), card_image_of_injective _ inj]
    simp; omega
  let e := Fintype.equivFinOfCardEq (show Fintype.card L = 10 by simpa using size)
  apply obstruction
  refine ⟨fun i => f ⁻¹' U (e.symm i).val, ?_, ?_⟩
  · intro x hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (cover (Or.inl ⟨x,hx,rfl⟩))
    have hjL : j ∈ L := by
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      rintro hj'
      obtain ⟨i,_,rfl⟩ := mem_image.mp hj'
      exact (hsmall _).not_ge ((cross' x hx i) ▸ edist_le_ediam_of_mem hj (memColor i))
    exact Set.mem_iUnion.mpr ⟨e ⟨j,hjL⟩, by simpa using hj⟩
  · intro i
    rw [diamX, ← hf.ediam_image]
    exact (ediam_mono (Set.image_preimage_subset f _)).trans_lt (hsmall _)

end OMA.R_Borsuk_borsuk_conjecture_not_of_nine_le_R1
