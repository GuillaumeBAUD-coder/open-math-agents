import FormalConjectures.Wikipedia.UnionClosed

-- Reduction UnionClosed.union_closed.R1 of the union-closed sets conjecture (Frankl)
-- Credit: @marcusbuffett

/-!
# The union-closed sets conjecture: families with a small set, and the open rest

The conjecture says that a finite union-closed family other than `{∅}` has an element lying in at
least half of its members. `main` first transports the family to a ground set `Fin m` (only the
finitely many elements that occur matter), so the hypotheses are stated there. Two classical
cases (Sarvate and Renaud, On the union-closed sets conjecture, Ars Combin. 27 (1989)) are
separated from the rest.

* `H1`: if the family contains a singleton `{x}`, then `x` lies in at least half of the members
  (adding `x` maps the members without `x` injectively to the members with `x`).
* `H2`: if the family contains a two-element set `{x, y}`, then `x` or `y` lies in at least half
  of the members (adding both maps the members with neither injectively to the members with both).
* `H3`: families with no member of size one or two. This is the open conjecture and stays open.
-/

namespace OMA.R_UnionClosed_union_closed_R1

/-- A union-closed family with a singleton member. -/
def H1 : Prop :=
  ∀ (m : ℕ) (A : Finset (Finset (Fin m))) (x : Fin m),
    UnionClosed.IsUnionClosed A → {x} ∈ A →
    (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => x ∈ X)).card

/-- A union-closed family with a two-element member. -/
def H2 : Prop :=
  ∀ (m : ℕ) (A : Finset (Finset (Fin m))) (x y : Fin m), x ≠ y →
    UnionClosed.IsUnionClosed A → {x, y} ∈ A →
    (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => x ∈ X)).card ∨
      (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => y ∈ X)).card

/-- The open part: no member has one or two elements. -/
def H3 : Prop :=
  ∀ (m : ℕ) (A : Finset (Finset (Fin m))), A ≠ {∅} →
    UnionClosed.IsUnionClosed A → (∀ X ∈ A, X.card ≠ 1 ∧ X.card ≠ 2) →
    (∃ X ∈ A, X ≠ ∅) →
    ∃ i : Fin m, (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => i ∈ X)).card

lemma fin_case (h1 : H1) (h2 : H2) (h3 : H3) (m : ℕ) (A : Finset (Finset (Fin m)))
    (hne : A ≠ {∅}) (huc : UnionClosed.IsUnionClosed A) (hex : ∃ X ∈ A, X ≠ ∅) :
    ∃ i : Fin m, (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => i ∈ X)).card := by
  by_cases hsmall : ∃ X ∈ A, X.card = 1 ∨ X.card = 2
  · obtain ⟨X, hX, hc | hc⟩ := hsmall
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc
      exact ⟨x, h1 m A x huc hX⟩
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
      rcases h2 m A x y hxy huc hX with h | h
      · exact ⟨x, h⟩
      · exact ⟨y, h⟩
  · have hno : ∀ X ∈ A, X.card ≠ 1 ∧ X.card ≠ 2 := by
      intro X hX
      constructor
      · intro h
        exact hsmall ⟨X, hX, Or.inl h⟩
      · intro h
        exact hsmall ⟨X, hX, Or.inr h⟩
    exact h3 m A hne huc hno hex

theorem main : H1 → H2 → H3 → type_of% @UnionClosed.union_closed := by
  intro h1 h2 h3 n _ A _ hne huc
  by_cases hall : ∀ X ∈ A, X = ∅
  · have hA : A = ∅ := by
      by_contra hA0
      apply hne
      obtain ⟨X, hX⟩ := Finset.nonempty_iff_ne_empty.mpr hA0
      ext Y
      rw [Finset.mem_singleton]
      constructor
      · exact hall Y
      · rintro rfl
        rw [← hall X hX]
        exact hX
    subst hA
    obtain ⟨i⟩ := ‹Nonempty n›
    exact ⟨i, by simp⟩
  push Not at hall
  obtain ⟨X0, hX0, hX0ne⟩ := hall
  have hsub : ∀ X ∈ A, X ⊆ A.sup id := fun X hX => Finset.le_sup (f := id) hX
  obtain ⟨ι, hι⟩ : ∃ ι : Fin (A.sup id).card → n, ∀ a ∈ A.sup id, ∃ i, ι i = a :=
    ⟨fun i => ((A.sup id).equivFin.symm i).1, fun a ha => ⟨(A.sup id).equivFin ⟨a, ha⟩, by simp⟩⟩
  have hφ_union : ∀ X Y : Finset n,
      (Finset.univ.filter (fun i => ι i ∈ X ∪ Y)) =
        (Finset.univ.filter (fun i => ι i ∈ X)) ∪ (Finset.univ.filter (fun i => ι i ∈ Y)) := by
    intro X Y
    ext i
    simp
  have hφ_inj : Set.InjOn (fun X : Finset n => Finset.univ.filter (fun i => ι i ∈ X))
      (A : Set (Finset n)) := by
    intro X hX Y hY h
    rw [Finset.mem_coe] at hX hY
    have h' : ∀ i, ι i ∈ X ↔ ι i ∈ Y := by
      intro i
      have h2 := Finset.ext_iff.mp h i
      simpa using h2
    ext a
    constructor
    · intro ha
      obtain ⟨i, rfl⟩ := hι a (hsub X hX ha)
      exact (h' i).mp ha
    · intro ha
      obtain ⟨i, rfl⟩ := hι a (hsub Y hY ha)
      exact (h' i).mpr ha
  have huc' : UnionClosed.IsUnionClosed
      (A.image (fun X : Finset n => Finset.univ.filter (fun i => ι i ∈ X))) := by
    intro X' hX' Y' hY'
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hX'
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hY'
    rw [← hφ_union]
    exact Finset.mem_image_of_mem _ (huc X hX Y hY)
  have hcard : (A.image (fun X : Finset n => Finset.univ.filter (fun i => ι i ∈ X))).card = A.card :=
    Finset.card_image_of_injOn hφ_inj
  have hfilt : ∀ i, ((A.image (fun X : Finset n => Finset.univ.filter (fun i => ι i ∈ X))).filter
      (fun X' => i ∈ X')).card = (A.filter (fun X => ι i ∈ X)).card := by
    intro i
    rw [Finset.filter_image]
    have hinj2 : Set.InjOn (fun X : Finset n => Finset.univ.filter (fun i => ι i ∈ X))
        ((A.filter (fun X => i ∈ Finset.univ.filter (fun i => ι i ∈ X)) : Finset (Finset n)) :
          Set (Finset n)) := by
      apply hφ_inj.mono
      intro X hX
      rw [Finset.mem_coe] at hX ⊢
      exact (Finset.mem_filter.mp hX).1
    rw [Finset.card_image_of_injOn hinj2]
    congr 1
    ext X
    simp
  have hX0' : Finset.univ.filter (fun i => ι i ∈ X0) ≠ (∅ : Finset (Fin (A.sup id).card)) := by
    obtain ⟨a, ha⟩ := hX0ne
    obtain ⟨i, rfl⟩ := hι a (hsub X0 hX0 ha)
    intro h
    have hi : i ∈ Finset.univ.filter (fun i => ι i ∈ X0) := by simp [ha]
    rw [h] at hi
    exact absurd hi (Finset.notMem_empty i)
  have hne' : (A.image (fun X : Finset n => Finset.univ.filter (fun i => ι i ∈ X))) ≠ {∅} := by
    intro h
    have hm : Finset.univ.filter (fun i => ι i ∈ X0) ∈
        (A.image (fun X : Finset n => Finset.univ.filter (fun i => ι i ∈ X))) :=
      Finset.mem_image_of_mem _ hX0
    rw [h, Finset.mem_singleton] at hm
    exact hX0' hm
  obtain ⟨i, hi⟩ := fin_case h1 h2 h3 _ _ hne' huc'
    ⟨_, Finset.mem_image_of_mem _ hX0, hX0'⟩
  refine ⟨ι i, ?_⟩
  rw [hcard, hfilt] at hi
  exact hi

end OMA.R_UnionClosed_union_closed_R1
