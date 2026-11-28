import OMAStatements.S_oeis_a188553
import Mathlib

namespace A188553

open OMA.S_oeis_a188553

private def mark {n : ℕ} (h : Fin (n + 1)) (i : Fin n) : Fin 2 :=
  if i.val < h.val then 1 else 0

private theorem mark_antitone {n : ℕ} (h : Fin (n + 1)) : Antitone (mark h) := by
  intro i j hij
  by_cases hj : j.val < h.val
  · have hi : i.val < h.val := lt_of_le_of_lt hij hj
    simp [mark, hi, hj]
  · simp [mark, hj]

private theorem exists_mark {n : ℕ} (f : Fin n → Fin 2) (hf : Antitone f) :
    ∃ h : Fin (n + 1), ∀ i, f i = mark h i := by
  classical
  by_cases h : ∃ d : ℕ, ∃ i : Fin n, i.val = d ∧ f i = 0
  · obtain ⟨j, hj, hj0⟩ := Nat.find_spec h
    refine ⟨⟨j.val, by omega⟩, fun i => ?_⟩
    by_cases hi : i.val < j.val
    · have hn : f i ≠ 0 := by
        intro e
        have hle := Nat.find_min' h ⟨i, rfl, e⟩
        omega
      have hv : (f i).val ≠ 0 := fun e => hn (Fin.ext e)
      have h1 : f i = 1 := Fin.ext (by
        have hb := (f i).isLt
        change (f i).val = 1
        omega)
      simpa [mark, hi] using h1
    · have hle : f i ≤ f j := hf (show j ≤ i from le_of_not_gt hi)
      rw [hj0] at hle
      have h0 : f i = 0 := Fin.ext (by
        change (f i).val ≤ 0 at hle
        change (f i).val = 0
        omega)
      simpa [mark, hi] using h0
  · refine ⟨⟨n, by omega⟩, fun i => ?_⟩
    have hn : f i ≠ 0 := fun e => h ⟨i.val, i, rfl, e⟩
    have hv : (f i).val ≠ 0 := fun e => hn (Fin.ext e)
    have h1 : f i = 1 := Fin.ext (by
      have hb := (f i).isLt
      change (f i).val = 1
      omega)
    simpa [mark, i.isLt] using h1

private theorem mark_injective {n : ℕ} : Function.Injective (@mark n) := by
  intro u v eqn
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hlt
  · let i : Fin n := ⟨u.val, by have := v.isLt; omega⟩
    have he := congrFun eqn i
    norm_num [mark, i, hlt] at he
  · let i : Fin n := ⟨v.val, by have := u.isLt; omega⟩
    have he := congrFun eqn i
    norm_num [mark, i, hlt] at he

private theorem transition {n : ℕ} (u v : Fin (n + 1)) :
    ((∀ i, mark v i ≤ mark u i) ∧
      ∀ i i' : Fin n, i.val + 1 = i'.val →
        mark v i' ≤ mark u i ∧ mark u i' ≤ mark v i) ↔
      v.val = u.val ∨ v.val + 1 = u.val := by
  constructor
  · rintro ⟨h, h'⟩
    have h₁ : v.val ≤ u.val := by
      by_contra! hbad
      let i : Fin n := ⟨u.val, by have := v.isLt; omega⟩
      have e := h i
      norm_num [mark, i, hbad] at e
    have h₂ : u.val ≤ v.val + 1 := by
      by_contra! hbad
      let i : Fin n := ⟨v.val, by have := u.isLt; omega⟩
      let i' : Fin n := ⟨v.val + 1, by have := u.isLt; omega⟩
      have e := (h' i i' rfl).2
      norm_num [mark, i, i', hbad] at e
    omega
  · intro h
    constructor
    · intro i
      by_cases hv : i.val < v.val
      · have hu : i.val < u.val := by omega
        simp [mark, hv, hu]
      · simp [mark, hv]
    · intro i i' hi
      constructor
      · by_cases hv : i'.val < v.val
        · have hu : i.val < u.val := by omega
          simp [mark, hv, hu]
        · simp [mark, hv]
      · by_cases hu : i'.val < u.val
        · have hv : i.val < v.val := by omega
          simp [mark, hv, hu]
        · simp [mark, hu]

end A188553

open A188553 OMA.S_oeis_a188553 in
theorem OMA.solution : type_of% @OMA.S_oeis_a188553.main := by
  intro n k _ _
  classical
  let g (w : {w : Fin k → Fin (n + 1) // Steps w}) :
      {A : Fin n → Fin k → Fin 2 // Avoids A} :=
    ⟨fun i j => mark (w.val j) i,
      ⟨fun j => mark_antitone (w.val j),
        fun j j' h => (transition (w.val j) (w.val j')).mpr (w.property j j' h)⟩⟩
  have hInj : Function.Injective g := by
    intro u v h
    apply Subtype.ext
    funext j
    apply mark_injective
    funext i
    exact congrFun (congrFun (congrArg Subtype.val h) i) j
  have hSurj : Function.Surjective g := by
    intro A
    choose w hw using fun j => exists_mark (fun i => A.val i j) (A.property.1 j)
    have hs : Steps w := by
      intro j j' h
      apply (transition (w j) (w j')).mp
      simpa only [← hw] using A.property.2 j j' h
    refine ⟨⟨w, hs⟩, Subtype.ext ?_⟩
    funext i j
    exact (hw j i).symm
  exact Nat.card_congr (Equiv.ofBijective g ⟨hInj, hSurj⟩).symm