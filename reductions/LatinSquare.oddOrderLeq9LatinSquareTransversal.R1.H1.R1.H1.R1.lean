import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1
import Mathlib

/-! Order-seven Latin squares normalized by the cycles of their second row. -/

namespace OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1_H1_R1

open LatinSquare

private theorem cycleCases (d : Equiv.Perm (Fin 7)) (hd : ∀ j, d j ≠ j) :
    ∃ k : Fin 4, d.cycleType = (![({7} : Multiset ℕ), {5, 2}, {4, 3}, {3, 2, 2}]) k := by
  have su : d.support = Finset.univ :=
    Finset.eq_univ_of_forall (fun j => Equiv.Perm.mem_support.mpr (hd j))
  have w : d.cycleType.sum = 7 := by rw [d.sum_cycleType, su]; simp
  let m := 2 ::ₘ d.cycleType
  have wm : m.sum = 9 := by simp [m, w]
  have hm (z : ℕ) (hz : z ∈ m) : 2 ≤ z := by
    rcases Multiset.mem_cons.mp hz with rfl | hz
    · exact le_rfl
    · exact Equiv.Perm.two_le_of_mem_cycleType hz
  let kinds : Fin 8 → Multiset ℕ :=
    ![{9}, {7, 2}, {6, 3}, {5, 4}, {5, 2, 2}, {4, 3, 2}, {3, 3, 3}, {3, 2, 2, 2}]
  have testKinds : ∀ a b c d : Fin 10, a.val ≠ 1 → b.val ≠ 1 → c.val ≠ 1 → d.val ≠ 1 →
      a.val + b.val + c.val + d.val = 9 →
      ∃ i, (([a.val, b.val, c.val, d.val].filter (· != 0) : List ℕ) : Multiset ℕ) =
        kinds i := by decide +kernel
  obtain ⟨k, h⟩ := OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1.fourSlots m wm hm kinds testKinds
  have inKind : 2 ∈ kinds k := h ▸ Multiset.mem_cons_self _ _
  have he : d.cycleType = (kinds k).erase 2 := by
    simpa [m] using congrArg (fun ys : Multiset ℕ => ys.erase 2) h
  fin_cases k
  · simp [kinds] at inKind
  · exact ⟨0, he⟩
  · simp [kinds] at inKind
  · simp [kinds] at inKind
  · exact ⟨1, he⟩
  · exact ⟨2, he⟩
  · simp [kinds] at inKind
  · exact ⟨3, he⟩

private theorem canonical
    (use : ∀ (k : Fin 4) (L : LatinSquare 7), (∀ j, L.mat 0 j = j) →
      (∀ i, L.mat i 0 = i) →
      (∀ j, L.mat 1 j = (![
        ![1, 2, 3, 4, 5, 6, 0],
    ![1, 2, 3, 4, 0, 6, 5],
    ![1, 2, 3, 0, 5, 6, 4],
    ![1, 2, 0, 4, 3, 6, 5]] : Fin 4 → Fin 7 → Fin 7) k j) →
      ∃ σ, IsTransversal L σ)
    (L : LatinSquare 7) : ∃ σ, IsTransversal L σ := by
  let rs : Fin 4 → Fin 7 → Fin 7 := ![
    ![1, 2, 3, 4, 5, 6, 0],
    ![1, 2, 3, 4, 0, 6, 5],
    ![1, 2, 3, 0, 5, 6, 4],
    ![1, 2, 0, 4, 3, 6, 5]]
  let vs : Fin 4 → Fin 7 → Fin 7 := ![
    ![6, 0, 1, 2, 3, 4, 5],
    ![4, 0, 1, 2, 3, 6, 5],
    ![3, 0, 1, 2, 6, 4, 5],
    ![2, 0, 1, 4, 3, 6, 5]]
  let il : ∀ k j, vs k (rs k j) = j := by decide +kernel
  let ir : ∀ k j, rs k (vs k j) = j := by decide +kernel
  let p (k : Fin 4) : Equiv.Perm (Fin 7) := ⟨rs k, vs k, il k, ir k⟩
  have types : ∀ k, (p k).cycleType =
      (![({7} : Multiset ℕ), {5, 2}, {4, 3}, {3, 2, 2}]) k := by decide +kernel
  have starts : ∀ k, rs k 0 = 1 := by decide +kernel
  let A : Fin 7 ≃ Fin 7 := Equiv.ofBijective (L.mat 0)
    ⟨L.row_injective 0, Finite.surjective_of_injective (L.row_injective 0)⟩
  let f : Fin 7 → Fin 7 := fun j => A.symm (L.mat 1 j)
  have hf : Function.Injective f := A.symm.injective.comp (L.row_injective 1)
  let d : Equiv.Perm (Fin 7) := Equiv.ofBijective f
    ⟨hf, Finite.surjective_of_injective hf⟩
  have hd (j : Fin 7) : d j ≠ j := by
    intro hj
    have hj' : A.symm (L.mat 1 j) = j := hj
    have hh : L.mat 1 j = L.mat 0 j := A.symm_apply_eq.mp hj'
    exact (by decide : (1 : Fin 7) ≠ 0) (L.col_injective j hh)
  obtain ⟨k, typ⟩ := cycleCases d hd
  obtain ⟨e, he⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr (typ.trans (types k).symm))
  let s : Fin 7 ≃ Fin 7 := A.symm.trans e
  let r : Fin 7 ≃ Fin 7 := Equiv.ofBijective (fun i => s (L.mat i (e.symm 0)))
    ⟨s.injective.comp (L.col_injective (e.symm 0)),
      Finite.surjective_of_injective (s.injective.comp (L.col_injective (e.symm 0)))⟩
  let M : LatinSquare 7 := {
    mat := fun i j => s (L.mat (r.symm i) (e.symm j))
    row_injective := fun i => s.injective.comp ((L.row_injective (r.symm i)).comp e.symm.injective)
    col_injective := fun j => s.injective.comp ((L.col_injective (e.symm j)).comp r.symm.injective) }
  have rb (j : Fin 7) : s (L.mat 0 (e.symm j)) = j := by
    change e (A.symm (A (e.symm j))) = j
    rw [A.symm_apply_apply, e.apply_symm_apply]
  have mk (j : Fin 7) : s (L.mat 1 (e.symm j)) = rs k j :=
    DFunLike.congr_fun he j
  have r0 : r 0 = 0 := rb 0
  have r1 : r 1 = 1 := (mk 0).trans (starts k)
  have row0 (j : Fin 7) : M.mat 0 j = j := by
    change s (L.mat (r.symm 0) (e.symm j)) = j
    rw [r.symm_apply_eq.mpr r0.symm]
    exact rb j
  have col0 (i : Fin 7) : M.mat i 0 = i := r.apply_symm_apply i
  have row1 (j : Fin 7) : M.mat 1 j = rs k j := by
    change s (L.mat (r.symm 1) (e.symm j)) = rs k j
    rw [r.symm_apply_eq.mpr r1.symm]
    exact mk j
  obtain ⟨g, cg, sg⟩ := use k M row0 col0 row1
  refine ⟨fun i => e.symm (g (r i)), e.symm.injective.comp (cg.comp r.injective), ?_⟩
  intro i j h
  apply r.injective
  apply sg
  change s (L.mat (r.symm (r i)) (e.symm (g (r i)))) =
    s (L.mat (r.symm (r j)) (e.symm (g (r j))))
  simpa only [r.symm_apply_apply] using congrArg s h

def H1 : Prop :=
  ∀ L : LatinSquare 7, (∀ j, L.mat 0 j = j) → (∀ i, L.mat i 0 = i) →
    (∀ j, L.mat 1 j = (![1, 2, 3, 4, 5, 6, 0] : Fin 7 → Fin 7) j) →
    ∃ σ, IsTransversal L σ

def H2 : Prop :=
  ∀ L : LatinSquare 7, (∀ j, L.mat 0 j = j) → (∀ i, L.mat i 0 = i) →
    (∀ j, L.mat 1 j = (![1, 2, 3, 4, 0, 6, 5] : Fin 7 → Fin 7) j) →
    ∃ σ, IsTransversal L σ

def H3 : Prop :=
  ∀ L : LatinSquare 7, (∀ j, L.mat 0 j = j) → (∀ i, L.mat i 0 = i) →
    (∀ j, L.mat 1 j = (![1, 2, 3, 0, 5, 6, 4] : Fin 7 → Fin 7) j) →
    ∃ σ, IsTransversal L σ

def H4 : Prop :=
  ∀ L : LatinSquare 7, (∀ j, L.mat 0 j = j) → (∀ i, L.mat i 0 = i) →
    (∀ j, L.mat 1 j = (![1, 2, 0, 4, 3, 6, 5] : Fin 7 → Fin 7) j) →
    ∃ σ, IsTransversal L σ

theorem main : H1 → H2 → H3 → H4 → OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1.H1 := by
  intro a b c d L
  apply canonical _ L
  intro k
  fin_cases k
  · exact a
  · exact b
  · exact c
  · exact d

end OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1_H1_R1