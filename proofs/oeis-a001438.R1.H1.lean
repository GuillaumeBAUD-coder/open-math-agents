import OMAReductions.R_oeis_a001438_R1

-- Step oeis-a001438.R1.H1: hypothesis H1 of reduction oeis-a001438.R1
-- Credit: @keiichisince1986-bot

namespace OMA.OeisA001438R1H1

open OMA.S_oeis_a001438

private def sqA : Fin 10 → Fin 10 → Fin 10 :=
  ![![0, 7, 8, 9, 4, 5, 6, 1, 2, 3],
    ![1, 2, 7, 8, 9, 6, 0, 3, 4, 5],
    ![2, 3, 4, 7, 8, 9, 1, 5, 6, 0],
    ![3, 4, 5, 6, 7, 8, 9, 0, 1, 2],
    ![9, 5, 6, 0, 1, 7, 8, 2, 3, 4],
    ![8, 9, 0, 1, 2, 3, 7, 4, 5, 6],
    ![7, 8, 9, 2, 3, 4, 5, 6, 0, 1],
    ![6, 1, 3, 5, 0, 2, 4, 7, 8, 9],
    ![5, 0, 2, 4, 6, 1, 3, 8, 9, 7],
    ![4, 6, 1, 3, 5, 0, 2, 9, 7, 8]]

private def sqB : Fin 10 → Fin 10 → Fin 10 :=
  ![![0, 1, 2, 3, 9, 8, 7, 6, 5, 4],
    ![7, 2, 3, 4, 5, 9, 8, 1, 0, 6],
    ![8, 7, 4, 5, 6, 0, 9, 3, 2, 1],
    ![9, 8, 7, 6, 0, 1, 2, 5, 4, 3],
    ![4, 9, 8, 7, 1, 2, 3, 0, 6, 5],
    ![5, 6, 9, 8, 7, 3, 4, 2, 1, 0],
    ![6, 0, 1, 9, 8, 7, 5, 4, 3, 2],
    ![1, 3, 5, 0, 2, 4, 6, 7, 8, 9],
    ![2, 4, 6, 1, 3, 5, 0, 9, 7, 8],
    ![3, 5, 0, 2, 4, 6, 1, 8, 9, 7]]

private def invR : Fin 10 → Fin 10 → Fin 10 :=
  ![![0, 2, 7, 6, 8, 3, 9, 4, 1, 5],
    ![9, 4, 6, 7, 3, 8, 0, 1, 5, 2],
    ![4, 9, 1, 3, 7, 0, 8, 5, 2, 6],
    ![8, 1, 9, 5, 0, 7, 4, 2, 6, 3],
    ![1, 8, 5, 9, 2, 4, 7, 6, 3, 0],
    ![7, 5, 8, 2, 9, 6, 1, 3, 0, 4],
    ![5, 7, 2, 8, 6, 9, 3, 0, 4, 1],
    ![3, 0, 4, 1, 5, 2, 6, 7, 8, 9],
    ![6, 3, 0, 4, 1, 5, 2, 9, 7, 8],
    ![2, 6, 3, 0, 4, 1, 5, 8, 9, 7]]

private def invC : Fin 10 → Fin 10 → Fin 10 :=
  ![![0, 9, 4, 8, 1, 7, 5, 3, 6, 2],
    ![2, 4, 9, 1, 8, 5, 7, 0, 3, 6],
    ![7, 6, 1, 9, 5, 8, 2, 4, 0, 3],
    ![6, 7, 3, 5, 9, 2, 8, 1, 4, 0],
    ![8, 3, 7, 0, 2, 9, 6, 5, 1, 4],
    ![3, 8, 0, 7, 4, 6, 9, 2, 5, 1],
    ![9, 0, 8, 4, 7, 1, 3, 6, 2, 5],
    ![4, 1, 5, 2, 6, 3, 0, 7, 9, 8],
    ![1, 5, 2, 6, 3, 0, 4, 9, 8, 7],
    ![5, 2, 6, 3, 0, 4, 1, 8, 7, 9]]

private lemma row_inj_A : ∀ i x y : Fin 10, sqA i x = sqA i y → x = y := by decide
private lemma col_inj_A : ∀ j x y : Fin 10, sqA x j = sqA y j → x = y := by decide
private lemma row_inj_B : ∀ i x y : Fin 10, sqB i x = sqB i y → x = y := by decide
private lemma col_inj_B : ∀ j x y : Fin 10, sqB x j = sqB y j → x = y := by decide
private lemma inv_r : ∀ i j : Fin 10, invR (sqA i j) (sqB i j) = i := by decide
private lemma inv_c : ∀ i j : Fin 10, invC (sqA i j) (sqB i j) = j := by decide

private lemma isLatin_A : IsLatin sqA :=
  ⟨fun i => (Fintype.bijective_iff_injective_and_card _).mpr ⟨row_inj_A i, rfl⟩,
   fun j => (Fintype.bijective_iff_injective_and_card _).mpr ⟨col_inj_A j, rfl⟩⟩

private lemma isLatin_B : IsLatin sqB :=
  ⟨fun i => (Fintype.bijective_iff_injective_and_card _).mpr ⟨row_inj_B i, rfl⟩,
   fun j => (Fintype.bijective_iff_injective_and_card _).mpr ⟨col_inj_B j, rfl⟩⟩

private lemma orth_AB : Orthogonal sqA sqB := by
  intro p q hpq
  injection hpq with h1 h2
  refine Prod.ext ?_ ?_
  · rw [← inv_r p.1 p.2, ← inv_r q.1 q.2, h1, h2]
  · rw [← inv_c p.1 p.2, ← inv_c q.1 q.2, h1, h2]

private lemma orth_BA : Orthogonal sqB sqA := by
  intro p q hpq
  injection hpq with h1 h2
  refine Prod.ext ?_ ?_
  · rw [← inv_r p.1 p.2, ← inv_r q.1 q.2, h2, h1]
  · rw [← inv_c p.1 p.2, ← inv_c q.1 q.2, h2, h1]

end OMA.OeisA001438R1H1

theorem OMA.solution : OMA.R_oeis_a001438_R1.H1 := by
  refine ⟨![OMA.OeisA001438R1H1.sqA, OMA.OeisA001438R1H1.sqB], ?_, ?_⟩
  · intro a
    fin_cases a
    · exact OMA.OeisA001438R1H1.isLatin_A
    · exact OMA.OeisA001438R1H1.isLatin_B
  · intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact OMA.OeisA001438R1H1.orth_AB
    · exact OMA.OeisA001438R1H1.orth_BA
    · exact absurd rfl hab
