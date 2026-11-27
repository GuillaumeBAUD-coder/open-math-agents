import OMAStatements.S_arxiv_2101_07103

/-!
Disproof of Estrada and Mugnolo (arXiv:2101.07103, JMAA 507 (2022) 125728,
Conjecture 4.13) on the 10-vertex barbell graph K4 - P3 - K4 (vertices 0..3
form K4, vertices 6..9 form K4, bridge path 3-4-5-6).

Exact rational Moore-Penrose Kirchhoff indices on K4 - P3 - K4:
- attracting: 914522 / 6695 (approx 136.598)
- ordinary:   97
- repelling:  728029 / 8580 (approx 84.852)
giving a simultaneous double reversal of both conjectured inequalities.
-/

namespace OMA.S_arxiv_2101_07103.Disproof

open OMA.S_arxiv_2101_07103

private def adj10 (i j : Fin 10) : Bool :=
  (i != j) && (
    (i.val < 4 && j.val < 4) ||
    (6 ≤ i.val && 6 ≤ j.val) ||
    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3) ||
    (i.val == 4 && j.val == 5) || (i.val == 5 && j.val == 4) ||
    (i.val == 5 && j.val == 6) || (i.val == 6 && j.val == 5))

private def G10 : SimpleGraph (Fin 10) where
  Adj i j := adj10 i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

private instance instDecAdj10 : DecidableRel G10.Adj :=
  fun i j => inferInstanceAs (Decidable (adj10 i j = true))

private lemma G10_connected : G10.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  have r03 : G10.Reachable 0 3 := SimpleGraph.Adj.reachable (by decide)
  have r04 : G10.Reachable 0 4 := r03.trans (SimpleGraph.Adj.reachable (by decide))
  have r05 : G10.Reachable 0 5 := r04.trans (SimpleGraph.Adj.reachable (by decide))
  have r06 : G10.Reachable 0 6 := r05.trans (SimpleGraph.Adj.reachable (by decide))
  fin_cases v
  · exact SimpleGraph.Reachable.refl 0
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact r03
  · exact r04
  · exact r05
  · exact r06
  · exact r06.trans (SimpleGraph.Adj.reachable (by decide))
  · exact r06.trans (SimpleGraph.Adj.reachable (by decide))
  · exact r06.trans (SimpleGraph.Adj.reachable (by decide))

private def deg10 (i : Fin 10) : ℕ :=
  match i.val with
  | 0 => 3 | 1 => 3 | 2 => 3 | 3 => 4 | 4 => 2
  | 5 => 2 | 6 => 4 | 7 => 3 | 8 => 3 | _ => 3

private lemma G10_degree_eq (i : Fin 10) {instF : Fintype (G10.neighborSet i)} :
    @SimpleGraph.degree _ G10 i instF = deg10 i := by
  have h : @SimpleGraph.degree _ G10 i instF =
      (Finset.univ.filter (fun j => adj10 i j = true)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext j
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [h]
  fin_cases i <;> decide

private def sum10Z (f : Fin 10 → ℤ) : ℤ :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9

private lemma sum_fin10_eq_sum10Z (f : Fin 10 → ℤ) :
    (∑ k : Fin 10, f k) = sum10Z f := by
  simp only [sum10Z, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + f 9)))))))) = _
  ring

private lemma sum_fin10_cast_real (f : Fin 10 → ℤ) :
    (∑ k : Fin 10, (f k : ℝ)) = (sum10Z f : ℝ) := by
  rw [← Int.cast_sum, sum_fin10_eq_sum10Z]

private def rowOf (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℤ) (j : Fin 10) : ℤ :=
  match j.val with
  | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4
  | 5 => a5 | 6 => a6 | 7 => a7 | 8 => a8 | _ => a9

private def matOf (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : Fin 10 → ℤ) (i : Fin 10) : Fin 10 → ℤ :=
  match i.val with
  | 0 => r0 | 1 => r1 | 2 => r2 | 3 => r3 | 4 => r4
  | 5 => r5 | 6 => r6 | 7 => r7 | 8 => r8 | _ => r9

private def cZ (b : Bias) (i j : Fin 10) : ℤ :=
  if adj10 i j then
    match b with
    | .repelling => (deg10 i : ℤ) * (12 / (deg10 j : ℤ))
    | .ordinary => 12
    | .attracting => (deg10 j : ℤ) * (12 / (deg10 i : ℤ))
  else 0

private def lapZ (b : Bias) (i j : Fin 10) : ℤ :=
  if i = j then sum10Z (cZ b i) else -cZ b i j

private lemma lap_eq_lapZ (b : Bias) (i j : Fin 10) :
    ((lap G10 b).map (Rat.castHom ℝ)) i j = (lapZ b i j : ℝ) / 12 := by
  have hdeg12 : ∀ k : Fin 10,
      ((12 / (deg10 k : ℤ) : ℤ) : ℚ) * (deg10 k : ℚ) = 12 ∧ (deg10 k : ℚ) ≠ 0 := by
    intro k; fin_cases k <;> norm_num [deg10]
  have hterm : ∀ (x y : Fin 10) {d : Decidable (G10.Adj x y)}
      {fx : Fintype (G10.neighborSet x)} {fy : Fintype (G10.neighborSet y)},
      @ite ℚ (G10.Adj x y) d
        (match b with
        | .repelling => (@SimpleGraph.degree _ G10 x fx : ℚ) / @SimpleGraph.degree _ G10 y fy
        | .ordinary => 1
        | .attracting => (@SimpleGraph.degree _ G10 y fy : ℚ) / @SimpleGraph.degree _ G10 x fx)
        0 = (cZ b x y : ℚ) / 12 := by
    intro x y d fx fy
    rw [G10_degree_eq x, G10_degree_eq y]
    unfold cZ
    by_cases hxy : adj10 x y = true
    · have hG : G10.Adj x y := hxy
      rw [if_pos hG, if_pos hxy]
      cases b with
      | repelling =>
        rcases hdeg12 y with ⟨h1, h2⟩
        push_cast
        field_simp [h2]
        linear_combination -(deg10 x : ℚ) * h1
      | ordinary => norm_num
      | attracting =>
        rcases hdeg12 x with ⟨h1, h2⟩
        push_cast
        field_simp [h2]
        linear_combination -(deg10 y : ℚ) * h1
    · have hG : ¬ G10.Adj x y := hxy
      rw [if_neg hG, if_neg hxy]
      norm_num
  have hQ : lap G10 b i j = (lapZ b i j : ℚ) / 12 := by
    unfold lap lapZ
    dsimp only
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      calc (∑ k : Fin 10, _) = ∑ k : Fin 10, (cZ b i k : ℚ) / 12 := by
              apply Finset.sum_congr rfl; intro k _; exact hterm i k
        _ = (sum10Z (cZ b i) : ℚ) / 12 := by
              rw [← Finset.sum_div, ← Int.cast_sum, sum_fin10_eq_sum10Z]
    · rw [if_neg hij, if_neg hij]
      calc -_ = -((cZ b i j : ℚ) / 12) := congrArg Neg.neg (hterm i j)
        _ = ((-cZ b i j : ℤ) : ℚ) / 12 := by push_cast; ring
  rw [Matrix.map_apply, Rat.coe_castHom, hQ]
  push_cast; rfl

private def mulZ (A B : Fin 10 → Fin 10 → ℤ) (i j : Fin 10) : ℤ :=
  sum10Z fun k => A i k * B k j

private def checkPenroseZ (L P : Fin 10 → Fin 10 → ℤ) (S : ℤ) : Bool :=
  let LP := mulZ L P
  let PL := mulZ P L
  let LPL := mulZ LP L
  let PLP := mulZ PL P
  (List.finRange 10).all fun i =>
    (List.finRange 10).all fun j =>
      decide (LPL i j = S * L i j) &&
      decide (PLP i j = S * P i j) &&
      decide (LP j i = LP i j) &&
      decide (PL j i = PL i j)

private noncomputable def matDiv (A : Fin 10 → Fin 10 → ℤ) (a : ℝ) : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.of fun i j => (A i j : ℝ) / a

private lemma mat_mul_div (A B : Fin 10 → Fin 10 → ℤ) (a b : ℝ) :
    matDiv A a * matDiv B b = matDiv (mulZ A B) (a * b) := by
  ext i j
  simp only [Matrix.mul_apply, matDiv, Matrix.of_apply, mulZ, ← sum_fin10_cast_real]
  simp_rw [div_mul_div_comm, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

private lemma penrose_of_checkZ (L P : Fin 10 → Fin 10 → ℤ) (cL cP : ℤ)
    (hcL : (cL : ℝ) ≠ 0) (hcP : (cP : ℝ) ≠ 0)
    (hchk : checkPenroseZ L P (cL * cP) = true) :
    Penrose (matDiv L (cL : ℝ)) (matDiv P (cP : ℝ)) := by
  have hall : ∀ i j : Fin 10,
      mulZ (mulZ L P) L i j = cL * cP * L i j ∧
      mulZ (mulZ P L) P i j = cL * cP * P i j ∧
      mulZ L P j i = mulZ L P i j ∧
      mulZ P L j i = mulZ P L i j := by
    intro i j
    unfold checkPenroseZ at hchk
    have hi := List.all_eq_true.mp hchk i (List.mem_finRange i)
    have hj := List.all_eq_true.mp hi j (List.mem_finRange j)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    exact ⟨hj.1.1.1, hj.1.1.2, hj.1.2, hj.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mat_mul_div, mat_mul_div]
    ext i j
    simp only [matDiv, Matrix.of_apply]
    have h1 := (hall i j).1
    have h1R : (mulZ (mulZ L P) L i j : ℝ) = (cL : ℝ) * (cP : ℝ) * (L i j : ℝ) := by
      exact_mod_cast h1
    rw [h1R]
    field_simp [hcL, hcP]
  · rw [mat_mul_div, mat_mul_div]
    ext i j
    simp only [matDiv, Matrix.of_apply]
    have h2 := (hall i j).2.1
    have h2R : (mulZ (mulZ P L) P i j : ℝ) = (cL : ℝ) * (cP : ℝ) * (P i j : ℝ) := by
      exact_mod_cast h2
    rw [h2R]
    field_simp [hcL, hcP]
  · rw [mat_mul_div]
    ext i j
    simp only [Matrix.transpose_apply, matDiv, Matrix.of_apply]
    rw [(hall i j).2.2.1]
  · rw [mat_mul_div]
    ext i j
    simp only [Matrix.transpose_apply, matDiv, Matrix.of_apply]
    rw [(hall i j).2.2.2]

private def idxNumZ (P : Fin 10 → Fin 10 → ℤ) : ℤ :=
  sum10Z fun i => sum10Z fun j => P i i + P j j - P i j - P j i

private lemma index_div (P : Fin 10 → Fin 10 → ℤ) (cP : ℝ) :
    index (matDiv P cP) = (idxNumZ P : ℝ) / (2 * cP) := by
  unfold index idxNumZ matDiv
  simp only [Matrix.of_apply]
  have hinner : ∀ i : Fin 10,
      (∑ j : Fin 10, ((P i i : ℝ) / cP + (P j j : ℝ) / cP - (P i j : ℝ) / cP - (P j i : ℝ) / cP)) =
      ((sum10Z fun j => P i i + P j j - P i j - P j i : ℤ) : ℝ) / cP := by
    intro i
    rw [← sum_fin10_cast_real, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  simp_rw [hinner, ← Finset.sum_div, ← sum_fin10_cast_real]
  ring

private def PZ_att : Fin 10 → Fin 10 → ℤ := matOf
  (rowOf 767916 644316 644316 1052064 102336 (-165464) (-1090336) (-653484) (-653484) (-653484))
  (rowOf 644316 767916 644316 1052064 102336 (-165464) (-1090336) (-653484) (-653484) (-653484))
  (rowOf 644316 644316 767916 1052064 102336 (-165464) (-1090336) (-653484) (-653484) (-653484))
  (rowOf 583206 583206 583206 1108224 116376 (-151424) (-1034176) (-621894) (-621894) (-621894))
  (rowOf 272571 272571 272571 555984 246116 (-21684) (-515216) (-329979) (-329979) (-329979))
  (rowOf (-329979) (-329979) (-329979) (-515216) (-21684) 246116 555984 272571 272571 272571)
  (rowOf (-621894) (-621894) (-621894) (-1034176) (-151424) 116376 1108224 583206 583206 583206)
  (rowOf (-653484) (-653484) (-653484) (-1090336) (-165464) 102336 1052064 767916 644316 644316)
  (rowOf (-653484) (-653484) (-653484) (-1090336) (-165464) 102336 1052064 644316 767916 644316)
  (rowOf (-653484) (-653484) (-653484) (-1090336) (-165464) 102336 1052064 644316 644316 767916)

private def PZ_ord : Fin 10 → Fin 10 → ℤ := matOf
  (rowOf 113 88 88 73 13 (-37) (-77) (-87) (-87) (-87))
  (rowOf 88 113 88 73 13 (-37) (-77) (-87) (-87) (-87))
  (rowOf 88 88 113 73 13 (-37) (-77) (-87) (-87) (-87))
  (rowOf 73 73 73 83 23 (-27) (-67) (-77) (-77) (-77))
  (rowOf 13 13 13 23 63 13 (-27) (-37) (-37) (-37))
  (rowOf (-37) (-37) (-37) (-27) 13 63 23 13 13 13)
  (rowOf (-77) (-77) (-77) (-67) (-27) 23 83 73 73 73)
  (rowOf (-87) (-87) (-87) (-77) (-37) 13 73 113 88 88)
  (rowOf (-87) (-87) (-87) (-77) (-37) 13 73 88 113 88)
  (rowOf (-87) (-87) (-87) (-77) (-37) 13 73 88 88 113)

private def PZ_rep : Fin 10 → Fin 10 → ℤ := matOf
  (rowOf 548944 411664 411664 167211 51084 (-206316) (-154539) (-343376) (-343376) (-343376))
  (rowOf 411664 548944 411664 167211 51084 (-206316) (-154539) (-343376) (-343376) (-343376))
  (rowOf 411664 411664 548944 167211 51084 (-206316) (-154539) (-343376) (-343376) (-343376))
  (rowOf 269584 269584 269584 190251 143244 (-114156) (-131499) (-302416) (-302416) (-302416))
  (rowOf (-97456) (-97456) (-97456) (-16209) 347004 89604 (-80559) (-211856) (-211856) (-211856))
  (rowOf (-211856) (-211856) (-211856) (-80559) 89604 347004 (-16209) (-97456) (-97456) (-97456))
  (rowOf (-302416) (-302416) (-302416) (-131499) (-114156) 143244 190251 269584 269584 269584)
  (rowOf (-343376) (-343376) (-343376) (-154539) (-206316) 51084 167211 548944 411664 411664)
  (rowOf (-343376) (-343376) (-343376) (-154539) (-206316) 51084 167211 411664 548944 411664)
  (rowOf (-343376) (-343376) (-343376) (-154539) (-206316) 51084 167211 411664 411664 548944)

private def denOf : Bias → ℤ
  | .attracting => 535600
  | .ordinary => 100
  | .repelling => 514800

private def PZOf : Bias → Fin 10 → Fin 10 → ℤ
  | .attracting => PZ_att
  | .ordinary => PZ_ord
  | .repelling => PZ_rep

private noncomputable def P10 (b : Bias) : Matrix (Fin 10) (Fin 10) ℝ :=
  matDiv (PZOf b) (denOf b : ℝ)

private lemma chk_att : checkPenroseZ (lapZ .attracting) PZ_att (12 * 535600) = true := by
  decide

private lemma chk_ord : checkPenroseZ (lapZ .ordinary) PZ_ord (12 * 100) = true := by
  decide

private lemma chk_rep : checkPenroseZ (lapZ .repelling) PZ_rep (12 * 514800) = true := by
  decide

private lemma idx_att_val : idxNumZ PZ_att = 146323520 := by decide

private lemma idx_ord_val : idxNumZ PZ_ord = 19400 := by decide

private lemma P10_penrose (b : Bias) :
    Penrose ((lap G10 b).map (Rat.castHom ℝ)) (P10 b) := by
  have hL : (lap G10 b).map (Rat.castHom ℝ) = matDiv (lapZ b) ((12 : ℤ) : ℝ) := by
    ext i j
    simpa [matDiv] using lap_eq_lapZ b i j
  rw [hL]
  unfold P10 PZOf denOf
  cases b with
  | attracting =>
    exact penrose_of_checkZ (lapZ .attracting) PZ_att 12 535600
      (by norm_num) (by norm_num) chk_att
  | ordinary =>
    exact penrose_of_checkZ (lapZ .ordinary) PZ_ord 12 100
      (by norm_num) (by norm_num) chk_ord
  | repelling =>
    exact penrose_of_checkZ (lapZ .repelling) PZ_rep 12 514800
      (by norm_num) (by norm_num) chk_rep

private lemma disproof_aux :
    ¬ (∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Connected →
      ∀ P : Bias → Matrix (Fin n) (Fin n) ℝ,
      (∀ b, Penrose ((lap G b).map (Rat.castHom ℝ)) (P b)) →
      index (P .attracting) ≤ index (P .ordinary) ∧
      index (P .ordinary) ≤ index (P .repelling) ∧
      ((index (P .attracting) = index (P .ordinary) ∧
        index (P .ordinary) = index (P .repelling)) ↔ ∀ i j, G.degree i = G.degree j)) := by
  intro hmain
  have h := (hmain G10 G10_connected P10 P10_penrose).1
  have hatt : index (P10 .attracting) = (146323520 : ℝ) / (2 * 535600) := by
    unfold P10 PZOf denOf
    rw [index_div, idx_att_val]
    norm_num
  have hord : index (P10 .ordinary) = (19400 : ℝ) / (2 * 100) := by
    unfold P10 PZOf denOf
    rw [index_div, idx_ord_val]
    norm_num
  rw [hatt, hord] at h
  norm_num at h

end OMA.S_arxiv_2101_07103.Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2101_07103.main) :=
  OMA.S_arxiv_2101_07103.Disproof.disproof_aux
