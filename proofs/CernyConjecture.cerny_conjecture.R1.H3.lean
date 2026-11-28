import OMAReductions.R_CernyConjecture_cerny_conjecture_R1

-- Step CernyConjecture.cerny_conjecture.R1.H3: a letter of rank at most two.
-- A shortest word merging the two image states visits pairwise distinct unordered
-- pairs of distinct states, so it has length at most C(n,2).

namespace OMA.CernyR1H3

theorem short_merge {α σ : Type} [Fintype σ] (M : DFA α σ) (x y : σ)
    (can : ∃ w : List α, M.evalFrom x w = M.evalFrom y w) :
    ∃ w : List α, M.evalFrom x w = M.evalFrom y w ∧ w.length ≤ (Fintype.card σ).choose 2 := by
  classical
  let P (k : Nat) := ∃ w : List α, w.length = k ∧ M.evalFrom x w = M.evalFrom y w
  have ex : ∃ k, P k := by
    obtain ⟨w, hw⟩ := can
    exact ⟨_, w, rfl, hw⟩
  obtain ⟨w, hw, ends⟩ := Nat.find_spec ex
  have minimal (v : List α) (hv : M.evalFrom x v = M.evalFrom y v) : w.length ≤ v.length := by
    rw [hw]
    exact Nat.find_min' ex ⟨v, rfl, hv⟩
  let f (i : Nat) : Sym2 σ := Sym2.mk (M.evalFrom x (w.take i)) (M.evalFrom y (w.take i))
  have ne (i : Nat) (hi : i < w.length) :
      M.evalFrom x (w.take i) ≠ M.evalFrom y (w.take i) := by
    intro hm
    have hl := minimal _ hm
    simp only [List.length_take, Nat.min_eq_left hi.le] at hl
    omega
  have distinct (i j : Nat) (hij : i < j) (hj : j < w.length) (heq : f i = f j) : False := by
    have short : M.evalFrom x (w.take i ++ w.drop j) = M.evalFrom y (w.take i ++ w.drop j) := by
      rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append]
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, ← DFA.evalFrom_of_append, ← DFA.evalFrom_of_append, List.take_append_drop]
        exact ends
      · rw [h1, h2, ← DFA.evalFrom_of_append, ← DFA.evalFrom_of_append, List.take_append_drop]
        exact ends.symm
    have hl := minimal _ short
    simp only [List.length_append, List.length_take, Nat.min_eq_left (hij.trans hj).le,
      List.length_drop] at hl
    omega
  have count := Finset.card_le_card_of_injOn (s := Finset.range w.length)
    (t := (Finset.univ : Finset σ).offDiag.image Sym2.mk.uncurry) f
    (fun i hi => Finset.mem_image.mpr ⟨(M.evalFrom x (w.take i), M.evalFrom y (w.take i)),
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
        ne i (Finset.mem_range.mp hi)⟩, rfl⟩)
    (by
      intro i hi j hj heq
      rcases lt_trichotomy i j with h | h | h
      · exact (distinct i j h (Finset.mem_range.mp hj) heq).elim
      · exact h
      · exact (distinct j i h (Finset.mem_range.mp hi) heq.symm).elim)
  rw [Sym2.card_image_offDiag, Finset.card_range, Finset.card_univ] at count
  exact ⟨w, ends, count⟩

theorem arith (m : Nat) (hm : 2 ≤ m) : 1 + (m + 1).choose 2 ≤ m ^ 2 := by
  rw [Nat.choose_two_right]
  have h := Nat.div_mul_le_self ((m + 1) * (m + 1 - 1)) 2
  simp only [Nat.add_sub_cancel] at h ⊢
  nlinarith

end OMA.CernyR1H3

theorem OMA.solution : OMA.R_CernyConjecture_cerny_conjecture_R1.H3 := by
  intro α σ inst M sync hrank
  obtain ⟨a, x, y, ha⟩ := hrank
  classical
  obtain ⟨r, z, reset⟩ := sync
  obtain ⟨w, hw, hlen⟩ := OMA.CernyR1H3.short_merge M x y ⟨r, by rw [reset, reset]⟩
  have hsync : M.IsSynchronizingWord (a :: w) := by
    refine ⟨M.evalFrom x w, fun q => ?_⟩
    rw [DFA.evalFrom_cons]
    rcases ha q with h | h
    · rw [h]
    · rw [h]; exact hw.symm
  rcases Nat.lt_or_ge (Fintype.card σ) 3 with h3 | h3
  · rcases Nat.lt_or_ge (Fintype.card σ) 2 with h2 | h2
    · have sub := Fintype.card_le_one_iff.mp (Nat.lt_succ_iff.mp h2)
      exact ⟨[], ⟨z, fun q => sub _ _⟩, Nat.zero_le _⟩
    · have hc : Fintype.card σ = 2 := by omega
      by_cases hxy : x = y
      · refine ⟨[a], ⟨x, fun q => ?_⟩, by rw [hc]; simp⟩
        show M.step q a = x
        rcases ha q with h | h
        · exact h
        · exact h.trans hxy.symm
      · have huniv : ({x, y} : Finset σ) = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [Finset.card_pair hxy, hc])
        refine ⟨w, ⟨M.evalFrom x w, fun q => ?_⟩, by rw [hc] at hlen ⊢; simpa using hlen⟩
        have hq : q ∈ ({x, y} : Finset σ) := by rw [huniv]; exact Finset.mem_univ q
        rcases Finset.mem_insert.mp hq with h | h
        · rw [h]
        · rw [Finset.mem_singleton.mp h]; exact hw.symm
  · refine ⟨a :: w, hsync, ?_⟩
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card σ = m + 1 := ⟨Fintype.card σ - 1, by omega⟩
    rw [hm] at hlen ⊢
    have := OMA.CernyR1H3.arith m (by omega)
    simp only [List.length_cons, Nat.add_sub_cancel]
    omega
