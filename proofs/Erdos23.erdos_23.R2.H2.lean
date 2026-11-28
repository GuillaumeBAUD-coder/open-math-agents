import OMAReductions.R_Erdos23_erdos_23_R2

-- Step Erdos23.erdos_23.R2.H2: hypothesis H2 of reduction Erdos23.erdos_23.R2.
-- Written with Claude Code (AI-assisted).
-- Averaging over all vertex subsets S: for an edge uv, toggling u in S swaps the subsets in
-- which uv is monochromatic with those in which it is cut, so summed over all S the number of
-- monochromatic edges equals the number of cut edges. Hence some S has at most half of the
-- edges monochromatic.

open SimpleGraph Finset

theorem OMA.solution : OMA.R_Erdos23_erdos_23_R2.H2 := by
  intro V _ G
  classical
  let P : Finset V → Sym2 V → Prop := fun S e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)
  have hedge : ∀ e ∈ G.edgeFinset, (∑ S : Finset V, if P S e then 1 else 0) =
      ∑ S : Finset V, if ¬ P S e then 1 else 0 := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
    have huv : u ≠ v := G.ne_of_adj (by simpa using he)
    apply Finset.sum_nbij' (fun S => symmDiff S {u}) (fun S => symmDiff S {u})
    · intros; simp
    · intros; simp
    · intro S _; simp [symmDiff_symmDiff_cancel_right]
    · intro S _; simp [symmDiff_symmDiff_cancel_right]
    · intro S _
      have h1 : P S s(u, v) ↔ (u ∈ S ↔ v ∈ S) := OMA.R_Erdos23_erdos_23_R2.same_mk S u v
      have h2 : P (symmDiff S {u}) s(u, v) ↔
          (u ∈ symmDiff S {u} ↔ v ∈ symmDiff S {u}) :=
        OMA.R_Erdos23_erdos_23_R2.same_mk _ u v
      have hu : u ∈ symmDiff S {u} ↔ u ∉ S := by simp [Finset.mem_symmDiff]
      have hv : v ∈ symmDiff S {u} ↔ v ∈ S := by simp [Finset.mem_symmDiff, huv.symm]
      have key : P S s(u, v) ↔ ¬ P (symmDiff S {u}) s(u, v) := by
        rw [h1, h2, hu, hv]
        by_cases a : u ∈ S <;> by_cases b : v ∈ S <;> simp [a, b]
      by_cases hP : P S s(u, v)
      · rw [if_pos hP, if_pos (key.mp hP)]
      · rw [if_neg hP, if_neg (fun h => hP (key.mpr h))]
  have hsum : ∑ S : Finset V, (G.edgeFinset.filter (P S)).card =
      ∑ S : Finset V, (G.edgeFinset.filter (fun e => ¬ P S e)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl hedge
  have htot : ∀ S : Finset V, (G.edgeFinset.filter (P S)).card +
      (G.edgeFinset.filter (fun e => ¬ P S e)).card = G.edgeFinset.card :=
    fun S => Finset.card_filter_add_card_filter_not _
  have hle : ∑ S : Finset V, 2 * (G.edgeFinset.filter (P S)).card ≤
      ∑ _S : Finset V, G.edgeFinset.card := by
    apply le_of_eq
    calc ∑ S : Finset V, 2 * (G.edgeFinset.filter (P S)).card
        = ∑ S : Finset V, (G.edgeFinset.filter (P S)).card +
            ∑ S : Finset V, (G.edgeFinset.filter (fun e => ¬ P S e)).card := by
          rw [← Finset.mul_sum, two_mul, hsum.symm]
      _ = ∑ S : Finset V, ((G.edgeFinset.filter (P S)).card +
            (G.edgeFinset.filter (fun e => ¬ P S e)).card) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ _S : Finset V, G.edgeFinset.card := Finset.sum_congr rfl (fun S _ => htot S)
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  refine ⟨S, ?_⟩
  convert (show (G.edgeFinset.filter (P S)).card ≤ G.edgeFinset.card / 2 by omega)
