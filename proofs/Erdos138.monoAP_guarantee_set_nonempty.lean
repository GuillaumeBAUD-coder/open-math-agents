import FormalConjectures.ErdosProblems.«138»

lemma OMA.progressionImage {N k : ℕ} (f : Fin k → ↥(Finset.Icc 1 N))
    (a d : ℕ) (hd : 0 < d) (hv : ∀ j, (f j).val = a + j.val * d) :
    (Subtype.val '' Set.range f).IsAPOfLength k := by
  have hf : Function.Injective f := by
    intro i j hij
    have heq := congrArg Subtype.val hij
    rw [hv i, hv j] at heq
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel heq)
  refine ⟨a, d, ?_, ?_⟩
  · rw [ENat.card_image_of_injective _ _ Subtype.val_injective,
      ← ENat.card_congr (Equiv.ofInjective f hf),
      ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  · ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, by
        simpa [nsmul_eq_mul] using (hv i).symm⟩
    · rintro ⟨n, hn, rfl⟩
      let i : Fin k := ⟨n, by exact_mod_cast hn⟩
      refine ⟨f i, ⟨i, rfl⟩, ?_⟩
      simpa [i, nsmul_eq_mul] using hv i

theorem OMA.solution : type_of% @Erdos138.monoAP_guarantee_set_nonempty := by
  classical
  intro r k
  obtain ⟨ι, fi, hj⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  let := fi
  let N := 1 + Fintype.card ι * k
  refine ⟨N, ?_⟩
  intro coloring
  -- A word maps into the interval by summing its digits and shifting to start at one.
  let point (w : ι → Fin k) : Finset.Icc 1 N :=
    ⟨1 + ∑ i, (w i).val, Finset.mem_Icc.mpr ⟨by omega, by
      have bound : (∑ i, (w i).val) ≤ ∑ _i : ι, k :=
        Finset.sum_le_sum fun i _ => (w i).isLt.le
      exact Nat.add_le_add_left (by simpa [nsmul_eq_mul] using bound) 1⟩⟩
  obtain ⟨line, color, mono⟩ := hj (fun w => coloring (point w))
  -- Along a combinatorial line, each wildcard adds the same digit once.
  let fixed (i : ι) : ℕ := ((line.idxFun i).map Fin.val).getD 0
  let variableWeight (i : ι) : ℕ := if line.idxFun i = none then 1 else 0
  let a := 1 + ∑ i, fixed i
  let d := ∑ i, variableWeight i
  have hd : 0 < d := by
    obtain ⟨i, hi⟩ := line.proper
    exact Finset.sum_pos' (fun j _ => Nat.zero_le (variableWeight j))
      ⟨i, Finset.mem_univ i, by simp [variableWeight, hi]⟩
  have digit (j : Fin k) (i : ι) :
      (line j i).val = fixed i + j.val * variableWeight i := by
    cases h : line.idxFun i <;>
      simp [Combinatorics.Line.coe_apply, fixed, variableWeight, h]
  have value (j : Fin k) : (point (line j)).val = a + j.val * d := by
    change 1 + ∑ i, (line j i).val = (1 + ∑ i, fixed i) + j.val * ∑ i, variableWeight i
    simp only [digit, Finset.sum_add_distrib, Finset.mul_sum, Nat.add_assoc]
  refine ⟨color, Set.range (fun j : Fin k => point (line j)), ?_, ?_⟩
  · exact OMA.progressionImage (fun j : Fin k => point (line j)) a d hd value
  · rintro _ ⟨j, rfl⟩
    exact mono j
