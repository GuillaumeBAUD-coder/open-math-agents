import OMAStatements.S_oeis_a176997

namespace OMA.P_oeis_a176997

open OMA.S_oeis_a176997

lemma key (k : ℕ) : k ∈ A176997 ↔ k = 1 ∨ (k.Prime ∧ Odd k) ∨ Nat.FermatPsp k 2 := by
  constructor
  · rintro ⟨hk0, hk⟩
    by_cases h1 : k = 1
    · exact Or.inl h1
    by_cases hp : k.Prime
    · refine Or.inr (Or.inl ⟨hp, ?_⟩)
      rcases hp.eq_two_or_odd' with h2 | h2
      · subst h2
        exfalso
        revert hk
        decide
      · exact h2
    · refine Or.inr (Or.inr ⟨?_, hp, by omega⟩)
      unfold Nat.ProbablePrime
      exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).1 hk.symm
  · rintro (h | ⟨hp, hodd⟩ | ⟨hpp, hnp, h1⟩)
    · subst h
      exact ⟨by norm_num, by decide⟩
    · refine ⟨hp.pos, ?_⟩
      have hc : Nat.Coprime 2 k := by
        rw [Nat.coprime_two_left]
        exact hodd
      exact Nat.ModEq.pow_card_sub_one_eq_one hp hc
    · refine ⟨by omega, ?_⟩
      exact ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).2 hpp).symm

end OMA.P_oeis_a176997

open OMA.S_oeis_a176997 OMA.P_oeis_a176997 in
theorem OMA.solution : type_of% @OMA.S_oeis_a176997.main := by
  constructor
  · ext k
    rw [key]
    simp only [Set.mem_union, Set.mem_singleton_iff, A065091, A001567, Set.mem_ofPred_eq]
    tauto
  · ext k
    rw [key]
    simp only [Set.mem_union, A006005, A001567, Set.mem_ofPred_eq]
    constructor
    · rintro (h | h | h)
      · exact Or.inl ⟨by rw [h]; decide, Or.inl h⟩
      · exact Or.inl ⟨h.2, Or.inr h.1⟩
      · exact Or.inr h
    · rintro (⟨ho, h | h⟩ | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h, ho⟩)
      · exact Or.inr (Or.inr h)
