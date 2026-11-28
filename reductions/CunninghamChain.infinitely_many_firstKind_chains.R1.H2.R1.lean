import OMAReductions.R_CunninghamChain_infinitely_many_firstKind_chains_R1

-- Reduction CunninghamChain.infinitely_many_firstKind_chains.R1.H2.R1 of step CunninghamChain.infinitely_many_firstKind_chains.R1.H2
-- Credit: @hiattco

namespace OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1_H2_R1



open CunninghamChain

private theorem firstKind_suffix (p d i : ℕ) :
    firstKindTerm (firstKindTerm p d) i = firstKindTerm p (d + i) := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Nat.add_succ, firstKindTerm, ih]

private theorem index_le_firstKind (p i : ℕ) : i ≤ firstKindTerm p i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    change i + 1 ≤ 2 * firstKindTerm p i + 1
    omega



private theorem firstFailure (P : Nat → Prop) {t : Nat} (ht : ¬ P t) :
    ∃ j, ¬ P j ∧ ∀ i < j, P i := by
  classical
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases all : ∀ i < t, P i
    · exact ⟨t, ht, all⟩
    · simp only [Classical.not_forall] at all
      obtain ⟨i, hi, hf⟩ := all
      exact ih i hi hf

private theorem suffix_unbounded (F : Nat → Nat → Nat) (P : Nat → Prop)
    (shift : ∀ p s i, F (F p s) i = F p (s+i))
    (grow : ∀ p s, s ≤ F p s)
    (prefixes : ∀ L, ∃ p, ∀ i < L, P (F p i))
    (ends : ∀ p, ∃ j, ¬ P (F p j)) (k B : Nat) :
    ∃ q, (∀ i < k, P (F q i)) ∧ ¬ P (F q k) ∧ B < q := by
  obtain ⟨p, hp⟩ := prefixes (B+k+1)
  obtain ⟨t, ht⟩ := ends p
  obtain ⟨j, hj, hbefore⟩ := firstFailure (fun i => P (F p i)) ht
  have hjbig : B+k+1 ≤ j := by
    exact Nat.le_of_not_gt (fun h => hj (hp j h))
  refine ⟨F p (j-k), ?_, ?_, ?_⟩
  · intro i hi
    rw [shift]
    exact hbefore _ (by omega)
  · rw [shift, Nat.sub_add_cancel (by omega)]
    exact hj
  · have := grow p (j-k)
    omega

-- The open prime-pattern input requires only one prefix of each length.
def H1 : Prop :=
  ∀ L : ℕ, ∃ p : ℕ, ∀ i < L, (firstKindTerm p i).Prime

-- Each prescribed start eventually encounters a nonprime.
def H2 : Prop :=
  ∀ p : ℕ, ∃ j : ℕ, ¬ (firstKindTerm p j).Prime

theorem main : H1 → H2 → OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1.H2 := by
  intro prefixes ends k hk
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨q, hprime, hstop, hB⟩ :=
    suffix_unbounded firstKindTerm Nat.Prime firstKind_suffix index_le_firstKind prefixes ends k B
  exact ⟨q, ⟨by omega, hprime, hstop⟩, hB⟩

end OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1_H2_R1
