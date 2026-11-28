import OMAStatements.S_oeis_a102341

-- Problem: A102341: Areas of 'close-to-equilateral' integer triangles.
-- Upstream: formal-conjectures statements/oeis-a102341.lean:0 (declaration OMA.S_oeis_a102341.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)


namespace OMA.Aux102341

def seq : ℕ → ℕ × ℕ
  | 0 => (4, 2)
  | n + 1 => (7 * (seq n).1 + 16 * (seq n).2 + 4, 3 * (seq n).1 + 2 + 7 * (seq n).2)

lemma inv (n : ℕ) : (3 * (seq n).1 + 4) * (seq n).1 = 16 * (seq n).2 ^ 2 ∧ 1 ≤ (seq n).2 := by
  induction n with
  | zero => simp [seq]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [seq]
      nlinarith [h1]
    · simp only [seq]
      omega

lemma mono : StrictMono (fun n => (seq n).1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [seq]
  omega

def tri (n : ℕ) : ℕ × ℕ × ℕ := ((seq n).1 + 1, (seq n).1 + 1, (seq n).1 + 2)

lemma tri_inj : Function.Injective tri := by
  intro m n h
  have h1 : (seq m).1 + 1 = (seq n).1 + 1 := congrArg Prod.fst h
  exact mono.injective (by simpa using h1)

lemma tri_mem (n : ℕ) : OMA.S_oeis_a102341.IsCloseToEquilateralHeronian (tri n) := by
  obtain ⟨h1, h2⟩ := inv n
  show 1 ≤ (seq n).1 + 1 ∧ (seq n).1 + 1 ≤ (seq n).1 + 1 ∧ (seq n).1 + 1 ≤ (seq n).1 + 2 ∧
    (seq n).1 + 2 = (seq n).1 + 1 + 1 ∧ ∃ A : ℕ, 1 ≤ A ∧
    16 * A ^ 2 = ((seq n).1 + 1 + ((seq n).1 + 1) + ((seq n).1 + 2)) *
      ((seq n).1 + 1 + ((seq n).1 + 1) - ((seq n).1 + 2)) *
      ((seq n).1 + 1 + ((seq n).1 + 2) - ((seq n).1 + 1)) *
      ((seq n).1 + 1 + ((seq n).1 + 2) - ((seq n).1 + 1))
  refine ⟨by omega, le_refl _, by omega, by omega, (seq n).2 * ((seq n).1 + 2), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · have e1 : (seq n).1 + 1 + ((seq n).1 + 1) - ((seq n).1 + 2) = (seq n).1 := by omega
    have e2 : (seq n).1 + 1 + ((seq n).1 + 2) - ((seq n).1 + 1) = (seq n).1 + 2 := by omega
    have e3 : (seq n).1 + 1 + ((seq n).1 + 1) + ((seq n).1 + 2) = 3 * (seq n).1 + 4 := by omega
    rw [e1, e2, e3]
    calc 16 * ((seq n).2 * ((seq n).1 + 2)) ^ 2 = (16 * (seq n).2 ^ 2) * ((seq n).1 + 2) ^ 2 := by ring
      _ = ((3 * (seq n).1 + 4) * (seq n).1) * ((seq n).1 + 2) ^ 2 := by rw [h1]
      _ = _ := by ring

end OMA.Aux102341

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a102341.main) := by
  intro h
  exact (Set.infinite_of_injective_forall_mem OMA.Aux102341.tri_inj
    (fun n => OMA.Aux102341.tri_mem n)) h
