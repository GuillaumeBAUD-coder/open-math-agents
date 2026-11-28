import OMAStatements.S_oeis_a008407

/-!
Disproof of the statement as formalized. `Admissible S` only asks for some natural `r` with
`s % p ≠ r` for every `s ∈ S`; taking `r = p` always works because `s % p < p`, so every finite set
is admissible. Hence `Finset.range 5` witnesses `a 5 ≤ 4`, so `a 5 / 5 ≤ 4 / 5 < 1 ≤ H 5`, which
contradicts part (ii) at `n = 5` (it claims `0 < a 5 / 5 - H 5`). The intended definition needs
`r < p` (a residue class modulo `p`).
-/

open OMA.S_oeis_a008407

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a008407.main) := by
  intro h
  have hpos : 0 < (a 5 : ℝ) / 5 - H 5 := by
    have := (h.2 5 (by norm_num)).1
    exact_mod_cast this
  have hadm : Admissible (Finset.range 5) := by
    intro p hp
    exact ⟨p, fun s _ => (Nat.mod_lt s hp.pos).ne⟩
  have hmem : (4 : ℕ) ∈
      {w : ℕ | ∃ S : Finset ℕ, S.card = 5 ∧ 0 ∈ S ∧ (∀ s ∈ S, s ≤ w) ∧ Admissible S} := by
    refine ⟨Finset.range 5, by simp, by simp, ?_, hadm⟩
    intro s hs
    simp only [Finset.mem_range] at hs
    omega
  have ha : a 5 ≤ 4 := Nat.sInf_le hmem
  have haR : (a 5 : ℝ) ≤ 4 := by exact_mod_cast ha
  have hH : (1 : ℝ) ≤ H 5 := by
    unfold H
    have key : (1 : ℝ) / ((1 : ℕ) : ℝ) ≤
        ∑ i ∈ (Finset.Icc 1 5 : Finset ℕ), (1 : ℝ) / ((i : ℕ) : ℝ) := by
      apply Finset.single_le_sum (f := fun i : ℕ => (1 : ℝ) / ((i : ℕ) : ℝ))
        (s := (Finset.Icc 1 5 : Finset ℕ))
      · intro i _
        positivity
      · simp
    have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1] at key
    exact key
  linarith
