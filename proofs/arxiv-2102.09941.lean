import OMAStatements.S_arxiv_2102_09941

/-!
# A counterexample to the odd-iterate condition at 6

Source: https://arxiv.org/abs/2102.09941v2, Conjecture 3.1.
Credit: @rleshner

The first three divisor sums are 12, 28 and 56 (also tabulated in OEIS A051572). The third iterate leaves
remainder 2 modulo 6, contradicting the first required condition.
-/

open OMA.S_arxiv_2102_09941

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2102_09941.main) := by
  intro conjecture
  have h := ((conjecture 6 (by decide)).mpr rfl).1 3 (by decide) ⟨1, rfl⟩
  have certificate : (divisorSum^[3]) 6 = 56 := by decide
  rw [certificate] at h
  exact (by decide : ¬ 6 ∣ 56) h
