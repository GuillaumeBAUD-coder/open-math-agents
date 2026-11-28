import OMAReductions.R_oeis_a306698_R1

/-!
# Proof of `oeis-a306698.R1.H1`

Proves that every term of the Recaman-like sequence `OMA.S_oeis_a306698.sequence` satisfies
`m % 3 = 0 ∨ m % 3 = 1`.

At step `n + 1`, the recurrence either subtracts `2 * (n + 1)` (when strictly less than the current
term) or adds `n + 1`. In both branches, `-2 * (n + 1) ≡ n + 1 (mod 3)`, so
`sequence (n + 1) % 3 = (sequence n + (n + 1)) % 3`. By induction on `n`,
`sequence n % 3 = if n % 3 = 1 then 1 else 0`, which is always `0` or `1`.
-/

namespace OeisA306698R1H1Proof

open OMA.S_oeis_a306698

private lemma sequence_mod_three (n : ℕ) :
    sequence n % 3 = if n % 3 = 1 then 1 else 0 := by
  induction n with
  | zero =>
    simp [sequence, state]
  | succ n ih =>
    have hstep : sequence (n + 1) =
        if 2 * (n + 1) < (state n).1 ∧ (state n).1 - 2 * (n + 1) ∉ (state n).2
        then (state n).1 - 2 * (n + 1)
        else (state n).1 + (n + 1) := rfl
    have hseq : (state n).1 = sequence n := rfl
    rw [hstep]
    by_cases hcond : 2 * (n + 1) < (state n).1 ∧ (state n).1 - 2 * (n + 1) ∉ (state n).2
    · rw [if_pos hcond, hseq]
      have hlt : 2 * (n + 1) < sequence n := hseq ▸ hcond.1
      split_ifs at ih ⊢ <;> omega
    · rw [if_neg hcond, hseq]
      split_ifs at ih ⊢ <;> omega

end OeisA306698R1H1Proof

theorem OMA.solution : OMA.R_oeis_a306698_R1.H1 := by
  rintro m ⟨n, rfl⟩
  change OMA.S_oeis_a306698.sequence n % 3 = 0 ∨ OMA.S_oeis_a306698.sequence n % 3 = 1
  have h := OeisA306698R1H1Proof.sequence_mod_three n
  split_ifs at h <;> omega
