import OMAStatements.S_oeis_a230168

/-!
# Proof of OEIS A230168 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a230168.main := by
  intro n hn
  rcases n with _ | k
  · exact absurd hn (by decide)
  · rw [pow_succ]
    have hpow : 0 < (2 : ℕ) ^ k := by positivity
    omega
