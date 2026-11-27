import FormalConjectures.OEIS.«189409»

/-! The ninth primorial squared plus one is divisible by the square of 29. -/

theorem OMA.disproof : ¬ (type_of% @OeisA189409.conjecture_1) := by
  intro hsquarefree
  have hprimorial : Nat.kthPrimorial 9 = 223092870 := by
    rw [Nat.kthPrimorial_succ 8, Nat.kthPrimorial_succ 7,
      Nat.kthPrimorial_succ 6, Nat.kthPrimorial_succ 5]
    norm_num [Nat.kthPrimorial_five, Nat.nth_prime_five_eq_thirteen,
      Nat.nth_prime_six_eq_seventeen, Nat.nth_prime_seven_eq_nineteen,
      Nat.nth_prime_eight_eq_twentyThree]
  apply Nat.squarefree_iff_prime_squarefree.mp (hsquarefree 9) 29 (by decide)
  rw [OeisA189409.a, hprimorial]
  exact ⟨59180057841661, by decide⟩
