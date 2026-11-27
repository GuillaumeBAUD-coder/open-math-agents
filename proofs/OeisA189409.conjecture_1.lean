import FormalConjectures.OEIS.«189409»

/-!
The product of the first nine primes is 223092870. Its square plus one is
841 * 59180057841661, so the ninth term has a repeated prime factor.
-/

theorem OMA.disproof : ¬ (type_of% @OeisA189409.conjecture_1) := by
  intro hall
  have hprimorial : Nat.kthPrimorial 9 = 223092870 := by
    norm_num [Nat.kthPrimorial_succ]
  have hdiv : 29 * 29 ∣ OeisA189409.a 9 := by
    refine ⟨59180057841661, ?_⟩
    norm_num [OeisA189409.a, hprimorial]
  exact (Nat.squarefree_iff_prime_squarefree.mp (hall 9) 29 (by decide)) hdiv
