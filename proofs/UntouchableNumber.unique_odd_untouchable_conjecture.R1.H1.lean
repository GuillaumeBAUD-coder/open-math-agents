import OMAReductions.R_UntouchableNumber_unique_odd_untouchable_conjecture_R1

-- Step UntouchableNumber.unique_odd_untouchable_conjecture.R1.H1: hypothesis H1 of reduction UntouchableNumber.unique_odd_untouchable_conjecture.R1
-- Credit: @Jeffreyyvdb
-- H1 := Nat.IsUntouchable 5

/-
The upstream module already proves this statement as `UntouchableNumber.isUntouchable_five`
(a test-category lemma, not a sorry): a number n >= 30 has proper-divisor sum 1 or at least 6,
and the cases n < 30 are checked one by one. This step is that lemma.
-/

theorem OMA.solution : OMA.R_UntouchableNumber_unique_odd_untouchable_conjecture_R1.H1 := by
  exact UntouchableNumber.isUntouchable_five
