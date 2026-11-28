import OMAStatements.S_oeis_a007484
open OMA.S_oeis_a007484 in
theorem OMA.solution : type_of% @OMA.S_oeis_a007484.main := by
  have h : ∀ n, 8*a n = b (n+2)+c (n+1) ∧ 8*a (n+1) = b (n+3)+c (n+2) := by
    intro n
    induction n with
    | zero => exact ⟨rfl,rfl⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      change 8*(3*a (n+1)+2*a n) = (3*b (n+3)+2*b (n+2))+(3*c (n+2)+2*c (n+1))
      obtain ⟨h,k⟩ := ih
      omega
  exact fun n => (h n).1
