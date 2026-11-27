import OMAStatements.S_oeis_a007484

open OMA.S_oeis_a007484 in
lemma OMA.a007484_key : ∀ n : ℕ, 8 * a n = b (n + 2) + c (n + 1) ∧
    8 * a (n + 1) = b (n + 3) + c (n + 2) := by
  intro n
  induction n with
  | zero => simp [a, b, c]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have ha : a (n + 2) = 3 * a (n + 1) + 2 * a n := by rw [a]
    have hb : b (n + 4) = 3 * b (n + 3) + 2 * b (n + 2) := by rw [b]
    have hc : c (n + 3) = 3 * c (n + 2) + 2 * c (n + 1) := by rw [c]
    show 8 * a (n + 2) = b (n + 4) + c (n + 3)
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a007484.main := by
  intro n
  exact (OMA.a007484_key n).1
