import OMAReductions.R_SierpinskiNumber_prime_sierpinski_problem_R1

namespace OMA.R_SierpinskiNumber_prime_sierpinski_problem_R1_H2_R1

/-- The candidate `90527`, treated separately because the required witness prime is enormous. -/
def H1 : Prop :=
  ∃ n : ℕ, (90527 * 2 ^ n + 1).Prime

/-- The candidate `168451`, treated separately because the required witness prime is enormous. -/
def H2 : Prop :=
  ∃ n : ℕ, (168451 * 2 ^ n + 1).Prime

theorem main : H1 → H2 → OMA.R_SierpinskiNumber_prime_sierpinski_problem_R1.H2 := by
  intro h90527 h168451 k hk
  simp at hk
  rcases hk with rfl | rfl
  · exact h90527
  · exact h168451

end OMA.R_SierpinskiNumber_prime_sierpinski_problem_R1_H2_R1
