import OMAStatements.S_wp_values_of_g_k_and_g_k_in_waring_s_problem

-- Reduction wp-values-of-g-k-and-g-k-in-waring-s-problem.R1 of wp-values-of-g-k-and-g-k-in-waring-s-problem: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_wp_values_of_g_k_and_g_k_in_waring_s_problem_R1

open OMA.S_wp_values_of_g_k_and_g_k_in_waring_s_problem

/-- Step H1 of the reduction. -/
def H1 : Prop := g 1 = 1

/-- Step H2 of the reduction. -/
def H2 : Prop := g 2 = 4

/-- Step H3 of the reduction. -/
def H3 : Prop := g 3 = 9

/-- Step H4 of the reduction. -/
def H4 : Prop := ( g 4 = 19 ∧ g 5 = 37 ∧ g 6 = 73 ∧ g 7 = 143 ∧ (∀ k ≥ 1, 2 ^ k + q k - 2 ≤ g k) ∧ (∀ k, q k + r k ≤ 2 ^ k → g k = 2 ^ k + q k - 2) ∧ (∀ k, q k + r k > 2 ^ k → q k * d k + q k + d k = 2 ^ k → g k = 2 ^ k + q k + d k - 2) ∧ (∀ k, q k + r k > 2 ^ k → q k * d k + q k + d k > 2 ^ k → g k = 2 ^ k + q k + d k - 3) ∧ G 1 = 1 ∧ G 2 = 4 ∧ G 4 = 16 ∧ (∀ k, G k ≤ g k) ∧ (∀ r ≥ 2, 2 ^ (r + 2) ≤ G (2 ^ r)) ∧ (∀ r, 2 ^ (r + 2) ≤ G (3 * 2 ^ r)) ∧ (∀ p r, Nat.Prime p → 2 < p → p ^ (r + 1) ≤ G (p ^ r * (p - 1))) ∧ (∀ p r, Nat.Prime p → 2 < p → (p ^ (r + 1) - 1) / 2 ≤ G (p ^ r * ((p - 1) / 2))) ∧ (∀ k ≥ 2, k + 1 ≤ G k) ∧ (4 ≤ G 3 ∧ G 3 ≤ 7) ∧ (6 ≤ G 5 ∧ G 5 ≤ 17) ∧ (9 ≤ G 6 ∧ G 6 ≤ 24) ∧ (8 ≤ G 7 ∧ G 7 ≤ 33) ∧ (32 ≤ G 8 ∧ G 8 ≤ 42) ∧ (13 ≤ G 9 ∧ G 9 ≤ 50) ∧ (12 ≤ G 10 ∧ G 10 ≤ 59) ∧ (12 ≤ G 11 ∧ G 11 ≤ 67) ∧ (16 ≤ G 12 ∧ G 12 ≤ 76) ∧ (14 ≤ G 13 ∧ G 13 ≤ 84) ∧ (15 ≤ G 14 ∧ G 14 ≤ 92) ∧ (16 ≤ G 15 ∧ G 15 ≤ 100) ∧ (64 ≤ G 16 ∧ G 16 ≤ 109) ∧ (18 ≤ G 17 ∧ G 17 ≤ 117) ∧ (27 ≤ G 18 ∧ G 18 ≤ 125) ∧ (20 ≤ G 19 ∧ G 19 ≤ 134) ∧ (25 ≤ G 20 ∧ G 20 ≤ 142) )

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_wp_values_of_g_k_and_g_k_in_waring_s_problem.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_wp_values_of_g_k_and_g_k_in_waring_s_problem_R1
