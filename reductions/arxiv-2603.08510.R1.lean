import OMAStatements.S_arxiv_2603_08510

-- Reduction arxiv-2603.08510.R1 of arxiv-2603.08510: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_arxiv_2603_08510_R1

open OMA.S_arxiv_2603_08510

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, n % 8 = 3 → jacobiSym n 7 = 1 → 7 ∣ overpartitionCount (2 ^ 4 * n))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, n % 8 = 3 → jacobiSym n 17 = -1 → jacobiSym n 19 = 1 →
      19 ∣ overpartitionCount (17 ^ 2 * 4 * n))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, n % 8 = 3 → jacobiSym n 11 = -1 →
      17 ∣ overpartitionCount (17 * 11 ^ 2 * n))

/-- Step H4 of the reduction. -/
def H4 : Prop := (∀ n : ℕ, n % 8 = 5 → jacobiSym n 13 = 1 →
      23 ∣ overpartitionCount (23 * 13 ^ 2 * n))

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_arxiv_2603_08510.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_arxiv_2603_08510_R1
