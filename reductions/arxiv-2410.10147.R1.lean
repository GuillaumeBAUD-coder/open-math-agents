import OMAStatements.S_arxiv_2410_10147

-- Reduction arxiv-2410.10147.R1 of arxiv-2410.10147: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_arxiv_2410_10147_R1

open OMA.S_arxiv_2410_10147

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ (n : ℕ) (ρ : ℝ), 1 ≤ n → 0 ≤ ρ → ρ ≤ 1 →
      ∀ f : Cube n → Bool, Balanced f →
        ∀ (k : Fin n) (s : Bool), stab ρ f ≤ stab ρ (fun x => x k == s)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ (n : ℕ) (ρ : ℝ), 1 ≤ n → 0 ≤ ρ → ρ ≤ 1 →
      ∀ f : Cube n → Bool, Balanced f →
        ∀ (k : Fin n) (s : Bool), stabSym ρ f ≤ stabSym ρ (fun x => x k == s)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2410_10147.main := by
  intro h1 h2 x1 x2 x3 x4 x5 x6 x7 x8 x9
  exact ⟨h1 x1 x2 x3 x4 x5 x6 x7 x8 x9, h2 x1 x2 x3 x4 x5 x6 x7 x8 x9⟩

end OMA.R_arxiv_2410_10147_R1
