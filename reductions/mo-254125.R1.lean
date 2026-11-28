import OMAStatements.S_mo_254125

-- Reduction mo-254125.R1 of mo-254125: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_mo_254125_R1

open OMA.S_mo_254125
open Finset

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ N M : ℕ, 0 < N → 0 < M →
      (2*(M:ℝ)/(M+1))*((N:ℝ)/(N+((M:ℝ)-1))) ≤ optimum N M ∧
      optimum N M ≤ 2*(M:ℝ)/(M+1) ∧
      meets N M (2*(M:ℝ)/(M+1)) (profile N M))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ M : ℕ, 0 < M → Filter.Tendsto (fun N : ℕ => optimum N M)
      Filter.atTop (nhds (2*(M:ℝ)/(M+1))))

/-- Step H3 of the reduction. -/
def H3 : Prop := (Filter.Tendsto (fun M : ℕ => 2*(M:ℝ)/(M+1)) Filter.atTop (nhds 2))

/-- Step H4 of the reduction. -/
def H4 : Prop := ( (∀ B : ℕ → ℕ, Filter.Tendsto B Filter.atTop Filter.atTop →
      Filter.Tendsto (fun N : ℕ => optimum N (B N)) Filter.atTop (nhds 2)) ∧ (∀ (M : ℕ), 0 < M → ∀ (q : ℕ → ℝ) (x : ℕ → ℕ → ℝ),
      (∀ N, 0 < N → meets N M (q N) (x N)) →
      Filter.Tendsto q Filter.atTop (nhds (2*(M:ℝ)/(M+1))) →
      Filter.Tendsto (fun N : ℕ => (∑ i ∈ range N, (x N i)^2)/(N:ℝ))
        Filter.atTop (nhds (2*(M:ℝ)/(M+1)))) ∧ (∀ k M : ℕ, 0 < k → 2 ≤ M →
      profile (k*M) M 0 - profile (k*M) M 1 = (M:ℝ)/Real.sqrt (M+1)) )

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_mo_254125.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_mo_254125_R1
