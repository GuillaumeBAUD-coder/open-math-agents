import OMAStatements.S_erdos_84

-- Reduction erdos-84.R1 of erdos-84: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_erdos_84_R1

open OMA.S_erdos_84
open Filter Topology
open Classical
open Classical

/-- Step H1 of the reduction. -/
def H1 : Prop := Tendsto (fun n : ℕ => (numCycleSets n : ℝ) / 2 ^ n) atTop (𝓝 0)

/-- Step H2 of the reduction. -/
def H2 : Prop := Tendsto (fun n : ℕ => (numCycleSets n : ℝ) / (2 : ℝ) ^ ((n : ℝ) / 2)) atTop atTop

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_erdos_84.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_erdos_84_R1
