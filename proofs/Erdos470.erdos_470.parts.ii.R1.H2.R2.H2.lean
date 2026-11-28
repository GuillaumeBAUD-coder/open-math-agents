import OMAReductions.R_Erdos470_erdos_470_parts_ii_R1_H2_R2

-- Step Erdos470.erdos_470.parts.ii.R1.H2.R2.H2: hypothesis H2 of reduction
-- Erdos470.erdos_470.parts.ii.R1.H2.R2.
-- Written with Claude Code (AI-assisted).
-- The reduction file already proves this bound unconditionally as `higherPowerBound`
-- (by @yiklin21): for each exponent e ≥ 2, two e-th powers in [x, x + h] with h² < x would be
-- farther apart than h, and every exponent is below E.

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R1_H2_R2.H2 :=
  OMA.R_Erdos470_erdos_470_parts_ii_R1_H2_R2.higherPowerBound
