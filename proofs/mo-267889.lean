import OMAStatements.S_mo_267889
import Mathlib

-- Two initial draws from two values give E|A|=3/2, E|B|=5/4,
-- and E|B\\A|=1/4. The proposed product is instead 5/16.
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_267889.main) := by
  intro h
  have hcounter : OMA.S_mo_267889.expectDiff 2 2 ≠
      OMA.S_mo_267889.expectB 2 2 * (1 - OMA.S_mo_267889.expectA 2 2 / 2) := by
    decide +kernel
  exact hcounter (h 2 2 (by decide))
