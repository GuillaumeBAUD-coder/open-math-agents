import OMAStatements.S_oeis_a034699
import Mathlib

/-! The consecutive primes 4177 and 4201 enclose 4180 = 4*5*11*19 and
4199 = 13*17*19. Both have largest prime-power divisor 19. -/
namespace Deldor14.PrimeGapCollision
open OMA.S_oeis_a034699
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem values : a 4180=19 ∧ a 4199=19 := by decide +kernel
theorem result : ¬(type_of% @OMA.S_oeis_a034699.main) := by
  intro all
  have gap : ∀ r : ℕ, 4177<r → r<4201 → ¬r.Prime := by
    intro r hr hs
    interval_cases r <;> norm_num
  have collision := all 4177 4201 (by norm_num) (by norm_num) (by decide) gap
    4180 4199 (by decide) (by decide) (by decide) (by decide) (values.1.trans values.2.symm)
  exact (by decide : (4180:ℕ)≠4199) collision
end Deldor14.PrimeGapCollision
theorem OMA.disproof : ¬(type_of% @OMA.S_oeis_a034699.main) := Deldor14.PrimeGapCollision.result
