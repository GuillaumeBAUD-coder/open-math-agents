import OMAReductions.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1
import Mathlib

/-! `9` is odd and greater than `1`, so it is not a power of two. -/

theorem OMA.solution :
    OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1.H2 := by
  intro k hk
  rcases k with _ | _ | _ | _ | k
  · norm_num at hk
  · norm_num at hk
  · norm_num at hk
  · norm_num at hk
  · have h16 : 16 ≤ 2 ^ (k + 4) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
