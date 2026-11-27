import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R3
import Mathlib

-- Step AgohGiuga.agoh_giuga.variants.giuga.R3.H1: hypothesis H1 of reduction AgohGiuga.agoh_giuga.variants.giuga.R3
-- Credit: @ivillar. From q D + m = m q k + 1 we get k >= 1 and D < m k; with s = m k - D, q s = m - 1, so 0 < s < m and D mod m = m - s.

/-! Step AgohGiuga.agoh_giuga.variants.giuga.R3.H1. -/

namespace P8GiugaR3H1

theorem giuga_h1 : ∀ m D q k : ℕ, 1 < m → 1 < q → q * D + m = (m * q) * k + 1 →
    q * (m - D % m) = m - 1 := by
  intro m D q k hm hq h
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h
      omega
    · exact hk
  have e1 : (m * q) * k = q * (m * k) := by ring
  have hDlt : D < m * k := by
    by_contra hc
    have hc := not_lt.mp hc
    have : q * (m * k) ≤ q * D := Nat.mul_le_mul_left q hc
    omega
  obtain ⟨s, hs⟩ : ∃ s, m * k = D + s := ⟨m * k - D, by omega⟩
  have hqs : q * s = m - 1 := by
    have : q * (m * k) = q * D + q * s := by rw [hs, Nat.mul_add]
    omega
  have h2s : 2 * s ≤ q * s := Nat.mul_le_mul_right s hq
  have hs_lt : s < m := by omega
  have hs_pos : 0 < s := by omega
  have hmk : m * k = m * (k - 1) + m := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    ring
  have hDm : D = m * (k - 1) + (m - s) := by omega
  have hmod : D % m = m - s := by
    rw [hDm, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hmod, Nat.sub_sub_self hs_lt.le]
  exact hqs

end P8GiugaR3H1

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3.H1 :=
  P8GiugaR3H1.giuga_h1
