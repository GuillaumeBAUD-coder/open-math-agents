import OMAStatements.S_oeis_a334603
import Mathlib

/-!
Write n = k + 1. Since 10^2 = 1 + 11 * 9 with 11 not dividing 9, Mathlib's
`ZMod.orderOf_one_add_mul_prime` gives that 10^2 has order 11^k modulo 11^(k+1). Reducing modulo
11, where 10 = -1 has order 2, shows that 2 divides the order of 10 modulo 11^(k+1). Then
`orderOf_pow'` (order of x^2 is orderOf x / gcd (orderOf x) 2) gives orderOf 10 = 2 * 11^k.
-/

namespace R334603
open OMA.S_oeis_a334603

theorem two_dvd (k : ℕ) : 2 ∣ orderOf (10 : ZMod (11 ^ (k + 1))) := by
  have h11 : (11 : ℕ) ∣ 11 ^ (k + 1) := dvd_pow_self 11 (Nat.succ_ne_zero k)
  have hmap := orderOf_map_dvd (ZMod.castHom h11 (ZMod 11)).toMonoidHom (10 : ZMod (11 ^ (k + 1)))
  have h10 : (ZMod.castHom h11 (ZMod 11)).toMonoidHom (10 : ZMod (11 ^ (k + 1))) = 10 := by
    first
    | exact map_ofNat (ZMod.castHom h11 (ZMod 11)) 10
    | (simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]; exact map_ofNat _ 10)
    | (simp; exact ZMod.cast_ofNat h11 10)
  have h2 : orderOf (10 : ZMod 11) = 2 := orderOf_eq_prime (by decide) (by decide)
  rw [h10, h2] at hmap
  exact hmap

theorem order_sq (k : ℕ) : orderOf ((10 : ZMod (11 ^ (k + 1))) ^ 2) = 11 ^ k := by
  have h := ZMod.orderOf_one_add_mul_prime (p := 11) (by norm_num) (by norm_num) 9 (by norm_num) k
  have e : (10 : ZMod (11 ^ (k + 1))) ^ 2 =
      1 + ((11 : ℕ) : ZMod (11 ^ (k + 1))) * ((9 : ℤ) : ZMod (11 ^ (k + 1))) := by
    norm_num
  rw [e]
  exact h

theorem order (k : ℕ) : orderOf (10 : ZMod (11 ^ (k + 1))) = 2 * 11 ^ k := by
  have h1 := order_sq k
  have h2 := two_dvd k
  rw [orderOf_pow' _ two_ne_zero, Nat.gcd_eq_right h2] at h1
  omega

end R334603

theorem OMA.solution : type_of% @OMA.S_oeis_a334603.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show orderOf (10 : ZMod (11 ^ (k + 1))) = 2 * 11 ^ (k + 1 - 1)
  rw [Nat.add_sub_cancel]
  exact R334603.order k
