import OMAStatements.S_oeis_a002000
import Mathlib

/-!
Key fact: 3^(2n+2) divides a(n)^2 - 4. Indeed a(0)^2 - 4 = 45, and with u = a(n)^2 one has
a(n+1)^2 - 4 = u (u - 3)^2 - 4 = (u - 4) (u - 1)^2, where 3 divides u - 1 = (u - 4) + 3.
Then a(n) - a(n+1) = -a(n) (a(n)^2 - 4) is divisible by 3^(2n+2), hence by 3^(n+r+2) for r <= n.
-/

namespace R002000
open OMA.S_oeis_a002000

theorem key : ∀ n : ℕ, (3 : ℤ) ^ (2 * n + 2) ∣ a n ^ 2 - 4 := by
  intro n
  induction n with
  | zero => exact ⟨5, by rw [show a 0 = 7 from rfl]; norm_num⟩
  | succ n ih =>
    have h3 : (3 : ℤ) ∣ a n ^ 2 - 1 := by
      have h0 : (3 : ℤ) ∣ (3 : ℤ) ^ (2 * n + 2) := dvd_pow_self 3 (by omega)
      have h := dvd_trans h0 ih
      have e1 : a n ^ 2 - 1 = (a n ^ 2 - 4) + 3 := by ring
      rw [e1]
      exact dvd_add h (dvd_refl 3)
    have h9 : (3 : ℤ) ^ 2 ∣ (a n ^ 2 - 1) ^ 2 := pow_dvd_pow_of_dvd h3 2
    have e : a (n + 1) ^ 2 - 4 = (a n ^ 2 - 4) * (a n ^ 2 - 1) ^ 2 := by
      rw [show a (n + 1) = a n * (a n ^ 2 - 3) from rfl]
      ring
    rw [e, show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by ring, pow_add]
    exact mul_dvd_mul ih h9

theorem solve : ∀ n r : ℕ, r ≤ n → a (n + 1) ≡ a n [ZMOD 3 ^ (n + r + 2)] := by
  intro n r hr
  rw [Int.modEq_iff_dvd]
  have h1 : (3 : ℤ) ^ (n + r + 2) ∣ 3 ^ (2 * n + 2) := pow_dvd_pow 3 (by omega)
  have e : a n - a (n + 1) = -(a n * (a n ^ 2 - 4)) := by
    rw [show a (n + 1) = a n * (a n ^ 2 - 3) from rfl]
    ring
  rw [e]
  exact (dvd_neg).mpr (dvd_mul_of_dvd_right (dvd_trans h1 (key n)) _)

end R002000

theorem OMA.solution : type_of% @OMA.S_oeis_a002000.main := R002000.solve
