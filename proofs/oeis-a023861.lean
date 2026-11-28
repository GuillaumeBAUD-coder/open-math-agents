import OMAStatements.S_oeis_a023861
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: closed form weightedSum (m+r) m = L(m+r+4) - L(r+4) - m*L(r+2) by induction; hence
-- a(2j), a(2j+1) in terms of Lucas numbers; order-10 recurrence by parity split and ring;
-- coefficient comparison (n<10 by decide, n+10 by the recurrence).

namespace OMA.P_oeis_a023861
open OMA.S_oeis_a023861 PowerSeries

theorem L2 (k : ℕ) : lucas (k + 2) = lucas (k + 1) + lucas k := by
  rw [lucas]

theorem ws_closed (m : ℕ) : ∀ r : ℕ,
    weightedSum (m + r) m + lucas (r + 4) + m * lucas (r + 2) = lucas (m + r + 4) := by
  induction m with
  | zero => intro r; simp [weightedSum]
  | succ m ih =>
    intro r
    have h := ih (r + 1)
    have e1 : weightedSum (m + 1 + r) (m + 1)
        = weightedSum (m + (r + 1)) m + ((m + 1 : ℕ) : ℤ) * lucas (r + 1) := by
      unfold weightedSum
      rw [Finset.sum_range_succ]
      have : m + 1 + r - m = r + 1 := by omega
      rw [this, show m + 1 + r = m + (r + 1) by omega]
    rw [e1, show m + 1 + r + 4 = m + (r + 1) + 4 by omega]
    rw [show r + 1 + 4 = r + 3 + 2 by omega, L2, show r + 3 + 1 = r + 2 + 2 by omega, L2,
      show r + 1 + 2 = r + 1 + 2 from rfl, L2] at h
    rw [show r + 4 = r + 2 + 2 by omega, L2, L2]
    push_cast at h ⊢
    linear_combination h

theorem aE (j : ℕ) : a (2 * j) = lucas (2 * j + 4) - lucas (j + 4) - j * lucas (j + 2) := by
  have h := ws_closed j j
  have : (2 * j + 1) / 2 = j := by omega
  unfold a
  rw [this, show 2 * j = j + j by omega]
  linear_combination h

theorem aO (j : ℕ) : a (2 * j + 1) = lucas (2 * j + 5) - lucas (j + 4) - (j + 1) * lucas (j + 2) := by
  have h := ws_closed (j + 1) j
  have : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  unfold a
  rw [this, show 2 * j + 1 = j + 1 + j by omega, show 2 * j + 5 = j + 1 + j + 4 by omega]
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
theorem rec (n : ℕ) : a (n+10) - a (n+9) - 3*a (n+8) + 2*a (n+7) + a (n+6) + a (n+5)
    + 3*a (n+4) - 2*a (n+3) - a (n+2) - a (n+1) - a n = 0 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2*j+10 = 2*(j+5) by ring, show 2*j+9 = 2*(j+4)+1 by ring,
      show 2*j+8 = 2*(j+4) by ring, show 2*j+7 = 2*(j+3)+1 by ring,
      show 2*j+6 = 2*(j+3) by ring, show 2*j+5 = 2*(j+2)+1 by ring,
      show 2*j+4 = 2*(j+2) by ring, show 2*j+3 = 2*(j+1)+1 by ring,
      show 2*j+2 = 2*(j+1) by ring]
    simp only [aE, aO]
    push_cast
    simp only [mul_add, add_assoc, Nat.reduceAdd, Nat.reduceMul, L2]
    ring
  · rw [show 2*j+1+10 = 2*(j+5)+1 by ring, show 2*j+1+9 = 2*(j+5) by ring,
      show 2*j+1+8 = 2*(j+4)+1 by ring, show 2*j+1+7 = 2*(j+4) by ring,
      show 2*j+1+6 = 2*(j+3)+1 by ring, show 2*j+1+5 = 2*(j+3) by ring,
      show 2*j+1+4 = 2*(j+2)+1 by ring, show 2*j+1+3 = 2*(j+2) by ring,
      show 2*j+1+2 = 2*(j+1)+1 by ring, show 2*j+1+1 = 2*(j+1) by ring]
    simp only [aE, aO]
    push_cast
    simp only [mul_add, add_assoc, Nat.reduceAdd, Nat.reduceMul, L2]
    ring

theorem main' : ((1-X-X^2 : ℤ⟦X⟧) * (1-X^2-X^4)^2) * mk a =
    X + C 2 * X^2 + C 4 * X^3 - C 2 * X^4 - X^5 + C 3 * X^6 := by
  have hP : ((1-X-X^2 : ℤ⟦X⟧) * (1-X^2-X^4)^2) = 1 - X^1 - C 3 * X^2 + C 2 * X^3 + X^4 + X^5
      + C 3 * X^6 - C 2 * X^7 - X^8 - X^9 - X^10 := by
    simp only [map_ofNat]; ring
  rw [hP]
  ext n
  simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
    coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_X]
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | n + 10 =>
    have := rec n
    simp only [show 1 ≤ n + 10 by omega, show 2 ≤ n + 10 by omega, show 3 ≤ n + 10 by omega,
      show 4 ≤ n + 10 by omega, show 5 ≤ n + 10 by omega, show 6 ≤ n + 10 by omega,
      show 7 ≤ n + 10 by omega, show 8 ≤ n + 10 by omega, show 9 ≤ n + 10 by omega,
      show 10 ≤ n + 10 by omega, if_true, show n + 10 ≠ 1 by omega, show n + 10 ≠ 2 by omega,
      show n + 10 ≠ 3 by omega, show n + 10 ≠ 4 by omega, show n + 10 ≠ 5 by omega,
      show n + 10 ≠ 6 by omega, if_false, Nat.add_sub_cancel, Nat.reduceSubDiff]
    try simp only [show n + 10 - 1 = n + 9 by omega, show n + 10 - 2 = n + 8 by omega,
      show n + 10 - 3 = n + 7 by omega, show n + 10 - 4 = n + 6 by omega,
      show n + 10 - 5 = n + 5 by omega, show n + 10 - 6 = n + 4 by omega,
      show n + 10 - 7 = n + 3 by omega, show n + 10 - 8 = n + 2 by omega,
      show n + 10 - 9 = n + 1 by omega, show n + 10 - 10 = n by omega] at *
    linear_combination this

end OMA.P_oeis_a023861

theorem OMA.solution : type_of% @OMA.S_oeis_a023861.main := OMA.P_oeis_a023861.main'
