import OMAStatements.S_oeis_a267777

namespace OMA.A267777Proof
open OMA.S_oeis_a267777 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool :=
  if t = 0 then (if x = 0 then true else false) else (if x = t - 2 ∨ x = t - 1 then false else true)

theorem S (t : ℕ) : ∀ x, state t x = P t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih =>
    intro x
    simp only [state, eca, ih, P]
    push_cast
    split_ifs <;> first | rfl | (exfalso; omega)

theorem T (N : ℕ) : ∑ k ∈ Finset.range (N + 1), (10 : ℚ) ^ (N - k) = (10 ^ (N + 1) - 1) / 9 := by
  have := Finset.sum_range_reflect (fun k => (10 : ℚ) ^ k) (N + 1)
  simp only [Nat.add_sub_cancel] at this
  rw [this, geom_sum_eq (by norm_num)]
  norm_num

theorem V (n : ℕ) : (a n : ℚ) = ∑ k ∈ Finset.range (2 * n + 1), if P n ((k : ℤ) - n) then (10 : ℚ) ^ (2 * n - k) else 0 := by
  simp only [a, S]
  push_cast
  rfl

theorem F (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (10 ^ (2 * n + 1) - 1) / 9 - 10 ^ (2) - 10 ^ (1) := by
  rw [V, Finset.sum_congr rfl (g := fun k => (10 : ℚ) ^ (2 * n - k) - (if k = 2 * n - 2 then 10 ^ (2 * n - k) else 0) - (if k = 2 * n - 1 then 10 ^ (2 * n - k) else 0)), Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (by simp <;> omega), if_pos (by simp <;> omega), T]
  try simp only [show 2 * n - (2 * n - 2) = 2 by omega, show 2 * n - (2 * n - 1) = 1 by omega]
  intro k _
  simp only [P]
  split_ifs <;> first | (exfalso; omega) | contradiction | simp

theorem R (n : ℕ) (hn : 2 < n) : (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 3 := ⟨n - 3, by omega⟩
  have h : (a (p + 3) : ℚ) = 101 * a (p + 2) - 100 * a (p + 1) := by
    rw [F _ (by omega), F _ (by omega), F _ (by omega)]
    ring
  rw [show p + 3 - 1 = p + 2 by omega, show p + 3 - 2 = p + 1 by omega]
  exact_mod_cast h

theorem G : (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 - 100 * X)) = 1 - 100 * X + 11000 * X ^ 2 := by
  have k : (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 - 100 * X)) = 1 - 100 * X + 11000 * X ^ 2 := by
    rw [show (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 - 100 * X)) = C (1 : ℤ) * (mk (fun n => (a n : ℤ))) + C (-101 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 1) + C (100 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 2) by simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 - 100 * X + 11000 * X ^ 2 : ℤ⟦X⟧) = C (1 : ℤ) + C (-100 : ℤ) * X ^ 1 + C (11000 : ℤ) * X ^ 2 by simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      simp only [show 1 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, show m + 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega, show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, ↓reduceIte]
      have h := (R (m + 3) (by omega))
      simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega] at h
      linear_combination h
  exact k

end OMA.A267777Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267777.main := ⟨OMA.A267777Proof.R, OMA.A267777Proof.G⟩
