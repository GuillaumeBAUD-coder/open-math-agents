import OMAStatements.S_oeis_a024219

-- Problem: A024219 (recurrence and generating function).
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Proof: closed form 12 * a n = 9 n^2 + 3 n - 12 + 6 [n mod 4 ≥ 2] for n ≥ 1 (floor bounds on
-- each residue class mod 4); the recurrence then follows linearly, and the generating function
-- identity coefficientwise.

namespace OMA.A024219

open OMA.S_oeis_a024219

def ind (n : ℕ) : ℤ := if 2 ≤ n % 4 then 1 else 0

lemma ind_add_two (n : ℕ) : ind (n + 2) = 1 - ind n := by
  unfold ind
  split_ifs <;> omega

lemma floor_val (n : ℕ) (m : ℤ) (h1 : (m : ℚ) * (4 * (3 * (n : ℚ) + 2)) ≤ (n : ℚ) * (9 * (n : ℚ) ^ 2 + 9 * (n : ℚ) - 2))
    (h2 : (n : ℚ) * (9 * (n : ℚ) ^ 2 + 9 * (n : ℚ) - 2) < ((m : ℚ) + 1) * (4 * (3 * (n : ℚ) + 2))) :
    a n = m := by
  unfold a
  have hpos : (0 : ℚ) < 4 * (3 * (n : ℚ) + 2) := by positivity
  rw [Int.floor_eq_iff, le_div_iff₀ hpos, div_lt_iff₀ hpos]
  exact ⟨h1, h2⟩

lemma closed (n : ℕ) (hn : 1 ≤ n) : 12 * a n = 9 * (n : ℤ) ^ 2 + 3 * n - 12 + 6 * ind n := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r := ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have hi : ind (4 * q + r) = if 2 ≤ r then 1 else 0 := by
    unfold ind; congr 1; simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  rw [hi]
  interval_cases r
  · have hq : 1 ≤ q := by omega
    have hq' : (1 : ℚ) ≤ q := by exact_mod_cast hq
    rw [floor_val _ (12 * (q : ℤ) ^ 2 + q - 1) (by push_cast; nlinarith) (by push_cast; nlinarith)]
    push_cast; ring_nf
  · have hq' : (0 : ℚ) ≤ q := by positivity
    rw [floor_val _ (12 * (q : ℤ) ^ 2 + 7 * q) (by push_cast; nlinarith) (by push_cast; nlinarith)]
    push_cast; ring_nf
  · have hq' : (0 : ℚ) ≤ q := by positivity
    rw [floor_val _ (12 * (q : ℤ) ^ 2 + 13 * q + 3) (by push_cast; nlinarith) (by push_cast; nlinarith)]
    push_cast; ring_nf
  · have hq' : (0 : ℚ) ≤ q := by positivity
    rw [floor_val _ (12 * (q : ℤ) ^ 2 + 19 * q + 7) (by push_cast; nlinarith) (by push_cast; nlinarith)]
    push_cast; ring_nf

lemma a_zero : a 0 = 0 := by simp [a]

lemma recur' (m : ℕ) : a (m + 6) - 3 * a (m + 5) + 4 * a (m + 4) - 4 * a (m + 3)
    + 3 * a (m + 2) - a (m + 1) = 0 := by
  have h6 := closed (m + 6) (by omega)
  have h5 := closed (m + 5) (by omega)
  have h4 := closed (m + 4) (by omega)
  have h3 := closed (m + 3) (by omega)
  have h2 := closed (m + 2) (by omega)
  have h1 := closed (m + 1) (Nat.le_add_left 1 m)
  have i3 := ind_add_two (m + 1)
  rw [show m + 1 + 2 = m + 3 by omega] at i3
  have i4 := ind_add_two (m + 2)
  rw [show m + 2 + 2 = m + 4 by omega] at i4
  have i5 := ind_add_two (m + 3)
  rw [show m + 3 + 2 = m + 5 by omega] at i5
  have i6 := ind_add_two (m + 4)
  rw [show m + 4 + 2 = m + 6 by omega] at i6
  rw [i6, i4] at h6
  rw [i5, i3] at h5
  rw [i4] at h4
  rw [i3] at h3
  push_cast at h6 h5 h4 h3 h2 h1
  have key : 12 * (a (m + 6) - 3 * a (m + 5) + 4 * a (m + 4) - 4 * a (m + 3) + 3 * a (m + 2)
      - a (m + 1)) = 0 := by
    linear_combination h6 - 3 * h5 + 4 * h4 - 4 * h3 + 3 * h2 - h1
  exact (mul_eq_zero.1 key).resolve_left (by norm_num)

lemma recur (n : ℕ) (hn : 6 ≤ n) : a n - 3*a (n-1) + 4*a (n-2) -
      4*a (n-3) + 3*a (n-4) - a (n-5) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 6 - 3 = m + 3 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e5 : m + 6 - 5 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  exact recur' m

end OMA.A024219

open PowerSeries OMA.S_oeis_a024219 in
theorem OMA.solution : type_of% @OMA.S_oeis_a024219.main := by
  refine ⟨OMA.A024219.recur, ?_⟩
  have hL : (1 + X ^ 2) * (1 - X) ^ 3 * F = F - (X ^ 1 * F + X ^ 1 * F + X ^ 1 * F)
      + (X ^ 2 * F + X ^ 2 * F + X ^ 2 * F + X ^ 2 * F)
      - (X ^ 3 * F + X ^ 3 * F + X ^ 3 * F + X ^ 3 * F)
      + (X ^ 4 * F + X ^ 4 * F + X ^ 4 * F) - X ^ 5 * F := by ring
  have hR : (3 : PowerSeries ℤ) * X ^ 2 - 2 * X ^ 3 + 3 * X ^ 4 - X ^ 5
      = (X ^ 2 + X ^ 2 + X ^ 2) - (X ^ 3 + X ^ 3) + (X ^ 4 + X ^ 4 + X ^ 4) - X ^ 5 := by ring
  have v1 : a 1 = 0 := by
    have := OMA.A024219.closed 1 le_rfl; simp [OMA.A024219.ind] at this; linarith
  have v2 : a 2 = 3 := by
    have := OMA.A024219.closed 2 (by norm_num); simp [OMA.A024219.ind] at this; linarith
  have v3 : a 3 = 7 := by
    have := OMA.A024219.closed 3 (by norm_num); simp [OMA.A024219.ind] at this; linarith
  have v4 : a 4 = 12 := by
    have := OMA.A024219.closed 4 (by norm_num); simp [OMA.A024219.ind] at this; linarith
  have v5 : a 5 = 19 := by
    have := OMA.A024219.closed 5 (by norm_num); simp [OMA.A024219.ind] at this; linarith
  rw [hL, hR]
  ext n
  simp only [map_sub, map_add, coeff_X_pow_mul', coeff_X_pow, F, coeff_mk]
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> simp [OMA.A024219.a_zero, v1, v2, v3, v4, v5]
  · have := OMA.A024219.recur n h
    simp [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      show n ≠ 5 by omega]
    linarith
