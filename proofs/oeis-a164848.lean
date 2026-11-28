import OMAStatements.S_oeis_a164848

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: b(n+1) - b(n+2) = n / D with D = (n+2)(n+3)(n+4) = n(n^2+9n+26) + 24, so
-- gcd(n, D) = gcd(n, 24) and the reduced numerator is A051712(n+1) = n / gcd(n, 24).
-- Hence a(n) = (n / gcd(n,2)) / (n / gcd(n,24)) = gcd(n,24) / gcd(n,2), which has period 24.

namespace OMA.A164848Proof

open OMA.S_oeis_a164848

lemma diff_eq (n : ℕ) : b (n + 1) - b (n + 1 + 1) =
    ((n : ℤ) : ℚ) / (((n + 2) * (n + 3) * (n + 4) : ℕ) : ℤ) := by
  unfold b
  push_cast
  field_simp
  ring

lemma gcd_D (n : ℕ) : Nat.gcd n ((n + 2) * (n + 3) * (n + 4)) = Nat.gcd n 24 := by
  have : (n + 2) * (n + 3) * (n + 4) = 24 + n * (n ^ 2 + 9 * n + 26) := by ring
  rw [this, Nat.gcd_add_mul_left_right]

lemma num_eq (n : ℕ) : A051712 (n + 1) = ((n / Nat.gcd n 24 : ℕ) : ℤ) := by
  unfold A051712
  rw [diff_eq]
  set D := (n + 2) * (n + 3) * (n + 4) with hD
  set g := Nat.gcd n D with hg
  have hDpos : 0 < D := by positivity
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hDpos
  have hgn : g ∣ n := Nat.gcd_dvd_left _ _
  have hgD : g ∣ D := Nat.gcd_dvd_right _ _
  have hq : ((n : ℤ) : ℚ) / ((D : ℤ) : ℚ) = (((n / g : ℕ) : ℤ) : ℚ) / (((D / g : ℕ) : ℤ) : ℚ) := by
    have h1 : (((n / g : ℕ) : ℤ) : ℚ) = (n : ℚ) / g := by
      rw [Int.cast_natCast, Nat.cast_div hgn (by exact_mod_cast hgpos.ne')]
    have h2 : (((D / g : ℕ) : ℤ) : ℚ) = (D : ℚ) / g := by
      rw [Int.cast_natCast, Nat.cast_div hgD (by exact_mod_cast hgpos.ne')]
    rw [h1, h2]
    have : (g : ℚ) ≠ 0 := by exact_mod_cast hgpos.ne'
    push_cast
    field_simp
  rw [hq, Rat.num_div_eq_of_coprime]
  · rw [hg, gcd_D]
  · have : 0 < D / g := Nat.div_pos (Nat.le_of_dvd hDpos hgD) hgpos
    exact_mod_cast this
  · rw [Int.natAbs_natCast, Int.natAbs_natCast]
    exact Nat.coprime_div_gcd_div_gcd hgpos

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = ((Nat.gcd n 24 / Nat.gcd n 2 : ℕ) : ℤ) := by
  unfold a A026741
  rw [num_eq]
  have h2 : Nat.gcd n 2 ∣ Nat.gcd n 24 := Nat.gcd_dvd_gcd_of_dvd_right _ (by norm_num)
  have h24 : Nat.gcd n 24 ∣ n := Nat.gcd_dvd_left _ _
  have hpos : 0 < n / Nat.gcd n 24 := Nat.div_pos (Nat.le_of_dvd hn h24) (Nat.gcd_pos_of_pos_right _ (by norm_num))
  have key : n / Nat.gcd n 2 = n / Nat.gcd n 24 * (Nat.gcd n 24 / Nat.gcd n 2) := by
    rw [← Nat.mul_div_assoc _ h2, Nat.div_mul_cancel h24]
  rw [key]
  push_cast
  rw [Int.mul_ediv_cancel_left]
  exact_mod_cast hpos.ne'

end OMA.A164848Proof

open OMA.S_oeis_a164848 OMA.A164848Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a164848.main := by
  intro n hn
  rw [a_eq n hn, a_eq (n + 24) (by omega)]
  have e1 : Nat.gcd (n + 24) 24 = Nat.gcd n 24 := by
    rw [Nat.gcd_comm, Nat.gcd_add_self_right, Nat.gcd_comm]
  have e2 : Nat.gcd (n + 24) 2 = Nat.gcd n 2 := by
    rw [Nat.gcd_comm, show n + 24 = n + 2 * 12 by ring, Nat.gcd_add_mul_left_right, Nat.gcd_comm]
  rw [e1, e2]
