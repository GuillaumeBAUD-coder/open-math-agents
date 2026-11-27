import OMAStatements.S_oeis_a337951

-- Problem: oeis-a337951
-- Credit: @anmolspace
-- Proof: 4^k mod 5 = 1 + 3 (k mod 2) (induction); the exponents n(n-1)/2 and n(n+1)/2 are rewritten explicitly for
-- n = 2m+1, 4m+2, 4m+4 and their parities computed, giving the residues term by term.

namespace OMA.PTri
lemma par_succ (m : ℕ) : (m + 1) % 2 = 1 - m % 2 := by omega
lemma par41 (m : ℕ) : (4 * m + 1) % 2 = 1 := by omega
lemma par43 (m : ℕ) : (4 * m + 3) % 2 = 1 := by omega
lemma pm1 (x y : ℕ) (hx : x % 2 = 1) : (x * y) % 2 = y % 2 := by
  rw [Nat.mul_mod, hx, one_mul, Nat.mod_mod]
lemma pm0 (x y : ℕ) (hx : x % 2 = 0) : (x * y) % 2 = 0 := by
  rw [Nat.mul_mod, hx, zero_mul, Nat.zero_mod]
lemma p5 (k : ℕ) : 4 ^ k % 5 = 1 + 3 * (k % 2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih, show (4 : ℕ) % 5 = 4 from rfl]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> omega
lemma e_odd1 (m : ℕ) : (2 * m + 1) * (2 * m + 1 - 1) / 2 = (2 * m + 1) * m := by
  rw [show 2 * m + 1 - 1 = 2 * m by omega,
    show (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
lemma e_odd2 (m : ℕ) : (2 * m + 1) * (2 * m + 1 + 1) / 2 = (2 * m + 1) * (m + 1) := by
  rw [show (2 * m + 1) * (2 * m + 1 + 1) = 2 * ((2 * m + 1) * (m + 1)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
lemma e_42a (m : ℕ) : (4 * m + 2) * (4 * m + 2 - 1) / 2 = (2 * m + 1) * (4 * m + 1) := by
  rw [show 4 * m + 2 - 1 = 4 * m + 1 by omega,
    show (4 * m + 2) * (4 * m + 1) = 2 * ((2 * m + 1) * (4 * m + 1)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
lemma e_42b (m : ℕ) : (4 * m + 2) * (4 * m + 2 + 1) / 2 = (2 * m + 1) * (4 * m + 3) := by
  rw [show (4 * m + 2) * (4 * m + 2 + 1) = 2 * ((2 * m + 1) * (4 * m + 3)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
lemma e_44a (m : ℕ) : (4 * m + 4) * (4 * m + 4 - 1) / 2 = (2 * m + 2) * (4 * m + 3) := by
  rw [show 4 * m + 4 - 1 = 4 * m + 3 by omega,
    show (4 * m + 4) * (4 * m + 3) = 2 * ((2 * m + 2) * (4 * m + 3)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
lemma e_44b (m : ℕ) : (4 * m + 4) * (4 * m + 4 + 1) / 2 = (2 * m + 2) * (4 * m + 5) := by
  rw [show (4 * m + 4) * (4 * m + 4 + 1) = 2 * ((2 * m + 2) * (4 * m + 5)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
end OMA.PTri

theorem OMA.solution : type_of% @OMA.S_oeis_a337951.main := by
  intro m
  simp only [Nat.ModEq, OMA.S_oeis_a337951.a, if_neg (show 2 * m + 1 ≠ 0 by omega),
    if_neg (show 4 * m + 2 ≠ 0 by omega), if_neg (show 4 * m + 4 ≠ 0 by omega),
    OMA.PTri.e_odd1, OMA.PTri.e_odd2, OMA.PTri.e_42a, OMA.PTri.e_42b, OMA.PTri.e_44a,
    OMA.PTri.e_44b]
  have q1 : ((2 * m + 1) * m) % 2 = m % 2 := OMA.PTri.pm1 _ _ (by omega)
  have q2 : ((2 * m + 1) * (m + 1)) % 2 = (m + 1) % 2 := OMA.PTri.pm1 _ _ (by omega)
  have q3 : ((2 * m + 1) * (4 * m + 1)) % 2 = (4 * m + 1) % 2 := OMA.PTri.pm1 _ _ (by omega)
  have q4 : ((2 * m + 1) * (4 * m + 3)) % 2 = (4 * m + 3) % 2 := OMA.PTri.pm1 _ _ (by omega)
  have q5 : ((2 * m + 2) * (4 * m + 3)) % 2 = 0 := OMA.PTri.pm0 _ _ (by omega)
  have q6 : ((2 * m + 2) * (4 * m + 5)) % 2 = 0 := OMA.PTri.pm0 _ _ (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_mod, OMA.PTri.p5, OMA.PTri.p5, q1, q2, OMA.PTri.par_succ]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h]
  · rw [Nat.add_mod, OMA.PTri.p5, OMA.PTri.p5, q3, q4, OMA.PTri.par41, OMA.PTri.par43]
  · rw [Nat.add_mod, OMA.PTri.p5, OMA.PTri.p5, q5, q6]
