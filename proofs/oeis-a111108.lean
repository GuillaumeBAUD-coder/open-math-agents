import OMAStatements.S_oeis_a111108

namespace OMA.S_oeis_a111108

/-- Pell numbers, companion of A001333. -/
def pell : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pell (n + 1) + pell n

lemma step (n : ℕ) :
    A001333 (n + 1) = A001333 n + 2 * pell n ∧ pell (n + 1) = A001333 n + pell n := by
  induction n with
  | zero => simp [A001333, pell]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · rw [A001333, h1, h2]; ring
    · rw [pell, h1, h2]; ring

lemma Mpow (p : ℕ) (n : ℕ) :
    (!![1, 2; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ n =
      !![((A001333 n : ℤ) : ZMod p), 2 * ((pell n : ℤ) : ZMod p);
        ((pell n : ℤ) : ZMod p), ((A001333 n : ℤ) : ZMod p)] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A001333, pell]
  | succ n ih =>
    rw [pow_succ, ih]
    obtain ⟨h1, h2⟩ := step n
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, h1, h2] <;> ring

lemma Npow (p : ℕ) (k : ℕ) :
    (!![0, 2; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (2 * k + 1) =
      !![0, 2 ^ (k + 1); 2 ^ k, 0] := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, pow_succ, pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> ring

end OMA.S_oeis_a111108

open OMA.S_oeis_a111108 in
theorem OMA.solution : type_of% @OMA.S_oeis_a111108.main := by
  intro p hp hp2
  have := Fact.mk hp
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by
    have := hp.eq_two_or_odd.resolve_left hp2
    omega⟩
  have hsplit : (!![1, 2; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      1 + !![0, 2; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hfrob := add_pow_char_of_commute (R := Matrix (Fin 2) (Fin 2) (ZMod p)) p
    (Commute.one_left (!![0, 2; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)))
  rw [← hsplit, Mpow, one_pow] at hfrob
  have hA : ((A001333 p : ℤ) : ZMod p) = 1 := by
    have h00 := congrFun (congrFun hfrob 0) 0
    have hNp : (!![0, 2; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p =
        (!![0, 2; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (2 * k + 1) := by rw [← hk]
    rw [hNp, Npow] at h00
    simpa using h00
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have := hp.two_le
    omega
  have hferm : ((-2 : ℤ) : ZMod p) ^ (p - 1) = 1 := by
    rw [show p - 1 = 2 * k by omega, pow_mul]
    push_cast
    rw [neg_sq, ← pow_mul, show 2 * k = p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one h2
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold a
  push_cast at hferm ⊢
  rw [hA, hferm, sub_self]
