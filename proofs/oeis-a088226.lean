import OMAStatements.S_oeis_a088226
import Mathlib

namespace OMA.A088226proof

open OMA.S_oeis_a088226

/-- The value at offset `e` past the square `k * k`. -/
def f (k e : ℕ) : ℕ := if e % 2 = 0 then e / 2 else (2 * k + 1 - e) / 2

def B (x : ℕ) : ℕ := f (Nat.sqrt x) (x - Nat.sqrt x * Nat.sqrt x)

lemma B_kd (k d : ℕ) (hd : d ≤ 2 * k) : B (k * k + d) = f k d := by
  unfold B; rw [Nat.sqrt_add_eq k (by omega)]; congr 1; omega

lemma B_step (k d j : ℕ) (hd : d ≤ 2 * k) (hj : j ≤ 3) : B (k * k + d + j) =
    if d + j ≤ 2 * k then f k (d + j) else f (k + 1) (d + j - (2 * k + 1)) := by
  split_ifs with h
  · rw [add_assoc, B_kd _ _ h]
  · have e : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    rw [show k * k + d + j = (k + 1) * (k + 1) + (d + j - (2 * k + 1)) by omega,
      B_kd _ _ (by omega)]

lemma key' (k d : ℕ) (hd : d ≤ 2 * k) :
    (B (k * k + d + 3) : ℤ) = |(B (k * k + d + 2) : ℤ) - B (k * k + d + 1) - B (k * k + d + 0)| := by
  rw [B_step k d 3 hd (by norm_num), B_step k d 2 hd (by norm_num), B_step k d 1 hd (by norm_num),
    B_step k d 0 hd (by norm_num)]
  unfold f
  rw [eq_comm, abs_eq (by positivity)]
  split_ifs <;> omega

lemma key (x : ℕ) : (B (x + 3) : ℤ) = |(B (x + 2) : ℤ) - B (x + 1) - B x| := by
  have h1 := Nat.sqrt_le x
  have h2 := Nat.lt_succ_sqrt x
  have e : (Nat.sqrt x).succ * (Nat.sqrt x).succ = Nat.sqrt x * Nat.sqrt x + 2 * Nat.sqrt x + 1 := by
    simp only [Nat.succ_eq_add_one]; ring
  have := key' (Nat.sqrt x) (x - Nat.sqrt x * Nat.sqrt x) (by omega)
  rwa [show Nat.sqrt x * Nat.sqrt x + (x - Nat.sqrt x * Nat.sqrt x) = x by omega, add_zero] at this

lemma a_eq (x : ℕ) : a (x + 1) = B x ∧ a (x + 2) = B (x + 1) ∧ a (x + 3) = B (x + 2) := by
  induction x with
  | zero =>
    refine ⟨by decide, by decide, ?_⟩
    rw [show (0 : ℕ) + 2 = 1 * 1 + 1 by rfl, B_kd 1 1 (by norm_num)]; decide
  | succ x ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    rw [show x + 1 + 3 = x + 4 by ring, show a (x + 4) = |a (x + 3) - a (x + 2) - a (x + 1)| from rfl,
      h1, h2, h3, show x + 1 + 2 = x + 3 by ring, key]

lemma m_kd (k d : ℕ) (hd : d ≤ 2 * k) : m (k * k + d) = 2 * f k d := by
  unfold m
  apply IsLeast.csInf_eq
  have e1 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
  constructor
  · unfold f
    split_ifs with h
    · refine ⟨⟨d / 2, by omega⟩, k, ?_⟩
      unfold Nat.dist; rw [sq]; omega
    · refine ⟨⟨(2 * k + 1 - d) / 2, by omega⟩, k + 1, ?_⟩
      unfold Nat.dist; rw [sq]; omega
  · rintro y ⟨⟨r, hr⟩, s, hs⟩
    unfold Nat.dist at hs; rw [sq] at hs
    unfold f
    rcases Nat.lt_or_ge s k with h | h
    · have h3 := Nat.mul_le_mul (Nat.le_sub_one_of_lt h) (Nat.le_sub_one_of_lt h)
      have e2 : (k - 1) * (k - 1) + 2 * k = k * k + 1 := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring
      split_ifs <;> omega
    · rcases Nat.lt_or_ge s (k + 2) with h' | h'
      · obtain rfl | rfl : s = k ∨ s = k + 1 := by omega
        · split_ifs <;> omega
        · split_ifs <;> omega
      · have h3 := Nat.mul_le_mul h' h'
        have e2 : (k + 2) * (k + 2) = k * k + 4 * k + 4 := by ring
        split_ifs <;> omega

lemma m_eq (x : ℕ) : m x = 2 * B x := by
  have h1 := Nat.sqrt_le x
  have h2 := Nat.lt_succ_sqrt x
  have e : (Nat.sqrt x).succ * (Nat.sqrt x).succ = Nat.sqrt x * Nat.sqrt x + 2 * Nat.sqrt x + 1 := by
    simp only [Nat.succ_eq_add_one]; ring
  have := m_kd (Nat.sqrt x) (x - Nat.sqrt x * Nat.sqrt x) (by omega)
  rwa [show Nat.sqrt x * Nat.sqrt x + (x - Nat.sqrt x * Nat.sqrt x) = x by omega] at this

theorem a088226 : type_of% @OMA.S_oeis_a088226.main := by
  intro n hn
  obtain ⟨x, rfl⟩ : ∃ x, n = x + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, m_eq, Nat.mul_div_cancel_left _ (by norm_num)]
  exact (a_eq x).1

end OMA.A088226proof

theorem OMA.solution : type_of% @OMA.S_oeis_a088226.main := OMA.A088226proof.a088226
