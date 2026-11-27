import OMAReductions.R_OeisA4290_conjecture_R1_H2_R1
import Mathlib

-- Step OeisA4290.conjecture.R1.H2.R1.H2: hypothesis H2 of reduction OeisA4290.conjecture.R1.H2.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Let `R L` be the repunit with `L` digits, so `9 R L = 10^L - 1`. From `9d ∣ 10^t - 1 = 9 R t`
we get `d ∣ R t`, so `m = 10^e R t` is a multiple of `10^e d`, hence of `n`; its digits are `e`
zeros and `t` ones, and `9 m ≤ 10^(9k) - 10` gives `m < (10^(9k) - 1) / 9`. -/

namespace P4A4290

/-- The repunit with `L` digits. -/
def R (L : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate L 1)

theorem R_succ (L : ℕ) : R (L + 1) = 1 + 10 * R L := by
  simp only [R, List.replicate_succ, Nat.ofDigits_cons]

theorem nine_R (L : ℕ) : 9 * R L + 1 = 10 ^ L := by
  induction L with
  | zero => simp [R]
  | succ L ih => rw [R_succ, pow_succ]; omega

theorem R_add (a b : ℕ) : R (a + b) = R a + 10 ^ a * R b := by
  simp only [R, List.replicate_add, Nat.ofDigits_append, List.length_replicate]

theorem R_pos (L : ℕ) (hL : 0 < L) : 0 < R L := by
  obtain ⟨L, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  rw [R_succ]; omega

theorem digits_R (L : ℕ) : Nat.digits 10 (R L) = List.replicate L 1 := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro l hl
    rw [List.eq_of_mem_replicate hl]; norm_num
  · intro h
    rw [List.getLast_replicate]; norm_num

theorem digits_shift (L e : ℕ) (hL : 0 < L) :
    ∀ x ∈ Nat.digits 10 (10 ^ e * R L), x = 0 ∨ x = 1 := by
  rw [Nat.digits_base_pow_mul (by norm_num) (R_pos L hL), digits_R]
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact Or.inl (List.eq_of_mem_replicate h)
  · exact Or.inr (List.eq_of_mem_replicate h)

theorem bound (L e k : ℕ) (he : 0 < e) (hle : L + e ≤ 9 * k) :
    10 ^ e * R L < (10 ^ (9 * k) - 1) / 9 := by
  have h1 : (10 ^ (9 * k) - 1) / 9 = R (9 * k) := by
    have := nine_R (9 * k)
    omega
  rw [h1]
  have h2 := nine_R L
  have h3 := nine_R (9 * k)
  have h4 : 10 ^ e * 10 ^ L ≤ 10 ^ (9 * k) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 10 ≤ 10 ^ e := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have h6 : 9 * (10 ^ e * R L) + 10 ^ e = 10 ^ e * 10 ^ L := by
    rw [← h2]; ring
  omega

theorem R_mul_modEq (d t : ℕ) (h : 10 ^ t ≡ 1 [MOD d]) (j : ℕ) :
    R (j * t) ≡ j * R t [MOD d] := by
  induction j with
  | zero => simp [R]; rfl
  | succ j ih =>
    rw [show (j + 1) * t = t + j * t by ring, R_add, show (j + 1) * R t = R t + j * R t by ring]
    have h2 : 10 ^ t * R (j * t) ≡ 1 * (j * R t) [MOD d] := Nat.ModEq.mul h ih
    rw [one_mul] at h2
    exact Nat.ModEq.add_left _ h2

end P4A4290

open P4A4290 in
theorem OMA.solution : OMA.R_OeisA4290_conjecture_R1_H2_R1.H2 := by
  intro k n d e t _ _ he ht hn hd hle
  have hR : d ∣ R t := by
    have h9 : 9 * R t = 10 ^ t - 1 := by have := nine_R t; omega
    rw [← h9] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
  refine ⟨10 ^ e * R t, bound t e k he hle, ?_, ?_, digits_shift _ e ht⟩
  · exact Nat.mul_pos (by positivity) (R_pos _ ht)
  · exact hn.trans (Nat.mul_dvd_mul_left _ hR)

