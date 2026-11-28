import OMAReductions.R_oeis_a000978_R1
import Mathlib

/-! Step H1 of the reduction R1 of OEIS A000978: the forward direction of the Vrba–Reix test.
For a prime `p > 3` with `W = (2^p + 1)/3` prime, `W ≡ 3 (mod 8)` makes `-2` a square and `2`
a non-square mod `W`; `W ≡ 1, 4 (mod 7)` and quadratic reciprocity make `7` a non-square, so
`14` is a square. With `r² = 14`, `s² = -2`, `c = (r + s)/4`, `d = (r - s)/4` we get `c d = 1`
and `c² + d² = 3/2`, so `S i = c^(2^(i+1)) + d^(2^(i+1))`; since `2^p = 3 (W - 1) + 2`, Fermat's
little theorem gives `S (p - 1) = c² + d² = S 0`. This is the classical direction, not progress
on the open converse. -/

namespace OMA.P_oeis_a000978_R1_H1

open OMA.S_oeis_a000978

lemma three_mul_W {p : ℕ} (hp : Odd p) : 3 * W p = 2 ^ p + 1 := by
  obtain ⟨k, rfl⟩ := hp
  have h4 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
  unfold W
  rw [h]
  omega

lemma S_formula {m : ℕ} {c d : ZMod m} (hcd : c * d = 1) (h0 : S m 0 = c ^ 2 + d ^ 2) :
    ∀ i, S m i = c ^ (2 ^ (i + 1)) + d ^ (2 ^ (i + 1)) := by
  intro i
  induction i with
  | zero => simpa using h0
  | succ i ih =>
    have hS : S m (i + 1) = S m i ^ 2 - 2 := rfl
    have hc : c ^ (2 ^ (i + 1 + 1)) = (c ^ (2 ^ (i + 1))) ^ 2 := by
      rw [← pow_mul, pow_succ 2 (i + 1)]
    have hd : d ^ (2 ^ (i + 1 + 1)) = (d ^ (2 ^ (i + 1))) ^ 2 := by
      rw [← pow_mul, pow_succ 2 (i + 1)]
    have hcd' : c ^ (2 ^ (i + 1)) * d ^ (2 ^ (i + 1)) = 1 := by
      rw [← mul_pow, hcd, one_pow]
    rw [hS, ih, hc, hd]
    linear_combination 2 * hcd'

end OMA.P_oeis_a000978_R1_H1

open OMA.S_oeis_a000978 OMA.P_oeis_a000978_R1_H1

theorem OMA.solution : OMA.R_oeis_a000978_R1.H1 := by
  intro p hp hp3 hWp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h3W := three_mul_W hodd
  set w := W p with hw
  have : Fact (Nat.Prime w) := ⟨hWp⟩
  -- residues of w
  have h8 : 2 ^ p % 8 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, p = j + 3 := ⟨p - 3, by omega⟩
    rw [pow_add]; norm_num [Nat.mul_mod_left]
  have hw8 : w % 8 = 3 := by omega
  have h32 : 32 ≤ 2 ^ p := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by obtain ⟨k, hk⟩ := hodd; omega)
  have hw11 : 11 ≤ w := by omega
  have hw7 : w % 7 = 1 ∨ w % 7 = 4 := by
    have hp3' : p % 3 ≠ 0 := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp (Nat.dvd_of_mod_eq_zero h)
      omega
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ p = 3 * q + r := ⟨p / 3, p % 3, Nat.mod_lt _ (by norm_num), by omega⟩
    have h87 : 8 ^ q % 7 = 1 := by rw [Nat.pow_mod]; norm_num
    have hpow : 2 ^ (3 * q + r) = 8 ^ q * 2 ^ r := by rw [pow_add, pow_mul]; norm_num
    have hr' : r = 1 ∨ r = 2 := by
      have : (3 * q + r) % 3 = r := by omega
      omega
    rw [hpow] at h3W
    rcases hr' with rfl | rfl
    · left
      have : 8 ^ q * 2 ^ 1 % 7 = 2 := by rw [Nat.mul_mod, h87]; norm_num
      omega
    · right
      have : 8 ^ q * 2 ^ 2 % 7 = 4 := by rw [Nat.mul_mod, h87]; norm_num
      omega
  -- squares mod w
  have hw2 : w ≠ 2 := by omega
  have hneg2 : IsSquare (-2 : ZMod w) := (ZMod.exists_sq_eq_neg_two_iff hw2).mpr (Or.inr hw8)
  have hn2 : ¬ IsSquare (2 : ZMod w) := by
    rw [ZMod.exists_sq_eq_two_iff hw2]; omega
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hn7 : ¬ IsSquare ((7 : ℕ) : ZMod w) := by
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (by omega) (by norm_num) (by omega),
      not_not, ← ZMod.natCast_mod]
    rcases hw7 with h | h
    · rw [h]; exact ⟨1, by norm_num⟩
    · rw [h]; exact ⟨2, by norm_num⟩
  have h14 : IsSquare (14 : ZMod w) := by
    have hl2 : legendreSym w 2 = -1 := (legendreSym.eq_neg_one_iff w).mpr (by exact_mod_cast hn2)
    have hl7 : legendreSym w 7 = -1 := (legendreSym.eq_neg_one_iff w).mpr (by exact_mod_cast hn7)
    have hl : legendreSym w 14 = 1 := by
      rw [show (14 : ℤ) = 2 * 7 by norm_num, legendreSym.mul, hl2, hl7]; norm_num
    have h0 : ((14 : ℤ) : ZMod w) ≠ 0 := by
      intro h
      have : ((14 : ℕ) : ZMod w) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      have hle := Nat.le_of_dvd (by norm_num) this
      obtain ⟨k, hk⟩ := this
      have h11 : w = 11 := by omega
      rw [h11] at hk
      omega
    exact_mod_cast (legendreSym.eq_one_iff w h0).mp hl
  obtain ⟨r, hr⟩ := h14
  obtain ⟨s, hs⟩ := hneg2
  have h2ne : (2 : ZMod w) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod w) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  set i : ZMod w := (2 : ZMod w)⁻¹ * (2 : ZMod w)⁻¹ with hi_def
  have hi : 4 * i = 1 := by
    rw [hi_def, show (4 : ZMod w) = 2 * 2 by norm_num]
    field_simp
  have hinv : (2 : ZMod w)⁻¹ = 2 * i := by
    rw [hi_def, ← mul_assoc, mul_inv_cancel₀ h2ne, one_mul]
  set c := (r + s) * i
  set d := (r - s) * i
  have hcd : c * d = 1 := by
    linear_combination (-(i ^ 2)) * hr + i ^ 2 * hs + (4 * i + 1) * hi
  have h0 : S w 0 = c ^ 2 + d ^ 2 := by
    show 3 * (2 : ZMod w)⁻¹ = c ^ 2 + d ^ 2
    rw [hinv]
    linear_combination (2 * i ^ 2) * hr + (2 * i ^ 2) * hs - 6 * i * hi
  have hF := S_formula hcd h0
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcd
  have hd0 : d ≠ 0 := right_ne_zero_of_mul_eq_one hcd
  have hexp : 2 ^ p = 3 * (w - 1) + 2 := by omega
  have hp1 : p - 1 + 1 = p := by omega
  rw [hF, hF 0, hp1, hexp, pow_add, pow_add, pow_mul', pow_mul',
    ZMod.pow_card_sub_one_eq_one hc0, ZMod.pow_card_sub_one_eq_one hd0]
  simp
