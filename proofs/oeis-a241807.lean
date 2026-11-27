import OMAStatements.S_oeis_a241807
import Mathlib

/-!
Let X = n^2+n+2 and Y = (n+1)(n+2)(n+3). The resultant identity
(4n^2+28n+56) X - (4n+8) Y = 64 shows gcd(X, Y) divides 64, so gcd(X, Y) only depends on
n mod 64, and a finite check of the 64 residues gives gcd(X, Y) = per(n). The numerator of X/Y
is X / gcd(X, Y).
-/

namespace R241807
open OMA.S_oeis_a241807

theorem g_dvd (n : ℕ) : Nat.gcd (n ^ 2 + n + 2) ((n + 1) * (n + 2) * (n + 3)) ∣ 64 := by
  have h1 := Nat.gcd_dvd_left (n ^ 2 + n + 2) ((n + 1) * (n + 2) * (n + 3))
  have h2 := Nat.gcd_dvd_right (n ^ 2 + n + 2) ((n + 1) * (n + 2) * (n + 3))
  generalize Nat.gcd (n ^ 2 + n + 2) ((n + 1) * (n + 2) * (n + 3)) = g at h1 h2 ⊢
  have i1 : (g : ℤ) ∣ ((n ^ 2 + n + 2 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h1
  have i2 : (g : ℤ) ∣ (((n + 1) * (n + 2) * (n + 3) : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h2
  have i3 : (g : ℤ) ∣ (4 * (n : ℤ) ^ 2 + 28 * n + 56) * ((n ^ 2 + n + 2 : ℕ) : ℤ) -
      (4 * (n : ℤ) + 8) * (((n + 1) * (n + 2) * (n + 3) : ℕ) : ℤ) :=
    dvd_sub (dvd_mul_of_dvd_right i1 _) (dvd_mul_of_dvd_right i2 _)
  have e : (4 * (n : ℤ) ^ 2 + 28 * n + 56) * ((n ^ 2 + n + 2 : ℕ) : ℤ) -
      (4 * (n : ℤ) + 8) * (((n + 1) * (n + 2) * (n + 3) : ℕ) : ℤ) = ((64 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [e] at i3
  exact Int.natCast_dvd_natCast.mp i3

theorem gcd_reduce (X Y : ℕ) (hd : Nat.gcd X Y ∣ 64) :
    Nat.gcd X Y = Nat.gcd (X % 64) (Nat.gcd (Y % 64) 64) := by
  rw [← Nat.gcd_eq_left hd, Nat.gcd_assoc]
  have e1 : Nat.gcd Y 64 = Nat.gcd (Y % 64) 64 := (Nat.gcd_comm Y 64).trans (Nat.gcd_rec 64 Y)
  rw [e1]
  have hz : Nat.gcd (Y % 64) 64 ∣ 64 := Nat.gcd_dvd_right _ _
  generalize Nat.gcd (Y % 64) 64 = z at hz ⊢
  calc Nat.gcd X z = Nat.gcd (X % z) z := (Nat.gcd_comm X z).trans (Nat.gcd_rec z X)
    _ = Nat.gcd (X % 64 % z) z := by rw [Nat.mod_mod_of_dvd X hz]
    _ = Nat.gcd (X % 64) z := ((Nat.gcd_comm _ z).trans (Nat.gcd_rec z _)).symm

theorem modA (n : ℕ) : ((n % 64) ^ 2 + n % 64 + 2) % 64 = (n ^ 2 + n + 2) % 64 := by
  have h : n % 64 ≡ n [MOD 64] := Nat.mod_modEq n 64
  exact ((h.pow 2).add h).add_right 2

theorem modB (n : ℕ) :
    ((n % 64 + 1) * (n % 64 + 2) * (n % 64 + 3)) % 64 = ((n + 1) * (n + 2) * (n + 3)) % 64 := by
  have h : n % 64 ≡ n [MOD 64] := Nat.mod_modEq n 64
  exact ((h.add_right 1).mul (h.add_right 2)).mul (h.add_right 3)

theorem fin_check : ∀ r < 64,
    ((Nat.gcd ((r ^ 2 + r + 2) % 64) (Nat.gcd (((r + 1) * (r + 2) * (r + 3)) % 64) 64) : ℕ) : ℤ)
      = per r := by
  decide +kernel

theorem main' (n : ℕ) : (a n : ℚ) = (A014206 n : ℚ) / (per n : ℚ) := by
  have hXpos : 0 < n ^ 2 + n + 2 := by positivity
  have hYpos : 0 < (n + 1) * (n + 2) * (n + 3) := by positivity
  have hgpos : 0 < Nat.gcd (n ^ 2 + n + 2) ((n + 1) * (n + 2) * (n + 3)) :=
    Nat.gcd_pos_of_pos_left _ hXpos
  have hgX := Nat.gcd_dvd_left (n ^ 2 + n + 2) ((n + 1) * (n + 2) * (n + 3))
  have hgY := Nat.gcd_dvd_right (n ^ 2 + n + 2) ((n + 1) * (n + 2) * (n + 3))
  have hcop := Nat.coprime_div_gcd_div_gcd hgpos
  have hper : per n = ((Nat.gcd (n ^ 2 + n + 2) ((n + 1) * (n + 2) * (n + 3)) : ℕ) : ℤ) := by
    rw [gcd_reduce _ _ (g_dvd n), ← modA n, ← modB n, fin_check (n % 64) (Nat.mod_lt n (by norm_num))]
    unfold per
    rw [Nat.mod_mod_of_dvd n (by norm_num : 16 ∣ 64)]
  generalize Nat.gcd (n ^ 2 + n + 2) ((n + 1) * (n + 2) * (n + 3)) = g at hgpos hgX hgY hper hcop
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hc : c n = ((((n ^ 2 + n + 2) / g : ℕ) : ℤ) : ℚ) /
      ((((n + 1) * (n + 2) * (n + 3) / g : ℕ) : ℤ) : ℚ) := by
    rw [Int.cast_natCast, Int.cast_natCast, Nat.cast_div hgX hg0, Nat.cast_div hgY hg0,
      div_div_div_cancel_right₀ hg0]
    unfold c
    push_cast <;> ring
  have hnum : a n = (((n ^ 2 + n + 2) / g : ℕ) : ℤ) := by
    unfold a
    rw [hc]
    apply Rat.num_div_eq_of_coprime
    · exact Int.natCast_pos.mpr (Nat.div_pos (Nat.le_of_dvd hYpos hgY) hgpos)
    · simpa only [Int.natAbs_natCast] using hcop
  rw [hnum, hper, Int.cast_natCast, Int.cast_natCast, Nat.cast_div hgX hg0]
  unfold A014206
  push_cast <;> ring

end R241807

theorem OMA.solution : type_of% @OMA.S_oeis_a241807.main := by
  intro n
  exact R241807.main' n
