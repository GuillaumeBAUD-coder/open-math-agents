import OMAStatements.S_oeis_a086004
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open OMA.S_oeis_a086004

-- R. J. Mathar's block factorization from OEIS A086004, Conjecture 1.
theorem OMA.solution : type_of% @OMA.S_oeis_a086004.main := by
  rintro p hp ⟨h, hh⟩
  have hd : numDigits p = 2*h := by omega
  have hpos : 0 < h := by
    by_contra! h0
    have e : (Nat.digits 10 p).length = 0 := by change numDigits p = 0; omega
    exact hp.ne_zero (Nat.digits_eq_nil_iff_eq_zero.1 (List.length_eq_zero_iff.1 e))
  let B : ℕ := 10^h
  have large : 10 ≤ B := Nat.le_self_pow (by omega) _
  have notB : ¬ B.Prime := by
    intro pr
    have dv : 2 ∣ B := dvd_trans (by decide : 2 ∣ 10) (dvd_pow_self 10 hpos.ne')
    have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two pr).1 dv
    omega
  have decomp := Nat.mod_add_div p B
  have sumgt : 1 < p%B + p/B := by
    by_contra! hsmall
    have small (a b : ℕ) (u : a+b ≤ 1) : b = 0 ∨ (a = 0 ∧ b = 1) := by omega
    rcases small _ _ hsmall with hzero | ⟨hr,hq⟩
    · rw [hzero, Nat.mul_zero, Nat.add_zero] at decomp
      have := hp.one_lt
      omega
    · rw [hq, hr, Nat.mul_one, Nat.zero_add] at decomp
      exact notB (decomp.symm ▸ hp)
  have rot_eq : rot p = p%B * B + p/B := by
    dsimp only [rot]
    rw [hd, show 2*h/2 = h by omega, show 2*h-h = h by omega, Nat.sub_self]
    simp [B, Nat.mod_one]
  have fact : p + rot p = (B+1)*(p%B+p/B) := by
    rw [rot_eq]
    calc
      _ = (p%B+B*(p/B))+(p%B*B+p/B) := by rw [decomp]
      _ = _ := by ring
  rw [fact]
  exact Nat.not_prime_mul (by omega) (by omega)
