import OMAStatements.S_mse_4930059
import Mathlib

-- Problem: Infinite chains of primes with p(n+1) = 2p(n) - 1 or p(n+1) = 2p(n) + 1
-- Credit: @xor2k
-- The sequence is strictly increasing, so q = p 2 is at least 5. From index 2 on no term is
-- divisible by 3, which forces the same residue mod 3, hence the same sign, at every step.
-- So p (2+j) = 2^j (q - 1) + 1 or p (2+j) + 1 = 2^j (q + 1). Fermat's little theorem at
-- j = q - 1 gives q ∣ p (q + 1), a prime larger than q: contradiction.

open OMA.S_mse_4930059

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_4930059.main) := by
  rintro ⟨p, hp, hrec⟩
  have hge : ∀ n, 2 ≤ p n := fun n => (hp n).two_le
  have hlt : ∀ n, p n < p (n + 1) := fun n => by
    have := hge n; rcases hrec n with h | h <;> omega
  have hmono : StrictMono p := strictMono_nat_of_lt_succ hlt
  have hbig : ∀ n, n + 2 ≤ p n := by
    intro n; induction n with
    | zero => exact hge 0
    | succ k ih => have := hlt k; omega
  have h3 : ∀ j, ¬ 3 ∣ p (2 + j) := by
    intro j hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (hp (2 + j))).1 hd
    have := hbig (2 + j); omega
  set q := p 2 with hq
  have hq5 : 5 ≤ q := by
    have := hbig 2
    have h32 := h3 0
    simp only [Nat.add_zero] at h32
    rcases (show q = 4 ∨ 5 ≤ q by omega) with h | h
    · have h4 := hp 2
      rw [← hq, h] at h4
      norm_num at h4
    · exact h
  have hmod : ∀ j, p (2 + j) % 3 = q % 3 := by
    intro j; induction j with
    | zero => rfl
    | succ k ih =>
      have a := h3 k; have b := h3 (k + 1); have c := hrec (2 + k)
      rw [show 2 + (k + 1) = 2 + k + 1 by omega] at b ⊢
      rw [Nat.dvd_iff_mod_eq_zero] at a b
      rw [← ih]
      rcases (show p (2 + k) % 3 = 1 ∨ p (2 + k) % 3 = 2 by omega) with h1 | h1 <;>
        rcases c with c | c <;> omega
  have : Fact q.Prime := ⟨hp 2⟩
  have h2ne : (2 : ZMod q) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this; omega
  have hferm : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hqz : ((q : ℕ) : ZMod q) = 0 := ZMod.natCast_self q
  have hdiv : q ∣ p (2 + (q - 1)) := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h30 : q % 3 ≠ 0 := by have := h3 0; simp only [Nat.add_zero] at this; omega
    rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with h1 | h1
    · have key : ∀ j, p (2 + j) = 2 ^ j * (q - 1) + 1 := by
        intro j; induction j with
        | zero => simp only [Nat.add_zero, pow_zero, one_mul]; omega
        | succ k ih =>
          have a := hmod k; have b := hmod (k + 1); have c := hrec (2 + k)
          rw [show 2 + (k + 1) = 2 + k + 1 by omega] at b ⊢
          have hk : p (2 + k + 1) = 2 * p (2 + k) - 1 := by rcases c with c | c <;> omega
          rw [hk, ih, pow_succ]
          have : 1 ≤ 2 ^ k * (q - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))
          rw [show 2 ^ k * 2 * (q - 1) = 2 * (2 ^ k * (q - 1)) by ring]
          omega
      rw [key, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega), hqz, Nat.cast_ofNat, hferm]
      push_cast; ring
    · have key : ∀ j, p (2 + j) + 1 = 2 ^ j * (q + 1) := by
        intro j; induction j with
        | zero => simp only [Nat.add_zero, pow_zero, one_mul]; omega
        | succ k ih =>
          have a := hmod k; have b := hmod (k + 1); have c := hrec (2 + k)
          rw [show 2 + (k + 1) = 2 + k + 1 by omega] at b ⊢
          have hk : p (2 + k + 1) = 2 * p (2 + k) + 1 := by rcases c with c | c <;> omega
          rw [hk, pow_succ, show 2 ^ k * 2 * (q + 1) = 2 * (2 ^ k * (q + 1)) by ring, ← ih]
          ring
      have := congrArg (fun x : ℕ => (x : ZMod q)) (key (q - 1))
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, hqz, Nat.cast_ofNat, hferm] at this
      have e : ((p (2 + (q - 1)) : ℕ) : ZMod q) = 1 * (0 + 1) - 1 := by
        rw [← this]; ring
      rw [e]; ring
  have hgt : q < p (2 + (q - 1)) := hmono (by omega)
  rcases (Nat.dvd_prime (hp (2 + (q - 1)))).1 hdiv with h | h <;> omega
