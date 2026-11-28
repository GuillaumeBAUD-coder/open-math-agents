import OMAStatements.S_oeis_a374105
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: 13 divides 9^k+3^k+1 only when 3 does not divide k. If k = m*q with 2 <= m < k,
-- then x^2+x+1 divides x^(2q)+x^q+1 for x = 3^m (since x^3 = 1 modulo x^2+x+1 and 3 does not divide q),
-- and 13 divides 9^m+3^m+1, which lies strictly between 13 and 13p, contradicting primality of p.

namespace OMA.A374105Proof

theorem key (x q : ℕ) (hq : ¬ 3 ∣ q) : x ^ 2 + x + 1 ∣ x ^ (2 * q) + x ^ q + 1 := by
  have h : ((x:ℤ))^3 ≡ 1 [ZMOD ((x:ℤ)^2 + x + 1)] :=
    Int.modEq_iff_dvd.mpr ⟨1 - x, by ring⟩
  have hr : q % 3 = 1 ∨ q % 3 = 2 := by omega
  have hq' : q = 3 * (q / 3) + q % 3 := (Nat.div_add_mod q 3).symm
  set t := q / 3
  rw [← Int.natCast_dvd_natCast]
  push_cast
  rcases hr with hr | hr
  · rw [hq', hr]
    have e : ((x:ℤ)) ^ (2 * (3 * t + 1)) + (x:ℤ) ^ (3 * t + 1) + 1
        = ((x:ℤ)^3)^(2*t) * x^2 + ((x:ℤ)^3)^t * x + 1 := by ring
    rw [e]
    have := (((h.pow (2*t)).mul_right ((x:ℤ)^2)).add ((h.pow t).mul_right (x:ℤ))).add_right 1
    simp only [one_pow, one_mul] at this
    have h2 : ((x:ℤ)^2 + x + 1) ≡ 0 [ZMOD ((x:ℤ)^2 + x + 1)] := Int.emod_self.trans (by simp)
    exact Int.ModEq.dvd ((this.trans h2).symm) |> fun d => by simpa using d
  · rw [hq', hr]
    have e : ((x:ℤ)) ^ (2 * (3 * t + 2)) + (x:ℤ) ^ (3 * t + 2) + 1
        = ((x:ℤ)^3)^(2*t+1) * x + ((x:ℤ)^3)^t * x^2 + 1 := by ring
    rw [e]
    have := (((h.pow (2*t+1)).mul_right ((x:ℤ))).add ((h.pow t).mul_right ((x:ℤ)^2))).add_right 1
    simp only [one_pow, one_mul] at this
    have h2 : ((x:ℤ) + x^2 + 1) ≡ 0 [ZMOD ((x:ℤ)^2 + x + 1)] := by
      have : (x:ℤ) + x^2 + 1 = ((x:ℤ)^2 + x + 1) := by ring
      rw [this]; exact Int.emod_self.trans (by simp)
    exact Int.ModEq.dvd ((this.trans h2).symm) |> fun d => by simpa using d

theorem main_proof : ∀ k p : ℕ, p.Prime → 9 ^ k + 3 ^ k + 1 = 13 * p → k.Prime := by
  intro k p hp hk
  have h3 : ¬ 3 ∣ k := by
    rintro ⟨j, rfl⟩
    have : (9 ^ (3 * j) + 3 ^ (3 * j) + 1) % 13 = 3 := by
      rw [pow_mul, pow_mul, Nat.add_mod, Nat.add_mod ((9^3) ^ j), Nat.pow_mod, Nat.pow_mod (3^3)]
      norm_num
    omega
  by_contra hnp
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · omega
    · have : p = 1 := by omega
      exact absurd this hp.one_lt.ne'
    · omega
  obtain ⟨m, hm, hm1, hmk⟩ := (Nat.not_prime_iff_exists_dvd_lt hk2).mp hnp
  obtain ⟨q, rfl⟩ := hm
  have hq : ¬ 3 ∣ q := fun h => h3 (dvd_mul_of_dvd_right h m)
  have hd := key (3 ^ m) q hq
  have e1 : (3 ^ m) ^ (2 * q) + (3 ^ m) ^ q + 1 = 9 ^ (m * q) + 3 ^ (m * q) + 1 := by
    rw [← pow_mul, ← pow_mul, show (9:ℕ) = 3 ^ 2 by norm_num, ← pow_mul]; ring_nf
  rw [e1, hk] at hd
  have hm3 : ¬ 3 ∣ m := fun h => h3 (dvd_mul_of_dvd_left h q)
  have h13 : 13 ∣ (3 ^ m) ^ 2 + 3 ^ m + 1 := by
    have := key 3 m hm3
    rw [← pow_mul, mul_comm 2 m] at *
    simpa [pow_mul] using this
  -- (3^m)^2+3^m+1 divides 13 p
  have hq1 : 2 ≤ q := by
    rcases q with _ | _ | q
    · simp at hk2
    · simp at hmk
    · omega
  have hlt : (3 ^ m) ^ 2 + 3 ^ m + 1 < 13 * p := by
    rw [← hk]
    have : 3 ^ m < 3 ^ (m * q) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
    have h9 : (3 ^ m) ^ 2 < 9 ^ (m * q) := by
      rw [← pow_mul, show (9:ℕ) = 3 ^ 2 by norm_num, ← pow_mul]
      exact Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
    omega
  have hgt : 13 < (3 ^ m) ^ 2 + 3 ^ m + 1 := by
    have : 9 ≤ 3 ^ m := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    nlinarith
  obtain ⟨c, hc⟩ := h13
  rw [hc] at hd hlt hgt
  have hcp : c ∣ p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
  rcases (Nat.dvd_prime hp).mp hcp with rfl | rfl <;> omega

end OMA.A374105Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a374105.main := OMA.A374105Proof.main_proof
