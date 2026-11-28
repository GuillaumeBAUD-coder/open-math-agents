import OMAStatements.S_oeis_a111002
import Mathlib

namespace OMA.P111002

open OMA.S_oeis_a111002

/-- gcd(n^2 - n + 1, n^2 + 3n + 3) is 7 when n = 3 mod 7 and 1 otherwise. -/
lemma gcd_BC (n : ℕ) :
    Int.gcd ((n : ℤ) ^ 2 - n + 1) ((n : ℤ) ^ 2 + 3 * n + 3) = if n % 7 = 3 then 7 else 1 := by
  have h1 : ((Int.gcd ((n : ℤ) ^ 2 - n + 1) ((n : ℤ) ^ 2 + 3 * n + 3) : ℕ) : ℤ) ∣ (n : ℤ) ^ 2 - n + 1 :=
    Int.gcd_dvd_left _ _
  have h2 : ((Int.gcd ((n : ℤ) ^ 2 - n + 1) ((n : ℤ) ^ 2 + 3 * n + 3) : ℕ) : ℤ) ∣ (n : ℤ) ^ 2 + 3 * n + 3 :=
    Int.gcd_dvd_right _ _
  generalize hg : Int.gcd ((n : ℤ) ^ 2 - n + 1) ((n : ℤ) ^ 2 + 3 * n + 3) = G at h1 h2
  have h14 : (G : ℤ) ∣ 14 := by
    have e : (14 : ℤ) = (2 * (n : ℤ) + 5) * ((n : ℤ) ^ 2 - n + 1)
        - (2 * (n : ℤ) - 3) * ((n : ℤ) ^ 2 + 3 * n + 3) := by ring
    rw [e]
    exact dvd_sub (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _)
  have hodd : ¬ (2 : ℤ) ∣ (n : ℤ) ^ 2 - n + 1 := by
    obtain ⟨r, hr⟩ := Int.even_mul_succ_self ((n : ℤ) - 1)
    have hB : (n : ℤ) ^ 2 - n + 1 = r + r + 1 := by linear_combination hr
    rw [hB]
    omega
  have hG2 : ¬ 2 ∣ G := by
    intro h
    apply hodd
    have h' : (2 : ℤ) ∣ (G : ℤ) := by exact_mod_cast h
    exact dvd_trans h' h1
  have hG14 : G ∣ 14 := by exact_mod_cast h14
  have hG7 : G ∣ 7 := by
    have hc : Nat.Coprime G 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hG2)
    exact hc.dvd_of_dvd_mul_left (by simpa using hG14)
  have hcase : G = 1 ∨ G = 7 := (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hG7
  split_ifs with h
  · -- n = 3 mod 7: 7 divides both numbers
    obtain ⟨q, hq⟩ : ∃ q : ℤ, (n : ℤ) = 7 * q + 3 := ⟨(n : ℤ) / 7, by omega⟩
    have d1 : (7 : ℤ) ∣ (n : ℤ) ^ 2 - n + 1 := ⟨7 * q ^ 2 + 5 * q + 1, by rw [hq]; ring⟩
    have d2 : (7 : ℤ) ∣ (n : ℤ) ^ 2 + 3 * n + 3 := ⟨7 * q ^ 2 + 9 * q + 3, by rw [hq]; ring⟩
    have d3 : (7 : ℤ) ∣ ((Int.gcd ((n : ℤ) ^ 2 - n + 1) ((n : ℤ) ^ 2 + 3 * n + 3) : ℕ) : ℤ) :=
      Int.dvd_coe_gcd d1 d2
    rw [hg] at d3
    rcases hcase with h1' | h7
    · rw [h1'] at d3
      norm_num at d3
    · exact h7
  · rcases hcase with h1' | h7
    · exact h1'
    · exfalso
      rw [h7] at h1 h2
      have d : (7 : ℤ) ∣ ((n : ℤ) ^ 2 + 3 * n + 3) - ((n : ℤ) ^ 2 - n + 1) := dvd_sub (by exact_mod_cast h2) (by exact_mod_cast h1)
      have e : ((n : ℤ) ^ 2 + 3 * n + 3) - ((n : ℤ) ^ 2 - n + 1) = 4 * (n : ℤ) + 2 := by ring
      rw [e] at d
      omega

/-- The closed form of the sequence. -/
lemma a_closed (n : ℕ) : a n = (n ^ 2 + n + 1) * (if n % 7 = 3 then 7 else 1) := by
  have e1 : ((n ^ 4 + n ^ 2 + 1 : ℕ) : ℤ)
      = (((n ^ 2 + n + 1 : ℕ)) : ℤ) * ((n : ℤ) ^ 2 - n + 1) := by
    push_cast
    ring
  have e2 : (((n + 1) ^ 4 + (n + 1) ^ 2 + 1 : ℕ) : ℤ)
      = (((n ^ 2 + n + 1 : ℕ)) : ℤ) * ((n : ℤ) ^ 2 + 3 * n + 3) := by
    push_cast
    ring
  have h := Int.gcd_mul_left (((n ^ 2 + n + 1 : ℕ)) : ℤ) ((n : ℤ) ^ 2 - n + 1) ((n : ℤ) ^ 2 + 3 * n + 3)
  rw [← e1, ← e2, Int.gcd_natCast_natCast, Int.natAbs_natCast, gcd_BC] at h
  unfold a f
  exact h

lemma rec_all (m : ℕ) :
    (a (m + 21) : ℤ) = 3 * a (m + 14) - 3 * a (m + 7) + a m := by
  rw [a_closed (m + 21), a_closed (m + 14), a_closed (m + 7), a_closed m]
  have r1 : (m + 21) % 7 = m % 7 := by omega
  have r2 : (m + 14) % 7 = m % 7 := by omega
  have r3 : (m + 7) % 7 = m % 7 := by omega
  rw [r1, r2, r3]
  split_ifs <;> (push_cast; ring)

end OMA.P111002

theorem OMA.solution : type_of% @OMA.S_oeis_a111002.main := by
  have part1 : ∀ n : ℕ, 20 < n → (OMA.S_oeis_a111002.a n : ℤ)
      = 3 * OMA.S_oeis_a111002.a (n - 7) - 3 * OMA.S_oeis_a111002.a (n - 14)
        + OMA.S_oeis_a111002.a (n - 21) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 21 := ⟨n - 21, by omega⟩
    have h := OMA.P111002.rec_all m
    rw [show m + 21 - 7 = m + 14 from by omega, show m + 21 - 14 = m + 7 from by omega,
      show m + 21 - 21 = m from by omega]
    exact h
  exact part1
