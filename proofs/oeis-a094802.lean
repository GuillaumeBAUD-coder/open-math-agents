import OMAStatements.S_oeis_a094802
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-! OEIS A094802: for `n > 4`, the least `k` with `m ∣ k!` for all `1 ≤ m ≤ n` is the largest
prime `p ≤ n`.

No `k < p` works since `p ∤ k!`. For `p` itself, Bertrand gives a prime in `(n / 2, n]`, so
`n < 2 p`. Every `m ≤ p` divides `p!`. An `m` with `p < m ≤ n` is composite; write `m = q b`
with `q` its least prime factor, so `q ≤ b` and `b ≤ m / 2 < p`. If `q < b` then `q b ∣ b!`.
If `q = b` then `q ≥ 3` and `2 q ≤ p` (for `q = 3`, `7 ≤ 9 ≤ n` forces `p ≥ 7`; for `q ≥ 4`,
`4 q ≤ q ^ 2 < 2 p`), so `q ^ 2 ∣ q (2 q) ∣ (2 q)!`. -/

namespace OpenMath.A094802

open OMA.S_oeis_a094802

/-- `a * b ∣ b!` for `0 < a < b`. -/
private theorem mul_dvd_factorial (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    a * b ∣ b.factorial := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [Nat.factorial_succ, mul_comm (c + 1)]
  exact mul_dvd_mul (Nat.dvd_factorial ha (by omega)) dvd_rfl

theorem main : ∀ n : ℕ, 4 < n → (a n).Prime ∧ a n = largestPrimeLe n := by
  intro n hn
  have hTne : ({q : ℕ | q ≤ n ∧ q.Prime} : Set ℕ).Nonempty := ⟨2, by omega, Nat.prime_two⟩
  have hTbdd : BddAbove ({q : ℕ | q ≤ n ∧ q.Prime} : Set ℕ) := ⟨n, fun q hq => hq.1⟩
  have hpT : largestPrimeLe n ∈ ({q : ℕ | q ≤ n ∧ q.Prime} : Set ℕ) := Nat.sSup_mem hTne hTbdd
  have hmax : ∀ q, q ≤ n → q.Prime → q ≤ largestPrimeLe n := fun q hq hqp =>
    le_csSup hTbdd ⟨hq, hqp⟩
  generalize largestPrimeLe n = p at hpT hmax ⊢
  obtain ⟨hpn, hp⟩ := hpT
  have hp5 : 5 ≤ p := hmax 5 (by omega) (by norm_num)
  have h2p : n < 2 * p := by
    obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
    have := hmax q (by omega) hq
    omega
  have hS : ∀ m : ℕ, 1 ≤ m → m ≤ n → m ∣ p.factorial := by
    intro m hm1 hmn
    rcases Nat.lt_or_ge p m with hpm | hmp
    · have hm_np : ¬m.Prime := fun hmp => by
        have := hmax m hmn hmp
        omega
      have hqp : m.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨b, hb⟩ := Nat.minFac_dvd m
      have hb2 : 2 ≤ b := by
        rcases (show b = 0 ∨ b = 1 ∨ 2 ≤ b by omega) with h | h | h
        · rw [h, mul_zero] at hb
          omega
        · rw [h, mul_one] at hb
          exact absurd (by rw [hb]; exact hqp) hm_np
        · exact h
      have hqb : m.minFac ≤ b := Nat.minFac_le_of_dvd hb2 (Dvd.intro_left _ hb.symm)
      generalize m.minFac = q at hqp hb hqb
      have hq2 := hqp.two_le
      have hbp : b < p := by
        have : 2 * b ≤ q * b := Nat.mul_le_mul_right b hq2
        omega
      rcases Nat.lt_or_ge q b with hlt | hge
      · rw [hb]
        exact (mul_dvd_factorial q b (by omega) hlt).trans
          (Nat.factorial_dvd_factorial (by omega))
      · have hbq : b = q := le_antisymm hge hqb
        rw [hbq] at hb
        have hq3 : 3 ≤ q := by
          rcases (show q = 2 ∨ 3 ≤ q by omega) with h | h
          · rw [h] at hb
            omega
          · exact h
        have h2q : 2 * q ≤ p := by
          rcases (show q = 3 ∨ 4 ≤ q by omega) with h | h
          · rw [h] at hb
            have := hmax 7 (by omega) (by norm_num)
            omega
          · have : 4 * q ≤ q * q := Nat.mul_le_mul_right q h
            omega
        rw [hb]
        exact (Dvd.intro 2 (by ring)).trans ((mul_dvd_factorial q (2 * q) (by omega)
          (by omega)).trans (Nat.factorial_dvd_factorial h2q))
    · exact Nat.dvd_factorial (by omega) hmp
  have hlow : ∀ k ∈ {k : ℕ | ∀ m : ℕ, 1 ≤ m → m ≤ n → m ∣ k.factorial}, p ≤ k := by
    intro k hk
    by_contra hkp
    have := (Nat.Prime.dvd_factorial hp).1 (hk p hp.one_lt.le hpn)
    omega
  have hmem : p ∈ {k : ℕ | ∀ m : ℕ, 1 ≤ m → m ≤ n → m ∣ k.factorial} := hS
  have ha : a n = p := le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨p, hmem⟩ hlow)
  exact ⟨by rw [ha]; exact hp, ha⟩

end OpenMath.A094802

theorem OMA.solution : type_of% @OMA.S_oeis_a094802.main := OpenMath.A094802.main
