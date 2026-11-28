import OMAStatements.S_oeis_a242560
import Mathlib

/-!
# Verification of the A242560 conjecture `a(2n) = n`

Key observation: the condition `(m! - k) % (m - k) = 0` in `ℤ` is equivalent to
`(m - k) ∣ (m! - m)`, because `m! - k = (m! - m) + (m - k)`.

For `m = 2 * n` we must show that `n` is the least `k` satisfying the condition:
* `k = n` works: `(2n)! - 2n = 2n * ((2n-1)! - 1)` is divisible by `n`.
* no `k < n` works: with `d = 2n - k` we get `n < d ≤ 2n - 1`; since `d ≤ 2n - 1` we have
  `d ∣ (2n-1)!`, and combined with `d ∣ 2n * ((2n-1)! - 1)` this yields `d ∣ 2n`;
  but a divisor of `2n` that is `< 2n` is `≤ n`, contradicting `d > n`.
-/

namespace OMA.A242560Aux

/-- `(m! - k) % (m - k) = 0` iff `(m - k) ∣ (m! - m)`, since `m! - k = (m! - m) + (m - k)`. -/
lemma mod_iff_dvd (m k : ℕ) :
    ((m.factorial : ℤ) - k) % ((m : ℤ) - k) = 0 ↔ ((m : ℤ) - k) ∣ ((m.factorial : ℤ) - m) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Int.dvd_iff_emod_eq_zero.mpr h
    refine ⟨c - 1, ?_⟩
    have e1 : ((m : ℤ) - k) * (c - 1) = ((m : ℤ) - k) * c - ((m : ℤ) - k) := by ring
    rw [e1, ← hc]
    ring
  · intro h
    obtain ⟨c, hc⟩ := h
    refine Int.dvd_iff_emod_eq_zero.mp ⟨c + 1, ?_⟩
    have e1 : ((m : ℤ) - k) * (c + 1) = ((m : ℤ) - k) * c + ((m : ℤ) - k) := by ring
    rw [e1, ← hc]
    ring

/-- For `n ≥ 1`: `(2n)! - 2n = 2n * ((2n-1)! - 1)` in `ℤ`. -/
lemma key_fac (n : ℕ) (hn : 0 < n) : (((2 * n).factorial : ℕ) : ℤ) - ((2 * n : ℕ) : ℤ) =
    ((2 * n : ℕ) : ℤ) * ((((2 * n - 1).factorial : ℕ) : ℤ) - 1) := by
  have h2 : (2 * n).factorial = (2 * n) * (2 * n - 1).factorial := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e1 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e1]
    simp only [Nat.add_sub_cancel]
    exact Nat.factorial_succ _
  have h2' : (((2 * n).factorial : ℕ) : ℤ) =
      ((2 * n : ℕ) : ℤ) * (((2 * n - 1).factorial : ℕ) : ℤ) := by
    rw [h2, Nat.cast_mul]
  rw [h2']
  ring

end OMA.A242560Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a242560.main := by
  intro n hn
  have hpos : 0 < n := hn
  refine ⟨⟨hpos, by omega, ?_⟩, ?_⟩
  · -- `n` satisfies the condition for `m = 2n`
    have hDeq : (((2 * n : ℕ) : ℤ) - ((n : ℕ) : ℤ)) = ((n : ℕ) : ℤ) := by
      have hnn : 2 * n - n = n := by omega
      rw [← Nat.cast_sub (by omega : n ≤ 2 * n), hnn]
    rw [OMA.A242560Aux.mod_iff_dvd (2 * n) n, hDeq, OMA.A242560Aux.key_fac n hn]
    have h2n : (n : ℕ) ∣ 2 * n := ⟨2, by ring⟩
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h2n) _
  · -- minimality: every `k` satisfying the condition is `≥ n`
    intro k hgood
    obtain ⟨hk0, hkn, hmod⟩ := hgood
    by_contra hlt
    set d := 2 * n - k with hd_def
    -- rewrite the `%`-condition as `↑d ∣ (2n)! - 2n`
    have hDd : (((2 * n : ℕ) : ℤ) - (k : ℤ)) = ((d : ℕ) : ℤ) := by
      rw [hd_def, Nat.cast_sub (by omega : k ≤ 2 * n)]
    rw [OMA.A242560Aux.mod_iff_dvd (2 * n) k, hDd] at hmod
    rw [OMA.A242560Aux.key_fac n hn] at hmod
    -- hmod : ↑d ∣ 2n * ((2n-1)! - 1)
    have h1 : (((d : ℕ) : ℤ) ∣ ((2 * n : ℕ) : ℤ) * (((2 * n - 1).factorial : ℕ) : ℤ)) :=
      dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr
        (Nat.dvd_factorial (by omega : 0 < d) (by omega : d ≤ 2 * n - 1))) _
    have hsub : ((2 * n : ℕ) : ℤ) * ((((2 * n - 1).factorial : ℕ) : ℤ) - 1) -
        ((2 * n : ℕ) : ℤ) * (((2 * n - 1).factorial : ℕ) : ℤ) = -((2 * n : ℕ) : ℤ) := by ring
    have hcomb := hmod.sub h1
    rw [hsub] at hcomb
    have hd2n : d ∣ 2 * n := Int.natCast_dvd_natCast.mp (Int.dvd_neg.mp hcomb)
    -- a divisor of `2n` below `2n` is at most `n`, contradicting `d > n`
    have hgtd : n < d := by omega
    have hd1 : d ≤ 2 * n - 1 := by omega
    obtain ⟨c, hc⟩ := hd2n
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, Nat.mul_zero] at hc; omega
      · exact h0
    rcases Nat.lt_or_ge c 2 with hc2 | hc2
    · have hceq : c = 1 := by omega
      rw [hceq, Nat.mul_one] at hc
      omega
    · have hm1 : d * 2 ≤ d * c := Nat.mul_le_mul_left d hc2
      omega
