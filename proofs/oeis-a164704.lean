import OMAStatements.S_oeis_a164704
import Mathlib

/-!
# A164704: Kaprekar numbers are `0` or `1` modulo `9`

If `n = q + r` and `n ^ 2 = q * 10 ^ m + r`, then, because `10 ^ m ≡ 1 (mod 9)`,
`n ^ 2 ≡ q + r = n (mod 9)`.  The only residues `k` modulo `9` with `k ^ 2 ≡ k` are `0` and `1`.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a164704.main := by
  rintro n ⟨-, ⟨m, q, r, -, -, hsum, hsq⟩, -⟩
  -- `10 ^ m ≡ 1 (mod 9)`
  have h10 : 10 ^ m ≡ 1 [MOD 9] := by
    have := Nat.ModEq.pow m (show 10 ≡ 1 [MOD 9] by decide)
    simpa using this
  -- hence `n ^ 2 ≡ n (mod 9)`
  have hcong : n ^ 2 ≡ n [MOD 9] := by
    rw [hsq]
    have := (Nat.ModEq.mul_left q h10).add_right r
    rw [mul_one] at this
    rw [hsum]
    exact this
  -- check the nine residues
  have hres : (n % 9) ^ 2 % 9 = n % 9 := by
    have h1 : n ^ 2 % 9 = n % 9 := hcong
    rwa [Nat.pow_mod] at h1
  have hlt : n % 9 < 9 := Nat.mod_lt _ (by norm_num)
  generalize n % 9 = k at hres hlt ⊢
  interval_cases k <;> simp_all
