import OMAReductions.R_SternPrime_isSternPrime_iff_R1

/-!
# Step H2 of the reduction SternPrime.isSternPrime_iff.R1

The eight numbers 2, 3, 17, 137, 227, 977, 1187 and 1493 are Stern primes: each is prime and
none of them can be written as p + 2 b^2 with p prime and b at least 1.

Only the upstream definitions `SternPrime.IsSternPrime` and `SternPrime.HasPrimePlusTwiceSquare`
are used (no upstream theorem and no upstream instance). The helper lemma below bounds b by an
explicit B with q at most 2 B^2, which turns the claim into finitely many facts of the form
q - 2 b^2 is not prime; these are decided by the kernel with the Mathlib decision procedure for
`Nat.Prime`.
-/

namespace OMA.Helpers

/-- If `q ≤ 2 * B ^ 2` and `q - 2 * b ^ 2` is not prime for every `1 ≤ b < B` with
`2 * b ^ 2 < q`, then `q` has no decomposition `p + 2 * b ^ 2` with `p` prime and `1 ≤ b`. -/
theorem sternPrime_not_hasPrimePlusTwiceSquare (q B : ℕ) (hB : q ≤ 2 * B ^ 2)
    (h : ∀ b, b < B → 1 ≤ b → 2 * b ^ 2 < q → ¬ (q - 2 * b ^ 2).Prime) :
    ¬ SternPrime.HasPrimePlusTwiceSquare q := by
  rintro ⟨p, b, hp, hb, rfl⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hbB : b < B := by
    by_contra hcon
    have hle : B ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (Nat.le_of_not_lt hcon) 2
    omega
  exact h b hbB hb (by omega) (by rwa [Nat.add_sub_cancel])

/-- A prime `q` passing the finite check of `sternPrime_not_hasPrimePlusTwiceSquare` is a
Stern prime. -/
theorem isSternPrime_of_check (q B : ℕ) (hq : q.Prime) (hB : q ≤ 2 * B ^ 2)
    (h : ∀ b, b < B → 1 ≤ b → 2 * b ^ 2 < q → ¬ (q - 2 * b ^ 2).Prime) :
    SternPrime.IsSternPrime q :=
  ⟨hq, sternPrime_not_hasPrimePlusTwiceSquare q B hB h⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact OMA.Helpers.isSternPrime_of_check 2 1 (by norm_num) (by norm_num) (by decide +kernel)
  · exact OMA.Helpers.isSternPrime_of_check 3 2 (by norm_num) (by norm_num) (by decide +kernel)
  · exact OMA.Helpers.isSternPrime_of_check 17 3 (by norm_num) (by norm_num) (by decide +kernel)
  · exact OMA.Helpers.isSternPrime_of_check 137 9 (by norm_num) (by norm_num) (by decide +kernel)
  · exact OMA.Helpers.isSternPrime_of_check 227 11 (by norm_num) (by norm_num) (by decide +kernel)
  · exact OMA.Helpers.isSternPrime_of_check 977 23 (by norm_num) (by norm_num) (by decide +kernel)
  · exact OMA.Helpers.isSternPrime_of_check 1187 25 (by norm_num) (by norm_num) (by decide +kernel)
  · exact OMA.Helpers.isSternPrime_of_check 1493 28 (by norm_num) (by norm_num) (by decide +kernel)
