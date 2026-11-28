import OMAStatements.S_mo_173510

-- Disproof: a₁ = 4, d = 13, k = 180 gives the term 2344 = 2 ^ 3 * 293, which is not prime.
-- Two primes 4 + 13 i and 4 + 13 j summing to 2 * 2344 force i + j = 360, and `key` checks
-- in the kernel that for every split one of the two terms has a divisor d with 2 ≤ d < 69.

set_option maxRecDepth 100000 in
private theorem key : ∀ i < 361, ∃ d < 69, 2 ≤ d ∧
    (d ∣ 4 + i * 13 ∧ d < 4 + i * 13 ∨ d ∣ 4 + (360 - i) * 13 ∧ d < 4 + (360 - i) * 13) := by
  decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_173510.main) := by
  intro h
  rcases h 4 13 (by decide) (by decide) (by decide) 180 (by decide) with h | ⟨i, j, hi, hj, e⟩
  · norm_num at h
  · obtain rfl : j = 360 - i := by omega
    obtain ⟨d, -, h2, ⟨hd, hl⟩ | ⟨hd, hl⟩⟩ := key i (by omega)
    · have := hi.eq_one_or_self_of_dvd d hd; omega
    · have := hj.eq_one_or_self_of_dvd d hd; omega
