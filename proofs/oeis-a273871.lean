import OMAStatements.S_oeis_a273871

-- Problem oeis-a273871: (1) a prime p has (p-1)^2 + 1 dividing 4^(p-1) - 1 if and only if (p-1)^2 + 1 divides
-- (4^k)^(p-1) - 1 for every k; (2) every Fermat prime 2^(2^m) + 1 has this property.
-- Upstream: statements/oeis-a273871.lean (declaration OMA.S_oeis_a273871.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: (1) (4^k)^(p-1) = (4^(p-1))^k and x - 1 divides x^k - 1; conversely take k = 1.
-- (2) For p = 2^(2^m) + 1 put A = (p-1)^2 = 2^(2^(m+1)). Since m + 2 <= 2^m + 1, the exponent 2 * 2^(2^m) of 2 in
-- 4^(p-1) is 2^(m+2) * 2^t, so 4^(p-1) = (A^2)^(2^t). Then A + 1 divides A^2 - 1, which divides (A^2)^(2^t) - 1.

open OMA.S_oeis_a273871

private lemma succ_dvd_sq_sub_one_a273871 (A : ℕ) : A + 1 ∣ A ^ 2 - 1 := by
  rcases A with _ | a
  · simp
  · refine ⟨a, ?_⟩
    have h : (a + 1) ^ 2 = (a + 1 + 1) * a + 1 := by ring
    rw [h, Nat.add_sub_cancel]

theorem OMA.solution : type_of% @OMA.S_oeis_a273871.main := by
  refine ⟨?_, ?_⟩
  · intro p
    constructor
    · rintro ⟨hp, hd⟩
      refine ⟨hp, fun k => ?_⟩
      have e : (4 ^ k) ^ (p - 1) = (4 ^ (p - 1)) ^ k := by
        rw [← pow_mul, ← pow_mul, mul_comm]
      rw [e]
      exact dvd_trans hd (Nat.sub_one_dvd_pow_sub_one (4 ^ (p - 1)) k)
    · rintro ⟨hp, hall⟩
      refine ⟨hp, ?_⟩
      have h1 := hall 1
      rw [pow_one] at h1
      exact h1
  · intro m hm
    refine ⟨hm, ?_⟩
    have hF : Nat.fermatNumber m - 1 = 2 ^ 2 ^ m := by
      unfold Nat.fermatNumber
      rw [Nat.add_sub_cancel]
    rw [hF]
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ m + 1 = m + 2 + t :=
      ⟨2 ^ m + 1 - (m + 2), by have := Nat.lt_two_pow_self (n := m); omega⟩
    have key : 2 ^ 2 ^ m * 2 = 2 ^ m * 2 ^ 2 * 2 ^ t := by
      have h := congrArg (fun e => 2 ^ e) ht
      simp only [pow_succ, pow_add] at h
      linarith [h]
    have e1 : (4 : ℕ) ^ (2 ^ 2 ^ m) = (((2 ^ 2 ^ m) ^ 2) ^ 2) ^ 2 ^ t := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      have h3 : 2 * 2 ^ 2 ^ m = 2 ^ m * 2 ^ 2 * 2 ^ t := by
        rw [← key]
        ring
      rw [h3]
      ring
    rw [e1]
    generalize (2 ^ 2 ^ m) ^ 2 = A
    exact dvd_trans (succ_dvd_sq_sub_one_a273871 A) (Nat.sub_one_dvd_pow_sub_one (A ^ 2) (2 ^ t))
