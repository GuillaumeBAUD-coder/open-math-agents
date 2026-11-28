import OMAStatements.S_oeis_a181666

-- Problem: A181666: Numbers whose odd part is of the form (4^k-1)/3.
-- Upstream: formal-conjectures statements/oeis-a181666.lean:0 (declaration OMA.S_oeis_a181666.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if m = 2^v * (4^k - 1)/3 then 3m = 2^(v+2k) - 2^v. Conversely, if
-- 3 divides x = 2^(j+d) - 2^j = 2^j * (2^d - 1) > 0, then 3 divides 2^d - 1, so d = 2e is even
-- (2^(2e+1) - 1 = 2*4^e - 1 is 1 mod 3), e >= 1, and x/3 = 2^j * q with q = (4^e - 1)/3 odd.

open OMA.S_oeis_a181666 in
theorem OMA.solution : type_of% @OMA.S_oeis_a181666.main := by
  have hodd : ∀ a q : ℕ, q % 2 = 1 → oddPart (2 ^ a * q) = q := by
    intro a q hq
    have hq0 : q ≠ 0 := by omega
    have hfac : Nat.factorization (2 ^ a * q) 2 = a := by
      rw [Nat.factorization_mul (show 2 ^ a ≠ 0 by positivity) hq0, Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ q by omega), Nat.add_zero]
    unfold oddPart
    rw [hfac, Nat.mul_div_cancel_left q (show 0 < 2 ^ a by positivity)]
  intro m
  constructor
  · rintro ⟨hm, k, hk⟩
    have hdec : 2 ^ (Nat.factorization m 2) * oddPart m = m :=
      Nat.ordProj_mul_ordCompl_eq_self m 2
    have h3 : 3 ∣ 4 ^ k - 1 := Nat.sub_one_dvd_pow_sub_one 4 k
    have hq3 : 3 * oddPart m = 4 ^ k - 1 := by
      rw [hk]
      exact Nat.mul_div_cancel' h3
    have h44 : (4 : ℕ) ^ k = 2 ^ (2 * k) := by
      rw [pow_mul]
      norm_num
    have hx : 2 ^ (Nat.factorization m 2 + 2 * k) - 2 ^ (Nat.factorization m 2) = 3 * m := by
      rw [pow_add, ← h44, ← Nat.mul_sub_one, ← hq3, Nat.mul_left_comm, hdec]
    refine ⟨2 ^ (Nat.factorization m 2 + 2 * k) - 2 ^ (Nat.factorization m 2),
      ⟨Nat.factorization m 2 + 2 * k, Nat.factorization m 2, by omega, rfl⟩, ?_, ?_, ?_⟩
    · rw [hx]
      omega
    · rw [hx]
      exact Nat.dvd_mul_right 3 m
    · rw [hx]
      omega
  · rintro ⟨x, ⟨i, j, hji, rfl⟩, hx, h3, rfl⟩
    obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
    have hxe : 2 ^ (j + d) - 2 ^ j = 2 ^ j * (2 ^ d - 1) := by
      rw [pow_add, Nat.mul_sub_one]
    rw [hxe] at hx h3 ⊢
    have hcop : Nat.Coprime 3 (2 ^ j) := Nat.Coprime.pow_right j (by decide)
    have h3d : 3 ∣ 2 ^ d - 1 := hcop.dvd_of_dvd_mul_left h3
    obtain ⟨e, rfl | rfl⟩ : ∃ e, d = 2 * e ∨ d = 2 * e + 1 := ⟨d / 2, by omega⟩
    · have h2 : (2 : ℕ) ^ (2 * e) = 4 ^ e := by
        rw [pow_mul]
        norm_num
      rw [h2] at hx h3d ⊢
      obtain ⟨q, hq⟩ : ∃ q, q = (4 ^ e - 1) / 3 := ⟨_, rfl⟩
      have hq3 : 4 ^ e - 1 = 3 * q := by
        rw [hq]
        exact (Nat.mul_div_cancel' h3d).symm
      rw [hq3] at hx ⊢
      have hdiv : 2 ^ j * (3 * q) / 3 = 2 ^ j * q := by
        rw [Nat.mul_left_comm]
        exact Nat.mul_div_cancel_left (2 ^ j * q) (by norm_num)
      rw [hdiv]
      have hqpos : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0] at hx
          simp at hx
        · exact h0
      have he : e ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hq3
        omega
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      have h4 : (4 : ℕ) ^ (e' + 1) = 4 ^ e' * 4 := pow_succ 4 e'
      have h4pos : 0 < (4 : ℕ) ^ e' := by positivity
      have hqodd : q % 2 = 1 := by omega
      refine ⟨Nat.mul_pos (by positivity) hqpos, e' + 1, ?_⟩
      rw [hodd j q hqodd]
      exact hq
    · exfalso
      have h2 : (2 : ℕ) ^ (2 * e + 1) = 4 ^ e * 2 := by
        rw [pow_succ, pow_mul]
        norm_num
      have h4 : (4 : ℕ) ^ e % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      rw [h2] at h3d
      omega
