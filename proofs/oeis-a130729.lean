import OMAStatements.S_oeis_a130729

/-!
# Odd-index terms in OEIS A130729

For odd n, the exponent 2^n leaves remainder 2 modulo 3. Since 2^3 leaves
remainder 1 modulo 7, the outer power leaves remainder 4 modulo 7.
Source: https://oeis.org/A130729. Formal statement by @AkiRA-COM-FP.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a130729.main := by
  intro n hn
  obtain ⟨k,rfl⟩ := hn
  have power : (2:ℕ)^(2*k+1) ≡ 2 [MOD 3] := by
    rw [pow_succ, pow_mul]
    have h : (2:ℕ)^2 ≡ 1 [MOD 3] := by decide
    simpa using (h.pow k).mul_right 2
  obtain ⟨m,hm⟩ : ∃ m, (2:ℕ)^(2*k+1) = 3*m+2 := by
    refine ⟨2^(2*k+1)/3, ?_⟩
    change 2^(2*k+1)%3 = 2%3 at power
    omega
  change 7 ∣ (2:ℕ)^(2^(2*k+1))+3
  rw [hm, pow_add, pow_mul]
  have h : (2:ℕ)^3 ≡ 1 [MOD 7] := by decide
  have result := ((h.pow m).mul_right (2^2)).add_right 3
  exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using result)
