import OMAStatements.S_oeis_a182208
import Mathlib

namespace OMA.A182208

theorem key (N : ℕ) : 3 ^ N % 7 = 3 ^ (N % 6) % 7 := by
  conv_lhs => rw [← Nat.div_add_mod N 6, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem mod6 (N : ℕ) (h : 3 ^ N % 7 = 1) : N % 6 = 0 := by
  rw [key] at h
  have hlt : N % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize N % 6 = s at h hlt
  interval_cases s <;> simp_all

end OMA.A182208

theorem OMA.solution : type_of% @OMA.S_oeis_a182208.main := by
  intro C hC h7
  obtain ⟨h1, -, hF⟩ := hC
  obtain ⟨e, r, hr, hCe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : C ≠ 0) 7 (by norm_num)
  have hcop : Nat.Coprime 7 r := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hr
  obtain ⟨b, hb7, hbr⟩ := Nat.chineseRemainder hcop 3 1
  have hb7c : Nat.Coprime b 7 := by
    rw [Nat.Coprime, hb7.gcd_eq]; norm_num
  have hbrc : Nat.Coprime b r := by
    rw [Nat.Coprime, hbr.gcd_eq]; simp
  have hbC : Nat.Coprime b C := by
    rw [hCe]; exact Nat.Coprime.mul_right (hb7c.pow_right e) hbrc
  have h3 : 3 ^ (C - 1) ≡ 1 [MOD 7] := ((hb7.pow _).symm.trans ((hF b hbC).of_dvd h7))
  have h6 : (C - 1) % 6 = 0 := OMA.A182208.mod6 _ h3
  obtain ⟨k, hk⟩ := h7
  refine ⟨(k - 1) / 6, 0, Or.inl ?_⟩
  omega
