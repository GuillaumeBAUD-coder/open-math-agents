import OMAStatements.S_oeis_a182206
import Mathlib
open OMA.S_oeis_a182206
theorem a182206_sq (C p : ℕ) (hC : IsCarmichael C) (hp : 1 < p) : ¬ p ^ 2 ∣ C := by
  rintro ⟨j, hj⟩
  obtain ⟨h1, -, h3⟩ := hC
  have hCx : C = p * (p * j) := by rw [hj]; ring
  have hxx : (p * j) ^ 2 = C * j := by rw [hCx]; ring
  have hxpos : 0 < p * j := by
    rcases Nat.eq_zero_or_pos (p * j) with h | h
    · rw [h] at hCx; omega
    · exact h
  have hcop : (1 + p * j).Coprime C := by
    have : (1 + p * j).Coprime (p * j) := by simp
    exact (this.pow_right 2).coprime_dvd_right ⟨j, hxx⟩
  have key := h3 _ hcop
  rw [← ZMod.natCast_eq_natCast_iff] at key
  have hx2 : ((p * j : ℕ) : ZMod C) ^ 2 = 0 := by
    rw [← Nat.cast_pow, hxx, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hpow : ∀ n : ℕ, ((1 + p * j : ℕ) : ZMod C) ^ n = 1 + (n : ZMod C) * ((p * j : ℕ) : ZMod C) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
      linear_combination (n : ZMod C) * hx2
  rw [Nat.cast_pow, hpow, Nat.cast_one] at key
  have h0 : (((C - 1) * (p * j) : ℕ) : ZMod C) = 0 := by
    rw [Nat.cast_mul]; linear_combination key
  rw [ZMod.natCast_eq_zero_iff] at h0
  rw [hCx] at h0
  have h4 : p ∣ C - 1 := by
    rw [hCx]; exact Nat.dvd_of_mul_dvd_mul_right hxpos h0
  have h5 : p ∣ C := ⟨p * j, hCx⟩
  have h6 : p ∣ C - (C - 1) := Nat.dvd_sub h5 h4
  rw [show C - (C - 1) = 1 by omega] at h6
  have := Nat.le_of_dvd one_pos h6
  omega

theorem a182206_pow5 (n : ℕ) (h : 5 ^ n ≡ 1 [MOD 73]) : 72 ∣ n := by
  have hr : ∀ r < 72, 5 ^ r % 73 = 1 → r = 0 := by decide
  have e : 5 ^ n % 73 = 5 ^ (n % 72) % 73 := by
    conv_lhs => rw [← Nat.div_add_mod n 72, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  unfold Nat.ModEq at h
  have := hr (n % 72) (Nat.mod_lt _ (by norm_num)) (by rw [← e, h])
  exact Nat.dvd_of_mod_eq_zero this

theorem a182206_dvd72 (C : ℕ) (hC : IsCarmichael C) (h73 : 73 ∣ C) : 72 ∣ C - 1 := by
  obtain ⟨k, hk⟩ := h73
  have hk73 : ¬ 73 ∣ k := by
    rintro ⟨j, rfl⟩; exact a182206_sq C 73 hC (by norm_num) ⟨j, by rw [hk]; ring⟩
  have hcop : Nat.Coprime 73 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hk73
  obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop 5 1
  have hbc : b.Coprime C := by
    rw [hk]
    apply Nat.Coprime.mul_right
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq hb1]; norm_num
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq hb2]; simp
  have key := hC.2.2 b hbc
  rw [hk] at key
  have k73 : b ^ (C - 1) ≡ 1 [MOD 73] := by
    rw [hk]; exact Nat.ModEq.of_mul_right k key
  have k5 : 5 ^ (C - 1) ≡ 1 [MOD 73] := (hb1.pow _).symm.trans k73
  exact a182206_pow5 _ k5

theorem OMA.solution : type_of% @OMA.S_oeis_a182206.main := by
  intro C hC h37 h73
  have h2701 : 2701 ∣ C :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 37 73) h37 h73
  obtain ⟨m, hm⟩ := h2701
  have h72 := a182206_dvd72 C hC h73
  have h1 := hC.1
  have hm37 : m ≠ 37 := by
    rintro rfl
    exact a182206_sq C 37 hC (by norm_num) ⟨73, by rw [hm]; norm_num⟩
  obtain ⟨t, ht⟩ := h72
  have hmod : m % 72 = 37 := by omega
  exact ⟨(m - 91) / 18, by omega⟩
