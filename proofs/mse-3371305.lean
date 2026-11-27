import OMAStatements.S_mse_3371305
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch (no computer search): yes, every n occurs as a block of trailing digits of a power of 2.
-- * 2 is a primitive root modulo 5^L: by lifting the exponent, v_5(16^e - 1) = 1 + v_5(e), so the order of
--   2 mod 5^L is 4 * 5^(L-1) = totient(5^L); hence every residue prime to 5 is a power of 2 mod 5^L.
-- * For n > 0 with m digits put j = 3m + 3, L = j + m and choose c < 10^j (c not divisible by 5) with
--   2^L | x := c + 10^j * n. Take k >= 4L with 2^k = x mod 5^L; then 2^k = x mod 10^L by CRT, so
--   2^k = c + 10^j * (n + 10^m * w) with w >= 1, and the digits of n sit inside the digits of 2^k.
-- * n = 0: 2^10 = 1024.

open OMA.S_mse_3371305

namespace OMA.P_mse_3371305

lemma four_dvd (d : ℕ) (h : 2 ^ d % 5 = 1) : 4 ∣ d := by
  have e : 2 ^ d = 16 ^ (d / 4) * 2 ^ (d % 4) := by
    rw [show (16:ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have h16 : 16 ^ (d / 4) % 5 = 1 := by
    rw [Nat.pow_mod]; norm_num
  rw [e, Nat.mul_mod, h16, one_mul, Nat.mod_mod] at h
  have hr : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have : d % 4 = 0 := by
    interval_cases hh : d % 4 <;> simp_all
  exact Nat.dvd_of_mod_eq_zero this

lemma ord_dvd (L d : ℕ) (hL : 1 ≤ L) (h : 5 ^ L ∣ 2 ^ d - 1) : 4 * 5 ^ (L - 1) ∣ d := by
  have h5 : 5 ∣ 2 ^ d - 1 := (dvd_pow_self 5 (by omega)).trans h
  have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have hm : 2 ^ d % 5 = 1 := by
    have := (Nat.modEq_iff_dvd' hpos).mpr h5
    exact this.symm
  obtain ⟨e, rfl⟩ := four_dvd d hm
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; simp
  apply Nat.mul_dvd_mul_left
  have h16 : 2 ^ (4 * e) - 1 = 16 ^ e - 1 ^ e := by
    rw [pow_mul]; norm_num
  rw [h16] at h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hv := @padicValNat.pow_sub_pow 16 1 5 _ (by decide) (by norm_num) (by norm_num) (by norm_num) e (by omega)
  have hne : 16 ^ e - 1 ^ e ≠ 0 := by
    have : 1 < 16 ^ e := Nat.one_lt_pow (by omega) (by norm_num)
    simp; omega
  have hle : L ≤ padicValNat 5 (16 ^ e - 1 ^ e) := (padicValNat_dvd_iff_le hne).mp h
  have h15 : padicValNat 5 (16 - 1) = 1 := by
    norm_num
    rw [show (15:ℕ) = 5 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num)]
    simp [padicValNat.eq_zero_of_not_dvd (show ¬ 5 ∣ 3 by norm_num)]
  rw [hv, h15] at hle
  exact (pow_dvd_pow 5 (by omega)).trans pow_padicValNat_dvd

lemma surj (L x : ℕ) (hL : 1 ≤ L) (hx : ¬ 5 ∣ x) : ∃ k, 2 ^ k ≡ x [MOD 5 ^ L] := by
  have : NeZero (5 ^ L) := ⟨by positivity⟩
  have c2 : Nat.Coprime 2 (5 ^ L) := Nat.Coprime.pow_right _ (by norm_num)
  have cx : Nat.Coprime x (5 ^ L) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hx))
  set g := ZMod.unitOfCoprime 2 c2 with hg
  have htot : (5 ^ L).totient = 4 * 5 ^ (L - 1) := by
    rw [Nat.totient_prime_pow (by norm_num) (by omega)]; ring
  have hord : orderOf g = 4 * 5 ^ (L - 1) := by
    apply Nat.dvd_antisymm
    · rw [← htot, ← ZMod.card_units_eq_totient]; exact orderOf_dvd_card
    · apply ord_dvd L _ hL
      have h1 := pow_orderOf_eq_one g
      have h2 : ((2 : ℕ) : ZMod (5 ^ L)) ^ orderOf g = ((1 : ℕ) : ZMod (5 ^ L)) := by
        have := congrArg (fun u : (ZMod (5 ^ L))ˣ => (u : ZMod (5 ^ L))) h1
        simp only [hg, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at this
        push_cast; exact this
      rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff] at h2
      exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h2.symm
  have htop : Subgroup.zpowers g = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, htot]
  have hu : ZMod.unitOfCoprime x cx ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers, htop]; trivial
  obtain ⟨k, hk⟩ := hu
  refine ⟨k, ?_⟩
  have := congrArg (fun u : (ZMod (5 ^ L))ˣ => (u : ZMod (5 ^ L))) hk
  simp only [hg, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime] at this
  rw [← ZMod.natCast_eq_natCast_iff]; push_cast; exact this


theorem solve : ∀ n : ℕ, ∃ k : ℕ, digs n <:+: digs (2 ^ k) := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact ⟨10, by norm_num [digs]; decide⟩
  set m := (Nat.digits 10 n).length with hm
  set j := 3 * m + 3 with hj
  set L := j + m with hL
  have hnm : n < 10 ^ m := Nat.lt_base_pow_length_digits (by norm_num)
  set c0 := (2 ^ L - (10 ^ j * n) % 2 ^ L) % 2 ^ L with hc0
  have hP : 0 < 2 ^ L := by positivity
  have hc0d : 2 ^ L ∣ c0 + 10 ^ j * n := by
    have h1 : (10 ^ j * n) % 2 ^ L < 2 ^ L := Nat.mod_lt _ hP
    apply Nat.dvd_of_mod_eq_zero
    rw [hc0, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : 2 ^ L - 10 ^ j * n % 2 ^ L + 10 ^ j * n
        = 2 ^ L * (1 + 10 ^ j * n / 2 ^ L) := by
      have := Nat.div_add_mod (10 ^ j * n) (2 ^ L)
      rw [mul_add, mul_one]; omega
    rw [this, Nat.mul_mod_right]
  set c := if 5 ∣ c0 then c0 + 2 ^ L else c0 with hc
  have hc5 : ¬ 5 ∣ c := by
    rw [hc]; split_ifs with h
    · intro h'
      have : 5 ∣ 2 ^ L := (Nat.dvd_add_right h).mp h'
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) this) (by norm_num)
    · exact h
  have hcd : 2 ^ L ∣ c + 10 ^ j * n := by
    rw [hc]; split_ifs
    · rw [show c0 + 2 ^ L + 10 ^ j * n = (c0 + 10 ^ j * n) + 2 ^ L by ring]
      exact dvd_add hc0d dvd_rfl
    · exact hc0d
  have hcl : c < 10 ^ j := by
    have h1 : c0 < 2 ^ L := Nat.mod_lt _ hP
    have h2 : c < 2 * 2 ^ L := by rw [hc]; split_ifs <;> omega
    have h3 : 2 * 2 ^ L ≤ 10 ^ j := by
      have e1 : 2 * 2 ^ L = 16 ^ (m + 1) := by
        rw [show (16:ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_succ']; congr 1; omega
      have e2 : 10 ^ j = 1000 ^ (m + 1) := by
        rw [show (1000:ℕ) = 10 ^ 3 by norm_num, ← pow_mul]; congr 1
      rw [e1, e2]; exact Nat.pow_le_pow_left (by norm_num) _
    omega
  set x := c + 10 ^ j * n with hx
  have hx5 : ¬ 5 ∣ x := by
    intro h
    have : 5 ∣ 10 ^ j * n := Dvd.dvd.mul_right (dvd_pow (by norm_num : 5 ∣ 10) (by omega)) n
    exact hc5 ((Nat.dvd_add_left this).mp h)
  have hxl : x < 10 ^ L := by
    have : 10 ^ j * n + 10 ^ j ≤ 10 ^ j * 10 ^ m := by nlinarith [Nat.one_le_two_pow (n := j)]
    rw [hL, pow_add]; omega
  obtain ⟨k0, hk0⟩ := surj L x (by omega) hx5
  set k := k0 + (5 ^ L).totient * (4 * L) with hk
  have htpos : 0 < (5 ^ L).totient := Nat.totient_pos.mpr (by positivity)
  have hkL : 4 * L ≤ k := by
    rw [hk]; nlinarith
  have h5 : 2 ^ k ≡ x [MOD 5 ^ L] := by
    have e : 2 ^ k = 2 ^ k0 * (2 ^ (5 ^ L).totient) ^ (4 * L) := by
      rw [← pow_mul, ← pow_add]
    rw [e]
    have : (2 ^ (5 ^ L).totient) ^ (4 * L) ≡ 1 [MOD 5 ^ L] := by
      have := (Nat.ModEq.pow_totient (Nat.Coprime.pow_right L (by norm_num : Nat.Coprime 2 5))).pow (4 * L)
      simpa using this
    simpa using hk0.mul this
  have h2 : 2 ^ k ≡ x [MOD 2 ^ L] := by
    have a : 2 ^ k ≡ 0 [MOD 2 ^ L] := Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 (by omega))
    exact a.trans (Nat.modEq_zero_iff_dvd.mpr hcd).symm
  have h10 : 2 ^ k ≡ x [MOD 10 ^ L] := by
    rw [show (10:ℕ) ^ L = 2 ^ L * 5 ^ L by rw [← mul_pow]; norm_num]
    exact (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.pow L L (by norm_num))).mp ⟨h2, h5⟩
  have hmod : 2 ^ k % 10 ^ L = x := by
    have := h10; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hxl]
  set w := 2 ^ k / 10 ^ L with hw
  have hwpos : 0 < w := by
    apply Nat.div_pos _ (by positivity)
    calc 10 ^ L ≤ 16 ^ L := Nat.pow_le_pow_left (by norm_num) L
      _ = 2 ^ (4 * L) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hkL
  have heq : 2 ^ k = c + 10 ^ ((Nat.digits 10 c).length + (j - (Nat.digits 10 c).length)) *
      (n + 10 ^ (Nat.digits 10 n).length * w) := by
    have hlen : (Nat.digits 10 c).length ≤ j := (Nat.digits_length_le_iff (by norm_num) c).mpr hcl
    rw [Nat.add_sub_cancel' hlen, ← hm]
    have := Nat.mod_add_div (2 ^ k) (10 ^ L)
    rw [hmod, ← hw, hx, hL, pow_add] at this
    rw [← this]; ring
  refine ⟨k, ?_⟩
  have hk0' : 2 ^ k ≠ 0 := by positivity
  simp only [digs, hk0', if_false, Nat.ne_of_gt hn, if_false]
  rw [heq, ← Nat.digits_append_zeroes_append_digits (by norm_num) (by omega),
    ← Nat.digits_append_digits (by norm_num)]
  rw [← List.append_assoc]
  exact List.infix_append _ _ _

end OMA.P_mse_3371305

theorem OMA.solution : type_of% @OMA.S_mse_3371305.main := OMA.P_mse_3371305.solve
