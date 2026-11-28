import OMAStatements.S_oeis_a066337
import Mathlib

namespace OMA.S_oeis_a066337

def c (r : ℕ) : ℕ :=
  if r = 0 then 0 else if r = 1 then 2 else if r = 2 then 5 else if r = 3 then 4
  else if r = 4 then 6 else if r = 5 then 9 else if r = 6 then 8 else if r = 7 then 10
  else if r = 8 then 13 else if r = 9 then 12 else if r = 10 then 14 else 17

def A (n : ℕ) : ℤ :=
  if 11 ≤ n % 16 ∧ n % 16 ≤ 14 then -1 else ((16 * (n / 16) + c (n % 16) : ℕ) : ℤ)

lemma gen (q s : ℕ) (hs : s < 16) : value (16 * q + s) = 16 * (q : ℤ) + low s := by
  unfold value
  rw [show (16 * q + s) / 16 = q by omega, show (16 * q + s) % 16 = s by omega]

lemma bad_none (q r : ℕ) (hr : r < 16) (hb : 11 ≤ r ∧ r ≤ 14) :
    ¬ ∃ m : ℕ, value m = ((16 * q + r : ℕ) : ℤ) := by
  rintro ⟨m, hm⟩
  obtain ⟨j, s, hs, rfl⟩ : ∃ j s, s < 16 ∧ m = 16 * j + s :=
    ⟨m / 16, m % 16, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 16).symm⟩
  rw [gen j s hs] at hm
  push_cast at hm
  obtain ⟨h1, h2⟩ := hb
  interval_cases s <;> simp [low] at hm <;> omega

set_option maxHeartbeats 8000000 in
lemma good_case (q r : ℕ) (hr : r < 16) (hb : ¬ (11 ≤ r ∧ r ≤ 14)) :
    a (16 * q + r) = ((16 * q + c r : ℕ) : ℤ) := by
  have hmin : ∀ k : ℕ, k < 16 * q + c r → value k ≠ ((16 * q + r : ℕ) : ℤ) := by
    intro k hk hv
    obtain ⟨j, s, hs, rfl⟩ : ∃ j s, s < 16 ∧ k = 16 * j + s :=
      ⟨k / 16, k % 16, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 16).symm⟩
    rw [gen j s hs] at hv
    push_cast at hv
    interval_cases r <;> interval_cases s <;> simp [low, c] at hv hk hb <;> omega
  have hval : value (16 * q + c r) = ((16 * q + r : ℕ) : ℤ) := by
    by_cases h15 : r = 15
    · subst h15
      have : 16 * q + c 15 = 16 * (q + 1) + 1 := by simp [c]; ring
      rw [this, gen (q + 1) 1 (by norm_num)]
      simp [low]; ring
    · have hc : c r < 16 := by
        interval_cases r <;> simp [c] at h15 hb ⊢
      rw [gen q (c r) hc]
      push_cast
      interval_cases r <;> simp [c, low] at h15 hb ⊢
  have hex : ∃ m : ℕ, value m = ((16 * q + r : ℕ) : ℤ) := ⟨_, hval⟩
  unfold a
  rw [dif_pos hex]
  have : Nat.find hex = 16 * q + c r := by
    rw [Nat.find_eq_iff]
    exact ⟨hval, fun k hk => hmin k hk⟩
  rw [this]

lemma A_qr (q r : ℕ) (hr : r < 16) :
    A (16 * q + r) = if 11 ≤ r ∧ r ≤ 14 then -1 else ((16 * q + c r : ℕ) : ℤ) := by
  unfold A
  rw [show (16 * q + r) % 16 = r by omega, show (16 * q + r) / 16 = q by omega]

lemma a_eq (n : ℕ) : a n = A n := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 16 ∧ n = 16 * q + r :=
    ⟨n / 16, n % 16, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 16).symm⟩
  rw [A_qr q r hr]
  by_cases hb : 11 ≤ r ∧ r ≤ 14
  · rw [if_pos hb]
    unfold a
    rw [dif_neg (bad_none q r hr hb)]
  · rw [if_neg hb]
    exact good_case q r hr hb

lemma Ed (m n : ℕ) (h : m + 16 = n) :
    A n - A m = if 11 ≤ n % 16 ∧ n % 16 ≤ 14 then 0 else 16 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 16 ∧ m = 16 * q + r :=
    ⟨m / 16, m % 16, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 16).symm⟩
  subst h
  have e : 16 * q + r + 16 = 16 * (q + 1) + r := by ring
  have e2 : (16 * q + r + 16) % 16 = r := by omega
  rw [e, A_qr (q + 1) r hr, A_qr q r hr, ← e, e2]
  by_cases hb : 11 ≤ r ∧ r ≤ 14
  · simp [hb]
  · simp only [hb, if_false]
    push_cast
    ring

set_option maxHeartbeats 16000000 in
lemma rec_ok (n : ℕ) (hn : 28 < n) :
    a n = a (n-1)-a (n-4)+a (n-5)-a (n-8)+a (n-9)-a (n-12)+a (n-13)+a (n-16)-
    a (n-17)+a (n-20)-a (n-21)+a (n-24)-a (n-25)+a (n-28)-a (n-29) := by
  simp only [a_eq]
  have E0 := Ed (n - 16) n (by omega)
  have E1 := Ed (n - 17) (n - 1) (by omega)
  have E2 := Ed (n - 20) (n - 4) (by omega)
  have E3 := Ed (n - 21) (n - 5) (by omega)
  have E4 := Ed (n - 24) (n - 8) (by omega)
  have E5 := Ed (n - 25) (n - 9) (by omega)
  have E6 := Ed (n - 28) (n - 12) (by omega)
  have E7 := Ed (n - 29) (n - 13) (by omega)
  split_ifs at E0 E1 E2 E3 E4 E5 E6 E7 <;> omega

end OMA.S_oeis_a066337

theorem OMA.solution : type_of% @OMA.S_oeis_a066337.main := by
  refine ⟨fun n hn => OMA.S_oeis_a066337.rec_ok n hn, ?_⟩
  show OMA.S_oeis_a066337.denominator * PowerSeries.mk OMA.S_oeis_a066337.a = OMA.S_oeis_a066337.numerator
  open PowerSeries in
  have hden : OMA.S_oeis_a066337.denominator = PowerSeries.X^0 + PowerSeries.X^4 + PowerSeries.X^8 + PowerSeries.X^12 + PowerSeries.X^17 + PowerSeries.X^21 + PowerSeries.X^25 + PowerSeries.X^29 - (PowerSeries.X^1 + PowerSeries.X^5 + PowerSeries.X^9 + PowerSeries.X^13 + PowerSeries.X^16 + PowerSeries.X^20 + PowerSeries.X^24 + PowerSeries.X^28) := by
    unfold OMA.S_oeis_a066337.denominator; ring
  open PowerSeries in
  have hnum : OMA.S_oeis_a066337.numerator = 2*PowerSeries.X^1 + 3*PowerSeries.X^2 + 2*PowerSeries.X^4 + 5*PowerSeries.X^5 + 2*PowerSeries.X^6 + PowerSeries.X^7 + 5*PowerSeries.X^8 + 4*PowerSeries.X^9 + 4*PowerSeries.X^10 + 5*PowerSeries.X^12 + 4*PowerSeries.X^13 + 4*PowerSeries.X^14 + 4*PowerSeries.X^15 + 4*PowerSeries.X^16 + 2*PowerSeries.X^17 + PowerSeries.X^18 + 5*PowerSeries.X^19 + 2*PowerSeries.X^20 + 2*PowerSeries.X^22 + 3*PowerSeries.X^23 + 2*PowerSeries.X^27 - (PowerSeries.X^3 + 14*PowerSeries.X^11 + PowerSeries.X^21 + PowerSeries.X^24 + PowerSeries.X^28) := by
    unfold OMA.S_oeis_a066337.numerator; ring
  open PowerSeries in
  have hmul : (PowerSeries.X^0 + PowerSeries.X^4 + PowerSeries.X^8 + PowerSeries.X^12 + PowerSeries.X^17 + PowerSeries.X^21 + PowerSeries.X^25 + PowerSeries.X^29 - (PowerSeries.X^1 + PowerSeries.X^5 + PowerSeries.X^9 + PowerSeries.X^13 + PowerSeries.X^16 + PowerSeries.X^20 + PowerSeries.X^24 + PowerSeries.X^28)) * PowerSeries.mk OMA.S_oeis_a066337.a = PowerSeries.X^0 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^4 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^8 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^12 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^17 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^21 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^25 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^29 * PowerSeries.mk OMA.S_oeis_a066337.a - (PowerSeries.X^1 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^5 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^9 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^13 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^16 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^20 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^24 * PowerSeries.mk OMA.S_oeis_a066337.a + PowerSeries.X^28 * PowerSeries.mk OMA.S_oeis_a066337.a) := by ring
  rw [hden, hnum, hmul]
  ext n
  have hc : ∀ k : ℕ, PowerSeries.coeff n (PowerSeries.X ^ k * PowerSeries.mk OMA.S_oeis_a066337.a) =
      if k ≤ n then OMA.S_oeis_a066337.a (n - k) else 0 := by
    intro k
    rw [PowerSeries.coeff_X_pow_mul']
    simp
  have hn : ∀ (c k : ℕ), PowerSeries.coeff n ((c : PowerSeries ℤ) * PowerSeries.X ^ k) =
      if n = k then (c : ℤ) else 0 := by
    intro c k
    rw [← map_natCast (PowerSeries.C) c, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  have i0 := hn 2 1
  have i1 := hn 3 2
  have i2 := hn 2 4
  have i3 := hn 5 5
  have i4 := hn 2 6
  have i5 := hn 5 8
  have i6 := hn 4 9
  have i7 := hn 4 10
  have i8 := hn 14 11
  have i9 := hn 5 12
  have i10 := hn 4 13
  have i11 := hn 4 14
  have i12 := hn 4 15
  have i13 := hn 4 16
  have i14 := hn 2 17
  have i15 := hn 5 19
  have i16 := hn 2 20
  have i17 := hn 2 22
  have i18 := hn 3 23
  have i19 := hn 2 27
  simp only [Nat.cast_ofNat] at i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19
  simp only [map_add, map_sub, hc, PowerSeries.coeff_X_pow, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19]
  by_cases h : 28 < n
  · have hr := OMA.S_oeis_a066337.rec_ok n h
    have h1 : ∀ k : ℕ, k ≤ 28 → n ≠ k := fun k hk => by omega
    have h2 : ∀ k : ℕ, k ≤ 29 → k ≤ n := fun k hk => by omega
    simp [h1, h2]
    omega
  · have : n ≤ 28 := by omega
    interval_cases n <;> norm_num [OMA.S_oeis_a066337.a_eq, OMA.S_oeis_a066337.A, OMA.S_oeis_a066337.c]
