import OMAStatements.S_oeis_a057192
import Mathlib

namespace A057192

lemma pow_period (q m : ℕ) (h : 2 ^ 24 ≡ 1 [MOD q]) : 2 ^ m ≡ 2 ^ (m % 24) [MOD q] := by
  have e : 2 ^ m = (2 ^ 24) ^ (m / 24) * 2 ^ (m % 24) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h1 : (2 ^ 24) ^ (m / 24) * 2 ^ (m % 24) ≡ 1 ^ (m / 24) * 2 ^ (m % 24) [MOD q] :=
    (h.pow _).mul_right _
  rw [one_pow, one_mul] at h1
  rw [e]
  exact h1

lemma dvd_of (q m r : ℕ) (h24 : 2 ^ 24 ≡ 1 [MOD q]) (hr : m % 24 = r)
    (hd : q ∣ 1 + 271129 * 2 ^ r) : q ∣ 1 + 271129 * 2 ^ m := by
  have h := pow_period q m h24
  rw [hr] at h
  have h2 : 1 + 271129 * 2 ^ m ≡ 1 + 271129 * 2 ^ r [MOD q] := (h.mul_left _).add_left _
  exact (Nat.modEq_zero_iff_dvd).mp (h2.trans ((Nat.modEq_zero_iff_dvd).mpr hd))

lemma p3 : 2 ^ 24 ≡ 1 [MOD 3] := by decide
lemma p5 : 2 ^ 24 ≡ 1 [MOD 5] := by decide
lemma p7 : 2 ^ 24 ≡ 1 [MOD 7] := by decide
lemma p13 : 2 ^ 24 ≡ 1 [MOD 13] := by decide
lemma p17 : 2 ^ 24 ≡ 1 [MOD 17] := by decide
lemma p241 : 2 ^ 24 ≡ 1 [MOD 241] := by decide

lemma cover (m : ℕ) : ∃ q, 1 < q ∧ q < 271129 ∧ q ∣ 1 + 271129 * 2 ^ m := by
  have hr : m % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have hc : m % 24 = 0 ∨ m % 24 = 1 ∨ m % 24 = 2 ∨ m % 24 = 3 ∨ m % 24 = 4 ∨ m % 24 = 5 ∨ m % 24 = 6 ∨ m % 24 = 7 ∨ m % 24 = 8 ∨ m % 24 = 9 ∨ m % 24 = 10 ∨ m % 24 = 11 ∨ m % 24 = 12 ∨ m % 24 = 13 ∨ m % 24 = 14 ∨ m % 24 = 15 ∨ m % 24 = 16 ∨ m % 24 = 17 ∨ m % 24 = 18 ∨ m % 24 = 19 ∨ m % 24 = 20 ∨ m % 24 = 21 ∨ m % 24 = 22 ∨ m % 24 = 23 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨5, by norm_num, by norm_num, dvd_of 5 m 0 p5 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 1 p3 h (by norm_num)⟩
  · exact ⟨7, by norm_num, by norm_num, dvd_of 7 m 2 p7 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 3 p3 h (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of 5 m 4 p5 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 5 p3 h (by norm_num)⟩
  · exact ⟨13, by norm_num, by norm_num, dvd_of 13 m 6 p13 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 7 p3 h (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of 5 m 8 p5 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 9 p3 h (by norm_num)⟩
  · exact ⟨241, by norm_num, by norm_num, dvd_of 241 m 10 p241 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 11 p3 h (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of 5 m 12 p5 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 13 p3 h (by norm_num)⟩
  · exact ⟨7, by norm_num, by norm_num, dvd_of 7 m 14 p7 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 15 p3 h (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of 5 m 16 p5 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 17 p3 h (by norm_num)⟩
  · exact ⟨13, by norm_num, by norm_num, dvd_of 13 m 18 p13 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 19 p3 h (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of 5 m 20 p5 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 21 p3 h (by norm_num)⟩
  · exact ⟨17, by norm_num, by norm_num, dvd_of 17 m 22 p17 h (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of 3 m 23 p3 h (by norm_num)⟩

end A057192

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a057192.main) := by
  intro h
  have hp : Nat.Prime 271129 := by norm_num
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.count Nat.Prime 271129 + 1 := ⟨_, rfl⟩
  have hnth : Nat.nth Nat.Prime (n - 1) = 271129 := by
    rw [hn, Nat.add_sub_cancel]
    exact Nat.nth_count hp
  have hn1 : 1 < n := by
    have h2 : Nat.count Nat.Prime 2 < Nat.count Nat.Prime 271129 :=
      Nat.count_strict_mono Nat.prime_two (by norm_num)
    omega
  have hno : ¬ ∃ m : ℕ, (1 + Nat.nth Nat.Prime (n - 1) * 2 ^ m).Prime := by
    rw [hnth]
    rintro ⟨m, hm⟩
    obtain ⟨q, hq1, hq2, hdvd⟩ := A057192.cover m
    have hbig : 271129 * 1 ≤ 271129 * 2 ^ m := Nat.mul_le_mul_left _ (Nat.one_le_two_pow)
    rcases hm.eq_one_or_self_of_dvd q hdvd with h1 | h1
    · omega
    · omega
  have ha : OMA.S_oeis_a057192.a n = -1 := by
    unfold OMA.S_oeis_a057192.a
    rw [dif_neg hno]
  have hev : Even (OMA.S_oeis_a057192.a n) := (h n hn1).mpr (by rw [hnth])
  rw [ha] at hev
  have h2 := Int.even_iff.mp hev
  omega
