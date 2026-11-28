import OMAReductions.R_mo_214595_R1

-- Step mo-214595.R1.H1: hypothesis H1 of reduction mo-214595.R1
-- Credit: @Lenqth (Claude Code, claude-opus-5-5)

/-! A covering argument. Write `2^r = o q + c` with `o` the order of `10` modulo a small prime:
* `r` even: `2^r ≡ 4 (mod 6)`, and `7 ∣ 10^(2^r) + 3`;
* `r ≡ 1 (mod 6)`, `r ≥ 7`: `2^r ≡ 16 (mod 112)`, and `113 ∣ 10^(2^r) + 7`;
* `r ≡ 5 (mod 6)`: `2^r ≡ 14 (mod 18)`, and `19 ∣ 10^(2^r) + 3`.
In each case the number exceeds the prime, so it is composite. -/

namespace OMA.Mo214595H1

lemma not_prime_of_dvd {p N : ℕ} (h : p ∣ N) (hp : 1 < p) (hN : p < N) : ¬ N.Prime := fun hN' =>
  by rcases hN'.eq_one_or_self_of_dvd p h with h1 | h1 <;> omega

lemma big (m : ℕ) (hm : 2 ≤ m) : 113 < 10 ^ m * 10 := by
  have : 100 ≤ 10 ^ m := by calc 100 = 10 ^ 2 := by norm_num
                              _ ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

lemma even_case (s : ℕ) (hs : 1 ≤ s) : 7 ∣ 10 ^ 2 ^ (2 * s) + 3 := by
  have key : ∀ s : ℕ, 1 ≤ s → ∃ q, 2 ^ (2 * s) = 6 * q + 4 := by
    intro s hs
    induction s with
    | zero => omega
    | succ s ih =>
      rcases Nat.eq_zero_or_pos s with rfl | hpos
      · exact ⟨0, by norm_num⟩
      · obtain ⟨q, hq⟩ := ih hpos
        exact ⟨4 * q + 2, by rw [show 2 * (s + 1) = 2 * s + 2 by ring, pow_add, hq]; ring⟩
  obtain ⟨q, hq⟩ := key s hs
  rw [hq, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

lemma one_case (s : ℕ) (hs : 1 ≤ s) : 113 ∣ 10 ^ 2 ^ (6 * s + 1) + 7 := by
  have key : ∀ s : ℕ, 1 ≤ s → ∃ q, 2 ^ (6 * s + 1) = 112 * q + 16 := by
    intro s hs
    induction s with
    | zero => omega
    | succ s ih =>
      rcases Nat.eq_zero_or_pos s with rfl | hpos
      · exact ⟨1, by norm_num⟩
      · obtain ⟨q, hq⟩ := ih hpos
        exact ⟨64 * q + 9, by rw [show 6 * (s + 1) + 1 = (6 * s + 1) + 6 by ring, pow_add, hq]; ring⟩
  obtain ⟨q, hq⟩ := key s hs
  rw [hq, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

lemma five_case (s : ℕ) : 19 ∣ 10 ^ 2 ^ (6 * s + 5) + 3 := by
  have key : ∀ s : ℕ, ∃ q, 2 ^ (6 * s + 5) = 18 * q + 14 := by
    intro s
    induction s with
    | zero => exact ⟨1, by norm_num⟩
    | succ s ih =>
      obtain ⟨q, hq⟩ := ih
      exact ⟨64 * q + 49, by rw [show 6 * (s + 1) + 5 = (6 * s + 5) + 6 by ring, pow_add, hq]; ring⟩
  obtain ⟨q, hq⟩ := key s
  rw [hq, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end OMA.Mo214595H1

open OMA.Mo214595H1 in
theorem OMA.solution : OMA.R_mo_214595_R1.H1 := by
  intro r hr h3
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hbig : 113 < 10 ^ 2 ^ r := by
    have := big (2 ^ r - 1) (by
      have : 4 ≤ 2 ^ r := by calc 4 = 2 ^ 2 := by norm_num
                              _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
      omega)
    rwa [← pow_succ, Nat.sub_add_cancel hpos] at this
  rcases (show r % 2 = 0 ∨ r % 6 = 1 ∨ r % 6 = 5 by omega) with h | h | h
  · refine ⟨3, by simp, not_prime_of_dvd (p := 7) ?_ (by norm_num) (by omega)⟩
    have := even_case (r / 2) (by omega)
    rwa [show 2 * (r / 2) = r by omega] at this
  · refine ⟨7, by simp, not_prime_of_dvd (p := 113) ?_ (by norm_num) (by omega)⟩
    have := one_case (r / 6) (by omega)
    rwa [show 6 * (r / 6) + 1 = r by omega] at this
  · refine ⟨3, by simp, not_prime_of_dvd (p := 19) ?_ (by norm_num) (by omega)⟩
    have := five_case (r / 6)
    rwa [show 6 * (r / 6) + 5 = r by omega] at this
