import OMAStatements.S_oeis_a081320

-- Problem: A081320, the 3-smooth part of F(n) has period 12 off the multiples of 12.
-- Credit: @ShoQo (statement by @bnb9001)
-- Proof: F(k+24) = F(23) F(k) + F(24) F(k+1) ≡ F(k) (mod 144), so for 12 ∤ k a check of the 24
-- residues shows 16 ∤ F(k) and 9 ∤ F(k); hence every 3-smooth divisor of such an F(k) divides
-- 24. As F(m+12) = 89 F(m) + 144 F(m+1) and gcd(89, 24) = 1, F(m+12) and F(m) have the same
-- 3-smooth divisors, so their 2- and 3-adic valuations agree.

open OMA.S_oeis_a081320

namespace OMA_A081320_Proof

lemma fib_add_12 (m : ℕ) : Nat.fib (m + 12) = 89 * Nat.fib m + 144 * Nat.fib (m + 1) := by
  have := Nat.fib_add m 11
  rw [show m + 11 + 1 = m + 12 by ring] at this
  rw [this]; norm_num [Nat.fib_add_two]; ring

lemma fib_add_24_mod (k : ℕ) : Nat.fib (k + 24) % 144 = Nat.fib k % 144 := by
  have := Nat.fib_add k 23
  rw [show k + 23 + 1 = k + 24 by ring] at this
  rw [this]
  have h23 : Nat.fib 23 = 28657 := by decide
  have h24 : Nat.fib 24 = 46368 := by decide
  rw [h23, h24]; omega

lemma fib_mod_144 (k : ℕ) : Nat.fib k % 144 = Nat.fib (k % 24) % 144 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 24 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 24 := ⟨k - 24, by omega⟩
      rw [fib_add_24_mod, ih j (by omega), show (j + 24) % 24 = j % 24 by omega]

lemma small_check : ∀ r < 24, ¬ 12 ∣ r → Nat.fib r % 16 ≠ 0 ∧ Nat.fib r % 9 ≠ 0 := by decide

lemma not_dvd {k : ℕ} (hk : ¬ 12 ∣ k) : ¬ 16 ∣ Nat.fib k ∧ ¬ 9 ∣ Nat.fib k := by
  have hm := fib_mod_144 k
  have hr := small_check (k % 24) (Nat.mod_lt _ (by norm_num)) (by omega)
  constructor
  · intro h; apply hr.1; omega
  · intro h; apply hr.2; omega

lemma iff_dvd {m d : ℕ} (hd : d ∣ 24) : d ∣ Nat.fib (m + 12) ↔ d ∣ Nat.fib m := by
  have h144 : d ∣ 144 * Nat.fib (m + 1) := (hd.trans (by norm_num : (24 : ℕ) ∣ 144)).mul_right _
  have hcop : Nat.Coprime d 89 := Nat.Coprime.coprime_dvd_left hd (by norm_num)
  rw [fib_add_12, Nat.dvd_add_left h144]
  exact hcop.dvd_mul_left

/-- The `p`-adic valuation of `F(m)` is 12-periodic off multiples of 12, when `p^e ∣ 24` and
`p^(e+1)` divides no such Fibonacci number. -/
lemma fact_eq {m p e : ℕ} (hp : p.Prime) (he : p ^ e ∣ 24) (hm : ¬ 12 ∣ m)
    (hnd : ∀ k, ¬ 12 ∣ k → ¬ p ^ (e + 1) ∣ Nat.fib k) :
    (Nat.fib (m + 12)).factorization p = (Nat.fib m).factorization p := by
  have hm' : ¬ 12 ∣ m + 12 := fun h => hm (by omega)
  have key : ∀ k, p ^ k ∣ Nat.fib (m + 12) ↔ p ^ k ∣ Nat.fib m := by
    intro k
    by_cases hk : k ≤ e
    · exact iff_dvd ((pow_dvd_pow p hk).trans he)
    · have hle : p ^ (e + 1) ∣ p ^ k := pow_dvd_pow p (by omega)
      exact ⟨fun h => absurd (hle.trans h) (hnd _ hm'), fun h => absurd (hle.trans h) (hnd _ hm)⟩
  have h0 : Nat.fib m ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
  have h0' : Nat.fib (m + 12) ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
  apply le_antisymm
  · rw [← hp.pow_dvd_iff_le_factorization h0]; exact (key _).1 (Nat.ordProj_dvd _ _)
  · rw [← hp.pow_dvd_iff_le_factorization h0']; exact (key _).2 (Nat.ordProj_dvd _ _)

end OMA_A081320_Proof

open OMA_A081320_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a081320.main := by
  intro n hn h12
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  have hm : ¬ 12 ∣ m := fun h => h12 (by omega)
  unfold a smooth3Part
  rw [Nat.add_sub_cancel,
    fact_eq Nat.prime_two (by norm_num : 2 ^ 3 ∣ 24) hm (fun k hk => by simpa using (not_dvd hk).1),
    fact_eq Nat.prime_three (by norm_num : 3 ^ 1 ∣ 24) hm (fun k hk => by simpa using (not_dvd hk).2)]
