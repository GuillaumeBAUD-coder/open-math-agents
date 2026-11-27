import OMAStatements.S_oeis_a051064

namespace OMA.P_oeis_a051064

lemma cassini (n : ℕ) : (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib (n + 1) * Nat.fib n - (Nat.fib n : ℤ) ^ 2
    = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      exact_mod_cast Nat.fib_add_two
    rw [h, pow_succ]
    linear_combination (-1 : ℤ) * ih

lemma fib_three_mul (k : ℕ) (he : Even (k + 1)) :
    Nat.fib (3 * (k + 1)) = Nat.fib (k + 1) * (5 * Nat.fib (k + 1) ^ 2 + 3) := by
  have e1 : Nat.fib (k + 1 + k + 1) = Nat.fib (k + 1) * Nat.fib k + Nat.fib (k + 2) * Nat.fib (k + 1) :=
    Nat.fib_add (k + 1) k
  have e2 : Nat.fib (k + 1 + (k + 1) + 1) = Nat.fib (k + 1) * Nat.fib (k + 1) +
      Nat.fib (k + 2) * Nat.fib (k + 2) := Nat.fib_add (k + 1) (k + 1)
  have e3 : Nat.fib (2 * k + 2 + k + 1) = Nat.fib (2 * k + 2) * Nat.fib k +
      Nat.fib (2 * k + 2 + 1) * Nat.fib (k + 1) := Nat.fib_add (2 * k + 2) k
  have e4 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
  have hc := cassini (k + 1)
  rw [he.neg_one_pow] at hc
  rw [show k + 1 + k + 1 = 2 * k + 2 by ring] at e1
  rw [show k + 1 + (k + 1) + 1 = 2 * k + 2 + 1 by ring] at e2
  rw [show 2 * k + 2 + k + 1 = 3 * (k + 1) by ring, e1, e2] at e3
  rw [e3]
  have : ((Nat.fib (k + 1) * Nat.fib k + Nat.fib (k + 2) * Nat.fib (k + 1)) * Nat.fib k +
      (Nat.fib (k + 1) * Nat.fib (k + 1) + Nat.fib (k + 2) * Nat.fib (k + 2)) * Nat.fib (k + 1) : ℤ)
      = (Nat.fib (k + 1) * (5 * Nat.fib (k + 1) ^ 2 + 3) : ℤ) := by
    have e4' : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by exact_mod_cast e4
    rw [show k + 1 + 1 = k + 2 by ring, e4'] at hc
    rw [e4']
    linear_combination (3 * (Nat.fib (k + 1) : ℤ)) * hc
  exact_mod_cast this

lemma fib_mod_nine (n : ℕ) : Nat.fib n % 9 = Nat.fib (n % 24) % 9 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 24
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 24 := ⟨n - 24, by omega⟩
      have e : Nat.fib (k + 23 + 1) = Nat.fib k * Nat.fib 23 + Nat.fib (k + 1) * Nat.fib 24 :=
        Nat.fib_add k 23
      have f23 : Nat.fib 23 = 28657 := by decide
      have f24 : Nat.fib 24 = 46368 := by decide
      rw [show k + 23 + 1 = k + 24 by ring, f23, f24] at e
      rw [e, show (k + 24) % 24 = k % 24 by omega, ← ih k (by omega)]
      omega

lemma val_one (x : ℕ) (h : x % 9 = 3 ∨ x % 9 = 6) : padicValNat 3 x = 1 := by
  have hx : x = 3 * (x / 3) := by omega
  have h1 : ¬ 3 ∣ x / 3 := by omega
  have h2 : x / 3 ≠ 0 := by omega
  rw [hx, padicValNat.mul (by norm_num) h2, padicValNat_self, padicValNat.eq_zero_of_not_dvd h1]

lemma base (b : ℕ) (hb : ¬ 3 ∣ b) : padicValNat 3 (Nat.fib (4 * b)) = 1 := by
  apply val_one
  rw [fib_mod_nine]
  have : 4 * b % 24 = 4 ∨ 4 * b % 24 = 8 ∨ 4 * b % 24 = 16 ∨ 4 * b % 24 = 20 := by omega
  rcases this with h | h | h | h <;> rw [h] <;> decide

lemma step (m : ℕ) (hm : 0 < m) (he : Even m) (h3 : 3 ∣ Nat.fib m) :
    padicValNat 3 (Nat.fib (3 * m)) = padicValNat 3 (Nat.fib m) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [fib_three_mul k he]
  have hpos : Nat.fib (k + 1) ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
  rw [padicValNat.mul hpos (by positivity)]
  congr 1
  apply val_one
  obtain ⟨t, ht⟩ := h3
  rw [ht]
  have : 5 * (3 * t) ^ 2 + 3 = 9 * (5 * t ^ 2) + 3 := by ring
  rw [this]
  omega

lemma main_val (b : ℕ) (hb : ¬ 3 ∣ b) (hb0 : b ≠ 0) :
    ∀ a : ℕ, padicValNat 3 (Nat.fib (4 * (3 ^ a * b))) = a + 1 := by
  intro a
  induction a with
  | zero => simpa using base b hb
  | succ a ih =>
    have hm : 0 < 4 * (3 ^ a * b) := by positivity
    have he : Even (4 * (3 ^ a * b)) := ⟨2 * (3 ^ a * b), by ring⟩
    have h3 : 3 ∣ Nat.fib (4 * (3 ^ a * b)) := by
      apply dvd_of_one_le_padicValNat
      omega
    rw [show 4 * (3 ^ (a + 1) * b) = 3 * (4 * (3 ^ a * b)) by ring, step _ hm he h3, ih]

lemma fib_mod_three (k : ℕ) (hk : ¬ 4 ∣ k) : ¬ 3 ∣ Nat.fib k := by
  intro h
  have h9 := fib_mod_nine k
  have hr : k % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have h4 : ¬ 4 ∣ k % 24 := by omega
  have key : ∀ j < 24, ¬ 4 ∣ j → Nat.fib j % 9 % 3 ≠ 0 := by decide
  have := key (k % 24) hr h4
  omega

end OMA.P_oeis_a051064

theorem OMA.solution : type_of% @OMA.S_oeis_a051064.main := by
  refine ⟨fun n hn => ?_, fun n r hr1 hr3 => ?_⟩
  · obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show n ≠ 0 by omega) 3 (by norm_num)
    have hb0 : b ≠ 0 := by rintro rfl; simp at hn
    rw [OMA.P_oeis_a051064.main_val b hb hb0 a]
    unfold OMA.S_oeis_a051064.a
    rw [show 3 * (3 ^ a * b) = 3 ^ (a + 1) * b by ring,
      padicValNat.mul (by positivity) hb0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hb]
  · exact padicValNat.eq_zero_of_not_dvd (OMA.P_oeis_a051064.fib_mod_three _ (by omega))
