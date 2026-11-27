import OMAReductions.R_OeisA232616_conjecture_3_R1

namespace OMA.R_OeisA232616_conjecture_3_R1_H1_R2

def H1 : Prop :=
  ∀ x z n : ℕ, 1 < x → 1 < z → 1 < n → ¬ 2 ∣ n →
    Even x → n % 8 = 1 → ¬ IsSquare x → x ^ n + n ≠ z ^ 2

def H2 : Prop :=
  ∀ x z n : ℕ, 1 < x → 1 < z → 1 < n → ¬ 2 ∣ n →
    Odd x → (x + n) % 4 = 0 → ¬ IsSquare x → x ^ n + n ≠ z ^ 2

lemma square_mod_eight (z : ℕ) : z ^ 2 % 8 = 0 ∨ z ^ 2 % 8 = 1 ∨ z ^ 2 % 8 = 4 := by
  have hmod : z ^ 2 % 8 = (z % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
  have hlt : z % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize he : z % 8 = r at *
  interval_cases r <;> norm_num at * <;> omega

lemma square_mod_four (z : ℕ) : z ^ 2 % 4 = 0 ∨ z ^ 2 % 4 = 1 := by
  have hmod : z ^ 2 % 4 = (z % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  have hlt : z % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize he : z % 4 = r at *
  interval_cases r <;> norm_num at * <;> omega

lemma odd_pow_mod_four (x n : ℕ) (hx : Odd x) (hn : n % 2 = 1) : x ^ n % 4 = x % 4 := by
  have hx2 : x % 2 = 1 := by obtain ⟨k, hk⟩ := hx; omega
  have hx4 : x % 4 = 1 ∨ x % 4 = 3 := by omega
  have hcast : (x : ZMod 4) = 1 ∨ (x : ZMod 4) = 3 := by
    rcases hx4 with h | h
    · left
      apply (ZMod.natCast_eq_natCast_iff' x 1 4).2
      simpa using h
    · right
      apply (ZMod.natCast_eq_natCast_iff' x 3 4).2
      simpa using h
  have hsquare : (x : ZMod 4) ^ 2 = 1 := by
    rcases hcast with h | h <;> rw [h] <;> decide
  have hpow : (x : ZMod 4) ^ n = (x : ZMod 4) := by
    rw [pow_eq_pow_mod n hsquare, hn, pow_one]
  apply (ZMod.natCast_eq_natCast_iff' (x ^ n) x 4).mp
  simpa only [Nat.cast_pow] using hpow

lemma no_square_base (x z n : ℕ) (hx : 1 < x) (hn : 1 < n)
    (heq : x ^ n + n = z ^ 2) : ¬ IsSquare x := by
  rintro ⟨a, rfl⟩
  have ha : 1 < a := by nlinarith
  have hnlt : n < a ^ n := Nat.lt_pow_self ha
  have hpow : 0 < a ^ n := pow_pos (by omega) _
  have he : (a ^ n) ^ 2 + n = z ^ 2 := by
    simpa only [mul_pow, pow_two] using heq
  have hz : a ^ n < z := by nlinarith
  have hgap : (a ^ n + 1) ^ 2 ≤ z ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  nlinarith

theorem main : H1 → H2 → OMA.R_OeisA232616_conjecture_3_R1.H1 := by
  intro hEven hOdd x z n hx hz hn hnod heq
  have hxs : ¬ IsSquare x := no_square_base x z n hx hn heq
  have hnmod : n % 2 ≠ 0 := fun h => hnod ((Nat.dvd_iff_mod_eq_zero).2 h)
  have hn2 : n % 2 = 1 := by omega
  have hn3 : 3 ≤ n := by omega
  rcases Nat.even_or_odd x with he | ho
  · have hdiv : 8 ∣ x ^ n := by
      have htwo : 2 ∣ x := he.two_dvd
      simpa using (pow_dvd_pow_of_dvd_of_le htwo hn3 : (2 : ℕ) ^ 3 ∣ x ^ n)
    have hxmod : x ^ n % 8 = 0 := (Nat.dvd_iff_mod_eq_zero).mp hdiv
    have hnz : n % 8 = z ^ 2 % 8 := by
      have h := congrArg (fun t : ℕ => t % 8) heq
      simpa [Nat.add_mod, hxmod] using h
    have hn8 : n % 8 = 1 := by
      have hs := square_mod_eight z
      omega
    exact hEven x z n hx hz hn hnod he hn8 hxs heq
  · have hx2 : x % 2 = 1 := by obtain ⟨k, hk⟩ := ho; omega
    have hpow := odd_pow_mod_four x n ho hn2
    have hsum : (x + n) % 4 = z ^ 2 % 4 := by
      have h := congrArg (fun t : ℕ => t % 4) heq
      rw [Nat.add_mod, hpow] at h
      rw [Nat.add_mod]
      exact h
    have hsum4 : (x + n) % 4 = 0 := by
      have hs := square_mod_four z
      omega
    exact hOdd x z n hx hz hn hnod ho hsum4 hxs heq

end OMA.R_OeisA232616_conjecture_3_R1_H1_R2
