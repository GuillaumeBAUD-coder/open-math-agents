import OMAReductions.R_OeisA2426_conjecture_R1

-- Step OeisA2426.conjecture.R1.H1: every prime p > 3 has a(p) = 1 mod p^2 (Z.-W. Sun).
-- Credit: @jagong-cmu

/-! H1 for OeisA2426: a(p) = 1 mod p^2 for primes p > 3. -/

open Polynomial

namespace A2426H1

lemma coeff_expand_X_add_one_pow (m : ℕ) :
    ((expand ℤ 2 (X + 1)) ^ m).coeff m = if 2 ∣ m then ((m.choose (m / 2) : ℕ) : ℤ) else 0 := by
  rw [← map_pow, coeff_expand (by norm_num), coeff_X_add_one_pow]

lemma sum_even (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1),
      (if 2 ∣ m then ((m.choose (m / 2) : ℕ) : ℤ) else 0) * ((n.choose m : ℕ) : ℤ)
      = ((OeisA2426.a n : ℕ) : ℤ) := by
  unfold OeisA2426.a
  push_cast
  symm
  calc ∑ k ∈ Finset.range (n / 2 + 1), ((n.choose (2 * k) : ℕ) : ℤ) * (((2 * k).choose k : ℕ) : ℤ)
      = ∑ k ∈ Finset.range (n / 2 + 1),
          (fun m : ℕ => (if 2 ∣ m then ((m.choose (m / 2) : ℕ) : ℤ) else 0)
            * ((n.choose m : ℕ) : ℤ)) (2 * k) := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp only
        rw [if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left k (by norm_num), mul_comm]
    _ = ∑ m ∈ (Finset.range (n / 2 + 1)).image (fun k => 2 * k),
          (if 2 ∣ m then ((m.choose (m / 2) : ℕ) : ℤ) else 0) * ((n.choose m : ℕ) : ℤ) := by
        rw [Finset.sum_image (fun x _ y _ h => by omega)]
    _ = _ := by
        apply Finset.sum_subset
        · intro m hm
          simp only [Finset.mem_image, Finset.mem_range] at hm ⊢
          obtain ⟨k, hk, rfl⟩ := hm
          omega
        · intro m hm hnot
          simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hm hnot
          have : ¬ 2 ∣ m := by
            rintro ⟨k, rfl⟩
            exact hnot k (by omega) rfl
          simp [this]

lemma coeff_trinom (n : ℕ) :
    ((X ^ 2 + X + 1 : ℤ[X]) ^ n).coeff n = ((OeisA2426.a n : ℕ) : ℤ) := by
  have hT : (X ^ 2 + X + 1 : ℤ[X]) = expand ℤ 2 (X + 1) + X := by
    rw [map_add, expand_X, map_one]; ring
  rw [hT, add_pow, finsetSum_coeff, ← sum_even n]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m ≤ n := by simpa [Nat.lt_succ_iff] using hm
  rw [coeff_mul_natCast, coeff_mul_X_pow', if_pos (Nat.sub_le n m), Nat.sub_sub_self hm',
    coeff_expand_X_add_one_pow]

lemma frob_dvd (p : ℕ) [hp : Fact p.Prime] (f : ℤ[X]) (i : ℕ) (hi : ¬ p ∣ i) :
    (p : ℤ) ∣ (f ^ p).coeff i := by
  have h : (expand (ZMod p) p (f.map (Int.castRingHom (ZMod p)))).coeff i
      = ((f.map (Int.castRingHom (ZMod p))) ^ p).coeff i := by rw [ZMod.expand_card]
  rw [coeff_expand hp.out.pos, if_neg hi, ← Polynomial.map_pow, coeff_map] at h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simpa using h.symm

end A2426H1

open A2426H1

theorem h1 : ∀ p : ℕ, 3 < p → p.Prime → OeisA2426.a p ≡ 1 [MOD p ^ 2] := by
  intro p hp3 hp
  have := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h3 : ¬ 3 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  have key : (X ^ 2 + X + 1 : ℤ[X]) ^ p * (X + C (-1)) ^ p = expand ℤ 3 ((X + C (-1)) ^ p) := by
    rw [← mul_pow, map_pow]
    congr 1
    simp only [map_add, map_neg, map_one, expand_X]
    ring
  have hcoeff : ((X ^ 2 + X + 1 : ℤ[X]) ^ p * (X + C (-1)) ^ p).coeff p = 0 := by
    rw [key, coeff_expand (by norm_num), if_neg h3]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.pos] at hcoeff
  have c0 : ((X ^ 2 + X + 1 : ℤ[X]) ^ p).coeff 0 = 1 := by
    simp [coeff_zero_eq_eval_zero]
  have cp : ((X ^ 2 + X + 1 : ℤ[X]) ^ p).coeff p = ((OeisA2426.a p : ℕ) : ℤ) := coeff_trinom p
  have d0 : ((X + C (-1) : ℤ[X]) ^ p).coeff 0 = -1 := by
    rw [coeff_X_add_C_pow]; simp [hodd.neg_one_pow]
  have dp : ((X + C (-1) : ℤ[X]) ^ p).coeff p = 1 := by
    rw [coeff_X_add_C_pow]; simp
  have hM : (p : ℤ) ^ 2 ∣ ∑ k ∈ Finset.Ico (0 + 1) p,
      ((X ^ 2 + X + 1 : ℤ[X]) ^ p).coeff k * ((X + C (-1) : ℤ[X]) ^ p).coeff (p - k) := by
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [pow_two]
    apply mul_dvd_mul
    · exact frob_dvd p _ k (Nat.not_dvd_of_pos_of_lt (by omega) hk.2)
    · rw [coeff_X_add_C_pow]
      apply Dvd.dvd.mul_left
      exact Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self (by omega) (by omega))
  simp only [Nat.sub_zero, Nat.sub_self, c0, cp, d0, dp] at hcoeff
  rw [Nat.modEq_iff_dvd]
  push_cast
  have e : (1 : ℤ) - ((OeisA2426.a p : ℕ) : ℤ) = -∑ k ∈ Finset.Ico (0 + 1) p,
      ((X ^ 2 + X + 1 : ℤ[X]) ^ p).coeff k * ((X + C (-1) : ℤ[X]) ^ p).coeff (p - k) := by
    linarith
  rw [e, dvd_neg]
  exact hM

theorem OMA.solution : OMA.R_OeisA2426_conjecture_R1.H1 := h1
