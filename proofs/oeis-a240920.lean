import OMAStatements.S_oeis_a240920

-- Problem: A240920, a prime is a term iff its next-to-last digit is even.
-- Credit: @ShoQo
-- Proof: 2 and 5 are terms (2 ∣ 1^2 + 5, 5 ∣ 0^2 + 5) with tens digit 0. For any other prime p,
-- p ∣ m^2 + 5 for some m iff -5 is a square mod p, iff the Legendre symbol (-5/p) = 1. By
-- multiplicativity and quadratic reciprocity (5 ≡ 1 mod 4), (-5/p) = χ₄(p) · (p/5), which is 1
-- exactly when p ≡ 1, 3, 7, 9 (mod 20), i.e. when the tens digit of p is even.

open OMA.S_oeis_a240920 ZMod

namespace OMA_A240920_Proof

instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

lemma leg5_1 : legendreSym 5 1 = 1 := legendreSym.at_one 5
lemma leg5_4 : legendreSym 5 4 = 1 := by
  rw [legendreSym.eq_one_iff 5 (by decide)]; exact ⟨2, by decide⟩
lemma leg5_2 : legendreSym 5 2 = -1 := by
  rw [legendreSym.eq_neg_one_iff]
  rintro ⟨x, hx⟩; revert hx; revert x; decide
lemma leg5_3 : legendreSym 5 3 = -1 := by
  rw [legendreSym.eq_neg_one_iff]
  rintro ⟨x, hx⟩; revert hx; revert x; decide

/-- `p ∣ m^2 + 5` for some `m` iff `-5` is a square mod `p`. -/
lemma dvd_iff_isSquare (p : ℕ) [Fact p.Prime] :
    (∃ m : ℕ, p ∣ m ^ 2 + 5) ↔ IsSquare (((-5 : ℤ) : ZMod p)) := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨(m : ZMod p), ?_⟩
    have : ((m ^ 2 + 5 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hm
    push_cast at this ⊢
    linear_combination -this
  · rintro ⟨x, hx⟩
    refine ⟨x.val, (ZMod.natCast_eq_zero_iff _ _).1 ?_⟩
    push_cast
    rw [ZMod.natCast_zmod_val, sq, ← hx]
    push_cast; ring

end OMA_A240920_Proof

open OMA_A240920_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a240920.main := by
  intro p hp
  have hev : Even (p / 10 % 10) ↔ p % 20 < 10 := by rw [Nat.even_iff]; omega
  rw [hev]
  by_cases h2 : p = 2
  · subst h2; exact ⟨fun _ => by norm_num, fun _ => ⟨Nat.prime_two, 1, by norm_num⟩⟩
  by_cases h5 : p = 5
  · subst h5; exact ⟨fun _ => by norm_num, fun _ => ⟨by norm_num, 0, by norm_num⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).2 h2
  have hp5 : p % 5 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).1 (Nat.dvd_of_mod_eq_zero h)
    exact h5 this.symm
  have hne : (((-5 : ℤ)) : ZMod p) ≠ 0 := by
    intro h
    have h' : ((5 : ℕ) : ZMod p) = 0 := by
      have : ((5 : ℤ) : ZMod p) = 0 := by rw [← neg_eq_zero, ← Int.cast_neg]; exact h
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h')
  have hleg : legendreSym p (-5) = χ₄ p * legendreSym 5 ((p : ℤ) % 5) := by
    have hr := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p)
      (by norm_num) h2
    push_cast at hr
    rw [show (-5 : ℤ) = -1 * 5 by norm_num, legendreSym.mul, legendreSym.at_neg_one h2, hr,
      legendreSym.mod 5 (p : ℤ)]
    norm_num
  have key : IsTerm p ↔ χ₄ p * legendreSym 5 ((p : ℤ) % 5) = 1 := by
    rw [IsTerm, and_iff_right hp, dvd_iff_isSquare, ← legendreSym.eq_one_iff p hne, hleg]
  rw [key]
  have h20 : p % 20 = 1 ∨ p % 20 = 3 ∨ p % 20 = 7 ∨ p % 20 = 9 ∨ p % 20 = 11 ∨ p % 20 = 13 ∨
      p % 20 = 17 ∨ p % 20 = 19 := by omega
  have hc4 : ∀ k : ℕ, p % 4 = k → (χ₄ p : ℤ) = if k = 1 then 1 else -1 := by
    intro k hk
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · interval_cases k <;> simp_all
      · omega
      · exact ZMod.χ₄_nat_one_mod_four hk
      · omega
      · exact ZMod.χ₄_nat_three_mod_four hk
    · omega
  have hm5 : ∀ k : ℤ, (p : ℤ) % 5 = k → legendreSym 5 ((p : ℤ) % 5) = legendreSym 5 k :=
    fun k hk => by rw [hk]
  rcases h20 with h | h | h | h | h | h | h | h
  · rw [hc4 1 (by omega), hm5 1 (by omega), leg5_1]; norm_num; omega
  · rw [hc4 3 (by omega), hm5 3 (by omega), leg5_3]; norm_num; omega
  · rw [hc4 3 (by omega), hm5 2 (by omega), leg5_2]; norm_num; omega
  · rw [hc4 1 (by omega), hm5 4 (by omega), leg5_4]; norm_num; omega
  · rw [hc4 3 (by omega), hm5 1 (by omega), leg5_1]; norm_num; omega
  · rw [hc4 1 (by omega), hm5 3 (by omega), leg5_3]; norm_num; omega
  · rw [hc4 1 (by omega), hm5 2 (by omega), leg5_2]; norm_num; omega
  · rw [hc4 3 (by omega), hm5 4 (by omega), leg5_4]; norm_num; omega
