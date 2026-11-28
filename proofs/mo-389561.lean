import OMAStatements.S_mo_389561

-- Problem: Why the curve x^2+y^2+y+1=0 has only one point over F_{3^{2n+1}}?
-- Upstream: statements/mo-389561.lean (declaration OMA.S_mo_389561.main)
-- Credit: @keiichisince1986-bot

namespace OMA.Mo389561

private lemma pow_three_odd_mod_four (n : ℕ) : ∃ k : ℕ, 3 ^ (2 * n + 1) = 4 * k + 3 := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨9 * k + 6, ?_⟩
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add, hk]
    ring

private lemma sum_sq_eq_zero {n : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 3]
    (hcard : Fintype.card F = 3 ^ (2 * n + 1)) (a b : F) (h : a ^ 2 + b ^ 2 = 0) :
    a = 0 ∧ b = 0 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  by_cases hb : b = 0
  · subst hb
    have ha2 : a ^ 2 = 0 := by simpa using h
    exact ⟨sq_eq_zero_iff.mp ha2, rfl⟩
  · let u : F := a / b
    have hu2 : u ^ 2 = -1 := by
      dsimp [u]
      rw [div_pow, eq_neg_iff_add_eq_zero]
      field_simp [hb]
      linear_combination h
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0] at hu2
      norm_num at hu2
    have hpow : u ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one u hu0
    obtain ⟨k, hk⟩ := pow_three_odd_mod_four n
    have hsub : Fintype.card F - 1 = 2 * (2 * k + 1) := by omega
    rw [hsub, pow_mul, hu2] at hpow
    have hneg : (-1 : F) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, rfl⟩
    rw [hneg] at hpow
    have h10 : (1 : F) = 0 := by linear_combination h3 + hpow
    exact absurd h10 one_ne_zero

end OMA.Mo389561

theorem OMA.solution : type_of% @OMA.S_mo_389561.main := by
  intro n F _ _ _ hcard
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  constructor
  · intro x y
    constructor
    · intro h
      have hsq : x ^ 2 + (y - 1) ^ 2 = 0 := by linear_combination h - y * h3
      obtain ⟨hx, hy⟩ := OMA.Mo389561.sum_sq_eq_zero hcard x (y - 1) hsq
      exact ⟨hx, sub_eq_zero.mp hy⟩
    · rintro ⟨rfl, rfl⟩
      linear_combination h3
  · intro x y z hnz
    constructor
    · intro h
      have hsq : x ^ 2 + (y - z) ^ 2 = 0 := by linear_combination h - y * z * h3
      obtain ⟨hx, hyz⟩ := OMA.Mo389561.sum_sq_eq_zero hcard x (y - z) hsq
      have hy : y = z := sub_eq_zero.mp hyz
      refine ⟨hx, hy, ?_⟩
      intro hz
      subst hx hy hz
      simp at hnz
    · rintro ⟨rfl, rfl, _⟩
      linear_combination y ^ 2 * h3
