import OMAStatements.S_oeis_a082274
import Mathlib

open OMA.S_oeis_a082274

theorem a082274_digits_step (m : ℕ) (hm : 10 ≤ m) :
    Nat.digits 10 m = m % 10 :: Nat.digits 10 (m / 10) :=
  Nat.digits_def' (by norm_num) (by omega)

theorem a082274_last_step (m : ℕ) (hm : 10 ≤ m) :
    (Nat.digits 10 m).getLast? = (Nat.digits 10 (m / 10)).getLast? := by
  rw [a082274_digits_step m hm]
  have hne : Nat.digits 10 (m / 10) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  obtain ⟨x, l, h⟩ := List.exists_cons_of_ne_nil hne
  rw [h]
  simp

theorem a082274_last_small (m : ℕ) (h0 : 0 < m) (h : m < 10) :
    (Nat.digits 10 m).getLast? = some m := by
  rw [Nat.digits_of_lt 10 m (by omega) h]
  rfl

theorem a082274_last_pal (x : ℕ) (hx : 0 < x) (hp : Pal x) :
    (Nat.digits 10 x).getLast? = some (x % 10) := by
  rw [← List.head?_reverse, hp, Nat.digits_def' (by norm_num) hx]
  rfl

theorem a082274_last_ne_zero (x : ℕ) (hx : 0 < x) :
    (Nat.digits 10 x).getLast? ≠ some 0 := by
  have hne : Nat.digits 10 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  rw [List.getLast?_eq_some_getLast hne]
  intro h
  exact Nat.getLast_digit_ne_zero 10 (by omega : x ≠ 0) (Option.some.inj h)

theorem a082274_key : ∀ m : ℕ, 0 < m → (Nat.digits 10 m).getLast? = some 9 →
    (Nat.digits 10 (m + 1)).getLast? = some 1 → ∃ j : ℕ, m + 1 = 10 ^ j := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h0 h9 h1
    by_cases hm : m < 10
    · rw [a082274_last_small m h0 hm] at h9
      have : m = 9 := Option.some.inj h9
      exact ⟨1, by omega⟩
    · push Not at hm
      rw [a082274_last_step m hm] at h9
      rw [a082274_last_step (m + 1) (by omega)] at h1
      by_cases hd : m % 10 = 9
      · have he : (m + 1) / 10 = m / 10 + 1 := by omega
        rw [he] at h1
        obtain ⟨j, hj⟩ := ih (m / 10) (by omega) (by omega) h9 h1
        refine ⟨j + 1, ?_⟩
        rw [pow_succ]
        omega
      · have he : (m + 1) / 10 = m / 10 := by omega
        rw [he, h9] at h1
        simp at h1

theorem a082274_rep9 (k : ℕ) : Nat.digits 10 (10 ^ k - 1) = List.replicate k 9 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 10 ^ (k + 1) - 1 = 9 + 10 * (10 ^ k - 1) := by
      have := Nat.one_le_pow k 10 (by norm_num)
      rw [pow_succ]; omega
    rw [hp, Nat.digits_add 10 (by norm_num) 9 _ (by norm_num) (Or.inl (by norm_num)), ih]
    rfl

theorem a082274_pow1 (j : ℕ) :
    Nat.digits 10 (10 ^ (j + 1) + 1) = 1 :: (List.replicate j 0 ++ [1]) := by
  have hp : 10 ^ (j + 1) + 1 = 1 + 10 * (10 ^ j * 1) := by rw [pow_succ]; ring
  rw [hp, Nat.digits_add 10 (by norm_num) 1 _ (by norm_num) (Or.inl (by norm_num)),
    Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
  simp

theorem OMA.solution : type_of% @OMA.S_oeis_a082274.main := by
  intro n hn
  constructor
  · rintro ⟨hp, hp2⟩
    by_cases h10 : n < 10
    · by_cases h7 : n ≤ 7
      · exact Or.inl h7
      · by_cases h8 : n = 8
        · subst h8
          exfalso
          revert hp2
          norm_num [Pal]
        · right
          exact ⟨1, by norm_num, by omega⟩
    · push Not at h10
      have hL := a082274_last_pal n hn hp
      rw [a082274_last_step n h10] at hL
      have hL2 := a082274_last_pal (n + 2) (by omega) hp2
      rw [a082274_last_step (n + 2) (by omega)] at hL2
      by_cases h7 : n % 10 ≤ 7
      · have he : (n + 2) / 10 = n / 10 := by omega
        rw [he, hL] at hL2
        have := Option.some.inj hL2
        omega
      · by_cases h8 : n % 10 = 8
        · have he : (n + 2) % 10 = 0 := by omega
          rw [he] at hL2
          exact absurd hL2 (a082274_last_ne_zero _ (by omega))
        · have h9 : n % 10 = 9 := by omega
          have he : (n + 2) / 10 = n / 10 + 1 := by omega
          have he1 : (n + 2) % 10 = 1 := by omega
          rw [he, he1] at hL2
          rw [h9] at hL
          obtain ⟨j, hj⟩ := a082274_key (n / 10) (by omega) hL hL2
          right
          refine ⟨j + 1, by omega, ?_⟩
          rw [pow_succ]
          omega
  · rintro (h | ⟨k, hk, rfl⟩)
    · interval_cases n <;> norm_num [Pal]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h2 : 10 ^ (j + 1) - 1 + 2 = 10 ^ (j + 1) + 1 := by
        have := Nat.one_le_pow (j + 1) 10 (by norm_num)
        omega
      refine ⟨?_, ?_⟩
      · unfold Pal
        rw [a082274_rep9]
        simp
      · unfold Pal
        rw [h2, a082274_pow1]
        simp
