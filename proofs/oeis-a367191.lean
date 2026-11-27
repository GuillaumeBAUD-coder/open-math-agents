import OMAStatements.S_oeis_a367191
import Mathlib

namespace A367191
open OMA.S_oeis_a367191 in
lemma core (n k : ℕ) (hn : 1 ≤ n) (hk : Admissible n k) :
    ∃ s d : ℤ, 1 ≤ s ∧ 2 * d = (n : ℤ) + s ∧ (k : ℤ) * s + d ^ 2 = (n : ℤ) ^ 2 := by
  obtain ⟨hk0, m, hm⟩ := hk
  have hmZ : (k : ℤ) ^ 2 + (k : ℤ) * n + (n : ℤ) ^ 2 = (m : ℤ) * m := by exact_mod_cast hm
  have hK : (1 : ℤ) ≤ k := by exact_mod_cast hk0
  have hN : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hM : (0 : ℤ) ≤ m := by positivity
  refine ⟨2 * ((m : ℤ) - k) - n, (m : ℤ) - k, ?_, by ring, ?_⟩
  · by_contra hcon
    have hcon' := not_le.mp hcon
    have h1 : 2 * (m : ℤ) ≤ 2 * k + n := by linarith
    have h2 := mul_self_le_mul_self (by positivity : (0 : ℤ) ≤ 2 * m) h1
    have hNN : (1 : ℤ) ≤ (n : ℤ) * n := by nlinarith
    nlinarith [h2, hmZ, hNN]
  · linear_combination (-1 : ℤ) * hmZ

open OMA.S_oeis_a367191 in
lemma bound_odd (j k : ℕ) (hk : Admissible (2 * j + 1) k) : k ≤ j * (3 * j + 2) := by
  have hk0 : (1 : ℤ) ≤ k := by exact_mod_cast hk.1
  obtain ⟨s, d, hs, hd, he⟩ := core (2 * j + 1) k (by omega) hk
  push_cast at hd he
  obtain ⟨e, rfl⟩ : ∃ e : ℤ, s = 2 * e + 1 := ⟨d - j - 1, by linarith⟩
  have he0 : 0 ≤ e := by omega
  have hd' : d = j + 1 + e := by linarith
  subst hd'
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hfin : (k : ℤ) ≤ (j : ℤ) * (3 * j + 2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ k) he0, mul_nonneg hj0 he0, mul_nonneg he0 he0]
  exact_mod_cast hfin

open OMA.S_oeis_a367191 in
lemma bound_two (j k : ℕ) (hk : Admissible (4 * j + 2) k) : k ≤ 2 * j * (3 * j + 2) := by
  have hk0 : (1 : ℤ) ≤ k := by exact_mod_cast hk.1
  obtain ⟨s, d, hs, hd, he⟩ := core (4 * j + 2) k (by omega) hk
  push_cast at hd he
  obtain ⟨f, rfl⟩ : ∃ f : ℤ, s = 2 * f + 2 := ⟨d - 2 * j - 2, by linarith⟩
  have hf0 : 0 ≤ f := by omega
  have hd' : d = 2 * j + 2 + f := by linarith
  subst hd'
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hfin : (k : ℤ) ≤ 2 * (j : ℤ) * (3 * j + 2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ k) hf0, mul_nonneg hj0 hf0, mul_nonneg hf0 hf0]
  exact_mod_cast hfin

open OMA.S_oeis_a367191 in
lemma bound_zero (i k : ℕ) (hk : Admissible (4 * i + 4) k) : k ≤ i * (3 * i + 4) := by
  have hk0 : (1 : ℤ) ≤ k := by exact_mod_cast hk.1
  obtain ⟨s, d, hs, hd, he⟩ := core (4 * i + 4) k (by omega) hk
  push_cast at hd he
  obtain ⟨e, rfl⟩ : ∃ e : ℤ, s = 2 * e := ⟨d - 2 * i - 2, by linarith⟩
  have he1 : 1 ≤ e := by omega
  have hd' : d = 2 * i + 2 + e := by linarith
  subst hd'
  have he2 : e ≠ 1 := by
    rintro rfl
    have h2 : (2 : ℤ) ∣ 1 := ⟨(k : ℤ) - 6 * i * i - 10 * i - 3, by linear_combination (-1 : ℤ) * he⟩
    omega
  obtain ⟨f, rfl⟩ : ∃ f : ℤ, e = f + 2 := ⟨e - 2, by ring⟩
  have hf0 : 0 ≤ f := by omega
  have hi0 : (0 : ℤ) ≤ i := by positivity
  have hfin : (k : ℤ) ≤ (i : ℤ) * (3 * i + 4) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ k) hf0, mul_nonneg hi0 hf0, mul_nonneg hf0 hf0]
  exact_mod_cast hfin

open OMA.S_oeis_a367191 in
lemma value_of (n a : ℕ) (hb : ∀ k, Admissible n k → k ≤ a)
    (hsq : IsSquare (a ^ 2 + a * n + n ^ 2)) : IsValue n a := by
  by_cases ha : a = 0
  · right
    refine ⟨ha, fun k hk => ?_⟩
    have h1 := hb k hk
    have h2 := hk.1
    omega
  · left
    exact ⟨⟨Nat.pos_of_ne_zero ha, hsq⟩, hb⟩

end A367191

theorem OMA.solution : type_of% @OMA.S_oeis_a367191.main := by
  intro n hn
  have hcases : (∃ j, n = 2 * j + 1) ∨ (∃ j, n = 4 * j + 2) ∨ (∃ i, n = 4 * i + 4) := by
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · right
      right
      exact ⟨n / 4 - 1, by omega⟩
    · left
      exact ⟨n / 2, by omega⟩
    · right
      left
      exact ⟨n / 4, by omega⟩
    · left
      exact ⟨n / 2, by omega⟩
  rcases hcases with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨j * (3 * j + 2), A367191.value_of _ _ (fun k hk => A367191.bound_odd j k hk)
      ⟨3 * j ^ 2 + 3 * j + 1, by ring⟩, ?_, ?_, ?_⟩
    · intro h
      omega
    · intro _
      push_cast
      ring
    · intro h
      omega
  · refine ⟨2 * j * (3 * j + 2), A367191.value_of _ _ (fun k hk => A367191.bound_two j k hk)
      ⟨6 * j ^ 2 + 6 * j + 2, by ring⟩, ?_, ?_, ?_⟩
    · intro h
      omega
    · intro h
      omega
    · intro _
      push_cast
      ring
  · refine ⟨i * (3 * i + 4), A367191.value_of _ _ (fun k hk => A367191.bound_zero i k hk)
      ⟨3 * i ^ 2 + 6 * i + 4, by ring⟩, ?_, ?_, ?_⟩
    · intro _
      push_cast
      ring
    · intro h
      omega
    · intro h
      omega
