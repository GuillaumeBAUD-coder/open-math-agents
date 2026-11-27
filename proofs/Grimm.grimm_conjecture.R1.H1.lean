import OMAReductions.R_Grimm_grimm_conjecture_R1
import Mathlib

-- Step Grimm.grimm_conjecture.R1.H1: hypothesis H1 of reduction Grimm.grimm_conjecture.R1
-- Credit: @ivillar

/-!
Grimm's conjecture for runs of at most three composites: neighbours are coprime, and of two
even numbers `n`, `n + 2` at least one has an odd prime factor.
-/
namespace F2Grimm

theorem inj2 {α : Type} (f : Fin 2 → α) (h10 : f 1 ≠ f 0) : Function.Injective f := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h h10 | exact absurd h.symm h10

theorem inj3 {α : Type} (f : Fin 3 → α) (h10 : f 1 ≠ f 0) (h20 : f 2 ≠ f 0) (h21 : f 2 ≠ f 1) :
    Function.Injective f := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h h10 | exact absurd h.symm h10 | exact absurd h h20 | exact absurd h.symm h20 | exact absurd h h21 | exact absurd h.symm h21

/-- A prime cannot divide two consecutive numbers. -/
theorem consec {p q a : ℕ} (hp : p.Prime) (h1 : p ∣ a) (h2 : q ∣ a + 1) : q ≠ p := by
  rintro rfl
  have h : q ∣ a + 1 - a := Nat.dvd_sub h2 h1
  rw [Nat.add_sub_cancel_left] at h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h)

/-- Distinct prime divisors for `n` and `n + 2`. -/
theorem two_apart (n : ℕ) (hn : 4 ≤ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ∣ n ∧ q ∣ n + 2 ∧ q ≠ p := by
  rcases Nat.even_or_odd n with he | ho
  · have h2n : 2 ∣ n := he.two_dvd
    have h2n2 : 2 ∣ n + 2 := by omega
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (n + 2) with ⟨b, hb⟩ | ⟨q, hq, hqd, hqo⟩
    · rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨a, ha⟩ | ⟨p, hp, hpd, hpo⟩
      · exfalso
        have ha2 : 2 ≤ a := by
          by_contra hlt
          have : a ≤ 1 := by omega
          interval_cases a <;> omega
        have hb2 : 2 ≤ b := by
          by_contra hlt
          have : b ≤ 1 := by omega
          interval_cases b <;> omega
        have h4n : 4 ∣ n := ha ▸ (pow_dvd_pow 2 ha2 : 2 ^ 2 ∣ 2 ^ a)
        have h4n2 : 4 ∣ n + 2 := hb ▸ (pow_dvd_pow 2 hb2 : 2 ^ 2 ∣ 2 ^ b)
        omega
      · refine ⟨p, 2, hp, Nat.prime_two, hpd, h2n2, ?_⟩
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hpo) even_two
    · refine ⟨2, q, Nat.prime_two, hq, h2n, hqd, ?_⟩
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hqo) even_two
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (by omega : n + 2 ≠ 1)
    refine ⟨p, q, hp, hq, hpd, hqd, ?_⟩
    rintro rfl
    have h : q ∣ n + 2 - n := Nat.dvd_sub hqd hpd
    rw [Nat.add_sub_cancel_left] at h
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
    rw [hq2] at hpd
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hpd)

theorem small : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k ≤ 3 → (∀ i : Fin k, (n + i).Composite) →
    ∃ ps : Fin k ↪ ℕ, ∀ i : Fin k, (ps i).Prime ∧ ps i ∣ (n + i) := by
  intro n k hn hk1 hk3 hc
  interval_cases k
  · have c0 : n.Composite := hc ⟨0, by norm_num⟩
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by have := c0.1; omega : n ≠ 1)
    refine ⟨⟨![p], fun i j _ => Subsingleton.elim i j⟩, fun i => ?_⟩
    match i with
    | ⟨0, _⟩ => exact ⟨hp, hpd⟩
  · have c0 : n.Composite := hc ⟨0, by norm_num⟩
    have c1 : (n + 1).Composite := hc ⟨1, by norm_num⟩
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by have := c0.1; omega : n ≠ 1)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (by omega : n + 1 ≠ 1)
    have hqp : q ≠ p := consec hp hpd hqd
    refine ⟨⟨![p, q], inj2 _ (by simpa using hqp)⟩, fun i => ?_⟩
    match i with
    | ⟨0, _⟩ => exact ⟨hp, hpd⟩
    | ⟨1, _⟩ => exact ⟨hq, hqd⟩
  · have c0 : n.Composite := hc ⟨0, by norm_num⟩
    have c1 : (n + 1).Composite := hc ⟨1, by norm_num⟩
    have hn4 : 4 ≤ n := by
      by_contra hlt
      have h1 := c0.1
      have h2 := c0.2
      have : n = 2 ∨ n = 3 := by omega
      rcases this with rfl | rfl
      · exact h2 Nat.prime_two
      · exact h2 Nat.prime_three
    obtain ⟨p, r, hp, hr, hpd, hrd, hrp⟩ := two_apart n hn4
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (by omega : n + 1 ≠ 1)
    have hqp : q ≠ p := consec hp hpd hqd
    have hrq : r ≠ q := consec hq hqd hrd
    refine ⟨⟨![p, q, r], inj3 _ (by simpa using hqp) (by simpa using hrp) (by simpa using hrq)⟩,
      fun i => ?_⟩
    match i with
    | ⟨0, _⟩ => exact ⟨hp, hpd⟩
    | ⟨1, _⟩ => exact ⟨hq, hqd⟩
    | ⟨2, _⟩ => exact ⟨hr, hrd⟩

end F2Grimm

theorem OMA.solution : OMA.R_Grimm_grimm_conjecture_R1.H1 :=
  F2Grimm.small
