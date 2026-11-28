import OMAStatements.S_oeis_a111002
import Mathlib

namespace A111002

lemma pick (n d : ℕ) (h14 : d ∣ 14) (h2 : ¬ 2 ∣ d) (h7 : 7 ∣ d ↔ n % 7 = 3) :
    d = if n % 7 = 3 then 7 else 1 := by
  have hle : d ≤ 14 := Nat.le_of_dvd (by norm_num) h14
  interval_cases d <;> split_ifs <;> omega

lemma seven (n A t : ℕ) (ht : t = n * n) (hA : A + n = t + 1) :
    (7 ∣ A ∧ 7 ∣ t + 3 * n + 3) ↔ n % 7 = 3 := by
  have hmod : t % 7 = ((n % 7) * (n % 7)) % 7 := by rw [ht]; exact Nat.mul_mod n n 7
  obtain ⟨r, hr⟩ : ∃ r, n % 7 = r := ⟨_, rfl⟩
  rw [hr] at hmod
  have hr7 : r < 7 := by omega
  interval_cases r <;> simp at hmod <;> omega

lemma key (n A : ℕ) (hA : A + n = n * n + 1) :
    Nat.gcd A (n * n + 3 * n + 3) = if n % 7 = 3 then 7 else 1 := by
  apply pick
  · have hdA : (Nat.gcd A (n * n + 3 * n + 3) : ℤ) ∣ (A : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
    have hdB : (Nat.gcd A (n * n + 3 * n + 3) : ℤ) ∣ ((n * n + 3 * n + 3 : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
    have hA' : (A : ℤ) = (n : ℤ) * n + 1 - n := by
      have h := congrArg (fun x : ℕ => (x : ℤ)) hA
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h
      linarith
    have e : (14 : ℤ) = (2 * (n : ℤ) + 5) * (A : ℤ)
        - (2 * (n : ℤ) - 3) * ((n * n + 3 * n + 3 : ℕ) : ℤ) := by
      rw [hA']; push_cast; ring
    have h14 : (Nat.gcd A (n * n + 3 * n + 3) : ℤ) ∣ (14 : ℤ) := by
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_left hdA _) (Dvd.dvd.mul_left hdB _)
    exact_mod_cast h14
  · intro h2
    have h2A : 2 ∣ A := h2.trans (Nat.gcd_dvd_left _ _)
    have hpar : (n * n) % 2 = ((n % 2) * (n % 2)) % 2 := Nat.mul_mod n n 2
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] at hpar <;> simp at hpar <;> omega
  · rw [Nat.dvd_gcd_iff]
    exact seven n A (n * n) rfl hA

lemma a_eq (n : ℕ) : OMA.S_oeis_a111002.a n = (n * n + n + 1) * (if n % 7 = 3 then 7 else 1) := by
  obtain ⟨A, hA⟩ : ∃ A, A + n = n * n + 1 := ⟨n * n + 1 - n, by
    have : n ≤ n * n := Nat.le_mul_self n
    omega⟩
  have hA' : (A : ℤ) = (n : ℤ) * n + 1 - n := by
    have h := congrArg (fun x : ℕ => (x : ℤ)) hA
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h
    linarith
  have f1 : OMA.S_oeis_a111002.f n = (n * n + n + 1) * A := by
    have : ((OMA.S_oeis_a111002.f n : ℕ) : ℤ) = (((n * n + n + 1) * A : ℕ) : ℤ) := by
      unfold OMA.S_oeis_a111002.f
      push_cast
      rw [hA']; ring
    exact_mod_cast this
  have f2 : OMA.S_oeis_a111002.f (n + 1) = (n * n + n + 1) * (n * n + 3 * n + 3) := by
    unfold OMA.S_oeis_a111002.f
    ring
  unfold OMA.S_oeis_a111002.a
  rw [f1, f2, Nat.gcd_mul_left, key n A hA]

end A111002

theorem OMA.solution : type_of% @OMA.S_oeis_a111002.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 21 := ⟨n - 21, by omega⟩
  have e1 : m + 21 - 7 = m + 14 := by omega
  have e2 : m + 21 - 14 = m + 7 := by omega
  have e3 : m + 21 - 21 = m := by omega
  rw [e1, e2, e3, A111002.a_eq, A111002.a_eq, A111002.a_eq, A111002.a_eq]
  have h1 : (m + 21) % 7 = m % 7 := by omega
  have h2 : (m + 14) % 7 = m % 7 := by omega
  have h3 : (m + 7) % 7 = m % 7 := by omega
  rw [h1, h2, h3]
  push_cast
  ring
