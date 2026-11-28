import OMAStatements.S_oeis_a218483
import Mathlib

namespace OMA.A218483Proof

open OMA.S_oeis_a218483

/-- A Fermat pseudoprime to base 2 is odd. -/
lemma odd_of_psp {N : ℕ} (h : Nat.FermatPsp N 2) : N % 2 = 1 := by
  obtain ⟨hd, -, h1⟩ := h
  by_contra hc
  have h2 : 2 ∣ N := by omega
  have ha : 2 ∣ 2 ^ (N - 1) - 1 := dvd_trans h2 hd
  have hb : 2 ∣ 2 ^ (N - 1) := dvd_pow_self 2 (by omega)
  have hc : 1 ≤ 2 ^ (N - 1) := Nat.one_le_two_pow
  omega

lemma sq_mod_eight {p : ℕ} (hp : p % 2 = 1) : p ^ 2 % 8 = 1 := by
  rw [Nat.pow_mod]
  have : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h2 : p % 8 % 2 = 1 := by omega
  interval_cases h : p % 8 <;> simp_all

/-- Writable with an odd `p` forces `N ≡ 1 (mod 8)`. -/
lemma mod_eight_of_writable {N p : ℕ} (hp : p % 2 = 1) (hw : Writable N p) : N % 8 = 1 := by
  obtain ⟨n, hn⟩ := hw
  have hs := sq_mod_eight hp
  have e : (N : ℤ) - ((p ^ 2 : ℕ) : ℤ) = 8 * ((p : ℤ) * n) := by rw [hn]; push_cast; ring
  generalize (p : ℤ) * n = t at e
  omega

/-- Conversely, `N ≡ 1 (mod 8)` makes `N` writable for each odd divisor `q`. -/
lemma writable_of_mod_eight {N q : ℕ} (hq : q % 2 = 1) (hqN : q ∣ N) (hN : N % 8 = 1) :
    Writable N q := by
  obtain ⟨k, rfl⟩ := hqN
  have hk : k % 8 = q % 8 := by
    have hm : q % 8 * (k % 8) % 8 = 1 := by rw [← Nat.mul_mod]; exact hN
    have h1 : q % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have h2 : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have h3 : q % 8 % 2 = 1 := by omega
    interval_cases hq8 : q % 8 <;> interval_cases hk8 : k % 8 <;> simp_all
  have h8 : (8 : ℤ) ∣ (k : ℤ) - q := by omega
  obtain ⟨m, hm⟩ := h8
  refine ⟨m, ?_⟩
  push_cast
  linear_combination (q : ℤ) * hm

lemma writable_iff {N p : ℕ} (hp : p % 2 = 1) (hpN : p ∣ N) : Writable N p ↔ N % 8 = 1 :=
  ⟨mod_eight_of_writable hp, writable_of_mod_eight hp hpN⟩

lemma prime_odd {N p : ℕ} (hN : N % 2 = 1) (hpN : p ∣ N) : p % 2 = 1 := by
  by_contra h
  have : 2 ∣ p := by omega
  have := dvd_trans this hpN
  omega

lemma part1 : ∀ N : ℕ, Nat.FermatPsp N 2 → N % 40 ≠ 15 := by
  intro N h h15
  obtain ⟨hd, -, -⟩ := h
  have h5 : 5 ∣ 2 ^ (N - 1) - 1 := dvd_trans ⟨N / 5, by omega⟩ hd
  obtain ⟨k, hk⟩ : ∃ k, N - 1 = 4 * k + 2 := ⟨(N - 1) / 4, by omega⟩
  rw [hk, pow_add, pow_mul] at h5
  have h16 : (2 ^ 4) ^ k % 5 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have hpos : 1 ≤ (2 ^ 4) ^ k := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem main_proof :
    (∀ N : ℕ, Nat.FermatPsp N 2 → N % 40 ≠ 15) ∧
    (∀ N : ℕ, Nat.FermatPsp N 2 → ∀ p : ℕ, p.Prime → p ∣ N → Writable N p →
      ∀ q : ℕ, q.Prime → q ∣ N → Writable N q) ∧
    (∀ N : ℕ, Nat.FermatPsp N 2 → ∀ p1 p2 : ℕ, p1.Prime → p2.Prime → N = p1 * p2 →
      ∀ n : ℕ, N = 8 * p1 * n + p1 ^ 2 →
        (N : ℤ) = 8 * p2 * (-(n : ℤ)) + (p2 : ℤ) ^ 2) ∧
    (∀ N : ℕ, Nat.FermatPsp N 2 → ∀ p : ℕ, p.Prime → p ∣ N → ¬ Writable N p →
      ∀ q : ℕ, q.Prime → q ∣ N → ¬ Writable N q) := by
  refine ⟨part1, ?_, ?_, ?_⟩
  · intro N h p _ hpN hw q _ hqN
    have hN := odd_of_psp h
    exact (writable_iff (prime_odd hN hqN) hqN).2
      ((writable_iff (prime_odd hN hpN) hpN).1 hw)
  · intro N _ p1 p2 hp1 _ hN n hn
    have hz : p2 = 8 * n + p1 := by
      apply Nat.eq_of_mul_eq_mul_left hp1.pos
      rw [← hN, hn]; ring
    subst hN
    have hz' : (p2 : ℤ) = 8 * n + p1 := by rw [hz]; push_cast; ring
    push_cast
    linear_combination (-(p2 : ℤ)) * hz'
  · intro N h p _ hpN hw q _ hqN hq
    have hN := odd_of_psp h
    exact hw ((writable_iff (prime_odd hN hpN) hpN).2
      ((writable_iff (prime_odd hN hqN) hqN).1 hq))

end OMA.A218483Proof

open OMA.A218483Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a218483.main := main_proof
