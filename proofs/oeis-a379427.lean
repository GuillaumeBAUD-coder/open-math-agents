import OMAStatements.S_oeis_a379427
import Mathlib

namespace OMA.A379427Proof

open OMA.S_oeis_a379427

lemma nthP {n : ℕ} (hp : n.Prime) {c : ℕ} (hc : Nat.count Nat.Prime n = c) :
    Nat.nth Nat.Prime c = n := by
  rw [← hc]; exact Nat.nth_count hp

lemma p1 : prime 1 = 2 := by simp [prime]
lemma p2 : prime 2 = 3 := by simp [prime]
lemma p3 : prime 3 = 5 := by simp [prime]
lemma p4 : prime 4 = 7 := by simp [prime]
lemma p5 : prime 5 = 11 := by simp [prime]
lemma p8 : prime 8 = 19 := nthP (by norm_num) (by decide)
lemma p9 : prime 9 = 23 := nthP (by norm_num) (by decide)

/-- If a prime `q` divides a prime `x > q`, contradiction. -/
lemma not_dvd_of_prime {x q : ℕ} (hx : x.Prime) (hq : q.Prime) (hlt : q < x) : ¬ q ∣ x := by
  intro h
  rcases (Nat.prime_dvd_prime_iff_eq hq hx).mp h with rfl
  omega

theorem main_proof :
    ∀ m : ℕ, 1 ≤ m → (∀ k ∈ Finset.Icc 1 8, (prime k * m + prime (k + 1)).Prime) → m % 30 = 14 := by
  intro m hm h
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h8 := h 8 (by decide)
  simp only [p1, p2, p3, p4, p5, p8, p9, Nat.reduceAdd] at h1 h2 h3 h4 h8
  have a2 := not_dvd_of_prime h2 Nat.prime_two (by omega)
  have b3 := not_dvd_of_prime h1 Nat.prime_three (by omega)
  have c3 := not_dvd_of_prime h3 Nat.prime_three (by omega)
  have d5 := not_dvd_of_prime h1 Nat.prime_five (by omega)
  have e5 := not_dvd_of_prime h2 Nat.prime_five (by omega)
  have f5 := not_dvd_of_prime h4 Nat.prime_five (by omega)
  have g5 := not_dvd_of_prime h8 Nat.prime_five (by omega)
  have r2 : m % 2 = 0 := by
    rcases (by omega : m % 2 = 0 ∨ m % 2 = 1) with h | h
    · exact h
    · exact absurd (by omega : 2 ∣ 3 * m + 5) a2
  have r3 : m % 3 = 2 := by
    rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
    · exact absurd (by omega : 3 ∣ 2 * m + 3) b3
    · exact absurd (by omega : 3 ∣ 5 * m + 7) c3
    · exact h
  have r5 : m % 5 = 4 := by
    rcases (by omega : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4)
      with h | h | h | h | h
    · exact absurd (by omega : 5 ∣ 3 * m + 5) e5
    · exact absurd (by omega : 5 ∣ 2 * m + 3) d5
    · exact absurd (by omega : 5 ∣ 7 * m + 11) f5
    · exact absurd (by omega : 5 ∣ 19 * m + 23) g5
    · exact h
  omega

end OMA.A379427Proof

open OMA.A379427Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a379427.main := main_proof
