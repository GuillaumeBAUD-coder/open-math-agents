import OMAReductions.R_OeisA287616_conjecture_R1_H1_R1
import Mathlib

/-!
Step H2 of OeisA287616.conjecture.R1.H1.R1. The two integral matrices
M1 = [[3,-2,-2],[0,-1,-4],[0,-2,1]] and M2 = [[3,-2,2],[0,-1,4],[0,2,1]] satisfy
M^T A M = 9 A for the Gram matrix A of 2x^2 - 2xy + 8y^2 + 15z^2, and M^2 = 9.
For a representation (x, 3Y, 3Z), the vector M (x, 3Y, 3Z) / 3 is again an integral primitive
representation. Writing (y, z) = 3^k (a, b) with 3 not dividing both a and b, one of the two maps
sends (a, b) to a pair not both divisible by 3 (M1 if 3 does not divide a + b, M2 otherwise),
lowering k by one. Iterating reaches k = 0.
-/

namespace OMA.P1OeisA287616H2

open OMA.R_OeisA287616_conjecture_R1_H1_R1

theorem not3 {n : ℕ} {u v w : ℤ}
    (h : 2 * u ^ 2 - 2 * u * v + 8 * v ^ 2 + 15 * w ^ 2 = 120 * (n : ℤ) + 23) :
    ¬ ((3 : ℤ) ∣ u ∧ (3 : ℤ) ∣ v ∧ (3 : ℤ) ∣ w) := by
  rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩, ⟨r, rfl⟩⟩
  have h3 : (3 : ℤ) ∣ 120 * (n : ℤ) + 23 :=
    ⟨3 * (2 * p ^ 2 - 2 * p * q + 8 * q ^ 2 + 15 * r ^ 2), by rw [← h]; ring⟩
  omega

theorem stepM1 (n : ℕ) (x Y Z : ℤ)
    (h : 2 * x ^ 2 - 2 * x * (3 * Y) + 8 * (3 * Y) ^ 2 + 15 * (3 * Z) ^ 2 = 120 * (n : ℤ) + 23)
    (hp : Int.gcd x (Int.gcd (3 * Y) (3 * Z)) = 1) :
    2 * (x - 2 * Y - 2 * Z) ^ 2 - 2 * (x - 2 * Y - 2 * Z) * (-Y - 4 * Z) +
        8 * (-Y - 4 * Z) ^ 2 + 15 * (-2 * Y + Z) ^ 2 = 120 * (n : ℤ) + 23 ∧
      Int.gcd (x - 2 * Y - 2 * Z) (Int.gcd (-Y - 4 * Z) (-2 * Y + Z)) = 1 := by
  have hn : 2 * (x - 2 * Y - 2 * Z) ^ 2 - 2 * (x - 2 * Y - 2 * Z) * (-Y - 4 * Z) +
      8 * (-Y - 4 * Z) ^ 2 + 15 * (-2 * Y + Z) ^ 2 = 120 * (n : ℤ) + 23 := by
    rw [← h]
    ring
  refine ⟨hn, primitive_of_inverse hp (not3 hn) ?_⟩
  rintro d ⟨p, hp1⟩ ⟨q, hq⟩ ⟨r, hr⟩
  refine ⟨⟨3 * p - 2 * q - 2 * r, ?_⟩, ⟨-q - 4 * r, ?_⟩, ⟨-2 * q + r, ?_⟩⟩
  · linear_combination 3 * hp1 - 2 * hq - 2 * hr
  · linear_combination -hq - 4 * hr
  · linear_combination -2 * hq + hr

theorem stepM2 (n : ℕ) (x Y Z : ℤ)
    (h : 2 * x ^ 2 - 2 * x * (3 * Y) + 8 * (3 * Y) ^ 2 + 15 * (3 * Z) ^ 2 = 120 * (n : ℤ) + 23)
    (hp : Int.gcd x (Int.gcd (3 * Y) (3 * Z)) = 1) :
    2 * (x - 2 * Y + 2 * Z) ^ 2 - 2 * (x - 2 * Y + 2 * Z) * (-Y + 4 * Z) +
        8 * (-Y + 4 * Z) ^ 2 + 15 * (2 * Y + Z) ^ 2 = 120 * (n : ℤ) + 23 ∧
      Int.gcd (x - 2 * Y + 2 * Z) (Int.gcd (-Y + 4 * Z) (2 * Y + Z)) = 1 := by
  have hn : 2 * (x - 2 * Y + 2 * Z) ^ 2 - 2 * (x - 2 * Y + 2 * Z) * (-Y + 4 * Z) +
      8 * (-Y + 4 * Z) ^ 2 + 15 * (2 * Y + Z) ^ 2 = 120 * (n : ℤ) + 23 := by
    rw [← h]
    ring
  refine ⟨hn, primitive_of_inverse hp (not3 hn) ?_⟩
  rintro d ⟨p, hp1⟩ ⟨q, hq⟩ ⟨r, hr⟩
  refine ⟨⟨3 * p - 2 * q + 2 * r, ?_⟩, ⟨-q + 4 * r, ?_⟩, ⟨2 * q + r, ?_⟩⟩
  · linear_combination 3 * hp1 - 2 * hq + 2 * hr
  · linear_combination -hq + 4 * hr
  · linear_combination 2 * hq + hr

theorem descend (n : ℕ) (k : ℕ) : ∀ x a b : ℤ,
    2 * x ^ 2 - 2 * x * (3 ^ k * a) + 8 * (3 ^ k * a) ^ 2 + 15 * (3 ^ k * b) ^ 2 =
      120 * (n : ℤ) + 23 →
    Int.gcd x (Int.gcd (3 ^ k * a) (3 ^ k * b)) = 1 → ¬ ((3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b) →
    ∃ x' y' z' : ℤ,
      2 * x' ^ 2 - 2 * x' * y' + 8 * y' ^ 2 + 15 * z' ^ 2 = 120 * (n : ℤ) + 23 ∧
        Int.gcd x' (Int.gcd y' z') = 1 ∧ ¬ ((3 : ℤ) ∣ y' ∧ (3 : ℤ) ∣ z') := by
  induction k with
  | zero =>
    intro x a b h hp hab
    refine ⟨x, a, b, ?_, ?_, hab⟩
    · simpa using h
    · simpa using hp
  | succ k ih =>
    intro x a b h hp hab
    have e1 : (3 : ℤ) ^ (k + 1) * a = 3 * (3 ^ k * a) := by ring
    have e2 : (3 : ℤ) ^ (k + 1) * b = 3 * (3 ^ k * b) := by ring
    rw [e1, e2] at h hp
    by_cases hc : (3 : ℤ) ∣ a + b
    · obtain ⟨h', hp'⟩ := stepM2 n x (3 ^ k * a) (3 ^ k * b) h hp
      have e3 : -(3 ^ k * a) + 4 * (3 ^ k * b) = (3 : ℤ) ^ k * (-a + 4 * b) := by ring
      have e4 : 2 * (3 ^ k * a) + 3 ^ k * b = (3 : ℤ) ^ k * (2 * a + b) := by ring
      rw [e3, e4] at h' hp'
      exact ih _ (-a + 4 * b) (2 * a + b) h' hp' (by omega)
    · obtain ⟨h', hp'⟩ := stepM1 n x (3 ^ k * a) (3 ^ k * b) h hp
      have e3 : -(3 ^ k * a) - 4 * (3 ^ k * b) = (3 : ℤ) ^ k * (-a - 4 * b) := by ring
      have e4 : -2 * (3 ^ k * a) + 3 ^ k * b = (3 : ℤ) ^ k * (-2 * a + b) := by ring
      rw [e3, e4] at h' hp'
      exact ih _ (-a - 4 * b) (-2 * a + b) h' hp' (by omega)

theorem decomp (m : ℕ) : ∀ y z : ℤ, y.natAbs + z.natAbs ≤ m → (y ≠ 0 ∨ z ≠ 0) →
    ∃ k : ℕ, ∃ a b : ℤ, y = 3 ^ k * a ∧ z = 3 ^ k * b ∧ ¬ ((3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b) := by
  induction m with
  | zero =>
    intro y z hm hne
    rcases hne with h | h
    · have := Int.natAbs_pos.mpr h
      omega
    · have := Int.natAbs_pos.mpr h
      omega
  | succ m ih =>
    intro y z hm hne
    by_cases h3 : (3 : ℤ) ∣ y ∧ (3 : ℤ) ∣ z
    · obtain ⟨⟨y1, rfl⟩, ⟨z1, rfl⟩⟩ := h3
      have hne' : y1 ≠ 0 ∨ z1 ≠ 0 := by
        rcases hne with h | h
        · left
          rintro rfl
          simp at h
        · right
          rintro rfl
          simp at h
      have hpos : 0 < y1.natAbs + z1.natAbs := by
        rcases hne' with h | h
        · have := Int.natAbs_pos.mpr h
          omega
        · have := Int.natAbs_pos.mpr h
          omega
      rw [Int.natAbs_mul, Int.natAbs_mul] at hm
      have h3a : (3 : ℤ).natAbs = 3 := rfl
      rw [h3a] at hm
      obtain ⟨k, a, b, ha, hb, hab⟩ := ih y1 z1 (by omega) hne'
      exact ⟨k + 1, a, b, by rw [ha]; ring, by rw [hb]; ring, hab⟩
    · exact ⟨0, y, z, by simp, by simp, h3⟩

end OMA.P1OeisA287616H2

open OMA.P1OeisA287616H2 in
theorem OMA.solution : OMA.R_OeisA287616_conjecture_R1_H1_R1.H2 := by
  unfold OMA.R_OeisA287616_conjecture_R1_H1_R1.H2
  intro n x y z h hprim _ _
  have hne : y ≠ 0 ∨ z ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨rfl, rfl⟩ := hc
    have h2 : (2 : ℤ) ∣ 120 * (n : ℤ) + 23 := ⟨x ^ 2, by rw [← h]; ring⟩
    omega
  obtain ⟨k, a, b, rfl, rfl, hab⟩ := decomp _ y z le_rfl hne
  exact descend n k x a b h hprim hab
