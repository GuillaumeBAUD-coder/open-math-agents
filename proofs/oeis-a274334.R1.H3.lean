import OMAReductions.R_oeis_a274334_R1
import Mathlib
-- Credit: Alain Van Kerckhoven (@avk-lab)

/-!
Step H3 of the reduction oeis-a274334.R1: none of the 22 exceptional numbers k has
k^3 = w^3 + x^3 + y^3 + z^3 with positive w, x, y, z.

A solution can be sorted as w ≥ x ≥ y ≥ z > 0. Then k^3 ≤ 4 w^3, w^3 + x^3 < k^3 ≤ w^3 + 3 x^3
and w^3 + x^3 + y^3 < k^3 ≤ w^3 + x^3 + 2 y^3. These bounds prune the bounded search to about
174000 evaluations in total, which the kernel carries out.
-/

namespace OMA.A274334H3

open OMA.S_oeis_a274334

/-- Innermost level: no positive z ≤ y completes the sum. -/
def Search4 (k w x y : ℕ) : Prop := ∀ z ≤ y, 0 < z → w ^ 3 + x ^ 3 + y ^ 3 + z ^ 3 ≠ k ^ 3

instance (k w x y : ℕ) : Decidable (Search4 k w x y) :=
  inferInstanceAs (Decidable (∀ z ≤ y, 0 < z → w ^ 3 + x ^ 3 + y ^ 3 + z ^ 3 ≠ k ^ 3))

def Search3 (k w x : ℕ) : Prop :=
  ∀ y ≤ x, w ^ 3 + x ^ 3 + y ^ 3 < k ^ 3 → k ^ 3 ≤ w ^ 3 + x ^ 3 + 2 * y ^ 3 → Search4 k w x y

instance (k w x : ℕ) : Decidable (Search3 k w x) :=
  inferInstanceAs (Decidable (∀ y ≤ x, w ^ 3 + x ^ 3 + y ^ 3 < k ^ 3 →
    k ^ 3 ≤ w ^ 3 + x ^ 3 + 2 * y ^ 3 → Search4 k w x y))

def Search2 (k w : ℕ) : Prop :=
  ∀ x ≤ w, w ^ 3 + x ^ 3 < k ^ 3 → k ^ 3 ≤ w ^ 3 + 3 * x ^ 3 → Search3 k w x

instance (k w : ℕ) : Decidable (Search2 k w) :=
  inferInstanceAs (Decidable (∀ x ≤ w, w ^ 3 + x ^ 3 < k ^ 3 →
    k ^ 3 ≤ w ^ 3 + 3 * x ^ 3 → Search3 k w x))

/-- The pruned bounded search for sorted solutions w ≥ x ≥ y ≥ z > 0 of the cube of k. -/
def Search1 (k : ℕ) : Prop := ∀ w < k, k ^ 3 ≤ 4 * w ^ 3 → Search2 k w

instance (k : ℕ) : Decidable (Search1 k) :=
  inferInstanceAs (Decidable (∀ w < k, k ^ 3 ≤ 4 * w ^ 3 → Search2 k w))

theorem sorted_ne {k : ℕ} (hdec : Search1 k)
    (a b c d : ℕ) (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c) (hd : 0 < d) :
    a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 ≠ k ^ 3 := by
  intro e
  have h1 : b ^ 3 ≤ a ^ 3 := Nat.pow_le_pow_left hab 3
  have h2 : c ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hbc 3
  have h3 : d ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hcd 3
  have h4 : 0 < d ^ 3 := by positivity
  have ha : a < k := (Nat.pow_lt_pow_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp (by omega)
  exact hdec a ha (by omega) b hab (by omega) (by omega) c hbc (by omega) (by omega) d hcd hd e

theorem not_isTerm (k : ℕ) (hdec : Search1 k) : ¬ IsTerm k := by
  rintro ⟨w, x, y, z, hw, hx, hy, hz, e⟩
  have key := sorted_ne hdec
  rcases le_total w x with h1 | h1 <;> rcases le_total w y with h2 | h2 <;>
  rcases le_total w z with h3 | h3 <;> rcases le_total x y with h4 | h4 <;>
  rcases le_total x z with h5 | h5 <;> rcases le_total y z with h6 | h6 <;>
  first
  | exact key w x y z ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key w x z y ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key w y x z ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key w y z x ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key w z x y ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key w z y x ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key x w y z ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key x w z y ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key x y w z ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key x y z w ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key x z w y ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key x z y w ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key y w x z ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key y w z x ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key y x w z ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key y x z w ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key y z w x ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key y z x w ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key z w x y ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key z w y x ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key z x w y ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key z x y w ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key z y w x ‹_› ‹_› ‹_› ‹_› (by omega)
  | exact key z y x w ‹_› ‹_› ‹_› ‹_› (by omega)

end OMA.A274334H3

set_option maxHeartbeats 4000000 in
theorem OMA.solution : OMA.R_oeis_a274334_R1.H3 := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact OMA.A274334H3.not_isTerm _ (by decide +kernel)
