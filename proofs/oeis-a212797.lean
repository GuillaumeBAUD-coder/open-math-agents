import OMAStatements.S_oeis_a212797
import Mathlib

-- Problem: oeis-a212797 (two closed forms via linear recurrence sequences)
-- Credit: @Aijy0264561
-- Every term (a = 2 n s(n), c, g, n) is annihilated by (x - 1)^2 (x^2 - 6x + 1)^2; so each difference
-- of the two sides satisfies one order-6 recurrence and vanishes from six zero initial values.

namespace OMA.A212797proof

open OMA.S_oeis_a212797

/-- The common annihilator `(x - 1)^2 (x^2 - 6x + 1)^2`, applied at `n`. -/
def L (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  f (n + 6) - 14 * f (n + 5) + 63 * f (n + 4) - 100 * f (n + 3) + 63 * f (n + 2) -
    14 * f (n + 1) + f n

lemma s_rec (n : ℕ) : squareTriIndex (n + 2) = 6 * squareTriIndex (n + 1) - squareTriIndex n + 2 := rfl
lemma c_rec (n : ℕ) : c (n + 2) = 6 * c (n + 1) - c n := rfl
lemma g_rec (n : ℕ) : g (n + 4) = 12 * g (n + 3) - 38 * g (n + 2) + 12 * g (n + 1) - g n := rfl

lemma L_c (k : ℕ) : L (fun n => c (n + k)) 0 = 0 := by
  unfold L
  have h0 := c_rec k; have h1 := c_rec (k + 1); have h2 := c_rec (k + 2)
  have h3 := c_rec (k + 3); have h4 := c_rec (k + 4)
  simp only [show ∀ j, j + 2 + k = k + 2 + j by intro j; ring] at *
  ring_nf at *
  linear_combination h4 - 8 * h3 + 14 * h2 - 8 * h1 + h0

lemma L_g (k : ℕ) : L (fun n => g (n + k)) 0 = 0 := by
  unfold L
  have h0 := g_rec k; have h1 := g_rec (k + 1); have h2 := g_rec (k + 2)
  ring_nf at *
  linear_combination h2 - 2 * h1 + h0

lemma L_a (k : ℕ) : L (fun n => a (n + k)) 0 = 0 := by
  unfold L a
  have h0 := s_rec k; have h1 := s_rec (k + 1); have h2 := s_rec (k + 2)
  have h3 := s_rec (k + 3); have h4 := s_rec (k + 4)
  push_cast
  ring_nf at *
  linear_combination 2 * ((k : ℤ) * h0 + (-8 * (k : ℤ) - 14) * h1 + (14 * (k : ℤ) + 42) * h2 +
    (-8 * (k : ℤ) - 34) * h3 + ((k : ℤ) + 6) * h4)

lemma L_shift (f : ℕ → ℤ) (k : ℕ) : L f k = L (fun n => f (n + k)) 0 := by
  unfold L; simp only [zero_add]; ring_nf

/-- A sequence annihilated by `L` with six zero initial values vanishes. -/
lemma zero_of_L (f : ℕ → ℤ) (hL : ∀ n, L f n = 0)
    (h0 : f 0 = 0) (h1 : f 1 = 0) (h2 : f 2 = 0) (h3 : f 3 = 0) (h4 : f 4 = 0) (h5 : f 5 = 0) :
    ∀ n, f n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | m + 6, ih =>
      have := hL m
      unfold L at this
      rw [ih (m + 5) (by omega), ih (m + 4) (by omega), ih (m + 3) (by omega), ih (m + 2) (by omega),
        ih (m + 1) (by omega), ih m (by omega)] at this
      linarith

lemma L_lin (n : ℕ) : L (fun m => ((m : ℤ) + n)) 0 = 0 := by unfold L; push_cast; ring

theorem a212797 : type_of% @OMA.S_oeis_a212797.main := by
  constructor
  · intro n hn
    let f : ℕ → ℤ := fun m => a (m + 1) - (16 * c (m + 2) + 3 * c (m + 1) -
      16 * (g (m + 1) - 6 * g m) - ((m : ℤ) + 1))
    have hL : ∀ m, L f m = 0 := by
      intro m
      rw [L_shift]
      have e1 := L_a (m + 1); have e2 := L_c (m + 2); have e3 := L_c (m + 1)
      have e4 := L_g (m + 1); have e5 := L_g m; have e6 := L_lin (m + 1)
      unfold L at *
      simp only [f]
      push_cast at *
      ring_nf at *
      linear_combination e1 - 16 * e2 - 3 * e3 + 16 * e4 - 96 * e5 + e6
    have hz := zero_of_L f hL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := hz m
    simp only [f] at this
    rw [show m + 1 - 1 = m by omega]
    push_cast; linarith
  · intro n hn
    let f : ℕ → ℤ := fun m => a (m + 3) - (3 * g (m + 2) - 2 * g (m + 1) + 3 * g m - ((m : ℤ) + 3))
    have hL : ∀ m, L f m = 0 := by
      intro m
      rw [L_shift]
      have e1 := L_a (m + 3); have e2 := L_g (m + 2); have e3 := L_g (m + 1)
      have e4 := L_g m; have e6 := L_lin (m + 3)
      unfold L at *
      simp only [f]
      push_cast at *
      ring_nf at *
      linear_combination e1 - 3 * e2 + 2 * e3 - 3 * e4 + e6
    have hz := zero_of_L f hL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := hz m
    simp only [f] at this
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega]
    push_cast; linarith

end OMA.A212797proof

theorem OMA.solution : type_of% @OMA.S_oeis_a212797.main := OMA.A212797proof.a212797
