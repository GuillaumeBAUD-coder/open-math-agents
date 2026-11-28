import OMAStatements.S_oeis_a273327

-- Problem: A273327: Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by Rule 646, based on the 5-celled von Neumann neighborhood.
-- Upstream: formal-conjectures statements/oeis-a273327.lean:0 (declaration OMA.S_oeis_a273327.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset
open OMA.S_oeis_a273327

namespace OEISA273327Proof

/-! ### Part 1: Even-sublattice reduction `cell 646` -> `A` -/

private def stepA (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  let s := (f (x + 1) y).toNat + (f (x - 1) y).toNat + (f x (y + 1)).toNat + (f x (y - 1)).toNat
  if f x y then decide (s = 0 ∨ s = 1 ∨ s = 4) else decide (s = 1)

private def A : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | t + 1 => stepA (A t)

private lemma stepA_eq_rule646_two_step (c n1 n2 n3 n4 : Bool) :
    (let e1 := xor c n1
     let e2 := xor c n2
     let e3 := xor c n3
     let e4 := xor c n4
     (646 : ℕ).testBit (c.toNat + 2 * (e1.toNat + e2.toNat + e3.toNat + e4.toNat))) =
    (let s := n1.toNat + n2.toNat + n3.toNat + n4.toNat
     if c then decide (s = 0 ∨ s = 1 ∨ s = 4) else decide (s = 1)) := by
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> decide

private lemma xor_four_cycle_off (a b c d : Bool) :
    (646 : ℕ).testBit (0 + 2 * ((xor a b).toNat + (xor b c).toNat + (xor c d).toNat + (xor d a).toNat)) = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma edge_cell_dies (a b : Bool) :
    (646 : ℕ).testBit ((xor a b).toNat + 2 * (a.toNat + b.toNat + 0 + 0)) = false := by
  cases a <;> cases b <;> decide

private lemma cell_even_and_odd (t : ℕ) :
    (∀ i j : ℤ, cell 646 (2 * t) i j =
      if i % 2 = 0 ∧ j % 2 = 0 then A t (i / 2) (j / 2) else false) ∧
    (∀ i j : ℤ, cell 646 (2 * t + 1) i j =
      if i % 2 = 0 ∧ j % 2 = 0 then A t (i / 2) (j / 2)
      else if i % 2 = 1 ∧ j % 2 = 0 then xor (A t ((i - 1) / 2) (j / 2)) (A t ((i + 1) / 2) (j / 2))
      else if i % 2 = 0 ∧ j % 2 = 1 then xor (A t (i / 2) ((j - 1) / 2)) (A t (i / 2) ((j + 1) / 2))
      else false) := by
  have step_odd : ∀ (f : ℤ → ℤ → Bool) (k : ℕ),
      (∀ i j : ℤ, cell 646 k i j = if i % 2 = 0 ∧ j % 2 = 0 then f (i / 2) (j / 2) else false) →
      ∀ i j : ℤ, cell 646 (k + 1) i j =
        if i % 2 = 0 ∧ j % 2 = 0 then f (i / 2) (j / 2)
        else if i % 2 = 1 ∧ j % 2 = 0 then xor (f ((i - 1) / 2) (j / 2)) (f ((i + 1) / 2) (j / 2))
        else if i % 2 = 0 ∧ j % 2 = 1 then xor (f (i / 2) ((j - 1) / 2)) (f (i / 2) ((j + 1) / 2))
        else false := by
    intro f k hk i j
    simp only [cell, hk]
    have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hi with hi0 | hi1 <;> rcases hj with hj0 | hj1
    · have h1 : (i + 1) % 2 = 1 := by omega
      have h2 : (i - 1) % 2 = 1 := by omega
      have h3 : (j + 1) % 2 = 1 := by omega
      have h4 : (j - 1) % 2 = 1 := by omega
      simp only [hi0, hj0, h1, h2, h3, h4, and_self, true_and, and_true,
        show (1 : ℤ) ≠ 0 by omega, false_and, and_false, ↓reduceIte, Bool.toNat_false]
      cases f (i / 2) (j / 2) <;> decide
    · have h1 : (i + 1) % 2 = 1 := by omega
      have h2 : (i - 1) % 2 = 1 := by omega
      have h3 : (j + 1) % 2 = 0 := by omega
      have h4 : (j - 1) % 2 = 0 := by omega
      simp only [hi0, hj1, h1, h2, h3, h4, and_self, true_and, and_true,
        show (1 : ℤ) ≠ 0 by omega, show (0 : ℤ) ≠ 1 by omega, false_and, and_false, ↓reduceIte,
        Bool.toNat_false]
      cases f (i / 2) ((j - 1) / 2) <;> cases f (i / 2) ((j + 1) / 2) <;> decide
    · have h1 : (i + 1) % 2 = 0 := by omega
      have h2 : (i - 1) % 2 = 0 := by omega
      have h3 : (j + 1) % 2 = 1 := by omega
      have h4 : (j - 1) % 2 = 1 := by omega
      simp only [hi1, hj0, h1, h2, h3, h4, and_self, true_and, and_true,
        show (1 : ℤ) ≠ 0 by omega, show (0 : ℤ) ≠ 1 by omega, false_and, and_false, ↓reduceIte,
        Bool.toNat_false]
      cases f ((i - 1) / 2) (j / 2) <;> cases f ((i + 1) / 2) (j / 2) <;> decide
    · have h1 : (i + 1) % 2 = 0 := by omega
      have h2 : (i - 1) % 2 = 0 := by omega
      have h3 : (j + 1) % 2 = 0 := by omega
      have h4 : (j - 1) % 2 = 0 := by omega
      simp only [hi1, hj1, h1, h2, h3, h4, and_self, true_and, and_true,
        show (1 : ℤ) ≠ 0 by omega, false_and, and_false, ↓reduceIte, Bool.toNat_false]
      decide
  induction t with
  | zero =>
    have h0 : ∀ i j : ℤ, cell 646 0 i j =
        if i % 2 = 0 ∧ j % 2 = 0 then A 0 (i / 2) (j / 2) else false := by
      intro i j
      simp only [cell, A]
      split_ifs with h
      · by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj] <;> omega
      · apply decide_eq_false
        rintro ⟨rfl, rfl⟩
        exact h ⟨by omega, by omega⟩
    exact ⟨h0, step_odd (A 0) 0 h0⟩
  | succ t ih =>
    obtain ⟨_, hodd⟩ := ih
    have heven : ∀ i j : ℤ, cell 646 (2 * (t + 1)) i j =
        if i % 2 = 0 ∧ j % 2 = 0 then A (t + 1) (i / 2) (j / 2) else false := by
      intro i j
      have h2t : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
      rw [h2t, cell]
      dsimp only
      rw [hodd, hodd, hodd, hodd, hodd]
      have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
      have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
      rcases hi with hi0 | hi1 <;> rcases hj with hj0 | hj1
      · have h1 : (i + 1) % 2 = 1 := by omega
        have h2 : (i - 1) % 2 = 1 := by omega
        have h3 : (j + 1) % 2 = 1 := by omega
        have h4 : (j - 1) % 2 = 1 := by omega
        simp only [hi0, hj0, h1, h2, h3, h4, and_self, true_and, and_true,
          show (1 : ℤ) ≠ 0 by omega, false_and, and_false, ↓reduceIte]
        have hx1 : (i + 1 - 1) / 2 = i / 2 := by omega
        have hx2 : (i + 1 + 1) / 2 = i / 2 + 1 := by omega
        have hx3 : (i - 1 - 1) / 2 = i / 2 - 1 := by omega
        have hx4 : (i - 1 + 1) / 2 = i / 2 := by omega
        have hy1 : (j + 1 - 1) / 2 = j / 2 := by omega
        have hy2 : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
        have hy3 : (j - 1 - 1) / 2 = j / 2 - 1 := by omega
        have hy4 : (j - 1 + 1) / 2 = j / 2 := by omega
        rw [hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4]
        have hxc1 : xor (A t (i / 2 - 1) (j / 2)) (A t (i / 2) (j / 2)) =
            xor (A t (i / 2) (j / 2)) (A t (i / 2 - 1) (j / 2)) := Bool.xor_comm _ _
        have hyc1 : xor (A t (i / 2) (j / 2 - 1)) (A t (i / 2) (j / 2)) =
            xor (A t (i / 2) (j / 2)) (A t (i / 2) (j / 2 - 1)) := Bool.xor_comm _ _
        rw [hxc1, hyc1]
        exact stepA_eq_rule646_two_step (A t (i / 2) (j / 2))
          (A t (i / 2 + 1) (j / 2)) (A t (i / 2 - 1) (j / 2))
          (A t (i / 2) (j / 2 + 1)) (A t (i / 2) (j / 2 - 1))
      · have h1 : (i + 1) % 2 = 1 := by omega
        have h2 : (i - 1) % 2 = 1 := by omega
        have h3 : (j + 1) % 2 = 0 := by omega
        have h4 : (j - 1) % 2 = 0 := by omega
        simp only [hi0, hj1, h1, h2, h3, h4, and_self, true_and, and_true,
          show (1 : ℤ) ≠ 0 by omega, show (0 : ℤ) ≠ 1 by omega, false_and, and_false, ↓reduceIte,
          Bool.toNat_false]
        have hadd : 0 + 0 + (A t (i / 2) ((j + 1) / 2)).toNat + (A t (i / 2) ((j - 1) / 2)).toNat =
            (A t (i / 2) ((j - 1) / 2)).toNat + (A t (i / 2) ((j + 1) / 2)).toNat + 0 + 0 := by omega
        rw [hadd]
        exact edge_cell_dies (A t (i / 2) ((j - 1) / 2)) (A t (i / 2) ((j + 1) / 2))
      · have h1 : (i + 1) % 2 = 0 := by omega
        have h2 : (i - 1) % 2 = 0 := by omega
        have h3 : (j + 1) % 2 = 1 := by omega
        have h4 : (j - 1) % 2 = 1 := by omega
        simp only [hi1, hj0, h1, h2, h3, h4, and_self, true_and, and_true,
          show (1 : ℤ) ≠ 0 by omega, show (0 : ℤ) ≠ 1 by omega, false_and, and_false, ↓reduceIte,
          Bool.toNat_false]
        have hadd : (A t ((i + 1) / 2) (j / 2)).toNat + (A t ((i - 1) / 2) (j / 2)).toNat + 0 + 0 =
            (A t ((i - 1) / 2) (j / 2)).toNat + (A t ((i + 1) / 2) (j / 2)).toNat + 0 + 0 := by omega
        rw [hadd]
        exact edge_cell_dies (A t ((i - 1) / 2) (j / 2)) (A t ((i + 1) / 2) (j / 2))
      · have h1 : (i + 1) % 2 = 0 := by omega
        have h2 : (i - 1) % 2 = 0 := by omega
        have h3 : (j + 1) % 2 = 0 := by omega
        have h4 : (j - 1) % 2 = 0 := by omega
        simp only [hi1, hj1, h1, h2, h3, h4, and_self, true_and, and_true,
          show (1 : ℤ) ≠ 0 by omega, false_and, and_false, ↓reduceIte, Bool.toNat_false]
        let u := (i - 1) / 2
        let v := (j - 1) / 2
        have hx1 : (i + 1) / 2 = u + 1 := by omega
        have hy1 : (j + 1) / 2 = v + 1 := by omega
        have hx2 : (i - 1 - 1) / 2 = u - 1 := by omega
        have hx3 : (i + 1 - 1) / 2 = u := by omega
        have hx4 : (i + 1 + 1) / 2 = u + 1 := by omega
        have hx5 : (i - 1 + 1) / 2 = u := by omega
        have hy3 : (j + 1 - 1) / 2 = v := by omega
        have hy4 : (j + 1 + 1) / 2 = v + 1 := by omega
        have hy5 : (j - 1 + 1) / 2 = v := by omega
        simp only [hx1, hy1, hx3, hy3, hx5, hy5, show (i - 1) / 2 = u by rfl, show (j - 1) / 2 = v by rfl]
        have hq : (xor (A t (u + 1) v) (A t (u + 1) (v + 1))).toNat +
            (xor (A t u v) (A t u (v + 1))).toNat +
            (xor (A t u (v + 1)) (A t (u + 1) (v + 1))).toNat +
            (xor (A t u v) (A t (u + 1) v)).toNat =
            (xor (A t u v) (A t (u + 1) v)).toNat +
            (xor (A t (u + 1) v) (A t (u + 1) (v + 1))).toNat +
            (xor (A t (u + 1) (v + 1)) (A t u (v + 1))).toNat +
            (xor (A t u (v + 1)) (A t u v)).toNat := by
          rw [Bool.xor_comm (A t (u + 1) (v + 1)) (A t u (v + 1)),
              Bool.xor_comm (A t u (v + 1)) (A t u v)]
          omega
        rw [hq]
        exact xor_four_cycle_off (A t u v) (A t (u + 1) v) (A t (u + 1) (v + 1)) (A t u (v + 1))
    exact ⟨heven, step_odd (A (t + 1)) (2 * (t + 1)) heven⟩

/-! ### Part 2: Symmetries, light cone, diagonal-off, and origin-on for `A` -/

private lemma stepA_congr {f g : ℤ → ℤ → Bool} {x y : ℤ}
    (h0 : f x y = g x y) (h1 : f (x + 1) y = g (x + 1) y) (h2 : f (x - 1) y = g (x - 1) y)
    (h3 : f x (y + 1) = g x (y + 1)) (h4 : f x (y - 1) = g x (y - 1)) :
    stepA f x y = stepA g x y := by
  simp only [stepA, h0, h1, h2, h3, h4]

private lemma stepA_congr' {f g : ℤ → ℤ → Bool} {x y u v : ℤ}
    (h0 : f x y = g u v) (h1 : f (x + 1) y = g (u + 1) v) (h2 : f (x - 1) y = g (u - 1) v)
    (h3 : f x (y + 1) = g u (v + 1)) (h4 : f x (y - 1) = g u (v - 1)) :
    stepA f x y = stepA g u v := by
  simp only [stepA, h0, h1, h2, h3, h4]

private lemma A_support (t : ℕ) : ∀ x y : ℤ, t < x.natAbs + y.natAbs → A t x y = false := by
  induction t with
  | zero =>
    intro x y h
    simp only [A]
    apply decide_eq_false
    rintro ⟨rfl, rfl⟩
    simp at h
  | succ t ih =>
    intro x y h
    simp only [A, stepA]
    have h0 : A t x y = false := ih x y (by omega)
    have h1 : A t (x + 1) y = false := ih (x + 1) y (by omega)
    have h2 : A t (x - 1) y = false := ih (x - 1) y (by omega)
    have h3 : A t x (y + 1) = false := ih x (y + 1) (by omega)
    have h4 : A t x (y - 1) = false := ih x (y - 1) (by omega)
    simp [h0, h1, h2, h3, h4]

private lemma A_symm (t : ℕ) :
    (∀ x y : ℤ, A t (-x) y = A t x y) ∧
    (∀ x y : ℤ, A t x (-y) = A t x y) ∧
    (∀ x y : ℤ, A t y x = A t x y) := by
  induction t with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intro x y <;> simp [A] <;>
      (by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy])
  | succ t ih =>
    obtain ⟨ihx, ihy, ihs⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      simp only [A, stepA]
      have h1 : A t (-x + 1) y = A t (x - 1) y := by rw [← ihx (x - 1) y]; congr 1; omega
      have h2 : A t (-x - 1) y = A t (x + 1) y := by rw [← ihx (x + 1) y]; congr 1; omega
      rw [ihx x y, h1, h2, ihx x (y + 1), ihx x (y - 1)]
      have hsum : (A t (x - 1) y).toNat + (A t (x + 1) y).toNat + (A t x (y + 1)).toNat + (A t x (y - 1)).toNat =
          (A t (x + 1) y).toNat + (A t (x - 1) y).toNat + (A t x (y + 1)).toNat + (A t x (y - 1)).toNat := by omega
      simp only [hsum]
    · intro x y
      simp only [A, stepA]
      have h3 : A t x (-y + 1) = A t x (y - 1) := by rw [← ihy x (y - 1)]; congr 1; omega
      have h4 : A t x (-y - 1) = A t x (y + 1) := by rw [← ihy x (y + 1)]; congr 1; omega
      rw [ihy x y, ihy (x + 1) y, ihy (x - 1) y, h3, h4]
      have hsum : (A t (x + 1) y).toNat + (A t (x - 1) y).toNat + (A t x (y - 1)).toNat + (A t x (y + 1)).toNat =
          (A t (x + 1) y).toNat + (A t (x - 1) y).toNat + (A t x (y + 1)).toNat + (A t x (y - 1)).toNat := by omega
      simp only [hsum]
    · intro x y
      simp only [A, stepA]
      rw [ihs x y, ihs x (y + 1), ihs x (y - 1), ihs (x + 1) y, ihs (x - 1) y]
      have hsum : (A t x (y + 1)).toNat + (A t x (y - 1)).toNat + (A t (x + 1) y).toNat + (A t (x - 1) y).toNat =
          (A t (x + 1) y).toNat + (A t (x - 1) y).toNat + (A t x (y + 1)).toNat + (A t x (y - 1)).toNat := by omega
      simp only [hsum]

private lemma A_diag_false (t : ℕ) : ∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → A t x y = false := by
  induction t with
  | zero =>
    intro x y hx _
    simp [A, hx]
  | succ t ih =>
    intro x y hx hxy
    have ⟨hsx, hsy, hss⟩ := A_symm t
    have h0 : A t x y = false := ih x y hx hxy
    simp only [A, stepA, h0]
    have hcases : y = x ∨ y = -x := by omega
    rcases hcases with hy | hy
    · rw [hy]
      have h1 : A t x (x + 1) = A t (x + 1) x := hss (x + 1) x
      have h2 : A t x (x - 1) = A t (x - 1) x := hss (x - 1) x
      rw [h1, h2]
      cases A t (x + 1) x <;> cases A t (x - 1) x <;> decide
    · rw [hy]
      have h1 : A t x (-x + 1) = A t (x - 1) (-x) := by
        rw [← hsy x (-x + 1), show -(-x + 1) = x - 1 by omega, ← hss x (x - 1), ← hsy (x - 1) x]
      have h2 : A t x (-x - 1) = A t (x + 1) (-x) := by
        rw [← hsy x (-x - 1), show -(-x - 1) = x + 1 by omega, ← hss x (x + 1), ← hsy (x + 1) x]
      rw [h1, h2]
      cases A t (x + 1) (-x) <;> cases A t (x - 1) (-x) <;> decide

private lemma A_origin_true (t : ℕ) : A t 0 0 = true := by
  induction t with
  | zero => decide
  | succ t ih =>
    have ⟨hsx, hsy, hss⟩ := A_symm t
    simp only [A, stepA, ih]
    have h1 : A t (-1) 0 = A t 1 0 := hsx 1 0
    have h2 : A t 0 1 = A t 1 0 := hss 1 0
    have h3 : A t 0 (-1) = A t 1 0 := by rw [hsy 0 1, hss 1 0]
    simp only [zero_add, zero_sub, h1, h2, h3]
    cases A t 1 0 <;> decide

/-! ### Part 3: Recursive static interior pattern `Static m` (`m ≥ 2`) -/

private def Static : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide ((x.natAbs + y.natAbs) % 2 = 1 ∨ (x = 0 ∧ y = 0))
  | 1, x, y => decide ((x.natAbs + y.natAbs) % 2 = 1 ∨ (x = 0 ∧ y = 0))
  | 2, x, y => decide ((x.natAbs + y.natAbs) % 2 = 1 ∨ (x = 0 ∧ y = 0))
  | m + 3, x, y =>
    let M : ℕ := 2 ^ (m + 2)
    if x.natAbs + y.natAbs < M then Static (m + 2) x y
    else if x.natAbs = y.natAbs then false
    else if y.natAbs < x.natAbs then
      if 0 < x then Static (m + 2) (x - M) y else Static (m + 2) (x + M) y
    else
      if 0 < y then Static (m + 2) x (y - M) else Static (m + 2) x (y + M)

private lemma Static_symm (m : ℕ) :
    (∀ x y : ℤ, Static m (-x) y = Static m x y) ∧
    (∀ x y : ℤ, Static m x (-y) = Static m x y) ∧
    (∀ x y : ℤ, Static m y x = Static m x y) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intro x y <;> simp only [Static, Int.natAbs_neg] <;>
      (try rw [add_comm y.natAbs x.natAbs]) <;>
      (by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy])
  | succ m ih =>
    cases m with
    | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> intro x y <;> simp only [Static, Int.natAbs_neg] <;>
        (try rw [add_comm y.natAbs x.natAbs]) <;>
        (by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy])
    | succ m =>
      cases m with
      | zero =>
        refine ⟨?_, ?_, ?_⟩ <;> intro x y <;> simp only [Static, Int.natAbs_neg] <;>
          (try rw [add_comm y.natAbs x.natAbs]) <;>
          (by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy])
      | succ k =>
        obtain ⟨ihx, ihy, ihs⟩ := ih
        refine ⟨?_, ?_, ?_⟩
        · intro x y
          simp only [Static, Int.natAbs_neg]
          split_ifs with hlt heq hylt hxneg hxpos hypos
          · exact ihx x y
          · rfl
          · exfalso; omega
          · rw [← ihx (x + (2 ^ (k + 2) : ℕ)) y]; congr 1; omega
          · rw [← ihx (x - (2 ^ (k + 2) : ℕ)) y]; congr 1; omega
          · exfalso; omega
          · exact ihx x (y - (2 ^ (k + 2) : ℕ))
          · exact ihx x (y + (2 ^ (k + 2) : ℕ))
        · intro x y
          simp only [Static, Int.natAbs_neg]
          split_ifs with hlt heq hylt hxpos hyneg hypos
          · exact ihy x y
          · rfl
          · exact ihy (x - (2 ^ (k + 2) : ℕ)) y
          · exact ihy (x + (2 ^ (k + 2) : ℕ)) y
          · exfalso; omega
          · rw [← ihy x (y + (2 ^ (k + 2) : ℕ))]; congr 1; omega
          · rw [← ihy x (y - (2 ^ (k + 2) : ℕ))]; congr 1; omega
          · exfalso; omega
        · intro x y
          simp only [Static]
          have hadd : y.natAbs + x.natAbs = x.natAbs + y.natAbs := add_comm _ _
          rw [hadd]
          by_cases hlt : x.natAbs + y.natAbs < 2 ^ (k + 2)
          · simp only [if_pos hlt]; exact ihs x y
          · simp only [if_neg hlt]
            by_cases heq : x.natAbs = y.natAbs
            · simp only [heq, ↓reduceIte]
            · simp only [if_neg heq, if_neg (Ne.symm heq)]
              by_cases hylt : y.natAbs < x.natAbs
              · simp only [if_pos hylt, if_neg (by omega : ¬ (x.natAbs < y.natAbs))]
                by_cases hx : 0 < x
                · simp only [if_pos hx]; exact ihs (x - (2 ^ (k + 2) : ℕ)) y
                · simp only [if_neg hx]; exact ihs (x + (2 ^ (k + 2) : ℕ)) y
              · simp only [if_neg hylt, if_pos (by omega : x.natAbs < y.natAbs)]
                by_cases hy : 0 < y
                · simp only [if_pos hy]; exact ihs x (y - (2 ^ (k + 2) : ℕ))
                · simp only [if_neg hy]; exact ihs x (y + (2 ^ (k + 2) : ℕ))

private lemma Static_odd (m : ℕ) (hm : 2 ≤ m) :
    ∀ x y : ℤ, x.natAbs + y.natAbs < 2 ^ m → (x.natAbs + y.natAbs) % 2 = 1 → Static m x y = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero =>
        intro x y _ hodd
        simp [Static, hodd]
      | succ k =>
        intro x y hlt hodd
        have hpow : 2 ^ (k + 1 + 1 + 1) = 2 * 2 ^ (k + 2) := by ring
        rw [hpow] at hlt
        have hM4 : 4 ≤ 2 ^ (k + 2) := by
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 2 ≤ k + 2 by omega)
          simpa using this
        have hMeven : 2 ∣ 2 ^ (k + 2) := ⟨2 ^ (k + 1), by ring⟩
        simp only [Static]
        split_ifs with h1 h2 h3 h4 h5
        · exact ih (by omega) x y h1 hodd
        · omega
        · exact ih (by omega) (x - (2 ^ (k + 2) : ℕ)) y (by omega) (by omega)
        · exact ih (by omega) (x + (2 ^ (k + 2) : ℕ)) y (by omega) (by omega)
        · exact ih (by omega) x (y - (2 ^ (k + 2) : ℕ)) (by omega) (by omega)
        · exact ih (by omega) x (y + (2 ^ (k + 2) : ℕ)) (by omega) (by omega)

private lemma Static_even_mod4 (m : ℕ) (hm : 2 ≤ m) :
    ∀ x y : ℤ, x.natAbs + y.natAbs < 2 ^ m → (x.natAbs + y.natAbs) % 2 = 0 →
      Static m x y = true → 4 ∣ x.natAbs ∧ 4 ∣ y.natAbs := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero =>
        intro x y _ heven hst
        simp only [Static, heven, show (0 : ℕ) ≠ 1 by omega, false_or, decide_eq_true_eq] at hst
        rcases hst with ⟨rfl, rfl⟩
        exact ⟨by norm_num, by norm_num⟩
      | succ k =>
        intro x y hlt heven hst
        have hpow : 2 ^ (k + 1 + 1 + 1) = 2 * 2 ^ (k + 2) := by ring
        rw [hpow] at hlt
        have hM4 : 4 ∣ 2 ^ (k + 2) := ⟨2 ^ k, by ring⟩
        have hMge4 : 4 ≤ 2 ^ (k + 2) := by
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 2 ≤ k + 2 by omega)
          simpa using this
        simp only [Static] at hst
        by_cases h1 : x.natAbs + y.natAbs < 2 ^ (k + 2)
        · rw [if_pos h1] at hst; exact ih (by omega) x y h1 heven hst
        · rw [if_neg h1] at hst
          by_cases h2 : x.natAbs = y.natAbs
          · rw [if_pos h2] at hst; cases hst
          · rw [if_neg h2] at hst
            by_cases h3 : y.natAbs < x.natAbs
            · rw [if_pos h3] at hst
              by_cases h4 : 0 < x
              · rw [if_pos h4] at hst
                have ⟨hd1, hd2⟩ := ih (by omega) (x - (2 ^ (k + 2) : ℕ)) y (by omega) (by omega) hst
                exact ⟨by omega, hd2⟩
              · rw [if_neg h4] at hst
                have ⟨hd1, hd2⟩ := ih (by omega) (x + (2 ^ (k + 2) : ℕ)) y (by omega) (by omega) hst
                exact ⟨by omega, hd2⟩
            · rw [if_neg h3] at hst
              by_cases h5 : 0 < y
              · rw [if_pos h5] at hst
                have ⟨hd1, hd2⟩ := ih (by omega) x (y - (2 ^ (k + 2) : ℕ)) (by omega) (by omega) hst
                exact ⟨hd1, by omega⟩
              · rw [if_neg h5] at hst
                have ⟨hd1, hd2⟩ := ih (by omega) x (y + (2 ^ (k + 2) : ℕ)) (by omega) (by omega) hst
                exact ⟨hd1, by omega⟩

private lemma Static_origin (m : ℕ) (hm : 2 ≤ m) : Static m 0 0 = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => decide
      | succ k =>
        simp only [Static, Int.natAbs_zero, add_zero, Nat.two_pow_pos, ↓reduceIte]
        exact ih (by omega)

private lemma Static_diag_false (m : ℕ) (hm : 2 ≤ m) :
    ∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → x.natAbs + y.natAbs < 2 ^ m → Static m x y = false := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero =>
        intro x y hx hxy _
        simp only [Static]
        apply decide_eq_false
        omega
      | succ k =>
        intro x y hx hxy hlt
        simp only [Static]
        by_cases h1 : x.natAbs + y.natAbs < 2 ^ (k + 2)
        · rw [if_pos h1]; exact ih (by omega) x y hx hxy h1
        · rw [if_neg h1, if_pos hxy]

private lemma stepA_static_interior {m : ℕ} (hm : 2 ≤ m) {f : ℤ → ℤ → Bool}
    (hf_in : ∀ x y : ℤ, x.natAbs + y.natAbs < 2 ^ m → f x y = Static m x y)
    (hf_seam : ∀ x y : ℤ, x.natAbs + y.natAbs = 2 ^ m → x ≠ 0 → y ≠ 0 → f x y = false) :
    ∀ x y : ℤ, x.natAbs + y.natAbs < 2 ^ m → stepA f x y = Static m x y := by
  intro x y hlt
  have hM4 : 4 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    simpa using this
  have hMdiv4 : 4 ∣ 2 ^ m := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    exact ⟨2 ^ k, by ring⟩
  by_cases hpar : (x.natAbs + y.natAbs) % 2 = 1
  · have hst : Static m x y = true := Static_odd m hm x y hlt hpar
    have hfx : f x y = true := by rw [hf_in x y hlt, hst]
    rw [hst]
    simp only [stepA, hfx, ↓reduceIte]
    have hatmost1 : (f (x + 1) y).toNat + (f (x - 1) y).toNat +
        (f x (y + 1)).toNat + (f x (y - 1)).toNat ≤ 1 := by
      have hdiv4_nbr : ∀ u v : ℤ, u.natAbs + v.natAbs ≤ 2 ^ m → (u.natAbs + v.natAbs) % 2 = 0 →
          f u v = true → 4 ∣ u.natAbs ∧ 4 ∣ v.natAbs := by
        intro u v hle hev hfu
        rcases lt_or_eq_of_le hle with hlt' | heq'
        · rw [hf_in u v hlt'] at hfu
          exact Static_even_mod4 m hm u v hlt' hev hfu
        · by_cases hu : u = 0
          · subst hu; simp only [Int.natAbs_zero, zero_add] at heq' ⊢
            exact ⟨dvd_zero 4, heq' ▸ hMdiv4⟩
          · by_cases hv : v = 0
            · subst hv; simp only [Int.natAbs_zero, add_zero] at heq' ⊢
              exact ⟨heq' ▸ hMdiv4, dvd_zero 4⟩
            · rw [hf_seam u v heq' hu hv] at hfu; cases hfu
      have h1 : f (x + 1) y = true → 4 ∣ (x + 1).natAbs ∧ 4 ∣ y.natAbs :=
        hdiv4_nbr (x + 1) y (by omega) (by omega)
      have h2 : f (x - 1) y = true → 4 ∣ (x - 1).natAbs ∧ 4 ∣ y.natAbs :=
        hdiv4_nbr (x - 1) y (by omega) (by omega)
      have h3 : f x (y + 1) = true → 4 ∣ x.natAbs ∧ 4 ∣ (y + 1).natAbs :=
        hdiv4_nbr x (y + 1) (by omega) (by omega)
      have h4 : f x (y - 1) = true → 4 ∣ x.natAbs ∧ 4 ∣ (y - 1).natAbs :=
        hdiv4_nbr x (y - 1) (by omega) (by omega)
      cases hf1 : f (x + 1) y <;> cases hf2 : f (x - 1) y <;>
        cases hf3 : f x (y + 1) <;> cases hf4 : f x (y - 1) <;>
        simp only [Bool.toNat_true, Bool.toNat_false] <;>
        try omega
      all_goals
        first
        | (have := h1 hf1; have := h2 hf2; omega)
        | (have := h1 hf1; have := h3 hf3; omega)
        | (have := h1 hf1; have := h4 hf4; omega)
        | (have := h2 hf2; have := h3 hf3; omega)
        | (have := h2 hf2; have := h4 hf4; omega)
        | (have := h3 hf3; have := h4 hf4; omega)
    apply decide_eq_true
    omega
  · have hev : (x.natAbs + y.natAbs) % 2 = 0 := by omega
    have hle2 : x.natAbs + y.natAbs ≤ 2 ^ m - 2 := by omega
    have hn1 : f (x + 1) y = true := by
      rw [hf_in (x + 1) y (by omega)]
      exact Static_odd m hm (x + 1) y (by omega) (by omega)
    have hn2 : f (x - 1) y = true := by
      rw [hf_in (x - 1) y (by omega)]
      exact Static_odd m hm (x - 1) y (by omega) (by omega)
    have hn3 : f x (y + 1) = true := by
      rw [hf_in x (y + 1) (by omega)]
      exact Static_odd m hm x (y + 1) (by omega) (by omega)
    have hn4 : f x (y - 1) = true := by
      rw [hf_in x (y - 1) (by omega)]
      exact Static_odd m hm x (y - 1) (by omega) (by omega)
    simp only [stepA, hf_in x y hlt, hn1, hn2, hn3, hn4, Bool.toNat_true]
    cases Static m x y <;> decide

/-! ### Part 4: Doubling invariant `A (2^m + r) = Combine (2^m) (Static m) (A r)` -/

private def Combine (M : ℕ) (g_in g_out : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  if x.natAbs + y.natAbs < M then g_in x y
  else if x.natAbs = y.natAbs then false
  else if y.natAbs < x.natAbs then
    if 0 < x then g_out (x - M) y else g_out (x + M) y
  else
    if 0 < y then g_out x (y - M) else g_out x (y + M)

private lemma Combine_symm {M : ℕ} {g_in g_out : ℤ → ℤ → Bool}
    (hin : (∀ x y : ℤ, g_in (-x) y = g_in x y) ∧
           (∀ x y : ℤ, g_in x (-y) = g_in x y) ∧
           (∀ x y : ℤ, g_in y x = g_in x y))
    (hout : (∀ x y : ℤ, g_out (-x) y = g_out x y) ∧
            (∀ x y : ℤ, g_out x (-y) = g_out x y) ∧
            (∀ x y : ℤ, g_out y x = g_out x y)) :
    (∀ x y : ℤ, Combine M g_in g_out (-x) y = Combine M g_in g_out x y) ∧
    (∀ x y : ℤ, Combine M g_in g_out x (-y) = Combine M g_in g_out x y) ∧
    (∀ x y : ℤ, Combine M g_in g_out y x = Combine M g_in g_out x y) := by
  obtain ⟨hinx, hiny, hins⟩ := hin
  obtain ⟨houtx, houty, houts⟩ := hout
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simp only [Combine, Int.natAbs_neg]
    split_ifs with hlt heq hylt hxneg hxpos hypos
    · exact hinx x y
    · rfl
    · exfalso; omega
    · rw [← houtx (x + M) y]; congr 1; omega
    · rw [← houtx (x - M) y]; congr 1; omega
    · exfalso; omega
    · exact houtx x (y - M)
    · exact houtx x (y + M)
  · intro x y
    simp only [Combine, Int.natAbs_neg]
    by_cases hlt : x.natAbs + y.natAbs < M
    · simp only [if_pos hlt]; exact hiny x y
    · simp only [if_neg hlt]
      by_cases heq : x.natAbs = y.natAbs
      · simp only [if_pos heq]
      · simp only [if_neg heq]
        by_cases hylt : y.natAbs < x.natAbs
        · simp only [if_pos hylt]
          by_cases hx : 0 < x
          · simp only [if_pos hx]; exact houty (x - M) y
          · simp only [if_neg hx]; exact houty (x + M) y
        · simp only [if_neg hylt]
          by_cases hy : 0 < y
          · simp only [if_pos hy, if_neg (by omega : ¬ (0 < -y))]
            rw [← houty x (y - M)]; congr 1; omega
          · simp only [if_neg hy, if_pos (by omega : 0 < -y)]
            rw [← houty x (y + M)]; congr 1; omega
  · intro x y
    simp only [Combine]
    rw [add_comm y.natAbs x.natAbs]
    by_cases hlt : x.natAbs + y.natAbs < M
    · simp only [if_pos hlt]; exact hins x y
    · simp only [if_neg hlt]
      by_cases heq : x.natAbs = y.natAbs
      · simp only [heq, ↓reduceIte]
      · simp only [if_neg heq, if_neg (Ne.symm heq)]
        by_cases hylt : y.natAbs < x.natAbs
        · simp only [if_pos hylt, if_neg (by omega : ¬ (x.natAbs < y.natAbs))]
          by_cases hx : 0 < x
          · simp only [if_pos hx]; exact houts (x - M) y
          · simp only [if_neg hx]; exact houts (x + M) y
        · simp only [if_neg hylt, if_pos (by omega : x.natAbs < y.natAbs)]
          by_cases hy : 0 < y
          · simp only [if_pos hy]; exact houts x (y - M)
          · simp only [if_neg hy]; exact houts x (y + M)

private lemma stepA_symm_reduce {f g : ℤ → ℤ → Bool}
    (hf : (∀ x y : ℤ, f (-x) y = f x y) ∧ (∀ x y : ℤ, f x (-y) = f x y) ∧ (∀ x y : ℤ, f y x = f x y))
    (hg : (∀ x y : ℤ, g (-x) y = g x y) ∧ (∀ x y : ℤ, g x (-y) = g x y) ∧ (∀ x y : ℤ, g y x = g x y))
    (hcone : ∀ x y : ℤ, 0 < x → y.natAbs < x.natAbs → f x y = g x y)
    (hdiag : ∀ x y : ℤ, x.natAbs = y.natAbs → f x y = g x y) :
    ∀ x y : ℤ, f x y = g x y := by
  intro x y
  by_cases hxy : x.natAbs = y.natAbs
  · exact hdiag x y hxy
  · by_cases hlt : y.natAbs < x.natAbs
    · by_cases hx : 0 < x
      · exact hcone x y hx hlt
      · rw [← hf.1 x y, ← hg.1 x y]
        exact hcone (-x) y (by omega) (by simp only [Int.natAbs_neg]; omega)
    · rw [← hf.2.2 x y, ← hg.2.2 x y]
      by_cases hy : 0 < y
      · exact hcone y x hy (by omega)
      · rw [← hf.1 y x, ← hg.1 y x]
        exact hcone (-y) x (by omega) (by simp only [Int.natAbs_neg]; omega)

private lemma Combine_right_cone {M : ℕ} {g_in g_out : ℤ → ℤ → Bool} {x y : ℤ}
    (hge : M ≤ x.natAbs + y.natAbs) (hx : 0 < x) (hlt : y.natAbs < x.natAbs) :
    Combine M g_in g_out x y = g_out (x - M) y := by
  simp only [Combine, if_neg (by omega : ¬ (x.natAbs + y.natAbs < M)),
    if_neg (by omega : ¬ (x.natAbs = y.natAbs)), if_pos hlt, if_pos hx]

private lemma stepA_combine {m r : ℕ} (hm : 2 ≤ m) (hr1 : 1 ≤ r) (hrm : r < 2 ^ m)
    (hcur : ∀ x y : ℤ, A (2 ^ m + r) x y = Combine (2 ^ m) (Static m) (A r) x y) :
    ∀ x y : ℤ, A (2 ^ m + r + 1) x y = Combine (2 ^ m) (Static m) (A (r + 1)) x y := by
  set M : ℕ := 2 ^ m
  have hM4 : 4 ≤ M := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    simpa [M] using this
  have hMeven : M % 2 = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    have : 2 ^ (k + 2) = 2 * (2 ^ (k + 1)) := by ring
    omega
  have hseam : ∀ x y : ℤ, x.natAbs + y.natAbs = M → x ≠ 0 → y ≠ 0 → A (M + r) x y = false := by
    intro x y hsum hx hy
    rw [hcur x y]
    simp only [Combine]
    split_ifs with h1 h2 h3 h4 h5
    · omega
    · rfl
    · exact A_diag_false r (x - M) y (by omega) (by omega)
    · exact A_diag_false r (x + M) y (by omega) (by omega)
    · exact A_diag_false r x (y - M) (by omega) (by omega)
    · exact A_diag_false r x (y + M) (by omega) (by omega)
  have h_in : ∀ x y : ℤ, x.natAbs + y.natAbs < M → A (M + r + 1) x y = Static m x y := by
    intro x y hlt
    change stepA (A (M + r)) x y = Static m x y
    exact stepA_static_interior hm
      (fun u v huv => by rw [hcur u v]; simp only [Combine, if_pos (show u.natAbs + v.natAbs < M from huv)])
      hseam x y hlt
  have hcsymm := Combine_symm (M := M) (Static_symm m) (A_symm (r + 1))
  apply stepA_symm_reduce (A_symm (M + r + 1)) hcsymm
  · intro x y hx hlt
    by_cases hin : x.natAbs + y.natAbs < M
    · rw [h_in x y hin]; simp [Combine, hin]
    · have hge : M ≤ x.natAbs + y.natAbs := by omega
      rw [Combine_right_cone hge hx hlt]
      by_cases hbd : x.natAbs + y.natAbs = M
      · by_cases hy : y = 0
        · subst hy
          have hxM : x = M := by omega
          subst hxM
          rw [show (M : ℤ) - M = 0 by ring, A_origin_true (r + 1)]
          change stepA (A (M + r)) M 0 = true
          have h0 : A (M + r) M 0 = true := by
            rw [hcur, Combine_right_cone (by omega) (by omega) (by omega),
              show (M : ℤ) - M = 0 by ring, A_origin_true r]
          have hL : A (M + r) ((M : ℤ) - 1) 0 = true := by
            rw [hcur]; simp only [Combine, Int.natAbs_zero, add_zero]
            rw [if_pos (by omega)]
            exact Static_odd m hm ((M : ℤ) - 1) 0 (by omega) (by omega)
          have hR : A (M + r) ((M : ℤ) + 1) 0 = A r 1 0 := by
            rw [hcur, Combine_right_cone (by omega) (by omega) (by omega)]
            congr 1; omega
          have hU : A (M + r) M 1 = A r 1 0 := by
            rw [hcur, Combine_right_cone (by omega) (by omega) (by omega),
              show (M : ℤ) - M = 0 by ring, (A_symm r).2.2]
          have hD : A (M + r) M (-1) = A r 1 0 := by
            rw [hcur, Combine_right_cone (by omega) (by omega) (by omega),
              show (M : ℤ) - M = 0 by ring, (A_symm r).2.1, (A_symm r).2.2]
          simp only [stepA, h0, hR, hL, hU, hD, zero_add, zero_sub, ↓reduceIte]
          cases A r 1 0 <;> decide
        · have hdiag_rhs : A (r + 1) (x - M) y = false :=
            A_diag_false (r + 1) (x - M) y (by omega) (by omega)
          rw [hdiag_rhs]
          change stepA (A (M + r)) x y = false
          have h0 : A (M + r) x y = false := hseam x y hbd (by omega) hy
          have hL : A (M + r) (x - 1) y = true := by
            rw [hcur]; simp only [Combine, if_pos (by omega : (x - 1).natAbs + y.natAbs < M)]
            exact Static_odd m hm (x - 1) y (by omega) (by omega)
          by_cases hypos : 0 < y
          · have hD : A (M + r) x (y - 1) = true := by
              rw [hcur]; simp only [Combine, if_pos (by omega : x.natAbs + (y - 1).natAbs < M)]
              exact Static_odd m hm x (y - 1) (by omega) (by omega)
            simp only [stepA, h0, hL, hD, Bool.false_eq_true, ↓reduceIte, Bool.toNat_true]
            apply decide_eq_false; omega
          · have hU : A (M + r) x (y + 1) = true := by
              rw [hcur]; simp only [Combine, if_pos (by omega : x.natAbs + (y + 1).natAbs < M)]
              exact Static_odd m hm x (y + 1) (by omega) (by omega)
            simp only [stepA, h0, hL, hU, Bool.false_eq_true, ↓reduceIte, Bool.toNat_true]
            apply decide_eq_false; omega
      · have hgt : M < x.natAbs + y.natAbs := by omega
        change stepA (A (M + r)) x y = stepA (A r) (x - M) y
        have hnbr : ∀ u v : ℤ, M ≤ u.natAbs + v.natAbs → 0 < u → v.natAbs ≤ u.natAbs →
            A (M + r) u v = A r (u - M) v := by
          intro u v hge' hu hle'
          rw [hcur u v]
          rcases lt_or_eq_of_le hle' with hlt' | heq'
          · exact Combine_right_cone hge' hu hlt'
          · simp only [Combine, if_neg (by omega : ¬ (u.natAbs + v.natAbs < M)), if_pos heq'.symm]
            by_cases hsmall : 2 * u.natAbs = M
            · exact (A_diag_false r (u - M) v (by omega) (by omega)).symm
            · exact (A_support r (u - M) v (by omega)).symm
        have heq0 : A (M + r) x y = A r (x - M) y := hnbr x y hge hx (by omega)
        have heq1 : A (M + r) (x + 1) y = A r (x - M + 1) y := by
          rw [show x - M + 1 = (x + 1) - M by ring]
          exact hnbr (x + 1) y (by omega) (by omega) (by omega)
        have heq2 : A (M + r) (x - 1) y = A r (x - M - 1) y := by
          rw [show x - M - 1 = (x - 1) - M by ring]
          exact hnbr (x - 1) y (by omega) (by omega) (by omega)
        have heq3 : A (M + r) x (y + 1) = A r (x - M) (y + 1) :=
          hnbr x (y + 1) (by omega) hx (by omega)
        have heq4 : A (M + r) x (y - 1) = A r (x - M) (y - 1) :=
          hnbr x (y - 1) (by omega) hx (by omega)
        exact stepA_congr' heq0 heq1 heq2 heq3 heq4
  · intro x y hxy
    by_cases hx0 : x = 0
    · subst hx0
      have hy0 : y = 0 := by omega
      subst hy0
      rw [A_origin_true (M + r + 1)]
      simp only [Combine, Int.natAbs_zero, add_zero, if_pos (by omega : 0 < M)]
      exact (Static_origin m hm).symm
    · rw [A_diag_false (M + r + 1) x y hx0 hxy]
      by_cases hin : x.natAbs + y.natAbs < M
      · simp only [Combine, if_pos hin]
        exact (Static_diag_false m hm x y hx0 hxy hin).symm
      · simp only [Combine, if_neg hin, if_pos hxy]

private lemma stepA_combine_top {m : ℕ} (hm : 2 ≤ m)
    (hM : ∀ x y : ℤ, A (2 * 2 ^ m) x y = Combine (2 ^ m) (Static m) (A (2 ^ m)) x y)
    (hM1 : ∀ x y : ℤ, A (2 ^ m + 1) x y = Combine (2 ^ m) (Static m) (A 1) x y)
    (hseamM : ∀ x y : ℤ, x.natAbs + y.natAbs = 2 ^ m → x ≠ 0 → y ≠ 0 → A (2 ^ m) x y = false)
    (htipM : A (2 ^ m) 0 ((2 ^ m : ℕ) - 1) = true) :
    ∀ x y : ℤ, A (2 ^ (m + 1) + 1) x y = Combine (2 ^ (m + 1)) (Static (m + 1)) (A 1) x y := by
  set M : ℕ := 2 ^ m
  have h2M : 2 ^ (m + 1) = 2 * M := by simp [M]; ring
  rw [h2M]
  have hM4 : 4 ≤ M := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
    simpa [M] using this
  have hMeven : M % 2 = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    have : 2 ^ (k + 2) = 2 * (2 ^ (k + 1)) := by ring
    omega
  have hStatic_succ : ∀ x y : ℤ, Static (m + 1) x y = Combine M (Static m) (Static m) x y := by
    intro x y
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    rfl
  have hseam : ∀ x y : ℤ, x.natAbs + y.natAbs = M → x ≠ 0 → y ≠ 0 → A (2 * M) x y = false := by
    intro x y hsum hx hy
    rw [hM x y]
    simp only [Combine]
    split_ifs with h1 h2 h3 h4 h5
    · omega
    · rfl
    · exact A_diag_false M (x - M) y (by omega) (by omega)
    · exact A_diag_false M (x + M) y (by omega) (by omega)
    · exact A_diag_false M x (y - M) (by omega) (by omega)
    · exact A_diag_false M x (y + M) (by omega) (by omega)
  have h_in : ∀ x y : ℤ, x.natAbs + y.natAbs < M → A (2 * M + 1) x y = Static m x y := by
    intro x y hlt
    change stepA (A (2 * M)) x y = Static m x y
    exact stepA_static_interior hm
      (fun u v huv => by rw [hM u v]; simp only [Combine, if_pos (show u.natAbs + v.natAbs < M from huv)])
      hseam x y hlt
  have hcsymm := Combine_symm (M := 2 * M) (Static_symm (m + 1)) (A_symm 1)
  apply stepA_symm_reduce (A_symm (2 * M + 1)) hcsymm
  · intro x y hx hlt
    by_cases hin : x.natAbs + y.natAbs < M
    · rw [h_in x y hin]
      simp only [Combine, if_pos (by omega : x.natAbs + y.natAbs < 2 * M), hStatic_succ, if_pos hin]
    · have hge : M ≤ x.natAbs + y.natAbs := by omega
      have hcorner : ∀ x y : ℤ, x = (M : ℤ) + 1 → y.natAbs = M →
          A (2 * M + 1) x y = Combine (2 * M) (Static (m + 1)) (A 1) x y := by
        intro x y hx1 hyM
        subst hx1
        rw [Combine_right_cone (by omega) (by omega) (by omega)]
        rw [A_support 1 ((M : ℤ) + 1 - (2 * M : ℕ)) y (by omega)]
        change stepA (A (2 * M)) ((M : ℤ) + 1) y = false
        have h0 : A (2 * M) ((M : ℤ) + 1) y = false := by
          rw [hM, Combine_right_cone (by omega) (by omega) (by omega)]
          exact A_support M ((M : ℤ) + 1 - M) y (by omega)
        have h1 : A (2 * M) ((M : ℤ) + 1 + 1) y = false := by
          rw [hM, Combine_right_cone (by omega) (by omega) (by omega)]
          exact A_support M ((M : ℤ) + 1 + 1 - M) y (by omega)
        have h2 : A (2 * M) M y = false := by
          rw [hM, Combine, if_neg (by omega), if_pos (by omega)]
        have h3 : A (2 * M) ((M : ℤ) + 1) (y + 1) = false := by
          rw [hM]
          rcases Int.natAbs_eq_iff.mp hyM with rfl | rfl
          · rw [Combine, if_neg (by omega), if_pos (by omega)]
          · rw [Combine_right_cone (by omega) (by omega) (by omega), show (M : ℤ) + 1 - M = 1 by ring]
            exact hseamM 1 (-(M : ℤ) + 1) (by omega) (by omega) (by omega)
        have h4 : A (2 * M) ((M : ℤ) + 1) (y - 1) = false := by
          rw [hM]
          rcases Int.natAbs_eq_iff.mp hyM with rfl | rfl
          · rw [Combine_right_cone (by omega) (by omega) (by omega), show (M : ℤ) + 1 - M = 1 by ring]
            exact hseamM 1 ((M : ℤ) - 1) (by omega) (by omega) (by omega)
          · rw [Combine, if_neg (by omega), if_pos (by omega)]
        simp only [stepA, add_sub_cancel_right, h0, h1, h2, h3, h4]; rfl
      have hcorner2 : ∀ x y : ℤ, x = M → y.natAbs = M - 1 →
          A (2 * M + 1) x y = Combine (2 * M) (Static (m + 1)) (A 1) x y := by
        intro x y hxM hyM1
        subst hxM
        have hrhs : Combine (2 * M) (Static (m + 1)) (A 1) M y = true := by
          simp only [Combine, if_pos (by omega : (M : ℤ).natAbs + y.natAbs < 2 * M), hStatic_succ]
          rw [if_neg (by omega : ¬ ((M : ℤ).natAbs + y.natAbs < M)),
            if_neg (by omega : ¬ ((M : ℤ).natAbs = y.natAbs)),
            if_pos (by omega : y.natAbs < (M : ℤ).natAbs),
            if_pos (by omega : (0 : ℤ) < M), show (M : ℤ) - M = 0 by ring]
          exact Static_odd m hm 0 y (by omega) (by omega)
        rw [hrhs]
        change stepA (A (2 * M)) M y = true
        have h0 : A (2 * M) M y = true := by
          rw [hM, Combine_right_cone (by omega) (by omega) (by omega), show (M : ℤ) - M = 0 by ring]
          rcases Int.natAbs_eq_iff.mp hyM1 with rfl | rfl
          · rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]; exact htipM
          · rw [(A_symm M).2.1, Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]; exact htipM
        have h1 : A (2 * M) ((M : ℤ) + 1) y = false := by
          rw [hM, Combine_right_cone (by omega) (by omega) (by omega), show (M : ℤ) + 1 - M = 1 by ring]
          exact hseamM 1 y (by omega) (by omega) (by omega)
        have h2 : A (2 * M) ((M : ℤ) - 1) y = false := by
          rw [hM]; simp only [Combine, if_neg (by omega : ¬ (((M : ℤ) - 1).natAbs + y.natAbs < M)),
            if_pos (by omega : ((M : ℤ) - 1).natAbs = y.natAbs)]
        rcases Int.natAbs_eq_iff.mp hyM1 with rfl | rfl
        · have h3 : A (2 * M) M (((M - 1 : ℕ) : ℤ) + 1) = false := by
            rw [hM]; simp only [Combine, if_neg (by omega : ¬ ((M : ℤ).natAbs + (((M - 1 : ℕ) : ℤ) + 1).natAbs < M)),
              if_pos (by omega : (M : ℤ).natAbs = (((M - 1 : ℕ) : ℤ) + 1).natAbs)]
          simp only [stepA, h0, h1, h2, h3, Bool.toNat_false, ↓reduceIte]
          cases A (2 * M) M (((M - 1 : ℕ) : ℤ) - 1) <;> decide
        · have h4 : A (2 * M) M (-((M - 1 : ℕ) : ℤ) - 1) = false := by
            rw [hM]; simp only [Combine, if_neg (by omega : ¬ ((M : ℤ).natAbs + (-((M - 1 : ℕ) : ℤ) - 1).natAbs < M)),
              if_pos (by omega : (M : ℤ).natAbs = (-((M - 1 : ℕ) : ℤ) - 1).natAbs)]
          simp only [stepA, h0, h1, h2, h4, Bool.toNat_false, ↓reduceIte]
          cases A (2 * M) M (-((M - 1 : ℕ) : ℤ) + 1) <;> decide
      by_cases hcor : x = (M : ℤ) + 1 ∧ y.natAbs = M
      · exact hcorner x y hcor.1 hcor.2
      · by_cases hcor2 : x = M ∧ y.natAbs = M - 1
        · exact hcorner2 x y hcor2.1 hcor2.2
        · have hstep_eq : A (2 * M + 1) x y = A (M + 1) (x - M) y := by
            by_cases hbd : x.natAbs + y.natAbs = M
            · by_cases hy : y = 0
              · subst hy
                have hxM : x = M := by omega
                subst hxM
                rw [show (M : ℤ) - M = 0 by ring, A_origin_true (M + 1)]
                change stepA (A (2 * M)) M 0 = true
                have h0 : A (2 * M) M 0 = true := by
                  rw [hM, Combine_right_cone (by omega) (by omega) (by omega),
                    show (M : ℤ) - M = 0 by ring, A_origin_true M]
                have hL : A (2 * M) ((M : ℤ) - 1) 0 = true := by
                  rw [hM]; simp only [Combine, Int.natAbs_zero, add_zero, if_pos (by omega : ((M : ℤ) - 1).natAbs < M)]
                  exact Static_odd m hm ((M : ℤ) - 1) 0 (by omega) (by omega)
                have hR : A (2 * M) ((M : ℤ) + 1) 0 = A M 1 0 := by
                  rw [hM, Combine_right_cone (by omega) (by omega) (by omega)]
                  congr 1; omega
                have hU : A (2 * M) M 1 = A M 1 0 := by
                  rw [hM, Combine_right_cone (by omega) (by omega) (by omega),
                    show (M : ℤ) - M = 0 by ring, (A_symm M).2.2]
                have hD : A (2 * M) M (-1) = A M 1 0 := by
                  rw [hM, Combine_right_cone (by omega) (by omega) (by omega),
                    show (M : ℤ) - M = 0 by ring, (A_symm M).2.1, (A_symm M).2.2]
                simp only [stepA, h0, hR, hL, hU, hD, zero_add, zero_sub, ↓reduceIte]
                cases A M 1 0 <;> decide
              · rw [A_diag_false (M + 1) (x - M) y (by omega) (by omega)]
                change stepA (A (2 * M)) x y = false
                have h0 : A (2 * M) x y = false := hseam x y hbd (by omega) hy
                have hL : A (2 * M) (x - 1) y = true := by
                  rw [hM]; simp only [Combine, if_pos (by omega : (x - 1).natAbs + y.natAbs < M)]
                  exact Static_odd m hm (x - 1) y (by omega) (by omega)
                by_cases hypos : 0 < y
                · have hD : A (2 * M) x (y - 1) = true := by
                    rw [hM]; simp only [Combine, if_pos (by omega : x.natAbs + (y - 1).natAbs < M)]
                    exact Static_odd m hm x (y - 1) (by omega) (by omega)
                  simp only [stepA, h0, hL, hD, Bool.false_eq_true, ↓reduceIte, Bool.toNat_true]
                  apply decide_eq_false; omega
                · have hU : A (2 * M) x (y + 1) = true := by
                    rw [hM]; simp only [Combine, if_pos (by omega : x.natAbs + (y + 1).natAbs < M)]
                    exact Static_odd m hm x (y + 1) (by omega) (by omega)
                  simp only [stepA, h0, hL, hU, Bool.false_eq_true, ↓reduceIte, Bool.toNat_true]
                  apply decide_eq_false; omega
            · have hgt : M < x.natAbs + y.natAbs := by omega
              change stepA (A (2 * M)) x y = stepA (A M) (x - M) y
              have hnbr : ∀ u v : ℤ, M ≤ u.natAbs + v.natAbs → 0 < u → v.natAbs ≤ u.natAbs →
                  (u ≠ M ∨ v.natAbs ≠ M) → A (2 * M) u v = A M (u - M) v := by
                intro u v hge' hu hle' hnotMM
                rw [hM u v]
                rcases lt_or_eq_of_le hle' with hlt' | heq'
                · exact Combine_right_cone hge' hu hlt'
                · simp only [Combine, if_neg (by omega : ¬ (u.natAbs + v.natAbs < M)), if_pos heq'.symm]
                  by_cases hltM : u.natAbs < M
                  · exact (hseamM (u - M) v (by omega) (by omega) (by omega)).symm
                  · exact (A_support M (u - M) v (by omega)).symm
              have heq0 : A (2 * M) x y = A M (x - M) y :=
                hnbr x y hge hx (by omega) (by omega)
              have heq1 : A (2 * M) (x + 1) y = A M (x - M + 1) y := by
                rw [show x - M + 1 = (x + 1) - M by ring]
                exact hnbr (x + 1) y (by omega) (by omega) (by omega) (by omega)
              have heq2 : A (2 * M) (x - 1) y = A M (x - M - 1) y := by
                rw [show x - M - 1 = (x - 1) - M by ring]
                exact hnbr (x - 1) y (by omega) (by omega) (by omega) (by omega)
              have heq3 : A (2 * M) x (y + 1) = A M (x - M) (y + 1) :=
                hnbr x (y + 1) (by omega) hx (by omega) (by omega)
              have heq4 : A (2 * M) x (y - 1) = A M (x - M) (y - 1) :=
                hnbr x (y - 1) (by omega) hx (by omega) (by omega)
              exact stepA_congr' heq0 heq1 heq2 heq3 heq4
          rw [hstep_eq, hM1 (x - M) y]
          by_cases h2lt : x.natAbs + y.natAbs < 2 * M
          · simp only [Combine, if_pos h2lt, hStatic_succ]
            rw [if_pos (by omega : (x - M).natAbs + y.natAbs < M)]
            rw [if_neg (by omega : ¬ (x.natAbs + y.natAbs < M)),
              if_neg (by omega : ¬ (x.natAbs = y.natAbs)),
              if_pos hlt, if_pos hx]
          · have h2ge : 2 * M ≤ x.natAbs + y.natAbs := by omega
            rw [Combine_right_cone h2ge hx hlt]
            simp only [Combine, if_neg (by omega : ¬ ((x - M).natAbs + y.natAbs < M))]
            split_ifs with hd hylt hxpos hypos
            · exact (A_support 1 (x - (2 * M : ℕ)) y (by omega)).symm
            · congr 1; omega
            · exfalso; omega
            · rw [A_support 1 (x - M) (y - M) (by omega), A_support 1 (x - (2 * M : ℕ)) y (by omega)]
            · rw [A_support 1 (x - M) (y + M) (by omega), A_support 1 (x - (2 * M : ℕ)) y (by omega)]
  · intro x y hxy
    by_cases hx0 : x = 0
    · subst hx0
      have hy0 : y = 0 := by omega
      subst hy0
      rw [A_origin_true (2 * M + 1)]
      simp only [Combine, Int.natAbs_zero, add_zero, if_pos (by omega : 0 < 2 * M)]
      exact (Static_origin (m + 1) (by omega)).symm
    · rw [A_diag_false (2 * M + 1) x y hx0 hxy]
      by_cases hin : x.natAbs + y.natAbs < 2 * M
      · simp only [Combine, if_pos hin]
        exact (Static_diag_false (m + 1) (by omega) x y hx0 hxy (by rw [h2M]; exact hin)).symm
      · simp only [Combine, if_neg hin, if_pos hxy]

private def A1_tab (x y : ℤ) : Bool :=
  let hi := max x.natAbs y.natAbs
  let lo := min x.natAbs y.natAbs
  decide ((hi = 0 ∧ lo = 0) ∨ (hi = 1 ∧ lo = 0))

private def A2_tab (x y : ℤ) : Bool :=
  let hi := max x.natAbs y.natAbs
  let lo := min x.natAbs y.natAbs
  decide ((hi = 0 ∧ lo = 0) ∨ (hi = 1 ∧ lo = 0) ∨ (hi = 2 ∧ lo = 0))

private def A3_tab (x y : ℤ) : Bool :=
  let hi := max x.natAbs y.natAbs
  let lo := min x.natAbs y.natAbs
  decide ((hi = 0 ∧ lo = 0) ∨ (hi = 2 ∧ lo = 0) ∨ (hi = 2 ∧ lo = 1) ∨ (hi = 3 ∧ lo = 0))

private def A4_tab (x y : ℤ) : Bool :=
  let hi := max x.natAbs y.natAbs
  let lo := min x.natAbs y.natAbs
  decide ((hi = 0 ∧ lo = 0) ∨ (hi = 2 ∧ lo = 1) ∨ (hi = 3 ∧ lo = 0) ∨ (hi = 4 ∧ lo = 0))

private def A5_tab (x y : ℤ) : Bool :=
  let hi := max x.natAbs y.natAbs
  let lo := min x.natAbs y.natAbs
  decide ((hi = 0 ∧ lo = 0) ∨ (hi = 1 ∧ lo = 0) ∨ (hi = 2 ∧ lo = 1) ∨
    (hi = 3 ∧ lo = 0) ∨ (hi = 4 ∧ lo = 0) ∨ (hi = 4 ∧ lo = 1) ∨ (hi = 5 ∧ lo = 0))

private lemma A1_eq_tab : ∀ x y : ℤ, A 1 x y = A1_tab x y := by
  intro x y
  by_cases h : x.natAbs + y.natAbs ≤ 1
  · have hb : ∀ u ∈ Finset.Icc (-1 : ℤ) 1, ∀ v ∈ Finset.Icc (-1 : ℤ) 1, A 1 u v = A1_tab u v := by decide
    exact hb x (Finset.mem_Icc.mpr (by omega)) y (Finset.mem_Icc.mpr (by omega))
  · rw [A_support 1 x y (by omega)]
    simp only [A1_tab]; apply Eq.symm; apply decide_eq_false; omega

private lemma A2_eq_tab : ∀ x y : ℤ, A 2 x y = A2_tab x y := by
  intro x y
  change stepA (A 1) x y = A2_tab x y
  rw [show A 1 = A1_tab by funext u v; exact A1_eq_tab u v]
  by_cases h : x.natAbs + y.natAbs ≤ 2
  · have hb : ∀ u ∈ Finset.Icc (-2 : ℤ) 2, ∀ v ∈ Finset.Icc (-2 : ℤ) 2, stepA A1_tab u v = A2_tab u v := by decide
    exact hb x (Finset.mem_Icc.mpr (by omega)) y (Finset.mem_Icc.mpr (by omega))
  · have h0 : A1_tab x y = false := by simp only [A1_tab]; apply decide_eq_false; omega
    have h1 : A1_tab (x + 1) y = false := by simp only [A1_tab]; apply decide_eq_false; omega
    have h2 : A1_tab (x - 1) y = false := by simp only [A1_tab]; apply decide_eq_false; omega
    have h3 : A1_tab x (y + 1) = false := by simp only [A1_tab]; apply decide_eq_false; omega
    have h4 : A1_tab x (y - 1) = false := by simp only [A1_tab]; apply decide_eq_false; omega
    simp only [stepA, h0, h1, h2, h3, h4, A2_tab]
    apply Eq.symm; apply decide_eq_false; omega

private lemma A3_eq_tab : ∀ x y : ℤ, A 3 x y = A3_tab x y := by
  intro x y
  change stepA (A 2) x y = A3_tab x y
  rw [show A 2 = A2_tab by funext u v; exact A2_eq_tab u v]
  by_cases h : x.natAbs + y.natAbs ≤ 3
  · have hb : ∀ u ∈ Finset.Icc (-3 : ℤ) 3, ∀ v ∈ Finset.Icc (-3 : ℤ) 3, stepA A2_tab u v = A3_tab u v := by decide
    exact hb x (Finset.mem_Icc.mpr (by omega)) y (Finset.mem_Icc.mpr (by omega))
  · have h0 : A2_tab x y = false := by simp only [A2_tab]; apply decide_eq_false; omega
    have h1 : A2_tab (x + 1) y = false := by simp only [A2_tab]; apply decide_eq_false; omega
    have h2 : A2_tab (x - 1) y = false := by simp only [A2_tab]; apply decide_eq_false; omega
    have h3 : A2_tab x (y + 1) = false := by simp only [A2_tab]; apply decide_eq_false; omega
    have h4 : A2_tab x (y - 1) = false := by simp only [A2_tab]; apply decide_eq_false; omega
    simp only [stepA, h0, h1, h2, h3, h4, A3_tab]
    apply Eq.symm; apply decide_eq_false; omega

private lemma A4_eq_tab : ∀ x y : ℤ, A 4 x y = A4_tab x y := by
  intro x y
  change stepA (A 3) x y = A4_tab x y
  rw [show A 3 = A3_tab by funext u v; exact A3_eq_tab u v]
  by_cases h : x.natAbs + y.natAbs ≤ 4
  · have hb : ∀ u ∈ Finset.Icc (-4 : ℤ) 4, ∀ v ∈ Finset.Icc (-4 : ℤ) 4, stepA A3_tab u v = A4_tab u v := by decide
    exact hb x (Finset.mem_Icc.mpr (by omega)) y (Finset.mem_Icc.mpr (by omega))
  · have h0 : A3_tab x y = false := by simp only [A3_tab]; apply decide_eq_false; omega
    have h1 : A3_tab (x + 1) y = false := by simp only [A3_tab]; apply decide_eq_false; omega
    have h2 : A3_tab (x - 1) y = false := by simp only [A3_tab]; apply decide_eq_false; omega
    have h3 : A3_tab x (y + 1) = false := by simp only [A3_tab]; apply decide_eq_false; omega
    have h4 : A3_tab x (y - 1) = false := by simp only [A3_tab]; apply decide_eq_false; omega
    simp only [stepA, h0, h1, h2, h3, h4, A4_tab]
    apply Eq.symm; apply decide_eq_false; omega

private lemma A5_eq_tab : ∀ x y : ℤ, A 5 x y = A5_tab x y := by
  intro x y
  change stepA (A 4) x y = A5_tab x y
  rw [show A 4 = A4_tab by funext u v; exact A4_eq_tab u v]
  by_cases h : x.natAbs + y.natAbs ≤ 5
  · have hb : ∀ u ∈ Finset.Icc (-5 : ℤ) 5, ∀ v ∈ Finset.Icc (-5 : ℤ) 5, stepA A4_tab u v = A5_tab u v := by decide
    exact hb x (Finset.mem_Icc.mpr (by omega)) y (Finset.mem_Icc.mpr (by omega))
  · have h0 : A4_tab x y = false := by simp only [A4_tab]; apply decide_eq_false; omega
    have h1 : A4_tab (x + 1) y = false := by simp only [A4_tab]; apply decide_eq_false; omega
    have h2 : A4_tab (x - 1) y = false := by simp only [A4_tab]; apply decide_eq_false; omega
    have h3 : A4_tab x (y + 1) = false := by simp only [A4_tab]; apply decide_eq_false; omega
    have h4 : A4_tab x (y - 1) = false := by simp only [A4_tab]; apply decide_eq_false; omega
    simp only [stepA, h0, h1, h2, h3, h4, A5_tab]
    apply Eq.symm; apply decide_eq_false; omega

private lemma A_five : ∀ x y : ℤ, A 5 x y = Combine 4 (Static 2) (A 1) x y := by
  intro x y
  rw [A5_eq_tab x y, show A 1 = A1_tab by funext u v; exact A1_eq_tab u v]
  by_cases h : x.natAbs + y.natAbs ≤ 5
  · have hb : ∀ u ∈ Finset.Icc (-5 : ℤ) 5, ∀ v ∈ Finset.Icc (-5 : ℤ) 5,
        A5_tab u v = Combine 4 (Static 2) A1_tab u v := by decide
    exact hb x (Finset.mem_Icc.mpr (by omega)) y (Finset.mem_Icc.mpr (by omega))
  · have hL : A5_tab x y = false := by simp only [A5_tab]; apply decide_eq_false; omega
    rw [hL]
    simp only [Combine]
    split_ifs with h1 h2 h3 h4 h5
    · omega
    · rfl
    · simp only [A1_tab]; apply Eq.symm; apply decide_eq_false; omega
    · simp only [A1_tab]; apply Eq.symm; apply decide_eq_false; omega
    · simp only [A1_tab]; apply Eq.symm; apply decide_eq_false; omega
    · simp only [A1_tab]; apply Eq.symm; apply decide_eq_false; omega

private lemma A_doubling (m : ℕ) (hm : 2 ≤ m) :
    (∀ r : ℕ, 1 ≤ r → r ≤ 2 ^ m → ∀ x y : ℤ,
      A (2 ^ m + r) x y = Combine (2 ^ m) (Static m) (A r) x y) ∧
    (∀ x y : ℤ, x.natAbs + y.natAbs = 2 ^ m → x ≠ 0 → y ≠ 0 → A (2 ^ m) x y = false) ∧
    A (2 ^ m) 0 ((2 ^ m : ℕ) - 1) = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero =>
        refine ⟨?_, ?_, ?_⟩
        · intro r hr1 hrm
          have hstep : ∀ k : ℕ, k ≤ 3 → ∀ x y : ℤ,
              A (4 + (k + 1)) x y = Combine 4 (Static 2) (A (k + 1)) x y := by
            intro k
            induction k with
            | zero => intro _; exact A_five
            | succ k ihk =>
              intro hk
              exact stepA_combine (m := 2) (r := k + 1) (by omega) (by omega) (by omega) (ihk (by omega))
          have hreq : r = (r - 1) + 1 := by omega
          rw [hreq]
          exact hstep (r - 1) (by omega)
        · intro x y hsum hx hy
          rw [show 2 ^ (0 + 1 + 1) = 4 by rfl, A4_eq_tab x y]
          simp only [A4_tab]; apply decide_eq_false; omega
        · rw [show 2 ^ (0 + 1 + 1) = 4 by rfl, A4_eq_tab]; decide
      | succ k =>
        obtain ⟨ih_comb, ih_seam, ih_tip⟩ := ih (by omega)
        have hM4 : 4 ≤ 2 ^ (k + 2) := by
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 2 ≤ k + 2 by omega); simpa using this
        have h2p : 2 ^ (k + 1 + 1 + 1) = 2 * 2 ^ (k + 2) := by ring
        have hM_eq : ∀ x y : ℤ, A (2 * 2 ^ (k + 2)) x y =
            Combine (2 ^ (k + 2)) (Static (k + 2)) (A (2 ^ (k + 2))) x y := by
          rw [show 2 * 2 ^ (k + 2) = 2 ^ (k + 2) + 2 ^ (k + 2) by ring]
          exact ih_comb (2 ^ (k + 2)) (by omega) le_rfl
        have hM1_eq : ∀ x y : ℤ, A (2 ^ (k + 2) + 1) x y =
            Combine (2 ^ (k + 2)) (Static (k + 2)) (A 1) x y :=
          ih_comb 1 le_rfl (by omega)
        have hbase1 : ∀ x y : ℤ, A (2 ^ (k + 3) + 1) x y =
            Combine (2 ^ (k + 3)) (Static (k + 3)) (A 1) x y :=
          stepA_combine_top (m := k + 2) (by omega) hM_eq hM1_eq ih_seam ih_tip
        refine ⟨?_, ?_, ?_⟩
        · intro r hr1 hrm
          have hstep : ∀ j : ℕ, j < 2 ^ (k + 3) → ∀ x y : ℤ,
              A (2 ^ (k + 3) + (j + 1)) x y = Combine (2 ^ (k + 3)) (Static (k + 3)) (A (j + 1)) x y := by
            intro j
            induction j with
            | zero => intro _; exact hbase1
            | succ j ihj =>
              intro hj
              exact stepA_combine (m := k + 3) (r := j + 1) (by omega) (by omega) (by omega) (ihj (by omega))
          have hreq : r = (r - 1) + 1 := by omega
          have h2p' : 2 ^ (k + 3) = 2 * 2 ^ (k + 2) := by ring
          rw [h2p] at hrm
          rw [hreq]
          exact hstep (r - 1) (by omega)
        · intro x y hsum hx hy
          rw [h2p] at hsum ⊢
          rw [hM_eq x y]
          simp only [Combine]
          by_cases h1 : x.natAbs + y.natAbs < 2 ^ (k + 2)
          · omega
          · rw [if_neg h1]
            by_cases h2 : x.natAbs = y.natAbs
            · rw [if_pos h2]
            · rw [if_neg h2]
              by_cases h3 : y.natAbs < x.natAbs
              · rw [if_pos h3]
                by_cases h4 : 0 < x
                · rw [if_pos h4]
                  exact ih_seam (x - (2 ^ (k + 2) : ℕ)) y (by omega) (by omega) hy
                · rw [if_neg h4]
                  exact ih_seam (x + (2 ^ (k + 2) : ℕ)) y (by omega) (by omega) hy
              · rw [if_neg h3]
                by_cases h5 : 0 < y
                · rw [if_pos h5]
                  exact ih_seam x (y - (2 ^ (k + 2) : ℕ)) (by omega) hx (by omega)
                · rw [if_neg h5]
                  exact ih_seam x (y + (2 ^ (k + 2) : ℕ)) (by omega) hx (by omega)
        · rw [h2p, hM_eq 0 ((2 * 2 ^ (k + 2) : ℕ) - 1)]
          simp only [Combine, Int.natAbs_zero, zero_add]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          have hsub : ((2 * 2 ^ (k + 2) : ℕ) : ℤ) - 1 - (2 ^ (k + 2) : ℕ) = (2 ^ (k + 2) : ℕ) - 1 := by
            push_cast; ring
          rw [hsub]
          exact ih_tip

/-! ### Part 5: Unified `lift` counting (`Score`) and `Score_Combine` -/

private def lift (g : ℤ → ℤ → Bool) (i j : ℤ) : Bool :=
  if i % 2 = 0 ∧ j % 2 = 0 then g (i / 2) (j / 2)
  else if i % 2 = 1 ∧ j % 2 = 0 then xor (g ((i - 1) / 2) (j / 2)) (g ((i + 1) / 2) (j / 2))
  else if i % 2 = 0 ∧ j % 2 = 1 then xor (g (i / 2) ((j - 1) / 2)) (g (i / 2) ((j + 1) / 2))
  else false

private noncomputable def Score (g : ℤ → ℤ → Bool) (M : ℕ) : ℕ :=
  ∑ p ∈ Finset.Icc (-(2 * (M : ℤ) - 1)) (2 * (M : ℤ) - 1) ×ˢ
        Finset.Icc (-(2 * (M : ℤ) - 1)) (2 * (M : ℤ) - 1),
    (lift g p.1 p.2).toNat

private def StaticTrunc (m : ℕ) (x y : ℤ) : Bool :=
  if x.natAbs + y.natAbs < 2 ^ m then Static m x y else false

private lemma StaticTrunc_succ {m : ℕ} (hm : 2 ≤ m) (x y : ℤ) :
    StaticTrunc (m + 1) x y = Combine (2 ^ m) (StaticTrunc m) (StaticTrunc m) x y := by
  have hStatic_succ : Static (m + 1) x y = Combine (2 ^ m) (Static m) (Static m) x y := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm; rfl
  have h2p : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  simp only [StaticTrunc, Combine, hStatic_succ, h2p]
  split_ifs <;> first | rfl | omega

private lemma A_pow_sub_one_eq_Combine {m : ℕ} (hm : 2 ≤ m) (x y : ℤ) :
    A (2 ^ (m + 1) - 1) x y = Combine (2 ^ m) (StaticTrunc m) (A (2 ^ m - 1)) x y := by
  have hMpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hpow : 2 ^ (m + 1) - 1 = 2 ^ m + (2 ^ m - 1) := by
    have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    omega
  have hM4 : 4 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm; simpa using this
  rw [hpow, (A_doubling m hm).1 (2 ^ m - 1) (by omega) (by omega) x y]
  simp only [Combine, StaticTrunc]
  split_ifs with h1 <;> rfl

private lemma lift_support {M : ℕ} {g : ℤ → ℤ → Bool}
    (hsupp : ∀ x y : ℤ, M ≤ x.natAbs + y.natAbs → g x y = false)
    {i j : ℤ} (hge : 2 * M ≤ i.natAbs + j.natAbs) :
    lift g i j = false := by
  simp only [lift]
  split_ifs with h1 h2 h3
  · exact hsupp (i / 2) (j / 2) (by omega)
  · rw [hsupp ((i - 1) / 2) (j / 2) (by omega), hsupp ((i + 1) / 2) (j / 2) (by omega)]; rfl
  · rw [hsupp (i / 2) ((j - 1) / 2) (by omega), hsupp (i / 2) ((j + 1) / 2) (by omega)]; rfl
  · rfl

private lemma lift_symm {g : ℤ → ℤ → Bool}
    (hsymm : (∀ x y : ℤ, g (-x) y = g x y) ∧
             (∀ x y : ℤ, g x (-y) = g x y) ∧
             (∀ x y : ℤ, g y x = g x y)) :
    (∀ i j : ℤ, lift g (-i) j = lift g i j) ∧
    (∀ i j : ℤ, lift g i (-j) = lift g i j) ∧
    (∀ i j : ℤ, lift g j i = lift g i j) := by
  obtain ⟨hx, hy, hs⟩ := hsymm
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [lift]
    have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hi with hi0 | hi1 <;> rcases hj with hj0 | hj1
    · simp only [show (-i) % 2 = 0 by omega, hi0, hj0, and_self, ↓reduceIte]
      rw [show (-i) / 2 = -(i / 2) by omega, hx]
    · simp only [show (-i) % 2 = 0 by omega, hi0, hj1, show (1 : ℤ) ≠ 0 by omega,
        show (0 : ℤ) ≠ 1 by omega, and_self, and_false, false_and, ↓reduceIte]
      rw [show (-i) / 2 = -(i / 2) by omega, hx, hx]
    · simp only [show (-i) % 2 = 1 by omega, hi1, hj0, show (1 : ℤ) ≠ 0 by omega,
        show (0 : ℤ) ≠ 1 by omega, and_self, and_false, false_and, ↓reduceIte]
      rw [show (-i - 1) / 2 = -((i + 1) / 2) by omega, show (-i + 1) / 2 = -((i - 1) / 2) by omega,
        hx, hx, Bool.xor_comm]
    · simp only [show (-i) % 2 = 1 by omega, hi1, hj1, show (1 : ℤ) ≠ 0 by omega,
        and_false, false_and, ↓reduceIte]
  · intro i j
    simp only [lift]
    have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hi with hi0 | hi1 <;> rcases hj with hj0 | hj1
    · simp only [hi0, show (-j) % 2 = 0 by omega, hj0, and_self, ↓reduceIte]
      rw [show (-j) / 2 = -(j / 2) by omega, hy]
    · simp only [hi0, show (-j) % 2 = 1 by omega, hj1, show (1 : ℤ) ≠ 0 by omega,
        show (0 : ℤ) ≠ 1 by omega, and_self, and_false, false_and, ↓reduceIte]
      rw [show (-j - 1) / 2 = -((j + 1) / 2) by omega, show (-j + 1) / 2 = -((j - 1) / 2) by omega,
        hy, hy, Bool.xor_comm]
    · simp only [hi1, show (-j) % 2 = 0 by omega, hj0, show (1 : ℤ) ≠ 0 by omega,
        show (0 : ℤ) ≠ 1 by omega, and_self, and_false, false_and, ↓reduceIte]
      rw [show (-j) / 2 = -(j / 2) by omega, hy, hy]
    · simp only [hi1, show (-j) % 2 = 1 by omega, hj1, show (1 : ℤ) ≠ 0 by omega,
        and_false, false_and, ↓reduceIte]
  · intro i j
    simp only [lift]
    have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hi with hi0 | hi1 <;> rcases hj with hj0 | hj1
    · simp only [hi0, hj0, and_self, ↓reduceIte]; exact hs _ _
    · simp only [hi0, hj1, show (1 : ℤ) ≠ 0 by omega, show (0 : ℤ) ≠ 1 by omega,
        and_self, and_false, false_and, ↓reduceIte]
      rw [hs (i / 2) ((j - 1) / 2), hs (i / 2) ((j + 1) / 2)]
    · simp only [hi1, hj0, show (1 : ℤ) ≠ 0 by omega, show (0 : ℤ) ≠ 1 by omega,
        and_self, and_false, false_and, ↓reduceIte]
      rw [hs ((i - 1) / 2) (j / 2), hs ((i + 1) / 2) (j / 2)]
    · simp only [hi1, hj1, show (1 : ℤ) ≠ 0 by omega, and_false, false_and, ↓reduceIte]

private lemma lift_diag_false {g : ℤ → ℤ → Bool}
    (hdiag : ∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → g x y = false)
    {i j : ℤ} (hi : i ≠ 0) (hij : i.natAbs = j.natAbs) :
    lift g i j = false := by
  simp only [lift]
  split_ifs with h1 h2 h3
  · exact hdiag (i / 2) (j / 2) (by omega) (by omega)
  · omega
  · omega
  · rfl

private lemma lift_Combine_in {M : ℕ} (hM : 4 ≤ M) {g_in g_out : ℤ → ℤ → Bool}
    (hin_supp : ∀ x y : ℤ, M ≤ x.natAbs + y.natAbs → g_in x y = false)
    (hin_bdy : ∀ x y : ℤ, x.natAbs + y.natAbs = M - 1 → g_in x y = true)
    (hout_0 : g_out 0 0 = true)
    (hout_diag : ∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → g_out x y = false)
    {i j : ℤ} (hlt : i.natAbs + j.natAbs < 2 * M) :
    lift (Combine M g_in g_out) i j =
      if (i = 2 * (M : ℤ) - 1 ∧ j = 0) ∨ (i = -(2 * (M : ℤ) - 1) ∧ j = 0) ∨
         (i = 0 ∧ j = 2 * (M : ℤ) - 1) ∨ (i = 0 ∧ j = -(2 * (M : ℤ) - 1))
      then false else lift g_in i j := by
  have hcomb_eq : ∀ u v : ℤ, u.natAbs + v.natAbs ≤ M →
      (u = M ∧ v = 0 → Combine M g_in g_out u v = true) ∧
      (u = -(M : ℤ) ∧ v = 0 → Combine M g_in g_out u v = true) ∧
      (u = 0 ∧ v = M → Combine M g_in g_out u v = true) ∧
      (u = 0 ∧ v = -(M : ℤ) → Combine M g_in g_out u v = true) ∧
      (¬ ((u = M ∧ v = 0) ∨ (u = -(M : ℤ) ∧ v = 0) ∨ (u = 0 ∧ v = M) ∨ (u = 0 ∧ v = -(M : ℤ))) →
        Combine M g_in g_out u v = g_in u v) := by
    intro u v hle
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨rfl, rfl⟩
      rw [Combine_right_cone (by omega) (by omega) (by omega), show (M : ℤ) - M = 0 by ring, hout_0]
    · rintro ⟨rfl, rfl⟩
      simp only [Combine, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_zero, add_zero]
      split_ifs <;> try omega
      rw [show -(M : ℤ) + M = 0 by ring, hout_0]
    · rintro ⟨rfl, rfl⟩
      simp only [Combine, Int.natAbs_natCast, Int.natAbs_zero, zero_add]
      split_ifs <;> try omega
      rw [show (M : ℤ) - M = 0 by ring, hout_0]
    · rintro ⟨rfl, rfl⟩
      simp only [Combine, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_zero, zero_add]
      split_ifs <;> try omega
      rw [show -(M : ℤ) + M = 0 by ring, hout_0]
    · intro hnot
      by_cases hlt' : u.natAbs + v.natAbs < M
      · simp [Combine, hlt']
      · rw [hin_supp u v (by omega)]
        simp only [Combine, if_neg hlt']
        split_ifs with h2 h3 h4 h5
        · rfl
        · exact hout_diag (u - M) v (by omega) (by omega)
        · exact hout_diag (u + M) v (by omega) (by omega)
        · exact hout_diag u (v - M) (by omega) (by omega)
        · exact hout_diag u (v + M) (by omega) (by omega)
  split_ifs with htip
  · rcases htip with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [lift, show (2 * (M : ℤ) - 1) % 2 = 1 by omega, show (0 : ℤ) % 2 = 0 by omega,
        show (1 : ℤ) ≠ 0 by omega, and_self, false_and, ↓reduceIte]
      have h1 : (2 * (M : ℤ) - 1 - 1) / 2 = (M : ℤ) - 1 := by omega
      have h2 : (2 * (M : ℤ) - 1 + 1) / 2 = M := by omega
      rw [h1, h2, show (0 : ℤ) / 2 = 0 by omega]
      rw [(hcomb_eq ((M : ℤ) - 1) 0 (by omega)).2.2.2.2 (by omega), hin_bdy ((M : ℤ) - 1) 0 (by omega),
        (hcomb_eq M 0 (by omega)).1 ⟨rfl, rfl⟩]; rfl
    · simp only [lift, show (-(2 * (M : ℤ) - 1)) % 2 = 1 by omega, show (0 : ℤ) % 2 = 0 by omega,
        show (1 : ℤ) ≠ 0 by omega, and_self, false_and, ↓reduceIte]
      have h1 : (-(2 * (M : ℤ) - 1) - 1) / 2 = -(M : ℤ) := by omega
      have h2 : (-(2 * (M : ℤ) - 1) + 1) / 2 = -((M : ℤ) - 1) := by omega
      rw [h1, h2, show (0 : ℤ) / 2 = 0 by omega]
      rw [(hcomb_eq (-(M : ℤ)) 0 (by omega)).2.1 ⟨rfl, rfl⟩,
        (hcomb_eq (-((M : ℤ) - 1)) 0 (by omega)).2.2.2.2 (by omega),
        hin_bdy (-((M : ℤ) - 1)) 0 (by omega)]; rfl
    · simp only [lift, show (0 : ℤ) % 2 = 0 by omega, show (2 * (M : ℤ) - 1) % 2 = 1 by omega,
        show (1 : ℤ) ≠ 0 by omega, show (0 : ℤ) ≠ 1 by omega, and_self, and_false, false_and, ↓reduceIte]
      have h1 : (2 * (M : ℤ) - 1 - 1) / 2 = (M : ℤ) - 1 := by omega
      have h2 : (2 * (M : ℤ) - 1 + 1) / 2 = M := by omega
      rw [h1, h2, show (0 : ℤ) / 2 = 0 by omega]
      rw [(hcomb_eq 0 ((M : ℤ) - 1) (by omega)).2.2.2.2 (by omega), hin_bdy 0 ((M : ℤ) - 1) (by omega),
        (hcomb_eq 0 M (by omega)).2.2.1 ⟨rfl, rfl⟩]; rfl
    · simp only [lift, show (0 : ℤ) % 2 = 0 by omega, show (-(2 * (M : ℤ) - 1)) % 2 = 1 by omega,
        show (1 : ℤ) ≠ 0 by omega, show (0 : ℤ) ≠ 1 by omega, and_self, and_false, false_and, ↓reduceIte]
      have h1 : (-(2 * (M : ℤ) - 1) - 1) / 2 = -(M : ℤ) := by omega
      have h2 : (-(2 * (M : ℤ) - 1) + 1) / 2 = -((M : ℤ) - 1) := by omega
      rw [h1, h2, show (0 : ℤ) / 2 = 0 by omega]
      rw [(hcomb_eq 0 (-(M : ℤ)) (by omega)).2.2.2.1 ⟨rfl, rfl⟩,
        (hcomb_eq 0 (-((M : ℤ) - 1)) (by omega)).2.2.2.2 (by omega),
        hin_bdy 0 (-((M : ℤ) - 1)) (by omega)]; rfl
  · simp only [lift]
    have hnot_tip : ∀ u v : ℤ, u.natAbs + v.natAbs ≤ M →
        (u.natAbs + v.natAbs < M ∨ (u ≠ 0 ∧ v ≠ 0)) →
        Combine M g_in g_out u v = g_in u v := by
      intro u v hle hor
      exact (hcomb_eq u v hle).2.2.2.2 (by
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · rcases hor with h1 | ⟨_, hv⟩
          · simp only [Int.natAbs_natCast, Int.natAbs_zero, add_zero] at h1; omega
          · exact hv rfl
        · rcases hor with h1 | ⟨_, hv⟩
          · simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_zero, add_zero] at h1; omega
          · exact hv rfl
        · rcases hor with h1 | ⟨hu, _⟩
          · simp only [Int.natAbs_natCast, Int.natAbs_zero, zero_add] at h1; omega
          · exact hu rfl
        · rcases hor with h1 | ⟨hu, _⟩
          · simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_zero, zero_add] at h1; omega
          · exact hu rfl)
    split_ifs with h1 h2 h3
    · exact hnot_tip (i / 2) (j / 2) (by omega) (Or.inl (by omega))
    · set u := (i - 1) / 2
      set v := j / 2
      have hi_eq : i = 2 * u + 1 := by omega
      have hj_eq : j = 2 * v := by omega
      have hi_plus : (i + 1) / 2 = u + 1 := by omega
      rw [hi_plus]
      have hlt' : (2 * u + 1).natAbs + (2 * v).natAbs < 2 * M := by rw [← hi_eq, ← hj_eq]; exact hlt
      have hle1 : u.natAbs + v.natAbs ≤ M := by omega
      have hle2 : (u + 1).natAbs + v.natAbs ≤ M := by omega
      have hor1 : u.natAbs + v.natAbs < M ∨ (u ≠ 0 ∧ v ≠ 0) := by
        by_cases hv : v = 0
        · left
          have h1' : ¬ (2 * u + 1 = 2 * (M : ℤ) - 1) := fun h => htip (Or.inl ⟨by omega, by omega⟩)
          have h2' : ¬ (2 * u + 1 = -(2 * (M : ℤ) - 1)) := fun h => htip (Or.inr (Or.inl ⟨by omega, by omega⟩))
          omega
        · by_cases hu : u = 0
          · left; rw [hu, Int.natAbs_zero, zero_add]; omega
          · exact Or.inr ⟨hu, hv⟩
      have hor2 : (u + 1).natAbs + v.natAbs < M ∨ (u + 1 ≠ 0 ∧ v ≠ 0) := by
        by_cases hv : v = 0
        · left
          have h1' : ¬ (2 * u + 1 = 2 * (M : ℤ) - 1) := fun h => htip (Or.inl ⟨by omega, by omega⟩)
          have h2' : ¬ (2 * u + 1 = -(2 * (M : ℤ) - 1)) := fun h => htip (Or.inr (Or.inl ⟨by omega, by omega⟩))
          omega
        · by_cases hu : u + 1 = 0
          · left; rw [hu, Int.natAbs_zero, zero_add]; omega
          · exact Or.inr ⟨hu, hv⟩
      rw [hnot_tip u v hle1 hor1, hnot_tip (u + 1) v hle2 hor2]
    · set u := i / 2
      set v := (j - 1) / 2
      have hi_eq : i = 2 * u := by omega
      have hj_eq : j = 2 * v + 1 := by omega
      have hj_plus : (j + 1) / 2 = v + 1 := by omega
      rw [hj_plus]
      have hlt' : (2 * u).natAbs + (2 * v + 1).natAbs < 2 * M := by rw [← hi_eq, ← hj_eq]; exact hlt
      have hle1 : u.natAbs + v.natAbs ≤ M := by omega
      have hle2 : u.natAbs + (v + 1).natAbs ≤ M := by omega
      have hor1 : u.natAbs + v.natAbs < M ∨ (u ≠ 0 ∧ v ≠ 0) := by
        by_cases hu : u = 0
        · left
          have h1' : ¬ (2 * v + 1 = 2 * (M : ℤ) - 1) := fun h => htip (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
          have h2' : ¬ (2 * v + 1 = -(2 * (M : ℤ) - 1)) := fun h => htip (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
          omega
        · by_cases hv : v = 0
          · left; rw [hv, Int.natAbs_zero, add_zero]; omega
          · exact Or.inr ⟨hu, hv⟩
      have hor2 : u.natAbs + (v + 1).natAbs < M ∨ (u ≠ 0 ∧ v + 1 ≠ 0) := by
        by_cases hu : u = 0
        · left
          have h1' : ¬ (2 * v + 1 = 2 * (M : ℤ) - 1) := fun h => htip (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
          have h2' : ¬ (2 * v + 1 = -(2 * (M : ℤ) - 1)) := fun h => htip (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
          omega
        · by_cases hv : v + 1 = 0
          · left; rw [hv, Int.natAbs_zero, add_zero]; omega
          · exact Or.inr ⟨hu, hv⟩
      rw [hnot_tip u v hle1 hor1, hnot_tip u (v + 1) hle2 hor2]
    · rfl

private lemma lift_Combine_right_cone {M : ℕ} (hM : 4 ≤ M) {g_in g_out : ℤ → ℤ → Bool}
    (hout_supp : ∀ x y : ℤ, M ≤ x.natAbs + y.natAbs → g_out x y = false)
    (hout_diag : ∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → g_out x y = false)
    {i j : ℤ} (hge : 2 * M ≤ i.natAbs + j.natAbs) (hi : 0 < i) (hlt : j.natAbs < i.natAbs) :
    lift (Combine M g_in g_out) i j = lift g_out (i - 2 * M) j := by
  have hpt' : ∀ u v : ℤ, M ≤ u.natAbs + v.natAbs → 0 < u → v.natAbs ≤ u.natAbs →
      Combine M g_in g_out u v = g_out (u - M) v := by
    intro u v hge' hu hle'
    rcases lt_or_eq_of_le hle' with hlt' | heq'
    · exact Combine_right_cone hge' hu hlt'
    · simp only [Combine, if_neg (by omega : ¬ (u.natAbs + v.natAbs < M)), if_pos heq'.symm]
      by_cases hsmall : 2 * u.natAbs = M
      · exact (hout_diag (u - M) v (by omega) (by omega)).symm
      · exact (hout_supp (u - M) v (by omega)).symm
  simp only [lift]
  have hmod : (i - 2 * (M : ℤ)) % 2 = i % 2 := by omega
  rw [hmod]
  split_ifs with h1 h2 h3
  · rw [show (i - 2 * (M : ℤ)) / 2 = i / 2 - M by omega]
    exact hpt' (i / 2) (j / 2) (by omega) (by omega) (by omega)
  · rw [show (i - 2 * (M : ℤ) - 1) / 2 = (i - 1) / 2 - M by omega,
      show (i - 2 * (M : ℤ) + 1) / 2 = (i + 1) / 2 - M by omega]
    rw [hpt' ((i - 1) / 2) (j / 2) (by omega) (by omega) (by omega),
      hpt' ((i + 1) / 2) (j / 2) (by omega) (by omega) (by omega)]
  · rw [show (i - 2 * (M : ℤ)) / 2 = i / 2 - M by omega]
    rw [hpt' (i / 2) ((j - 1) / 2) (by omega) (by omega) (by omega),
      hpt' (i / 2) ((j + 1) / 2) (by omega) (by omega) (by omega)]
  · rfl

private lemma Score_quadrant_decomp {M : ℕ} (hM : 4 ≤ M) {g : ℤ → ℤ → Bool}
    (hsupp : ∀ x y : ℤ, M ≤ x.natAbs + y.natAbs → g x y = false)
    (hsymm : (∀ x y : ℤ, g (-x) y = g x y) ∧
             (∀ x y : ℤ, g x (-y) = g x y) ∧
             (∀ x y : ℤ, g y x = g x y))
    (h0 : g 0 0 = true)
    (hdiag : ∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → g x y = false) :
    let S := Finset.Icc (-(2 * (M : ℤ) - 1)) (2 * (M : ℤ) - 1) ×ˢ
             Finset.Icc (-(2 * (M : ℤ) - 1)) (2 * (M : ℤ) - 1)
    let Q := ∑ p ∈ S.filter (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs), (lift g p.1 p.2).toNat
    Score g M = 1 + 4 * Q := by
  intro S Q
  have hlsymm := lift_symm hsymm
  have hQR : ∑ p ∈ S.filter (fun p => 0 < p.1 ∧ p.2.natAbs < p.1.natAbs), (lift g p.1 p.2).toNat = Q := by
    apply Finset.sum_bij (fun p _ => (-p.1, p.2))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hp ⊢
      refine ⟨⟨⟨by omega, by omega⟩, hp.1.2⟩, by omega, by simp only [Int.natAbs_neg]; exact hp.2.2⟩
    · intro p1 _ p2 _ heq; ext <;> simp_all
    · intro q hq
      refine ⟨(-q.1, q.2), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hq ⊢
      refine ⟨⟨⟨by omega, by omega⟩, hq.1.2⟩, by omega, by simp only [Int.natAbs_neg]; exact hq.2.2⟩
    · intro p _; simp only [hlsymm.1]
  have hQU : ∑ p ∈ S.filter (fun p => 0 < p.2 ∧ p.1.natAbs < p.2.natAbs), (lift g p.1 p.2).toNat = Q := by
    rw [← hQR]
    apply Finset.sum_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.1, hp.2.2⟩
    · intro p1 _ p2 _ heq; ext <;> simp_all
    · intro q hq
      refine ⟨(q.2, q.1), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2.1, hq.2.2⟩
    · intro p _; simp only [hlsymm.2.2]
  have hQD : ∑ p ∈ S.filter (fun p => p.2 < 0 ∧ p.1.natAbs < p.2.natAbs), (lift g p.1 p.2).toNat = Q := by
    rw [← hQU]
    apply Finset.sum_bij (fun p _ => (p.1, -p.2))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hp ⊢
      refine ⟨⟨hp.1.1, ⟨by omega, by omega⟩⟩, by omega, by simp only [Int.natAbs_neg]; exact hp.2.2⟩
    · intro p1 _ p2 _ heq; ext <;> simp_all
    · intro q hq
      refine ⟨(q.1, -q.2), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S] at hq ⊢
      refine ⟨⟨hq.1.1, ⟨by omega, by omega⟩⟩, by omega, by simp only [Int.natAbs_neg]; exact hq.2.2⟩
    · intro p _; simp only [hlsymm.2.1]
  have hdiag_sum : ∑ p ∈ S.filter (fun p => p.1.natAbs = p.2.natAbs), (lift g p.1 p.2).toNat = 1 := by
    have hmem0 : (0, 0) ∈ S.filter (fun p => p.1.natAbs = p.2.natAbs) := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S, Int.natAbs_zero]
      exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, trivial⟩
    rw [Finset.sum_eq_single (0, 0)]
    · simp [lift, h0]
    · intro p hp hp0
      simp only [Finset.mem_filter] at hp
      have hne : p.1 ≠ 0 := by
        intro h1; apply hp0; ext
        · exact h1
        · have : p.2.natAbs = 0 := by rw [← hp.2, h1]; rfl
          exact Int.natAbs_eq_zero.mp this
      rw [lift_diag_false hdiag hne hp.2]; rfl
    · intro h; exact absurd hmem0 h
  unfold Score
  change ∑ p ∈ S, (lift g p.1 p.2).toNat = 1 + 4 * Q
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p.1.natAbs = p.2.natAbs)]
  rw [hdiag_sum]
  have hrest : S.filter (fun p => ¬ p.1.natAbs = p.2.natAbs) =
      (S.filter (fun p => p.2.natAbs < p.1.natAbs)) ∪ (S.filter (fun p => p.1.natAbs < p.2.natAbs)) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨h1, h2⟩; rcases lt_or_gt_of_ne h2 with hlt | hgt; exact Or.inr ⟨h1, hlt⟩; exact Or.inl ⟨h1, hgt⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
  rw [hrest, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
  have hLR : S.filter (fun p => p.2.natAbs < p.1.natAbs) =
      (S.filter (fun p => 0 < p.1 ∧ p.2.natAbs < p.1.natAbs)) ∪
      (S.filter (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs)) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨h1, h2⟩; by_cases hp : 0 < p.1; exact Or.inl ⟨h1, hp, h2⟩; exact Or.inr ⟨h1, by omega, h2⟩
    · rintro (⟨h1, _, h2⟩ | ⟨h1, _, h2⟩) <;> exact ⟨h1, h2⟩
  have hUD : S.filter (fun p => p.1.natAbs < p.2.natAbs) =
      (S.filter (fun p => 0 < p.2 ∧ p.1.natAbs < p.2.natAbs)) ∪
      (S.filter (fun p => p.2 < 0 ∧ p.1.natAbs < p.2.natAbs)) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro ⟨h1, h2⟩; by_cases hp : 0 < p.2; exact Or.inl ⟨h1, hp, h2⟩; exact Or.inr ⟨h1, by omega, h2⟩
    · rintro (⟨h1, _, h2⟩ | ⟨h1, _, h2⟩) <;> exact ⟨h1, h2⟩
  rw [hLR, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
  rw [hUD, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
  rw [hQR, hQU, hQD]
  omega

private lemma Score_Combine {M : ℕ} (hM : 4 ≤ M) {g_in g_out : ℤ → ℤ → Bool}
    (hin_supp : ∀ x y : ℤ, M ≤ x.natAbs + y.natAbs → g_in x y = false)
    (hin_bdy : ∀ x y : ℤ, x.natAbs + y.natAbs = M - 1 → g_in x y = true)
    (hin_symm : (∀ x y : ℤ, g_in (-x) y = g_in x y) ∧
                (∀ x y : ℤ, g_in x (-y) = g_in x y) ∧
                (∀ x y : ℤ, g_in y x = g_in x y))
    (hout_supp : ∀ x y : ℤ, M ≤ x.natAbs + y.natAbs → g_out x y = false)
    (hout_symm : (∀ x y : ℤ, g_out (-x) y = g_out x y) ∧
                 (∀ x y : ℤ, g_out x (-y) = g_out x y) ∧
                 (∀ x y : ℤ, g_out y x = g_out x y))
    (hout_0 : g_out 0 0 = true)
    (hout_diag : ∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → g_out x y = false) :
    Score (Combine M g_in g_out) (2 * M) + 3 = Score g_in M + 3 * Score g_out M := by
  set S1 := Finset.Icc (-(2 * (M : ℤ) - 1)) (2 * (M : ℤ) - 1) ×ˢ
            Finset.Icc (-(2 * (M : ℤ) - 1)) (2 * (M : ℤ) - 1)
  set S2 := Finset.Icc (-(2 * ((2 * M : ℕ) : ℤ) - 1)) (2 * ((2 * M : ℕ) : ℤ) - 1) ×ˢ
            Finset.Icc (-(2 * ((2 * M : ℕ) : ℤ) - 1)) (2 * ((2 * M : ℕ) : ℤ) - 1)
  set H := Combine M g_in g_out
  have hHsymm := lift_symm (Combine_symm (M := M) hin_symm hout_symm)
  have hQ_eq := Score_quadrant_decomp hM hout_supp hout_symm hout_0 hout_diag
  set Q := ∑ p ∈ S1.filter (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs), (lift g_out p.1 p.2).toNat
  -- Step 1: Split S2 into |i|+|j| < 2*M and 2*M <= |i|+|j|
  have hsplit_S2 : Score H (2 * M) =
      (∑ p ∈ S2.filter (fun p => p.1.natAbs + p.2.natAbs < 2 * M), (lift H p.1 p.2).toNat) +
      (∑ p ∈ S2.filter (fun p => ¬ p.1.natAbs + p.2.natAbs < 2 * M), (lift H p.1 p.2).toNat) := by
    unfold Score
    exact (Finset.sum_filter_add_sum_filter_not S2 (fun p => p.1.natAbs + p.2.natAbs < 2 * M) _).symm
  -- Step 2: Interior sum + 4 = Score g_in M
  have hsum_in : (∑ p ∈ S2.filter (fun p => p.1.natAbs + p.2.natAbs < 2 * M), (lift H p.1 p.2).toNat) + 4 =
      Score g_in M := by
    have hset_eq : S2.filter (fun p => p.1.natAbs + p.2.natAbs < 2 * M) =
        S1.filter (fun p => p.1.natAbs + p.2.natAbs < 2 * M) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S1, S2]; push_cast; omega
    rw [hset_eq]
    have hgin_in : ∑ p ∈ S1.filter (fun p => p.1.natAbs + p.2.natAbs < 2 * M), (lift g_in p.1 p.2).toNat =
        Score g_in M := by
      unfold Score
      rw [← Finset.sum_filter_add_sum_filter_not S1 (fun p => p.1.natAbs + p.2.natAbs < 2 * M)]
      have hzero : ∑ p ∈ S1.filter (fun p => ¬ p.1.natAbs + p.2.natAbs < 2 * M), (lift g_in p.1 p.2).toNat = 0 := by
        apply Finset.sum_eq_zero; intro p hp
        simp only [Finset.mem_filter] at hp
        rw [lift_support hin_supp (by omega)]; rfl
      omega
    rw [← hgin_in]
    set pred : ℤ × ℤ → Prop := fun p =>
      (p.1 = 2 * (M : ℤ) - 1 ∧ p.2 = 0) ∨ (p.1 = -(2 * (M : ℤ) - 1) ∧ p.2 = 0) ∨
      (p.1 = 0 ∧ p.2 = 2 * (M : ℤ) - 1) ∨ (p.1 = 0 ∧ p.2 = -(2 * (M : ℤ) - 1))
    set F := S1.filter (fun p => p.1.natAbs + p.2.natAbs < 2 * M)
    rw [← Finset.sum_filter_add_sum_filter_not F pred (fun p => (lift H p.1 p.2).toNat)]
    rw [← Finset.sum_filter_add_sum_filter_not F pred (fun p => (lift g_in p.1 p.2).toNat)]
    have hsame_not : ∑ p ∈ F.filter (fun p => ¬ pred p), (lift H p.1 p.2).toNat =
        ∑ p ∈ F.filter (fun p => ¬ pred p), (lift g_in p.1 p.2).toNat := by
      apply Finset.sum_congr rfl; intro p hp
      simp only [Finset.mem_filter, F] at hp
      rw [lift_Combine_in hM hin_supp hin_bdy hout_0 hout_diag hp.1.2, if_neg hp.2]
    have hH_tip : ∑ p ∈ F.filter pred, (lift H p.1 p.2).toNat = 0 := by
      apply Finset.sum_eq_zero; intro p hp
      simp only [Finset.mem_filter, F] at hp
      rw [lift_Combine_in hM hin_supp hin_bdy hout_0 hout_diag hp.1.2, if_pos hp.2]; rfl
    have hFpred : F.filter pred =
        {(2 * (M : ℤ) - 1, 0), (-(2 * (M : ℤ) - 1), 0), (0, 2 * (M : ℤ) - 1), (0, -(2 * (M : ℤ) - 1))} := by
      ext ⟨pi, pj⟩
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, F, S1,
        Finset.mem_product, Finset.mem_Icc, pred, Prod.ext_iff]
      constructor
      · intro hp; exact hp.2
      · intro hp
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
        · exact ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
        · exact ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    have hgin_tip : ∑ p ∈ F.filter pred, (lift g_in p.1 p.2).toNat = 4 := by
      rw [hFpred]
      have h1 : lift g_in (2 * (M : ℤ) - 1) 0 = true := by
        simp only [lift, show (2 * (M : ℤ) - 1) % 2 = 1 by omega, show (0 : ℤ) % 2 = 0 by omega,
          show (1 : ℤ) ≠ 0 by omega, and_self, false_and, ↓reduceIte]
        rw [show (2 * (M : ℤ) - 1 - 1) / 2 = (M : ℤ) - 1 by omega,
          show (2 * (M : ℤ) - 1 + 1) / 2 = M by omega, show (0 : ℤ) / 2 = 0 by omega]
        rw [hin_bdy ((M : ℤ) - 1) 0 (by omega), hin_supp M 0 (by omega)]; rfl
      have h2 : lift g_in (-(2 * (M : ℤ) - 1)) 0 = true := by
        rw [(lift_symm hin_symm).1]; exact h1
      have h3 : lift g_in 0 (2 * (M : ℤ) - 1) = true := by
        rw [(lift_symm hin_symm).2.2]; exact h1
      have h4 : lift g_in 0 (-(2 * (M : ℤ) - 1)) = true := by
        rw [(lift_symm hin_symm).2.1]; exact h3
      rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]; rintro (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩) <;> omega),
        Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]; rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> omega),
        Finset.sum_insert (by simp only [Finset.mem_singleton, Prod.ext_iff]; rintro ⟨_, h2⟩; omega),
        Finset.sum_singleton]
      rw [h1, h2, h3, h4]
      rfl
    rw [hsame_not, hH_tip, hgin_tip]
    omega
  -- Step 3: Exterior sum = 4 * C where C + Q = Score g_out M
  set S2out := S2.filter (fun p => ¬ p.1.natAbs + p.2.natAbs < 2 * M)
  set C := ∑ p ∈ S2out.filter (fun p => 0 < p.1 ∧ p.2.natAbs < p.1.natAbs), (lift H p.1 p.2).toNat
  have hsum_out : ∑ p ∈ S2out, (lift H p.1 p.2).toNat = 4 * C := by
    have hdiag0 : ∑ p ∈ S2out.filter (fun p => p.1.natAbs = p.2.natAbs), (lift H p.1 p.2).toNat = 0 := by
      apply Finset.sum_eq_zero; intro p hp
      simp only [Finset.mem_filter, S2out] at hp
      simp only [lift]
      split_ifs with h1 h2 h3
      · simp only [H, Combine, if_neg (by omega : ¬ ((p.1 / 2).natAbs + (p.2 / 2).natAbs < M)),
          if_pos (by omega : (p.1 / 2).natAbs = (p.2 / 2).natAbs)]; rfl
      · omega
      · omega
      · rfl
    have hCL : ∑ p ∈ S2out.filter (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs), (lift H p.1 p.2).toNat = C := by
      apply Finset.sum_bij (fun p _ => (-p.1, p.2))
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hp ⊢
        push_cast at hp ⊢
        refine ⟨⟨⟨⟨by omega, by omega⟩, hp.1.1.2⟩, by simp only [Int.natAbs_neg]; exact hp.1.2⟩,
          by omega, by simp only [Int.natAbs_neg]; exact hp.2.2⟩
      · intro p1 _ p2 _ heq; ext <;> simp_all
      · intro q hq
        refine ⟨(-q.1, q.2), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hq ⊢
        push_cast at hq ⊢
        refine ⟨⟨⟨⟨by omega, by omega⟩, hq.1.1.2⟩, by simp only [Int.natAbs_neg]; exact hq.1.2⟩,
          by omega, by simp only [Int.natAbs_neg]; exact hq.2.2⟩
      · intro p _; exact congrArg Bool.toNat (hHsymm.1 p.1 p.2).symm
    have hCU : ∑ p ∈ S2out.filter (fun p => 0 < p.2 ∧ p.1.natAbs < p.2.natAbs), (lift H p.1 p.2).toNat = C := by
      apply Finset.sum_bij (fun p _ => (p.2, p.1))
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hp ⊢
        refine ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, by omega⟩, hp.2.1, hp.2.2⟩
      · intro p1 _ p2 _ heq; ext <;> simp_all
      · intro q hq
        refine ⟨(q.2, q.1), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hq ⊢
        refine ⟨⟨⟨hq.1.1.2, hq.1.1.1⟩, by omega⟩, hq.2.1, hq.2.2⟩
      · intro p _; exact congrArg Bool.toNat (hHsymm.2.2 p.1 p.2).symm
    have hCD : ∑ p ∈ S2out.filter (fun p => p.2 < 0 ∧ p.1.natAbs < p.2.natAbs), (lift H p.1 p.2).toNat = C := by
      rw [← hCU]
      apply Finset.sum_bij (fun p _ => (p.1, -p.2))
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hp ⊢
        push_cast at hp ⊢
        refine ⟨⟨⟨hp.1.1.1, ⟨by omega, by omega⟩⟩, by simp only [Int.natAbs_neg]; exact hp.1.2⟩,
          by omega, by simp only [Int.natAbs_neg]; exact hp.2.2⟩
      · intro p1 _ p2 _ heq; ext <;> simp_all
      · intro q hq
        refine ⟨(q.1, -q.2), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, S2out, S2] at hq ⊢
        push_cast at hq ⊢
        refine ⟨⟨⟨hq.1.1.1, ⟨by omega, by omega⟩⟩, by simp only [Int.natAbs_neg]; exact hq.1.2⟩,
          by omega, by simp only [Int.natAbs_neg]; exact hq.2.2⟩
      · intro p _; exact congrArg Bool.toNat (hHsymm.2.1 p.1 p.2).symm
    rw [← Finset.sum_filter_add_sum_filter_not S2out (fun p => p.1.natAbs = p.2.natAbs)]
    rw [hdiag0, zero_add]
    have hrest : S2out.filter (fun p => ¬ p.1.natAbs = p.2.natAbs) =
        (S2out.filter (fun p => p.2.natAbs < p.1.natAbs)) ∪ (S2out.filter (fun p => p.1.natAbs < p.2.natAbs)) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro ⟨h1, h2⟩; rcases lt_or_gt_of_ne h2 with hlt | hgt; exact Or.inr ⟨h1, hlt⟩; exact Or.inl ⟨h1, hgt⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
    rw [hrest, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
    have hLR : S2out.filter (fun p => p.2.natAbs < p.1.natAbs) =
        (S2out.filter (fun p => 0 < p.1 ∧ p.2.natAbs < p.1.natAbs)) ∪
        (S2out.filter (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs)) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro ⟨h1, h2⟩; by_cases hp : 0 < p.1; exact Or.inl ⟨h1, hp, h2⟩; exact Or.inr ⟨h1, by omega, h2⟩
      · rintro (⟨h1, _, h2⟩ | ⟨h1, _, h2⟩) <;> exact ⟨h1, h2⟩
    have hUD : S2out.filter (fun p => p.1.natAbs < p.2.natAbs) =
        (S2out.filter (fun p => 0 < p.2 ∧ p.1.natAbs < p.2.natAbs)) ∪
        (S2out.filter (fun p => p.2 < 0 ∧ p.1.natAbs < p.2.natAbs)) := by
      ext p; simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro ⟨h1, h2⟩; by_cases hp : 0 < p.2; exact Or.inl ⟨h1, hp, h2⟩; exact Or.inr ⟨h1, by omega, h2⟩
      · rintro (⟨h1, _, h2⟩ | ⟨h1, _, h2⟩) <;> exact ⟨h1, h2⟩
    rw [hLR, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
    rw [hUD, Finset.sum_union (by rw [Finset.disjoint_filter]; intro p _ h1 h2; omega)]
    rw [hCL, hCU, hCD]
    omega
  -- Step 4: C + Q = Score g_out M via shift bijection (i, j) ↦ (i - 2*M, j)
  have hCQ : C + Q = Score g_out M := by
    have hS1_split : Score g_out M =
        Q + ∑ p ∈ S1.filter (fun p => ¬ (p.1 < 0 ∧ p.2.natAbs < p.1.natAbs)), (lift g_out p.1 p.2).toNat := by
      unfold Score
      exact (Finset.sum_filter_add_sum_filter_not S1 (fun p => p.1 < 0 ∧ p.2.natAbs < p.1.natAbs) _).symm
    have hC_eq : C = ∑ p ∈ S1.filter (fun p => ¬ (p.1 < 0 ∧ p.2.natAbs < p.1.natAbs)), (lift g_out p.1 p.2).toNat := by
      set R1 := S2out.filter (fun p => 0 < p.1 ∧ p.2.natAbs < p.1.natAbs)
      set R2 := S1.filter (fun p => ¬ (p.1 < 0 ∧ p.2.natAbs < p.1.natAbs))
      change ∑ p ∈ R1, (lift H p.1 p.2).toNat = ∑ p ∈ R2, (lift g_out p.1 p.2).toNat
      rw [← Finset.sum_filter_add_sum_filter_not R1 (fun p => (p.1 - 2 * (M : ℤ)).natAbs + p.2.natAbs < 2 * M)]
      rw [← Finset.sum_filter_add_sum_filter_not R2 (fun p => p.1.natAbs + p.2.natAbs < 2 * M)]
      have hz1 : ∑ p ∈ R1.filter (fun p => ¬ (p.1 - 2 * (M : ℤ)).natAbs + p.2.natAbs < 2 * M),
          (lift H p.1 p.2).toNat = 0 := by
        apply Finset.sum_eq_zero; intro p hp
        simp only [Finset.mem_filter, R1, S2out] at hp
        rw [lift_Combine_right_cone hM hout_supp hout_diag (by omega) hp.1.2.1 hp.1.2.2]
        rw [lift_support hout_supp (by omega)]; rfl
      have hz2 : ∑ p ∈ R2.filter (fun p => ¬ p.1.natAbs + p.2.natAbs < 2 * M),
          (lift g_out p.1 p.2).toNat = 0 := by
        apply Finset.sum_eq_zero; intro p hp
        simp only [Finset.mem_filter] at hp
        rw [lift_support hout_supp (by omega)]; rfl
      rw [hz1, hz2, add_zero, add_zero]
      apply Finset.sum_bij (fun p _ => (p.1 - 2 * (M : ℤ), p.2))
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, R1, R2, S1, S2out, S2] at hp ⊢
        push_cast at hp ⊢
        refine ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, hp.2⟩
      · intro p1 _ p2 _ heq
        simp only [Prod.mk.injEq] at heq; ext <;> omega
      · intro q hq
        refine ⟨(q.1 + 2 * (M : ℤ), q.2), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, R1, R2, S1, S2out, S2] at hq ⊢
        push_cast at hq ⊢
        refine ⟨⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
      · intro p hp
        simp only [Finset.mem_filter, R1, S2out] at hp
        rw [lift_Combine_right_cone hM hout_supp hout_diag (by omega) hp.1.2.1 hp.1.2.2]
    omega
  change Score g_out M = 1 + 4 * Q at hQ_eq
  rw [hsplit_S2, hsum_out] at *
  omega

/-! ### Part 6: Closed forms, `onCount` bridge, and `OMA.solution` -/

private lemma Score_StaticTrunc_base : Score (StaticTrunc 2) 4 = 77 := by
  unfold Score
  rw [Finset.sum_product]
  decide

private lemma Score_A3_base : Score (A 3) 4 = 61 := by
  have hfn : A 3 = A3_tab := by funext x y; exact A3_eq_tab x y
  rw [hfn]
  unfold Score
  rw [Finset.sum_product]
  decide

private lemma StaticTrunc_props (m : ℕ) (hm : 2 ≤ m) :
    (∀ x y : ℤ, 2 ^ m ≤ x.natAbs + y.natAbs → StaticTrunc m x y = false) ∧
    (∀ x y : ℤ, x.natAbs + y.natAbs = 2 ^ m - 1 → StaticTrunc m x y = true) ∧
    ((∀ x y : ℤ, StaticTrunc m (-x) y = StaticTrunc m x y) ∧
     (∀ x y : ℤ, StaticTrunc m x (-y) = StaticTrunc m x y) ∧
     (∀ x y : ℤ, StaticTrunc m y x = StaticTrunc m x y)) ∧
    StaticTrunc m 0 0 = true ∧
    (∀ x y : ℤ, x ≠ 0 → x.natAbs = y.natAbs → StaticTrunc m x y = false) := by
  have hM4 : 4 ≤ 2 ^ m := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm; simpa using this
  have hMeven : 2 ^ m % 2 = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hge; simp [StaticTrunc, show ¬ (x.natAbs + y.natAbs < 2 ^ m) by omega]
  · intro x y hbd
    simp only [StaticTrunc, if_pos (by omega : x.natAbs + y.natAbs < 2 ^ m)]
    exact Static_odd m hm x y (by omega) (by omega)
  · obtain ⟨hsx, hsy, hss⟩ := Static_symm m
    refine ⟨?_, ?_, ?_⟩
    · intro x y; simp only [StaticTrunc, Int.natAbs_neg, hsx]
    · intro x y; simp only [StaticTrunc, Int.natAbs_neg, hsy]
    · intro x y; simp only [StaticTrunc, add_comm y.natAbs x.natAbs, hss]
  · simp only [StaticTrunc, Int.natAbs_zero, add_zero, if_pos (by omega : 0 < 2 ^ m)]
    exact Static_origin m hm
  · intro x y hx hxy
    simp only [StaticTrunc]
    split_ifs with hlt
    · exact Static_diag_false m hm x y hx hxy hlt
    · rfl

private lemma Score_StaticTrunc_closed (m : ℕ) (hm : 2 ≤ m) :
    Score (StaticTrunc m) (2 ^ m) = 19 * 4 ^ (m - 1) + 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => exact Score_StaticTrunc_base
      | succ k =>
        have hM4 : 4 ≤ 2 ^ (k + 2) := by
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 2 ≤ k + 2 by omega); simpa using this
        obtain ⟨hsupp, hbdy, hsymm, h0, hdiag⟩ := StaticTrunc_props (k + 2) (by omega)
        have hcomb : Score (Combine (2 ^ (k + 2)) (StaticTrunc (k + 2)) (StaticTrunc (k + 2)))
            (2 * 2 ^ (k + 2)) + 3 =
            Score (StaticTrunc (k + 2)) (2 ^ (k + 2)) + 3 * Score (StaticTrunc (k + 2)) (2 ^ (k + 2)) :=
          Score_Combine hM4 hsupp hbdy hsymm hsupp hsymm h0 hdiag
        have heq : Score (StaticTrunc (k + 3)) (2 ^ (k + 3)) =
            Score (Combine (2 ^ (k + 2)) (StaticTrunc (k + 2)) (StaticTrunc (k + 2))) (2 * 2 ^ (k + 2)) := by
          rw [show 2 ^ (k + 3) = 2 * 2 ^ (k + 2) by ring]
          unfold Score
          apply Finset.sum_congr rfl; intro p _
          have hfn : StaticTrunc (k + 3) = Combine (2 ^ (k + 2)) (StaticTrunc (k + 2)) (StaticTrunc (k + 2)) := by
            funext x y; exact StaticTrunc_succ (m := k + 2) (by omega) x y
          rw [hfn]
        have hih : Score (StaticTrunc (k + 2)) (2 ^ (k + 2)) = 19 * 4 ^ (k + 1) + 1 := by
          simpa [show k + 1 + 1 = k + 2 by omega, show k + 1 + 1 - 1 = k + 1 by omega] using ih (by omega)
        have hpow4 : 4 ^ (k + 1 + 1 + 1 - 1) = 4 * 4 ^ (k + 1) := by
          have h1 : k + 1 + 1 + 1 - 1 = (k + 1) + 1 := by omega
          rw [h1, pow_succ]; ring
        rw [heq]
        omega

private lemma Score_A_closed (m : ℕ) (hm : 2 ≤ m) :
    Score (A (2 ^ m - 1)) (2 ^ m) + 16 * 3 ^ (m - 2) = 19 * 4 ^ (m - 1) + 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero =>
        rw [show 2 ^ 2 - 1 = 3 by rfl, show 2 ^ 2 = 4 by rfl, Score_A3_base]
        norm_num
      | succ k =>
        have hM4 : 4 ≤ 2 ^ (k + 2) := by
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 2 ≤ k + 2 by omega); simpa using this
        obtain ⟨hsupp, hbdy, hsymm, _, _⟩ := StaticTrunc_props (k + 2) (by omega)
        have hcomb : Score (Combine (2 ^ (k + 2)) (StaticTrunc (k + 2)) (A (2 ^ (k + 2) - 1)))
            (2 * 2 ^ (k + 2)) + 3 =
            Score (StaticTrunc (k + 2)) (2 ^ (k + 2)) + 3 * Score (A (2 ^ (k + 2) - 1)) (2 ^ (k + 2)) :=
          Score_Combine hM4 hsupp hbdy hsymm
            (fun x y hge => A_support (2 ^ (k + 2) - 1) x y (by omega))
            (A_symm (2 ^ (k + 2) - 1))
            (A_origin_true (2 ^ (k + 2) - 1))
            (A_diag_false (2 ^ (k + 2) - 1))
        have heq : Score (A (2 ^ (k + 3) - 1)) (2 ^ (k + 3)) =
            Score (Combine (2 ^ (k + 2)) (StaticTrunc (k + 2)) (A (2 ^ (k + 2) - 1))) (2 * 2 ^ (k + 2)) := by
          have hfn : A (2 ^ (k + 3) - 1) = Combine (2 ^ (k + 2)) (StaticTrunc (k + 2)) (A (2 ^ (k + 2) - 1)) := by
            funext x y; exact A_pow_sub_one_eq_Combine (m := k + 2) (by omega) x y
          rw [hfn, show 2 ^ (k + 3) = 2 * 2 ^ (k + 2) by ring]
        have hst : Score (StaticTrunc (k + 2)) (2 ^ (k + 2)) = 19 * 4 ^ (k + 1) + 1 := by
          simpa [show k + 2 - 1 = k + 1 by omega] using Score_StaticTrunc_closed (k + 2) (by omega)
        have hih : Score (A (2 ^ (k + 2) - 1)) (2 ^ (k + 2)) + 16 * 3 ^ k = 19 * 4 ^ (k + 1) + 1 := by
          simpa [show k + 1 + 1 = k + 2 by omega, show k + 1 + 1 - 1 = k + 1 by omega,
            show k + 1 + 1 - 2 = k by omega] using ih (by omega)
        have hpow4 : 4 ^ (k + 1 + 1 + 1 - 1) = 4 * 4 ^ (k + 1) := by
          have h1 : k + 1 + 1 + 1 - 1 = (k + 1) + 1 := by omega
          rw [h1, pow_succ]; ring
        have hpow3 : 3 ^ (k + 1 + 1 + 1 - 2) = 3 * 3 ^ k := by
          have h1 : k + 1 + 1 + 1 - 2 = k + 1 := by omega
          rw [h1, pow_succ]; ring
        rw [heq]
        omega

private lemma onCount_eq_Score (M : ℕ) (hM : 1 ≤ M) :
    onCount 646 (2 * M - 1) = Score (A (M - 1)) M := by
  unfold onCount Score
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun p _ => ((p.1 : ℤ) - (2 * M - 1 : ℕ), (p.2 : ℤ) - (2 * M - 1 : ℕ)))
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    omega
  · intro p1 _ p2 _ heq
    simp only [Prod.mk.injEq] at heq; ext <;> omega
  · intro q hq
    simp only [Finset.mem_product, Finset.mem_Icc] at hq
    refine ⟨((q.1 + (2 * M - 1 : ℕ)).toNat, (q.2 + (2 * M - 1 : ℕ)).toNat), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]; omega
    · ext <;> simp <;> omega
  · intro p _
    have ht : 2 * M - 1 = 2 * (M - 1) + 1 := by omega
    rw [ht, (cell_even_and_odd (M - 1)).2]
    change (if lift (A (M - 1)) _ _ then 1 else 0) = (lift (A (M - 1)) _ _).toNat
    cases lift (A (M - 1)) ((p.1 : ℤ) - (2 * (M - 1) + 1 : ℕ)) ((p.2 : ℤ) - (2 * (M - 1) + 1 : ℕ)) <;> rfl

private lemma main_proof :
    ∀ n : ℕ, 3 ≤ n → (a n : ℚ) = 19 * (4 : ℚ) ^ (n - 2) - 16 * (3 : ℚ) ^ (n - 3) + 1 := by
  intro n hn
  set m : ℕ := n - 1
  have hm : 2 ≤ m := by omega
  have hpow : 2 ^ n = 2 * 2 ^ m := by
    have : n = m + 1 := by omega
    rw [this, pow_succ]; ring
  have ha_eq : onCount 646 (2 ^ n - 1) = Score (A (2 ^ m - 1)) (2 ^ m) := by
    rw [hpow]
    exact onCount_eq_Score (2 ^ m) Nat.one_le_two_pow
  have hclosed := Score_A_closed m hm
  have hcast : ((onCount 646 (2 ^ n - 1) : ℕ) : ℚ) + 16 * (3 : ℚ) ^ (m - 2) =
      19 * (4 : ℚ) ^ (m - 1) + 1 := by
    rw [ha_eq]
    exact_mod_cast hclosed
  have hm1 : m - 1 = n - 2 := by omega
  have hm2 : m - 2 = n - 3 := by omega
  rw [hm1, hm2] at hcast
  unfold a
  push_cast
  linarith

end OEISA273327Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a273327.main :=
  OEISA273327Proof.main_proof

