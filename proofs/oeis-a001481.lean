import OMAStatements.S_oeis_a001481

namespace Lowell

-- An odd square leaves 1 modulo 8. An even square leaves 0 or 4.
private theorem squareResidue (x : ℕ) :
    (x % 2 = 0 ∧ (x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 4)) ∨
    (x % 2 = 1 ∧ x ^ 2 % 8 = 1) := by
  have table : ∀ r : Fin 8,
      (r.val % 2 = 0 ∧ (r.val ^ 2 % 8 = 0 ∨ r.val ^ 2 % 8 = 4)) ∨
      (r.val % 2 = 1 ∧ r.val ^ 2 % 8 = 1) := by decide
  have parity : x % 2 = (x % 8) % 2 := by omega
  have square : x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using Nat.mul_mod x x 8
  rw [parity, square]
  exact table ⟨x % 8, Nat.mod_lt _ (by decide)⟩

private theorem notThree (x y : ℕ) : x ^ 2 + y ^ 2 ≠ 3 := by
  have hx := squareResidue x
  have hy := squareResidue y
  omega

private theorem evenWhenEightDivides (x y z w q : ℕ)
    (h : (x ^ 2 + y ^ 2) + (z ^ 2 + w ^ 2) = 8 * q) :
    x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 ∧ w % 2 = 0 := by
  have hx := squareResidue x
  have hy := squareResidue y
  have hz := squareResidue z
  have hw := squareResidue w
  omega

private theorem halveSquare (x : ℕ) (even : x % 2 = 0) :
    x ^ 2 = 4 * (x / 2) ^ 2 := by
  have twice : x = 2 * (x / 2) := by omega
  calc
    x ^ 2 = (2 * (x / 2)) ^ 2 := congrArg (fun v : ℕ => v ^ 2) twice
    _ = 4 * (x / 2) ^ 2 := Nat.mul_pow 2 (x / 2) 2

theorem classify (k x y z w : ℕ)
    (h : (x ^ 2 + y ^ 2) + (z ^ 2 + w ^ 2) = 2 ^ k) :
    x ^ 2 + y ^ 2 = 0 ∨ z ^ 2 + w ^ 2 = 0 ∨ x ^ 2 + y ^ 2 = z ^ 2 + w ^ 2 := by
  induction k using Nat.strongRecOn generalizing x y z w with
  | ind k ih =>
    by_cases small : k ≤ 2
    · have powers : (2 : ℕ) ^ k = 1 ∨ 2 ^ k = 2 ∨ 2 ^ k = 4 := by
        have cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases cases with rfl | rfl | rfl <;> decide
      have left := notThree x y
      have right := notThree z w
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have pow8 : (2 : ℕ) ^ (j + 3) = 8 * 2 ^ j := by
        rw [Nat.pow_add, Nat.mul_comm]
      have pow2 : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by
        rw [Nat.pow_succ, Nat.mul_comm]
      obtain ⟨hx, hy, hz, hw⟩ := evenWhenEightDivides x y z w (2 ^ j) (h.trans pow8)
      have sx := halveSquare x hx
      have sy := halveSquare y hy
      have sz := halveSquare z hz
      have sw := halveSquare w hw
      have smaller : ((x / 2) ^ 2 + (y / 2) ^ 2) +
          ((z / 2) ^ 2 + (w / 2) ^ 2) = 2 ^ (j + 1) := by omega
      have result := ih (j + 1) (by omega) (x / 2) (y / 2) (z / 2) (w / 2) smaller
      omega

end Lowell

theorem OMA.solution : type_of% @OMA.S_oeis_a001481.main := by
  rintro a b k _ different ⟨x, y, rfl⟩ ⟨z, w, rfl⟩ sum
  rcases Lowell.classify k x y z w sum with left | right | equal
  · exact Or.inl left
  · exact Or.inr right
  · exact (different equal).elim
