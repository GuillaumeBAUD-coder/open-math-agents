import FormalConjectures.OEIS.«109074»

/-! # A109074 and vertically symmetric alternating-sign matrices
Credit: @shivareddy42. The two steps are correctness of the row-counting program
and the vertically symmetric ASM enumeration of Kuperberg (Ann. Math., 2002).
The ratio of consecutive factorial products is verified here. -/

namespace OMA.R_OeisA109074_conjecture_R1

open Finset OeisA109074

private theorem factor_eq (n : ℕ) : frac (n+1) = ((6*n+4).factorial : ℚ) * (2*n+1).factorial /
    (2 * (4*n+3).factorial * (4*n+2).factorial) := by
  unfold frac
  rw [show 6*(n+1)-2 = 6*n+4 by omega, show 4*(n+1)-1 = 4*n+3 by omega]
  push_cast
  rw [Nat.cast_choose ℚ (show 2*(n+1) ≤ 6*n+4 by omega),
      Nat.cast_choose ℚ (show 2*(n+1) ≤ 4*n+3 by omega),
      show 6*n+4-2*(n+1) = 4*n+2 by omega,
      show 4*n+3-2*(n+1) = 2*n+1 by omega]
  have pos (k : ℕ) : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  field_simp [fun k => (pos k).ne']

-- The symbols 0, 1, 2 encode the matrix entries -1, 0, 1.
def H1 : Prop := ∀ n : ℕ,
  let I := Fin (2*n+1)
  let lineOK (v : I → Fin 3) :=
    let partialSum (k : ℕ) := ∑ j : I, if j.val < k then ((v j).val : ℤ) - 1 else 0
    partialSum (2*n+1) = 1 ∧ ∀ k : Fin (2*n+2), partialSum k.val = 0 ∨ partialSum k.val = 1
  let matrices : Set (I → I → Fin 3) := {M | (∀ i, lineOK (M i)) ∧
    (∀ j, lineOK fun i => M i j) ∧ ∀ i j, M i j = M i (Fin.rev j)}
  b n = matrices.ncard

def H2 : Prop := ∀ n : ℕ,
  let I := Fin (2*n+1)
  let lineOK (v : I → Fin 3) :=
    let partialSum (k : ℕ) := ∑ j : I, if j.val < k then ((v j).val : ℤ) - 1 else 0
    partialSum (2*n+1) = 1 ∧ ∀ k : Fin (2*n+2), partialSum k.val = 0 ∨ partialSum k.val = 1
  let matrices : Set (I → I → Fin 3) := {M | (∀ i, lineOK (M i)) ∧
    (∀ j, lineOK fun i => M i j) ∧ ∀ i j, M i j = M i (Fin.rev j)}
  (matrices.ncard : ℚ) = ∏ k ∈ range n, ((6*k+4).factorial : ℚ) * (2*k+1).factorial /
    (2 * (4*k+3).factorial * (4*k+2).factorial)

theorem main : H1 → H2 → type_of% @OeisA109074.conjecture := by
  intro hcount hformula n
  let F (k : ℕ) : ℚ := ((6*k+4).factorial : ℚ) * (2*k+1).factorial /
    (2 * (4*k+3).factorial * (4*k+2).factorial)
  have eqn (j : ℕ) : (b j : ℚ) = ∏ k ∈ range j, F k := by
    rw [hcount j]
    exact hformula j
  have pos (k : ℕ) : 0 < F k := by dsimp [F]; positivity
  have hp : (∏ k ∈ range n, F k) ≠ 0 := (Finset.prod_pos (fun i _ => pos i)).ne'
  rw [eqn, eqn, prod_range_succ]
  change frac (n+1) = (∏ k ∈ range n, F k) * F n / (∏ k ∈ range n, F k)
  rw [mul_div_cancel_left₀ _ hp]
  exact factor_eq n

end OMA.R_OeisA109074_conjecture_R1
