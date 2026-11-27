import OMAReductions.R_OeisA109074_conjecture_R1

/-! # Vertically symmetric alternating-sign matrices and the symplectic dimension formula
Credit: @shivareddy42.
Okada, "Enumeration of symmetry classes of alternating sign matrices and characters
of classical groups" (2006), specializes the VSASM partition function to a symplectic
character. Its shifted weights, in increasing order, are 1, 2, 4, 5, ..., 3n-1.
H1 is this specialization at the identity with the Weyl denominator cleared.
H2 evaluates the two new numerator rows when the rank increases from 2n to 2n+2.
The denominator rows and the passage from these identities to the product formula
are proved below. -/

namespace OMA.R_OeisA109074_conjecture_R1_H2_R1

open Finset

private theorem denominator_row (j : ℕ) :
    (j+1) * (∏ i ∈ range j, ((j+1)-(i+1)) * ((j+1)+(i+1))) = (2*j+1).factorial := by
  calc
    _ = (j+1) * (∏ i ∈ range j, (j-i) * ((j+1+1)+i)) := by
      apply congrArg ((j+1) * ·)
      apply prod_congr rfl
      intro i _
      exact congrArg₂ Nat.mul (by omega) (by omega)
    _ = _ := by
      rw [prod_mul_distrib, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self,
        ← Nat.ascFactorial_eq_prod_range, ← mul_assoc, ← Nat.factorial_succ,
        Nat.factorial_mul_ascFactorial]
      congr 1
      omega

def H1 : Prop := ∀ n : ℕ,
  let I := Fin (2*n+1)
  let lineOK (v : I → Fin 3) :=
    let partialSum (k : ℕ) := ∑ j : I, if j.val < k then ((v j).val : ℤ) - 1 else 0
    partialSum (2*n+1) = 1 ∧ ∀ k : Fin (2*n+2), partialSum k.val = 0 ∨ partialSum k.val = 1
  let matrices : Set (I → I → Fin 3) := {M | (∀ i, lineOK (M i)) ∧
    (∀ j, lineOK fun i => M i j) ∧ ∀ i j, M i j = M i (Fin.rev j)}
  let alt (a : ℕ → ℕ) := ∏ j ∈ range (2*n),
    a j * ∏ i ∈ range j, (a j - a i) * (a j + a i)
  3^(n*(n-1)) * matrices.ncard * alt (fun j => j+1) = alt (fun j => j+1+j/2)

def H2 : Prop := ∀ n : ℕ,
  let a (j : ℕ) := j+1+j/2
  let row (j : ℕ) := a j * ∏ i ∈ range j, (a j - a i) * (a j + a i)
  2*(4*n+2) * (row (2*n) * row (2*n+1)) =
    3^(2*n) * (6*n+4).factorial * (2*n+1).factorial

theorem main : H1 → H2 → OMA.R_OeisA109074_conjecture_R1.H2 := by
  intro hs hr
  let a (j : ℕ) := j+1+j/2
  let row (j : ℕ) := a j * ∏ i ∈ range j, (a j - a i) * (a j + a i)
  let numer (n : ℕ) : ℚ := ∏ j ∈ range (2*n), (row j : ℚ)
  let denom (n : ℕ) : ℚ := ∏ j ∈ range (2*n), ((2*j+1).factorial : ℚ)
  let factor (k : ℕ) : ℚ := ((6*k+4).factorial : ℚ) * (2*k+1).factorial /
    (2 * (4*k+3).factorial * (4*k+2).factorial)
  have pos (k : ℕ) : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have step (n : ℕ) : (row (2*n) : ℚ) * row (2*n+1) =
      (3:ℚ)^(2*n) * factor n * (4*n+1).factorial * (4*n+3).factorial := by
    have h := hr n
    change 2*(4*n+2) * (row (2*n) * row (2*n+1)) = _ at h
    have hc : (2:ℚ)*(4*n+2) * ((row (2*n) : ℚ) * row (2*n+1)) =
        (3:ℚ)^(2*n) * (6*n+4).factorial * (2*n+1).factorial := by exact_mod_cast h
    have fac : ((4*n+2).factorial : ℚ) = (4*(n:ℚ)+2) * (4*n+1).factorial := by
      exact_mod_cast Nat.factorial_succ (4*n+1)
    calc
      _ = (3:ℚ)^(2*n) * (6*n+4).factorial * (2*n+1).factorial / (2*(4*n+2)) := by
        apply (eq_div_iff (by positivity)).mpr
        rwa [mul_comm]
      _ = _ := by
        dsimp only [factor]
        rw [fac]
        field_simp [fun k => (pos k).ne']
  have eval (n : ℕ) : numer n = (3:ℚ)^(n*(n-1)) *
      (∏ k ∈ range n, factor k) * denom n := by
    induction n with
    | zero => simp [numer, denom]
    | succ n ih =>
      have e : (n+1)*((n+1)-1) = n*(n-1)+2*n := by
        cases n <;> simp
        ring
      have index : 2*(n+1) = 2*n+1+1 := by omega
      have hn : numer (n+1) = numer n * ((row (2*n) : ℚ) * row (2*n+1)) := by
        simp only [numer, index, prod_range_succ, mul_assoc]
      have hd : denom (n+1) = denom n * ((4*n+1).factorial : ℚ) * (4*n+3).factorial := by
        simp only [denom, index, prod_range_succ, show 2*(2*n)+1 = 4*n+1 by omega,
          show 2*(2*n+1)+1 = 4*n+3 by omega]
      rw [hn, step, ih, hd, e, pow_add, prod_range_succ]
      ring
  intro n
  have h := hs n
  dsimp only at h ⊢
  simp_rw [denominator_row] at h
  have hd : 0 < denom n := Finset.prod_pos (fun j _ => pos (2*j+1))
  apply mul_left_cancel₀ (by positivity : (3:ℚ)^(n*(n-1)) ≠ 0)
  apply mul_right_cancel₀ hd.ne'
  change _ = (3:ℚ)^(n*(n-1)) * (∏ k ∈ range n, factor k) * denom n
  rw [← eval]
  dsimp only [denom, numer]
  exact_mod_cast h

end OMA.R_OeisA109074_conjecture_R1_H2_R1
