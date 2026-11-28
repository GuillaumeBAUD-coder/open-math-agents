import OMAStatements.S_oeis_a288473

-- Proof of the statement in #22810 (statement by @etaubman). Credit for the proof: @bnb9001
-- scan parses words into the prefix code 00, 01, 1 and maps tokens to whole tokens
-- (00 -> 01 01, 01 -> 00 1 1, 1 -> 01 1), so it is a morphism; the token lengths satisfy a linear
-- system whose characteristic polynomial x^3 - x^2 - 4x + 2 gives the recurrence.

namespace OMA_OEIS_A288473_Proof

open OMA.S_oeis_a288473

/-- the tokens `00`, `01`, `1` (a complete prefix code) -/
def img : Fin 3 → List Bool
  | 0 => [false, false]
  | 1 => [false, true]
  | 2 => [true]

/-- `scan` acts on tokens as the morphism `A -> BB`, `B -> ACC`, `C -> BC` -/
def sig : Fin 3 → List (Fin 3)
  | 0 => [1, 1]
  | 1 => [0, 2, 2]
  | 2 => [1, 2]

def flat (ts : List (Fin 3)) : List Bool := ts.flatMap img

def F (l : List (Fin 3)) : List (Fin 3) := l.flatMap sig

theorem flat_cons (t : Fin 3) (ts : List (Fin 3)) : flat (t :: ts) = img t ++ flat ts := by
  simp [flat]

theorem flat_append (a b : List (Fin 3)) : flat (a ++ b) = flat a ++ flat b := by
  simp [flat]

theorem scan_flat : ∀ ts : List (Fin 3), scan (flat ts) = flat (F ts) := by
  intro ts
  induction ts with
  | nil => simp [flat, F, scan]
  | cons t ts ih =>
    have hF : F (t :: ts) = sig t ++ F ts := by simp [F]
    rw [hF, flat_append, flat_cons]
    match t with
    | 0 =>
      show scan (false :: false :: flat ts) = _
      rw [scan, ih]; rfl
    | 1 =>
      show scan (false :: true :: flat ts) = _
      rw [scan, ih]; rfl
    | 2 =>
      show scan (true :: flat ts) = _
      rw [scan, ih]; rfl

theorem word_eq (n : ℕ) : word n = flat (F^[n] [0]) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← scan_flat, ← ih]; rfl

theorem F_append (a b : List (Fin 3)) : F (a ++ b) = F a ++ F b := by simp [F]

theorem iter_append (n : ℕ) : ∀ a b : List (Fin 3), F^[n] (a ++ b) = F^[n] a ++ F^[n] b := by
  induction n with
  | zero => intro a b; rfl
  | succ n ih => intro a b; rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, F_append, ih]

theorem iter_nil (n : ℕ) : F^[n] [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

def L (n : ℕ) (t : Fin 3) : ℕ := (flat (F^[n] [t])).length

theorem L_succ (n : ℕ) (t : Fin 3) : L (n + 1) t = ((sig t).map (L n)).sum := by
  unfold L
  rw [Function.iterate_succ_apply]
  have hF : F [t] = sig t := by simp [F]
  rw [hF]
  generalize sig t = l
  induction l with
  | nil => simp [flat, iter_nil]
  | cons s l ih =>
    rw [show s :: l = [s] ++ l from rfl, iter_append, flat_append, List.length_append, ih]
    simp

theorem rec3 (n : ℕ) : L (n + 3) 0 + 2 * L n 0 = L (n + 2) 0 + 4 * L (n + 1) 0 := by
  have a1 : L (n + 3) 0 = L (n + 2) 1 + L (n + 2) 1 := by
    rw [L_succ (n + 2) 0]; simp [sig]
  have a2 : L (n + 2) 1 = L (n + 1) 0 + (L (n + 1) 2 + L (n + 1) 2) := by
    rw [L_succ (n + 1) 1]; simp [sig]
  have a3 : L (n + 1) 2 = L n 1 + L n 2 := by
    rw [L_succ n 2]; simp [sig]
  have b1 : L (n + 2) 0 = L (n + 1) 1 + L (n + 1) 1 := by
    rw [L_succ (n + 1) 0]; simp [sig]
  have b2 : L (n + 1) 1 = L n 0 + (L n 2 + L n 2) := by
    rw [L_succ n 1]; simp [sig]
  have c1 : L (n + 1) 0 = L n 1 + L n 1 := by
    rw [L_succ n 0]; simp [sig]
  omega

theorem L0 : L 0 0 = 2 := rfl
theorem L1 : L 1 0 = 4 := by decide
theorem L2 : L 2 0 = 8 := by decide

theorem stmt' : ∀ n : ℕ, (word n).length = a288476 n := by
  intro n
  rw [word_eq]
  show L n 0 = a288476 n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => exact L1
    | 2, _ => exact L2
    | (n + 3), ih =>
      show L (n + 3) 0 = a288476 (n + 2) + 4 * a288476 (n + 1) - 2 * a288476 n
      rw [← ih (n + 2) (by omega), ← ih (n + 1) (by omega), ← ih n (by omega)]
      have := rec3 n
      omega

end OMA_OEIS_A288473_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a288473.main := OMA_OEIS_A288473_Proof.stmt'
