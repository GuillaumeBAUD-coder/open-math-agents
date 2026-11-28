import OMAStatements.S_oeis_a233637
import Mathlib

/-!
Transfer matrix on the nine rows `Fin 2 → Fin 3`. With `T f s = ∑ x, [BlockOK s x] f x`,
`E k = T^k 1` and `S L f` the sum of `f (last row)` over valid arrays with `L + 1` rows,
appending a row (`Fin.snoc`) gives `S (L + 1) f = S L (T f)`, hence `a (L + k) = S L (E k)`.
The identity `E 3 = 2 E 2 + 6 E 1` holds on every row (checked by `decide +kernel`), and
`a 1`, `a 2` are `sum9 (E 1)`, `sum9 (E 2)`.
-/

namespace R233637
open OMA.S_oeis_a233637

abbrev Row := Fin 2 → Fin 3

def sum9 (h : Row → ℕ) : ℕ :=
  h ![0, 0] + h ![0, 1] + h ![0, 2] + (h ![1, 0] + h ![1, 1] + h ![1, 2]) +
    (h ![2, 0] + h ![2, 1] + h ![2, 2])

theorem sum9_eq (h : Row → ℕ) : ∑ x : Row, h x = sum9 h := by
  have e : ∀ u v : Fin 3, (piFinTwoEquiv fun _ => Fin 3).symm (u, v) = ![u, v] := by
    intro u v
    funext i
    fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => Fin 3).symm.sum_comp h, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, e] <;> rfl

def T (f : Row → ℕ) (s : Row) : ℕ := sum9 (fun x => if BlockOK s x then f x else 0)

def E : ℕ → Row → ℕ
  | 0 => fun _ => 1
  | k + 1 => T (E k)

def S (L : ℕ) (f : Row → ℕ) : ℕ :=
  ∑ A : Fin (L + 1) → Row,
    if (∀ i : Fin L, BlockOK (A i.castSucc) (A i.succ)) then f (A (Fin.last L)) else 0

theorem a_eq (n : ℕ) : a n = S n (fun _ => 1) := by
  rw [a, Fintype.card_subtype, Finset.card_filter] <;> rfl

theorem valid_snoc {L : ℕ} (w : Fin (L + 1) → Row) (x : Row) :
    (∀ i : Fin (L + 1), BlockOK (Fin.snoc (α := fun _ => Row) w x i.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ)) ↔
      (∀ i : Fin L, BlockOK (w i.castSucc) (w i.succ)) ∧ BlockOK (w (Fin.last L)) x := by
  have h1 : ∀ i : Fin L, Fin.snoc (α := fun _ => Row) w x i.castSucc.castSucc = w i.castSucc :=
    fun i => by rw [Fin.snoc_castSucc]
  have h2 : ∀ i : Fin L, Fin.snoc (α := fun _ => Row) w x i.castSucc.succ = w i.succ :=
    fun i => by rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  have h3 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).castSucc = w (Fin.last L) := by
    rw [Fin.snoc_castSucc]
  have h4 : Fin.snoc (α := fun _ => Row) w x (Fin.last L).succ = x := Fin.snoc_last ..
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := h i.castSucc
      rwa [h1, h2] at hi
    · have hl := h (Fin.last L)
      rwa [h3, h4] at hl
  · rintro ⟨hw, hx⟩ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [h1, h2]
      exact hw j
    · rw [h3, h4]
      exact hx

theorem step_w {L : ℕ} (w : Fin (L + 1) → Row) (f : Row → ℕ) :
    (∑ x : Row, if (∀ i : Fin (L + 1), BlockOK (Fin.snoc (α := fun _ => Row) w x i.castSucc)
        (Fin.snoc (α := fun _ => Row) w x i.succ))
      then f (Fin.snoc (α := fun _ => Row) w x (Fin.last (L + 1))) else 0) =
    if (∀ i : Fin L, BlockOK (w i.castSucc) (w i.succ)) then T f (w (Fin.last L)) else 0 := by
  rw [T, ← sum9_eq]
  by_cases hw : ∀ i : Fin L, BlockOK (w i.castSucc) (w i.succ)
  · rw [if_pos hw]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : BlockOK (w (Fin.last L)) x
    · rw [if_pos ((valid_snoc w x).2 ⟨hw, hx⟩), if_pos hx, Fin.snoc_last]
    · rw [if_neg (fun h => hx ((valid_snoc w x).1 h).2), if_neg hx]
  · rw [if_neg hw]
    exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hw ((valid_snoc w x).1 h).1))

theorem pull (L : ℕ) (f : Row → ℕ) : S (L + 1) f = S L (T f) := by
  have he : S (L + 1) f = ∑ p : Row × (Fin (L + 1) → Row),
      if (∀ i : Fin (L + 1), BlockOK (Fin.snoc (α := fun _ => Row) p.2 p.1 i.castSucc)
        (Fin.snoc (α := fun _ => Row) p.2 p.1 i.succ))
      then f (Fin.snoc (α := fun _ => Row) p.2 p.1 (Fin.last (L + 1))) else 0 :=
    (Equiv.sum_comp (Fin.snocEquiv fun _ => Row)
      (fun A : Fin (L + 1 + 1) → Row =>
        if (∀ i : Fin (L + 1), BlockOK (A i.castSucc) (A i.succ))
        then f (A (Fin.last (L + 1))) else 0)).symm
  rw [he, Fintype.sum_prod_type, Finset.sum_comm]
  unfold S
  exact Finset.sum_congr rfl (fun w _ => step_w w f)

theorem iter (k : ℕ) : ∀ L, S (L + k) (fun _ => 1) = S L (E k) := by
  induction k with
  | zero => intro L; rfl
  | succ k ih =>
    intro L
    rw [show L + (k + 1) = L + 1 + k by omega, ih (L + 1)]
    exact pull L (E k)

theorem a_S (L k : ℕ) : a (L + k) = S L (E k) :=
  (a_eq _).trans (iter k L)

theorem ident (s : Row) : E 3 s = 2 * E 2 s + 6 * E 1 s := by
  obtain ⟨u, v, rfl⟩ : ∃ u v : Fin 3, s = ![u, v] :=
    ⟨s 0, s 1, by funext i; fin_cases i <;> rfl⟩
  revert u v
  decide +kernel

theorem rec_S (L : ℕ) : S L (E 3) = 2 * S L (E 2) + 6 * S L (E 1) := by
  unfold S
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases hA : ∀ i : Fin L, BlockOK (A i.castSucc) (A i.succ)
  · simp only [if_pos hA]
    exact ident _
  · simp only [if_neg hA, mul_zero, add_zero]

theorem S0 (f : Row → ℕ) : S 0 f = sum9 f := by
  rw [← sum9_eq, ← (Equiv.funUnique (Fin 1) Row).sum_comp f]
  unfold S
  refine Fintype.sum_congr _ _ (fun A => ?_)
  have h0 : ∀ i : Fin 0, BlockOK (A i.castSucc) (A i.succ) := fun i => Fin.elim0 i
  exact (if_pos h0).trans rfl

theorem main' : a 1 = 24 ∧ a 2 = 90 ∧
    ∀ n : ℕ, 3 ≤ n → a n = 2 * a (n - 1) + 6 * a (n - 2) := by
  refine ⟨?_, ?_, fun n hn => ?_⟩
  · rw [show a 1 = S 0 (E 1) from a_S 0 1, S0]
    decide +kernel
  · rw [show a 2 = S 0 (E 2) from a_S 0 2, S0]
    decide +kernel
  · obtain ⟨L, rfl⟩ : ∃ L, n = L + 3 := ⟨n - 3, by omega⟩
    rw [show L + 3 - 1 = L + 2 by omega, show L + 3 - 2 = L + 1 by omega, a_S L 3, a_S L 2,
      a_S L 1]
    exact rec_S L

end R233637

theorem OMA.solution : type_of% @OMA.S_oeis_a233637.main := R233637.main'
