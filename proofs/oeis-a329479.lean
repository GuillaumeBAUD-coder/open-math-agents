import OMAStatements.S_oeis_a329479
import Mathlib

namespace A329479Aux

def stp (s : ZMod 3 × ZMod 3) (b : Bool) : ZMod 3 × ZMod 3 :=
  (1 * s.1 + OMA.S_oeis_a329479.bit b, 2 * s.2 + OMA.S_oeis_a329479.bit b)

def run (l : List Bool) (s : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (OMA.S_oeis_a329479.evalBits l 1 s.1, OMA.S_oeis_a329479.evalBits l 2 s.2)

lemma run_cons (b : Bool) (l : List Bool) (s : ZMod 3 × ZMod 3) :
    run (b :: l) s = run l (stp s b) := rfl

def G (n : ℕ) (s : ZMod 3 × ZMod 3) : ℤ :=
  ∑ w : Fin n → Bool, if run (List.ofFn w) s = (0, 0) then 1 else 0

lemma G_succ (n : ℕ) (s : ZMod 3 × ZMod 3) :
    G (n + 1) s = G n (stp s true) + G n (stp s false) := by
  unfold G
  have h1 : (∑ w : Fin (n + 1) → Bool, if run (List.ofFn w) s = (0, 0) then (1 : ℤ) else 0)
      = ∑ p : Bool × (Fin n → Bool),
          if run (List.ofFn p.2) (stp s p.1) = (0, 0) then (1 : ℤ) else 0 := by
    symm
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
    intro p
    have e : (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) p = Fin.cons p.1 p.2 := rfl
    rw [e, List.ofFn_cons, run_cons]
  have h2 : (∑ p : Bool × (Fin n → Bool),
        if run (List.ofFn p.2) (stp s p.1) = (0, 0) then (1 : ℤ) else 0)
      = (∑ w : Fin n → Bool, if run (List.ofFn w) (stp s true) = (0, 0) then (1 : ℤ) else 0)
        + ∑ w : Fin n → Bool, if run (List.ofFn w) (stp s false) = (0, 0) then (1 : ℤ) else 0 :=
    (Fintype.sum_prod_type _).trans (Fintype.sum_bool _)
  exact h1.trans h2

lemma cond_iff (l : List Bool) :
    (∀ x : ZMod 3, x * OMA.S_oeis_a329479.evalBits l x 1 = 0) ↔ run l (1, 1) = (0, 0) := by
  have h2 : ∀ e : ZMod 3, 2 * e = 0 → e = 0 := by decide
  have h3 : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  constructor
  · intro h
    have a1 := h 1
    have a2 := h 2
    rw [one_mul] at a1
    exact Prod.ext a1 (h2 _ a2)
  · intro h x
    have b1 : OMA.S_oeis_a329479.evalBits l 1 1 = 0 := congrArg Prod.fst h
    have b2 : OMA.S_oeis_a329479.evalBits l 2 1 = 0 := congrArg Prod.snd h
    rcases h3 x with rfl | rfl | rfl
    · rw [zero_mul]
    · rw [one_mul]; exact b1
    · rw [b2, mul_zero]

lemma a_eq (n : ℕ) : OMA.S_oeis_a329479.a (n + 1) = G n (1, 1) := by
  show (∑ w : Fin n → Bool,
      if ∀ x : ZMod 3, x * OMA.S_oeis_a329479.evalBits (List.ofFn w) x 1 = 0 then (1 : ℤ) else 0)
    = G n (1, 1)
  unfold G
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : run (List.ofFn w) (1, 1) = (0, 0)
  · rw [if_pos h, if_pos ((cond_iff _).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((cond_iff _).mp h'))]

lemma gs_00 (m : ℕ) : G (m + 1) (0, 0) = G m (1, 1) + G m (0, 0) := by
  have h1 : stp (0, 0) true = (1, 1) := by decide
  have h0 : stp (0, 0) false = (0, 0) := by decide
  rw [G_succ, h1, h0]

lemma gs_01 (m : ℕ) : G (m + 1) (0, 1) = G m (1, 0) + G m (0, 2) := by
  have h1 : stp (0, 1) true = (1, 0) := by decide
  have h0 : stp (0, 1) false = (0, 2) := by decide
  rw [G_succ, h1, h0]

lemma gs_02 (m : ℕ) : G (m + 1) (0, 2) = G m (1, 2) + G m (0, 1) := by
  have h1 : stp (0, 2) true = (1, 2) := by decide
  have h0 : stp (0, 2) false = (0, 1) := by decide
  rw [G_succ, h1, h0]

lemma gs_10 (m : ℕ) : G (m + 1) (1, 0) = G m (2, 1) + G m (1, 0) := by
  have h1 : stp (1, 0) true = (2, 1) := by decide
  have h0 : stp (1, 0) false = (1, 0) := by decide
  rw [G_succ, h1, h0]

lemma gs_11 (m : ℕ) : G (m + 1) (1, 1) = G m (2, 0) + G m (1, 2) := by
  have h1 : stp (1, 1) true = (2, 0) := by decide
  have h0 : stp (1, 1) false = (1, 2) := by decide
  rw [G_succ, h1, h0]

lemma gs_12 (m : ℕ) : G (m + 1) (1, 2) = G m (2, 2) + G m (1, 1) := by
  have h1 : stp (1, 2) true = (2, 2) := by decide
  have h0 : stp (1, 2) false = (1, 1) := by decide
  rw [G_succ, h1, h0]

lemma gs_20 (m : ℕ) : G (m + 1) (2, 0) = G m (0, 1) + G m (2, 0) := by
  have h1 : stp (2, 0) true = (0, 1) := by decide
  have h0 : stp (2, 0) false = (2, 0) := by decide
  rw [G_succ, h1, h0]

lemma gs_21 (m : ℕ) : G (m + 1) (2, 1) = G m (0, 0) + G m (2, 2) := by
  have h1 : stp (2, 1) true = (0, 0) := by decide
  have h0 : stp (2, 1) false = (2, 2) := by decide
  rw [G_succ, h1, h0]

lemma gs_22 (m : ℕ) : G (m + 1) (2, 2) = G m (0, 2) + G m (2, 1) := by
  have h1 : stp (2, 2) true = (0, 2) := by decide
  have h0 : stp (2, 2) false = (2, 1) := by decide
  rw [G_succ, h1, h0]

lemma T1 (m : ℕ) : G (m + 1) (1, 1) = G m (1, 2) + G m (2, 0) := by
  rw [gs_11 m]
  ring

lemma T2 (m : ℕ) : G (m + 2) (1, 1) = G m (0, 1) + G m (1, 1) + G m (2, 0) + G m (2, 2) := by
  have h : G (m + 2) (1, 1) = G (m + 1) (1, 2) + G (m + 1) (2, 0) := T1 (m + 1)
  rw [h, gs_12 m, gs_20 m]
  ring

lemma T3 (m : ℕ) : G (m + 3) (1, 1) = G m (0, 1) + 2 * G m (0, 2) + G m (1, 0) + G m (1, 2) + 2 * G m (2, 0) + G m (2, 1) := by
  have h : G (m + 3) (1, 1) = G (m + 1) (0, 1) + G (m + 1) (1, 1) + G (m + 1) (2, 0) + G (m + 1) (2, 2) := T2 (m + 1)
  rw [h, gs_01 m, gs_11 m, gs_20 m, gs_22 m]
  ring

lemma T4 (m : ℕ) : G (m + 4) (1, 1) = G m (0, 0) + 4 * G m (0, 1) + G m (0, 2) + 2 * G m (1, 0) + G m (1, 1) + 2 * G m (1, 2) + 2 * G m (2, 0) + G m (2, 1) + 2 * G m (2, 2) := by
  have h : G (m + 4) (1, 1) = G (m + 1) (0, 1) + 2 * G (m + 1) (0, 2) + G (m + 1) (1, 0) + G (m + 1) (1, 2) + 2 * G (m + 1) (2, 0) + G (m + 1) (2, 1) := T3 (m + 1)
  rw [h, gs_01 m, gs_02 m, gs_10 m, gs_12 m, gs_20 m, gs_21 m]
  ring

lemma T5 (m : ℕ) : G (m + 5) (1, 1) = 2 * G m (0, 0) + 3 * G m (0, 1) + 6 * G m (0, 2) + 6 * G m (1, 0) + 3 * G m (1, 1) + 2 * G m (1, 2) + 3 * G m (2, 0) + 4 * G m (2, 1) + 3 * G m (2, 2) := by
  have h : G (m + 5) (1, 1) = G (m + 1) (0, 0) + 4 * G (m + 1) (0, 1) + G (m + 1) (0, 2) + 2 * G (m + 1) (1, 0) + G (m + 1) (1, 1) + 2 * G (m + 1) (1, 2) + 2 * G (m + 1) (2, 0) + G (m + 1) (2, 1) + 2 * G (m + 1) (2, 2) := T4 (m + 1)
  rw [h, gs_00 m, gs_01 m, gs_02 m, gs_10 m, gs_11 m, gs_12 m, gs_20 m, gs_21 m, gs_22 m]
  ring

lemma T6 (m : ℕ) : G (m + 6) (1, 1) = 6 * G m (0, 0) + 9 * G m (0, 1) + 6 * G m (0, 2) + 9 * G m (1, 0) + 4 * G m (1, 1) + 9 * G m (1, 2) + 6 * G m (2, 0) + 9 * G m (2, 1) + 6 * G m (2, 2) := by
  have h : G (m + 6) (1, 1) = 2 * G (m + 1) (0, 0) + 3 * G (m + 1) (0, 1) + 6 * G (m + 1) (0, 2) + 6 * G (m + 1) (1, 0) + 3 * G (m + 1) (1, 1) + 2 * G (m + 1) (1, 2) + 3 * G (m + 1) (2, 0) + 4 * G (m + 1) (2, 1) + 3 * G (m + 1) (2, 2) := T5 (m + 1)
  rw [h, gs_00 m, gs_01 m, gs_02 m, gs_10 m, gs_11 m, gs_12 m, gs_20 m, gs_21 m, gs_22 m]
  ring

lemma T7 (m : ℕ) : G (m + 7) (1, 1) = 15 * G m (0, 0) + 12 * G m (0, 1) + 15 * G m (0, 2) + 18 * G m (1, 0) + 15 * G m (1, 1) + 10 * G m (1, 2) + 10 * G m (2, 0) + 15 * G m (2, 1) + 18 * G m (2, 2) := by
  have h : G (m + 7) (1, 1) = 6 * G (m + 1) (0, 0) + 9 * G (m + 1) (0, 1) + 6 * G (m + 1) (0, 2) + 9 * G (m + 1) (1, 0) + 4 * G (m + 1) (1, 1) + 9 * G (m + 1) (1, 2) + 6 * G (m + 1) (2, 0) + 9 * G (m + 1) (2, 1) + 6 * G (m + 1) (2, 2) := T6 (m + 1)
  rw [h, gs_00 m, gs_01 m, gs_02 m, gs_10 m, gs_11 m, gs_12 m, gs_20 m, gs_21 m, gs_22 m]
  ring

lemma T8 (m : ℕ) : G (m + 8) (1, 1) = 30 * G m (0, 0) + 25 * G m (0, 1) + 30 * G m (0, 2) + 30 * G m (1, 0) + 25 * G m (1, 1) + 30 * G m (1, 2) + 25 * G m (2, 0) + 36 * G m (2, 1) + 25 * G m (2, 2) := by
  have h : G (m + 8) (1, 1) = 15 * G (m + 1) (0, 0) + 12 * G (m + 1) (0, 1) + 15 * G (m + 1) (0, 2) + 18 * G (m + 1) (1, 0) + 15 * G (m + 1) (1, 1) + 10 * G (m + 1) (1, 2) + 10 * G (m + 1) (2, 0) + 15 * G (m + 1) (2, 1) + 18 * G (m + 1) (2, 2) := T7 (m + 1)
  rw [h, gs_00 m, gs_01 m, gs_02 m, gs_10 m, gs_11 m, gs_12 m, gs_20 m, gs_21 m, gs_22 m]
  ring

end A329479Aux

open A329479Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a329479.main := by
  intro n
  have e1 : OMA.S_oeis_a329479.a (n + 1) = G n (1, 1) := a_eq n
  have e2 : OMA.S_oeis_a329479.a (n + 2) = G (n + 1) (1, 1) := a_eq (n + 1)
  have e3 : OMA.S_oeis_a329479.a (n + 3) = G (n + 2) (1, 1) := a_eq (n + 2)
  have e4 : OMA.S_oeis_a329479.a (n + 4) = G (n + 3) (1, 1) := a_eq (n + 3)
  have e5 : OMA.S_oeis_a329479.a (n + 5) = G (n + 4) (1, 1) := a_eq (n + 4)
  have e6 : OMA.S_oeis_a329479.a (n + 6) = G (n + 5) (1, 1) := a_eq (n + 5)
  have e7 : OMA.S_oeis_a329479.a (n + 7) = G (n + 6) (1, 1) := a_eq (n + 6)
  have e8 : OMA.S_oeis_a329479.a (n + 8) = G (n + 7) (1, 1) := a_eq (n + 7)
  have e9 : OMA.S_oeis_a329479.a (n + 9) = G (n + 8) (1, 1) := a_eq (n + 8)
  rw [e9, e8, e7, e6, e5, e4, e3, e2, e1, T8 n, T7 n, T6 n, T5 n, T4 n, T3 n, T2 n, T1 n]
  ring
