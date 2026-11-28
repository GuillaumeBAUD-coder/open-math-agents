import OMAStatements.S_oeis_a329479
import Mathlib.Algebra.BigOperators.Ring.Finset

-- Original Lean proof: @justusklocke-cloud.

namespace A329479Aux

open OMA.S_oeis_a329479

private abbrev State := ZMod 3 × ZMod 3

private def stp (s : State) (b : Bool) : State :=
  (1 * s.1 + bit b, 2 * s.2 + bit b)

private def run (l : List Bool) (s : State) : State :=
  (evalBits l 1 s.1, evalBits l 2 s.2)

private def G (n : ℕ) (s : State) : ℤ :=
  ∑ w : Fin n → Bool, if run (List.ofFn w) s = (0, 0) then 1 else 0

private lemma G_succ (n : ℕ) (s : State) :
    G (n + 1) s = G n (stp s true) + G n (stp s false) := by
  rw [← Fintype.sum_bool (fun b => G n (stp s b))]
  unfold G
  rw [← Fintype.sum_prod_type (fun p : Bool × (Fin n → Bool) =>
    if run (List.ofFn p.2) (stp s p.1) = (0, 0) then (1 : ℤ) else 0)]
  symm
  apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
  rintro ⟨b, w⟩
  change _ = if run (List.ofFn (Fin.cons b w)) s = (0, 0) then 1 else 0
  rw [List.ofFn_cons]
  rfl

private lemma cond_iff (l : List Bool) :
    (∀ x : ZMod 3, x * evalBits l x 1 = 0) ↔ run l (1, 1) = (0, 0) := by
  simp only [run, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨by simpa using h 1, (show ∀ e : ZMod 3, 2 * e = 0 → e = 0 by decide) _ (h 2)⟩
  · rintro ⟨h₁, h₂⟩ x
    rcases (show ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 by decide) x with rfl | rfl | rfl <;>
      simp [h₁, h₂]

private def paths : ℕ → State → State → ℤ
  | 0, s, t => if s = t then 1 else 0
  | k + 1, s, t => paths k (stp s true) t + paths k (stp s false) t

private lemma G_shift (n k : ℕ) (s : State) :
    G (n + k) s = ∑ t : State, paths k s t * G n t := by
  induction k generalizing s with
  | zero => simp [paths, ite_mul]
  | succ k ih =>
    change G (n + k + 1) s = _
    simp only [G_succ, ih, ← Finset.sum_add_distrib, paths, add_mul]

private lemma a_shift (n k : ℕ) :
    a (n + k + 1) = ∑ t : State, paths k (1, 1) t * G n t := by
  rw [← G_shift, a]
  simp_rw [G, cond_iff]

private lemma paths_recur : ∀ t : State,
    paths 8 (1, 1) t = 2 * paths 7 (1, 1) t + 2 * paths 6 (1, 1) t - 5 * paths 5 (1, 1) t -
      2 * paths 4 (1, 1) t + 10 * paths 3 (1, 1) t - 4 * paths 2 (1, 1) t -
      4 * paths 1 (1, 1) t + 8 * paths 0 (1, 1) t := by decide

theorem recurrence : type_of% @OMA.S_oeis_a329479.main := by
  intro n
  rw [a_shift n 8, a_shift n 7, a_shift n 6, a_shift n 5, a_shift n 4,
    a_shift n 3, a_shift n 2, a_shift n 1, a_shift n 0]
  simp only [Finset.mul_sum, ← mul_assoc, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← add_mul, ← sub_mul]
  exact Finset.sum_congr rfl fun t _ => congrArg (· * G n t) (paths_recur t)

end A329479Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a329479.main := A329479Aux.recurrence
