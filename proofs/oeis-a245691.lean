import OMAStatements.S_oeis_a245691
import Mathlib

/-!
# Decoding the second trajectory

Decode a multiple of three by dividing by three and taking one Collatz step.
Leave every other state unchanged. On states greater than one this decoding
intertwines the two updates, and six is the only state that decodes to one.
Consequently the sets of positive hitting times agree, as do their least elements.
-/

namespace OMA.S_oeis_a245691

/-- The Collatz state represented by a trajectory state. -/
def decode (x : ℕ) := if x % 3 = 0 then collatz (x/3) else x

/-- One update commutes with decoding. -/
lemma decode_step (x : ℕ) : decode (step x) = collatz (decode x) := by
  unfold step decode collatz
  split_ifs <;> omega

/-- No update from a state above one reaches zero or one. -/
lemma step_large (x : ℕ) (hx : 1 < x) : 1 < step x := by
  unfold step
  split <;> omega

/-- Decoding tracks every iterate after the first multiplication. -/
lemma track (n j : ℕ) (hn : 1 < n) :
    1 < step^[j] (3*n) ∧ decode (step^[j] (3*n)) = collatz^[j+1] n := by
  induction j with
  | zero => simp [decode]; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply' step, Function.iterate_succ_apply' collatz]
    exact ⟨step_large _ ih.1, (decode_step _).trans (congrArg collatz ih.2)⟩

end OMA.S_oeis_a245691

open OMA.S_oeis_a245691 in
theorem OMA.solution : type_of% @OMA.S_oeis_a245691.main := by
  intro n hn k
  suffices he : {j : ℕ | 1 ≤ j ∧ T n j = 6} = {j : ℕ | collatz^[j] n = 1} by rw [he]
  ext j
  cases j with
  | zero => simp; omega
  | succ j =>
    obtain ⟨hl, hd⟩ := track n j hn
    simp only [Set.mem_ofPred_eq, Nat.succ_le_succ_iff, Nat.zero_le, true_and, T, ← hd]
    unfold decode collatz
    split_ifs <;> omega
