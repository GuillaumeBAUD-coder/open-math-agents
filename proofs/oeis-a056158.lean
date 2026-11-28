import OMAStatements.S_oeis_a056158
import Mathlib.Tactic.Ring

namespace OMA.P_oeis_a056158

open OMA.S_oeis_a056158

theorem prove_main : ∀ k : ℕ,
    let n := (k : ℤ) + 6
    fromThree (k + 3) + (n - 5) * fromThree (k + 2) +
      (-2 * n + 9) * fromThree (k + 1) + (n - 5) * fromThree k = 0 := by
  intro k
  simp only [fromThree]
  push_cast
  ring

end OMA.P_oeis_a056158

theorem OMA.solution : type_of% @OMA.S_oeis_a056158.main :=
  OMA.P_oeis_a056158.prove_main
