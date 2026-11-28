import OMAStatements.S_oeis_a071282

-- First project proof of A071282: @dk8827.
-- Stream-period argument adapted from @senamakel and Medulla, A071284 (PR #7844).
-- Group tokens in blocks of n+2. Moving forward n+1 blocks preserves
-- the insertion rule and advances every inherited index by n*(n+1).
namespace Peirce071282

open OMA.S_oeis_a071282 hiding peirce
open OMA.S_oeis_a071282 renaming peirce → stream

private theorem lift_period (n : ℕ) (hn : 0 < n) (old : ℕ → Symbol)
    (shift : ∀ x, old (x + n * (n + 1)) = old x) (i : ℕ) :
    expandStream n old (i + (n + 1) * (n + 2)) = expandStream n old i := by
  have divShift := Nat.add_mul_div_right i (n + 1) (z := n + 2) (by omega)
  have remShift := Nat.add_mul_mod_self_right i (n + 1) (n + 2)
  have next (q : ℕ) : (q + (n + 1) + 1) * n = (q + 1) * n + n * (n + 1) := by ring
  have parity (q : ℕ) : (q + (n + 1) + 1) * n % 2 = (q + 1) * n % 2 := by
    rw [next, Nat.add_mod, Nat.even_iff.mp (Nat.even_mul_succ_self n)]
    simp
  have copied (q r : ℕ) : old ((q + (n + 1)) * n + r) = old (q * n + r) := by
    convert shift (q * n + r) using 2
    ring
  have last (q : ℕ) : old ((q + (n + 1) + 1) * n - 1) = old ((q + 1) * n - 1) := by
    have pos : 0 < (q + 1) * n := by positivity
    rw [next, show (q + 1) * n + n * (n + 1) - 1 = ((q + 1) * n - 1) + n * (n + 1) by omega, shift]
  simp only [expandStream, divShift, remShift, parity, copied, last]

private theorem stream_period : ∀ n i : ℕ, stream n (i + n * (n + 1)) = stream n i
  | 0, _ => rfl
  | 1, i => by simp [stream]
  | n + 2, i => lift_period (n+1) (by omega) _ (stream_period (n+1)) i

private theorem period : Function.Periodic (denominatorAt 3) 6 := by
  intro i
  unfold denominatorAt
  rw [show 2 * (i + 6) = 2*i + 3*(3+1) by omega, stream_period]

end Peirce071282

open OMA.S_oeis_a071282 in
theorem OMA.solution : type_of% @OMA.S_oeis_a071282.main := by
  intro i
  rw [← Peirce071282.period.map_mod_nat i]
  have table : ∀ j : Fin 6, denominatorAt 3 j = ([2, 3, 1, 3, 2, 3] : List ℕ)[j.val]! := by decide
  exact table ⟨i % 6, Nat.mod_lt _ (by decide)⟩
