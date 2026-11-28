import OMAReductions.R_Green14_W_3_16_R2_H1_R1

-- Step Green14.W_3_16.R2.H1.R1.H1: hypothesis H1 of reduction Green14.W_3_16.R2.H1.R1
-- Credit: @Lenqth (Claude Code, claude-opus-5-5)

/-! An explicit palindromic 2-colouring of `[0, 231)` (bit `i` of the number below; `true` = the
colour without 3-term progressions, `false` = the colour without 16-term progressions), found
with a SAT solver (CaDiCaL) and checked by `decide +kernel`. Progressions fit in `[0, 231)`
only with `a < 231` and `d < 231`, which bounds the check. -/

namespace OMA.Green14W316H1

def M : Nat := 105415954105051622863246535537913902584431136677165610424602738688

def c (i : Nat) : Bool := M.testBit i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem key : ∀ b : Bool, ∀ a < 231, ∀ d < 231, 0 < d →
    a + ((if b then 16 else 3) - 1) * d < 231 →
    ∃ t < (if b then 16 else 3), c (a + t*d) = b := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sym : ∀ x < 231, c (231 - 1 - x) = c x := by
  decide +kernel

end OMA.Green14W316H1

theorem OMA.solution : OMA.R_Green14_W_3_16_R2_H1_R1.H1 := by
  refine ⟨OMA.Green14W316H1.c, ?_⟩
  show (∀ x < 231, OMA.Green14W316H1.c (231 - 1 - x) = OMA.Green14W316H1.c x) ∧
    ∀ (b : Bool) (a d : Nat), 0 < d → a + ((if b then 16 else 3) - 1) * d < 231 →
      ∃ t < (if b then 16 else 3), OMA.Green14W316H1.c (a + t*d) = b
  refine ⟨OMA.Green14W316H1.sym, fun b a d hd h => ?_⟩
  have hL : 2 ≤ (if b then 16 else 3) - 1 := by split_ifs <;> omega
  have hd' : d < 231 := by nlinarith
  exact OMA.Green14W316H1.key b a (by nlinarith) d hd' hd h
