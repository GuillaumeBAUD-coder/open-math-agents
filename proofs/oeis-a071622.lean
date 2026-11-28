import OMAStatements.S_oeis_a071622
import Mathlib.Tactic.Ring

namespace OMA.A071622

open OMA.S_oeis_a071622

-- Original refutation by @KoaOkano. The witness here splits into three dyadic blocks.
private def block (start : ℕ) : ℕ → ℤ
  | 0 => contribution (start + 1)
  | d + 1 => block start d + block (start + 2 ^ d) d

private theorem add_block (start d : ℕ) : a (start + 2 ^ d) = a start + block start d := by
  induction d generalizing start with
  | zero => simp [block, a]
  | succ d ih =>
    rw [show start + 2 ^ (d + 1) = start + 2 ^ d + 2 ^ d by ring,
      ih (start + 2 ^ d), ih start, block, add_assoc]

private theorem three_blocks (d e f : ℕ) :
    a (2 ^ d + 2 ^ e + 2 ^ f) = block 0 d + block (2 ^ d) e + block (2 ^ d + 2 ^ e) f := by
  rw [add_block (2 ^ d + 2 ^ e) f, add_block (2 ^ d) e]
  rw [show a (2 ^ d) = block 0 d by simpa [a] using add_block 0 d]

set_option maxHeartbeats 4000000 in
private theorem first : block 0 13 = 114 := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem second : block (2 ^ 13) 13 = 42 := by decide +kernel

set_option maxHeartbeats 4000000 in
private theorem third : block (2 ^ 13 + 2 ^ 13) 12 = -204 := by decide +kernel

theorem witness : a 20480 = -48 := (three_blocks 13 13 12).trans (by simp only [first, second, third]; decide)

end OMA.A071622

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071622.main) := by
  intro h
  have hb := h 20480 (by decide)
  rw [OMA.A071622.witness] at hb
  exact (not_lt_of_ge (sq_nonneg _)) (hb.trans_le (by norm_num))
