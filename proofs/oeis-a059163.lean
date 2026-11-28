import OMAStatements.S_oeis_a059163

-- Proof of the statement in #27478 (statement by @ivillar). Credit for the proof: @bnb9001
-- With h = A001511(k), the three inner phrases of W'3{2,2}* sum to 2^(h+1), 2^(h+2), 2^(h+1).

namespace OMA_OEIS_A059163_Proof

open OMA.S_oeis_a059163

theorem stmt' : ∀ n : ℕ, a n = 2 ^ (1 + A059129 n) := by
  intro n
  have hr : 1 ≤ ruler (n / 3 + 1) := by unfold ruler; omega
  obtain ⟨h, hh⟩ : ∃ h, ruler (n / 3 + 1) = h + 1 := ⟨ruler (n / 3 + 1) - 1, by omega⟩
  unfold a A059129 element' element phrase
  rw [hh]
  have h3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with e | e | e <;>
    simp [e, pow_succ] <;> ring

end OMA_OEIS_A059163_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a059163.main := OMA_OEIS_A059163_Proof.stmt'
