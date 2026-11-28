import OMAStatements.S_oeis_a230260

-- Disproof: for n = 139 (2n = 278) every prime pair p + q = 278 has an even total binary weight,
-- checked by kernel computation with a structural popcount equal to the digit sum.
namespace OMA.A230260

def pc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, p => if p = 0 then 0 else p % 2 + pc f (p / 2)

lemma pc_eq (f p : ℕ) (hf : p ≤ f) : pc f p = (Nat.digits 2 p).sum := by
  induction f generalizing p with
  | zero => simp [pc, Nat.le_zero.mp hf]
  | succ f ih =>
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp [pc]
    · rw [pc, if_neg hp.ne', Nat.digits_def' (by norm_num) hp, List.sum_cons,
        ih _ (by omega)]

lemma check : ∀ p < 279, p.Prime → (278 - p).Prime → Even (pc 300 p + pc 300 (278 - p)) := by
  decide +kernel

end OMA.A230260

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a230260.main) := by
  intro h
  obtain ⟨p, q, hp, hq, hs, hodd⟩ := h 139 (by norm_num)
  have hq' : q = 278 - p := by omega
  subst hq'
  have := OMA.A230260.check p (by omega) hp hq
  rw [OMA.A230260.pc_eq 300 p (by omega), OMA.A230260.pc_eq 300 _ (by omega)] at this
  exact (Nat.not_even_iff_odd.mpr hodd) this

