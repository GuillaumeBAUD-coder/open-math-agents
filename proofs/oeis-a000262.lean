import OMAStatements.S_oeis_a000262

/-! An independent proof of Peter Bala’s congruence via Francesca Aicardi’s
finite-sum formula. See also the standalone formalization in PR 6909. -/

namespace OMA.A000262Proof

open OMA.S_oeis_a000262

/-- Multiplication by the factorial turns a binomial coefficient into
the value of an integer polynomial, even when the upper index is small. -/
lemma weighted_choose {q x y : ℕ} (h : (x : ZMod q) = (y : ZMod q)) (j : ℕ) :
    (j.factorial : ZMod q) * (x.choose j : ZMod q) =
    (j.factorial : ZMod q) * (y.choose j : ZMod q) := by
  simpa only [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul] using congrArg (fun z => (descPochhammer (ZMod q) j).eval z) h

def summand (q x y j : ℕ) : ZMod q :=
  (j.factorial : ZMod q) * (x.choose j : ZMod q) * (y.choose j : ZMod q)

lemma summand_congr {q x y x' y' : ℕ}
    (hx : (x : ZMod q) = x') (hy : (y : ZMod q) = y') (j : ℕ) :
    summand q x y j = summand q x' y' j := by
  unfold summand
  rw [weighted_choose hx j]
  linear_combination (x'.choose j : ZMod q) * weighted_choose hy j

lemma expanded (q n b : ℕ) (hb : n+1 ≤ b) :
    (a (n+1) : ZMod q) = ∑ j ∈ Finset.range b, summand q n (n+1) j := by
  simp only [a, Nat.cast_sum, Nat.cast_mul, summand]
  apply Finset.sum_subset (Finset.range_mono hb)
  intro j _ hj
  have hlt : n < j := by simp only [Finset.mem_range] at hj; omega
  simp [Nat.choose_eq_zero_of_lt hlt]

end OMA.A000262Proof

open OMA.S_oeis_a000262 OMA.A000262Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a000262.main := by
  intro q hq n
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  cases n with
  | zero =>
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    rw [Nat.zero_add, expanded (r+1) r (r+1) le_rfl, Finset.sum_eq_single 0]
    · simp [summand, a]
    · intro j _ hj
      have h := weighted_choose (q := r+1) (x := r+1) (y := 0) (by simp) j
      simp [Nat.choose_eq_zero_of_lt (by omega : 0 < j)] at h
      unfold summand
      linear_combination ((r.choose j : ℕ) : ZMod (r+1)) * h
    · simp
  | succ n =>
    rw [show n+1+q=n+q+1 by omega, expanded q (n+q) (n+q+1) le_rfl,
      expanded q n (n+q+1) (by omega)]
    apply Finset.sum_congr rfl
    intro j _
    apply summand_congr <;> push_cast <;> simp
