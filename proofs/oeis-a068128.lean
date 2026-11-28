import OMAStatements.S_oeis_a068128
import Mathlib

namespace A068128Proof

lemma digits_sum_eq_zero (t : ℕ) : (Nat.digits 10 t).sum = 0 → t = 0 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h
    by_contra ht
    have hpos : 0 < t := Nat.pos_of_ne_zero ht
    rw [Nat.digits_def' (by norm_num) hpos, List.sum_cons] at h
    have h1 : t % 10 = 0 := by omega
    have h2 : (Nat.digits 10 (t / 10)).sum = 0 := by omega
    have h3 := ih (t / 10) (by omega) h2
    omega

end A068128Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068128.main) := by
  intro h
  have h0 := h 0
  apply h0
  apply Set.Finite.subset (Set.finite_singleton 0)
  rintro t ⟨_, ht⟩
  have h1 : OMA.S_oeis_a068128.triangular 0 = 0 := by decide
  rw [h1] at ht
  exact A068128Proof.digits_sum_eq_zero t ht
