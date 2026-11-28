import OMAStatements.S_oeis_a090528
import Mathlib.NumberTheory.Bertrand

/-! Bertrand's postulate supplies the witness from Weston Markham's comment
on A090527. See also Lien-Hung Su, *Prime Witnesses in a Floor-Quotient
Sequence* (2026), https://zenodo.org/records/23038248. -/

open OMA.S_oeis_a090528

theorem OMA.solution : type_of% @OMA.S_oeis_a090528.main := by
  classical
  intro i hi
  let n := i+1
  have hn : 2 ≤ n := by dsimp [n]; omega
  have size : 4 ≤ n^n := (show 4 ≤ n^2 by nlinarith).trans
    (Nat.pow_le_pow_right (by omega) hn)
  obtain ⟨p,hp,lower,upper⟩ := Nat.exists_prime_lt_and_le_two_mul (n^n/4) (by omega)
  have lo : 2 ≤ n^n/p := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
  have high : n^n/p < 4 := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
  have yes : ∃ p : ℕ, p.Prime ∧ (n^n/p).Prime := by
    refine ⟨p,hp,?_⟩
    rcases (show n^n/p = 2 ∨ n^n/p = 3 by omega) with h | h <;> rw [h] <;> decide
  change n^n / leastWitness n ≠ 0
  rw [leastWitness,dif_pos yes]
  exact (Nat.find_spec yes).2.ne_zero
