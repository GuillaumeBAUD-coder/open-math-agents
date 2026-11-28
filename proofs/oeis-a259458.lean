import OMAStatements.S_oeis_a259458
import Mathlib

namespace OMA.S_oeis_a259458

lemma rf_eq (c : ℕ) (n : ℕ) :
    rf ((c : ℚ) + 1) n * (c.factorial : ℚ) = ((n + c).factorial : ℚ) := by
  induction n with
  | zero => simp [rf]
  | succ n ih =>
    have h : rf ((c : ℚ) + 1) (n + 1) = rf ((c : ℚ) + 1) n * ((c : ℚ) + 1 + n) := by
      simp [rf, Finset.prod_range_succ]
    rw [h, mul_assoc, mul_comm _ (c.factorial : ℚ), ← mul_assoc, mul_comm (rf _ n), mul_assoc] at *
    have : ((n + 1 + c).factorial : ℚ) = ((n + c + 1 : ℕ) : ℚ) * ((n + c).factorial : ℚ) := by
      rw [show n + 1 + c = (n + c) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    rw [this, ← ih]; push_cast; ring

end OMA.S_oeis_a259458

theorem OMA.solution : type_of% @OMA.S_oeis_a259458.main := by
  unfold OMA.S_oeis_a259458.a
  congr 1
  funext n
  have e5 : OMA.S_oeis_a259458.rf 5 n = ((n+4).factorial : ℚ) / 24 := by
    have h := OMA.S_oeis_a259458.rf_eq 4 n
    have c1 : ((4:ℕ):ℚ) + 1 = 5 := by norm_num
    have c2 : ((Nat.factorial 4 : ℕ) : ℚ) = 24 := by norm_num [Nat.factorial]
    rw [c1, c2] at h
    rw [eq_div_iff (by norm_num)]; linarith
  have e3 : OMA.S_oeis_a259458.rf 3 n = ((n+2).factorial : ℚ) / 2 := by
    have h := OMA.S_oeis_a259458.rf_eq 2 n
    have c1 : ((2:ℕ):ℚ) + 1 = 3 := by norm_num
    have c2 : ((Nat.factorial 2 : ℕ) : ℚ) = 2 := by norm_num [Nat.factorial]
    rw [c1, c2] at h
    rw [eq_div_iff (by norm_num)]; linarith
  rw [e5, e3]
  have f4 : ((n+4).factorial : ℚ) = ((n:ℚ)+4)*((n:ℚ)+3)*((n+2).factorial : ℚ) := by
    rw [show n + 4 = (n+2)+1+1 by ring, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have f2 : ((n+2).factorial : ℚ) = ((n:ℚ)+2)*((n:ℚ)+1)*(n.factorial : ℚ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((n+2).factorial : ℚ) ≠ 0 := by positivity
  rw [f4, f2]
  field_simp
  ring
