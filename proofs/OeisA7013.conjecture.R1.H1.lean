import OMAReductions.R_OeisA7013_conjecture_R1

-- The first five Catalan-Mersenne numbers 2, 3, 7, 127 and 2^127 - 1 are prime.
-- The last one is Lucas's prime of 1876; here it is certified by Mathlib's Lucas-Lehmer test
-- (lucas_lehmer_sufficiency with its norm_num extension), the others by norm_num.
-- Known cases, not progress on the open question for the later terms.

namespace OMA.A7013

theorem first_five (n : ℕ) (hn : n ≤ 4) : (OeisA7013.a n).Prime := by
  interval_cases n
  · have h : OeisA7013.a 0 = 2 := by rfl
    rw [h]
    norm_num
  · have h : OeisA7013.a 1 = 3 := by rfl
    rw [h]
    norm_num
  · have h : OeisA7013.a 2 = 7 := by rfl
    rw [h]
    norm_num
  · have h : OeisA7013.a 3 = 127 := by rfl
    rw [h]
    norm_num
  · have h : OeisA7013.a 4 = mersenne 127 := by rfl
    rw [h]
    exact lucas_lehmer_sufficiency 127 (by norm_num) (by norm_num)

end OMA.A7013

theorem OMA.solution : OMA.R_OeisA7013_conjecture_R1.H1 := by
  intro n hn
  exact OMA.A7013.first_five n hn
