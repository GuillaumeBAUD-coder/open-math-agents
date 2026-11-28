import OMAStatements.S_oeis_a298793

/-!
Disproof of the A298793 statement. Barker's recurrence is claimed for n > 16, but his
generating function has a numerator of degree 18, so the order-16 recurrence sum at n = 18
equals the numerator coefficient -1, not 0 (with the listed data: a(18) = 54 while the
recurrence predicts 55). The two conjuncts of main already contradict each other at n = 18.
-/

namespace OMA.Helpers

theorem a298793_numerator_eighteen : OMA.S_oeis_a298793.numerator 18 = -1 := by decide

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298793.main) := by
  intro h
  have hgf := h.1 18
  have hrec := h.2 18 (by norm_num)
  simp only [OMA.S_oeis_a298793.lag, OMA.Helpers.a298793_numerator_eighteen] at hgf
  norm_num at hgf hrec
  linarith
