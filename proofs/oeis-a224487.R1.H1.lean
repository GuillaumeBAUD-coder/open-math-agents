import OMAReductions.R_oeis_a224487_R1

/-!
Proof of `OMA.R_oeis_a224487_R1.H1`.
For n = 2, 3, 4, 5, 6 take b = 2, 4, 4, 6, 10 (the OEIS values of a(n)). Then
S n b = 3, 37, 229, 7207, 853211, which are prime, and F(n) < b < F(n+4) holds.
-/

open OMA.S_oeis_a224487 in
theorem OMA.solution : OMA.R_oeis_a224487_R1.H1 := by
  intro n hn1 hn6
  interval_cases n
  · refine ⟨2, by decide, by decide, ?_⟩
    rw [show S 2 2 = 3 from rfl]
    norm_num
  · refine ⟨4, by decide, by decide, ?_⟩
    rw [show S 3 4 = 37 from rfl]
    norm_num
  · refine ⟨4, by decide, by decide, ?_⟩
    rw [show S 4 4 = 229 from rfl]
    norm_num
  · refine ⟨6, by decide, by decide, ?_⟩
    rw [show S 5 6 = 7207 from rfl]
    norm_num
  · refine ⟨10, by decide, by decide, ?_⟩
    rw [show S 6 10 = 853211 from rfl]
    norm_num
