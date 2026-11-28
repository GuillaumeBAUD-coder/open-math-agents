import OMAReductions.R_OeisA250131_conjecture_1_R1

/-!
In the tabulated range, every nonprime term is either 1 or has an earlier
nonunit term dividing it. Both alternatives exclude it from the sieve.
-/

open OeisA250131

private def checkIndex (n : ℕ) : Bool :=
  decide ((b n).Prime ∨ b n = 1) ||
    (List.range' 1 (n - 1)).any (fun k => decide (b k ≠ 1 ∧ b k ∣ b n))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem checked : (List.range' 1 79).all checkIndex = true := by
  decide +kernel

theorem OMA.solution : OMA.R_OeisA250131_conjecture_1_R1.H1 := by
  intro n upper survives
  change 1 ≤ n ∧ b n ≠ 1 ∧
    (∀ k, (1 ≤ k ∧ k < n ∧ b k ≠ 1) → ¬ b k ∣ b n) at survives
  have member : n ∈ List.range' 1 79 :=
    List.mem_range'_1.mpr ⟨survives.1, by omega⟩
  have test := List.all_eq_true.mp checked n member
  simp only [checkIndex, Bool.or_eq_true, decide_eq_true_eq] at test
  rcases test with (prime | one) | earlier
  · exact prime
  · exact (survives.2.1 one).elim
  · obtain ⟨k, hk, certificate⟩ := List.any_eq_true.mp earlier
    have interval := List.mem_range'_1.mp hk
    obtain ⟨nonunit, dvd⟩ := of_decide_eq_true certificate
    exact (survives.2.2 k ⟨interval.1, by omega, nonunit⟩ dvd).elim
