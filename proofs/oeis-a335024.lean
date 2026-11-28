import OMAStatements.S_oeis_a335024

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem harmonicRatioAt624 : OMA.S_oeis_a335024.a 624 ≠ 1 := by
  decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a335024.main) := by
  intro h
  have h624 : OMA.S_oeis_a335024.a 624 = 1 :=
    (h.1 624 (by decide)).2 ⟨5, 4, by decide, by decide, by decide, by decide⟩
  exact harmonicRatioAt624 h624
