import OMAReductions.R_oeis_a247602_R1

/-! Witnesses for the first eleven instances of Sun's prime-count/totient equation. -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_oeis_a247602_R1.H1 := by
  intro n hn hN
  interval_cases n
  · exact ⟨3, by decide, by decide +kernel⟩
  · exact ⟨2, by decide, by decide +kernel⟩
  · exact ⟨1, by decide, by decide +kernel⟩
  · exact ⟨91, by decide, by decide +kernel⟩
  · exact ⟨6, by decide, by decide +kernel⟩
  · exact ⟨5, by decide, by decide +kernel⟩
  · exact ⟨1, by decide, by decide +kernel⟩
  · exact ⟨5, by decide, by decide +kernel⟩
  · exact ⟨1, by decide, by decide +kernel⟩
  · exact ⟨8041, by decide, by decide +kernel⟩
  · exact ⟨15870, by decide, by decide +kernel⟩
