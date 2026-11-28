import OMAReductions.R_oeis_a231725_R1
import Mathlib

set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_oeis_a231725_R1.H1 := by
  intro n h hn
  interval_cases n
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨4, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨10, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨6, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨4, ?_⟩; norm_num
  · refine ⟨5, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨5, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨4, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨8, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨4, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨4, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨6, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨12, ?_⟩; norm_num
  · refine ⟨5, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨8, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨4, ?_⟩; norm_num
  · refine ⟨5, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨11, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨6, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨4, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨4, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨5, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨4, ?_⟩; norm_num
  · refine ⟨1, ?_⟩; norm_num
  · refine ⟨22, ?_⟩; norm_num
  · refine ⟨3, ?_⟩; norm_num
  · refine ⟨2, ?_⟩; norm_num