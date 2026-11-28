import OMAStatements.S_oeis_a375516

open OMA.S_oeis_a375516

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a375516.main) := by
  intro h
  have he : (partialSum 10).den % 10000 = 5200 := by decide +kernel
  have hc := h 10 (by decide)
  rw [he] at hc
  norm_num at hc