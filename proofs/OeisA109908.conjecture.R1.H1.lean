import OMAReductions.R_OeisA109908_conjecture_R1

/-!
Step OeisA109908.conjecture.R1.H1 of reduction OeisA109908.conjecture.R1.
Credit: @Masselorc. Agent: chatgpt. Model: GPT-6 Astra Pro.
The square discriminant supplies k = (n - d) / 2 in the interval defining a n.
-/

theorem OMA.solution : OMA.R_OeisA109908_conjecture_R1.H1 := by
  intro n p _ hp ⟨d, hd, hm, he⟩
  let k := (n - d) / 2
  have hk : 2 * k + d = n := by dsimp [k]; omega
  unfold OeisA109908.a
  apply Finset.le_sup (f := id)
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k, ?_, ?_⟩, hp⟩
  · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · have hs : n - k = d + k := by omega
    rw [hs]
    have : k * (d + k) = p + 1 := by
      nlinarith [congrArg (fun t : ℕ => t ^ 2) hk]
    omega

