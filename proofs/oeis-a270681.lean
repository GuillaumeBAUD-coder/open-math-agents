import OMAStatements.S_oeis_a270681

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270681.main) := by
  rintro ⟨_, heven, hodd, hrec, _⟩
  have h6 := hrec 6 (by decide)
  have v6 : OMA.S_oeis_a270681.a 6 = 60 := heven 6 (by decide) (by decide)
  have v5 : (OMA.S_oeis_a270681.a 5 : ℤ) = 52 := by
    have := hodd 5 (by decide) (by decide); norm_num at this; exact this
  have v4 : OMA.S_oeis_a270681.a 4 = 32 := heven 4 (by decide) (by decide)
  have v3 : (OMA.S_oeis_a270681.a 3 : ℤ) = 24 := by
    have := hodd 3 (by decide) (by decide); norm_num at this; exact this
  have v2 : OMA.S_oeis_a270681.a 2 = 12 := heven 2 (by decide) (by decide)
  have v1 : OMA.S_oeis_a270681.a 1 = 5 := by decide
  norm_num [v6, v5, v4, v3, v2, v1] at h6
