import OMAReductions.R_Erdos1013_erdos_1013_variants_upper_R1

/-! Deleting the last vertex of a graph on Fin (n + 1) lowers the chromatic number by at
most one, because a colouring of the rest extends with one new colour. Hence, by induction
on the number of vertices, a triangle-free graph with chromatic number at least k ≥ 1 has
an induced subgraph on an initial segment with chromatic number exactly k, and that
subgraph is triangle-free. The supremum over graphs on Fin n is attained because chromatic
numbers there are at most n. -/

namespace OMA1013

open SimpleGraph

lemma extend_color {n c : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (h : (G.comap (Fin.castSuccEmb (n := n))).Colorable c) : G.Colorable (c + 1) := by
  obtain ⟨C⟩ := h
  refine ⟨Coloring.mk
    (fun i => if hi : (i : ℕ) < n then Fin.castSucc (C ⟨i, hi⟩) else Fin.last c) ?_⟩
  intro v w hadj
  by_cases hv : (v : ℕ) < n <;> by_cases hw : (w : ℕ) < n
  · simp only [dif_pos hv, dif_pos hw]
    intro heq
    have h1 := Fin.castSucc_injective _ heq
    have hadj' : (G.comap (Fin.castSuccEmb (n := n))).Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
      show G.Adj (Fin.castSuccEmb ⟨v, hv⟩) (Fin.castSuccEmb ⟨w, hw⟩)
      exact hadj
    exact C.valid hadj' h1
  · simp only [dif_pos hv, dif_neg hw]
    exact (Fin.castSucc_lt_last _).ne
  · simp only [dif_neg hv, dif_pos hw]
    exact (Fin.castSucc_lt_last _).ne'
  · exfalso
    have hvw : v = w := Fin.ext (by
      have h1 := v.isLt
      have h2 := w.isLt
      omega)
    exact hadj.ne hvw

lemma exact_chrom : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 3 → ∀ k χ₀ : ℕ,
    G.chromaticNumber = χ₀ → 1 ≤ k → k ≤ χ₀ →
    ∃ m ≤ n, ∃ H : SimpleGraph (Fin m), H.CliqueFree 3 ∧ H.chromaticNumber = k := by
  intro n
  induction n with
  | zero =>
    intro G _ k χ₀ hχ hk1 hk
    rw [chromaticNumber_eq_zero_of_isEmpty] at hχ
    have h0 : χ₀ = 0 := by exact_mod_cast hχ.symm
    omega
  | succ n ih =>
    intro G hG k χ₀ hχ hk1 hk
    by_cases hkχ : k = χ₀
    · exact ⟨n + 1, le_rfl, G, hG, by rw [hχ, hkχ]⟩
    · have hlt : k < χ₀ := lt_of_le_of_ne hk hkχ
      have hne : (G.comap (Fin.castSuccEmb (n := n))).chromaticNumber ≠ ⊤ :=
        chromaticNumber_ne_top_iff_exists.2 ⟨_, colorable_of_fintype _⟩
      obtain ⟨c', hc'⟩ : ∃ c' : ℕ,
          (G.comap (Fin.castSuccEmb (n := n))).chromaticNumber = c' :=
        ⟨_, (ENat.natCast_toNat hne).symm⟩
      have hcol : (G.comap (Fin.castSuccEmb (n := n))).Colorable c' :=
        chromaticNumber_le_iff_colorable.1 (le_of_eq hc')
      have hext := (extend_color G hcol).chromaticNumber_le
      rw [hχ] at hext
      have hle' : χ₀ ≤ c' + 1 := by exact_mod_cast hext
      have hfree : (G.comap (Fin.castSuccEmb (n := n))).CliqueFree 3 :=
        hG.comap (SimpleGraph.Embedding.comap (Fin.castSuccEmb (n := n)) G).isContained
      obtain ⟨m, hm, H, hH, hHk⟩ := ih _ hfree k c' hc' hk1 (by omega)
      exact ⟨m, by omega, H, hH, hHk⟩

end OMA1013

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_upper_R1.H2 := by
  intro n k hk1 hk
  have hbdd : BddAbove {χ : ℕ | ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ G.chromaticNumber = χ} := by
    refine ⟨n, ?_⟩
    rintro χ ⟨G, _, hχ⟩
    have h := SimpleGraph.chromaticNumber_le_card (G := G)
    rw [hχ, Fintype.card_fin] at h
    exact_mod_cast h
  have hne : {χ : ℕ | ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ G.chromaticNumber = χ}.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hk
    have h0 : sSup (∅ : Set ℕ) = 0 := by simp
    rw [h0] at hk
    omega
  obtain ⟨G, hG, hχ⟩ := Nat.sSup_mem hne hbdd
  obtain ⟨m, hm, H, hH, hHk⟩ := OMA1013.exact_chrom n G hG k _ hχ hk1 hk
  exact le_trans (Erdos1013.h3_le H hH hHk) hm
