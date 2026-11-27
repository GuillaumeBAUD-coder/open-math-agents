import OMAReductions.R_Erdos1013_erdos_1013_variants_lower_R1

/-! Triangle-free graphs of every chromatic number, by shift graphs instead of the
Mycielski construction. The shift graph on the increasing pairs (i, j) from N points joins
(i, j) to (j, l). It has no triangle. In a proper colouring with m colours the sets of
colours used on the pairs starting at i are pairwise distinct subsets of the colours, so
N ≤ 2^m. With N = 2^k + 1 the chromatic number exceeds k, and deleting vertices one at a
time, which lowers the chromatic number by at most one, reaches exactly k. -/

namespace OMA1013b

open SimpleGraph

/-- The shift graph on increasing pairs from `Fin N`. -/
def shiftG (N : ℕ) : SimpleGraph {p : Fin N × Fin N // p.1 < p.2} :=
  SimpleGraph.fromRel (fun p q => p.1.2 = q.1.1)

lemma shift_free (N : ℕ) : (shiftG N).CliqueFree 3 := by
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.1 hs
  unfold shiftG at hab hac hbc
  rw [SimpleGraph.fromRel_adj] at hab hac hbc
  have ha : (a.1.1 : ℕ) < a.1.2 := a.2
  have hb : (b.1.1 : ℕ) < b.1.2 := b.2
  have hc : (c.1.1 : ℕ) < c.1.2 := c.2
  rcases hab.2 with h1 | h1 <;> rcases hac.2 with h2 | h2 <;> rcases hbc.2 with h3 | h3 <;>
    · have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      have e3 := congrArg Fin.val h3
      omega

lemma shift_bound (N m : ℕ) (h : (shiftG N).Colorable m) : N ≤ 2 ^ m := by
  classical
  obtain ⟨C⟩ := h
  have key : ∀ i j : Fin N, i < j →
      (Finset.univ.filter (fun p : {p : Fin N × Fin N // p.1 < p.2} => p.1.1 = i)).image C =
      (Finset.univ.filter (fun p : {p : Fin N × Fin N // p.1 < p.2} => p.1.1 = j)).image C →
      False := by
    intro i j hlt heq
    have hp : C ⟨(i, j), hlt⟩ ∈
        (Finset.univ.filter (fun p : {p : Fin N × Fin N // p.1 < p.2} => p.1.1 = i)).image C :=
      Finset.mem_image.2 ⟨⟨(i, j), hlt⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    rw [heq] at hp
    obtain ⟨q, hq, hCq⟩ := Finset.mem_image.1 hp
    have hq1 : q.1.1 = j := (Finset.mem_filter.1 hq).2
    have hadj : (shiftG N).Adj ⟨(i, j), hlt⟩ q := by
      unfold shiftG
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl hq1.symm⟩
      intro hpq
      rw [← hpq] at hq1
      exact absurd hq1 (ne_of_lt hlt)
    exact C.valid hadj hCq.symm
  have hinj : Function.Injective (fun i : Fin N =>
      (Finset.univ.filter (fun p : {p : Fin N × Fin N // p.1 < p.2} => p.1.1 = i)).image C) := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i j h hij
    · exact key j i h hij.symm
  have hcard := Fintype.card_le_of_injective _ hinj
  rwa [Fintype.card_fin, Fintype.card_finset, Fintype.card_fin] at hcard

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

end OMA1013b

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H2 := by
  intro k hk1
  classical
  obtain ⟨e⟩ : Nonempty ({p : Fin (2 ^ k + 1) × Fin (2 ^ k + 1) // p.1 < p.2} ≃
      Fin (Fintype.card {p : Fin (2 ^ k + 1) × Fin (2 ^ k + 1) // p.1 < p.2})) :=
    ⟨Fintype.equivFin _⟩
  have hfree' : ((OMA1013b.shiftG (2 ^ k + 1)).comap e.symm.toEmbedding).CliqueFree 3 :=
    (OMA1013b.shift_free _).comap
      (SimpleGraph.Embedding.comap e.symm.toEmbedding (OMA1013b.shiftG (2 ^ k + 1))).isContained
  have hne : ((OMA1013b.shiftG (2 ^ k + 1)).comap e.symm.toEmbedding).chromaticNumber ≠ ⊤ :=
    SimpleGraph.chromaticNumber_ne_top_iff_exists.2 ⟨_, SimpleGraph.colorable_of_fintype _⟩
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : ℕ,
      ((OMA1013b.shiftG (2 ^ k + 1)).comap e.symm.toEmbedding).chromaticNumber = χ₀ :=
    ⟨_, (ENat.natCast_toNat hne).symm⟩
  have hcol' := SimpleGraph.chromaticNumber_le_iff_colorable.1 (le_of_eq hχ₀)
  have hcol : (OMA1013b.shiftG (2 ^ k + 1)).Colorable χ₀ := by
    obtain ⟨C'⟩ := hcol'
    refine ⟨C'.comp ⟨fun v => e v, ?_⟩⟩
    intro a b hab
    show (OMA1013b.shiftG (2 ^ k + 1)).Adj (e.symm (e a)) (e.symm (e b))
    simpa using hab
  have hbound := OMA1013b.shift_bound _ _ hcol
  have hk : k ≤ χ₀ := by
    by_contra hcon
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_le.1 hcon).le
    omega
  obtain ⟨m, hm, H, hH, hHk⟩ := OMA1013b.exact_chrom _ _ hfree' k χ₀ hχ₀ hk1 hk
  exact ⟨m, H, hH, hHk⟩
