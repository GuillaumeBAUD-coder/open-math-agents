import FormalConjectures.ErdosProblems.«357»

noncomputable def OMA.answer : ℕ → ℝ := fun n ↦ √(n : ℝ) / Real.log (n : ℝ)

open Finset Filter Asymptotics in
theorem OMA.solution :
    Erdos357.erdos_357.parts.ii.littleO_version.answer = OMA.answer →
      type_of% @Erdos357.erdos_357.parts.ii.littleO_version := by
  intro h; rw [h]
  have h1 : (fun n : ℕ ↦ √(n : ℝ) / Real.log (n : ℝ)) =o[atTop] (fun n : ℕ ↦ √(n : ℝ)) := by
    simpa [div_eq_mul_inv] using (isBigO_refl (fun n : ℕ ↦ √(n : ℝ)) atTop).mul_isLittleO
      ((isLittleO_one_iff ℝ).2 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop)
  refine h1.trans_isBigO (IsBigO.of_bound 2 ?_)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  let a (i : Fin n.sqrt) : ℤ := (n : ℤ) - n.sqrt + 1 + i.1
  have hle : n.sqrt ≤ Erdos357.f n := by
    refine le_csSup ⟨n, ?_⟩ ⟨a, ?_, fun i j hij => by dsimp [a]; omega, ?_⟩
    · rintro k ⟨b, hR, hM, _⟩
      have hc := card_le_card (s := univ.image b) (t := Icc (1 : ℤ) n) fun z hz => by
        obtain ⟨i, _, rfl⟩ := mem_image.1 hz; exact mem_Icc.2 (hR ⟨i, rfl⟩)
      rw [card_image_of_injective _ hM.injective] at hc; simpa [Int.card_Icc] using hc
    · rintro _ ⟨i, rfl⟩
      have := Nat.sqrt_le_self n; have := i.2; exact ⟨by dsimp [a]; omega, by dsimp [a]; omega⟩
    · intro J hJ K hK hsum
      have hlt {A B : Finset (Fin n.sqrt)} (hAB : A.card < B.card) :
          ∑ i ∈ A, a i < ∑ i ∈ B, a i := by
        have hup : ∑ i ∈ A, a i ≤ A.card * (n : ℤ) := by
          simpa using sum_le_sum fun i (_ : i ∈ A) => show a i ≤ n by have := i.2; dsimp [a]; omega
        have hlo : B.card * ((n : ℤ) - n.sqrt + 1) ≤ ∑ i ∈ B, a i := by
          simpa using sum_le_sum fun i (_ : i ∈ B) => show (n : ℤ) - n.sqrt + 1 ≤ a i by dsimp [a]; omega
        have h1 : (A.card : ℤ) + 1 ≤ B.card := by exact_mod_cast hAB
        have h2 : (B.card : ℤ) ≤ n.sqrt := by exact_mod_cast (by simpa using card_le_card (subset_univ B) : B.card ≤ n.sqrt)
        have h3 : (n.sqrt : ℤ) * n.sqrt ≤ n := by exact_mod_cast Nat.sqrt_le n
        nlinarith [Nat.cast_nonneg (α := ℤ) n, Nat.cast_nonneg (α := ℤ) n.sqrt]
      have hcard : J.card = K.card := by
        by_contra hne; rcases lt_or_gt_of_ne hne with h | h
        · exact (hlt h).ne hsum
        · exact (hlt h).ne hsum.symm
      by_cases hJe : J = ∅
      · subst J; exact (card_eq_zero.1 hcard.symm).symm
      have hJne : J.Nonempty := nonempty_iff_ne_empty.2 hJe
      have hKne : K.Nonempty := card_pos.1 (hcard ▸ hJne.card_pos)
      have : NeZero n.sqrt := ⟨fun hk => by obtain ⟨j, _⟩ := hJne; exact Fin.elim0 (hk ▸ j)⟩
      let jl := J.min' hJne; let ju := J.max' hJne
      let kl := K.min' hKne; let ku := K.max' hKne
      have hJf : J = Icc jl ju := coe_injective <| by
        simpa [jl, ju, hJne.csInf_eq_min', hJne.csSup_eq_max'] using
          (coe_nonempty.2 hJne).ordConnected_iff_of_bdd'.1 hJ
      have hKf : K = Icc kl ku := coe_injective <| by
        simpa [kl, ku, hKne.csInf_eq_min', hKne.csSup_eq_max'] using
          (coe_nonempty.2 hKne).ordConnected_iff_of_bdd'.1 hK
      have hlen : ju.1 + 1 - jl.1 = ku.1 + 1 - kl.1 := by simpa [hJf, hKf, Fin.card_Icc] using hcard
      have hsV : ∑ i ∈ Icc jl.1 ju.1, (i : ℤ) = ∑ i ∈ Icc kl.1 ku.1, (i : ℤ) := by
        simp only [a, sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
        rw [hcard] at hsum
        have hs' : ∑ i ∈ Icc jl ju, (i.1 : ℤ) = ∑ i ∈ Icc kl ku, (i.1 : ℤ) := by
          rw [← hJf, ← hKf]; linarith
        rw [← Fin.map_valEmbedding_Icc, ← Fin.map_valEmbedding_Icc, sum_map, sum_map]; exact hs'
      rw [← Ico_add_one_right_eq_Icc, ← Ico_add_one_right_eq_Icc,
        sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, hlen] at hsV
      simp only [Nat.cast_add, sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at hsV
      have hjle : jl.1 ≤ ju.1 := min'_le_max' J hJne
      have hkle : kl.1 ≤ ku.1 := min'_le_max' K hKne
      have hjl : jl = kl := Fin.ext <| by
        have hpos : (0 : ℤ) < (ku.1 + 1 - kl.1 : ℕ) := by omega
        have : (jl.1 : ℤ) = kl.1 := by nlinarith
        omega
      have hju : ju = ku := Fin.ext (by have := congrArg Fin.val hjl; omega)
      rw [hJf, hKf, hjl, hju]
  have hsq : √(n : ℝ) < (n.sqrt : ℝ) + 1 := (Real.sqrt_lt' (by positivity)).2 <| by
    exact_mod_cast (by simpa [pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n : n < (n.sqrt + 1) ^ 2)
  have hfR : (n.sqrt : ℝ) ≤ Erdos357.f n := by exact_mod_cast hle
  have h1 : (1 : ℝ) ≤ n.sqrt := by exact_mod_cast Nat.sqrt_pos.2 hn
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
    (show √(n : ℝ) ≤ 2 * (Erdos357.f n : ℝ) by nlinarith)
