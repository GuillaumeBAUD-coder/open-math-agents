import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

/-! Finite union bound over the shift tuples, following the counting argument in PR #32350. -/

open Finset

lemma shift_tuple_bound {N q s : ℕ} (hN : 0 < N) (hs : s ≤ N)
    (h : 2 * (N : ℝ) * Real.log N < q * (s : ℝ)) : N * (2 * N - s) ^ q < (2 * N) ^ q := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm : 0 < 2 * (N : ℝ) := by positivity
  let p : ℝ := (s : ℝ) / (2 * N)
  have hp : p ≤ 1 := (div_le_one hm).2 (by
    have : (s : ℝ) ≤ N := by exact_mod_cast hs
    linarith)
  have hlog : Real.log N < q * p := by
    dsimp [p]
    rw [mul_div_assoc', lt_div_iff₀ hm]
    linarith
  have hpow : (1 - p) ^ q ≤ Real.exp (-(q * p)) := by
    rw [show -(q * p) = q * (-p) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) q
  have hsmall : (N : ℝ) * (1 - p) ^ q < 1 := by
    calc
      _ ≤ (N : ℝ) * Real.exp (-(q * p)) := mul_le_mul_of_nonneg_left hpow hNr.le
      _ = Real.exp (Real.log N - q * p) := by rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hNr]
      _ < Real.exp 0 := Real.exp_lt_exp.mpr (sub_neg.mpr hlog)
      _ = 1 := Real.exp_zero
  have hratio : ((2 * N - s : ℕ) : ℝ) / (2 * N) = 1 - p := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, sub_div, div_self hm.ne']
  have hfrac : (N : ℝ) * ((2 * N - s : ℕ) : ℝ) ^ q / (2 * N) ^ q < 1 := by
    rwa [mul_div_assoc, ← div_pow, hratio]
  have hreal := (div_lt_iff₀ (pow_pos hm q)).mp hfrac
  rw [one_mul] at hreal
  exact_mod_cast hreal

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H2 := by
  intro N q S hN _ hS h
  have hsN : S.card ≤ N := by simpa using card_le_card hS
  let good (x : ℕ) := (univ : Finset (Fin (2 * N))).filter
    (fun (r : Fin (2 * N)) => ∃ b ∈ S, x + N = r.val + b)
  have goodCard (x : ℕ) (hx : x ∈ Icc 1 N) : S.card ≤ (good x).card := by
    have hx' := mem_Icc.mp hx
    let encode (b : S) : Fin (2 * N) :=
      ⟨x + N - b.val, by have := mem_Icc.mp (hS b.prop); omega⟩
    have hinj : Function.Injective encode := by
      intro b b' heq
      apply Subtype.ext
      have := mem_Icc.mp (hS b.prop)
      have := mem_Icc.mp (hS b'.prop)
      have he := congrArg Fin.val heq
      change x + N - b.val = x + N - b'.val at he
      omega
    have hsub : S.attach.image encode ⊆ good x := by
      rintro r hr
      obtain ⟨b, _, rfl⟩ := mem_image.mp hr
      apply mem_filter.mpr
      refine ⟨mem_univ _, b.val, b.prop, ?_⟩
      have := mem_Icc.mp (hS b.prop)
      change x + N = x + N - b.val + b.val
      omega
    rw [← card_attach, ← card_image_of_injective _ hinj]
    exact card_le_card hsub
  let bad x : Finset (Fin q → Fin (2 * N)) := Fintype.piFinset (fun _ => (good x)ᶜ)
  have hbad : ((Icc 1 N).biUnion bad).card < Fintype.card (Fin q → Fin (2 * N)) := by
    calc
      _ ≤ ∑ x ∈ Icc 1 N, (bad x).card := card_biUnion_le
      _ ≤ ∑ _x ∈ Icc 1 N, (2 * N - S.card) ^ q := by
        apply sum_le_sum
        intro x hx
        dsimp [bad]
        rw [Fintype.card_piFinset_const, card_compl, Fintype.card_fin]
        exact Nat.pow_le_pow_left (Nat.sub_le_sub_left (goodCard x hx) _) q
      _ = N * (2 * N - S.card) ^ q := by simp
      _ < _ := by simpa using shift_tuple_bound hN hsN h
  rw [← card_univ] at hbad
  obtain ⟨f, _, hf⟩ := exists_mem_notMem_of_card_lt_card hbad
  refine ⟨fun t => f t, fun x hx => ?_⟩
  have hmiss : f ∉ bad x := fun hmem => hf (mem_biUnion.mpr ⟨x, hx, hmem⟩)
  rw [Fintype.mem_piFinset] at hmiss
  push Not at hmiss
  obtain ⟨t, ht⟩ := hmiss
  have hgood : f t ∈ good x := by simpa [mem_compl] using ht
  obtain ⟨b, hb, heq⟩ := (mem_filter.mp hgood).2
  exact ⟨t, b, hb, heq⟩
