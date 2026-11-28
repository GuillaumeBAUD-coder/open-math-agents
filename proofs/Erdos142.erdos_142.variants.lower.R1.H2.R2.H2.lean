import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

/-! Step H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R2: a covering lemma.
Choose q shifts in [0, 2N) independently and uniformly. A fixed target x + N is missed by
one shift with probability 1 - |S| / 2N, so the expected number of uncovered targets is at
most N (1 - |S| / 2N)^q < N exp(-q |S| / 2N) < 1. We run this as a counting argument on
the finite set of shift tuples.
This proof builds on Salofe’s original proof in PR 5279 and weizj99’s
revision in PR 32350. -/

namespace OMA.Helpers

open Finset

/-- The union bound: N bad events, each of probability (1 - s / 2N)^q, cover less than everything. -/
theorem count_bound (N q s : ℕ) (hN : 0 < N) (hsN : s ≤ N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (s : ℝ)) :
    N * (2 * N - s) ^ q < (2 * N) ^ q := by
  let m : ℝ := 2 * N
  let density : ℝ := s / m
  have hm : 0 < m := by dsimp [m]; positivity
  have hlog : Real.log N < q * density := by
    rw [show density = s / m from rfl, mul_div_assoc', lt_div_iff₀ hm]
    simpa [m, mul_comm] using h
  have hsmall : (N : ℝ) * Real.exp (-(q * density)) < 1 := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < N), ← Real.exp_add, ← Real.exp_zero,
      Real.exp_lt_exp]
    linarith
  have hbase : ((2 * N - s : ℕ) : ℝ) ≤ m * Real.exp (-density) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    change m - s ≤ m * Real.exp (-density)
    have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-density)) hm.le
    have hd : m * density = s := by dsimp [density]; field_simp
    nlinarith
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase q
  rw [mul_pow, ← Real.exp_nat_mul, mul_neg] at hp
  have hfinal : (N : ℝ) * ((2 * N - s : ℕ) : ℝ) ^ q < m ^ q := by
    calc
      _ ≤ (N : ℝ) * (m ^ q * Real.exp (-(q * density))) :=
        mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
      _ = m ^ q * ((N : ℝ) * Real.exp (-(q * density))) := by ring
      _ < m ^ q := by simpa using mul_lt_mul_of_pos_left hsmall (pow_pos hm q)
  exact_mod_cast (show (N : ℝ) * ((2 * N - s : ℕ) : ℝ) ^ q < ((2 * N : ℕ) : ℝ) ^ q by
    push_cast; exact hfinal)

end OMA.Helpers

open Finset OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H2 := by
  intro N q S hN _ hS h
  have hsN : S.card ≤ N := by
    have := card_le_card hS
    simpa using this
  let A : ℕ → Finset (Fin (2 * N)) := fun x =>
    univ.filter (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
  have hA : ∀ x ∈ Icc 1 N, (A x).card ≤ 2 * N - S.card := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_Icc.mp hx
    let C := univ.filter (fun r : Fin (2 * N) => ¬ ∀ b ∈ S, r.val + b ≠ x + N)
    have sub (b : ℕ) (hb : b ∈ S) : (x + N - b) % (2 * N) = x + N - b := by
      have := mem_Icc.mp (hS hb)
      exact Nat.mod_eq_of_lt (by omega)
    have hC : S.card ≤ C.card := by
      apply card_le_card_of_injOn
        (fun b => (⟨(x + N - b) % (2 * N), Nat.mod_lt _ (by omega)⟩ : Fin (2 * N)))
      · intro b hb
        have := (mem_Icc.mp (hS hb)).2
        refine mem_filter.mpr ⟨mem_univ _, fun hall => hall b hb ?_⟩
        change (x + N - b) % (2 * N) + b = x + N
        rw [sub b hb]; omega
      · intro b hb c hc he
        have hb' := (mem_Icc.mp (hS hb)).2
        have hc' := (mem_Icc.mp (hS hc)).2
        have e := congrArg Fin.val he
        change (x + N - b) % (2 * N) = (x + N - c) % (2 * N) at e
        rw [sub b hb, sub c hc] at e
        omega
    have hs : (A x).card + C.card = 2 * N := by
      simpa only [A, C, card_univ, Fintype.card_fin] using
        card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * N))))
          (fun r => ∀ b ∈ S, r.val + b ≠ x + N)
    omega
  let Bad : ℕ → Finset (Fin q → Fin (2 * N)) := fun x => Fintype.piFinset (fun _ => A x)
  let U := (Icc 1 N).biUnion Bad
  have hU : U.card < (univ : Finset (Fin q → Fin (2 * N))).card := by
    calc U.card ≤ ∑ x ∈ Icc 1 N, (Bad x).card := card_biUnion_le
      _ ≤ ∑ x ∈ Icc 1 N, (2 * N - S.card) ^ q := by
          exact sum_le_sum fun x hx => by
            simpa only [Bad, Fintype.card_piFinset_const] using Nat.pow_le_pow_left (hA x hx) q
      _ = N * (2 * N - S.card) ^ q := by simp
      _ < (2 * N) ^ q := count_bound N q S.card hN hsN h
      _ = _ := by simp
  obtain ⟨f, -, hf⟩ := exists_mem_notMem_of_card_lt_card hU
  refine ⟨fun t => (f t).val, ?_⟩
  intro x hx
  have hnot : f ∉ Bad x := fun hmem => hf (mem_biUnion.mpr ⟨x, hx, hmem⟩)
  rw [Fintype.mem_piFinset] at hnot
  push Not at hnot
  obtain ⟨t, ht⟩ := hnot
  simp only [A, mem_filter, mem_univ, true_and, not_forall, not_not] at ht
  obtain ⟨b, hb, hbeq⟩ := ht
  exact ⟨t, b, hb, hbeq.symm⟩
