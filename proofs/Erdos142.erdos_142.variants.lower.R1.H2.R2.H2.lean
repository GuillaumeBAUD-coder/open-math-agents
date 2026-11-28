import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2

/-! Finite union bound for translates. The preceding arguments in PRs #5279, #32350,
and #37622 use the same counting method. The injection below counts good shifts
directly in the subtype of shifts that hit a point. -/

open Finset

lemma miss_bound {N q s : ℕ} (hN : 0 < N) (hs : s ≤ N)
    (h : 2 * (N : ℝ) * Real.log N < q * (s : ℝ)) : N * (2 * N - s)^q < (2 * N)^q := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm : 0 < 2 * (N : ℝ) := by positivity
  let p : ℝ := s / (2 * N)
  have hr : ((2 * N - s : ℕ) : ℝ) / (2 * N) = 1 - p := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, sub_div, div_self hm.ne']
  have hp : 0 ≤ 1 - p := by rw [← hr]; positivity
  have hpow := pow_le_pow_left₀ hp (show 1 - p ≤ Real.exp (-p) by linarith [Real.add_one_le_exp (-p)]) q
  rw [← Real.exp_nat_mul, mul_neg] at hpow
  have hl : Real.log N < q * p := by
    dsimp [p]
    rw [mul_div_assoc', lt_div_iff₀ hm]
    linarith
  have he : (N : ℝ) * Real.exp (-(q * p)) < 1 := by
    rw [← Real.exp_log hn, ← Real.exp_add, ← Real.exp_zero, Real.exp_lt_exp]
    linarith
  have H := (mul_le_mul_of_nonneg_left hpow hn.le).trans_lt he
  rw [← hr, div_pow, ← mul_div_assoc, div_lt_iff₀ (pow_pos hm q), one_mul] at H
  exact_mod_cast H

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H2 := by
  intro N q S hN _ hS h
  let good (x : ℕ) := univ.filter (fun t : Fin (2 * N) => ∃ b ∈ S, x + N = t.val + b)
  have count x (hx : x ∈ Icc 1 N) : S.card ≤ (good x).card := by
    have := mem_Icc.mp hx
    let f (b : S) : good x := by
      have := mem_Icc.mp (hS b.property)
      refine ⟨⟨x + N - b.val, by omega⟩, mem_filter.mpr ⟨mem_univ _, b.val, b.property, ?_⟩⟩
      change x + N = x + N - b.val + b.val
      omega
    have inj : Function.Injective f := by
      intro a b eq
      have := mem_Icc.mp (hS a.property)
      have := mem_Icc.mp (hS b.property)
      have eq' := congrArg (fun t : good x => t.val.val) eq
      change x + N - a.val = x + N - b.val at eq'
      exact Subtype.ext (by omega)
    simpa using Fintype.card_le_of_injective f inj
  let bad x : Finset (Fin q → Fin (2 * N)) := Fintype.piFinset (fun _ => (good x)ᶜ)
  have hb : ((Icc 1 N).biUnion bad).card < (univ : Finset (Fin q → Fin (2 * N))).card := calc
    _ ≤ ∑ x ∈ Icc 1 N, (bad x).card := card_biUnion_le
    _ ≤ ∑ _x ∈ Icc 1 N, (2 * N - S.card)^q := sum_le_sum fun x hx => by
      simpa only [bad, Fintype.card_piFinset_const, card_compl, Fintype.card_fin] using
        Nat.pow_le_pow_left (Nat.sub_le_sub_left (count x hx) (2 * N)) q
    _ = N * (2 * N - S.card)^q := by simp
    _ < _ := by simpa using miss_bound hN (by simpa using card_le_card hS) h
  obtain ⟨f, _, hf⟩ := exists_mem_notMem_of_card_lt_card hb
  refine ⟨fun i => (f i).val, fun x hx => ?_⟩
  have e : f ∉ bad x := fun he => hf (mem_biUnion.mpr ⟨x, hx, he⟩)
  simp only [bad, Fintype.mem_piFinset, mem_compl, not_forall, not_not] at e
  obtain ⟨i, hi⟩ := e
  exact ⟨i, (mem_filter.mp hi).2⟩
