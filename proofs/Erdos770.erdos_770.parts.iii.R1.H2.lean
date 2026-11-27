import OMAReductions.R_Erdos770_erdos_770_parts_iii_R1

/-! Small residues generate all units modulo a prime q if their bound squares
to at least q. To descend from a residue a, multiply it by floor(q/a)+1:
the product modulo q is a positive residue smaller than a. -/

private theorem small_residues_generate {q M : ℕ} (hq : q.Prime) (hM : 1 ≤ M)
    (hsq : q ≤ M * M) (H : Subgroup (ZMod q)ˣ)
    (small : ∀ u : (ZMod q)ˣ, (u : ZMod q).val ≤ M → u ∈ H) : H = ⊤ := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have makeUnit (a : ℕ) (ha : 0 < a) (h : a < q) :
      ∃ u : (ZMod q)ˣ, (u : ZMod q).val = a := by
    have hp : a.Coprime q :=
      (hq.coprime_iff_not_dvd.mpr (fun hd => h.not_ge (Nat.le_of_dvd ha hd))).symm
    exact ⟨ZMod.unitOfCoprime a hp, by rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt h]⟩
  have allMem (a : ℕ) : ∀ u : (ZMod q)ˣ, (u : ZMod q).val = a → u ∈ H := by
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro u hu
      by_cases ha : a ≤ M
      · exact small u (hu ▸ ha)
      have hap : 0 < a := by omega
      have haq : a < q := hu ▸ ZMod.val_lt (u : ZMod q)
      have ham : M < a := by omega
      let t := q / a + 1
      let r := a - q % a
      have ht : q / a < M := (Nat.div_lt_iff_lt_mul hap).mpr
        (by nlinarith [Nat.mul_lt_mul_of_pos_left ham (show 0 < M by omega)])
      have hmod : q % a ≠ 0 := fun h => by
        rcases hq.eq_one_or_self_of_dvd a (Nat.dvd_of_mod_eq_zero h) with e | e <;> omega
      have hm := Nat.mod_lt q hap
      have hrt : 0 < r ∧ r < a := by dsimp [r]; omega
      have htt : 0 < t ∧ t < a := ⟨Nat.zero_lt_succ _, (Nat.succ_le_of_lt ht).trans_lt ham⟩
      obtain ⟨w, hw⟩ := makeUnit t htt.1 (htt.2.trans haq)
      obtain ⟨v, hv⟩ := makeUnit r hrt.1 (hrt.2.trans haq)
      have hprod : a * t = q + r := by
        dsimp [t, r]
        rw [Nat.mul_add, Nat.mul_one]
        have := Nat.mod_add_div q a
        omega
      have hu' : (a : ZMod q) = u := hu ▸ ZMod.natCast_zmod_val (u : ZMod q)
      have hw' : (t : ZMod q) = w := hw ▸ ZMod.natCast_zmod_val (w : ZMod q)
      have hv' : (r : ZMod q) = v := hv ▸ ZMod.natCast_zmod_val (v : ZMod q)
      have heq : u * w = v := by
        apply Units.ext
        rw [Units.val_mul, ← hu', ← hw', ← hv', ← Nat.cast_mul, hprod,
          Nat.cast_add, ZMod.natCast_self, zero_add]
      exact (H.mul_mem_cancel_right (ih t htt.2 w hw)).mp (heq ▸ ih r hrt.2 v hv)
  exact top_unique (fun u _ => allMem _ u rfl)

private theorem size_bound {q : ℕ} (hq : 2 ≤ q) (hlim : q < 2 ^ 17) :
    ∃ M : ℕ, 1 ≤ M ∧ q ≤ M * M ∧ (M : ℝ) ≤ 21 / 5 * Real.log q ^ 2 := by
  have lower (m : ℕ) (h : 2 ^ m ≤ q) : (m : ℝ) * (693 / 1000) ≤ Real.log q := by
    have hmono := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ m)
      (show (2 : ℝ) ^ m ≤ q by exact_mod_cast h)
    rw [Real.log_pow] at hmono
    have hlo : (693 / 1000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact (mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg m)).trans hmono
  by_cases h16 : 65536 ≤ q
  · refine ⟨400, by decide, by norm_num at *; omega, ?_⟩
    have h := lower 16 (by norm_num; exact h16)
    norm_num at h ⊢
    nlinarith [sq_nonneg (Real.log q - 10)]
  by_cases h12 : 4096 ≤ q
  · refine ⟨256, by decide, by norm_num at *; omega, ?_⟩
    have h := lower 12 (by norm_num; exact h12)
    norm_num at h ⊢
    nlinarith [sq_nonneg (Real.log q - 8)]
  by_cases h6 : 64 ≤ q
  · refine ⟨64, by decide, by norm_num at *; omega, ?_⟩
    have h := lower 6 (by norm_num; exact h6)
    norm_num at h ⊢
    nlinarith [sq_nonneg (Real.log q - 4)]
  by_cases h2 : 4 ≤ q
  · refine ⟨8, by decide, by norm_num at *; omega, ?_⟩
    have h := lower 2 (by norm_num; exact h2)
    norm_num at h ⊢
    nlinarith [sq_nonneg (Real.log q - (693 / 500))]
  have h₁ : 2 ≤ q := hq
  refine ⟨2, by decide, by norm_num at *; omega, ?_⟩
  have h := lower 1 (by norm_num; exact h₁)
  norm_num at h ⊢
  nlinarith [sq_nonneg (Real.log q - (693 / 1000))]

theorem OMA.solution : OMA.R_Erdos770_erdos_770_parts_iii_R1.H2 := by
  intro q hq hlim H hH
  obtain ⟨M, hM, hsq, hlog⟩ := size_bound hq.two_le hlim
  by_contra! h
  apply hH (small_residues_generate hq hM hsq H ?_)
  intro u hu
  by_contra hu'
  exact (h u hu').not_ge ((show ((u : ZMod q).val : ℝ) ≤ M by exact_mod_cast hu).trans hlog)

