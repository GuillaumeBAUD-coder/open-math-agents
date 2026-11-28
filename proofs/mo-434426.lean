import OMAStatements.S_mo_434426

-- Problem: mo-434426 double series
-- Upstream: formal-conjectures statements/mo-434426.lean:0 (declaration OMA.S_mo_434426.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OMA.S_mo_434426.main := by
  intro a ha
  have ha0 : 0 < a := by linarith
  have ha1 : a - 1 ≠ 0 := by linarith
  set u : ℕ → ℝ := fun m => ((m:ℝ)+1) / a^(m+1) with hu
  have hupos : ∀ m, 0 < u m := fun m => by positivity
  have hscale : ∀ m, OMA.S_mo_434426.scale a m = 1 / u m := by
    intro m
    simp only [OMA.S_mo_434426.scale, hu]
    push_cast
    field_simp
  have hr : ‖(1/a : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one ha0]
    exact ha
  have hgs := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hsu : HasSum u (a/(a-1)^2) := by
    have h1 : HasSum (fun n : ℕ => ((n+1 : ℕ):ℝ) * (1/a)^(n+1)) ((1/a)/(1-1/a)^2) := by
      have := (hasSum_nat_add_iff' 1).mpr hgs
      simpa using this
    convert h1 using 1
    · funext m
      simp only [hu]
      push_cast
      rw [one_div, inv_pow]
      ring
    · have : a ≠ 0 := ha0.ne'
      field_simp
  have hS := hsu.summable
  set f : ℕ × ℕ → ℝ := fun p => OMA.S_mo_434426.term a p.1 p.2 with hf
  have hfeq : ∀ p, f p = u p.1 ^ 2 * u p.2 / (u p.1 + u p.2) := by
    intro p
    simp only [hf, OMA.S_mo_434426.term, hscale]
    have h1 := hupos p.1
    have h2 := hupos p.2
    field_simp
    ring
  have hfnn : ∀ p, 0 ≤ f p := fun p => by
    rw [hfeq]
    have h1 := hupos p.1
    have h2 := hupos p.2
    positivity
  have hsym : ∀ p : ℕ × ℕ, f p + f p.swap = u p.1 * u p.2 := by
    intro p
    rw [hfeq, hfeq]
    simp only [Prod.fst_swap, Prod.snd_swap]
    have h1 := hupos p.1
    have h2 := hupos p.2
    field_simp
    ring
  have hprod : Summable fun p : ℕ × ℕ => u p.1 * u p.2 :=
    hS.mul_of_nonneg hS (fun m => (hupos m).le) (fun m => (hupos m).le)
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le hfnn (fun p => ?_) hprod
    have := hfnn p.swap
    linarith [hsym p]
  have hswap : ∑' p : ℕ × ℕ, f p.swap = ∑' p, f p := (Equiv.prodComm ℕ ℕ).tsum_eq f
  have hfs' : Summable fun p : ℕ × ℕ => f p.swap := (Equiv.prodComm ℕ ℕ).summable_iff.mpr hfs
  have h2 : 2 * ∑' p, f p = (a/(a-1)^2)^2 := by
    calc 2 * ∑' p, f p = ∑' p, f p + ∑' p : ℕ × ℕ, f p.swap := by rw [hswap]; ring
      _ = ∑' p : ℕ × ℕ, (f p + f p.swap) := (hfs.tsum_add hfs').symm
      _ = ∑' p : ℕ × ℕ, u p.1 * u p.2 := by simp only [hsym]
      _ = (∑' m, u m) * ∑' n, u n := (hS.tsum_mul_tsum hS hprod).symm
      _ = _ := by rw [hsu.tsum_eq]; ring
  have h3 : ∑' m : ℕ, ∑' n : ℕ, OMA.S_mo_434426.term a m n = ∑' p, f p := (hfs.tsum_prod).symm
  rw [h3]
  have h4 : ∑' p, f p = (a/(a-1)^2)^2 / 2 := by linarith
  rw [h4]
  field_simp
