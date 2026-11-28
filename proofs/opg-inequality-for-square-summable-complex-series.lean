import OMAStatements.S_opg_inequality_for_square_summable_complex_series

/-!
Retkes's inequality. An anonymous contributor posted the Cauchy–Schwarz proof
on 3 November 2013 at
https://www.openproblemgarden.org/op/inequality_for_square_summable_complex_series .
Ibragimov and Salimova published a proof in 2015 (doi:10.4171/EM/278).
Ksungwon09 supplied the first merged desk formalization. Here each row is an
inner product in complex ℓ² and injectivity suffices for the final estimate.
-/

private def index (q : ℕ × ℕ) := 2 ^ q.1 * (2 * q.2 + 1) - 1

private lemma index_succ (q : ℕ × ℕ) : index q + 1 = 2 ^ q.1 * (2*q.2+1) :=
  Nat.sub_add_cancel (show 0 < 2 ^ q.1 * (2*q.2+1) by positivity)

private lemma index_injective : Function.Injective index := by
  rintro ⟨k,l⟩ ⟨s,t⟩ h
  have he := congrArg (· + 1) h
  simp only [index_succ] at he
  have val (x y : ℕ) : padicValNat 2 (2^x * (2*y+1)) = x := by
    rw [padicValNat_base_pow_mul (by decide) (by omega), padicValNat.eq_zero_of_not_dvd
      (by omega : ¬ 2 ∣ 2*y+1), zero_add]
  have : k = s := by simpa only [val] using congrArg (padicValNat 2) he
  subst s
  have := Nat.eq_of_mul_eq_mul_left (by positivity) he
  congr 1
  omega

private noncomputable abbrev H := lp (fun _ : ℕ => ℂ) 2

private lemma energy (x : H) : ‖x‖ ^ 2 = ∑' i, ‖x i‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x

private def vector (f : ℕ → ℂ) (h : Summable fun i => ‖f i‖ ^ 2) : H :=
  ⟨f, memℓp_gen (by simpa using h)⟩

theorem OMA.solution : type_of% @OMA.S_opg_inequality_for_square_summable_complex_series.main := by
  intro a ha
  let w (i : ℕ) : ℂ := ((i : ℂ) + 1)⁻¹
  have hw : HasSum (fun i => ‖w i‖ ^ 2) (Real.pi ^ 2 / 6) := by
    have h := hasSum_zeta_two
    rw [← hasSum_nat_add_iff' 1] at h
    norm_num at h
    refine h.congr_fun fun i => ?_
    simp only [w, ← Nat.cast_succ, norm_inv, Complex.norm_natCast, inv_pow]
  let u := vector w hw.summable
  let row (k l : ℕ) := a (2 ^ k * (2*l+1))
  let mass (k : ℕ) := ∑' l, ‖row k l‖ ^ 2
  have hrows : Summable fun q : ℕ × ℕ => ‖row q.1 q.2‖ ^ 2 := by
    simpa only [Function.comp_def, index_succ, row] using ha.comp_injective index_injective
  obtain ⟨each, outer⟩ := (summable_prod_of_nonneg (fun q : ℕ × ℕ => sq_nonneg ‖row q.1 q.2‖)).mp hrows
  have bound (k : ℕ) :
      (6 / Real.pi ^ 2) * ‖∑' l, w l * row k l‖ ^ 2 ≤ mass k := by
    let v := vector (row k) (each k)
    have cs := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) u v) 2
    rw [mul_pow, energy, energy, lp.inner_eq_tsum] at cs
    simp only [u, v, vector, RCLike.inner_apply', w, map_inv₀, map_add,
      map_natCast, map_one] at cs
    change _ ≤ (∑' i, ‖w i‖ ^ 2) * mass k at cs
    rw [hw.tsum_eq] at cs
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  rw [← tsum_mul_left]
  refine ((Summable.of_nonneg_of_le (fun _ => by positivity) bound outer).tsum_le_tsum bound outer).trans ?_
  rw [← hrows.tsum_prod' each]
  apply Summable.tsum_le_tsum_of_inj index index_injective (fun _ _ => sq_nonneg _) _ hrows ha
  rintro ⟨k,l⟩
  rw [index_succ]
