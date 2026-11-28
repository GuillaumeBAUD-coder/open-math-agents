import OMAReductions.R_Green4_large_green_4_R1

/-!
Proof of `Green4.large_green_4.R1.H1`: for all sufficiently large `n`, there exist
`x : Fin n` and `I : Set (Fin n)` whose extremal product-free family in `alternatingGroup (Fin n)`
has density at least `n ^ (-33 / 50)`.

We take `k = Nat.sqrt (n / 4)`, `x = 0`, and `I = {1, ..., k}`.
1. Right multiplication by a transposition supported outside `insert x I` gives a sign-reversing
   involution on the corresponding family in `Equiv.Perm (Fin n)`, so the density in
   `alternatingGroup (Fin n)` equals the density in `Equiv.Perm (Fin n)`.
2. An explicit injection from `I × (I ↪ Iᶜ) × Equiv.Perm ((insert x I)ᶜ)` shows the family in
   `Equiv.Perm (Fin n)` has size at least `k * (n - k).descFactorial k * (n - k - 1)!`.
3. Bernoulli's inequality yields `(n - k).descFactorial k / n.descFactorial k ≥ 1 / 2`, so the
   density is at least `k / (2 * n) ≥ n ^ (-33 / 50)` for all `n ≥ 6 ^ 7`.
-/

-- Step Green4.large_green_4.R1.H1: hypothesis H1 of reduction Green4.large_green_4.R1
-- Credit: @PrimordialAA

namespace OMA.Green4H1

open Filter Finset Green4

private noncomputable def permExtremal {n : ℕ} (x : Fin n) (I : Set (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  haveI := Classical.decPred (fun σ : Equiv.Perm (Fin n) => σ x ∈ I ∧ Disjoint (I.image σ) I)
  Finset.univ.filter (fun σ => σ x ∈ I ∧ Disjoint (I.image σ) I)

private lemma mem_permExtremal {n : ℕ} {x : Fin n} {I : Set (Fin n)} {σ : Equiv.Perm (Fin n)} :
    σ ∈ permExtremal x I ↔ σ x ∈ I ∧ Disjoint (I.image σ) I := by
  classical
  simp [permExtremal]

private lemma ncard_extremalFamily_eq_even_card {n : ℕ} (x : Fin n) (I : Set (Fin n)) :
    (extremalFamily x I).ncard =
      ((permExtremal x I).filter (fun σ => Equiv.Perm.sign σ = 1)).card := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  refine Finset.card_bij (fun π _ => π.val) ?_ ?_ ?_
  · intro π hπ
    rw [Set.mem_toFinset] at hπ
    rw [Finset.mem_filter, mem_permExtremal]
    exact ⟨⟨hπ.1, hπ.2⟩, Equiv.Perm.mem_alternatingGroup.mp π.property⟩
  · intro π₁ _ π₂ _ h
    exact Subtype.ext h
  · intro σ hσ
    rw [Finset.mem_filter, mem_permExtremal] at hσ
    refine ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ.2⟩, ?_, rfl⟩
    rw [Set.mem_toFinset]
    exact hσ.1

private lemma two_mul_ncard_extremalFamily {n : ℕ} (x : Fin n) (I : Set (Fin n))
    (u v : Fin n) (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x) (huI : u ∉ I) (hvI : v ∉ I) :
    2 * (extremalFamily x I).ncard = (permExtremal x I).card := by
  classical
  rw [ncard_extremalFamily_eq_even_card]
  let E := permExtremal x I
  let evenE := E.filter (fun σ => Equiv.Perm.sign σ = 1)
  let oddE := E.filter (fun σ => Equiv.Perm.sign σ ≠ 1)
  let τ : Equiv.Perm (Fin n) := Equiv.swap u v
  have hτ_sign : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap huv
  have hτ_x : τ x = x := Equiv.swap_apply_of_ne_of_ne hux.symm hvx.symm
  have hτ_I : ∀ z ∈ I, τ z = z := fun z hz =>
    Equiv.swap_apply_of_ne_of_ne (fun h => huI (h ▸ hz)) (fun h => hvI (h ▸ hz))
  have hmul_mem : ∀ σ ∈ E, σ * τ ∈ E := by
    intro σ hσ
    rw [mem_permExtremal] at hσ ⊢
    constructor
    · change σ (τ x) ∈ I
      rw [hτ_x]
      exact hσ.1
    · have himg : I.image (⇑(σ * τ)) = I.image (⇑σ) := by
        ext w
        simp only [Set.mem_image, Equiv.Perm.coe_mul, Function.comp_apply]
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z, hz, by rw [hτ_I z hz]⟩
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z, hz, by rw [hτ_I z hz]⟩
      rw [himg]
      exact hσ.2
  have hcard_eq : evenE.card = oddE.card := by
    refine Finset.card_bij (fun σ _ => σ * τ) ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_filter] at hσ ⊢
      refine ⟨hmul_mem σ hσ.1, ?_⟩
      rw [map_mul, hσ.2, hτ_sign, one_mul]
      decide
    · intro σ₁ _ σ₂ _ h
      exact mul_right_cancel h
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      refine ⟨σ * τ, ?_, by simp [τ, mul_assoc]⟩
      rw [Finset.mem_filter]
      refine ⟨hmul_mem σ hσ.1, ?_⟩
      rw [map_mul, hτ_sign]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | hneg
      · exact absurd h1 hσ.2
      · rw [hneg]; decide
  have hsum : evenE.card + oddE.card = E.card :=
    Finset.card_filter_add_card_filter_not (s := E) (p := fun σ => Equiv.Perm.sign σ = 1)
  change 2 * evenE.card = E.card
  omega

private lemma two_mul_card_alternatingGroup {n : ℕ} (hn : 2 ≤ n) :
    2 * Fintype.card (alternatingGroup (Fin n)) = n.factorial := by
  classical
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by simp [u, v]
  let τ : Equiv.Perm (Fin n) := Equiv.swap u v
  have hτ_sign : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap huv
  let evenAll := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => Equiv.Perm.sign σ = 1)
  let oddAll := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => Equiv.Perm.sign σ ≠ 1)
  have hAlt : Fintype.card (alternatingGroup (Fin n)) = evenAll.card := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun π _ => π.val) ?_ ?_ ?_
    · intro π _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Equiv.Perm.mem_alternatingGroup.mp π.property⟩
    · intro π₁ _ π₂ _ h
      exact Subtype.ext h
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      exact ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ.2⟩, Finset.mem_univ _, rfl⟩
  have hcard_eq : evenAll.card = oddAll.card := by
    refine Finset.card_bij (fun σ _ => σ * τ) ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_filter] at hσ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [map_mul, hσ.2, hτ_sign, one_mul]
      decide
    · intro σ₁ _ σ₂ _ h
      exact mul_right_cancel h
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      refine ⟨σ * τ, ?_, by simp [τ, mul_assoc]⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [map_mul, hτ_sign]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | hneg
      · exact absurd h1 hσ.2
      · rw [hneg]; decide
  have hsum : evenAll.card + oddAll.card = (Finset.univ : Finset (Equiv.Perm (Fin n))).card :=
    Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun σ => Equiv.Perm.sign σ = 1)
  have htot : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  omega

private lemma card_permExtremal_ge {n k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k + 1 ≤ n) :
    let x : Fin n := ⟨0, by omega⟩
    let Ifin : Finset (Fin n) := Finset.univ.filter (fun j => 1 ≤ j.val ∧ j.val ≤ k)
    k * (n - k).descFactorial k * (n - k - 1).factorial ≤
      (permExtremal x (Ifin : Set (Fin n))).card := by
  classical
  intro x Ifin
  have hIfin_card : Ifin.card = k := by
    have hbij : Ifin.card = (Finset.range k).card := by
      refine Finset.card_bij (fun j _ => j.val - 1) ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_range]
        omega
      · intro j₁ hj₁ j₂ hj₂ h
        rw [Finset.mem_filter] at hj₁ hj₂
        exact Fin.ext (by omega)
      · intro m hm
        rw [Finset.mem_range] at hm
        refine ⟨⟨m + 1, by omega⟩, ?_, by simp⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩
    rw [hbij, Finset.card_range]
  have hx_not_mem : x ∉ Ifin := by simp [Ifin, x]
  let S : Finset (Fin n) := insert x Ifin
  have hS_card : S.card = k + 1 := by
    rw [Finset.card_insert_of_notMem hx_not_mem, hIfin_card]
  have hIfin_compl_card : Fintype.card {w : Fin n // w ∉ Ifin} = n - k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hIfin_card]
  have hS_compl_card : Fintype.card {z : Fin n // z ∉ S} = n - k - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hS_card]
    omega
  let Dom := {y : Fin n // y ∈ Ifin} ×
    ({z : Fin n // z ∈ Ifin} ↪ {w : Fin n // w ∉ Ifin}) ×
    Equiv.Perm {z : Fin n // z ∉ S}
  have hDom_card : Fintype.card Dom = k * (n - k).descFactorial k * (n - k - 1).factorial := by
    simp only [Dom, Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_perm,
      Fintype.card_coe, hIfin_card, hIfin_compl_card, hS_compl_card, mul_assoc]
  have hT_card : ∀ (y : {y : Fin n // y ∈ Ifin})
      (f : {z : Fin n // z ∈ Ifin} ↪ {w : Fin n // w ∉ Ifin}),
      Fintype.card {z : Fin n // z ∉ S} =
        Fintype.card {w : Fin n // w ∉ insert y.val (Finset.univ.image (fun z => (f z).val))} := by
    intro y f
    let imgF : Finset (Fin n) := Finset.univ.image (fun z => (f z).val)
    have himgF_card : imgF.card = k := by
      rw [Finset.card_image_of_injective _ (fun a b h => f.injective (Subtype.ext h)),
        Finset.card_univ, Fintype.card_coe, hIfin_card]
    have hy_not_img : y.val ∉ imgF := by
      intro hy
      obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hy
      exact (f z).property (hz.symm ▸ y.property)
    have hT : (insert y.val imgF).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hy_not_img, himgF_card]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_coe, Fintype.card_coe, hS_card, hT]
  let buildFun : Dom → Fin n → Fin n := fun ⟨y, f, ρ⟩ z =>
    let e := Fintype.equivOfCardEq (hT_card y f)
    if hz : z = x then y.val
    else if hI : z ∈ Ifin then (f ⟨z, hI⟩).val
    else (e (ρ ⟨z, by simp [S, hz, hI]⟩)).val
  have hbuild_inj : ∀ p : Dom, Function.Injective (buildFun p) := by
    rintro ⟨y, f, ρ⟩ z₁ z₂ h
    let imgF : Finset (Fin n) := Finset.univ.image (fun z => (f z).val)
    let T : Finset (Fin n) := insert y.val imgF
    let e := Fintype.equivOfCardEq (hT_card y f)
    have hmem_T_y : y.val ∈ T := Finset.mem_insert_self _ _
    have hmem_T_f : ∀ z : {z : Fin n // z ∈ Ifin}, (f z).val ∈ T := fun z =>
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩)
    dsimp only [buildFun] at h
    by_cases hz₁ : z₁ = x <;> by_cases hz₂ : z₂ = x
    · exact hz₁.trans hz₂.symm
    · rw [dif_pos hz₁, dif_neg hz₂] at h
      split_ifs at h with hI₂
      · exact absurd (h ▸ y.property) (f ⟨z₂, hI₂⟩).property
      · exact absurd (h ▸ hmem_T_y) (e (ρ ⟨z₂, by simp [S, hz₂, hI₂]⟩)).property
    · rw [dif_neg hz₁, dif_pos hz₂] at h
      split_ifs at h with hI₁
      · exact absurd (h.symm ▸ y.property) (f ⟨z₁, hI₁⟩).property
      · exact absurd (h.symm ▸ hmem_T_y) (e (ρ ⟨z₁, by simp [S, hz₁, hI₁]⟩)).property
    · rw [dif_neg hz₁, dif_neg hz₂] at h
      by_cases hI₁ : z₁ ∈ Ifin <;> by_cases hI₂ : z₂ ∈ Ifin
      · rw [dif_pos hI₁, dif_pos hI₂] at h
        exact congrArg Subtype.val (f.injective (Subtype.ext h))
      · rw [dif_pos hI₁, dif_neg hI₂] at h
        exact absurd (h ▸ hmem_T_f ⟨z₁, hI₁⟩) (e (ρ ⟨z₂, by simp [S, hz₂, hI₂]⟩)).property
      · rw [dif_neg hI₁, dif_pos hI₂] at h
        exact absurd (h.symm ▸ hmem_T_f ⟨z₂, hI₂⟩) (e (ρ ⟨z₁, by simp [S, hz₁, hI₁]⟩)).property
      · rw [dif_neg hI₁, dif_neg hI₂] at h
        exact congrArg Subtype.val (ρ.injective (e.injective (Subtype.ext h)))
  let build : Dom → Equiv.Perm (Fin n) := fun p =>
    Equiv.ofBijective (buildFun p) (Finite.injective_iff_bijective.mp (hbuild_inj p))
  have hbuild_mem : ∀ p : Dom, build p ∈ permExtremal x (Ifin : Set (Fin n)) := by
    rintro ⟨y, f, ρ⟩
    rw [mem_permExtremal]
    constructor
    · change buildFun ⟨y, f, ρ⟩ x ∈ (Ifin : Set (Fin n))
      simp [buildFun]
    · rw [Set.disjoint_left]
      rintro w ⟨z, hz, rfl⟩ hw
      have hz' : z ∈ Ifin := hz
      have hzx : z ≠ x := fun h => hx_not_mem (h ▸ hz')
      change buildFun ⟨y, f, ρ⟩ z ∈ (Ifin : Set (Fin n)) at hw
      simp only [buildFun, dif_neg hzx, dif_pos hz'] at hw
      exact (f ⟨z, hz'⟩).property hw
  have hbuild_outer_inj : Function.Injective build := by
    rintro ⟨y₁, f₁, ρ₁⟩ ⟨y₂, f₂, ρ₂⟩ h
    have hfun : buildFun ⟨y₁, f₁, ρ₁⟩ = buildFun ⟨y₂, f₂, ρ₂⟩ :=
      funext (fun z => Equiv.congr_fun h z)
    have hy : y₁ = y₂ := by
      have hx := congrFun hfun x
      simp only [buildFun, dif_pos rfl] at hx
      exact Subtype.ext hx
    subst hy
    have hf : f₁ = f₂ := by
      ext z
      have hz := congrFun hfun z.val
      have hzx : z.val ≠ x := fun h => hx_not_mem (h ▸ z.property)
      simp only [buildFun, dif_neg hzx, dif_pos z.property] at hz
      exact congrArg Fin.val (by simpa using hz)
    subst hf
    have hρ : ρ₁ = ρ₂ := by
      ext z
      have hz := congrFun hfun z.val
      have hzx : z.val ≠ x := fun h => z.property (Finset.mem_insert.mpr (Or.inl h))
      have hzI : z.val ∉ Ifin := fun h => z.property (Finset.mem_insert.mpr (Or.inr h))
      simp only [buildFun, dif_neg hzx, dif_neg hzI] at hz
      have := (Fintype.equivOfCardEq (hT_card y₁ f₁)).injective (Subtype.ext hz)
      exact congrArg Fin.val (by simpa using congrArg Subtype.val this)
    subst hρ
    rfl
  rw [← hDom_card, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn build (fun p _ => hbuild_mem p)
    (fun p₁ _ p₂ _ h => hbuild_outer_inj h)

private lemma descFactorial_ratio_lower {n k : ℕ} (h2k : 2 * k ≤ n) (hn : 0 < n) :
    ∀ m ≤ k, (((n - 2 * k : ℕ) : ℝ) / (n : ℝ)) ^ m * (n.descFactorial m : ℝ) ≤
      ((n - k).descFactorial m : ℝ) := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    have hmk : m < k := Nat.lt_of_succ_le hm
    have ih' := ih (Nat.le_of_lt hmk)
    rw [pow_succ, Nat.descFactorial_succ, Nat.descFactorial_succ]
    push_cast
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hstep : (((n - 2 * k : ℕ) : ℝ) / (n : ℝ)) * ((n - m : ℕ) : ℝ) ≤
        ((n - k - m : ℕ) : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hn_pos]
      have h1 : ((n - 2 * k : ℕ) : ℝ) = (n : ℝ) - 2 * (k : ℝ) := by
        rw [Nat.cast_sub h2k]; push_cast; ring
      have h2 : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
        rw [Nat.cast_sub (by omega)]
      have h3 : ((n - k - m : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) - (m : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      rw [h1, h2, h3]
      have hmkR : (2 * (m : ℝ)) ≤ (n : ℝ) := by exact_mod_cast (show 2 * m ≤ n by omega)
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    have hnonneg : (0 : ℝ) ≤ (((n - 2 * k : ℕ) : ℝ) / (n : ℝ)) ^ m * (n.descFactorial m : ℝ) := by
      positivity
    calc
      (((n - 2 * k : ℕ) : ℝ) / (n : ℝ)) ^ m * (((n - 2 * k : ℕ) : ℝ) / (n : ℝ)) *
          (((n - m : ℕ) : ℝ) * (n.descFactorial m : ℝ))
        = ((((n - 2 * k : ℕ) : ℝ) / (n : ℝ)) * ((n - m : ℕ) : ℝ)) *
            ((((n - 2 * k : ℕ) : ℝ) / (n : ℝ)) ^ m * (n.descFactorial m : ℝ)) := by ring
      _ ≤ ((n - k - m : ℕ) : ℝ) * ((n - k).descFactorial m : ℝ) :=
        mul_le_mul hstep ih' hnonneg (Nat.cast_nonneg _)

private lemma descFactorial_mul_factorial (n k : ℕ) (hkn : k ≤ n) :
    n.descFactorial k * (n - k).factorial = n.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : n - k = (n - (k + 1)) + 1 := by omega
    have hfac : (n - k) * (n - (k + 1)).factorial = (n - k).factorial := by
      conv_rhs => rw [h1, Nat.factorial_succ]
      rw [← h1]
    calc
      n.descFactorial (k + 1) * (n - (k + 1)).factorial
        = n.descFactorial k * ((n - k) * (n - (k + 1)).factorial) := by
          rw [Nat.descFactorial_succ]; ring
      _ = n.descFactorial k * (n - k).factorial := by rw [hfac]
      _ = n.factorial := ih (by omega)

private lemma rpow_le_k_div_two_n {n k : ℕ} (hn : 6 ^ 7 ≤ n) (h9k_sq : n ≤ 9 * (k * k)) :
    (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ (k : ℝ) / (2 * (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  apply le_of_pow_le_pow_left₀ (by norm_num : 50 ≠ 0) (by positivity)
  rw [← Real.rpow_natCast ((n : ℝ) ^ (-(33 : ℝ) / 50)) 50, ← Real.rpow_mul hn_pos.le]
  have hexp : (-(33 : ℝ) / 50) * (50 : ℕ) = (-33 : ℤ) := by norm_num
  rw [hexp, Real.rpow_intCast, zpow_neg, div_pow, mul_pow]
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (n : ℝ) ^ 25 ≤ (9 : ℝ) ^ 25 * (k : ℝ) ^ 50 := by
    have h9R : (n : ℝ) ≤ 9 * (k : ℝ) ^ 2 := by
      have : (n : ℝ) ≤ 9 * ((k * k : ℕ) : ℝ) := by exact_mod_cast h9k_sq
      push_cast at this
      linarith
    calc
      (n : ℝ) ^ 25 ≤ (9 * (k : ℝ) ^ 2) ^ 25 := pow_le_pow_left₀ hn_pos.le h9R 25
      _ = (9 : ℝ) ^ 25 * (k : ℝ) ^ 50 := by ring
  have h2 : (6 : ℝ) ^ 50 ≤ (n : ℝ) ^ 8 := by
    have hn6 : (6 : ℝ) ^ 7 ≤ (n : ℝ) := by exact_mod_cast hn
    calc
      (6 : ℝ) ^ 50 ≤ ((6 : ℝ) ^ 7) ^ 8 := by norm_num
      _ ≤ (n : ℝ) ^ 8 := pow_le_pow_left₀ (by positivity) hn6 8
  have h3 : (2 : ℝ) ^ 50 * (9 : ℝ) ^ 25 = (6 : ℝ) ^ 50 := by norm_num
  have h4 : (2 : ℝ) ^ 50 * (9 : ℝ) ^ 25 * (n : ℝ) ^ 50 ≤ (n : ℝ) ^ 8 * (n : ℝ) ^ 50 := by
    rw [h3]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have h5 : (n : ℝ) ^ 8 * (n : ℝ) ^ 50 = (n : ℝ) ^ 33 * (n : ℝ) ^ 25 := by ring
  have h6 : (n : ℝ) ^ 33 * (n : ℝ) ^ 25 ≤ (n : ℝ) ^ 33 * ((9 : ℝ) ^ 25 * (k : ℝ) ^ 50) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h7 : (9 : ℝ) ^ 25 * ((2 : ℝ) ^ 50 * (n : ℝ) ^ 50) ≤
      (9 : ℝ) ^ 25 * ((k : ℝ) ^ 50 * (n : ℝ) ^ 33) := by linarith
  have h8 : (2 : ℝ) ^ 50 * (n : ℝ) ^ 50 ≤ (k : ℝ) ^ 50 * (n : ℝ) ^ 33 :=
    le_of_mul_le_mul_left h7 (by positivity : (0 : ℝ) < (9 : ℝ) ^ 25)
  rw [one_mul]
  exact h8

private lemma combinatorial_ratio_ge {n k : ℕ} (h4k_sq : 4 * (k * k) ≤ n) (h2k_le : 2 * k + 1 ≤ n) :
    (k : ℝ) / (2 * (n : ℝ)) ≤
      ((k * (n - k).descFactorial k * (n - k - 1).factorial : ℕ) : ℝ) / (n.factorial : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hbernoulli : (1 / 2 : ℝ) ≤ (((n - 2 * k : ℕ) : ℝ) / (n : ℝ)) ^ k := by
    have hsub : (((n - 2 * k : ℕ) : ℝ) / (n : ℝ)) = 1 + (-(2 * (k : ℝ)) / (n : ℝ)) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      field_simp
      ring
    rw [hsub]
    have hge_neg1 : (-1 : ℝ) ≤ -(2 * (k : ℝ)) / (n : ℝ) := by
      rw [le_div_iff₀ hn_pos]
      have : (2 * k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 2 * k ≤ n by omega)
      linarith
    have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -(2 * (k : ℝ)) / (n : ℝ)) k
    have h2k2 : (k : ℝ) * (2 * (k : ℝ)) ≤ (n : ℝ) / 2 := by
      have : (4 * (k * k) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h4k_sq
      linarith
    have hdiv : (k : ℝ) * (2 * (k : ℝ)) / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hn_pos]
      linarith
    have heq : (k : ℝ) * (-(2 * (k : ℝ)) / (n : ℝ)) = -((k : ℝ) * (2 * (k : ℝ)) / (n : ℝ)) := by
      ring
    linarith
  have hhalf_desc : (1 / 2 : ℝ) * (n.descFactorial k : ℝ) ≤ ((n - k).descFactorial k : ℝ) := by
    calc
      (1 / 2 : ℝ) * (n.descFactorial k : ℝ)
        ≤ (((n - 2 * k : ℕ) : ℝ) / (n : ℝ)) ^ k * (n.descFactorial k : ℝ) :=
          mul_le_mul_of_nonneg_right hbernoulli (Nat.cast_nonneg _)
      _ ≤ ((n - k).descFactorial k : ℝ) :=
        descFactorial_ratio_lower (n := n) (k := k) (by omega) (by omega) k le_rfl
  rw [div_le_div_iff₀ (by positivity) hfac_pos]
  have hfac1 : (n - k) * (n - k - 1).factorial = (n - k).factorial := by
    have h1 : n - k = (n - k - 1) + 1 := by omega
    conv_rhs => rw [h1, Nat.factorial_succ]
    rw [← h1]
  have hfac1R : ((n - k : ℕ) : ℝ) * ((n - k - 1).factorial : ℝ) = ((n - k).factorial : ℝ) := by
    exact_mod_cast hfac1
  have hfac2R : (n.descFactorial k : ℝ) * ((n - k).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast descFactorial_mul_factorial n k (by omega)
  have hnk_le : ((n - k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n k
  push_cast
  have hmul1 :
      ((n - k : ℕ) : ℝ) * ((k : ℝ) * ((n - k).descFactorial k : ℝ) * ((n - k - 1).factorial : ℝ)) =
        (k : ℝ) * ((n - k).descFactorial k : ℝ) * ((n - k).factorial : ℝ) := by
    calc
      ((n - k : ℕ) : ℝ) * ((k : ℝ) * ((n - k).descFactorial k : ℝ) * ((n - k - 1).factorial : ℝ))
        = (k : ℝ) * ((n - k).descFactorial k : ℝ) *
            (((n - k : ℕ) : ℝ) * ((n - k - 1).factorial : ℝ)) := by ring
      _ = (k : ℝ) * ((n - k).descFactorial k : ℝ) * ((n - k).factorial : ℝ) := by rw [hfac1R]
  have hmul2 :
      (1 / 2 : ℝ) * (k : ℝ) * (n.factorial : ℝ) ≤
        (k : ℝ) * ((n - k).descFactorial k : ℝ) * ((n - k).factorial : ℝ) := by
    rw [← hfac2R]
    have ha := mul_le_mul_of_nonneg_left hhalf_desc (Nat.cast_nonneg k)
    have hb := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg (n - k).factorial)
    linarith
  have hmul3 :
      ((n - k : ℕ) : ℝ) * ((k : ℝ) * ((n - k).descFactorial k : ℝ) * ((n - k - 1).factorial : ℝ)) ≤
        (n : ℝ) * ((k : ℝ) * ((n - k).descFactorial k : ℝ) * ((n - k - 1).factorial : ℝ)) :=
    mul_le_mul_of_nonneg_right hnk_le (by positivity)
  linarith

private lemma density_lower_bound (n : ℕ) (hn : 6 ^ 7 ≤ n) :
    ∃ (x : Fin n) (I : Set (Fin n)),
      (n : ℝ) ^ (-(33 : ℝ) / 50) ≤
        ((extremalFamily x I).ncard : ℝ) / Fintype.card (alternatingGroup (Fin n)) := by
  let k : ℕ := Nat.sqrt (n / 4)
  have hk_sq : k * k ≤ n / 4 := Nat.sqrt_le (n / 4)
  have hk_gt : n / 4 < (k + 1) * (k + 1) := Nat.lt_succ_sqrt (n / 4)
  have hk_ge : 2 ≤ k := Nat.le_sqrt.mpr (by omega)
  have h4k_sq : 4 * (k * k) ≤ n := by omega
  have h9k_sq : n ≤ 9 * (k * k) := by
    have h1 : n < 4 * ((k + 1) * (k + 1)) := by omega
    nlinarith
  have h2k_le : 2 * k + 3 ≤ n := by nlinarith
  let x : Fin n := ⟨0, by omega⟩
  let Ifin : Finset (Fin n) := Finset.univ.filter (fun j => 1 ≤ j.val ∧ j.val ≤ k)
  refine ⟨x, (Ifin : Set (Fin n)), ?_⟩
  let u : Fin n := ⟨k + 1, by omega⟩
  let v : Fin n := ⟨k + 2, by omega⟩
  have heven := two_mul_ncard_extremalFamily x (Ifin : Set (Fin n)) u v
    (by simp [u, v]) (by simp [u, x]) (by simp [v, x]) (by simp [Ifin, u]) (by simp [Ifin, v])
  have halt := two_mul_card_alternatingGroup (n := n) (by omega)
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hratio_eq :
      ((extremalFamily x (Ifin : Set (Fin n))).ncard : ℝ) /
          (Fintype.card (alternatingGroup (Fin n)) : ℝ) =
        ((permExtremal x (Ifin : Set (Fin n))).card : ℝ) / (n.factorial : ℝ) := by
    have h1 : (2 : ℝ) * ((extremalFamily x (Ifin : Set (Fin n))).ncard : ℝ) =
        ((permExtremal x (Ifin : Set (Fin n))).card : ℝ) := by exact_mod_cast heven
    have h2 : (2 : ℝ) * (Fintype.card (alternatingGroup (Fin n)) : ℝ) =
        (n.factorial : ℝ) := by exact_mod_cast halt
    have halt_pos : (0 : ℝ) < (Fintype.card (alternatingGroup (Fin n)) : ℝ) := by linarith
    rw [div_eq_div_iff halt_pos.ne' hfac_pos.ne']
    nlinarith
  rw [hratio_eq]
  have hcard_ge :
      ((k * (n - k).descFactorial k * (n - k - 1).factorial : ℕ) : ℝ) ≤
        ((permExtremal x (Ifin : Set (Fin n))).card : ℝ) := by
    exact_mod_cast card_permExtremal_ge (n := n) (k := k) (by omega) (by omega)
  exact (rpow_le_k_div_two_n hn h9k_sq).trans
    ((combinatorial_ratio_ge h4k_sq (by omega)).trans
      (div_le_div_of_nonneg_right hcard_ge hfac_pos.le))

end OMA.Green4H1

theorem OMA.solution : OMA.R_Green4_large_green_4_R1.H1 := by
  rw [OMA.R_Green4_large_green_4_R1.H1, Filter.eventually_atTop]
  exact ⟨6 ^ 7, OMA.Green4H1.density_lower_bound⟩
