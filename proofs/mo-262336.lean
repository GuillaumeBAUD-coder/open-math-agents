import OMAStatements.S_mo_262336

-- Problem: Permanent of distorted matrix
-- Upstream: formal-conjectures statements/mo-262336.lean:0 (declaration OMA.S_mo_262336.main)
-- Credit: @umarsxlim (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

private def restrictPerm {n : ℕ} (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) : S ↪ Fin n :=
  ⟨fun i => σ i.1, fun _ _ h => Subtype.ext (σ.injective h)⟩

private lemma card_subtype_not_mem {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card {x : Fin n // x ∉ S} = n - S.card := by
  have h1 : Fintype.card {x : Fin n // x ∉ S} = Sᶜ.card := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ⟨fun x => ⟨x.1, Finset.mem_compl.mpr x.2⟩,
      fun x => ⟨x.1, Finset.mem_compl.mp x.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [h1, Finset.card_compl, Fintype.card_fin]

private noncomputable def fiberEquiv {n : ℕ} (S : Finset (Fin n)) (e : S ↪ Fin n) :
    {σ : Equiv.Perm (Fin n) // restrictPerm S σ = e} ≃
      ({x : Fin n // x ∉ S} ≃ {y : Fin n // y ∉ (Finset.univ : Finset S).image e}) :=
  { toFun := fun ⟨σ, hσ⟩ =>
      { toFun := fun ⟨x, hx⟩ => ⟨σ x, by
          intro hT
          rcases Finset.mem_image.mp hT with ⟨i, _, hi⟩
          have hσi : σ i.1 = e i := congrFun (congrArg DFunLike.coe hσ) i
          have heq : i.1 = x := σ.injective (hσi.trans hi)
          exact hx (heq ▸ i.2)⟩
        invFun := fun ⟨y, hy⟩ => ⟨σ.symm y, by
          intro hS
          have hσi : σ (σ.symm y) = e ⟨σ.symm y, hS⟩ :=
            congrFun (congrArg DFunLike.coe hσ) ⟨σ.symm y, hS⟩
          rw [σ.apply_symm_apply] at hσi
          exact hy (hσi ▸ Finset.mem_image_of_mem e (Finset.mem_univ _))⟩
        left_inv := fun ⟨x, _⟩ => Subtype.ext (σ.symm_apply_apply x)
        right_inv := fun ⟨y, _⟩ => Subtype.ext (σ.apply_symm_apply y) }
    invFun := fun g =>
      let f : Fin n → Fin n := fun x => if hx : x ∈ S then e ⟨x, hx⟩ else (g ⟨x, hx⟩).1
      have hf : Function.Injective f := by
        intro x y hxy
        dsimp only [f] at hxy
        split_ifs at hxy with hx hy hy
        · exact congrArg Subtype.val (e.injective hxy)
        · exfalso
          exact (g ⟨y, hy⟩).2 (hxy ▸ Finset.mem_image_of_mem e (Finset.mem_univ (⟨x, hx⟩ : S)))
        · exfalso
          exact (g ⟨x, hx⟩).2 (hxy.symm ▸ Finset.mem_image_of_mem e (Finset.mem_univ (⟨y, hy⟩ : S)))
        · exact congrArg Subtype.val (g.injective (Subtype.ext hxy))
      ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf),
        Function.Embedding.ext fun i => by
          change f i.1 = e i
          simp only [f, i.2, ↓reduceDIte]⟩
    left_inv := fun ⟨σ, hσ⟩ => by
      apply Subtype.ext
      apply Equiv.ext
      intro x
      change (if hx : x ∈ S then e ⟨x, hx⟩ else σ x) = σ x
      split_ifs with hx
      · exact (congrFun (congrArg DFunLike.coe hσ) ⟨x, hx⟩).symm
      · rfl
    right_inv := fun g => by
      apply Equiv.ext
      rintro ⟨x, hx⟩
      apply Subtype.ext
      change (if hx' : x ∈ S then e ⟨x, hx'⟩ else (g ⟨x, hx'⟩).1) = (g ⟨x, hx⟩).1
      simp only [hx, ↓reduceDIte] }

private lemma card_fiber_restrictPerm {n : ℕ} (S : Finset (Fin n)) (e : S ↪ Fin n) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => restrictPerm S σ = e).card =
      (n - S.card).factorial := by
  let T : Finset (Fin n) := Finset.univ.image e
  have hTcard : T.card = S.card := by
    rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ, Fintype.card_coe]
  have hcards : Fintype.card {x : Fin n // x ∉ S} = Fintype.card {y : Fin n // y ∉ T} := by
    rw [card_subtype_not_mem S, card_subtype_not_mem T, hTcard]
  have α : {x : Fin n // x ∉ S} ≃ {y : Fin n // y ∉ T} := Fintype.equivOfCardEq hcards
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {σ : Equiv.Perm (Fin n) // restrictPerm S σ = e}
      = Fintype.card ({x : Fin n // x ∉ S} ≃ {y : Fin n // y ∉ T}) :=
          Fintype.card_congr (fiberEquiv S e)
    _ = Fintype.card (Equiv.Perm {x : Fin n // x ∉ S}) :=
          Fintype.card_congr (Equiv.equivCongr (Equiv.refl _) α.symm)
    _ = (Fintype.card {x : Fin n // x ∉ S}).factorial := Fintype.card_perm
    _ = (n - S.card).factorial := by rw [card_subtype_not_mem S]

private lemma sum_perm_fin2 {R : Type*} [AddCommMonoid R] (f : Equiv.Perm (Fin 2) → R) :
    ∑ σ : Equiv.Perm (Fin 2), f σ = f 1 + f (Equiv.swap 0 1) := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
    ext σ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases h0 : σ 0 = 0
    · left
      ext i
      fin_cases i
      · simp [h0]
      · by_cases h1 : σ 1 = 0
        · exact absurd (σ.injective (h1.trans h0.symm)) (by decide)
        · have h1' : σ 1 = 1 := by
            have hlt := (σ 1).isLt
            have hval : (σ 1).val ≠ 0 := fun hv => h1 (Fin.ext hv)
            exact Fin.ext (by omega)
          simp [h1']
    · right
      have h0' : σ 0 = 1 := by
        have hlt := (σ 0).isLt
        have hval : (σ 0).val ≠ 0 := fun hv => h0 (Fin.ext hv)
        exact Fin.ext (by omega)
      ext i
      fin_cases i
      · simp [h0']
      · by_cases h1 : σ 1 = 1
        · exact absurd (σ.injective (h1.trans h0'.symm)) (by decide)
        · have h1' : σ 1 = 0 := by
            have hlt := (σ 1).isLt
            have hval : (σ 1).val ≠ 1 := fun hv => h1 (Fin.ext hv)
            exact Fin.ext (by omega)
          simp [h1']
  rw [huniv, Finset.sum_pair (by decide)]

theorem OMA.solution : type_of% @OMA.S_mo_262336.main := by
  constructor
  · intro R _ n M a
    unfold OMA.S_mo_262336.perm OMA.S_mo_262336.minors
    have hexpand : ∀ σ : Equiv.Perm (Fin n),
        ∏ i : Fin n, (M i (σ i) + (a : R)) =
          ∑ S : Finset (Fin n), (∏ i ∈ S, M i (σ i)) * (a : R) ^ (n - S.card) := by
      intro σ
      rw [Finset.prod_add, Finset.powerset_univ]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← Finset.sum_mul,
      ← Finset.sum_fiberwise_of_maps_to (g := restrictPerm S) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
    have hfib : ∀ e : S ↪ Fin n,
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => restrictPerm S σ = e),
          ∏ i ∈ S, M i (σ i) =
          ((n - S.card).factorial : R) * ∏ i : S, M i (e i) := by
      intro e
      have hterm : ∀ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => restrictPerm S σ = e),
          ∏ i ∈ S, M i (σ i) = ∏ i : S, M i (e i) := by
        intro σ hσ
        have heq : restrictPerm S σ = e := (Finset.mem_filter.mp hσ).2
        rw [← Finset.prod_coe_sort S (fun i => M i (σ i))]
        refine Finset.prod_congr rfl fun i _ => ?_
        have hi : σ i.1 = e i := congrFun (congrArg DFunLike.coe heq) i
        rw [hi]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, card_fiber_restrictPerm]
    simp_rw [hfib]
    rw [← Finset.mul_sum]
    ring
  · intro a ha
    refine ⟨!![0, 0; 0, 0], !![1, 0; 0, 0], ?_, ?_⟩
    · simp [OMA.S_mo_262336.perm, sum_perm_fin2, Fin.prod_univ_two]
    · simp only [OMA.S_mo_262336.perm, sum_perm_fin2, Fin.prod_univ_two,
        Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      intro h
      ring_nf at h
      exact ha (by linarith)
