import OMAStatements.S_mo_119430

open OMA.S_mo_119430

private abbrev Triple (m : ℕ) := (Fin m → ℂ) × (Fin m → ℂ) × (Fin m → ℂ)

private def shift (m : ℕ) : Module.End ℂ (Fin m → ℂ) where
  toFun x i := if h : i.val + 1 < m then x ⟨i.val + 1, h⟩ else 0
  map_add' x y := by
    ext i
    by_cases h : i.val + 1 < m <;> simp [h]
  map_smul' c x := by
    ext i
    by_cases h : i.val + 1 < m <;> simp [h]

private lemma shift_single_zero {m : ℕ} (hm : 0 < m) :
    shift m (Pi.single ⟨0, hm⟩ (1 : ℂ)) = 0 := by
  ext i
  simp only [shift, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  split_ifs with h
  · rw [Pi.single_apply, if_neg]
    intro heq
    have : i.val + 1 = 0 := congrArg Fin.val heq
    omega
  · rfl

private lemma shift_single_succ {m : ℕ} (r : ℕ) (hr : r + 1 < m) :
    shift m (Pi.single ⟨r + 1, hr⟩ (1 : ℂ)) =
      Pi.single ⟨r, Nat.lt_of_succ_lt hr⟩ (1 : ℂ) := by
  ext i
  simp only [shift, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with h
  · simp only [Pi.single_apply]
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2; ext; exact Nat.succ.inj (congrArg Fin.val h1)
    · exfalso; apply h1; ext; simp [congrArg Fin.val h2]
    · rfl
  · rw [Pi.single_apply, if_neg]
    intro heq
    have : i.val = r := congrArg Fin.val heq
    omega

private lemma eq_smul_single_zero_of_shift_eq_zero {m : ℕ} (hm : 0 < m)
    {v : Fin m → ℂ} (hv : shift m v = 0) :
    v = v ⟨0, hm⟩ • Pi.single ⟨0, hm⟩ (1 : ℂ) := by
  ext j
  by_cases hj : j.val = 0
  · have hjeq : j = ⟨0, hm⟩ := Fin.ext hj
    subst hjeq
    simp
  · have hpos : 0 < j.val := Nat.pos_of_ne_zero hj
    let p : ℕ := j.val - 1
    have hp : p + 1 = j.val := Nat.succ_pred_eq_of_pos hpos
    have hlt : p + 1 < m := by rw [hp]; exact j.isLt
    have h0 : shift m v ⟨p, Nat.lt_of_succ_lt hlt⟩ = 0 := by rw [hv]; rfl
    simp only [shift, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hlt] at h0
    have hidx : (⟨p + 1, hlt⟩ : Fin m) = j := Fin.ext hp
    rw [hidx] at h0
    rw [h0, Pi.smul_apply, Pi.single_apply, if_neg]
    · simp
    · intro heq
      exact hj (congrArg Fin.val heq)

private lemma eq_zero_of_idem_comm_shift_zero {m : ℕ} (hm : 0 < m)
    (D : Module.End ℂ (Fin m → ℂ))
    (hD2 : D ∘ₗ D = D) (hDJ : D ∘ₗ shift m = shift m ∘ₗ D)
    (hD0 : D (Pi.single ⟨0, hm⟩ (1 : ℂ)) = 0) :
    D = 0 := by
  have hsingle : ∀ (r : ℕ) (hr : r < m), D (Pi.single ⟨r, hr⟩ (1 : ℂ)) = 0 := by
    intro r
    induction r with
    | zero =>
      intro hr
      exact hD0
    | succ r ih =>
      intro hr
      have hshift : shift m (D (Pi.single ⟨r + 1, hr⟩ (1 : ℂ))) = 0 := by
        have h1 := congrArg (fun f => f (Pi.single ⟨r + 1, hr⟩ (1 : ℂ))) hDJ
        simp only [LinearMap.comp_apply] at h1
        rw [← h1, shift_single_succ r hr, ih (Nat.lt_of_succ_lt hr)]
      have hker := eq_smul_single_zero_of_shift_eq_zero hm hshift
      have h2 := congrArg (fun f => f (Pi.single ⟨r + 1, hr⟩ (1 : ℂ))) hD2
      simp only [LinearMap.comp_apply] at h2
      rw [← h2]
      conv_lhs => rw [hker]
      rw [map_smul, hD0, smul_zero]
  apply LinearMap.ext
  intro v
  have hv : v = ∑ i : Fin m, v i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  simp only [map_smul, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [show i = ⟨i.val, i.isLt⟩ from rfl, hsingle i.val i.isLt, smul_zero]

private lemma idem_comm_shift_eq_zero_or_one {m : ℕ} (hm : 0 < m)
    (C : Module.End ℂ (Fin m → ℂ))
    (hC2 : C ∘ₗ C = C) (hCJ : C ∘ₗ shift m = shift m ∘ₗ C) :
    C = 0 ∨ C = LinearMap.id := by
  let e0 : Fin m → ℂ := Pi.single ⟨0, hm⟩ (1 : ℂ)
  have hshift : shift m (C e0) = 0 := by
    have h1 := congrArg (fun f => f e0) hCJ
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, shift_single_zero hm, map_zero]
  have hker := eq_smul_single_zero_of_shift_eq_zero hm hshift
  set c : ℂ := C e0 ⟨0, hm⟩
  have hidem : C (C e0) = C e0 := by
    have h1 := congrArg (fun f => f e0) hC2
    simpa [LinearMap.comp_apply] using h1
  have hc2 : c * c = c := by
    have h1 : (C (c • e0)) ⟨0, hm⟩ = (c • e0) ⟨0, hm⟩ := by
      rw [← hker, hidem]
    rw [map_smul, hker, smul_smul] at h1
    simpa [e0] using h1
  have hc01 : c = 0 ∨ c = 1 := by
    have hsub : c * (c - 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp hsub with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  rcases hc01 with hc0 | hc1
  · left
    apply eq_zero_of_idem_comm_shift_zero hm C hC2 hCJ
    rw [hker, hc0, zero_smul]
  · right
    have hsub : LinearMap.id - C = 0 := by
      apply eq_zero_of_idem_comm_shift_zero hm (LinearMap.id - C)
      · apply LinearMap.ext
        intro v
        have hvv : C (C v) = C v := by
          have h1 := congrArg (fun f => f v) hC2
          simpa [LinearMap.comp_apply] using h1
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hvv]
        abel
      · apply LinearMap.ext
        intro v
        have h1 := congrArg (fun f => f v) hCJ
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub] at h1 ⊢
        rw [h1]
      · simp only [LinearMap.sub_apply, LinearMap.id_apply]
        rw [hker, hc1, one_smul, sub_self]
    exact (sub_eq_zero.mp hsub).symm

private def A0 (m : ℕ) : Module.End ℂ (Triple m) where
  toFun v := (0, v.2.1, -v.2.2)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' c x := by ext <;> simp

private lemma A0_cube (m : ℕ) : A0 m ^ 3 = A0 m := by
  apply LinearMap.ext
  intro v
  simp only [pow_three, Module.End.mul_apply]
  ext <;> simp [A0]

private def Pmap (m : ℕ) : Module.End ℂ (Triple m) where
  toFun v := (v.1 + v.2.1, v.2.1 + v.2.2, shift m v.1 + v.2.2)
  map_add' x y := by
    ext i <;> simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add] <;> ring
  map_smul' c x := by
    ext <;> simp [map_smul]

private lemma eq_zero_of_shift_eq_neg {m : ℕ} {x : Fin m → ℂ}
    (hx : shift m x = -x) : x = 0 := by
  have hstep : ∀ d : ℕ, ∀ i : Fin m, i.val + d = m → x i = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi
      omega
    | succ d ih =>
      intro i hi
      have h0 : shift m x i = -x i := congrFun hx i
      by_cases hlt : i.val + 1 < m
      · simp only [shift, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hlt] at h0
        have hnext : x ⟨i.val + 1, hlt⟩ = 0 := ih ⟨i.val + 1, hlt⟩ (by dsimp; omega)
        rw [hnext] at h0
        exact neg_eq_zero.mp h0.symm
      · simp only [shift, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hlt] at h0
        exact neg_eq_zero.mp h0.symm
  ext i
  exact hstep (m - i.val) i (by omega)

private lemma Pmap_injective (m : ℕ) : Function.Injective (Pmap m) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h1 : v.1 + v.2.1 = 0 := congrArg Prod.fst hv
  have h2 : v.2.1 + v.2.2 = 0 := congrArg (fun p => p.2.1) hv
  have h3 : shift m v.1 + v.2.2 = 0 := congrArg (fun p => p.2.2) hv
  have hv21 : v.2.1 = -v.1 := eq_neg_of_add_eq_zero_right h1
  have hv22 : v.2.2 = v.1 := by
    rw [hv21] at h2
    exact (eq_of_neg_add_eq_zero h2).symm
  rw [hv22] at h3
  have hx : v.1 = 0 := eq_zero_of_shift_eq_neg (eq_neg_of_add_eq_zero_left h3)
  ext <;> simp [hv21, hv22, hx]

private noncomputable def Pequiv (m : ℕ) : Triple m ≃ₗ[ℂ] Triple m :=
  LinearEquiv.ofBijective (Pmap m)
    ⟨Pmap_injective m, LinearMap.injective_iff_surjective.mp (Pmap_injective m)⟩

private noncomputable def B0 (m : ℕ) : Module.End ℂ (Triple m) :=
  (Pequiv m).toLinearMap ∘ₗ A0 m ∘ₗ (Pequiv m).symm.toLinearMap

private lemma B0_cube (m : ℕ) : B0 m ^ 3 = B0 m := by
  apply LinearMap.ext
  intro v
  have hAv : A0 m (A0 m (A0 m ((Pequiv m).symm v))) = A0 m ((Pequiv m).symm v) := by
    have := congrArg (fun f => f ((Pequiv m).symm v)) (A0_cube m)
    simpa [pow_three, Module.End.mul_apply] using this
  simp only [pow_three, Module.End.mul_apply, B0, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [hAv]

private lemma comm_A0_blocks {m : ℕ} (f : Module.End ℂ (Triple m))
    (hf : f ∘ₗ A0 m = A0 m ∘ₗ f) :
    ∃ C1 C2 C3 : Module.End ℂ (Fin m → ℂ),
      ∀ x y z, f (x, y, z) = (C1 x, C2 y, C3 z) := by
  let inl1 : (Fin m → ℂ) →ₗ[ℂ] Triple m :=
    { toFun := fun x => (x, 0, 0)
      map_add' := fun _ _ => by ext <;> simp
      map_smul' := fun _ _ => by ext <;> simp }
  let inl2 : (Fin m → ℂ) →ₗ[ℂ] Triple m :=
    { toFun := fun y => (0, y, 0)
      map_add' := fun _ _ => by ext <;> simp
      map_smul' := fun _ _ => by ext <;> simp }
  let inl3 : (Fin m → ℂ) →ₗ[ℂ] Triple m :=
    { toFun := fun z => (0, 0, z)
      map_add' := fun _ _ => by ext <;> simp
      map_smul' := fun _ _ => by ext <;> simp }
  let p1 : Triple m →ₗ[ℂ] (Fin m → ℂ) := LinearMap.fst ℂ _ _
  let p2 : Triple m →ₗ[ℂ] (Fin m → ℂ) :=
    (LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)
  let p3 : Triple m →ₗ[ℂ] (Fin m → ℂ) :=
    (LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)
  refine ⟨p1 ∘ₗ f ∘ₗ inl1, p2 ∘ₗ f ∘ₗ inl2, p3 ∘ₗ f ∘ₗ inl3, fun x y z => ?_⟩
  have h1 : f (x, 0, 0) = (p1 (f (inl1 x)), 0, 0) := by
    have h0 := congrArg (fun g => g (x, 0, 0)) hf
    simp only [LinearMap.comp_apply] at h0
    have hAz : A0 m (x, 0, 0) = 0 := by ext <;> simp [A0]
    rw [hAz, map_zero] at h0
    have h21 : (f (x, 0, 0)).2.1 = 0 :=
      (congrArg (fun u => u.2.1) h0).symm
    have h22 : (f (x, 0, 0)).2.2 = 0 :=
      neg_eq_zero.mp (congrArg (fun u => u.2.2) h0).symm
    ext <;> simp [p1, inl1, h21, h22]
  have h2 : f (0, y, 0) = (0, p2 (f (inl2 y)), 0) := by
    have h0 := congrArg (fun g => g (0, y, 0)) hf
    simp only [LinearMap.comp_apply] at h0
    have hAy : A0 m (0, y, 0) = (0, y, 0) := by ext <;> simp [A0]
    rw [hAy] at h0
    have h10 : (f (0, y, 0)).1 = 0 := by
      have hcomp := congrArg Prod.fst h0
      change (f (0, y, 0)).1 = 0 at hcomp
      exact hcomp
    have h22 : (f (0, y, 0)).2.2 = 0 := by
      have hcomp := congrArg (fun u => u.2.2) h0
      change (f (0, y, 0)).2.2 = -(f (0, y, 0)).2.2 at hcomp
      ext i
      have hi : (f (0, y, 0)).2.2 i = -(f (0, y, 0)).2.2 i := congrFun hcomp i
      have hi2 : (2 : ℂ) * (f (0, y, 0)).2.2 i = 0 := by linear_combination hi
      exact (mul_eq_zero.mp hi2).resolve_left (by norm_num)
    ext <;> simp [p2, inl2, h10, h22]
  have h3 : f (0, 0, z) = (0, 0, p3 (f (inl3 z))) := by
    have h0 := congrArg (fun g => g (0, 0, z)) hf
    simp only [LinearMap.comp_apply] at h0
    have hAz : A0 m (0, 0, z) = -(0, 0, z) := by ext <;> simp [A0]
    rw [hAz, map_neg] at h0
    have h10 : (f (0, 0, z)).1 = 0 := by
      have hcomp := congrArg Prod.fst h0
      change -(f (0, 0, z)).1 = 0 at hcomp
      exact neg_eq_zero.mp hcomp
    have h21 : (f (0, 0, z)).2.1 = 0 := by
      have hcomp := congrArg (fun u => u.2.1) h0
      change -(f (0, 0, z)).2.1 = (f (0, 0, z)).2.1 at hcomp
      ext i
      have hi : -(f (0, 0, z)).2.1 i = (f (0, 0, z)).2.1 i := congrFun hcomp i
      have hi2 : (2 : ℂ) * (f (0, 0, z)).2.1 i = 0 := by linear_combination -hi
      exact (mul_eq_zero.mp hi2).resolve_left (by norm_num)
    ext <;> simp [p3, inl3, h10, h21]
  have hsum : (x, y, z) = (x, 0, 0) + ((0, y, 0) + (0, 0, z)) := by ext <;> simp
  rw [hsum, map_add, map_add, h1, h2, h3]
  ext <;> simp

private lemma proj_comm_A0_B0_eq_zero_or_id {m : ℕ} (hm : 0 < m)
    (π : Module.End ℂ (Triple m))
    (hπ2 : π ∘ₗ π = π)
    (hπA : π ∘ₗ A0 m = A0 m ∘ₗ π)
    (hπB : π ∘ₗ B0 m = B0 m ∘ₗ π) :
    π = 0 ∨ π = LinearMap.id := by
  obtain ⟨C1, C2, C3, hC⟩ := comm_A0_blocks π hπA
  let π' : Module.End ℂ (Triple m) :=
    (Pequiv m).symm.toLinearMap ∘ₗ π ∘ₗ (Pequiv m).toLinearMap
  have hπ'A : π' ∘ₗ A0 m = A0 m ∘ₗ π' := by
    apply LinearMap.ext
    intro v
    have hB := congrArg (fun g => g (Pequiv m v)) hπB
    simp only [LinearMap.comp_apply, B0, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at hB
    have hB' := congrArg (Pequiv m).symm hB
    simpa [π'] using hB'
  obtain ⟨D1, D2, D3, hD⟩ := comm_A0_blocks π' hπ'A
  have hPD : ∀ x y z, π (Pmap m (x, y, z)) = Pmap m (D1 x, D2 y, D3 z) := by
    intro x y z
    have h1 : π' (x, y, z) = (D1 x, D2 y, D3 z) := hD x y z
    have h2 := congrArg (Pequiv m) h1
    simp only [π', LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] at h2
    exact h2
  have hC1D1 : ∀ x, C1 x = D1 x := fun x => by
    have h := hPD x 0 0
    simp only [Pmap, LinearMap.coe_mk, AddHom.coe_mk, add_zero, map_zero] at h
    rw [hC] at h
    exact congrArg Prod.fst h
  have hC3J : ∀ x, C3 (shift m x) = shift m (D1 x) := fun x => by
    have h := hPD x 0 0
    simp only [Pmap, LinearMap.coe_mk, AddHom.coe_mk, add_zero, map_zero] at h
    rw [hC] at h
    exact congrArg (fun u => u.2.2) h
  have hC1D2 : ∀ y, C1 y = D2 y := fun y => by
    have h := hPD 0 y 0
    simp only [Pmap, LinearMap.coe_mk, AddHom.coe_mk, zero_add, add_zero, map_zero] at h
    rw [hC] at h
    exact congrArg Prod.fst h
  have hC2D2 : ∀ y, C2 y = D2 y := fun y => by
    have h := hPD 0 y 0
    simp only [Pmap, LinearMap.coe_mk, AddHom.coe_mk, zero_add, add_zero, map_zero] at h
    rw [hC] at h
    exact congrArg (fun u => u.2.1) h
  have hC2D3 : ∀ z, C2 z = D3 z := fun z => by
    have h := hPD 0 0 z
    simp only [Pmap, LinearMap.coe_mk, AddHom.coe_mk, zero_add, map_zero] at h
    rw [hC] at h
    exact congrArg (fun u => u.2.1) h
  have hC3D3 : ∀ z, C3 z = D3 z := fun z => by
    have h := hPD 0 0 z
    simp only [Pmap, LinearMap.coe_mk, AddHom.coe_mk, zero_add, map_zero] at h
    rw [hC] at h
    exact congrArg (fun u => u.2.2) h
  have hC2eq : C2 = C1 := by
    apply LinearMap.ext
    intro v
    rw [hC2D2 v, ← hC1D2 v]
  have hC3eq : C3 = C1 := by
    apply LinearMap.ext
    intro v
    rw [hC3D3 v, ← hC2D3 v, hC2eq]
  have hC1J : C1 ∘ₗ shift m = shift m ∘ₗ C1 := by
    apply LinearMap.ext
    intro x
    calc C1 (shift m x) = C3 (shift m x) := by rw [hC3eq]
      _ = shift m (D1 x) := hC3J x
      _ = shift m (C1 x) := by rw [← hC1D1 x]
  have hC1_idem : C1 ∘ₗ C1 = C1 := by
    apply LinearMap.ext
    intro x
    have h := congrArg (fun g => (g (x, 0, 0)).1) hπ2
    simp only [LinearMap.comp_apply, hC] at h
    exact h
  rcases idem_comm_shift_eq_zero_or_one hm C1 hC1_idem hC1J with h0 | h1
  · left
    apply LinearMap.ext
    intro v
    have hv : π v = (C1 v.1, C2 v.2.1, C3 v.2.2) := hC v.1 v.2.1 v.2.2
    rw [hv, hC2eq, hC3eq, h0]
    simp
  · right
    apply LinearMap.ext
    intro v
    have hv : π v = (C1 v.1, C2 v.2.1, C3 v.2.2) := hC v.1 v.2.1 v.2.2
    rw [hv, hC2eq, hC3eq, h1]
    simp

private noncomputable def tripleEquiv (m : ℕ) : Triple m ≃ₗ[ℂ] (Fin (3 * m) → ℂ) where
  toFun v idx :=
    match finProdFinEquiv.symm idx with
    | (0, j) => v.1 j
    | (1, j) => v.2.1 j
    | (2, j) => v.2.2 j
  invFun w :=
    (fun j => w (finProdFinEquiv (0, j)),
     fun j => w (finProdFinEquiv (1, j)),
     fun j => w (finProdFinEquiv (2, j)))
  left_inv v := by
    ext j <;> simp
  right_inv w := by
    ext idx
    rcases h : finProdFinEquiv.symm idx with ⟨a, j⟩
    have hidx : idx = finProdFinEquiv (a, j) := by
      rw [← h, Equiv.apply_symm_apply]
    fin_cases a <;> simp [hidx]
  map_add' x y := by
    ext idx
    simp only [Pi.add_apply]
    generalize finProdFinEquiv.symm idx = p
    rcases p with ⟨a, j⟩
    fin_cases a <;> rfl
  map_smul' c x := by
    ext idx
    simp only [Pi.smul_apply, RingHom.id_apply]
    generalize finProdFinEquiv.symm idx = p
    rcases p with ⟨a, j⟩
    fin_cases a <;> rfl

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_119430.main) := by
  intro hmain
  rcases hmain with ⟨k, hk⟩
  let m : ℕ := k + 1
  have hm : 0 < m := Nat.succ_pos k
  let e : Triple m ≃ₗ[ℂ] (Fin (3 * m) → ℂ) := tripleEquiv m
  let A : Module.End ℂ (Fin (3 * m) → ℂ) := e.toLinearMap ∘ₗ A0 m ∘ₗ e.symm.toLinearMap
  let B : Module.End ℂ (Fin (3 * m) → ℂ) := e.toLinearMap ∘ₗ B0 m ∘ₗ e.symm.toLinearMap
  have hA3 : A ^ 3 = A := by
    apply LinearMap.ext
    intro v
    have hAv : A0 m (A0 m (A0 m (e.symm v))) = A0 m (e.symm v) := by
      have := congrArg (fun f => f (e.symm v)) (A0_cube m)
      simpa [pow_three, Module.End.mul_apply] using this
    simp only [pow_three, Module.End.mul_apply, A, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hAv]
  have hB3 : B ^ 3 = B := by
    apply LinearMap.ext
    intro v
    have hBv : B0 m (B0 m (B0 m (e.symm v))) = B0 m (e.symm v) := by
      have := congrArg (fun f => f (e.symm v)) (B0_cube m)
      simpa [pow_three, Module.End.mul_apply] using this
    simp only [pow_three, Module.End.mul_apply, B, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hBv]
  obtain ⟨r, V, hV, hVprop⟩ := hk (3 * m) A B hA3 hB3
  let eV := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
  let proj : Fin r → Module.End ℂ (Fin (3 * m) → ℂ) := fun i =>
    (V i).subtype ∘ₗ DirectSum.component ℂ (Fin r) (fun j => V j) i ∘ₗ eV.symm.toLinearMap
  have hproj_mem : ∀ (i : Fin r) (x : Fin (3 * m) → ℂ), proj i x ∈ V i := fun i x =>
    (eV.symm x i).2
  have hproj_self : ∀ (i : Fin r) {x : Fin (3 * m) → ℂ}, x ∈ V i → proj i x = x := by
    intro i x hx
    change ((V i).subtype) ((eV.symm x) i) = x
    rw [hV.ofBijective_coeLinearMap_of_mem hx]
    rfl
  have hproj_ne : ∀ {i j : Fin r} (hij : i ≠ j) {x : Fin (3 * m) → ℂ},
      x ∈ V j → proj i x = 0 := by
    intro i j hij x hx
    change ((V i).subtype) ((eV.symm x) i) = 0
    rw [hV.ofBijective_coeLinearMap_of_mem_ne hij.symm hx]
    simp
  have hproj_idem : ∀ i, proj i ∘ₗ proj i = proj i := by
    intro i
    apply LinearMap.ext
    intro x
    exact hproj_self i (hproj_mem i x)
  have hproj_commA : ∀ i, proj i ∘ₗ A = A ∘ₗ proj i := by
    intro i
    apply LinearMap.ext
    intro x
    change proj i (A x) = A (proj i x)
    have hx : x = DirectSum.coeLinearMap V (eV.symm x) := (eV.apply_symm_apply x).symm
    rw [hx]
    induction eV.symm x using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [DirectSum.coeLinearMap_of]
      by_cases hij : j = i
      · subst hij
        rw [hproj_self j y.2, hproj_self j ((hVprop j).2.1 y.1 y.2)]
      · rw [hproj_ne (Ne.symm hij) y.2, map_zero,
          hproj_ne (Ne.symm hij) ((hVprop j).2.1 y.1 y.2)]
    | add a b ha hb =>
      simp only [map_add] at ha hb ⊢
      rw [ha, hb]
  have hproj_commB : ∀ i, proj i ∘ₗ B = B ∘ₗ proj i := by
    intro i
    apply LinearMap.ext
    intro x
    change proj i (B x) = B (proj i x)
    have hx : x = DirectSum.coeLinearMap V (eV.symm x) := (eV.apply_symm_apply x).symm
    rw [hx]
    induction eV.symm x using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      rw [DirectSum.coeLinearMap_of]
      by_cases hij : j = i
      · subst hij
        rw [hproj_self j y.2, hproj_self j ((hVprop j).2.2 y.1 y.2)]
      · rw [hproj_ne (Ne.symm hij) y.2, map_zero,
          hproj_ne (Ne.symm hij) ((hVprop j).2.2 y.1 y.2)]
    | add a b ha hb =>
      simp only [map_add] at ha hb ⊢
      rw [ha, hb]
  have hproj_zero_or_id : ∀ i, proj i = 0 ∨ proj i = LinearMap.id := by
    intro i
    let π0 : Module.End ℂ (Triple m) :=
      e.symm.toLinearMap ∘ₗ proj i ∘ₗ e.toLinearMap
    have hπ0_idem : π0 ∘ₗ π0 = π0 := by
      apply LinearMap.ext
      intro v
      have h2 := congrArg (fun f => f (e v)) (hproj_idem i)
      simpa [π0] using congrArg e.symm h2
    have hπ0_A : π0 ∘ₗ A0 m = A0 m ∘ₗ π0 := by
      apply LinearMap.ext
      intro v
      have h2 := congrArg (fun f => f (e v)) (hproj_commA i)
      simp only [LinearMap.comp_apply, A, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] at h2
      simpa [π0] using congrArg e.symm h2
    have hπ0_B : π0 ∘ₗ B0 m = B0 m ∘ₗ π0 := by
      apply LinearMap.ext
      intro v
      have h2 := congrArg (fun f => f (e v)) (hproj_commB i)
      simp only [LinearMap.comp_apply, B, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] at h2
      simpa [π0] using congrArg e.symm h2
    rcases proj_comm_A0_B0_eq_zero_or_id hm π0 hπ0_idem hπ0_A hπ0_B with h0 | h1
    · left
      apply LinearMap.ext
      intro x
      have hx := congrArg (fun f => f (e.symm x)) h0
      simp only [π0, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.zero_apply] at hx
      have hx' := congrArg e hx
      rw [LinearEquiv.apply_symm_apply, map_zero] at hx'
      exact hx'
    · right
      apply LinearMap.ext
      intro x
      have hx := congrArg (fun f => f (e.symm x)) h1
      simp only [π0, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply] at hx
      have hx' := congrArg e hx
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hx'
      exact hx'
  have hex : ∃ i : Fin r, proj i = LinearMap.id := by
    by_contra hnone
    push Not at hnone
    have hall0 : ∀ i, proj i = 0 := fun i => (hproj_zero_or_id i).resolve_right (hnone i)
    have hbot : ∀ i, V i = ⊥ := by
      intro i
      rw [eq_bot_iff]
      intro x hx
      have hpx := hproj_self i hx
      rw [hall0 i, LinearMap.zero_apply] at hpx
      simp only [Submodule.mem_bot]
      exact hpx.symm
    have htop : (⊤ : Submodule ℂ (Fin (3 * m) → ℂ)) = ⊥ := by
      rw [← hV.submodule_iSup_eq_top]
      simp [hbot]
    have hnz : (fun _ : Fin (3 * m) => (1 : ℂ)) ≠ 0 := by
      intro hz
      have := congrFun hz ⟨0, by omega⟩
      norm_num at this
    have hmem : (fun _ : Fin (3 * m) => (1 : ℂ)) ∈ (⊥ : Submodule ℂ (Fin (3 * m) → ℂ)) := by
      rw [← htop]
      trivial
    simp only [Submodule.mem_bot] at hmem
    exact hnz hmem
  rcases hex with ⟨i, hi⟩
  have hVi_top : V i = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : proj i x = x := by rw [hi]; rfl
    rw [← hx]
    exact hproj_mem i x
  have hrank : Module.finrank ℂ (V i) = 3 * m := by
    rw [hVi_top, finrank_top, Module.finrank_fin_fun]
  have hle := (hVprop i).1
  omega
