import FormalConjectures.GreensOpenProblems.«5»
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic

open MatrixGroups
open scoped Matrix Pointwise

private lemma card_SL2 (p : ℕ) [Fact p.Prime] :
    Fintype.card SL(2, ZMod p) = p * (p ^ 2 - 1) := by
  have e : SL(2, ZMod p) ≃ Σ ac : {v : ZMod p × ZMod p // v ≠ (0, 0)}, ZMod p :=
    { toFun := fun M =>
        let a := M 0 0
        let b := M 0 1
        let c := M 1 0
        let d := M 1 1
        have hdet : a * d - b * c = 1 := by
          rw [← Matrix.det_fin_two M.1]
          exact M.2
        have hac : (a, c) ≠ (0, 0) := by
          intro h
          simp only [Prod.mk.injEq] at h
          rw [h.1, h.2] at hdet
          norm_num at hdet
        ⟨⟨(a, c), hac⟩, if a ≠ 0 then b * a⁻¹ else d * c⁻¹⟩
      invFun := fun ⟨⟨(a, c), hac⟩, t⟩ =>
        ⟨!![a, if a ≠ 0 then t * a else -c⁻¹; c, if a ≠ 0 then a⁻¹ + t * c else t * c], by
          rw [Matrix.det_fin_two]
          by_cases ha : a ≠ 0
          · simp [ha]
            calc a * (a⁻¹ + t * c) - t * a * c
              _ = a * a⁻¹ := by ring
              _ = 1 := mul_inv_cancel₀ ha
          · have ha0 : a = 0 := not_not.mp ha
            have hc : c ≠ 0 := fun hc0 => hac (Prod.ext ha0 hc0)
            simp [ha0]
            exact inv_mul_cancel₀ hc⟩
      left_inv := fun M => by
        ext i j
        have hdet : (M 0 0 : ZMod p) * M 1 1 - M 0 1 * M 1 0 = 1 := by
          rw [← Matrix.det_fin_two M.1]
          exact M.2
        by_cases ha : (M 0 0 : ZMod p) ≠ 0
        · fin_cases i <;> fin_cases j
          · simp [ha]
          · simp [ha, mul_assoc]
          · simp [ha]
          · simp [ha]
            have h1 : (M 0 0 : ZMod p) * ((M 0 0)⁻¹ + M 0 1 * (M 0 0)⁻¹ * M 1 0) = M 0 0 * M 1 1 := by
              calc (M 0 0 : ZMod p) * ((M 0 0)⁻¹ + M 0 1 * (M 0 0)⁻¹ * M 1 0)
                _ = M 0 0 * (M 0 0)⁻¹ + M 0 1 * (M 0 0 * (M 0 0)⁻¹) * M 1 0 := by ring
                _ = 1 + M 0 1 * 1 * M 1 0 := by rw [mul_inv_cancel₀ (by exact ha)]
                _ = M 0 0 * M 1 1 := by linear_combination -hdet
            exact mul_left_cancel₀ ha h1
        · have ha0 : (M 0 0 : ZMod p) = 0 := not_not.mp ha
          have hc : (M 1 0 : ZMod p) ≠ 0 := by
            intro hc0
            rw [ha0, hc0] at hdet
            norm_num at hdet
          fin_cases i <;> fin_cases j
          · simp [ha0]
          · simp [ha0]
            have h1 : (-(M 1 0 : ZMod p)⁻¹) * M 1 0 = M 0 1 * M 1 0 := by
              rw [neg_mul, inv_mul_cancel₀ (by exact hc)]
              rw [ha0] at hdet
              linear_combination hdet
            exact mul_right_cancel₀ hc h1
          · simp [ha0]
          · simp [ha0, mul_assoc, inv_mul_cancel₀ (by exact hc)]
      right_inv := fun ⟨⟨(a, c), hac⟩, t⟩ => by
        ext
        · rfl
        · rfl
        · dsimp only
          by_cases ha : a ≠ 0
          · simp [ha, mul_assoc]
          · have ha0 : a = 0 := not_not.mp ha
            have hc : c ≠ 0 := fun hc0 => hac (Prod.ext ha0 hc0)
            simp [ha0, mul_assoc, mul_inv_cancel₀ hc] }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcard : Fintype.card {v : ZMod p × ZMod p // v ≠ (0, 0)} = p ^ 2 - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    simp [ZMod.card, sq]
  rw [hcard, ZMod.card p]
  ring

private noncomputable def u_mat {p : ℕ} [Fact p.Prime] (b : ZMod p) : SL(2, ZMod p) :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

private noncomputable def w_mat (p : ℕ) [Fact p.Prime] : SL(2, ZMod p) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

private noncomputable def l_mat {p : ℕ} [Fact p.Prime] (y : ZMod p) : SL(2, ZMod p) :=
  w_mat p * u_mat (-y) * (w_mat p)⁻¹

private lemma l_mat_eq {p : ℕ} [Fact p.Prime] (y : ZMod p) :
    ((l_mat (p := p) y : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; y, 1] := by
  have hw : (w_mat p)⁻¹ = ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change ((w_mat p).1 * !![0, 1; -1, 0]) = (1 : Matrix (Fin 2) (Fin 2) (ZMod p))
    ext a b
    fin_cases a <;> fin_cases b <;> simp [w_mat, Matrix.mul_apply, Fin.sum_univ_two]
  ext i j
  rw [l_mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hw]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [w_mat, u_mat]

private lemma sl2_generated_by_unipotents (p : ℕ) [Fact p.Prime] (M : SL(2, ZMod p)) :
    M ∈ Subgroup.closure (Set.range (u_mat (p := p)) ∪ Set.range (l_mat (p := p))) := by
  let H := Subgroup.closure (Set.range (u_mat (p := p)) ∪ Set.range (l_mat (p := p)))
  have hu : ∀ b, u_mat b ∈ H := fun b => Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)
  have hl : ∀ y, l_mat y ∈ H := fun y => Subgroup.subset_closure (Or.inr ⟨y, rfl⟩)
  have hd : ∀ (a : ZMod p) (ha : a ≠ 0),
      (⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, mul_inv_cancel₀ ha]⟩ : SL(2, ZMod p)) ∈ H := by
    intro a ha
    have h4 : u_mat (p := p) (a - 1) * l_mat 1 * u_mat (a⁻¹ - 1) * l_mat (-a) =
        ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, mul_inv_cancel₀ ha]⟩ := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, l_mat_eq, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j
      · simp [u_mat]
        left
        calc a * (a⁻¹ - 1) + (a - 1)
          _ = a * a⁻¹ - a + (a - 1) := by ring
          _ = 1 - a + (a - 1) := by rw [mul_inv_cancel₀ ha]
          _ = 0 := by ring
      · simp [u_mat]
        calc a * (a⁻¹ - 1) + (a - 1)
          _ = a * a⁻¹ - a + (a - 1) := by ring
          _ = 1 - a + (a - 1) := by rw [mul_inv_cancel₀ ha]
          _ = 0 := by ring
      · simp [u_mat]
        calc 1 + -(a⁻¹ * a)
          _ = 1 - a⁻¹ * a := by ring
          _ = 1 - 1 := by rw [inv_mul_cancel₀ ha]
          _ = 0 := by ring
      · simp [u_mat]
    rw [← h4]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hu _) (hl _)) (hu _)) (hl _)
  have htop : ∀ (N : SL(2, ZMod p)), N 0 0 ≠ 0 → N ∈ H := by
    intro N hN0
    let a : ZMod p := N 0 0
    let b : ZMod p := N 0 1
    let c : ZMod p := N 1 0
    let d : ZMod p := N 1 1
    have ha0 : a ≠ 0 := hN0
    have hdet : a * d - b * c = 1 := by
      rw [← Matrix.det_fin_two N.1]
      exact N.2
    have hmul : l_mat (p := p) (-c * a⁻¹) * N * u_mat (-a⁻¹ * b) =
        ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, mul_inv_cancel₀ ha0]⟩ := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, l_mat_eq, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp [u_mat, a, b, c]
      · calc -(a * (a⁻¹ * b)) + b
          _ = -(a * a⁻¹) * b + b := by ring
          _ = -1 * b + b := by rw [mul_inv_cancel₀ ha0]
          _ = 0 := by ring
      · calc -(N 1 0 * (N 0 0)⁻¹ * N 0 0) + N 1 0
          _ = -(N 1 0 * ((N 0 0)⁻¹ * N 0 0)) + N 1 0 := by ring
          _ = -(N 1 0 * 1) + N 1 0 := by rw [inv_mul_cancel₀ (by exact hN0)]
          _ = 0 := by ring
      · have h1 : a * (-((-(c * a⁻¹ * a) + c) * (a⁻¹ * b)) + (-(c * a⁻¹ * b) + d)) = a * a⁻¹ := by
          have hca : -(c * a⁻¹ * a) + c = 0 := by
            rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]
            ring
          rw [hca, zero_mul, neg_zero, zero_add]
          calc a * (-(c * a⁻¹ * b) + d)
            _ = -c * (a * a⁻¹) * b + a * d := by ring
            _ = -c * 1 * b + a * d := by rw [mul_inv_cancel₀ ha0]
            _ = a * d - b * c := by ring
            _ = 1 := hdet
            _ = a * a⁻¹ := (mul_inv_cancel₀ ha0).symm
        exact mul_left_cancel₀ ha0 h1
    have hN' : N = (l_mat (-c * a⁻¹))⁻¹ *
        ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, mul_inv_cancel₀ ha0]⟩ * (u_mat (-a⁻¹ * b))⁻¹ := by
      rw [← hmul]
      group
    rw [hN']
    exact H.mul_mem (H.mul_mem (H.inv_mem (hl _)) (hd a ha0)) (H.inv_mem (hu _))
  by_cases hM : (M 0 0 : ZMod p) ≠ 0
  · exact htop M hM
  · have hM0 : (M 0 0 : ZMod p) = 0 := not_not.mp hM
    have hdet : (M 0 0 : ZMod p) * M 1 1 - M 0 1 * M 1 0 = 1 := by
      rw [← Matrix.det_fin_two M.1]
      exact M.2
    have hc : (M 1 0 : ZMod p) ≠ 0 := by
      intro hc0
      rw [hM0, hc0] at hdet
      norm_num at hdet
    have hUM : (u_mat (p := p) 1 * M) 0 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      simp [u_mat, hM0, hc]
    have h1 := htop (u_mat (p := p) 1 * M) hUM
    have h2 : M = (u_mat (p := p) 1)⁻¹ * (u_mat (p := p) 1 * M) := by group
    rw [h2]
    exact H.mul_mem (H.inv_mem (hu 1)) h1

private noncomputable def rightReg {G : Type*} [Group G] (g : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f x := f (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma rightReg_mul {G : Type*} [Group G] (g₁ g₂ : G) (f : G → ℂ) :
    rightReg g₁ (rightReg g₂ f) = rightReg (g₁ * g₂) f := by
  ext x
  simp [rightReg, mul_assoc]

private lemma rightReg_one {G : Type*} [Group G] (f : G → ℂ) :
    rightReg (1 : G) f = f := by
  ext x
  simp [rightReg]

private lemma u_mat_add {p : ℕ} [Fact p.Prime] (a b : ZMod p) :
    u_mat a * u_mat b = u_mat (a + b) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [u_mat] <;> ring

private lemma u_mat_pow {p : ℕ} [Fact p.Prime] (m : ℕ) :
    (u_mat (p := p) 1) ^ m = u_mat (m : ZMod p) := by
  induction m with
  | zero =>
    rw [pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u_mat]
  | succ m ih =>
    rw [pow_succ, ih, u_mat_add, Nat.cast_succ]

private lemma frobenius_min_dim (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p)
    (W : Submodule ℂ (SL(2, ZMod p) → ℂ))
    (hW_ne : W ≠ ⊥)
    (hW_inv : ∀ g : SL(2, ZMod p), ∀ v ∈ W, rightReg g v ∈ W)
    (hW_nofix : ∀ v ∈ W, (∀ g : SL(2, ZMod p), rightReg g v = v) → v = 0) :
    (p - 1) / 2 ≤ Module.finrank ℂ W := by
  have hp_pos : 0 < p := Nat.lt_of_lt_of_le (by norm_num) hp3
  have hp_ne0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
  have hu1_nontriv : ∃ v ∈ W, rightReg (u_mat (p := p) 1) v ≠ v := by
    by_contra hcon
    push_neg at hcon
    have hu_nat : ∀ (m : ℕ) (v : SL(2, ZMod p) → ℂ), v ∈ W →
        rightReg ((u_mat (p := p) 1) ^ m) v = v := by
      intro m
      induction m with
      | zero =>
        intro v _
        rw [pow_zero, rightReg_one]
      | succ m ih =>
        intro v hv
        rw [pow_succ, ← rightReg_mul, hcon v hv, ih v hv]
    have hu_all : ∀ (b : ZMod p) (v : SL(2, ZMod p) → ℂ), v ∈ W → rightReg (u_mat b) v = v := by
      intro b v hv
      have hb : u_mat b = (u_mat (p := p) 1) ^ b.val := by
        rw [u_mat_pow, ZMod.natCast_zmod_val]
      rw [hb]
      exact hu_nat b.val v hv
    have hl_all : ∀ (y : ZMod p) (v : SL(2, ZMod p) → ℂ), v ∈ W → rightReg (l_mat y) v = v := by
      intro y v hv
      rw [l_mat, ← rightReg_mul, ← rightReg_mul]
      rw [hu_all (-y) _ (hW_inv _ v hv), rightReg_mul, mul_inv_cancel, rightReg_one]
    have hg_all : ∀ (g : SL(2, ZMod p)) (v : SL(2, ZMod p) → ℂ), v ∈ W → rightReg g v = v := by
      intro g
      have hg_mem := sl2_generated_by_unipotents p g
      induction hg_mem using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with ⟨b, rfl⟩ | ⟨y, rfl⟩
        · exact hu_all b
        · exact hl_all y
      | one =>
        intro v _
        exact rightReg_one v
      | mul x y _ _ ihx ihy =>
        intro v hv
        rw [← rightReg_mul, ihy v hv, ihx v hv]
      | inv x _ ihx =>
        intro v hv
        calc rightReg x⁻¹ v
          _ = rightReg x⁻¹ (rightReg x v) := by rw [ihx v hv]
          _ = v := by rw [rightReg_mul, inv_mul_cancel, rightReg_one]
    have hbot : W = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      exact hW_nofix v hv (fun g => hg_all g v hv)
    exact hW_ne hbot
  rcases hu1_nontriv with ⟨v, hvW, hv_ne⟩
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))
  have hζ_ne0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hζp : ζ ^ p = 1 := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    have harg : (p : ℂ) * (2 * Real.pi * Complex.I / (p : ℂ)) = 2 * Real.pi * Complex.I := by
      field_simp [hp_ne0]
    rw [harg, Complex.exp_two_pi_mul_I]
  have hζ_zmod : ∀ (a b : ZMod p), ζ ^ a.val = ζ ^ b.val → a = b := by
    intro a b hab
    have h1 : ζ ^ (a.val : ℤ) = ζ ^ (b.val : ℤ) := by exact_mod_cast hab
    have h2 : ζ ^ ((a.val : ℤ) - (b.val : ℤ)) = 1 := by
      rw [zpow_sub₀ hζ_ne0, h1, div_self (zpow_ne_zero _ hζ_ne0)]
    have h3 : Complex.exp (((a.val : ℤ) - (b.val : ℤ)) * (2 * Real.pi * Complex.I / (p : ℂ))) = 1 := by
      rw [← Int.cast_sub, Complex.exp_int_mul]
      exact h2
    rw [Complex.exp_eq_one_iff] at h3
    rcases h3 with ⟨m, hm⟩
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hm1 : (((a.val : ℤ) - (b.val : ℤ) : ℤ) : ℂ) / (p : ℂ) * (2 * Real.pi * Complex.I) =
        (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast at hm ⊢
      linear_combination hm
    have hm2 : (((a.val : ℤ) - (b.val : ℤ) : ℤ) : ℂ) / (p : ℂ) = (m : ℂ) :=
      mul_right_cancel₀ h2pi hm1
    have hm4 : (a.val : ℤ) - (b.val : ℤ) = m * (p : ℤ) := by
      exact_mod_cast (div_eq_iff hp_ne0).mp hm2
    have hdvd : (p : ℤ) ∣ (a.val : ℤ) - (b.val : ℤ) := ⟨m, by linarith⟩
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub] at hdvd
    simpa [ZMod.natCast_zmod_val] using hdvd.symm
  have hζ_ne1 : ζ ≠ 1 := by
    intro h1
    have h01 : ζ ^ (1 : ZMod p).val = ζ ^ (0 : ZMod p).val := by
      have hp1 : 1 < p := by omega
      simp [ZMod.val_one'', hp1.ne', h1]
    have h01' := hζ_zmod 1 0 h01
    exact one_ne_zero h01'
  have hζ_add : ∀ (x y : ZMod p), ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
    intro x y
    have hmod : (x + y).val = (x.val + y.val) % p := ZMod.val_add x y
    have hdiv : x.val + y.val = p * ((x.val + y.val) / p) + (x.val + y.val) % p :=
      (Nat.div_add_mod (x.val + y.val) p).symm
    calc ζ ^ (x + y).val
      _ = 1 ^ ((x.val + y.val) / p) * ζ ^ ((x.val + y.val) % p) := by simp [hmod]
      _ = (ζ ^ p) ^ ((x.val + y.val) / p) * ζ ^ ((x.val + y.val) % p) := by rw [hζp]
      _ = ζ ^ (p * ((x.val + y.val) / p) + (x.val + y.val) % p) := by rw [← pow_mul, ← pow_add]
      _ = ζ ^ (x.val + y.val) := by rw [← hdiv]
      _ = ζ ^ x.val * ζ ^ y.val := pow_add ζ x.val y.val
  have hζ_sum : ∀ (x : ZMod p), (∑ r : ZMod p, ζ ^ (r * x).val) = if x = 0 then (p : ℂ) else 0 := by
    intro x
    by_cases hx : x = 0
    · simp [hx, ZMod.card]
    · simp only [hx, ↓reduceIte]
      have hbij : (∑ r : ZMod p, ζ ^ (r * x).val) = ∑ s : ZMod p, ζ ^ s.val := by
        exact Fintype.sum_equiv (Equiv.mulRight₀ x hx) _ _ (fun r => rfl)
      rw [hbij]
      have hsum_range : (∑ s : ZMod p, ζ ^ s.val) = ∑ i ∈ Finset.range p, ζ ^ i := by
        refine Finset.sum_bij (fun (s : ZMod p) _ => s.val)
          (fun s _ => Finset.mem_range.mpr (ZMod.val_lt s))
          (fun s₁ _ s₂ _ h => ZMod.val_injective p h)
          (fun i hi => ⟨(i : ZMod p), Finset.mem_univ _, by
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]⟩)
          (fun _ _ => rfl)
      rw [hsum_range]
      have hgeom : (ζ - 1) * (∑ i ∈ Finset.range p, ζ ^ i) = ζ ^ p - 1 := by
        simpa [mul_comm] using geom_sum_mul ζ p
      rw [hζp, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hζ_ne1)
  let P : ZMod p → (SL(2, ZMod p) → ℂ) → (SL(2, ZMod p) → ℂ) := fun r w =>
    ((p : ℂ)⁻¹) • ∑ b : ZMod p, (ζ ^ (r * b).val) • rightReg (u_mat b) w
  have hP_mem : ∀ r w, w ∈ W → P r w ∈ W := by
    intro r w hw
    exact W.smul_mem _ (W.sum_mem (fun b _ => W.smul_mem _ (hW_inv _ w hw)))
  have hP_sum : ∀ w, (∑ r : ZMod p, P r w) = w := by
    intro w
    dsimp only [P]
    rw [← Finset.smul_sum, Finset.sum_comm]
    have hterm : ∀ b : ZMod p, (∑ r : ZMod p, (ζ ^ (r * b).val) • rightReg (u_mat b) w) =
        (if b = 0 then (p : ℂ) else 0) • rightReg (u_mat b) w := by
      intro b
      rw [← Finset.sum_smul, hζ_sum b]
    simp_rw [hterm, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq' Finset.univ (0 : ZMod p)]
    simp only [Finset.mem_univ, ↓reduceIte, smul_smul, inv_mul_cancel₀ hp_ne0, one_smul]
    have hu0 : u_mat (p := p) 0 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [u_mat]
    rw [hu0, rightReg_one]
  have hP_eig : ∀ r c w, rightReg (u_mat c) (P r w) = (ζ ^ (-(r * c)).val) • P r w := by
    intro r c w
    dsimp only [P]
    rw [map_smul, map_sum]
    simp_rw [map_smul, rightReg_mul, u_mat_add]
    have hreidx : (∑ b : ZMod p, (ζ ^ (r * b).val) • rightReg (u_mat (c + b)) w) =
        ∑ b' : ZMod p, (ζ ^ (r * (b' - c)).val) • rightReg (u_mat b') w := by
      exact Fintype.sum_equiv (Equiv.addLeft c) _ _ (fun b => by simp)
    rw [hreidx, smul_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [smul_smul, ← hζ_add]
    congr 2
    ring
  have hr0 : ∃ r₀ : ZMod p, r₀ ≠ 0 ∧ P r₀ v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hv0 : v = P 0 v := by
      calc v = ∑ r : ZMod p, P r v := (hP_sum v).symm
        _ = P 0 v := by
          rw [Finset.sum_eq_single 0]
          · intro r _ hr0; exact hcon r hr0
          · intro h; exact absurd (Finset.mem_univ 0) h
    have hfix : rightReg (u_mat 1) v = v := by
      rw [hv0, hP_eig 0 1 v]
      simp
    exact hv_ne hfix
  rcases hr0 with ⟨r₀, hr₀_ne0, hv₀_ne0⟩
  let v₀ := P r₀ v
  have hv₀W : v₀ ∈ W := hP_mem r₀ v hvW
  let S_sq : Finset (ZMod p) := Finset.univ.image (fun a : (ZMod p)ˣ => (a : ZMod p)⁻¹ ^ 2)
  have hS_sq_card : S_sq.card = (p - 1) / 2 := by
    have h2 : 2 * S_sq.card = Fintype.card (ZMod p)ˣ := by
      have hsum : (∑ y ∈ S_sq, (Finset.univ.filter (fun a : (ZMod p)ˣ =>
          (a : ZMod p)⁻¹ ^ 2 = y)).card) = Fintype.card (ZMod p)ˣ := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext a
          rw [Finset.mem_biUnion]
          exact ⟨fun _ => Finset.mem_univ _, fun _ => ⟨(a : ZMod p)⁻¹ ^ 2,
            Finset.mem_image_of_mem _ (Finset.mem_univ a),
            by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩⟩⟩
        · intro y _ z _ hyz
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro a ha1 ha2
          rw [Finset.mem_filter] at ha1 ha2
          exact hyz (ha1.2.symm.trans ha2.2)
      have hfib : ∀ y ∈ S_sq, (Finset.univ.filter (fun a : (ZMod p)ˣ =>
          (a : ZMod p)⁻¹ ^ 2 = y)).card = 2 := by
        intro y hy
        rw [Finset.mem_image] at hy
        rcases hy with ⟨a, _, rfl⟩
        have hpair : Finset.univ.filter (fun b : (ZMod p)ˣ =>
            (b : ZMod p)⁻¹ ^ 2 = (a : ZMod p)⁻¹ ^ 2) = {a, -a} := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          rw [sq_eq_sq_iff_eq_or_eq_neg]
          constructor
          · rintro (h | h)
            · left; exact Units.ext (inv_injective h)
            · right
              have hneg : (b : ZMod p)⁻¹ = ((-a : (ZMod p)ˣ) : ZMod p)⁻¹ := by
                rw [Units.val_neg, inv_neg]; exact h
              exact Units.ext (inv_injective hneg)
          · rintro (rfl | rfl)
            · left; rfl
            · right; rw [Units.val_neg, inv_neg]
        rw [hpair, Finset.card_pair]
        intro hneg
        have h11 : (1 : ZMod p) = -1 := by
          have : (a : ZMod p) = -(a : ZMod p) := congrArg Units.val hneg
          have h2a : (2 : ZMod p) * (a : ZMod p) = 0 := by linear_combination this
          have h20 : (2 : ZMod p) = 0 := (mul_eq_zero.mp h2a).resolve_right a.ne_zero
          linear_combination h20
        have hp2 : p ∣ 2 := by
          rw [← ZMod.natCast_eq_zero_iff]
          exact_mod_cast (show (2 : ZMod p) = 0 by linear_combination h11)
        have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
        omega
      rw [← hsum, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [ZMod.card_units] at h2
    omega
  let T : Module.End ℂ W := (rightReg (u_mat (p := p) 1)).restrict (fun w hw => hW_inv _ w hw)
  let ev_of : ZMod p → ℂ := fun y => ζ ^ (-(r₀ * y)).val
  have hev_inj : Function.Injective ev_of := by
    intro y₁ y₂ hy
    have h1 := hζ_zmod _ _ hy
    have h2 : r₀ * y₁ = r₀ * y₂ := by linear_combination -h1
    exact mul_left_cancel₀ hr₀_ne0 h2
  let μs_fin : Finset ℂ := S_sq.image ev_of
  let μs : Set ℂ := (μs_fin : Set ℂ)
  have hμs_card : Fintype.card μs = (p - 1) / 2 := by
    change Fintype.card μs_fin = (p - 1) / 2
    rw [Fintype.card_coe, Finset.card_image_of_injective _ hev_inj, hS_sq_card]
  have h_eig : ∀ μ : μs, ∃ w : W, T.HasEigenvector (μ : ℂ) w := by
    rintro ⟨μ, hμ⟩
    change μ ∈ μs_fin at hμ
    rw [Finset.mem_image] at hμ
    rcases hμ with ⟨y, hy, rfl⟩
    rw [Finset.mem_image] at hy
    rcases hy with ⟨a, _, rfl⟩
    let t_a : SL(2, ZMod p) :=
      ⟨!![(a : ZMod p), 0; 0, (a : ZMod p)⁻¹], by
        rw [Matrix.det_fin_two]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          mul_zero, sub_zero]
        exact mul_inv_cancel₀ a.ne_zero⟩
    let w : W := ⟨rightReg t_a v₀, hW_inv t_a v₀ hv₀W⟩
    have hconj : u_mat (p := p) 1 * t_a = t_a * u_mat ((a : ZMod p)⁻¹ ^ 2) := by
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
      dsimp only [u_mat, t_a]
      fin_cases i <;> fin_cases j
      · change (1 : ZMod p) * (a : ZMod p) + 1 * 0 = (a : ZMod p) * 1 + 0 * 0; ring
      · change (1 : ZMod p) * 0 + 1 * (a : ZMod p)⁻¹ = (a : ZMod p) * ((a : ZMod p)⁻¹ ^ 2) + 0 * 1
        rw [sq, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul, zero_mul, add_zero, zero_add, one_mul]
      · change (0 : ZMod p) * (a : ZMod p) + 1 * 0 = 0 * 1 + (a : ZMod p)⁻¹ * 0; ring
      · change (0 : ZMod p) * 0 + 1 * (a : ZMod p)⁻¹ = 0 * ((a : ZMod p)⁻¹ ^ 2) + (a : ZMod p)⁻¹ * 1; ring
    refine ⟨w, ⟨?_, ?_⟩⟩
    · rw [Module.End.mem_eigenspace_iff]
      apply Subtype.ext
      change rightReg (u_mat (p := p) 1) (rightReg t_a v₀) =
        ev_of ((a : ZMod p)⁻¹ ^ 2) • rightReg t_a v₀
      rw [rightReg_mul, hconj, ← rightReg_mul, hP_eig r₀ ((a : ZMod p)⁻¹ ^ 2) v, map_smul]
    · intro hw0
      have hv_zero : rightReg t_a v₀ = 0 := congrArg Subtype.val hw0
      have hv₀_zero : v₀ = 0 := by
        calc v₀ = rightReg (1 : SL(2, ZMod p)) v₀ := (rightReg_one v₀).symm
          _ = rightReg (t_a⁻¹ * t_a) v₀ := by rw [inv_mul_cancel]
          _ = rightReg t_a⁻¹ (rightReg t_a v₀) := (rightReg_mul t_a⁻¹ t_a v₀).symm
          _ = 0 := by rw [hv_zero, map_zero]
      exact hv₀_ne0 hv₀_zero
  let ws : μs → W := fun μ => Classical.choose (h_eig μ)
  have hli := Module.End.eigenvectors_linearIndependent T μs ws (fun μ => Classical.choose_spec (h_eig μ))
  calc (p - 1) / 2 = Fintype.card μs := hμs_card.symm
    _ ≤ Module.finrank ℂ W := hli.fintype_card_le_finrank

private lemma gowers_bound (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p)
    (S : Finset SL(2, ZMod p)) (hS : IsProductFree (S : Set SL(2, ZMod p))) :
    (S.card : ℝ) ^ 3 ≤ (Fintype.card SL(2, ZMod p) : ℝ) ^ 3 / (((p - 1) / 2 : ℕ) : ℝ) := by
  by_cases hS0 : S.card = 0
  · simp [hS0]
    positivity
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS0)
  let G := SL(2, ZMod p)
  let n : ℕ := Fintype.card G
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hn_ne0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  let k : ℕ := (p - 1) / 2
  have hk_pos_nat : 0 < k := by dsimp [k]; omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos_nat
  let A : Matrix G G ℂ := Matrix.of fun x y => if x * y⁻¹ ∈ S then 1 else 0
  let J : Matrix G G ℂ := Matrix.of fun _ _ => 1
  let c₀ : ℂ := ((S.card : ℂ) ^ 2) / (n : ℂ)
  let H₀ : Matrix G G ℂ := Aᴴ * A - c₀ • J
  have hc₀_star : star c₀ = c₀ := by
    dsimp only [c₀]
    simp [map_div₀, map_pow]
  have hJ_herm : J.IsHermitian := by
    ext x y
    simp [J, Matrix.conjTranspose_apply]
  have hH₀ : H₀.IsHermitian := by
    dsimp only [H₀]
    refine (Matrix.isHermitian_conjTranspose_mul_self A).sub ?_
    ext x y
    simp [Matrix.conjTranspose_apply, hc₀_star, J]
  have hA_comm : ∀ (g : G) (u : G → ℂ), A.mulVec (rightReg g u) = rightReg g (A.mulVec u) := by
    intro g u
    ext x
    simp only [Matrix.mulVec, dotProduct, rightReg, LinearMap.coe_mk, AddHom.coe_mk]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun y => ?_)
    simp only [Equiv.coe_mulRight, A, Matrix.of_apply]
    congr 1
    rw [show x * y⁻¹ = (x * g) * (y * g)⁻¹ by rw [mul_inv_rev, mul_assoc, mul_inv_cancel_left]]
  have hAH_comm : ∀ (g : G) (u : G → ℂ), Aᴴ.mulVec (rightReg g u) = rightReg g (Aᴴ.mulVec u) := by
    intro g u
    ext x
    simp only [Matrix.mulVec, dotProduct, rightReg, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.conjTranspose_apply]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun y => ?_)
    simp only [Equiv.coe_mulRight, A, Matrix.of_apply]
    congr 1
    rw [show y * x⁻¹ = (y * g) * (x * g)⁻¹ by rw [mul_inv_rev, mul_assoc, mul_inv_cancel_left]]
  have hJ_comm : ∀ (g : G) (u : G → ℂ), J.mulVec (rightReg g u) = rightReg g (J.mulVec u) := by
    intro g u
    ext x
    simp only [Matrix.mulVec, dotProduct, rightReg, LinearMap.coe_mk, AddHom.coe_mk, J,
      Matrix.of_apply, one_mul]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun y => rfl)
  have hH₀_comm : ∀ (g : G) (u : G → ℂ), H₀.mulVec (rightReg g u) = rightReg g (H₀.mulVec u) := by
    intro g u
    dsimp only [H₀]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.smul_mulVec]
    rw [← Matrix.mulVec_mulVec, hA_comm, hAH_comm, hJ_comm, map_sub, map_smul,
      ← Matrix.mulVec_mulVec]
  have hA_one : ∀ x : G, (A.mulVec (fun _ => 1)) x = (S.card : ℂ) := by
    intro x
    simp only [Matrix.mulVec, dotProduct, mul_one, A, Matrix.of_apply]
    let e : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft x)
    have hsum : (∑ y : G, if x * y⁻¹ ∈ S then (1 : ℂ) else 0) =
        ∑ z : G, if z ∈ S then (1 : ℂ) else 0 := by
      exact Fintype.sum_equiv e _ _ (fun y => rfl)
    rw [hsum, Finset.sum_boole]
    simp
  have hAH_one : ∀ x : G, (Aᴴ.mulVec (fun _ => 1)) x = (S.card : ℂ) := by
    intro x
    simp only [Matrix.mulVec, dotProduct, mul_one, Matrix.conjTranspose_apply, A, Matrix.of_apply]
    let e : G ≃ G := Equiv.mulRight x⁻¹
    have hsum : (∑ y : G, star (if y * x⁻¹ ∈ S then (1 : ℂ) else 0)) =
        ∑ z : G, if z ∈ S then (1 : ℂ) else 0 := by
      refine Fintype.sum_equiv e _ _ (fun y => ?_)
      dsimp only [e]
      rw [Equiv.coe_mulRight]
      split_ifs <;> simp
    rw [hsum, Finset.sum_boole]
    simp
  have hH₀_one : H₀.mulVec (fun _ => 1) = 0 := by
    ext x
    dsimp only [H₀]
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Pi.zero_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [← Matrix.mulVec_mulVec]
    have h1 : (A.mulVec (fun _ => 1)) = fun _ => (S.card : ℂ) := funext hA_one
    rw [h1, show (fun _ : G => (S.card : ℂ)) = (S.card : ℂ) • (fun _ => 1) from
      funext (fun _ => by simp), Matrix.mulVec_smul]
    simp only [Pi.smul_apply, hAH_one, smul_eq_mul]
    have hJ1 : (J.mulVec (fun _ => 1)) x = (n : ℂ) := by
      simp [Matrix.mulVec, dotProduct, J, n]
    rw [hJ1]
    dsimp only [c₀]
    field_simp [hn_ne0]
    ring
  let v : G → ℂ := fun y => if y ∈ S then 1 else 0
  let v₀ : G → ℂ := fun _ => (S.card : ℂ) / (n : ℂ)
  let v₁ : G → ℂ := v - v₀
  have hv₁_sum : (∑ y : G, v₁ y) = 0 := by
    simp only [v₁, Pi.sub_apply, Finset.sum_sub_distrib, v, v₀, Finset.sum_boole,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    change (S.card : ℂ) - (n : ℂ) * ((S.card : ℂ) / (n : ℂ)) = 0
    field_simp [hn_ne0]
    ring
  have hJ_v₁ : J.mulVec v₁ = 0 := by
    ext x
    simp [Matrix.mulVec, dotProduct, J, hv₁_sum]
  have hH₀_v₁ : H₀.mulVec v₁ = (Aᴴ * A).mulVec v₁ := by
    dsimp only [H₀]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hJ_v₁, smul_zero, sub_zero]
  have hv_Av : star v ⬝ᵥ A.mulVec v = 0 := by
    simp only [dotProduct, Pi.star_apply, Matrix.mulVec, A, Matrix.of_apply, v]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hx : x ∈ S
    · simp only [hx, ↓reduceIte, star_one, one_mul]
      refine Finset.sum_eq_zero (fun y _ => ?_)
      by_cases hy : y ∈ S
      · have hxy : x * y⁻¹ ∉ S := by
          intro hmem
          have hprod : (x * y⁻¹) * y ∈ (S : Set G) * (S : Set G) :=
            Set.mul_mem_mul hmem hy
          rw [mul_assoc, inv_mul_cancel, mul_one] at hprod
          exact Set.disjoint_left.mp hS hprod hx
        simp [hy, hxy]
      · simp [hy]
    · simp [hx]
  have hv_Av₀ : star v ⬝ᵥ A.mulVec v₀ = (S.card : ℂ) ^ 3 / (n : ℂ) := by
    have hAv₀ : A.mulVec v₀ = fun _ => (S.card : ℂ) ^ 2 / (n : ℂ) := by
      ext x
      rw [show v₀ = ((S.card : ℂ) / (n : ℂ)) • (fun _ => 1) from funext (fun _ => by simp [v₀]),
        Matrix.mulVec_smul, Pi.smul_apply, hA_one x, smul_eq_mul]
      ring
    rw [hAv₀]
    simp only [dotProduct, Pi.star_apply, v]
    have hsum : (∑ x : G, star (if x ∈ S then (1 : ℂ) else 0)) = (S.card : ℂ) := by
      simp [Finset.sum_boole]
    rw [← Finset.sum_mul, hsum]
    ring
  have hv_Av₁ : star v ⬝ᵥ A.mulVec v₁ = -((S.card : ℂ) ^ 3 / (n : ℂ)) := by
    dsimp only [v₁]
    rw [Matrix.mulVec_sub, dotProduct_sub, hv_Av, hv_Av₀, zero_sub]
  have hCS : ((S.card : ℝ) ^ 3 / (n : ℝ)) ^ 2 ≤
      (S.card : ℝ) * (star v₁ ⬝ᵥ H₀.mulVec v₁).re := by
    have hnorm : ‖star v ⬝ᵥ A.mulVec v₁‖ = (S.card : ℝ) ^ 3 / (n : ℝ) := by
      rw [hv_Av₁, norm_neg]
      have hpos : (0 : ℝ) ≤ (S.card : ℝ) ^ 3 / (n : ℝ) := by positivity
      rw [show ((S.card : ℂ) ^ 3 / (n : ℂ)) = (((S.card : ℝ) ^ 3 / (n : ℝ) : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.norm_of_nonneg hpos
    have hle : ‖star v ⬝ᵥ A.mulVec v₁‖ ≤ ∑ x : G, ‖v x‖ * ‖(A.mulVec v₁) x‖ := by
      calc ‖∑ x : G, star (v x) * (A.mulVec v₁) x‖
        _ ≤ ∑ x : G, ‖star (v x) * (A.mulVec v₁) x‖ := norm_sum_le _ _
        _ = ∑ x : G, ‖v x‖ * ‖(A.mulVec v₁) x‖ := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [norm_mul, norm_star]
    have hcs_real := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset G)
      (fun x => ‖v x‖) (fun x => ‖(A.mulVec v₁) x‖)
    have hsq_le : ((S.card : ℝ) ^ 3 / (n : ℝ)) ^ 2 ≤
        (∑ x : G, ‖v x‖ ^ 2) * (∑ x : G, ‖(A.mulVec v₁) x‖ ^ 2) := by
      calc ((S.card : ℝ) ^ 3 / (n : ℝ)) ^ 2
        _ = ‖star v ⬝ᵥ A.mulVec v₁‖ ^ 2 := by rw [hnorm]
        _ ≤ (∑ x : G, ‖v x‖ * ‖(A.mulVec v₁) x‖) ^ 2 := by
          gcongr
        _ ≤ (∑ x : G, ‖v x‖ ^ 2) * (∑ x : G, ‖(A.mulVec v₁) x‖ ^ 2) := hcs_real
    have hv_norm : (∑ x : G, ‖v x‖ ^ 2) = (S.card : ℝ) := by
      have : ∀ x : G, ‖v x‖ ^ 2 = if x ∈ S then (1 : ℝ) else 0 := by
        intro x; dsimp only [v]; split_ifs <;> simp
      simp [this, Finset.sum_boole]
    have hAv₁_norm : (∑ x : G, ‖(A.mulVec v₁) x‖ ^ 2) = (star v₁ ⬝ᵥ H₀.mulVec v₁).re := by
      rw [hH₀_v₁, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose,
        star_star]
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [hv_norm, hAv₁_norm] at hsq_le
    exact hsq_le
  let b := hH₀.eigenvectorBasis
  have hquad : ∀ u : G → ℂ, (star u ⬝ᵥ H₀.mulVec u).re =
      ∑ i : G, hH₀.eigenvalues i * ‖b.repr (WithLp.toLp 2 u) i‖ ^ 2 := by
    intro u
    let u' : EuclideanSpace ℂ G := WithLp.toLp 2 u
    have hu : u = ∑ i : G, (b.repr u' i) • (b i).ofLp := by
      have h := b.sum_repr u'
      ext x
      have hx := congrArg (fun (w : EuclideanSpace ℂ G) => w.ofLp x) h
      simpa using hx.symm
    have hHu : H₀.mulVec u = ∑ i : G, (b.repr u' i * (hH₀.eigenvalues i : ℂ)) • (b i).ofLp := by
      conv_lhs => rw [hu]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.mulVec_smul, hH₀.mulVec_eigenvectorBasis i]
      ext x
      change (b.repr u').ofLp i * (hH₀.eigenvalues i * (b i).ofLp x) =
        ((b.repr u').ofLp i * (hH₀.eigenvalues i : ℂ)) * (b i).ofLp x
      ring
    have horth : ∀ i j : G, star (b i).ofLp ⬝ᵥ (b j).ofLp = if i = j then 1 else 0 := by
      intro i j
      have h := orthonormal_iff_ite.mp b.orthonormal i j
      rw [PiLp.inner_apply] at h
      simpa [dotProduct, Complex.inner, mul_comm] using h
    have hdot : star u ⬝ᵥ H₀.mulVec u =
        ∑ i : G, (hH₀.eigenvalues i : ℂ) * ‖b.repr u' i‖ ^ 2 := by
      conv_lhs => rhs; rw [hHu]
      conv_lhs => lhs; rw [hu]
      simp only [star_sum, star_smul, dotProduct_sum, sum_dotProduct, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_right_comm, mul_comm ((b.repr u').ofLp i), Complex.star_def,
        mul_comm ((starRingEnd ℂ) _), Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.ofReal_pow, mul_comm]
    rw [hdot, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hev_nonneg : ∀ i : G, 0 ≤ hH₀.eigenvalues i := by
    intro i
    let u : G → ℂ := (b i).ofLp
    let u₀ : G → ℂ := fun _ => (∑ x : G, u x) / (n : ℂ)
    let u₁ : G → ℂ := u - u₀
    have hu₀_mul : H₀.mulVec u₀ = 0 := by
      rw [show u₀ = ((∑ x : G, u x) / (n : ℂ)) • (fun _ => 1) from
        funext (fun _ => by simp [u₀]), Matrix.mulVec_smul, hH₀_one, smul_zero]
    have hu₁_sum : (∑ x : G, u₁ x) = 0 := by
      simp only [u₁, Pi.sub_apply, Finset.sum_sub_distrib, u₀, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      change (∑ x : G, u x) - (n : ℂ) * ((∑ x : G, u x) / (n : ℂ)) = 0
      field_simp [hn_ne0]
      ring
    have hJ_u₁ : J.mulVec u₁ = 0 := by
      ext x; simp [Matrix.mulVec, dotProduct, J, hu₁_sum]
    have hH₀_u₁ : H₀.mulVec u₁ = (Aᴴ * A).mulVec u₁ := by
      dsimp only [H₀]
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hJ_u₁, smul_zero, sub_zero]
    have hdot_u₀_u₁ : star u₀ ⬝ᵥ H₀.mulVec u₁ = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      have htrans : H₀.transpose.mulVec (star u₀) = 0 := by
        ext x
        have hrow : ∀ y, H₀.transpose x y = star (H₀ x y) := fun y => by
          have := congrFun (congrFun hH₀.eq y) x
          simpa [Matrix.conjTranspose_apply] using this.symm
        have hmul : H₀.transpose.mulVec (star u₀) x = star (H₀.mulVec u₀ x) := by
          simp only [Matrix.mulVec, dotProduct, star_sum, Pi.star_apply]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [hrow y, star_mul']
        rw [hmul, hu₀_mul, Pi.zero_apply, star_zero]
      rw [htrans, zero_dotProduct]
    have hdot_u : star u ⬝ᵥ H₀.mulVec u = star u₁ ⬝ᵥ (Aᴴ * A).mulVec u₁ := by
      have hu_eq : u = u₀ + u₁ := funext (fun x => by simp [u₁])
      rw [hu_eq, Matrix.mulVec_add, hu₀_mul, zero_add, star_add, add_dotProduct, hdot_u₀_u₁,
        zero_add, hH₀_u₁]
    rw [hH₀.eigenvalues_eq i, RCLike.re_to_complex, hdot_u, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_nonneg (fun x _ => ?_)
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    exact sq_nonneg _
  let μ : ℝ := Finset.univ.sup' Finset.univ_nonempty hH₀.eigenvalues
  have hμ_le : (star v₁ ⬝ᵥ H₀.mulVec v₁).re ≤ μ * (S.card : ℝ) := by
    rw [hquad v₁]
    have h1 : (∑ i : G, hH₀.eigenvalues i * ‖b.repr (WithLp.toLp 2 v₁) i‖ ^ 2) ≤
        μ * ∑ i : G, ‖b.repr (WithLp.toLp 2 v₁) i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact mul_le_mul_of_nonneg_right (Finset.le_sup' hH₀.eigenvalues (Finset.mem_univ i))
        (sq_nonneg _)
    have h2 : (∑ i : G, ‖b.repr (WithLp.toLp 2 v₁) i‖ ^ 2) = ∑ x : G, ‖v₁ x‖ ^ 2 := by
      have hnorm_b := b.repr.norm_map (WithLp.toLp 2 v₁)
      have hsq : ‖b.repr (WithLp.toLp 2 v₁)‖ ^ 2 = ‖WithLp.toLp 2 v₁‖ ^ 2 := by rw [hnorm_b]
      simpa [PiLp.norm_sq_eq_of_L2] using hsq
    have h3 : (∑ x : G, ‖v₁ x‖ ^ 2) ≤ (S.card : ℝ) := by
      have hv_norm : (∑ x : G, ‖v x‖ ^ 2) = (S.card : ℝ) := by
        have : ∀ x : G, ‖v x‖ ^ 2 = if x ∈ S then (1 : ℝ) else 0 := by
          intro x; dsimp only [v]; split_ifs <;> simp
        simp [this, Finset.sum_boole]
      have hdiff : (∑ x : G, ‖v₁ x‖ ^ 2) =
          (∑ x : G, ‖v x‖ ^ 2) - (S.card : ℝ) ^ 2 / (n : ℝ) := by
        have hterm : ∀ x : G, ‖v₁ x‖ ^ 2 =
            ‖v x‖ ^ 2 - 2 * (v x * star (v₀ x)).re + ‖v₀ x‖ ^ 2 := by
          intro x
          dsimp only [v₁]
          rw [Pi.sub_apply, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
            ← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.star_def]
          ring
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have hcross : (∑ x : G, 2 * (v x * star (v₀ x)).re) = 2 * ((S.card : ℝ) ^ 2 / (n : ℝ)) := by
          have : ∀ x : G, (v x * star (v₀ x)).re =
              (if x ∈ S then (1 : ℝ) else 0) * ((S.card : ℝ) / (n : ℝ)) := by
            intro x
            dsimp only [v, v₀]
            by_cases hx : x ∈ S
            · simp only [hx, ↓reduceIte, one_mul, Complex.star_def, map_div₀, Complex.conj_natCast]
              rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
                Complex.ofReal_re]
            · simp [hx]
          simp_rw [this, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_boole]
          simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, mul_eq_mul_left_iff,
            OfNat.ofNat_ne_zero, or_false]
          rw [sq, mul_div_assoc]
        have hv₀_sq : (∑ x : G, ‖v₀ x‖ ^ 2) = (S.card : ℝ) ^ 2 / (n : ℝ) := by
          have : ∀ x : G, ‖v₀ x‖ ^ 2 = ((S.card : ℝ) / (n : ℝ)) ^ 2 := by
            intro x
            dsimp only [v₀]
            rw [norm_div, Complex.norm_natCast, Complex.norm_natCast, div_pow]
          simp_rw [this]
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          change (n : ℝ) * ((S.card : ℝ) / (n : ℝ)) ^ 2 = (S.card : ℝ) ^ 2 / (n : ℝ)
          field_simp [hn_pos.ne']
        rw [hcross, hv₀_sq]
        ring
      rw [hdiff, hv_norm]
      have : 0 ≤ (S.card : ℝ) ^ 2 / (n : ℝ) := by positivity
      linarith
    have hμ_nn : 0 ≤ μ := by
      rcases Finset.exists_mem_eq_sup' Finset.univ_nonempty hH₀.eigenvalues with ⟨i₀, _, hi₀⟩
      dsimp only [μ]
      rw [hi₀]
      exact hev_nonneg i₀
    calc (∑ i : G, hH₀.eigenvalues i * ‖b.repr (WithLp.toLp 2 v₁) i‖ ^ 2)
      _ ≤ μ * ∑ i : G, ‖b.repr (WithLp.toLp 2 v₁) i‖ ^ 2 := h1
      _ = μ * ∑ x : G, ‖v₁ x‖ ^ 2 := by rw [h2]
      _ ≤ μ * (S.card : ℝ) := mul_le_mul_of_nonneg_left h3 hμ_nn
  have hCS2 : ((S.card : ℝ) ^ 3 / (n : ℝ)) ^ 2 ≤ μ * (S.card : ℝ) ^ 2 := by
    calc ((S.card : ℝ) ^ 3 / (n : ℝ)) ^ 2
      _ ≤ (S.card : ℝ) * (star v₁ ⬝ᵥ H₀.mulVec v₁).re := hCS
      _ ≤ (S.card : ℝ) * (μ * (S.card : ℝ)) := mul_le_mul_of_nonneg_left hμ_le hS_pos.le
      _ = μ * (S.card : ℝ) ^ 2 := by ring
  have hμ_pos : 0 < μ := by
    by_contra hcon
    have hle0 : μ ≤ 0 := not_lt.mp hcon
    have hpos_lhs : 0 < ((S.card : ℝ) ^ 3 / (n : ℝ)) ^ 2 := by positivity
    have hle_rhs : μ * (S.card : ℝ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle0 (sq_nonneg _)
    linarith
  let W : Submodule ℂ (G → ℂ) := LinearMap.ker (H₀.mulVecLin - (μ : ℂ) • LinearMap.id)
  have hW_mem : ∀ u : G → ℂ, u ∈ W ↔ H₀.mulVec u = (μ : ℂ) • u := by
    intro u
    dsimp only [W]
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, Matrix.mulVecLin_apply]
  have hW_ne : W ≠ ⊥ := by
    rcases Finset.exists_mem_eq_sup' Finset.univ_nonempty hH₀.eigenvalues with ⟨i₀, _, hi₀⟩
    rw [Submodule.ne_bot_iff]
    refine ⟨(b i₀).ofLp, ?_, ?_⟩
    · rw [hW_mem, hH₀.mulVec_eigenvectorBasis i₀, ← hi₀]
      rfl
    · intro h0
      have hnorm := b.orthonormal.norm_eq_one i₀
      have hb0 : b i₀ = 0 := by
        ext x
        exact congrFun h0 x
      rw [hb0, norm_zero] at hnorm
      norm_num at hnorm
  have hW_inv : ∀ (g : G), ∀ u ∈ W, rightReg g u ∈ W := by
    intro g u hu
    rw [hW_mem] at hu ⊢
    rw [hH₀_comm, hu, map_smul]
  have hW_nofix : ∀ u ∈ W, (∀ g : G, rightReg g u = u) → u = 0 := by
    intro u hu hfix
    rw [hW_mem] at hu
    have hu_const : u = (u 1) • (fun _ => 1) := by
      ext g
      have hg := congrFun (hfix g) 1
      simpa [rightReg] using hg
    have hmul0 : H₀.mulVec u = 0 := by
      rw [hu_const, Matrix.mulVec_smul, hH₀_one, smul_zero]
    rw [hmul0] at hu
    have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ_pos.ne'
    exact smul_eq_zero.mp hu.symm |>.resolve_left hμc
  have hk_le_W : k ≤ Module.finrank ℂ W :=
    frobenius_min_dim p hp3 W hW_ne hW_inv hW_nofix
  let I_μ : Finset G := Finset.univ.filter (fun i => hH₀.eigenvalues i = μ)
  have hW_le_span : W ≤ Submodule.span ℂ ((fun i => (b i).ofLp) '' (I_μ : Set G)) := by
    intro u hu
    rw [hW_mem] at hu
    let u' : EuclideanSpace ℂ G := WithLp.toLp 2 u
    have hu_repr : u = ∑ i : G, (b.repr u' i) • (b i).ofLp := by
      have h := b.sum_repr u'
      ext x
      have hx := congrArg (fun (w : EuclideanSpace ℂ G) => w.ofLp x) h
      simpa using hx.symm
    have hcoeff : ∀ i : G, hH₀.eigenvalues i ≠ μ → b.repr u' i = 0 := by
      intro i hi
      have h1 : star (b i).ofLp ⬝ᵥ H₀.mulVec u = (μ : ℂ) * (star (b i).ofLp ⬝ᵥ u) := by
        rw [hu, dotProduct_smul, smul_eq_mul]
      have h2 : star (b i).ofLp ⬝ᵥ H₀.mulVec u = (hH₀.eigenvalues i : ℂ) * (star (b i).ofLp ⬝ᵥ u) := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
        have hHerm : H₀ᴴ = H₀ := hH₀.eq
        have hbi : H₀.transpose.mulVec (star (b i).ofLp) =
            (hH₀.eigenvalues i : ℂ) • star (b i).ofLp := by
          have hmul := hH₀.mulVec_eigenvectorBasis i
          have hstar : star (H₀.mulVec (b i).ofLp) =
              star ((hH₀.eigenvalues i : ℂ) • (b i).ofLp) := congrArg star hmul
          rw [star_smul, show star (hH₀.eigenvalues i : ℂ) = (hH₀.eigenvalues i : ℂ) by simp] at hstar
          have htrans : star (H₀.mulVec (b i).ofLp) = H₀.transpose.mulVec (star (b i).ofLp) := by
            ext x
            simp [Matrix.mulVec, dotProduct, star_sum]
            refine Finset.sum_congr rfl (fun y _ => ?_)
            have hxy : star (H₀ x y) = H₀ y x := by
              have := congrFun (congrFun hHerm y) x
              simpa [Matrix.conjTranspose_apply] using this
            rw [← Complex.star_def, hxy, mul_comm]
          rw [← htrans]
          exact hstar
        rw [hbi, smul_dotProduct, smul_eq_mul]
      have hdot_bi : star (b i).ofLp ⬝ᵥ u = b.repr u' i := by
        have h := b.repr_apply_apply u' i
        rw [PiLp.inner_apply] at h
        simpa [dotProduct, Complex.inner, mul_comm] using h.symm
      rw [hdot_bi] at h1 h2
      have hdiff : ((μ : ℂ) - (hH₀.eigenvalues i : ℂ)) * b.repr u' i = 0 := by
        linear_combination h1.symm - h2.symm
      have hne : (μ : ℂ) - (hH₀.eigenvalues i : ℂ) ≠ 0 := by
        intro h0
        apply hi
        have : (μ : ℂ) = (hH₀.eigenvalues i : ℂ) := sub_eq_zero.mp h0
        exact (Complex.ofReal_inj.mp this).symm
      exact (mul_eq_zero.mp hdiff).resolve_left hne
    rw [hu_repr]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hi : hH₀.eigenvalues i = μ
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨i, by simp [I_μ, hi], rfl⟩
    · rw [hcoeff i hi, zero_smul]
      exact Submodule.zero_mem _
  have hW_le_I : Module.finrank ℂ W ≤ I_μ.card := by
    calc Module.finrank ℂ W
      _ ≤ Module.finrank ℂ (Submodule.span ℂ ((fun i => (b i).ofLp) '' (I_μ : Set G))) :=
        Submodule.finrank_mono hW_le_span
      _ ≤ ((fun i => (b i).ofLp) '' (I_μ : Set G)).toFinset.card :=
        finrank_span_le_card _
      _ ≤ I_μ.card := by
        rw [Set.toFinset_image, Finset.toFinset_coe]
        exact Finset.card_image_le
  have hk_le_I : k ≤ I_μ.card := hk_le_W.trans hW_le_I
  have htrace_H₀ : (H₀.trace).re = ∑ i : G, hH₀.eigenvalues i := by
    rw [hH₀.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  have htrace_le : (H₀.trace).re ≤ (n : ℝ) * (S.card : ℝ) := by
    dsimp only [H₀]
    rw [Matrix.trace_sub, Complex.sub_re, Matrix.trace_smul, smul_eq_mul]
    have htr_J : (c₀ * J.trace).re = (S.card : ℝ) ^ 2 := by
      have hJtr : J.trace = (n : ℂ) := by
        change (∑ _ : G, (1 : ℂ)) = (Fintype.card G : ℂ)
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [hJtr]
      dsimp only [c₀]
      have hmul : ((S.card : ℂ) ^ 2 / (n : ℂ)) * (n : ℂ) = (S.card : ℂ) ^ 2 := by
        field_simp [hn_ne0]
      rw [hmul, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
    have htr_A : ((Aᴴ * A).trace).re = (n : ℝ) * (S.card : ℝ) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.re_sum]
      have hinner : ∀ x : G, (∑ y : G, (star (A y x) * A y x).re) = (S.card : ℝ) := by
        intro x
        have hsum : (∑ y : G, (star (A y x) * A y x).re) =
            ∑ y : G, if y * x⁻¹ ∈ S then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          dsimp only [A]
          by_cases h : y * x⁻¹ ∈ S <;> simp [h]
        rw [hsum]
        have hbij : (∑ y : G, if y * x⁻¹ ∈ S then (1 : ℝ) else 0) =
            ∑ z : G, if z ∈ S then (1 : ℝ) else 0 := by
          exact Fintype.sum_equiv (Equiv.mulRight x⁻¹) _ _ (fun y => rfl)
        rw [hbij, Finset.sum_boole]
        simp
      simp_rw [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
    rw [htr_J, htr_A]
    have : 0 ≤ (S.card : ℝ) ^ 2 := sq_nonneg _
    linarith
  have hk_mul_μ : (k : ℝ) * μ ≤ (n : ℝ) * (S.card : ℝ) := by
    calc (k : ℝ) * μ
      _ ≤ (I_μ.card : ℝ) * μ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk_le_I) hμ_pos.le
      _ = ∑ i ∈ I_μ, hH₀.eigenvalues i := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        simp only [I_μ, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi.symm
      _ ≤ ∑ i : G, hH₀.eigenvalues i := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hev_nonneg i)
      _ = (H₀.trace).re := htrace_H₀.symm
      _ ≤ (n : ℝ) * (S.card : ℝ) := htrace_le
  have hμ_le_bound : μ ≤ (n : ℝ) * (S.card : ℝ) / (k : ℝ) :=
    (le_div_iff₀ hk_pos).mpr (by linarith)
  have h6 : (S.card : ℝ) ^ 6 / (n : ℝ) ^ 2 ≤ ((n : ℝ) * (S.card : ℝ) / (k : ℝ)) * (S.card : ℝ) ^ 2 := by
    calc (S.card : ℝ) ^ 6 / (n : ℝ) ^ 2
      _ = ((S.card : ℝ) ^ 3 / (n : ℝ)) ^ 2 := by ring
      _ ≤ μ * (S.card : ℝ) ^ 2 := hCS2
      _ ≤ ((n : ℝ) * (S.card : ℝ) / (k : ℝ)) * (S.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hμ_le_bound (sq_nonneg _)
  have h3_pos : (0 : ℝ) < (S.card : ℝ) ^ 3 := by positivity
  have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  change (S.card : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 / (k : ℝ)
  rw [le_div_iff₀ hk_pos]
  have h6' : (S.card : ℝ) ^ 6 * (k : ℝ) ≤ (n : ℝ) ^ 3 * (S.card : ℝ) ^ 3 := by
    have hmul1 : ((S.card : ℝ) ^ 6 / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 ≤
        (((n : ℝ) * (S.card : ℝ) / (k : ℝ)) * (S.card : ℝ) ^ 2) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h6 hn2_pos.le
    rw [div_mul_cancel₀ _ hn2_pos.ne'] at hmul1
    have hmul2 : (S.card : ℝ) ^ 6 * (k : ℝ) ≤
        ((((n : ℝ) * (S.card : ℝ) / (k : ℝ)) * (S.card : ℝ) ^ 2) * (n : ℝ) ^ 2) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right hmul1 hk_pos.le
    have hrhs : ((((n : ℝ) * (S.card : ℝ) / (k : ℝ)) * (S.card : ℝ) ^ 2) * (n : ℝ) ^ 2) * (k : ℝ) =
        (n : ℝ) ^ 3 * (S.card : ℝ) ^ 3 := by
      calc ((((n : ℝ) * (S.card : ℝ) / (k : ℝ)) * (S.card : ℝ) ^ 2) * (n : ℝ) ^ 2) * (k : ℝ)
        _ = (((n : ℝ) * (S.card : ℝ) / (k : ℝ)) * (k : ℝ)) * (S.card : ℝ) ^ 2 * (n : ℝ) ^ 2 := by ring
        _ = ((n : ℝ) * (S.card : ℝ)) * (S.card : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
            rw [div_mul_cancel₀ _ hk_pos.ne']
        _ = (n : ℝ) ^ 3 * (S.card : ℝ) ^ 3 := by ring
    exact hmul2.trans_eq hrhs
  have h_le : ((S.card : ℝ) ^ 3 * (k : ℝ)) * (S.card : ℝ) ^ 3 ≤ ((n : ℝ) ^ 3) * (S.card : ℝ) ^ 3 := by
    calc ((S.card : ℝ) ^ 3 * (k : ℝ)) * (S.card : ℝ) ^ 3
      _ = (S.card : ℝ) ^ 6 * (k : ℝ) := by ring
      _ ≤ (n : ℝ) ^ 3 * (S.card : ℝ) ^ 3 := h6'
  exact le_of_mul_le_mul_right h_le h3_pos

theorem OMA.solution : type_of% @Green5.green_5.variants.gowers_sl_two := by
  refine ⟨3, by norm_num, fun p hp S hS => ?_⟩
  have hcard : Fintype.card SL(2, ZMod p) = p * (p ^ 2 - 1) := card_SL2 p
  by_cases hp2 : p < 3
  · have hp_eq2 : p = 2 := by
      have := hp.out.two_le
      omega
    have hn6 : Fintype.card SL(2, ZMod p) = 6 := by
      rw [hcard, hp_eq2]
      norm_num
    have hS6 : (S.card : ℝ) ≤ 6 := by
      exact_mod_cast (S.card_le_univ.trans_eq hn6)
    rw [hn6]
    have h6_pow : (6 : ℝ) ≤ 3 * (6 : ℝ) ^ ((8 : ℝ) / 9) := by
      have h19 : (6 : ℝ) ^ ((1 : ℝ) / 9) ≤ 3 := by
        have hle : (6 : ℝ) ≤ (3 : ℝ) ^ (9 : ℕ) := by norm_num
        calc (6 : ℝ) ^ ((1 : ℝ) / 9)
          _ ≤ ((3 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 9) :=
            Real.rpow_le_rpow (by norm_num) hle (by norm_num)
          _ = 3 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num
      calc (6 : ℝ) = (6 : ℝ) ^ ((1 : ℝ) / 9) * (6 : ℝ) ^ ((8 : ℝ) / 9) := by
            rw [← Real.rpow_add (by norm_num)]
            norm_num
        _ ≤ 3 * (6 : ℝ) ^ ((8 : ℝ) / 9) :=
          mul_le_mul_of_nonneg_right h19 (by positivity)
    exact hS6.trans h6_pow
  · push_neg at hp2
    let n := Fintype.card SL(2, ZMod p)
    let k := (p - 1) / 2
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by dsimp [k]; omega)
    have hp_odd : p % 2 = 1 := by
      rcases hp.out.eq_two_or_odd with rfl | hodd
      · omega
      · exact hodd
    have hp_le_3k : (p : ℝ) ≤ 3 * (k : ℝ) := by
      have : p ≤ 3 * k := by dsimp [k]; omega
      exact_mod_cast this
    have hn_le_p3 : (n : ℝ) ≤ (p : ℝ) ^ 3 := by
      have : n ≤ p ^ 3 := by
        dsimp only [n]
        rw [hcard]
        calc p * (p ^ 2 - 1) ≤ p * p ^ 2 := Nat.mul_le_mul_left p (Nat.sub_le _ _)
          _ = p ^ 3 := by ring
      exact_mod_cast this
    have hn_le_27k3 : (n : ℝ) ≤ (3 * (k : ℝ)) ^ 3 := by
      calc (n : ℝ) ≤ (p : ℝ) ^ 3 := hn_le_p3
        _ ≤ (3 * (k : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hp_le_3k 3
    have hn13_le_3k : (n : ℝ) ^ ((1 : ℝ) / 3) ≤ 3 * (k : ℝ) := by
      calc (n : ℝ) ^ ((1 : ℝ) / 3)
        _ ≤ ((3 * (k : ℝ)) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hn_pos.le hn_le_27k3 (by norm_num)
        _ = 3 * (k : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
    have hgow := gowers_bound p hp2 S hS
    have hcube : (S.card : ℝ) ^ 3 ≤ (3 * (n : ℝ) ^ ((8 : ℝ) / 9)) ^ 3 := by
      have h83 : (3 * (n : ℝ) ^ ((8 : ℝ) / 9)) ^ 3 = 27 * (n : ℝ) ^ ((8 : ℝ) / 3) := by
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((8 : ℝ) / 9)) 3,
          ← Real.rpow_mul hn_pos.le]
        norm_num
      have hn3_eq : (n : ℝ) ^ 3 = (n : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ ((8 : ℝ) / 3) := by
        rw [← Real.rpow_add hn_pos]
        norm_num
      rw [h83]
      calc (S.card : ℝ) ^ 3
        _ ≤ (n : ℝ) ^ 3 / (k : ℝ) := hgow
        _ = ((n : ℝ) ^ ((1 : ℝ) / 3) / (k : ℝ)) * (n : ℝ) ^ ((8 : ℝ) / 3) := by
          rw [hn3_eq]; ring
        _ ≤ 3 * (n : ℝ) ^ ((8 : ℝ) / 3) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact (div_le_iff₀ hk_pos).mpr hn13_le_3k
        _ ≤ 27 * (n : ℝ) ^ ((8 : ℝ) / 3) := by
          refine mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hcube
