import OMAStatements.S_mo_188526

open OMA.S_mo_188526

namespace EllipsoidPinwheel

noncomputable def rotMap (θ : ℝ) : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun v := WithLp.toLp 2 ![Real.cos θ * v 0 + Real.sin θ * v 1,
    -Real.sin θ * v 0 + Real.cos θ * v 1]
  map_add' u v := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r v := by
    ext i
    fin_cases i <;> simp <;> ring

noncomputable def rotEquiv (θ : ℝ) : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  { toLinearEquiv := LinearEquiv.ofLinearMap (rotMap θ) (rotMap (-θ))
      (by
        ext v i
        have h := Real.cos_sq_add_sin_sq θ
        fin_cases i
        · simp only [LinearMap.comp_apply, LinearMap.id_apply, rotMap, LinearMap.coe_mk,
            AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            Real.cos_neg, Real.sin_neg]
          calc
            Real.cos θ * (Real.cos θ * v 0 + -Real.sin θ * v 1) +
                Real.sin θ * (-(-Real.sin θ) * v 0 + Real.cos θ * v 1) =
                (Real.cos θ ^ 2 + Real.sin θ ^ 2) * v 0 := by ring
            _ = v 0 := by rw [h, one_mul]
        · simp only [LinearMap.comp_apply, LinearMap.id_apply, rotMap, LinearMap.coe_mk,
            AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            Real.cos_neg, Real.sin_neg]
          calc
            -Real.sin θ * (Real.cos θ * v 0 + -Real.sin θ * v 1) +
                Real.cos θ * (-(-Real.sin θ) * v 0 + Real.cos θ * v 1) =
                (Real.cos θ ^ 2 + Real.sin θ ^ 2) * v 1 := by ring
            _ = v 1 := by rw [h, one_mul])
      (by
        ext v i
        have h := Real.cos_sq_add_sin_sq θ
        fin_cases i
        · simp only [LinearMap.comp_apply, LinearMap.id_apply, rotMap, LinearMap.coe_mk,
            AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            Real.cos_neg, Real.sin_neg]
          calc
            Real.cos θ * (Real.cos θ * v 0 + Real.sin θ * v 1) +
                -Real.sin θ * (-Real.sin θ * v 0 + Real.cos θ * v 1) =
                (Real.cos θ ^ 2 + Real.sin θ ^ 2) * v 0 := by ring
            _ = v 0 := by rw [h, one_mul]
        · simp only [LinearMap.comp_apply, LinearMap.id_apply, rotMap, LinearMap.coe_mk,
            AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            Real.cos_neg, Real.sin_neg]
          calc
            -(-Real.sin θ) * (Real.cos θ * v 0 + Real.sin θ * v 1) +
                Real.cos θ * (-Real.sin θ * v 0 + Real.cos θ * v 1) =
                (Real.cos θ ^ 2 + Real.sin θ ^ 2) * v 1 := by ring
            _ = v 1 := by rw [h, one_mul])
    norm_map' := by
      intro v
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      congr 1
      simp only [LinearEquiv.coe_ofLinearMap, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, rotMap,
        LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      have h := Real.cos_sq_add_sin_sq θ
      calc
        (Real.cos θ * v 0 + Real.sin θ * v 1) ^ 2 +
            (-Real.sin θ * v 0 + Real.cos θ * v 1) ^ 2 =
            (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by ring
        _ = v 0 ^ 2 + v 1 ^ 2 := by rw [h, one_mul] }

lemma rotEquiv_apply_zero (θ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    rotEquiv θ v 0 = Real.cos θ * v 0 + Real.sin θ * v 1 := rfl

lemma rotEquiv_apply_one (θ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    rotEquiv θ v 1 = -Real.sin θ * v 0 + Real.cos θ * v 1 := rfl

noncomputable def pinCenter (a θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![9 / 10 * a * Real.cos θ, 9 / 10 * a * Real.sin θ]

lemma rotEquiv_neg_pinCenter (a θ : ℝ) :
    rotEquiv θ (0 - pinCenter a θ) 0 = -(9 / 10 * a) ∧
      rotEquiv θ (0 - pinCenter a θ) 1 = 0 := by
  have h := Real.cos_sq_add_sin_sq θ
  constructor
  · simp only [rotEquiv_apply_zero, zero_sub, PiLp.neg_apply, pinCenter,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    calc
      Real.cos θ * -(9 / 10 * a * Real.cos θ) + Real.sin θ * -(9 / 10 * a * Real.sin θ) =
          -(9 / 10 * a) * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = -(9 / 10 * a) := by rw [h, mul_one]
  · simp only [rotEquiv_apply_one, zero_sub, PiLp.neg_apply, pinCenter,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring

lemma rotEquiv_sub_pinCenter_one (a θ₁ θ₂ : ℝ) :
    rotEquiv θ₂ (pinCenter a θ₁ - pinCenter a θ₂) 1 =
      9 / 10 * a * Real.sin (θ₁ - θ₂) := by
  simp only [rotEquiv_apply_one, PiLp.sub_apply, pinCenter,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.sin_sub]
  ring

noncomputable def expPair : Fin 2 → ℝ := ![3 / 2, 5 / 2]

lemma sin_abs_ge_of_pin (N : ℕ) (hN : 1 ≤ N) {j k : Fin N} (hjk : j ≠ k) :
    (1 : ℝ) / N ≤
      |Real.sin (((j : ℕ) : ℝ) * Real.pi / (2 * N) - ((k : ℕ) : ℝ) * Real.pi / (2 * N))| := by
  set d : ℝ := |((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)|
  have hNpos : (0 : ℝ) < N := by positivity
  have hd_ge : (1 : ℝ) ≤ d := by
    have hne : (j : ℕ) ≠ (k : ℕ) := fun h ↦ hjk (Fin.ext h)
    dsimp [d]
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : ((j : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast hlt
      rw [abs_of_neg (by linarith)]
      linarith
    · have h1 : ((k : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast hgt
      rw [abs_of_pos (by linarith)]
      linarith
  have hd_le : d ≤ N := by
    have hj : ((j : ℕ) : ℝ) < N := by exact_mod_cast j.isLt
    have hk : ((k : ℕ) : ℝ) < N := by exact_mod_cast k.isLt
    have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
    dsimp [d]
    rw [abs_le]
    constructor <;> linarith
  set φ : ℝ := d * Real.pi / (2 * N)
  have hφ_nonneg : 0 ≤ φ := by positivity
  have hφ_le : φ ≤ Real.pi / 2 := by
    dsimp [φ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  set α : ℝ := ((j : ℕ) : ℝ) * Real.pi / (2 * N) - ((k : ℕ) : ℝ) * Real.pi / (2 * N)
  have hangle : |α| = φ := by
    dsimp [α, φ, d]
    rw [show ((j : ℕ) : ℝ) * Real.pi / (2 * N) - ((k : ℕ) : ℝ) * Real.pi / (2 * N) =
      (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * (Real.pi / (2 * N)) by ring,
      abs_mul, abs_of_pos (by positivity : 0 < Real.pi / (2 * N))]
    ring
  have hsin_nonneg : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφ_nonneg (hφ_le.trans (by linarith [Real.pi_pos]))
  have hsin_eq : |Real.sin α| = Real.sin φ := by
    rcases le_or_gt 0 α with hsign | hsign
    · have hα : α = φ := by rwa [abs_of_nonneg hsign] at hangle
      rw [hα, abs_of_nonneg hsin_nonneg]
    · have hα : -α = φ := by rwa [abs_of_neg hsign] at hangle
      have hα' : α = -φ := by linarith
      rw [hα', Real.sin_neg, abs_neg, abs_of_nonneg hsin_nonneg]
  rw [hsin_eq]
  calc
    (1 : ℝ) / N = 2 / Real.pi * (1 * Real.pi / (2 * N)) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ 2 / Real.pi * φ := by
      dsimp [φ]
      gcongr
    _ ≤ Real.sin φ := Real.mul_le_sin hφ_nonneg hφ_le

end EllipsoidPinwheel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_188526.main) := by
  open EllipsoidPinwheel in
  intro hmain
  obtain ⟨M, hM⟩ := hmain 2 le_rfl 3 (by norm_num)
  let N : ℕ := M + 1
  have hN1 : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le M)
  have hNpos : (0 : ℝ) < N := by positivity
  let R₀ : ℝ := 1 / (2 * (N : ℝ))
  have hR0_pos : 0 < R₀ := by positivity
  have hR0_lt : R₀ < 1 := by
    dsimp [R₀]
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith
  let a : ℝ := R₀ ^ (3 / 2 : ℝ)
  have ha_pos : 0 < a := Real.rpow_pos_of_pos hR0_pos _
  have hb_eq : R₀ ^ (5 / 2 : ℝ) = R₀ * a := by
    dsimp [a]
    rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hR0_pos, Real.rpow_one]
  let θ : Fin N → ℝ := fun k ↦ ((k : ℕ) : ℝ) * Real.pi / (2 * N)
  have hle := hM N (fun k ↦ pinCenter a (θ k)) (fun k ↦ rotEquiv (θ k)) (fun _ ↦ R₀)
    (fun _ ↦ expPair) (fun _ ↦ ⟨hR0_pos, hR0_lt⟩)
    (fun _ i ↦ by fin_cases i <;> simp [expPair] <;> norm_num)
    ⟨0, fun k ↦ by
      simp only [ellipsoid, Set.mem_ofPred_eq, Fin.sum_univ_two, expPair, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      obtain ⟨h0, h1⟩ := rotEquiv_neg_pinCenter a (θ k)
      rw [h0, h1]
      change (-(9 / 10 * a) / a) ^ 2 + (0 / R₀ ^ (5 / 2 : ℝ)) ^ 2 ≤ 1
      rw [zero_div, zero_pow (by norm_num), add_zero]
      have hdiv : -(9 / 10 * a) / a = -(9 / 10 : ℝ) := by field_simp [ha_pos.ne']
      rw [hdiv]
      norm_num⟩
    (fun j k hmem ↦ by
      by_contra hjk
      simp only [ellipsoid, Set.mem_ofPred_eq, Fin.sum_univ_two, expPair, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] at hmem
      have hsq1 : (rotEquiv (θ k) (pinCenter a (θ j) - pinCenter a (θ k)) 1 /
          R₀ ^ (5 / 2 : ℝ)) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (rotEquiv (θ k) (pinCenter a (θ j) - pinCenter a (θ k)) 0 /
          R₀ ^ (3 / 2 : ℝ))]
      rw [rotEquiv_sub_pinCenter_one, hb_eq] at hsq1
      have hsin := sin_abs_ge_of_pin N hN1 hjk
      have hrat : (9 / 5 : ℝ) ≤ |9 / 10 * a * Real.sin (θ j - θ k) / (R₀ * a)| := by
        rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 10),
          abs_of_pos ha_pos, abs_of_pos (mul_pos hR0_pos ha_pos)]
        have hcancel : 9 / 10 * a * |Real.sin (θ j - θ k)| / (R₀ * a) =
            9 / 10 * |Real.sin (θ j - θ k)| / R₀ := by
          field_simp [ha_pos.ne', hR0_pos.ne']
        rw [hcancel]
        dsimp [R₀]
        rw [div_div_eq_mul_div, div_one]
        calc
          (9 / 5 : ℝ) = 9 / 10 * (1 / N) * (2 * N) := by field_simp [hNpos.ne']; ring
          _ ≤ 9 / 10 * |Real.sin (θ j - θ k)| * (2 * N) := by gcongr
      have hsq_gt : (1 : ℝ) < (9 / 10 * a * Real.sin (θ j - θ k) / (R₀ * a)) ^ 2 := by
        rw [← sq_abs]
        nlinarith
      linarith)
  omega
