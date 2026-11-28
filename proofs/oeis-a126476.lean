import OMAStatements.S_oeis_a126476

-- Problem: oeis-a126476 (transfer-matrix proof: path counts via powers of the adjacency matrix)

namespace OMA.Path
open Matrix

theorem cons_mk_zero {α : Type} {n : ℕ} (a : α) (f : Fin n → α) (h : 0 < n + 1) :
    (Fin.cons a f : Fin (n + 1) → α) ⟨0, h⟩ = a := rfl

theorem cons_mk_succ {α : Type} {n : ℕ} (a : α) (f : Fin n → α) (i : ℕ) (h : i + 1 < n + 1) :
    (Fin.cons a f : Fin (n + 1) → α) ⟨i + 1, h⟩ = f ⟨i, by omega⟩ := rfl

variable {k : ℕ}

theorem valid_cons (R : Fin k → Fin k → Prop) (m : ℕ) (x y : Fin k) (t : Fin m → Fin k) :
    (∀ i : Fin (m + 1), R ((Fin.cons x (Fin.cons y t) : Fin (m + 2) → Fin k) ⟨i.val, by omega⟩)
        ((Fin.cons x (Fin.cons y t) : Fin (m + 2) → Fin k) ⟨i.val + 1, by omega⟩)) ↔
      R x y ∧ ∀ i : Fin m, R ((Fin.cons y t : Fin (m + 1) → Fin k) ⟨i.val, by omega⟩)
        ((Fin.cons y t : Fin (m + 1) → Fin k) ⟨i.val + 1, by omega⟩) := by
  constructor
  · intro h
    refine ⟨?_, fun i => ?_⟩
    · have h0 := h ⟨0, by omega⟩
      dsimp only at h0
      rw [cons_mk_zero, cons_mk_succ, cons_mk_zero] at h0
      exact h0
    · have h1 := h ⟨i.val + 1, by omega⟩
      dsimp only at h1
      rw [cons_mk_succ, cons_mk_succ] at h1
      exact h1
  · intro h i
    obtain ⟨i, hi⟩ := i
    dsimp only
    cases i with
    | zero =>
      rw [cons_mk_zero, cons_mk_succ, cons_mk_zero]
      exact h.1
    | succ i =>
      rw [cons_mk_succ, cons_mk_succ]
      exact h.2 ⟨i, by omega⟩

theorem sum_path (A : Matrix (Fin k) (Fin k) ℤ) (R : Fin k → Fin k → Prop) [DecidableRel R]
    (hA : ∀ x y, A x y = if R x y then 1 else 0) : ∀ (m : ℕ) (x : Fin k),
    (∑ t : Fin m → Fin k,
      if (∀ i : Fin m, R ((Fin.cons x t : Fin (m + 1) → Fin k) ⟨i.val, by omega⟩)
        ((Fin.cons x t : Fin (m + 1) → Fin k) ⟨i.val + 1, by omega⟩)) then (1 : ℤ) else 0)
      = (A ^ m *ᵥ 1) x := by
  intro m
  induction m with
  | zero =>
    intro x
    rw [Fintype.sum_unique, if_pos (fun i => i.elim0)]
    simp
  | succ m ih =>
    intro x
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin k)).sum_comp, Fintype.sum_prod_type,
      pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← ih y, Finset.mul_sum, hA]
    refine Finset.sum_congr rfl fun t _ => ?_
    have key := valid_cons R m x y t
    rw [show (Fin.consEquiv (fun _ : Fin (m + 1) => Fin k)) (y, t) = Fin.cons y t from rfl]
    by_cases hxy : R x y
    · rw [if_pos hxy, one_mul]
      exact if_congr (by rw [key]; simp [hxy]) rfl rfl
    · rw [if_neg hxy, zero_mul, if_neg]
      rw [key]
      simp [hxy]

theorem path_card (A : Matrix (Fin k) (Fin k) ℤ) (R : Fin k → Fin k → Prop) [DecidableRel R]
    (hA : ∀ x y, A x y = if R x y then 1 else 0) (m : ℕ) :
    (((Finset.univ : Finset (Fin (m + 1) → Fin k)).filter (fun w =>
      ∀ i : Fin m, R (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩))).card : ℤ)
      = ∑ x, (A ^ m *ᵥ 1) x := by
  rw [Finset.card_filter]
  push_cast
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin k)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sum_path A R hA m x]
  rfl

end OMA.Path

namespace OMA.P126476
open OMA.S_oeis_a126476 Matrix

def A : Matrix (Fin 8) (Fin 8) ℤ := fun x y => if close x y then 1 else 0

def S (m : ℕ) : ℤ := ∑ x, (A ^ m *ᵥ 1) x

theorem a_eq (m : ℕ) : (a (m + 1) : ℤ) = S m := by
  unfold S
  rw [← OMA.Path.path_card A close (fun _ _ => rfl) m]
  unfold a
  refine congrArg Nat.cast (congrArg Finset.card (Finset.filter_congr fun w _ => ?_))
  constructor
  · intro h i
    exact h ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ rfl
  · intro h i j hij
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    simp only at hij
    subst hij
    exact h ⟨i, by omega⟩

theorem a0 : a 0 = 1 := by
  decide

theorem V0 : A ^ 4 *ᵥ (1 : Fin 8 → ℤ) = (6 : ℤ) • (A ^ 3 *ᵥ 1) + (-1 : ℤ) • (A ^ 2 *ᵥ 1) + (-3 : ℤ) • (A ^ 1 *ᵥ 1) + (1 : ℤ) • (1 : Fin 8 → ℤ) := by
  decide +kernel

theorem vals : S 0 = 8 ∧ S 1 = 44 ∧ S 2 = 252 ∧ S 3 = 1446 := by
  decide +kernel

theorem vrec (m : ℕ) : A ^ (m + 4) *ᵥ (1 : Fin 8 → ℤ) = (6 : ℤ) • (A ^ (m + 3) *ᵥ 1) + (-1 : ℤ) • (A ^ (m + 2) *ᵥ 1) + (-3 : ℤ) • (A ^ (m + 1) *ᵥ 1) + (1 : ℤ) • (A ^ m *ᵥ 1) := by
  have e : ∀ j : ℕ, A ^ (m + j) *ᵥ (1 : Fin 8 → ℤ) = A ^ m *ᵥ (A ^ j *ᵥ 1) := fun j => by
    rw [Matrix.mulVec_mulVec, pow_add]
  rw [e 4, e 3, e 2, e 1, V0]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]

theorem Srec (m : ℕ) : S (m + 4) = 6 * S (m + 3) + (-1) * S (m + 2) + (-3) * S (m + 1) + 1 * S m := by
  unfold S
  rw [vrec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]

end OMA.P126476

theorem OMA.solution : type_of% @OMA.S_oeis_a126476.main := by
  obtain ⟨s0, s1, s2, s3⟩ := OMA.P126476.vals
  have hz : ∀ m : ℕ, (OMA.S_oeis_a126476.a (m + 5) : ℤ) = 6 * OMA.S_oeis_a126476.a (m + 4) + (-1) * OMA.S_oeis_a126476.a (m + 3) + (-3) * OMA.S_oeis_a126476.a (m + 2) + 1 * OMA.S_oeis_a126476.a (m + 1) := by
    intro m
    rw [OMA.P126476.a_eq (m + 4), OMA.P126476.a_eq (m + 3), OMA.P126476.a_eq (m + 2), OMA.P126476.a_eq (m + 1), OMA.P126476.a_eq m]
    exact OMA.P126476.Srec m
  have B0 : OMA.S_oeis_a126476.a 0 = 1 := OMA.P126476.a0
  have B1 : OMA.S_oeis_a126476.a 1 = 8 := by
    have h := OMA.P126476.a_eq 0; rw [s0] at h; exact_mod_cast h
  have B2 : OMA.S_oeis_a126476.a 2 = 44 := by
    have h := OMA.P126476.a_eq 1; rw [s1] at h; exact_mod_cast h
  have B3 : OMA.S_oeis_a126476.a 3 = 252 := by
    have h := OMA.P126476.a_eq 2; rw [s2] at h; exact_mod_cast h
  have B4 : OMA.S_oeis_a126476.a 4 = 1446 := by
    have h := OMA.P126476.a_eq 3; rw [s3] at h; exact_mod_cast h
  have hrec : ∀ m : ℕ, (OMA.S_oeis_a126476.a (m + 5) : ℚ) = 6 * OMA.S_oeis_a126476.a (m + 4) + (-1) * OMA.S_oeis_a126476.a (m + 3) + (-3) * OMA.S_oeis_a126476.a (m + 2) + 1 * OMA.S_oeis_a126476.a (m + 1) := by
    intro m; exact_mod_cast hz m
  refine ⟨?_, ?_⟩
  · have hD : ((1 - 6 * PowerSeries.X + PowerSeries.X ^ 2 + 3 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4) : PowerSeries ℚ)
        = PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-6 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 4 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have hNum : ((1 + 2 * PowerSeries.X - 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4) : PowerSeries ℚ)
        = PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (-3 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 4 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have key : ∀ F : PowerSeries ℚ, F * (PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-6 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 4)
        = PowerSeries.C (1 : ℚ) * (F * PowerSeries.X ^ 0) + PowerSeries.C (-6 : ℚ) * (F * PowerSeries.X ^ 1) + PowerSeries.C (1 : ℚ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (3 : ℚ) * (F * PowerSeries.X ^ 3) + PowerSeries.C (-1 : ℚ) * (F * PowerSeries.X ^ 4) := by
      intro F; ring
    rw [hD, hNum, key]
    ext n
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases n with _ | _ | _ | _ | _ | m
    · norm_num [B0]
    · norm_num [B0, B1]
    · norm_num [B0, B1, B2]
    · norm_num [B0, B1, B2, B3]
    · norm_num [B0, B1, B2, B3, B4]
    · rw [show m + 1 + 1 + 1 + 1 + 1 = m + 5 from rfl]
      have h := hrec m
      simp only [show 0 ≤ m + 5 from by omega,
        show m + 5 - 0 = m + 5 from rfl,
        show ¬ (m + 5 = 0) from by omega,
        show 1 ≤ m + 5 from by omega,
        show m + 5 - 1 = m + 4 from rfl,
        show ¬ (m + 4 = 0) from by omega,
        show 2 ≤ m + 5 from by omega,
        show m + 5 - 2 = m + 3 from rfl,
        show ¬ (m + 3 = 0) from by omega,
        show 3 ≤ m + 5 from by omega,
        show m + 5 - 3 = m + 2 from rfl,
        show ¬ (m + 2 = 0) from by omega,
        show 4 ≤ m + 5 from by omega,
        show m + 5 - 4 = m + 1 from rfl,
        show ¬ (m + 1 = 0) from by omega,
        if_true, if_false]
      rw [h]
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h := hz m
    simp only [show m + 5 - 1 = m + 4 from rfl, show m + 5 - 2 = m + 3 from rfl, show m + 5 - 3 = m + 2 from rfl, show m + 5 - 4 = m + 1 from rfl]
    linarith
