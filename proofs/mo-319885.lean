import OMAStatements.S_mo_319885


open OMA.S_mo_319885 Matrix

theorem PX_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Sq ι) (v : ι → ℝ) :
    ‖A.toEuclideanLin.toContinuousLinearMap (WithLp.toLp 2 v)‖ ^ 2 = ∑ i, (A *ᵥ v) i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.toLpLin_toLp]

theorem PX_norm_sq' {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

/-- X1 -/
theorem X_op_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Sq ι) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ v : ι → ℝ, ∑ i, (A *ᵥ v) i ^ 2 ≤ c ^ 2 * ∑ i, v i ^ 2) : op A ≤ c := by
  unfold op
  refine ContinuousLinearMap.opNorm_le_bound _ hc (fun x => ?_)
  obtain ⟨v, rfl⟩ : ∃ v : ι → ℝ, WithLp.toLp 2 v = x := ⟨WithLp.ofLp x, rfl⟩
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp ?_
  rw [mul_pow, PX_norm_sq, PX_norm_sq']
  exact h v

/-- X2 -/
theorem X_le_op {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Sq ι) (v : ι → ℝ) :
    ∑ i, (A *ᵥ v) i ^ 2 ≤ op A ^ 2 * ∑ i, v i ^ 2 := by
  have h := ContinuousLinearMap.le_opNorm A.toEuclideanLin.toContinuousLinearMap
    (WithLp.toLp 2 v)
  have h2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow, PX_norm_sq, PX_norm_sq'] at h2
  exact h2

/-- X3 -/
theorem X_op_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Sq ι) : 0 ≤ op A := by
  unfold op
  exact norm_nonneg _

theorem PX_soft_sq (r : ℝ) (hr : 0 ≤ r) (a : ℝ) :
    (Real.sign a * max (|a| - r) 0) ^ 2 ≤ a ^ 2 := by
  have h1 : (Real.sign a) ^ 2 ≤ 1 := by
    rcases Real.sign_apply_eq a with h | h | h <;> rw [h] <;> norm_num
  have h2 : 0 ≤ max (|a| - r) 0 := le_max_right _ _
  have h3 : max (|a| - r) 0 ≤ |a| := max_le (by linarith) (abs_nonneg a)
  have h4 : (max (|a| - r) 0) ^ 2 ≤ |a| ^ 2 := pow_le_pow_left₀ h2 h3 2
  rw [sq_abs] at h4
  rw [mul_pow]
  nlinarith [sq_nonneg (Real.sign a), sq_nonneg (max (|a| - r) 0)]

theorem PX_frob {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Sq ι) :
    ∑ i, ∑ j, A i j ^ 2 ≤ (Fintype.card ι : ℝ) * op A ^ 2 := by
  rw [Finset.sum_comm]
  have h : ∀ j : ι, ∑ i, A i j ^ 2 ≤ op A ^ 2 := by
    intro j
    have h := X_le_op A (Pi.single j 1)
    have e : ∑ i, (Pi.single j (1:ℝ) : ι → ℝ) i ^ 2 = 1 := by
      simp [Pi.single_apply]
    rw [e, mul_one] at h
    simpa using h
  calc ∑ j, ∑ i, A i j ^ 2 ≤ ∑ _j : ι, op A ^ 2 := Finset.sum_le_sum (fun j _ => h j)
    _ = (Fintype.card ι : ℝ) * op A ^ 2 := by simp

/-- X4: part 1 of the target -/
theorem X_part1 : ∀ (n : ℕ) (A : Sq (Fin n)), A.IsSymm → ∀ r : ℝ, 0 ≤ r →
    op (soft r A) ≤ Real.sqrt n * op A := by
  intro n A _ r hr
  refine X_op_le _ _ (mul_nonneg (Real.sqrt_nonneg _) (X_op_nonneg A)) (fun v => ?_)
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hf := PX_frob A
  rw [Fintype.card_fin] at hf
  have hv : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc ∑ i, (soft r A *ᵥ v) i ^ 2
      ≤ ∑ i, (∑ j, soft r A i j ^ 2) * ∑ j, v j ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => soft r A i j) v)
    _ = (∑ i, ∑ j, soft r A i j ^ 2) * ∑ j, v j ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, A i j ^ 2) * ∑ j, v j ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hv
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => PX_soft_sq r hr _))
    _ ≤ ((n : ℝ) * op A ^ 2) * ∑ j, v j ^ 2 := mul_le_mul_of_nonneg_right hf hv


abbrev PY_tau (a : ZMod 3) : ℝ := if a = 0 then 2 else -1

theorem PY_tau_mul (a b : ZMod 3) : PY_tau a * PY_tau b = PY_tau (a + b) + PY_tau (a - b) := by
  unfold PY_tau
  split_ifs with h1 h2 h3 h4 h3 h4 h2 h3 h4 h3 h4 <;>
    first
      | (exfalso; revert a b; decide)
      | norm_num

theorem PY_tau_three (a c : ZMod 3) (hc : c ≠ 0) :
    PY_tau a + PY_tau (a + c) + PY_tau (a + 2 * c) = 0 := by
  unfold PY_tau
  split_ifs with h1 h2 h3 h3 h2 h3 h3 <;>
    first
      | (exfalso; revert a c; decide)
      | norm_num

theorem PY_pair_comm {k : ℕ} (x y : G k) : pair x y = pair y x := by
  unfold pair
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem PY_pair_add {k : ℕ} (x y z : G k) : pair x (y + z) = pair x y + pair x z := by
  simp [pair, mul_add, Finset.sum_add_distrib]

theorem PY_pair_sub {k : ℕ} (x y z : G k) : pair x (y - z) = pair x y - pair x z := by
  simp [pair, mul_sub, Finset.sum_sub_distrib]

theorem PY_pair_single {k : ℕ} (w : G k) (i : Fin k) :
    pair w (Pi.single i 1) = w i := by
  simp [pair, Pi.single_apply]

theorem PY_card (k : ℕ) : (Fintype.card (G k) : ℝ) = (3:ℝ) ^ k := by
  simp [G]

theorem PY_S {k : ℕ} (w : G k) :
    ∑ y : G k, PY_tau (pair w y) = if w = 0 then 2 * (3:ℝ) ^ k else 0 := by
  by_cases hw : w = 0
  · subst hw
    have h0 : ∀ y : G k, pair (0 : G k) y = 0 := fun y => by simp [pair]
    simp only [h0, PY_tau, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, PY_card]
    ring
  · rw [if_neg hw]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have hi' : w i ≠ 0 := hi
    have hp : ∀ y : G k, pair w (y + Pi.single i 1) = pair w y + w i := fun y => by
      rw [PY_pair_add, PY_pair_single]
    have h1 : ∑ y : G k, PY_tau (pair w (y + Pi.single i 1)) = ∑ y : G k, PY_tau (pair w y) :=
      Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ (fun y => rfl)
    have h2 : ∑ y : G k, PY_tau (pair w (y + Pi.single i 1 + Pi.single i 1))
        = ∑ y : G k, PY_tau (pair w (y + Pi.single i 1)) :=
      Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ (fun y => rfl)
    have h3 : ∑ y : G k, (PY_tau (pair w y) + PY_tau (pair w y + w i)
        + PY_tau (pair w y + 2 * w i)) = 0 :=
      Finset.sum_eq_zero (fun y _ => PY_tau_three _ _ hi')
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h3
    have hp2 : ∀ y : G k, pair w (y + Pi.single i 1 + Pi.single i 1) = pair w y + 2 * w i :=
      fun y => by rw [hp, hp]; ring
    simp only [hp2] at h2
    simp only [hp] at h1 h2
    linarith

theorem PY_S' {k : ℕ} (w : G k) :
    ∑ x : G k, PY_tau (pair x w) = if w = 0 then 2 * (3:ℝ) ^ k else 0 := by
  rw [← PY_S w]
  exact Finset.sum_congr rfl (fun x _ => by rw [PY_pair_comm])

theorem PY_T (k : ℕ) (x y : G k) : ternary k x y = PY_tau (pair x y) := rfl

theorem PY_mulVec (k : ℕ) (v : G k → ℝ) (x : G k) :
    (ternary k *ᵥ v) x = ∑ y, PY_tau (pair x y) * v y := rfl

/-- Y1 -/
theorem Y_symm (k : ℕ) : (ternary k).IsSymm :=
  Matrix.IsSymm.ext (fun x y => by rw [PY_T, PY_T, PY_pair_comm])

/-- Y2: T² = 2n(I + P) in quadratic-form shape -/
theorem Y_sq (k : ℕ) (v : G k → ℝ) :
    ∑ x, (ternary k *ᵥ v) x ^ 2 = 2 * (3:ℝ) ^ k * (∑ x, v x ^ 2 + ∑ x, v x * v (-x)) := by
  have hin : ∀ y z : G k, ∑ x : G k, PY_tau (pair x y) * v y * (PY_tau (pair x z) * v z)
      = v y * v z * ((if y + z = 0 then 2 * (3:ℝ) ^ k else 0)
          + (if y - z = 0 then 2 * (3:ℝ) ^ k else 0)) := by
    intro y z
    rw [← PY_S' (y + z), ← PY_S' (y - z), ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [PY_pair_add, PY_pair_sub, ← PY_tau_mul]
    ring
  have hz : ∀ y : G k, ∑ z : G k, v y * v z * ((if y + z = 0 then 2 * (3:ℝ) ^ k else 0)
          + (if y - z = 0 then 2 * (3:ℝ) ^ k else 0))
      = 2 * (3:ℝ) ^ k * (v y ^ 2) + 2 * (3:ℝ) ^ k * (v y * v (-y)) := by
    intro y
    simp only [mul_add, Finset.sum_add_distrib, add_eq_zero_iff_neg_eq, sub_eq_zero, mul_ite,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  calc ∑ x, (ternary k *ᵥ v) x ^ 2
      = ∑ x : G k, ∑ y : G k, ∑ z : G k, PY_tau (pair x y) * v y * (PY_tau (pair x z) * v z) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [PY_mulVec, sq, Finset.sum_mul_sum]
    _ = ∑ y : G k, ∑ z : G k, ∑ x : G k, PY_tau (pair x y) * v y * (PY_tau (pair x z) * v z) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ y : G k, (2 * (3:ℝ) ^ k * (v y ^ 2) + 2 * (3:ℝ) ^ k * (v y * v (-y))) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← hz y]
        exact Finset.sum_congr rfl (fun z _ => hin y z)
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-- Y3 -/
theorem Y_sum (k : ℕ) (v : G k → ℝ) :
    ∑ x, (ternary k *ᵥ v) x = 2 * (3:ℝ) ^ k * v 0 := by
  have h1 : ∀ x : G k, (ternary k *ᵥ v) x = ∑ y, PY_tau (pair x y) * v y := fun x => rfl
  have h2 : ∀ y : G k, ∑ x : G k, PY_tau (pair x y) * v y
      = if y = 0 then 2 * (3:ℝ) ^ k * v 0 else 0 := by
    intro y
    rw [← Finset.sum_mul, PY_S']
    by_cases h : y = 0
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_comm,
    Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_ite_eq' Finset.univ (0 : G k)]
  exact if_pos (Finset.mem_univ _)

/-- Y4 -/
theorem Y_soft (k : ℕ) (v : G k → ℝ) (x : G k) :
    (soft 1 (ternary k) *ᵥ v) x = ((ternary k *ᵥ v) x + ∑ y, v y) / 3 := by
  have he : ∀ y : G k, soft 1 (ternary k) x y = (PY_tau (pair x y) + 1) / 3 := by
    intro y
    show Real.sign (PY_tau (pair x y)) * max (|PY_tau (pair x y)| - 1) 0 = _
    unfold PY_tau
    by_cases h : pair x y = 0
    · rw [if_pos h, Real.sign_of_pos (by norm_num)]
      norm_num
    · rw [if_neg h, Real.sign_of_neg (by norm_num)]
      norm_num
  have hm : (soft 1 (ternary k) *ᵥ v) x = ∑ y, soft 1 (ternary k) x y * v y := rfl
  rw [hm, PY_mulVec, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [he]
  ring

/-- Y5: column of T at 0 -/
theorem Y_col (k : ℕ) (x : G k) : (ternary k *ᵥ (Pi.single 0 1)) x = 2 := by
  rw [PY_mulVec]
  have h0 : pair x 0 = 0 := by simp [pair]
  simp [Pi.single_apply, h0]

/-- Y6: row sums of T -/
theorem Y_row (k : ℕ) (x : G k) :
    ∑ y, ternary k x y = if x = 0 then 2 * (3:ℝ) ^ k else 0 :=
  PY_S x

theorem PZ_card (k : ℕ) (c : ℝ) : ∑ _x : G k, c = (3:ℝ) ^ k * c := by
  simp [Finset.sum_const, Finset.card_univ]

theorem PZ_cross (k : ℕ) (v : G k → ℝ) : ∑ x, v x * v (-x) ≤ ∑ x, v x ^ 2 := by
  have h1 : ∑ x : G k, v (-x) ^ 2 = ∑ x, v x ^ 2 :=
    Equiv.sum_comp (Equiv.neg (G k)) (fun x => v x ^ 2)
  have h2 : ∑ x, (2 * (v x * v (-x))) ≤ ∑ x, (v x ^ 2 + v (-x) ^ 2) :=
    Finset.sum_le_sum (fun x _ => by nlinarith [sq_nonneg (v x - v (-x))])
  rw [← Finset.mul_sum, Finset.sum_add_distrib, h1] at h2
  linarith

theorem PZ_Tsq_le (k : ℕ) (v : G k → ℝ) :
    ∑ x, (ternary k *ᵥ v) x ^ 2 ≤ 4 * (3:ℝ) ^ k * ∑ x, v x ^ 2 := by
  rw [Y_sq]
  have h := PZ_cross k v
  have hN : (0:ℝ) < 3 ^ k := by positivity
  nlinarith [mul_nonneg hN.le (sub_nonneg.2 h)]

theorem PZ_quad (N μ a b R : ℝ) (hμ : μ ^ 2 = N * μ + 6 * N) (hμ3 : 3 ≤ μ)
    (hCS : b ^ 2 ≤ (N - 1) * R) (hR : 0 ≤ R) :
    4 * a * (a + b) + (a + b) ^ 2 ≤ (μ + 2) * (a ^ 2 + R) := by
  rcases eq_or_lt_of_le hμ3 with h | h
  · subst h
    have hN1 : N = 1 := by linarith
    subst hN1
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    subst hb
    nlinarith
  · have h1 : (μ - 3) * (μ + 2) = (9 + (μ - 3)) * (N - 1) := by linear_combination hμ
    have h1R : (μ - 3) * (μ + 2) * R = (9 + (μ - 3)) * ((N - 1) * R) := by rw [h1]; ring
    have h2 : (9 + (μ - 3)) * b ^ 2 ≤ (9 + (μ - 3)) * ((N - 1) * R) :=
      mul_le_mul_of_nonneg_left hCS (by linarith)
    have h3 : 0 ≤ (μ - 3) * ((μ + 2) * (a ^ 2 + R) - (4 * a * (a + b) + (a + b) ^ 2)) := by
      nlinarith [sq_nonneg ((μ - 3) * a - 3 * b)]
    have h4 := (mul_nonneg_iff_of_pos_left (sub_pos.2 h)).mp h3
    linarith

theorem PZ_S_upper (k : ℕ) (L : ℝ) (hL : 9 * L ^ 2 = 3 * (3:ℝ) ^ k * L + 6 * (3:ℝ) ^ k)
    (hL1 : 1 ≤ L) (v : G k → ℝ) :
    ∑ x, (soft 1 (ternary k) *ᵥ v) x ^ 2 ≤ L ^ 2 * ∑ x, v x ^ 2 := by
  have hN : (0:ℝ) < 3 ^ k := by positivity
  have hA := PZ_Tsq_le k v
  have E1 : ∑ x, (soft 1 (ternary k) *ᵥ v) x ^ 2 =
      (∑ x, (ternary k *ᵥ v) x ^ 2 + 2 * (∑ y, v y) * (2 * (3:ℝ) ^ k * v 0)
        + (3:ℝ) ^ k * (∑ y, v y) ^ 2) / 9 := by
    simp_rw [Y_soft]
    have e : ∀ x : G k, (((ternary k *ᵥ v) x + ∑ y, v y) / 3) ^ 2 =
        ((ternary k *ᵥ v) x ^ 2 + 2 * (∑ y, v y) * (ternary k *ᵥ v) x + (∑ y, v y) ^ 2) / 9 := by
      intro x; ring
    simp_rw [e]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      PZ_card, Y_sum]
  have hσ : v 0 + ∑ x ∈ Finset.univ.erase (0 : G k), v x = ∑ x, v x :=
    Finset.add_sum_erase _ _ (Finset.mem_univ _)
  have hQ : v 0 ^ 2 + ∑ x ∈ Finset.univ.erase (0 : G k), v x ^ 2 = ∑ x, v x ^ 2 :=
    Finset.add_sum_erase _ (fun x => v x ^ 2) (Finset.mem_univ _)
  have hcard : (((Finset.univ.erase (0 : G k)).card : ℕ) : ℝ) = (3:ℝ) ^ k - 1 := by
    have h := Finset.card_erase_add_one (Finset.mem_univ (0 : G k))
    have h' : (((Finset.univ.erase (0 : G k)).card : ℕ) : ℝ) + 1 = (3:ℝ) ^ k := by
      have h2 : ((Finset.univ : Finset (G k)).card : ℝ) = (3:ℝ) ^ k := by
        simp [Finset.card_univ]
      rw [← h2, ← h]; push_cast; ring
    linarith
  have hCS : (∑ x ∈ Finset.univ.erase (0 : G k), v x) ^ 2 ≤
      ((3:ℝ) ^ k - 1) * ∑ x ∈ Finset.univ.erase (0 : G k), v x ^ 2 := by
    rw [← hcard]; exact sq_sum_le_card_mul_sum_sq
  have hR : 0 ≤ ∑ x ∈ Finset.univ.erase (0 : G k), v x ^ 2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hq := PZ_quad ((3:ℝ) ^ k) (3 * L) (v 0) _ _ (by linear_combination hL) (by linarith) hCS hR
  rw [hσ, hQ] at hq
  rw [E1]
  have hq' := mul_le_mul_of_nonneg_left hq hN.le
  have e2 : L ^ 2 = (3 * (3:ℝ) ^ k * L + 6 * (3:ℝ) ^ k) / 9 := by linarith
  rw [e2]
  nlinarith

theorem PZ_S_lower (k : ℕ) (L : ℝ) (hL : 9 * L ^ 2 = 3 * (3:ℝ) ^ k * L + 6 * (3:ℝ) ^ k)
    (hL0 : 0 < L) : L ≤ op (soft 1 (ternary k)) := by
  have hN : (0:ℝ) < 3 ^ k := by positivity
  have hv : (fun x : G k => L + if x = 0 then 2 * (3:ℝ) ^ k / 3 else 0) =
      L • (fun _ => (1:ℝ)) + (2 * (3:ℝ) ^ k / 3) • Pi.single 0 1 := by
    funext x
    by_cases h : x = 0 <;> simp [h]
  have hone : ∀ x : G k, (ternary k *ᵥ fun _ => (1:ℝ)) x = ∑ y, ternary k x y := by
    intro x; simp [Matrix.mulVec, dotProduct]
  have hsum : ∑ x : G k, (L + if x = 0 then 2 * (3:ℝ) ^ k / 3 else 0) =
      (3:ℝ) ^ k * L + 2 * (3:ℝ) ^ k / 3 := by
    rw [Finset.sum_add_distrib, PZ_card]; simp
  have heig : ∀ x : G k, (soft 1 (ternary k) *ᵥ
      (fun x : G k => L + if x = 0 then 2 * (3:ℝ) ^ k / 3 else 0)) x =
      L * (L + if x = 0 then 2 * (3:ℝ) ^ k / 3 else 0) := by
    intro x
    rw [Y_soft, hsum, hv, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Y_col, hone, Y_row]
    by_cases h : x = 0
    · simp only [h, if_true]; linear_combination (-1/9 : ℝ) * hL
    · simp only [h, if_false]; linear_combination (-1/9 : ℝ) * hL
  have h := X_le_op (soft 1 (ternary k))
    (fun x : G k => L + if x = 0 then 2 * (3:ℝ) ^ k / 3 else 0)
  simp_rw [heig, mul_pow] at h
  rw [← Finset.mul_sum] at h
  have hpos : 0 < ∑ x : G k, (L + if x = 0 then 2 * (3:ℝ) ^ k / 3 else 0) ^ 2 := by
    have h0 : (L + if (0 : G k) = 0 then 2 * (3:ℝ) ^ k / 3 else 0) ^ 2 ≤
        ∑ x : G k, (L + if x = 0 then 2 * (3:ℝ) ^ k / 3 else 0) ^ 2 :=
      Finset.single_le_sum (f := fun x : G k => (L + if x = 0 then 2 * (3:ℝ) ^ k / 3 else 0) ^ 2)
        (fun x _ => sq_nonneg _) (Finset.mem_univ 0)
    have : 0 < (L + if (0 : G k) = 0 then 2 * (3:ℝ) ^ k / 3 else 0) ^ 2 := by
      simp only [if_true]; positivity
    linarith
  have hsq : L ^ 2 ≤ op (soft 1 (ternary k)) ^ 2 := le_of_mul_le_mul_right h hpos
  have hop := X_op_nonneg (soft 1 (ternary k))
  by_contra hc
  push Not at hc
  nlinarith

theorem PZ_iff (N : ℝ) (hN : 0 < N) :
    2 * Real.sqrt N < (N + Real.sqrt (N ^ 2 + 24 * N)) / 6 ↔ 25 < N := by
  have ht := Real.sq_sqrt hN.le
  have ht0 := Real.sqrt_nonneg N
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ N ^ 2 + 24 * N by positivity)
  have hs0 := Real.sqrt_nonneg (N ^ 2 + 24 * N)
  generalize Real.sqrt N = t at *
  generalize Real.sqrt (N ^ 2 + 24 * N) = s at *
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have ht5 : t ≤ 5 := by nlinarith
    have hy : 0 ≤ 12 * t - N := by nlinarith
    have h1 : (12 * t - N) ^ 2 < s ^ 2 := by nlinarith
    have h2 : N ^ 2 + 24 * N ≤ (12 * t - N) ^ 2 := by
      nlinarith [mul_nonneg hN.le (sub_nonneg.2 ht5)]
    linarith
  · intro h
    have ht5 : 5 < t := by nlinarith
    by_contra hc
    push Not at hc
    have h1 : s ^ 2 ≤ (12 * t - N) ^ 2 := by nlinarith
    have h2 : (12 * t - N) ^ 2 < N ^ 2 + 24 * N := by
      nlinarith [mul_pos hN (sub_pos.2 ht5)]
    linarith

/-- Z1 -/
theorem Z_opT (k : ℕ) : op (ternary k) = 2 * Real.sqrt ((3:ℝ) ^ k) := by
  have hN : (0:ℝ) < 3 ^ k := by positivity
  have hs := Real.sq_sqrt hN.le
  have hs0 := Real.sqrt_nonneg ((3:ℝ) ^ k)
  apply le_antisymm
  · apply X_op_le _ _ (by positivity)
    intro v
    have e : (2 * Real.sqrt ((3:ℝ) ^ k)) ^ 2 = 4 * 3 ^ k := by rw [mul_pow, hs]; norm_num
    rw [e]; exact PZ_Tsq_le k v
  · have h := X_le_op (ternary k) (Pi.single 0 1)
    simp only [Y_col] at h
    have e : ∑ x : G k, (Pi.single 0 1 : G k → ℝ) x ^ 2 = 1 := by
      simp [Pi.single_apply, ite_pow]
    rw [e, PZ_card] at h
    have h0 := X_op_nonneg (ternary k)
    by_contra hc
    push Not at hc
    nlinarith

/-- Z2 -/
theorem Z_opS (k : ℕ) : op (soft 1 (ternary k)) =
    ((3:ℝ) ^ k + Real.sqrt (((3:ℝ) ^ k) ^ 2 + 24 * (3:ℝ) ^ k)) / 6 := by
  have hN1 : (1:ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ ((3:ℝ) ^ k) ^ 2 + 24 * (3:ℝ) ^ k by positivity)
  have hs0 := Real.sqrt_nonneg (((3:ℝ) ^ k) ^ 2 + 24 * (3:ℝ) ^ k)
  generalize Real.sqrt (((3:ℝ) ^ k) ^ 2 + 24 * (3:ℝ) ^ k) = s at *
  have hs5 : 5 ≤ s := by
    by_contra hc
    push Not at hc
    nlinarith
  have hL : 9 * (((3:ℝ) ^ k + s) / 6) ^ 2 =
      3 * (3:ℝ) ^ k * (((3:ℝ) ^ k + s) / 6) + 6 * (3:ℝ) ^ k := by
    linear_combination (1/4 : ℝ) * hs
  have hL1 : 1 ≤ ((3:ℝ) ^ k + s) / 6 := by linarith
  apply le_antisymm
  · exact X_op_le _ _ (by linarith) (PZ_S_upper k _ hL hL1)
  · exact PZ_S_lower k _ hL (by linarith)

/-- Z3: assembly -/
theorem assembled : (∀ (n : ℕ) (A : Sq (Fin n)), A.IsSymm → ∀ r : ℝ, 0 ≤ r →
      op (soft r A) ≤ Real.sqrt n*op A) ∧
    (∀ k : ℕ, let n : ℝ := (3:ℝ)^k
      (ternary k).IsSymm ∧ op (ternary k)=2*Real.sqrt n ∧
      op (soft 1 (ternary k))=(n+Real.sqrt (n^2+24*n))/6 ∧
      (op (ternary k)<op (soft 1 (ternary k)) ↔ 25<n)) := by
  refine ⟨X_part1, ?_⟩
  intro k n
  refine ⟨Y_symm k, Z_opT k, Z_opS k, ?_⟩
  rw [Z_opT, Z_opS]
  exact PZ_iff ((3:ℝ) ^ k) (by positivity)

theorem OMA.solution : type_of% @OMA.S_mo_319885.main := assembled
