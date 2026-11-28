import OMAStatements.S_wp_hadamard_s_maximal_determinant_problem
import Mathlib

namespace HadamardParts

open Matrix OMA.S_wp_hadamard_s_maximal_determinant_problem

theorem D_mem (n : ℕ) :
    ∃ M : Matrix (Fin n) (Fin n) ℤ, IsPM1 M ∧ D n = Int.natAbs M.det := by
  have hne : ({d : ℕ | ∃ M : Matrix (Fin n) (Fin n) ℤ, IsPM1 M ∧ d = Int.natAbs M.det}).Nonempty :=
    ⟨_, fun _ _ => 1, fun _ _ => Or.inl rfl, rfl⟩
  have hbdd : BddAbove {d : ℕ | ∃ M : Matrix (Fin n) (Fin n) ℤ, IsPM1 M ∧ d = Int.natAbs M.det} := by
    refine ⟨n.factorial, ?_⟩
    rintro d ⟨M, hM, rfl⟩
    have h := Matrix.det_le (A := M) (abv := AbsoluteValue.abs) (x := 1) (fun i j => by
      rcases hM i j with h | h <;> simp [h])
    simp only [Fintype.card_fin, one_pow, nsmul_eq_mul, mul_one, AbsoluteValue.abs_apply] at h
    have h2 := Int.natCast_natAbs M.det
    omega
  exact Nat.sSup_mem hne hbdd

theorem part6 : ∀ n : ℕ, 0 < n → ∀ M : Matrix (Fin n) (Fin n) ℤ, IsPM1 M → (2 : ℤ) ^ (n - 1) ∣ M.det := by
  intro n hn M hM
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  let d : Fin (k + 1) → ℤ := fun i => if i = 0 then 1 else 2
  let N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun i j => if i = 0 then M 0 j else (M i j - M 0 j) / 2
  have hdvd : ∀ i j, (2 : ℤ) ∣ M i j - M 0 j := by
    intro i j
    rcases hM i j with h | h <;> rcases hM 0 j with h' | h' <;> rw [h, h'] <;> decide
  have heq : M.det = (diagonal d * N).det := by
    refine det_eq_of_forall_row_eq_smul_add_const (fun i => if i = 0 then 0 else 1) 0 (by simp) ?_
    intro i j
    rw [diagonal_mul, diagonal_mul]
    by_cases hi : i = 0
    · subst hi; simp [d, N]
    · simp [d, N, hi, Int.mul_ediv_cancel' (hdvd i j)]
  rw [heq, det_mul, det_diagonal]
  refine Dvd.dvd.mul_right ?_ _
  simp [d, Fin.prod_univ_succ, Fin.succ_ne_zero]

theorem amgm {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hs : ∑ i, x i = n * n) :
    ∏ i, x i ≤ (n : ℝ) ^ n ∧ (∏ i, x i = (n : ℝ) ^ n → ∀ i, x i = n) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hw' : ∑ _i : Fin n, ((n : ℝ)⁻¹) = 1 := by
    simp [Finset.card_univ, hn0]
  have hAM : ∑ i : Fin n, (n : ℝ)⁻¹ * x i = n := by
    rw [← Finset.mul_sum, hs]; field_simp
  have hGM : ∏ i : Fin n, x i ^ ((n : ℝ)⁻¹) = (∏ i, x i) ^ ((n : ℝ)⁻¹) :=
    Real.finsetProd_rpow _ _ (fun i _ => hx i) _
  have hP : 0 ≤ ∏ i, x i := Finset.prod_nonneg fun i _ => hx i
  have hle := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (n : ℝ)⁻¹) x
    (fun _ _ => by positivity) hw' (fun i _ => hx i)
  rw [hGM, hAM] at hle
  constructor
  · have := pow_le_pow_left₀ (by positivity) hle n
    rwa [Real.rpow_inv_natCast_pow hP (by omega)] at this
  · intro heq
    have h := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos' Finset.univ
      (fun _ => (n : ℝ)⁻¹) x (fun _ _ => by positivity) hw' (fun i _ => hx i)).1 (by
        rw [hGM, hAM, heq, Real.pow_rpow_inv_natCast (by positivity) (by omega)])
    intro i
    rw [h i (Finset.mem_univ _), hAM]

theorem key {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℤ) (hM : IsPM1 M) :
    ((M.det : ℝ)) ^ 2 ≤ (n : ℝ) ^ n ∧
      (((M.det : ℝ)) ^ 2 = (n : ℝ) ^ n → ∀ i j, i ≠ j → ∑ k, M i k * M j k = 0) := by
  set A : Matrix (Fin n) (Fin n) ℝ := M.map (Int.cast : ℤ → ℝ) with hA
  have hG : (A * Aᴴ).PosSemidef := posSemidef_self_mul_conjTranspose A
  have hH := hG.isHermitian
  have hentry : ∀ i j, (A * Aᴴ) i j = ((∑ k, M i k * M j k : ℤ) : ℝ) := by
    intro i j; simp [A, mul_apply]
  have hdiag : ∀ i, (A * Aᴴ) i i = n := by
    intro i
    rw [hentry]
    have : ∀ k, M i k * M i k = 1 := fun k => by rcases hM i k with h | h <;> simp [h]
    simp [this]
  have hdA : A.det = (M.det : ℝ) := by
    rw [show A = (Int.castRingHom ℝ).mapMatrix M from rfl, ← RingHom.map_det]
    rfl
  have hdet : (A * Aᴴ).det = (M.det : ℝ) ^ 2 := by
    rw [det_mul, det_conjTranspose, hdA]; simp [sq]
  have htr : (A * Aᴴ).trace = n * n := by
    unfold trace
    simp only [diag_apply, hdiag]
    simp
  have hdet' := hH.det_eq_prod_eigenvalues
  have htr' := hH.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id] at hdet' htr'
  obtain ⟨h1, h2⟩ := amgm hn hH.eigenvalues hG.eigenvalues_nonneg (by rw [← htr', htr])
  constructor
  · rw [← hdet, hdet']; exact h1
  · intro heq
    have hev := h2 (by rw [← hdet', hdet, heq])
    have hGs : A * Aᴴ = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      have hs := hH.spectral_theorem
      have hd : diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
          (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
        ext i j
        by_cases h : i = j
        · subst h
          rw [diagonal_apply_eq, Function.comp_apply, hev]
          simp
        · rw [diagonal_apply_ne _ h]
          simp [h]
      rw [hd] at hs
      rw [hs]
      simp
    intro i j hij
    have := congrFun (congrFun hGs i) j
    rw [hentry] at this
    simp [hij] at this
    exact_mod_cast this

theorem rpow_eq_sqrt (n : ℕ) : (n : ℝ) ^ ((n : ℝ) / 2) = Real.sqrt ((n : ℝ) ^ n) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  ring_nf

theorem part1 : ∀ n : ℕ, 0 < n → (D n : ℝ) ≤ (n : ℝ) ^ ((n : ℝ) / 2) := by
  intro n hn
  obtain ⟨M, hM, hD⟩ := D_mem n
  have hDsq : ((D n : ℝ)) ^ 2 = (M.det : ℝ) ^ 2 := by
    rw [hD, Nat.cast_natAbs]; simp
  rw [rpow_eq_sqrt]
  apply Real.le_sqrt_of_sq_le
  rw [hDsq]
  exact (key hn M hM).1

theorem part2 : ∀ n : ℕ, 0 < n → (D n : ℝ) = (n : ℝ) ^ ((n : ℝ) / 2) → n = 1 ∨ n = 2 ∨ 4 ∣ n := by
  intro n hn heq
  by_cases h3 : n < 3
  · omega
  obtain ⟨M, hM, hD⟩ := D_mem n
  have hDsq : ((D n : ℝ)) ^ 2 = (M.det : ℝ) ^ 2 := by
    rw [hD, Nat.cast_natAbs]; simp
  rw [rpow_eq_sqrt] at heq
  have hsq : (M.det : ℝ) ^ 2 = (n : ℝ) ^ n := by
    rw [← hDsq, heq, Real.sq_sqrt (by positivity)]
  have horth := (key hn M hM).2 hsq
  right; right
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hk : ∀ k, (M a k + M b k) * (M a k + M c k) =
      1 + M a k * M c k + M b k * M a k + M b k * M c k := by
    intro k
    rcases hM a k with h | h <;> rw [h] <;> ring
  have hsum : (n : ℤ) = ∑ k, (M a k + M b k) * (M a k + M c k) := by
    simp only [hk, Finset.sum_add_distrib, horth a c hac, horth b a hab.symm, horth b c hbc]
    simp
  have h4 : (4 : ℤ) ∣ ∑ k, (M a k + M b k) * (M a k + M c k) := by
    refine Finset.dvd_sum fun k _ => ?_
    rcases hM a k with h | h <;> rcases hM b k with h' | h' <;> rcases hM c k with h'' | h'' <;>
      rw [h, h', h''] <;> decide
  rw [← hsum] at h4
  exact_mod_cast h4

end HadamardParts

namespace HadamardPart5

open Matrix OMA.S_wp_hadamard_s_maximal_determinant_problem

/-- The bordered matrix: first row and column all ones, entry `1 - 2 B i j` elsewhere. -/
def bord {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ℤ) 1
    (fun i' => Fin.cases (motive := fun _ => ℤ) 1 (fun j' => 1 - 2 * B i' j') j) i

lemma det_bord {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) :
    (bord B).det = (-2) ^ m * B.det := by
  let N' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := Matrix.of fun i j =>
    Fin.cases (motive := fun _ => ℤ) 1
      (fun i' => Fin.cases (motive := fun _ => ℤ) 0 (fun j' => -2 * B i' j') j) i
  have h1 : (bord B).det = N'.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => Fin.cases (motive := fun _ => ℤ) 0 (fun _ => 1) i) 0 rfl
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · simp [bord, N']
    · simp [bord, N']
    · simp [bord, N']
    · simp [bord, N']
      ring
  have h2 : N'.submatrix Fin.succ Fin.succ = (-2 : ℤ) • B := by
    ext i j
    simp [N']
  rw [h1, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h3 : ∀ i : Fin m, N' i.succ 0 = 0 := fun i => by simp [N']
  simp only [h3, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.succAbove_zero, h2,
    det_smul, Fintype.card_fin]
  simp [N']

lemma natAbs_det_bord {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) :
    (bord B).det.natAbs = 2 ^ m * B.det.natAbs := by
  rw [det_bord, Int.natAbs_mul, Int.natAbs_pow]
  rfl

lemma isPM1_bord {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hB : IsZeroOne B) :
    IsPM1 (bord B) := by
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [bord]
  · simp [bord]
  · simp [bord]
  · rcases hB i' j' with h | h <;> simp [bord, h]

lemma sq_of_pm {x : ℤ} (h : x = 1 ∨ x = -1) : x * x = 1 := by
  rcases h with h | h <;> simp [h]

lemma pm_mul {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with h | h <;> rcases hy with h' | h' <;> simp [h, h']

lemma natAbs_prod_pm {k : ℕ} (r : Fin k → ℤ) (hr : ∀ i, r i = 1 ∨ r i = -1) :
    (∏ i, r i).natAbs = 1 := by
  apply Finset.prod_induction r (fun x : ℤ => x.natAbs = 1)
  · intro a b ha hb
    rw [Int.natAbs_mul, ha, hb]
  · rfl
  · intro i _
    rcases hr i with h | h <;> simp [h]

lemma pm1_eq_bord {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hM : IsPM1 M) :
    ∃ B : Matrix (Fin m) (Fin m) ℤ, IsZeroOne B ∧ (bord B).det.natAbs = M.det.natAbs := by
  let r : Fin (m + 1) → ℤ := fun i => M 0 0 * M i 0
  let c : Fin (m + 1) → ℤ := fun j => M 0 j
  have hr : ∀ i, r i = 1 ∨ r i = -1 := fun i => pm_mul (hM 0 0) (hM i 0)
  have hc : ∀ j, c j = 1 ∨ c j = -1 := fun j => hM 0 j
  let M2 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := diagonal r * M * diagonal c
  have hM2 : ∀ i j, M2 i j = r i * M i j * c j := by
    intro i j
    simp [M2, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hM2pm : ∀ i j, M2 i j = 1 ∨ M2 i j = -1 := fun i j => by
    rw [hM2]; exact pm_mul (pm_mul (hr i) (hM i j)) (hc j)
  have hrow : ∀ j, M2 0 j = 1 := by
    intro j
    rw [hM2]
    have h1 := sq_of_pm (hM 0 0)
    have h2 := sq_of_pm (hM 0 j)
    simp only [r, c]
    calc M 0 0 * M 0 0 * M 0 j * M 0 j = (M 0 0 * M 0 0) * (M 0 j * M 0 j) := by ring
      _ = 1 := by rw [h1, h2]; ring
  have hcol : ∀ i, M2 i 0 = 1 := by
    intro i
    rw [hM2]
    have h1 := sq_of_pm (hM 0 0)
    have h2 := sq_of_pm (hM i 0)
    simp only [r, c]
    calc M 0 0 * M i 0 * M i 0 * M 0 0 = (M 0 0 * M 0 0) * (M i 0 * M i 0) := by ring
      _ = 1 := by rw [h1, h2]; ring
  have hdet : M2.det.natAbs = M.det.natAbs := by
    simp only [M2, det_mul, det_diagonal, Int.natAbs_mul, natAbs_prod_pm r hr,
      natAbs_prod_pm c hc, one_mul, mul_one]
  let B : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i j => if M2 i.succ j.succ = 1 then 0 else 1
  refine ⟨B, ?_, ?_⟩
  · intro i j
    by_cases h : M2 i.succ j.succ = 1 <;> simp [B, h]
  · have hb : bord B = M2 := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · simp [bord, hrow]
      · simp [bord, hrow]
      · simp [bord, hcol]
      · rcases hM2pm i'.succ j'.succ with h | h <;> simp [bord, B, h]
    rw [hb, hdet]

lemma bdd_PM1 (n : ℕ) :
    BddAbove {d : ℕ | ∃ M : Matrix (Fin n) (Fin n) ℤ, IsPM1 M ∧ d = Int.natAbs M.det} := by
  apply Set.Finite.bddAbove
  apply (Set.finite_range (fun f : Fin n → Fin n → Bool =>
    Int.natAbs (Matrix.of fun i j => if f i j then (1 : ℤ) else -1).det)).subset
  rintro d ⟨M, hM, rfl⟩
  refine ⟨fun i j => decide (M i j = 1), ?_⟩
  have : (Matrix.of fun i j => if decide (M i j = 1) then (1 : ℤ) else -1) = M := by
    ext i j
    rcases hM i j with h | h <;> simp [h]
  simp only [this]

lemma bdd_01 (n : ℕ) :
    BddAbove {d : ℕ | ∃ M : Matrix (Fin n) (Fin n) ℤ, IsZeroOne M ∧ d = Int.natAbs M.det} := by
  apply Set.Finite.bddAbove
  apply (Set.finite_range (fun f : Fin n → Fin n → Bool =>
    Int.natAbs (Matrix.of fun i j => if f i j then (1 : ℤ) else 0).det)).subset
  rintro d ⟨M, hM, rfl⟩
  refine ⟨fun i j => decide (M i j = 1), ?_⟩
  have : (Matrix.of fun i j => if decide (M i j = 1) then (1 : ℤ) else 0) = M := by
    ext i j
    rcases hM i j with h | h <;> simp [h]
  simp only [this]

theorem part5 : ∀ n : ℕ, 0 < n → D n = 2 ^ (n - 1) * D01 (n - 1) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, Matrix.of fun _ _ => 1, fun i j => by simp, rfl⟩
    · rintro d ⟨M, hM, rfl⟩
      obtain ⟨B, hB, hdet⟩ := pm1_eq_bord M hM
      rw [← hdet, natAbs_det_bord]
      exact Nat.mul_le_mul_left _ (le_csSup (bdd_01 m) ⟨B, hB, rfl⟩)
  · have hne : {d : ℕ | ∃ M : Matrix (Fin m) (Fin m) ℤ, IsZeroOne M ∧
        d = Int.natAbs M.det}.Nonempty := ⟨_, 0, fun i j => by simp, rfl⟩
    obtain ⟨B, hB, hBd⟩ := Nat.sSup_mem hne (bdd_01 m)
    unfold D01
    rw [hBd, ← natAbs_det_bord]
    exact le_csSup (bdd_PM1 (m + 1)) ⟨bord B, isPM1_bord B hB, rfl⟩

end HadamardPart5

namespace HadamardParts34

open Real Set Matrix OMA.S_wp_hadamard_s_maximal_determinant_problem

lemma h_mono : MonotoneOn (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) (Ioi (-1)) := by
  have hd : ∀ x ∈ Ioi (-1 : ℝ), HasDerivAt (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
      (x ^ 2 / (1 + x)) x := by
    intro x hx
    have hx' : (0 : ℝ) < 1 + x := by simp at hx; linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have h2 := (h1.log hx'.ne').sub (hasDerivAt_id x)
    have h3 := h2.add ((hasDerivAt_pow 2 x).div_const 2)
    refine h3.congr_deriv ?_
    field_simp
    ring
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => x ^ 2 / (1 + x)) (convex_Ioi _) ?_ ?_ ?_
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : (0 : ℝ) < 1 + x := by simp at hx; linarith
    positivity

lemma m_anti : AntitoneOn (fun t : ℝ => 2 * Real.log (1 + t) - 2 * t + t ^ 2 / (1 + t))
    (Ioi (-1)) := by
  have hd : ∀ x ∈ Ioi (-1 : ℝ), HasDerivAt
      (fun t : ℝ => 2 * Real.log (1 + t) - 2 * t + t ^ 2 / (1 + t))
      (-(x ^ 2 / (1 + x) ^ 2)) x := by
    intro x hx
    have hx' : (0 : ℝ) < 1 + x := by simp at hx; linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have h2 := ((h1.log hx'.ne').const_mul 2).sub ((hasDerivAt_id x).const_mul 2)
    have h3 := h2.add ((hasDerivAt_pow 2 x).div h1 hx'.ne')
    refine h3.congr_deriv ?_
    field_simp
    ring
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x => -(x ^ 2 / (1 + x) ^ 2)) (convex_Ioi _) ?_ ?_ ?_
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : (0 : ℝ) < 1 + x := by simp at hx; linarith
    have : 0 ≤ x ^ 2 / (1 + x) ^ 2 := by positivity
    linarith

lemma m_nonpos {t : ℝ} (ht : 0 ≤ t) : 2 * Real.log (1 + t) - 2 * t + t ^ 2 / (1 + t) ≤ 0 := by
  have := m_anti (show (0 : ℝ) ∈ Ioi (-1) by norm_num) (show t ∈ Ioi (-1) by simp; linarith) ht
  simpa using this

lemma g_anti : AntitoneOn (fun t : ℝ => (t - Real.log (1 + t)) / t ^ 2) (Ioi 0) := by
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t - Real.log (1 + t)) / t ^ 2)
      ((2 * Real.log (1 + x) - 2 * x + x ^ 2 / (1 + x)) / x ^ 3) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hx' : (0 : ℝ) < 1 + x := by linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have h2 := (hasDerivAt_id x).sub (h1.log hx'.ne')
    have h3 := h2.div (hasDerivAt_pow 2 x) (by positivity)
    refine h3.congr_deriv ?_
    simp only [Pi.sub_apply, id]
    field_simp
    ring
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x => (2 * Real.log (1 + x) - 2 * x + x ^ 2 / (1 + x)) / x ^ 3) (convex_Ioi _) ?_ ?_ ?_
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : (0 : ℝ) < x := hx
    exact div_nonpos_of_nonpos_of_nonneg (m_nonpos hx0.le) (by positivity)


lemma pt_small {c y : ℝ} (hc : 0 < c) (hy1 : -1 ≤ y) (hyc : y ≤ c) :
    1 + y ≤ Real.exp (y - (c - Real.log (1 + c)) / c ^ 2 * y ^ 2) := by
  have hc1 : (0 : ℝ) < 1 + c := by linarith
  have hlogc : Real.log (1 + c) ≤ c := by
    have := Real.log_le_sub_one_of_pos hc1; linarith
  have hh : 0 ≤ Real.log (1 + c) - c + c ^ 2 / 2 := by
    have := h_mono (show (0 : ℝ) ∈ Ioi (-1) by norm_num) (show c ∈ Ioi (-1) by simp; linarith)
      hc.le
    simpa using this
  have hk0 : 0 ≤ (c - Real.log (1 + c)) / c ^ 2 := by
    apply div_nonneg <;> nlinarith
  have hk1 : (c - Real.log (1 + c)) / c ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  rcases eq_or_lt_of_le hy1 with h | h
  · rw [← h]; simp; positivity
  have hy' : 0 < 1 + y := by linarith
  rw [← Real.exp_log hy']
  apply Real.exp_le_exp.mpr
  rcases le_or_gt y 0 with h0 | h0
  · have := h_mono (show y ∈ Ioi (-1) by simpa using h) (show (0 : ℝ) ∈ Ioi (-1) by norm_num) h0
    simp at this
    have : (c - Real.log (1 + c)) / c ^ 2 * y ^ 2 ≤ 1 / 2 * y ^ 2 :=
      mul_le_mul_of_nonneg_right hk1 (sq_nonneg y)
    linarith
  · have := g_anti (show y ∈ Ioi 0 from h0) (show c ∈ Ioi 0 from hc) hyc
    simp only at this
    rw [le_div_iff₀ (by positivity)] at this
    linarith

lemma pt_big {c y : ℝ} (hc : 0 < c) (hyc : c ≤ y) :
    1 + y ≤ (1 + c) * Real.exp (y - c) := by
  have hc1 : (0 : ℝ) < 1 + c := by linarith
  have h1 := Real.add_one_le_exp ((y - c) / (1 + c))
  have h2 : (y - c) / (1 + c) ≤ y - c := by
    rw [div_le_iff₀ hc1]; nlinarith
  have h3 := Real.exp_le_exp.mpr h2
  have h4 : 1 + y = (1 + c) * ((y - c) / (1 + c) + 1) := by field_simp; ring
  rw [h4]
  apply mul_le_mul_of_nonneg_left _ hc1.le
  linarith

/-- The scalar inequality behind Barba-type bounds. -/
lemma scalar {k : ℕ} (y : Fin k → ℝ) (hy : ∀ i, -1 ≤ y i) {c : ℝ} (hc : 0 < c)
    (hs : ∑ i, y i = c) (hq : c ^ 2 ≤ ∑ i, y i ^ 2) : ∏ i, (1 + y i) ≤ 1 + c := by
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ 1 + y i := fun i _ => by linarith [hy i]
  by_cases hA : ∃ j, c ≤ y j
  · obtain ⟨j, hj⟩ := hA
    have hle : ∀ i ∈ Finset.univ, 1 + y i ≤
        Real.exp (y i) * (if i = j then (1 + c) * Real.exp (-c) else 1) := by
      intro i _
      by_cases hij : i = j
      · subst hij
        simp only [if_true]
        have := pt_big hc hj
        calc 1 + y i ≤ (1 + c) * Real.exp (y i - c) := this
          _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring
      · simp only [hij, if_false, mul_one]
        linarith [Real.add_one_le_exp (y i)]
    refine (Finset.prod_le_prod hnn hle).trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, hs, Finset.prod_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [mul_comm (1 + c), ← mul_assoc, ← Real.exp_add]
    simp
  · push Not at hA
    set k0 := (c - Real.log (1 + c)) / c ^ 2 with hk0
    have hle : ∀ i ∈ Finset.univ, 1 + y i ≤ Real.exp (y i - k0 * y i ^ 2) :=
      fun i _ => pt_small hc (hy i) (hA i).le
    refine (Finset.prod_le_prod hnn hle).trans ?_
    rw [← Real.exp_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
    have hc1 : (0 : ℝ) < 1 + c := by linarith
    have hk0n : 0 ≤ k0 := by
      have := Real.log_le_sub_one_of_pos hc1
      apply div_nonneg <;> nlinarith
    calc Real.exp (c - k0 * ∑ i, y i ^ 2) ≤ Real.exp (c - k0 * c ^ 2) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left hq hk0n]
      _ = 1 + c := by
          rw [hk0, div_mul_cancel₀ _ (by positivity), sub_sub_cancel, Real.exp_log hc1]


open Matrix in
lemma sum_sq_eigenvalues {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ) (hH : G.IsHermitian) :
    ∑ i, hH.eigenvalues i ^ 2 = ∑ i, ∑ j, G i j ^ 2 := by
  have hsym : ∀ i j, G j i = G i j := by
    intro i j
    have := congrFun (congrFun hH i) j
    simpa using this
  have h1 : (G * G).trace = ∑ i, ∑ j, G i j ^ 2 := by
    simp only [trace, diag_apply, mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym, sq]
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U : Matrix (Fin k) (Fin k) ℝ := (hH.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)
  set Dg : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hs' : G = U * Dg * star U := hs
  have h2 : Matrix.trace (G * G) = Matrix.trace (Dg * Dg) := by
    rw [hs']
    have e1 : U * Dg * star U * (U * Dg * star U) = U * (Dg * Dg * star U) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul]
    rw [e1, Matrix.trace_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [← h1, h2]
  simp [Dg, Matrix.trace, sq]

open Matrix in
lemma barba_gen {k : ℕ} (hk : 0 < k) (G : Matrix (Fin k) (Fin k) ℝ) (hG : G.PosSemidef)
    {d e : ℝ} (he : 0 < e) (hde : e < d) (hdiag : ∀ i, G i i = d)
    (hoff : ∀ i j, i ≠ j → e ^ 2 ≤ G i j ^ 2) :
    G.det ≤ (d - e) ^ (k - 1) * (d - e + k * e) := by
  have hH := hG.isHermitian
  set lam := hH.eigenvalues with hlam
  have ha : 0 < d - e := by linarith
  set a := d - e with ha_def
  have hdet := hH.det_eq_prod_eigenvalues
  have htr := hH.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id] at hdet htr
  have htr2 : G.trace = k * d := by
    simp [trace, hdiag]
  have hS1 : ∑ i, lam i = k * d := by rw [← htr, htr2]
  have hS2 : (k : ℝ) * d ^ 2 + k * (k - 1) * e ^ 2 ≤ ∑ i, lam i ^ 2 := by
    rw [sum_sq_eigenvalues G hH]
    have hrow : ∀ i, d ^ 2 + (k - 1) * e ^ 2 ≤ ∑ j, G i j ^ 2 := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag]
      have : ∑ j ∈ Finset.univ.erase i, e ^ 2 ≤ ∑ j ∈ Finset.univ.erase i, G i j ^ 2 :=
        Finset.sum_le_sum fun j hj => hoff i j (Finset.ne_of_mem_erase hj).symm
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hk] at this
      simp only [Nat.cast_one] at this
      linarith
    calc (k : ℝ) * d ^ 2 + k * (k - 1) * e ^ 2 = ∑ _i : Fin k, (d ^ 2 + (k - 1) * e ^ 2) := by
          simp; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => hrow i
  set y : Fin k → ℝ := fun i => lam i / a - 1 with hy
  have hy1 : ∀ i, -1 ≤ y i := by
    intro i
    have := hG.eigenvalues_nonneg i
    simp only [hy]
    have : 0 ≤ lam i / a := div_nonneg this ha.le
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : 0 < k * e / a := by positivity
  have hsy : ∑ i, y i = k * e / a := by
    simp only [hy, Finset.sum_sub_distrib, ← Finset.sum_div, hS1]
    simp
    field_simp
    ring
  have hqy : (k * e / a) ^ 2 ≤ ∑ i, y i ^ 2 := by
    have : ∀ i, y i ^ 2 = lam i ^ 2 * (1 / a ^ 2) - lam i * (2 / a) + 1 := by
      intro i; simp only [hy]; field_simp; ring
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hS1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have h3 : (k : ℝ) * d ^ 2 + k * (k - 1) * e ^ 2 - 2 * k * d * a + k * a ^ 2 =
        k ^ 2 * e ^ 2 := by rw [ha_def]; ring
    have h4 : (k * e / a) ^ 2 = ((k : ℝ) * d ^ 2 + k * (k - 1) * e ^ 2) * (1 / a ^ 2)
        - k * d * (2 / a) + k := by
      field_simp
      linear_combination -h3
    rw [h4]
    have : ((k : ℝ) * d ^ 2 + k * (k - 1) * e ^ 2) * (1 / a ^ 2) ≤
        (∑ i, lam i ^ 2) * (1 / a ^ 2) :=
      mul_le_mul_of_nonneg_right hS2 (by positivity)
    linarith
  have hsc := scalar y hy1 hc hsy hqy
  have hprod : ∏ i, lam i = a ^ k * ∏ i, (1 + y i) := by
    have : ∏ i, lam i = ∏ i, (a * (1 + y i)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hy]
      field_simp
      ring
    rw [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hdet, hprod]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  calc a ^ (m + 1) * ∏ i, (1 + y i) ≤ a ^ (m + 1) * (1 + ((m + 1 : ℕ) : ℝ) * e / a) :=
        mul_le_mul_of_nonneg_left hsc (by positivity)
    _ = a ^ m * (a + ((m + 1 : ℕ) : ℝ) * e) := by
        rw [pow_succ]; field_simp


theorem D_mem (n : ℕ) :
    ∃ M : Matrix (Fin n) (Fin n) ℤ, IsPM1 M ∧ D n = Int.natAbs M.det := by
  have hne : ({d : ℕ | ∃ M : Matrix (Fin n) (Fin n) ℤ, IsPM1 M ∧ d = Int.natAbs M.det}).Nonempty :=
    ⟨_, fun _ _ => 1, fun _ _ => Or.inl rfl, rfl⟩
  have hbdd : BddAbove {d : ℕ | ∃ M : Matrix (Fin n) (Fin n) ℤ, IsPM1 M ∧
      d = Int.natAbs M.det} := by
    refine ⟨n.factorial, ?_⟩
    rintro d ⟨M, hM, rfl⟩
    have h := Matrix.det_le (A := M) (abv := AbsoluteValue.abs) (x := 1) (fun i j => by
      rcases hM i j with h | h <;> simp [h])
    simp only [Fintype.card_fin, one_pow, nsmul_eq_mul, mul_one, AbsoluteValue.abs_apply] at h
    have h2 := Int.natCast_natAbs M.det
    omega
  exact Nat.sSup_mem hne hbdd

/-- The real Gram matrix of an integer matrix. -/
noncomputable def gram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  M.map (Int.cast : ℤ → ℝ) * (M.map (Int.cast : ℤ → ℝ))ᴴ

lemma gram_posSemidef {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : (gram M).PosSemidef :=
  posSemidef_self_mul_conjTranspose _

lemma gram_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    gram M i j = ((∑ k, M i k * M j k : ℤ) : ℝ) := by
  simp [gram, mul_apply]

lemma gram_diag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : IsPM1 M) (i : Fin n) :
    gram M i i = n := by
  rw [gram_apply]
  have : ∀ k, M i k * M i k = 1 := fun k => by rcases hM i k with h | h <;> simp [h]
  simp [this]

lemma gram_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : (gram M).det = (M.det : ℝ) ^ 2 := by
  have hdA : (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := by
    rw [show M.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix M from rfl,
      ← RingHom.map_det]
    rfl
  rw [gram, det_mul, det_conjTranspose, hdA]; simp [sq]

lemma inner_sub_even {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : IsPM1 M) (i j : Fin n) :
    (2 : ℤ) ∣ (∑ k, M i k * M j k) - n := by
  have : (∑ k, M i k * M j k) - n = ∑ k, (M i k * M j k - 1) := by
    simp [Finset.sum_sub_distrib]
  rw [this]
  refine Finset.dvd_sum fun k _ => ?_
  rcases hM i k with h | h <;> rcases hM j k with h' | h' <;> rw [h, h'] <;> decide

lemma sq_D {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hD : D n = Int.natAbs M.det) :
    ((D n : ℝ)) ^ 2 = (gram M).det := by
  rw [gram_det, hD, Nat.cast_natAbs]; simp

lemma rpow_half {x : ℝ} (hx : 0 ≤ x) (m : ℕ) (hm : (m : ℝ) = x) :
    x ^ (x / 2) = Real.sqrt (x ^ m) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx, hm]
  ring_nf

theorem part3 : ∀ n : ℕ, 0 < n → n % 2 = 1 →
      (D n : ℝ) ≤ Real.sqrt ((2 : ℝ) * n - 1) * ((n : ℝ) - 1) ^ (((n : ℝ) - 1) / 2) := by
  intro n hn hodd
  obtain ⟨M, hM, hD⟩ := D_mem n
  rcases Nat.lt_or_ge n 2 with h1 | h3
  · obtain rfl : n = 1 := by omega
    have hdet : M.det = M 0 0 := Matrix.det_unique M
    rw [hD, hdet]
    rcases hM 0 0 with h | h <;> rw [h] <;> norm_num
  have hn3 : 3 ≤ n := by omega
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hb := barba_gen hn (gram M) (gram_posSemidef M) (d := n) (e := 1) one_pos
    (by linarith) (gram_diag M hM) (by
      intro i j _
      rw [gram_apply]
      have hev := inner_sub_even M hM i j
      have hne : (∑ k, M i k * M j k) ≠ 0 := by
        intro h0
        rw [h0, zero_sub, Int.dvd_neg] at hev
        have : (2 : ℤ) ∣ (n : ℤ) := hev
        omega
      have : (1 : ℤ) ≤ (∑ k, M i k * M j k) ^ 2 := by
        have := Int.one_le_abs hne
        nlinarith [abs_mul_abs_self (∑ k, M i k * M j k)]
      exact_mod_cast this)
  rw [← sq_D M hD] at hb
  have hx : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  rw [rpow_half hx (n - 1) (by rw [Nat.cast_sub (by omega)]; simp),
    ← Real.sqrt_mul (by linarith)]
  apply Real.le_sqrt_of_sq_le
  calc ((D n : ℝ)) ^ 2 ≤ ((n : ℝ) - 1) ^ (n - 1) * ((n : ℝ) - 1 + n * 1) := hb
    _ = _ := by ring


lemma barba_idx {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (hG : G.PosSemidef)
    {d e : ℝ} (he : 0 < e) (hde : e < d) (hdiag : ∀ i, G i i = d)
    (hoff : ∀ i j, i ≠ j → e ^ 2 ≤ G i j ^ 2) :
    G.det ≤ (d - e) ^ (Fintype.card ι) * (1 + (Fintype.card ι : ℝ) * e / (d - e)) := by
  have ha : 0 < d - e := by linarith
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hk
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
    rw [Matrix.det_isEmpty, h0]
    simp
  set f := Fintype.equivFin ι
  have hb := barba_gen hk (G.submatrix f.symm f.symm) (hG.submatrix _) he hde
    (fun i => hdiag _) (fun i j hij => hoff _ _ (fun h => hij (f.symm.injective h)))
  rw [Matrix.det_submatrix_equiv_self] at hb
  refine hb.trans (le_of_eq ?_)
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 := ⟨Fintype.card ι - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel, pow_succ]
  field_simp

lemma one_le_det_one_add {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℝ)
    (hX : X.PosSemidef) : 1 ≤ (1 + X).det := by
  have hH := hX.isHermitian
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ)
  set Dg : Matrix ι ι ℝ := Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hs' : X = U * Dg * star U := hs
  have h1 : 1 + X = U * (1 + Dg) * star U := by
    rw [hs', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU']
  have h2 : (1 + X).det = (1 + Dg).det := by
    rw [h1, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, hU, det_one, one_mul]
  rw [h2]
  have h3 : (1 : Matrix ι ι ℝ) + Dg = Matrix.diagonal (fun i => 1 + hH.eigenvalues i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Dg]
    · simp [Dg, hij]
  rw [h3, det_diagonal]
  calc (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
    _ ≤ ∏ i, (1 + hH.eigenvalues i) := by
      apply Finset.prod_le_prod (fun _ _ => zero_le_one)
      intro i _
      linarith [hX.eigenvalues_nonneg i]


lemma psd_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (hS : S.PosSemidef) : ∃ B : Matrix ι ι ℝ, S = Bᴴ * B := by
  have hH := hS.isHermitian
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ)
  have hs' : S = U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := hs
  refine ⟨Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * star U, ?_⟩
  rw [conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose, conjTranspose_conjTranspose]
  conv_lhs => rw [hs']
  have hd : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      (Matrix.diagonal (star (fun i => Real.sqrt (hH.eigenvalues i)))) *
        Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp [Real.mul_self_sqrt (hS.eigenvalues_nonneg i)]
  rw [hd]
  simp only [Matrix.mul_assoc]
  rfl

lemma det_le_det_add {ι : Type*} [Fintype ι] [DecidableEq ι] (S T : Matrix ι ι ℝ)
    (hS : S.PosSemidef) (hT : T.PosSemidef) : S.det ≤ (S + T).det := by
  by_cases h : S.det = 0
  · rw [h]; exact (hS.add hT).det_nonneg
  obtain ⟨B, rfl⟩ := psd_factor S hS
  have hdB : B.det ≠ 0 := by
    intro h0; apply h; rw [det_mul, h0, mul_zero]
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdB
  set Bi := B⁻¹
  have h1 : Bi * B = 1 := Matrix.nonsing_inv_mul B hu
  have hX : (Biᴴ * T * Bi).PosSemidef := hT.conjTranspose_mul_mul_same Bi
  have heq : Bᴴ * B + T = Bᴴ * (1 + Biᴴ * T * Bi) * B := by
    have : Bᴴ * Biᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    congr 1
    calc T = (Bᴴ * Biᴴ) * T * (Bi * B) := by rw [this, h1, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hm : (Bᴴ * (1 + Biᴴ * T * Bi) * B).det = (Bᴴ * B).det * (1 + Biᴴ * T * Bi).det := by
    simp only [det_mul]; ring
  rw [heq, hm]
  have h0 : 0 ≤ (Bᴴ * B).det := (posSemidef_conjTranspose_mul_self B).det_nonneg
  have h2 := one_le_det_one_add _ hX
  nlinarith

lemma fischer {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (hG : G.PosSemidef)
    (p : ι → Prop) [DecidablePred p] :
    G.det ≤ (G.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det *
      (G.submatrix (Subtype.val : {i // ¬ p i} → ι) Subtype.val).det := by
  have hA0 := (hG.submatrix (Subtype.val : {i // p i} → ι)).det_nonneg
  have hC0 := (hG.submatrix (Subtype.val : {i // ¬ p i} → ι)).det_nonneg
  by_cases hd : G.det = 0
  · rw [hd]; exact mul_nonneg hA0 hC0
  have hGpd : G.PosDef := hG.posDef_iff_det_ne_zero.mpr hd
  set A := G.submatrix (Subtype.val : {i // p i} → ι) Subtype.val
  set C := G.submatrix (Subtype.val : {i // ¬ p i} → ι) Subtype.val
  set B := G.submatrix (Subtype.val : {i // p i} → ι) (Subtype.val : {i // ¬ p i} → ι)
  have hApd : A.PosDef := hGpd.submatrix Subtype.val_injective
  set e := Equiv.sumCompl p
  have hsym : ∀ i j, G j i = G i j := by
    intro i j
    have := congrFun (congrFun hG.isHermitian i) j
    simpa using this
  have hblk : G.submatrix e e = fromBlocks A B Bᴴ C := by
    ext (i | i) (j | j)
    · simp [e, A]
    · simp [e, B]
    · simp [e, B, hsym]
    · simp [e, C]
  have hGd : G.det = (fromBlocks A B Bᴴ C).det := by
    rw [← hblk, det_submatrix_equiv_self]
  let _ := hApd.isUnit.invertible
  have hpsd : (fromBlocks A B Bᴴ C).PosSemidef := hblk ▸ hG.submatrix e
  have hS : (C - Bᴴ * A⁻¹ * B).PosSemidef := (PosDef.fromBlocks₁₁ B C hApd).mp hpsd
  have hT : (Bᴴ * A⁻¹ * B).PosSemidef := hApd.posSemidef.inv.conjTranspose_mul_mul_same B
  rw [hGd, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  apply mul_le_mul_of_nonneg_left _ hA0
  have := det_le_det_add _ _ hS hT
  rwa [sub_add_cancel] at this


lemma mod4_aux {κ : Type*} [DecidableEq κ] (s : Finset κ) (x : κ → ℤ)
    (hx : ∀ k, x k = 1 ∨ x k = -1) :
    (4 : ℤ) ∣ ∑ k ∈ s, x k - s.card - 1 + ∏ k ∈ s, x k ∧
      (∏ k ∈ s, x k = 1 ∨ ∏ k ∈ s, x k = -1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    obtain ⟨hd, hp⟩ := ih
    push_cast
    rcases hx a with h | h <;> rcases hp with hp | hp <;> rw [h] <;> rw [hp] at hd ⊢ <;>
      refine ⟨?_, by norm_num⟩ <;> omega

lemma prod_pm {κ : Type*} [Fintype κ] [DecidableEq κ] (x : κ → ℤ) (hx : ∀ k, x k = 1 ∨ x k = -1) :
    ∏ k, x k = 1 ∨ ∏ k, x k = -1 := (mod4_aux Finset.univ x hx).2

lemma same_class {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : IsPM1 M) (hn : n % 4 = 2)
    (i j : Fin n) (hσ : ∏ k, M i k = ∏ k, M j k) : (4 : ℝ) ≤ gram M i j ^ 2 := by
  rw [gram_apply]
  have hpm : ∀ k, M i k * M j k = 1 ∨ M i k * M j k = -1 := fun k => by
    rcases hM i k with h | h <;> rcases hM j k with h' | h' <;> simp [h, h']
  have h4 := (mod4_aux Finset.univ (fun k => M i k * M j k) hpm).1
  rw [Finset.prod_mul_distrib, hσ, Finset.card_univ, Fintype.card_fin] at h4
  have h1 : (∏ k, M j k) * (∏ k, M j k) = 1 := by
    rcases prod_pm (fun k => M j k) (hM j) with h | h <;> rw [h] <;> norm_num
  rw [h1] at h4
  set s := ∑ k, M i k * M j k
  have hs : ∃ t, s = 4 * t + 2 := by
    obtain ⟨u, hu⟩ := h4
    exact ⟨(s - 2) / 4, by omega⟩
  obtain ⟨t, ht⟩ := hs
  have : (4 : ℤ) ≤ s ^ 2 := by
    rw [ht]
    rcases le_or_gt 0 t with h | h
    · nlinarith
    · have : t + 1 ≤ 0 := by omega
      nlinarith
  exact_mod_cast this

theorem part4 : ∀ n : ℕ, 0 < n → n % 4 = 2 →
      (D n : ℝ) ≤ ((2 : ℝ) * n - 2) * ((n : ℝ) - 2) ^ (((n : ℝ) - 2) / 2) := by
  intro n hn hmod
  obtain ⟨M, hM, hD⟩ := D_mem n
  rcases Nat.lt_or_ge n 3 with h1 | h3
  · obtain rfl : n = 2 := by omega
    have hle : (D 2 : ℝ) ≤ 2 := by
      rw [hD, Matrix.det_fin_two]
      rcases hM 0 0 with a | a <;> rcases hM 0 1 with b | b <;> rcases hM 1 0 with c | c <;>
        rcases hM 1 1 with d | d <;> rw [a, b, c, d] <;> norm_num
    norm_num
    exact_mod_cast hle
  have hn6 : 6 ≤ n := by omega
  have hnr : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  set G := gram M
  let p : Fin n → Prop := fun i => ∏ k, M i k = 1
  have hF := fischer G (gram_posSemidef M) p
  have hsig : ∀ i, ¬ p i → ∏ k, M i k = -1 := fun i h =>
    (prod_pm (fun k => M i k) (hM i)).resolve_left h
  have hA := barba_idx (G.submatrix (Subtype.val : {i // p i} → Fin n) Subtype.val)
    ((gram_posSemidef M).submatrix _) (d := n) (e := 2) two_pos (by linarith)
    (fun i => gram_diag M hM _) (fun i j hij => by
      have : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [this]
      exact same_class M hM hmod i.1 j.1 (by rw [i.2, j.2]))
  have hC := barba_idx (G.submatrix (Subtype.val : {i // ¬ p i} → Fin n) Subtype.val)
    ((gram_posSemidef M).submatrix _) (d := n) (e := 2) two_pos (by linarith)
    (fun i => gram_diag M hM _) (fun i j hij => by
      have : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [this]
      exact same_class M hM hmod i.1 j.1 (by rw [hsig _ i.2, hsig _ j.2]))
  have hcard : Fintype.card {i // ¬ p i} = n - Fintype.card {i // p i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
  have hle : Fintype.card {i // p i} ≤ n := by
    have := Fintype.card_subtype_le p
    simpa using this
  set a := Fintype.card {i // p i}
  set b := Fintype.card {i // ¬ p i}
  have hab : a + b = n := by omega
  set q : ℝ := (n : ℝ) - 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hdet := sq_D M hD
  have hA0 := ((gram_posSemidef M).submatrix (Subtype.val : {i // p i} → Fin n)).det_nonneg
  have hbound : ((D n : ℝ)) ^ 2 ≤ q ^ (n - 2) * ((q + 2 * a) * (q + 2 * b)) := by
    rw [hdet]
    refine hF.trans ((mul_le_mul hA hC
      ((gram_posSemidef M).submatrix _).det_nonneg (by positivity)).trans (le_of_eq ?_))
    have hpow : q ^ a * q ^ b = q ^ (n - 2) * q ^ 2 := by
      rw [← pow_add, ← pow_add, hab]; congr 1; omega
    calc q ^ a * (1 + a * 2 / q) * (q ^ b * (1 + b * 2 / q))
        = q ^ a * q ^ b * ((q + 2 * a) * (q + 2 * b)) / q ^ 2 := by field_simp
      _ = _ := by rw [hpow]; field_simp
  have hamgm : (q + 2 * a) * (q + 2 * b) ≤ ((2 : ℝ) * n - 2) ^ 2 := by
    have : (a : ℝ) + b = n := by exact_mod_cast hab
    nlinarith [sq_nonneg ((a : ℝ) - b)]
  have hx : (0 : ℝ) ≤ q := hq0.le
  rw [rpow_half hx (n - 2) (by rw [Nat.cast_sub (by omega)]; simp [hq])]
  have hr : 0 ≤ ((2 : ℝ) * n - 2) * Real.sqrt (q ^ (n - 2)) := by
    apply mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  rw [← pow_le_pow_iff_left₀ (by positivity) hr two_ne_zero, mul_pow,
    Real.sq_sqrt (by positivity)]
  calc ((D n : ℝ)) ^ 2 ≤ q ^ (n - 2) * ((q + 2 * a) * (q + 2 * b)) := hbound
    _ ≤ q ^ (n - 2) * ((2 : ℝ) * n - 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hamgm (by positivity)
    _ = _ := by ring

end HadamardParts34

theorem OMA.solution : type_of% @OMA.S_wp_hadamard_s_maximal_determinant_problem.main :=
  ⟨HadamardParts.part1, HadamardParts.part2, HadamardParts34.part3, HadamardParts34.part4,
    HadamardPart5.part5, HadamardParts.part6⟩
