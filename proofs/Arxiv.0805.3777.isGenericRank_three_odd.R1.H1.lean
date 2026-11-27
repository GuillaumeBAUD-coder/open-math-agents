import OMAReductions.R_Arxiv_0805_3777_isGenericRank_three_odd_R1

/-! Lower bound on the generic CP rank of 3 x (2p+1) x (2p+1) complex tensors. -/

-- Step Arxiv.0805.3777.isGenericRank_three_odd.R1.H1: hypothesis H1 of reduction Arxiv.0805.3777.isGenericRank_three_odd.R1
-- Credit: @green-notes
-- H1 := ∀ (p : ℕ), 1 ≤ p → ∃ U : Set (Holor ℂ [3, 2 * p + 1, 2 * p + 1]), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, 3 * p + 2 ≤ T.cprank

namespace Arxiv08053777H1

open scoped Matrix Arxiv.«0805.3777»

private def idx3 {n : ℕ} (k : Fin 3) (i j : Fin n) : HolorIndex [3, n, n] :=
  ⟨[k.1, i.1, j.1],
    List.Forall₂.cons k.isLt (List.Forall₂.cons i.isLt (List.Forall₂.cons j.isLt List.Forall₂.nil))⟩

private def sliceMat {R : Type*} {n : ℕ} (T : Holor R [3, n, n]) (k : Fin 3) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => T (idx3 k i j)

private lemma sliceMat_continuous {n : ℕ} (k : Fin 3) :
    Continuous (fun T : Holor ℂ [3, n, n] => sliceMat T k) :=
  continuous_matrix fun i j => continuous_apply (idx3 k i j)

private noncomputable def commAdjugate {R : Type*} [CommRing R] {n : ℕ}
    (T : Holor R [3, n, n]) : Matrix (Fin n) (Fin n) R :=
  sliceMat T 1 * (sliceMat T 0).adjugate * sliceMat T 2 -
    sliceMat T 2 * (sliceMat T 0).adjugate * sliceMat T 1

private noncomputable def polyObstruction {R : Type*} [CommRing R] {n : ℕ}
    (T : Holor R [3, n, n]) : R :=
  (sliceMat T 0).det * (commAdjugate T).det

private lemma polyObstruction_continuous {n : ℕ} :
    Continuous (fun T : Holor ℂ [3, n, n] => polyObstruction T) := by
  have h0 : Continuous (fun T : Holor ℂ [3, n, n] => sliceMat T 0) := sliceMat_continuous 0
  have h1 : Continuous (fun T : Holor ℂ [3, n, n] => sliceMat T 1) := sliceMat_continuous 1
  have h2 : Continuous (fun T : Holor ℂ [3, n, n] => sliceMat T 2) := sliceMat_continuous 2
  have hadj : Continuous (fun T : Holor ℂ [3, n, n] => (sliceMat T 0).adjugate) :=
    h0.matrix_adjugate
  have hcomm : Continuous (fun T : Holor ℂ [3, n, n] => commAdjugate T) :=
    ((h1.matrix_mul hadj).matrix_mul h2).sub ((h2.matrix_mul hadj).matrix_mul h1)
  exact h0.matrix_det.mul hcomm.matrix_det

private lemma sliceMat_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (T : Holor R [3, n, n]) (k : Fin 3) :
    sliceMat (fun idx => f (T idx)) k = f.mapMatrix (sliceMat T k) :=
  rfl

private lemma map_polyObstruction {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (T : Holor R [3, n, n]) :
    f (polyObstruction T) = polyObstruction (fun idx => f (T idx)) := by
  simp only [polyObstruction, commAdjugate, map_mul, map_sub, RingHom.map_det,
    RingHom.map_adjugate, ← sliceMat_map]

private def witnessMat0 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := 1

private def witnessMat1 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => (i.1 : ℂ)

private def witnessMat2 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if (i.1 + 1) % n = j.1 then (1 : ℂ) else 0

private def witnessTensor (n : ℕ) : Holor ℂ [3, n, n] := fun idx =>
  match idx.1 with
  | [0, i, j] => if h : i < n ∧ j < n then witnessMat0 n ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  | [1, i, j] => if h : i < n ∧ j < n then witnessMat1 n ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  | [2, i, j] => if h : i < n ∧ j < n then witnessMat2 n ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  | _ => 0

private lemma sliceMat_witness_0 (n : ℕ) : sliceMat (witnessTensor n) 0 = witnessMat0 n := by
  ext i j
  simp [sliceMat, idx3, witnessTensor]

private lemma sliceMat_witness_1 (n : ℕ) : sliceMat (witnessTensor n) 1 = witnessMat1 n := by
  ext i j
  simp [sliceMat, idx3, witnessTensor]

private lemma sliceMat_witness_2 (n : ℕ) : sliceMat (witnessTensor n) 2 = witnessMat2 n := by
  ext i j
  simp [sliceMat, idx3, witnessTensor]

private lemma polyObstruction_witness_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    polyObstruction (witnessTensor n) ≠ 0 := by
  have hdet0 : (sliceMat (witnessTensor n) 0).det = 1 := by
    rw [sliceMat_witness_0, witnessMat0, Matrix.det_one]
  have hadj0 : (sliceMat (witnessTensor n) 0).adjugate = 1 := by
    rw [sliceMat_witness_0, witnessMat0, Matrix.adjugate_one]
  have hcomm_eq :
      commAdjugate (witnessTensor n) =
        witnessMat1 n * witnessMat2 n - witnessMat2 n * witnessMat1 n := by
    simp [commAdjugate, sliceMat_witness_1, sliceMat_witness_2, hadj0]
  have hcomm_det : (commAdjugate (witnessTensor n)).det ≠ 0 := by
    intro hzero
    obtain ⟨x, hxne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
    apply hxne
    ext j
    let nextIdx : Fin n → Fin n := fun i => ⟨(i.1 + 1) % n, Nat.mod_lt _ (by omega)⟩
    have hshift : ∀ i : Fin n, x (nextIdx i) = 0 := by
      intro i
      have hi := congrFun hmul i
      rw [hcomm_eq, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hi
      have h2_mul : ∀ y : Fin n → ℂ, (witnessMat2 n *ᵥ y) i = y (nextIdx i) := by
        intro y
        simp only [witnessMat2, Matrix.mulVec, dotProduct, Matrix.of_apply]
        rw [Finset.sum_eq_single (nextIdx i)]
        · simp [nextIdx]
        · intro k _ hkne
          have hne_val : (i.1 + 1) % n ≠ k.1 := by
            intro heq
            apply hkne
            exact Fin.ext heq.symm
          simp [hne_val]
        · intro hmem
          exact absurd (Finset.mem_univ (nextIdx i)) hmem
      have h1_mul : ∀ (k : Fin n) (y : Fin n → ℂ),
          (witnessMat1 n *ᵥ y) k = (k.1 : ℂ) * y k := by
        intro k y
        simp [witnessMat1, Matrix.mulVec_diagonal]
      have h12 : (witnessMat1 n *ᵥ (witnessMat2 n *ᵥ x)) i = (i.1 : ℂ) * x (nextIdx i) := by
        rw [h1_mul i (witnessMat2 n *ᵥ x), h2_mul x]
      have h21 : (witnessMat2 n *ᵥ (witnessMat1 n *ᵥ x)) i =
          ((nextIdx i).1 : ℂ) * x (nextIdx i) := by
        rw [h2_mul (witnessMat1 n *ᵥ x), h1_mul (nextIdx i) x]
      have hdiff : ((i.1 : ℂ) - ((nextIdx i).1 : ℂ)) * x (nextIdx i) = 0 := by
        rw [Pi.sub_apply, h12, h21, ← sub_mul] at hi
        exact hi
      have hne_coeff : (i.1 : ℂ) - ((nextIdx i).1 : ℂ) ≠ 0 := by
        rw [sub_ne_zero]
        intro hcast
        have hval : i.1 = (i.1 + 1) % n := Nat.cast_injective hcast
        by_cases hlt : i.1 + 1 < n
        · rw [Nat.mod_eq_of_lt hlt] at hval
          omega
        · have heq : i.1 + 1 = n := by omega
          rw [heq, Nat.mod_self] at hval
          omega
      exact (mul_eq_zero.mp hdiff).resolve_left hne_coeff
    let prevIdx : Fin n := ⟨(j.1 + n - 1) % n, Nat.mod_lt _ (by omega)⟩
    have hprev : nextIdx prevIdx = j := by
      ext
      dsimp only [nextIdx, prevIdx]
      have hle : 1 ≤ j.1 + n := by omega
      have hmod : ((j.1 + n - 1) % n + 1) % n = (j.1 + n - 1 + 1) % n := by
        simp [Nat.add_mod]
      rw [hmod, Nat.sub_add_cancel hle, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    simpa [hprev] using hshift prevIdx
  rw [polyObstruction, hdet0, one_mul]
  exact hcomm_det

private lemma open_and_dense_nonvanishing {n : ℕ} (hn : 2 ≤ n) :
    let U : Set (Holor ℂ [3, n, n]) := {T | polyObstruction T ≠ 0}
    IsOpen U ∧ Dense U := by
  intro U
  refine ⟨isOpen_ne.preimage polyObstruction_continuous, ?_⟩
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro T
  let Tpoly : Holor (Polynomial ℂ) [3, n, n] := fun idx =>
    Polynomial.C (T idx) + Polynomial.X * Polynomial.C (witnessTensor n idx - T idx)
  let P : Polynomial ℂ := polyObstruction Tpoly
  have hP_eval : ∀ t : ℂ, P.eval t =
      polyObstruction (fun idx => T idx + t * (witnessTensor n idx - T idx)) := by
    intro t
    have h := map_polyObstruction (Polynomial.evalRingHom t) Tpoly
    simpa [P, Tpoly, Polynomial.coe_evalRingHom] using h
  have hP_ne : P ≠ 0 := by
    intro h0
    have hev := hP_eval 1
    rw [h0, Polynomial.eval_zero] at hev
    have hW : (fun idx => T idx + 1 * (witnessTensor n idx - T idx)) = witnessTensor n := by
      ext idx
      ring
    rw [hW] at hev
    exact polyObstruction_witness_ne_zero hn hev.symm
  let seq : ℕ → ℂ := fun k => 1 / ((k : ℂ) + 1)
  have hseq_inj : Function.Injective seq := by
    intro a b hab
    have hab' : (a : ℂ) + 1 = (b : ℂ) + 1 := by
      simpa [seq] using hab
    exact Nat.cast_injective (add_right_cancel hab')
  let bad : Set ℕ := seq ⁻¹' (P.roots.toFinset : Set ℂ)
  have hbad_fin : bad.Finite :=
    (P.roots.toFinset.finite_toSet).preimage hseq_inj.injOn
  obtain ⟨N, hN⟩ := hbad_fin.bddAbove
  let pts : ℕ → Holor ℂ [3, n, n] := fun k =>
    fun idx => T idx + seq k * (witnessTensor n idx - T idx)
  have h_tend : Filter.Tendsto pts Filter.atTop (nhds T) := by
    refine tendsto_pi_nhds.2 fun idx => ?_
    have hs : Filter.Tendsto seq Filter.atTop (nhds (0 : ℂ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := hs.mul_const (witnessTensor n idx - T idx)
    simpa [pts, zero_mul, add_zero] using tendsto_const_nhds.add hmul
  have h_mem : ∀ᶠ k in Filter.atTop, pts k ∈ U := by
    refine Filter.eventually_atTop.2 ⟨N + 1, fun k hk => ?_⟩
    show polyObstruction (pts k) ≠ 0
    rw [← hP_eval (seq k)]
    intro hroot
    have hk_mem : k ∈ bad := by
      simp only [bad, Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hP_ne).2 hroot
    have hle := hN hk_mem
    omega
  exact mem_closure_of_tendsto h_tend h_mem

private lemma cprankMax1_decomp {n : ℕ} {x : Holor ℂ [3, n, n]} (hx : Holor.CPRankMax1 x) :
    ∃ (α β γ : ℂ) (v w : Fin n → ℂ),
      (∀ i j : Fin n, sliceMat x 0 i j = α * v i * w j) ∧
      (∀ i j : Fin n, sliceMat x 1 i j = β * v i * w j) ∧
      (∀ i j : Fin n, sliceMat x 2 i j = γ * v i * w j) := by
  cases hx with
  | cons u y hy =>
    cases hy with
    | cons v z hz =>
      cases hz with
      | cons w c hc =>
        cases hc with
        | nil c =>
          let c0 : ℂ := c ⟨[], List.Forall₂.nil⟩
          let u0 : ℂ := u ⟨[0], List.Forall₂.cons (by omega : 0 < 3) List.Forall₂.nil⟩ * c0
          let u1 : ℂ := u ⟨[1], List.Forall₂.cons (by omega : 1 < 3) List.Forall₂.nil⟩ * c0
          let u2 : ℂ := u ⟨[2], List.Forall₂.cons (by omega : 2 < 3) List.Forall₂.nil⟩ * c0
          let vv : Fin n → ℂ := fun i => v ⟨[i.1], List.Forall₂.cons i.isLt List.Forall₂.nil⟩
          let ww : Fin n → ℂ := fun j => w ⟨[j.1], List.Forall₂.cons j.isLt List.Forall₂.nil⟩
          refine ⟨u0, u1, u2, vv, ww, ?_, ?_, ?_⟩
          · intro i j
            change u ⟨[0], _⟩ * (v ⟨[i.1], _⟩ * (w ⟨[j.1], _⟩ * c ⟨[], _⟩)) = u0 * vv i * ww j
            dsimp only [u0, c0, vv, ww]
            ring
          · intro i j
            change u ⟨[1], _⟩ * (v ⟨[i.1], _⟩ * (w ⟨[j.1], _⟩ * c ⟨[], _⟩)) = u1 * vv i * ww j
            dsimp only [u1, c0, vv, ww]
            ring
          · intro i j
            change u ⟨[2], _⟩ * (v ⟨[i.1], _⟩ * (w ⟨[j.1], _⟩ * c ⟨[], _⟩)) = u2 * vv i * ww j
            dsimp only [u2, c0, vv, ww]
            ring

private lemma cprankMax_decomp {n : ℕ} :
    ∀ (r : ℕ) {T : Holor ℂ [3, n, n]}, Holor.CPRankMax r T →
      ∃ (α β γ : Fin r → ℂ) (v w : Fin r → Fin n → ℂ),
        (∀ i j : Fin n, sliceMat T 0 i j = ∑ k : Fin r, α k * v k i * w k j) ∧
        (∀ i j : Fin n, sliceMat T 1 i j = ∑ k : Fin r, β k * v k i * w k j) ∧
        (∀ i j : Fin n, sliceMat T 2 i j = ∑ k : Fin r, γ k * v k i * w k j)
  | 0, T, h => by
    cases h with
    | zero =>
      refine ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩ <;>
        intro i j <;> simp [sliceMat] <;> rfl
  | r + 1, T, h => by
    cases h with
    | succ _ x y hx hy =>
      obtain ⟨a0, b0, c0, v0, w0, hx0, hx1, hx2⟩ := cprankMax1_decomp hx
      obtain ⟨ar, br, cr, vr, wr, hy0, hy1, hy2⟩ := cprankMax_decomp r hy
      refine ⟨Fin.cons a0 ar, Fin.cons b0 br, Fin.cons c0 cr,
        Fin.cons v0 vr, Fin.cons w0 wr, ?_, ?_, ?_⟩
      · intro i j
        have hadd : sliceMat (x + y) 0 i j = sliceMat x 0 i j + sliceMat y 0 i j := rfl
        rw [hadd, hx0 i j, hy0 i j, Fin.sum_univ_succ]
        simp
      · intro i j
        have hadd : sliceMat (x + y) 1 i j = sliceMat x 1 i j + sliceMat y 1 i j := rfl
        rw [hadd, hx1 i j, hy1 i j, Fin.sum_univ_succ]
        simp
      · intro i j
        have hadd : sliceMat (x + y) 2 i j = sliceMat x 2 i j + sliceMat y 2 i j := rfl
        rw [hadd, hx2 i j, hy2 i j, Fin.sum_univ_succ]
        simp

private lemma sum_split_nz {r : ℕ} (α : Fin r → ℂ) (f : Fin r → ℂ) :
    (∑ k : Fin r, f k) =
      (∑ k : {k : Fin r // α k ≠ 0}, f k.1) + ∑ k : {k : Fin r // α k = 0}, f k.1 := by
  let e : {k : Fin r // α k ≠ 0} ⊕ {k : Fin r // α k = 0} ≃ Fin r :=
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun k => if h : α k ≠ 0 then Sum.inl ⟨k, h⟩ else Sum.inr ⟨k, not_not.mp h⟩
      left_inv := fun s => by
        cases s with
        | inl k => simp [k.2]
        | inr k => simp [k.2]
      right_inv := fun k => by
        by_cases h : α k ≠ 0 <;> simp [h] }
  rw [← Equiv.sum_comp e f, Fintype.sum_sum_type]
  rfl

private lemma commAdjugate_det_eq_zero_of_cprankMax {p r : ℕ} {T : Holor ℂ [3, 2 * p + 1, 2 * p + 1]}
    (hr : r ≤ 3 * p + 1) (hcp : Holor.CPRankMax r T)
    (hdet0 : (sliceMat T 0).det ≠ 0) :
    (commAdjugate T).det = 0 := by
  let n : ℕ := 2 * p + 1
  obtain ⟨α, β, γ, v, w, hA0, hA1, hA2⟩ := cprankMax_decomp r hcp
  let A₀ : Matrix (Fin n) (Fin n) ℂ := sliceMat T 0
  let A₁ : Matrix (Fin n) (Fin n) ℂ := sliceMat T 1
  let A₂ : Matrix (Fin n) (Fin n) ℂ := sliceMat T 2
  have hu : IsUnit A₀.det := hdet0.isUnit
  have hinv_mul : A₀⁻¹ * A₀ = 1 := Matrix.nonsing_inv_mul A₀ hu
  have hadj_eq : A₀.adjugate = A₀.det • A₀⁻¹ := by
    have hm := congrArg (fun M => A₀⁻¹ * M) (Matrix.mul_adjugate A₀)
    simpa [← Matrix.mul_assoc, hinv_mul, Matrix.mul_smul] using hm
  let B : Matrix (Fin n) (Fin n) ℂ := A₀⁻¹ * A₁
  let C : Matrix (Fin n) (Fin n) ℂ := A₀⁻¹ * A₂
  let K := {k : Fin r // α k ≠ 0}
  let Kc := {k : Fin r // α k = 0}
  let vtilde : Fin r → Fin n → ℂ := fun k => A₀⁻¹ *ᵥ v k
  let u : K → Fin n → ℂ := fun k => α k.1 • vtilde k.1
  let b₁ : K → ℂ := fun k => β k.1 / α k.1
  let b₂ : K → ℂ := fun k => γ k.1 / α k.1
  have hvtilde_sum : ∀ (c : Fin r → ℂ) (x : Fin n → ℂ) (i : Fin n),
      (A₀⁻¹ *ᵥ (Matrix.of (fun a b => ∑ k : Fin r, c k * v k a * w k b) *ᵥ x)) i =
        ∑ k : Fin r, c k * (w k ⬝ᵥ x) * vtilde k i := by
    intro c x i
    simp only [vtilde, Matrix.mulVec, dotProduct, Matrix.of_apply]
    have hstep1 :
        ∑ a : Fin n, A₀⁻¹ i a * ∑ b : Fin n, (∑ k : Fin r, c k * v k a * w k b) * x b =
          ∑ a : Fin n, ∑ b : Fin n, ∑ k : Fin r,
            c k * (w k b * x b) * (A₀⁻¹ i a * v k a) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hstep2 :
        ∑ a : Fin n, ∑ b : Fin n, ∑ k : Fin r, c k * (w k b * x b) * (A₀⁻¹ i a * v k a) =
          ∑ k : Fin r, ∑ b : Fin n, ∑ a : Fin n,
            c k * (w k b * x b) * (A₀⁻¹ i a * v k a) := by
      rw [Finset.sum_comm]
      have hinner :
          (∑ b : Fin n, ∑ a : Fin n, ∑ k : Fin r, c k * (w k b * x b) * (A₀⁻¹ i a * v k a)) =
            ∑ b : Fin n, ∑ k : Fin r, ∑ a : Fin n, c k * (w k b * x b) * (A₀⁻¹ i a * v k a) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
      rw [hinner, Finset.sum_comm]
    have hstep3 :
        ∑ k : Fin r, ∑ b : Fin n, ∑ a : Fin n, c k * (w k b * x b) * (A₀⁻¹ i a * v k a) =
          ∑ k : Fin r, c k * (∑ b : Fin n, w k b * x b) * ∑ a : Fin n, A₀⁻¹ i a * v k a := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hs1 :
          (∑ b : Fin n, ∑ a : Fin n, c k * (w k b * x b) * (A₀⁻¹ i a * v k a)) =
            ∑ b : Fin n, c k * (w k b * x b) * ∑ a : Fin n, A₀⁻¹ i a * v k a :=
        Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
      rw [hs1, ← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]
    exact hstep1.trans (hstep2.trans hstep3)
  have hA0_mat : A₀ = Matrix.of (fun a b => ∑ k : Fin r, α k * v k a * w k b) := by
    ext a b; exact hA0 a b
  have hA1_mat : A₁ = Matrix.of (fun a b => ∑ k : Fin r, β k * v k a * w k b) := by
    ext a b; exact hA1 a b
  have hA2_mat : A₂ = Matrix.of (fun a b => ∑ k : Fin r, γ k * v k a * w k b) := by
    ext a b; exact hA2 a b
  let U : (K → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun z i => ∑ k : K, z k * u k i
      map_add' := fun z₁ z₂ => by
        ext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        ext i; simp [Finset.mul_sum, mul_assoc] }
  let W : (Fin n → ℂ) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun x k => w k.1 ⬝ᵥ x
      map_add' := fun x₁ x₂ => by
        ext k; simp [dotProduct_add]
      map_smul' := fun c x => by
        ext k; simp [dotProduct_smul] }
  let D₁ : (K → ℂ) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun z k => b₁ k * z k
      map_add' := fun z₁ z₂ => by
        ext k; simp [mul_add]
      map_smul' := fun c z => by
        ext k; simp [mul_left_comm] }
  let D₂ : (K → ℂ) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun z k => b₂ k * z k
      map_add' := fun z₁ z₂ => by
        ext k; simp [mul_add]
      map_smul' := fun c z => by
        ext k; simp [mul_left_comm] }
  have hUW : ∀ x : Fin n → ℂ, U (W x) = x := by
    intro x
    ext i
    have hmul : (A₀⁻¹ *ᵥ ((Matrix.of fun a b => ∑ k : Fin r, α k * v k a * w k b) *ᵥ x)) i = x i := by
      rw [← hA0_mat, Matrix.mulVec_mulVec, hinv_mul, Matrix.one_mulVec]
    rw [← hmul, hvtilde_sum α x i, sum_split_nz α]
    have hzero : (∑ k : Kc, α k.1 * (w k.1 ⬝ᵥ x) * vtilde k.1 i) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [k.2]
    rw [hzero, add_zero]
    dsimp only [U, W, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [u, Pi.smul_apply, smul_eq_mul]
    ring
  have hU_surj : Function.Surjective U := fun x => ⟨W x, hUW x⟩
  have hU_range : LinearMap.range U = ⊤ := LinearMap.range_eq_top.mpr hU_surj
  let Q : (K → ℂ) →ₗ[ℂ] (K → ℂ) := LinearMap.id - W.comp U
  have hQ_ker : ∀ z : K → ℂ, Q z ∈ LinearMap.ker U := by
    intro z
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, hUW (U z), sub_self]
  let B_K : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := U.comp (D₁.comp W)
  let C_K : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := U.comp (D₂.comp W)
  let E₁ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x => ∑ j : Kc, (β j.1 * (w j.1 ⬝ᵥ x)) • vtilde j.1
      map_add' := fun x₁ x₂ => by
        simp [dotProduct_add, mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp [dotProduct_smul, Finset.smul_sum, smul_smul, mul_left_comm] }
  let E₂ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x => ∑ j : Kc, (γ j.1 * (w j.1 ⬝ᵥ x)) • vtilde j.1
      map_add' := fun x₁ x₂ => by
        simp [dotProduct_add, mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp [dotProduct_smul, Finset.smul_sum, smul_smul, mul_left_comm] }
  have hB_split : ∀ x : Fin n → ℂ, B *ᵥ x = B_K x + E₁ x := by
    intro x
    ext i
    dsimp only [B, B_K, E₁, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Pi.add_apply, Finset.sum_apply, ← Matrix.mulVec_mulVec, hA1_mat, hvtilde_sum β x i,
      sum_split_nz α]
    congr 1
    simp only [U, D₁, W, LinearMap.coe_mk, AddHom.coe_mk, u, b₁, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hne : α k.1 ≠ 0 := k.2
    field_simp [hne]
  have hC_split : ∀ x : Fin n → ℂ, C *ᵥ x = C_K x + E₂ x := by
    intro x
    ext i
    dsimp only [C, C_K, E₂, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Pi.add_apply, Finset.sum_apply, ← Matrix.mulVec_mulVec, hA2_mat, hvtilde_sum γ x i,
      sum_split_nz α]
    congr 1
    simp only [U, D₂, W, LinearMap.coe_mk, AddHom.coe_mk, u, b₂, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hne : α k.1 ≠ 0 := k.2
    field_simp [hne]
  let Φ₁ : (Fin n → ℂ) →ₗ[ℂ] LinearMap.ker U :=
    { toFun := fun x => ⟨Q (D₁ (W x)), hQ_ker _⟩
      map_add' := fun x₁ x₂ => by ext; simp
      map_smul' := fun c x => by ext; simp }
  let Φ₂ : (Fin n → ℂ) →ₗ[ℂ] LinearMap.ker U :=
    { toFun := fun x => ⟨Q (D₂ (W x)), hQ_ker _⟩
      map_add' := fun x₁ x₂ => by ext; simp
      map_smul' := fun c x => by ext; simp }
  let Φ₃ : (Fin n → ℂ) →ₗ[ℂ] (Kc → ℂ) :=
    { toFun := fun x j => w j.1 ⬝ᵥ x
      map_add' := fun x₁ x₂ => by ext j; simp [dotProduct_add]
      map_smul' := fun c x => by ext j; simp [dotProduct_smul] }
  let Φ₄ : (Fin n → ℂ) →ₗ[ℂ] (Kc → ℂ) :=
    { toFun := fun x j => β j.1 * (w j.1 ⬝ᵥ (C *ᵥ x)) - γ j.1 * (w j.1 ⬝ᵥ (B_K x))
      map_add' := fun x₁ x₂ => by
        ext j
        simp only [Matrix.mulVec_add, map_add, dotProduct_add, Pi.add_apply]
        ring
      map_smul' := fun c x => by
        ext j
        simp only [Matrix.mulVec_smul, map_smul, dotProduct_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  let Φ : (Fin n → ℂ) →ₗ[ℂ] (LinearMap.ker U × LinearMap.ker U × (Kc → ℂ) × (Kc → ℂ)) :=
    Φ₁.prod (Φ₂.prod (Φ₃.prod Φ₄))
  have hker_dim : Module.finrank ℂ (LinearMap.ker U) + n = Fintype.card K := by
    have h := LinearMap.finrank_range_add_finrank_ker U
    rw [hU_range, finrank_top, Module.finrank_pi ℂ, Module.finrank_pi ℂ,
      Fintype.card_fin] at h
    omega
  have hcard_split : Fintype.card K + Fintype.card Kc = r := by
    let e : K ⊕ Kc ≃ Fin r :=
      { toFun := Sum.elim Subtype.val Subtype.val
        invFun := fun k => if h : α k ≠ 0 then Sum.inl ⟨k, h⟩ else Sum.inr ⟨k, not_not.mp h⟩
        left_inv := fun s => by
          cases s with
          | inl k => simp [k.2]
          | inr k => simp [k.2]
        right_inv := fun k => by
          by_cases h : α k ≠ 0 <;> simp [h] }
    have hcard := Fintype.card_congr e
    rw [Fintype.card_sum, Fintype.card_fin] at hcard
    exact hcard
  have hfinrank_lt :
      Module.finrank ℂ (LinearMap.ker U × LinearMap.ker U × (Kc → ℂ) × (Kc → ℂ)) <
        Module.finrank ℂ (Fin n → ℂ) := by
    simp only [Module.finrank_prod, Module.finrank_pi ℂ, Fintype.card_fin]
    omega
  have hker_ne : LinearMap.ker Φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hfinrank_lt
  obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  rw [LinearMap.mem_ker] at hx_mem
  have hΦ₁ : Q (D₁ (W x)) = 0 := by
    have := congrArg (fun t => t.1.1) hx_mem
    simpa [Φ, Φ₁] using this
  have hΦ₂ : Q (D₂ (W x)) = 0 := by
    have := congrArg (fun t => t.2.1.1) hx_mem
    simpa [Φ, Φ₂] using this
  have hΦ₃ : ∀ j : Kc, w j.1 ⬝ᵥ x = 0 := by
    intro j
    have := congrFun (congrArg (fun t => t.2.2.1) hx_mem) j
    simpa [Φ, Φ₃] using this
  have hΦ₄ : ∀ j : Kc, β j.1 * (w j.1 ⬝ᵥ (C *ᵥ x)) - γ j.1 * (w j.1 ⬝ᵥ (B_K x)) = 0 := by
    intro j
    have := congrFun (congrArg (fun t => t.2.2.2) hx_mem) j
    simpa [Φ, Φ₄] using this
  have hE1x : E₁ x = 0 := by
    dsimp only [E₁, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hΦ₃ j]
  have hE2x : E₂ x = 0 := by
    dsimp only [E₂, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hΦ₃ j]
  have hBK_CK : B_K (C_K x) = C_K (B_K x) := by
    have hWU1 : W (U (D₁ (W x))) = D₁ (W x) := by
      have : D₁ (W x) - W (U (D₁ (W x))) = 0 := hΦ₁
      exact (sub_eq_zero.mp this).symm
    have hWU2 : W (U (D₂ (W x))) = D₂ (W x) := by
      have : D₂ (W x) - W (U (D₂ (W x))) = 0 := hΦ₂
      exact (sub_eq_zero.mp this).symm
    have hD12 : D₁ (D₂ (W x)) = D₂ (D₁ (W x)) := by
      ext k
      simp only [D₁, D₂, LinearMap.coe_mk, AddHom.coe_mk]
      ring
    calc
      B_K (C_K x) = U (D₁ (W (U (D₂ (W x))))) := rfl
      _ = U (D₁ (D₂ (W x))) := by rw [hWU2]
      _ = U (D₂ (D₁ (W x))) := by rw [hD12]
      _ = U (D₂ (W (U (D₁ (W x))))) := by rw [hWU1]
      _ = C_K (B_K x) := rfl
  have hE12_diff : E₁ (C *ᵥ x) - E₂ (B_K x) = 0 := by
    dsimp only [E₁, E₂, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← sub_smul, hΦ₄ j, zero_smul]
  have hcomm_BC : (B * C - C * B) *ᵥ x = 0 := by
    have hCx : C *ᵥ x = C_K x := by rw [hC_split x, hE2x, add_zero]
    have hBx : B *ᵥ x = B_K x := by rw [hB_split x, hE1x, add_zero]
    have hBCx : (B * C) *ᵥ x = B_K (C_K x) + E₁ (C *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, hCx, hB_split (C_K x), show E₁ (C_K x) = E₁ (C *ᵥ x) from congrArg E₁ hCx.symm]
    have hCBx : (C * B) *ᵥ x = C_K (B_K x) + E₂ (B_K x) := by
      rw [← Matrix.mulVec_mulVec, hBx, hC_split (B_K x)]
    rw [Matrix.sub_mulVec, hBCx, hCBx, hBK_CK]
    simpa [add_sub_add_left_eq_sub] using hE12_diff
  have hcomm_adj : commAdjugate T *ᵥ x = 0 := by
    have hmul_inv : A₀ * A₀⁻¹ = 1 := Matrix.mul_nonsing_inv A₀ hu
    have h1 : A₀ * (B * C) = A₁ * A₀⁻¹ * A₂ := by
      calc
        A₀ * (B * C) = (A₀ * A₀⁻¹) * (A₁ * (A₀⁻¹ * A₂)) := by
          simp only [B, C, Matrix.mul_assoc]
        _ = A₁ * A₀⁻¹ * A₂ := by
          rw [hmul_inv, Matrix.one_mul, Matrix.mul_assoc]
    have h2 : A₀ * (C * B) = A₂ * A₀⁻¹ * A₁ := by
      calc
        A₀ * (C * B) = (A₀ * A₀⁻¹) * (A₂ * (A₀⁻¹ * A₁)) := by
          simp only [B, C, Matrix.mul_assoc]
        _ = A₂ * A₀⁻¹ * A₁ := by
          rw [hmul_inv, Matrix.one_mul, Matrix.mul_assoc]
    have hmat : commAdjugate T = A₀.det • (A₀ * (B * C - C * B)) := by
      rw [Matrix.mul_sub, h1, h2]
      simp only [commAdjugate, A₀, A₁, A₂, hadj_eq, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have hsmul_mv : ∀ (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ),
        (c • M) *ᵥ y = c • (M *ᵥ y) := by
      intro c M y
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [hmat, hsmul_mv, ← Matrix.mulVec_mulVec, hcomm_BC, Matrix.mulVec_zero, smul_zero]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx_ne, hcomm_adj⟩

end Arxiv08053777H1

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_three_odd_R1.H1 := by
  intro p hp
  obtain ⟨hopen, hdense⟩ := Arxiv08053777H1.open_and_dense_nonvanishing (n := 2 * p + 1) (by omega)
  refine ⟨{T | Arxiv08053777H1.polyObstruction T ≠ 0}, hopen, hdense, ?_⟩
  intro T hT
  by_contra! hlt
  have hle : T.cprank ≤ 3 * p + 1 := by omega
  have hcp : Holor.CPRankMax T.cprank T := by
    unfold Holor.cprank
    exact @Nat.find_spec (fun n => Holor.CPRankMax n T) (Classical.decPred _)
      ⟨([3, 2 * p + 1, 2 * p + 1] : List ℕ).prod, Holor.cprankMax_upper_bound T⟩
  have hdet0 : (Arxiv08053777H1.sliceMat T 0).det ≠ 0 := by
    intro h0
    apply hT
    simp [Arxiv08053777H1.polyObstruction, h0]
  have hcomm0 := Arxiv08053777H1.commAdjugate_det_eq_zero_of_cprankMax hle hcp hdet0
  apply hT
  simp [Arxiv08053777H1.polyObstruction, hcomm0]
