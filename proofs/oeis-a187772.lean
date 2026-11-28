import OMAStatements.S_oeis_a187772

namespace OMA.P_oeis_a187772

open Matrix OMA.S_oeis_a187772

private def QMat (k : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod k) :=
  !![(0 : ZMod k), 1; 1, 1]

private lemma matMod_danzer_2_0 (k : ℕ) :
    matMod k (danzerMatrix 2 0) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matMod, danzerMatrix, chebSMat]

private lemma matMod_danzer_2_1 (k : ℕ) :
    matMod k (danzerMatrix 2 1) = QMat k := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matMod, danzerMatrix, chebSMat, danzerBase, QMat]

private lemma QMat_pow_succ (k : ℕ) (m : ℕ) :
    QMat k ^ (m + 1) =
      !![(Nat.fib m : ZMod k), (Nat.fib (m + 1) : ZMod k);
         (Nat.fib (m + 1) : ZMod k), (Nat.fib (m + 2) : ZMod k)] := by
  induction m with
  | zero =>
    ext i j; fin_cases i <;> fin_cases j <;> simp [QMat, Nat.fib_zero, Nat.fib_one, Nat.fib_two]
  | succ m ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [QMat, Matrix.mul_apply, Fin.sum_univ_two, Nat.fib_add_two]

private lemma QMat_pow_eq_one_iff (k : ℕ) (p : ℕ) (hp : 0 < p) :
    QMat k ^ p = 1 ↔
      ((Nat.fib p : ZMod k) = 0 ∧ (Nat.fib (p + 1) : ZMod k) = 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hp)
  rw [QMat_pow_succ]
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod k) => M 0 1) h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod k) => M 1 1) h
    simp at h01 h11
    exact ⟨h01, h11⟩
  · rintro ⟨h1, h2⟩
    have h0 : (Nat.fib m : ZMod k) = 1 := by
      have hrec : (Nat.fib (m + 2) : ZMod k) = (Nat.fib m : ZMod k) + (Nat.fib (m + 1) : ZMod k) := by
        rw [Nat.fib_add_two]; push_cast; rfl
      rw [h2, h1, add_zero] at hrec
      exact hrec.symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

private lemma fib_periodic_iff (k : ℕ) (p : ℕ) :
    (∀ r : ℕ, (Nat.fib (r + p) : ZMod k) = (Nat.fib r : ZMod k)) ↔
      ((Nat.fib p : ZMod k) = 0 ∧ (Nat.fib (p + 1) : ZMod k) = 1) := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [zero_add, Nat.fib_zero, Nat.cast_zero, Nat.fib_one, Nat.cast_one] at h0 h1
    rw [add_comm] at h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    have hpair : ∀ r : ℕ,
        (Nat.fib (r + p) : ZMod k) = (Nat.fib r : ZMod k) ∧
        (Nat.fib (r + 1 + p) : ZMod k) = (Nat.fib (r + 1) : ZMod k) := by
      intro r
      induction r with
      | zero =>
        simp only [zero_add, Nat.fib_zero, Nat.cast_zero, Nat.fib_one, Nat.cast_one]
        rw [add_comm]
        exact ⟨h0, h1⟩
      | succ r ih =>
        refine ⟨ih.2, ?_⟩
        have hL : r + 1 + 1 + p = (r + p) + 2 := by omega
        have hR : r + 1 + 1 = r + 2 := by omega
        rw [hL, hR, Nat.fib_add_two, Nat.fib_add_two]
        push_cast
        rw [ih.1, show r + p + 1 = r + 1 + p by omega, ih.2]
    intro r
    exact (hpair r).1

private lemma zmod_eq_iff_mod_eq (k : ℕ) [NeZero k] (a b : ℕ) :
    (a : ZMod k) = (b : ZMod k) ↔ a % k = b % k := by
  rw [ZMod.natCast_eq_natCast_iff]
  rfl

private lemma QMat_isOfFinOrder (k : ℕ) (hk : 2 ≤ k) : IsOfFinOrder (QMat k) := by
  have : NeZero k := ⟨by omega⟩
  -- QMat k is invertible over ZMod k since QMat k * !![-1, 1; 1, 0] = 1
  let Qinv : Matrix (Fin 2) (Fin 2) (ZMod k) := !![(-1 : ZMod k), 1; 1, 0]
  have hmul : QMat k * Qinv = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [QMat, Qinv, Matrix.mul_apply, Fin.sum_univ_two]
  have hmul' : Qinv * QMat k = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [QMat, Qinv, Matrix.mul_apply, Fin.sum_univ_two]
  let u : (Matrix (Fin 2) (Fin 2) (ZMod k))ˣ := ⟨QMat k, Qinv, hmul, hmul'⟩
  have hu : IsOfFinOrder u := isOfFinOrder_of_finite u
  rw [isOfFinOrder_iff_pow_eq_one] at hu ⊢
  obtain ⟨n, hn, hpow⟩ := hu
  refine ⟨n, hn, ?_⟩
  have := congrArg Units.val hpow
  simpa [u] using this

private theorem main_proof : type_of% @OMA.S_oeis_a187772.main := by
  intro k hk
  have : NeZero k := ⟨by omega⟩
  unfold a187772 a220555 pisanoPeriod
  rw [show 2 - 1 = 1 from rfl, one_mul]
  have hfin : IsOfFinOrder (QMat k) := QMat_isOfFinOrder k hk
  have hord_pos : 0 < orderOf (QMat k) := hfin.orderOf_pos
  have hsup : Finset.sup (Finset.univ : Finset (Fin 2))
      (fun N => orderOf (matMod k (danzerMatrix 2 N.val))) = orderOf (QMat k) := by
    apply le_antisymm
    · rw [Finset.sup_le_iff]
      intro N _
      fin_cases N
      · dsimp only
        rw [matMod_danzer_2_0, orderOf_one]
        exact hord_pos
      · dsimp only
        rw [matMod_danzer_2_1]
    · have h1 : orderOf (matMod k (danzerMatrix 2 (1 : Fin 2).val)) ≤
          Finset.sup (Finset.univ : Finset (Fin 2))
            (fun N => orderOf (matMod k (danzerMatrix 2 N.val))) :=
        Finset.le_sup (f := fun N : Fin 2 => orderOf (matMod k (danzerMatrix 2 N.val)))
          (Finset.mem_univ (1 : Fin 2))
      simpa [matMod_danzer_2_1] using h1
  rw [hsup]
  let S : Set ℕ := { p : ℕ | 0 < p ∧ ∀ r : ℕ, Nat.fib (r + p) % k = Nat.fib r % k }
  have hmem_iff : ∀ p : ℕ, p ∈ S ↔ 0 < p ∧ QMat k ^ p = 1 := by
    intro p
    change (0 < p ∧ ∀ r : ℕ, Nat.fib (r + p) % k = Nat.fib r % k) ↔ 0 < p ∧ QMat k ^ p = 1
    constructor
    · rintro ⟨hp, hper⟩
      refine ⟨hp, (QMat_pow_eq_one_iff k p hp).mpr ((fib_periodic_iff k p).mp ?_)⟩
      intro r
      exact (zmod_eq_iff_mod_eq k _ _).mpr (hper r)
    · rintro ⟨hp, hpow⟩
      refine ⟨hp, ?_⟩
      have hper := (fib_periodic_iff k p).mpr ((QMat_pow_eq_one_iff k p hp).mp hpow)
      intro r
      exact (zmod_eq_iff_mod_eq k _ _).mp (hper r)
  have hord_mem : orderOf (QMat k) ∈ S :=
    (hmem_iff (orderOf (QMat k))).mpr ⟨hord_pos, pow_orderOf_eq_one (QMat k)⟩
  have hord_le : ∀ p ∈ S, orderOf (QMat k) ≤ p := by
    intro p hp
    obtain ⟨hpos, hpow⟩ := (hmem_iff p).mp hp
    exact orderOf_le_of_pow_eq_one hpos hpow
  exact le_antisymm (le_csInf ⟨orderOf (QMat k), hord_mem⟩ hord_le) (Nat.sInf_le hord_mem)

end OMA.P_oeis_a187772

theorem OMA.solution : type_of% @OMA.S_oeis_a187772.main :=
  OMA.P_oeis_a187772.main_proof

