import FormalConjectures.Millennium.BSD

-- Reduction WeierstrassCurve.Affine.Rat.weakBSD.R1 of The Birch and Swinnerton-Dyer (BSD) Conjecture — weakBSD
-- Credit: @carterleffen
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Notation used in the comments, for an elliptic curve E over ℚ and n : ℕ:
--   D n = #(E(ℚ) / 2ⁿ E(ℚ))      the finite-level descent count of the Mordell-Weil group
--   s n = #Ш(E)[2ⁿ]              the 2ⁿ-torsion of the Tate-Shafarevich group
-- H1: Mordell-Weil. E(ℚ) is finitely generated (a theorem; admitted upstream, so kept as a step).
-- H2: Ш(E)[2^∞] is finite, stated as: s n is finite, nonzero and eventually constant.
-- H3: analytic comparison with no rank in it. There is a meromorphic continuation L of natural
--     order a at s = 1 such that the products D n * s n are nonzero and eventually grow by exactly
--     2 ^ a. Classically D n * s n is the order of the 2ⁿ-Selmer group, so H3 is the statement
--     that the analytic rank is the 2^∞-Selmer corank. That identification is NOT formalised or
--     used here: H3 speaks only about the concrete product.
-- main: generic arithmetic (D (n + 1) = 2 ^ rank * D n eventually, for every finitely generated
--     abelian group) cancels D n and s n and leaves 2 ^ rank = 2 ^ a.

namespace OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1

def H1 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic], Module.Finite ℤ E.Point

def H2 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic],
    let s : ℕ → ℕ := fun n ↦ Nat.card {x : E.tateShafarevich // (2 ^ n : ℕ) • x = 0}
    ∃ N, ∀ n, N ≤ n → s n ≠ 0 ∧ s (n + 1) = s n

def H3 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic],
    let D : ℕ → ℕ := fun n ↦
      Nat.card (E.Point ⧸ (nsmulAddMonoidHom (2 ^ n) : E.Point →+ E.Point).range)
    let s : ℕ → ℕ := fun n ↦ Nat.card {x : E.tateShafarevich // (2 ^ n : ℕ) • x = 0}
    ∃ (L : ℂ → ℂ) (a : ℕ), HasseWeil.HasMeromorphicContinuation E L ∧
      meromorphicOrderAt L 1 = a ∧
      ∃ N, ∀ n, N ≤ n → D n * s n ≠ 0 ∧ D (n + 1) * s (n + 1) = 2 ^ a * (D n * s n)

/-- `2ⁿ⁺¹ A ≤ 2ⁿ A`, for any base `m`. -/
lemma range_nsmul_pow_succ_le {A : Type*} [AddCommGroup A] (m n : ℕ) :
    (nsmulAddMonoidHom (α := A) (m ^ (n + 1))).range ≤
      (nsmulAddMonoidHom (α := A) (m ^ n)).range := by
  rintro x ⟨y, rfl⟩
  refine ⟨m • y, ?_⟩
  show m ^ n • m • y = m ^ (n + 1) • y
  rw [pow_succ, mul_smul]

/-- `[A : m A] = [A_tors : m A ∩ A_tors] * m ^ rank A` for a finitely generated abelian group. -/
lemma index_range_nsmul_eq {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] (m : ℕ) :
    (nsmulAddMonoidHom (α := A) m).range.index =
      (nsmulAddMonoidHom (α := A) m).range.relIndex (Submodule.torsion ℤ A).toAddSubgroup *
        m ^ Module.finrank ℤ A := by
  set T := Submodule.torsion ℤ A with hT
  have hr : Module.finrank ℤ (A ⧸ T) = Module.finrank ℤ A :=
    finrank_quotient_eq_of_le_torsion (le_refl T)
  have hsurj : Function.Surjective T.mkQ := T.mkQ_surjective
  set H := (nsmulAddMonoidHom (α := A) m).range with hH
  set f : A →+ A ⧸ T := T.mkQ.toAddMonoidHom with hf
  have hmap : H.map f = (nsmulAddMonoidHom (α := A ⧸ T) m).range := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨f z, (map_nsmul f m z).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := hsurj y
      exact ⟨m • z, ⟨z, rfl⟩, map_nsmul f m z⟩
  have hfree : (H.map f).index = m ^ Module.finrank ℤ A := by
    rw [hmap, AddSubgroup.index_range_nsmul (A ⧸ T) m, hr]
  have hker : f.ker = T.toAddSubgroup := by
    ext x
    simp [hf, AddMonoidHom.mem_ker]
  have hrange : f.range = ⊤ := AddMonoidHom.range_eq_top.mpr hsurj
  have h1 : (H.map f).index = (H ⊔ f.ker).index := by
    rw [AddSubgroup.index_map, hrange, AddSubgroup.index_top, mul_one]
  have h2 : H.relIndex (H ⊔ f.ker) * (H ⊔ f.ker).index = H.index :=
    AddSubgroup.relIndex_mul_index le_sup_left
  have h3 : H.relIndex (H ⊔ f.ker) = H.relIndex f.ker := by
    rw [sup_comm]
    exact AddSubgroup.relIndex_sup_right (K := H) (H := f.ker)
  rw [← h2, h3, ← h1, hfree, hker]

/-- The torsion index is nonzero and bounded by the order of the torsion subgroup. -/
lemma relIndex_torsion_bound {A : Type*} [AddCommGroup A] [Module.Finite ℤ A]
    (H : AddSubgroup A) :
    H.relIndex (Submodule.torsion ℤ A).toAddSubgroup ≠ 0 ∧
      H.relIndex (Submodule.torsion ℤ A).toAddSubgroup ≤
        Nat.card (Submodule.torsion ℤ A).toAddSubgroup := by
  have hfin0 : Finite (Submodule.torsion ℤ A) :=
    Module.finite_of_fg_torsion _ (Submodule.torsion_isTorsion)
  have hfin : Finite (Submodule.torsion ℤ A).toAddSubgroup := hfin0
  have hdvd : H.relIndex (Submodule.torsion ℤ A).toAddSubgroup ∣
      Nat.card (Submodule.torsion ℤ A).toAddSubgroup := AddSubgroup.relIndex_dvd_card _ _
  have hpos : 0 < Nat.card (Submodule.torsion ℤ A).toAddSubgroup := Nat.card_pos
  refine ⟨?_, Nat.le_of_dvd hpos hdvd⟩
  intro h0
  rw [h0, zero_dvd_iff] at hdvd
  exact hpos.ne' hdvd

/-- A bounded monotone sequence of natural numbers is eventually constant. -/
lemma eventually_const_of_monotone_of_le (τ : ℕ → ℕ) (hmono : Monotone τ) (B : ℕ)
    (hB : ∀ n, τ n ≤ B) : ∃ N, ∀ n, N ≤ n → τ n = τ N := by
  have hbdd : BddAbove (Set.range τ) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hB n
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty τ) hbdd
  refine ⟨N, fun n hn ↦ le_antisymm ?_ (hmono hn)⟩
  have hle : τ n ≤ sSup (Set.range τ) := le_csSup hbdd ⟨n, rfl⟩
  exact hle.trans (le_of_eq hN.symm)

/-- **Descent growth for finitely generated abelian groups** (no arithmetic input):
`#(A / 2ⁿ⁺¹ A) = 2 ^ rank A * #(A / 2ⁿ A)` for all sufficiently large `n`. -/
theorem card_quotient_range_nsmul_pow_succ {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] :
    ∃ N, ∀ n, N ≤ n →
      Nat.card (A ⧸ (nsmulAddMonoidHom (2 ^ (n + 1)) : A →+ A).range) =
        2 ^ Module.finrank ℤ A * Nat.card (A ⧸ (nsmulAddMonoidHom (2 ^ n) : A →+ A).range) := by
  obtain ⟨N, hN⟩ := eventually_const_of_monotone_of_le
    (fun n ↦ (nsmulAddMonoidHom (α := A) (2 ^ n)).range.relIndex
      (Submodule.torsion ℤ A).toAddSubgroup)
    (monotone_nat_of_le_succ fun n ↦ Nat.le_of_dvd
      (Nat.pos_of_ne_zero (relIndex_torsion_bound _).1)
      (AddSubgroup.relIndex_dvd_of_le_left _ (range_nsmul_pow_succ_le 2 n)))
    (Nat.card (Submodule.torsion ℤ A).toAddSubgroup) (fun n ↦ (relIndex_torsion_bound _).2)
  refine ⟨N, fun n hn ↦ ?_⟩
  have e1 := index_range_nsmul_eq (A := A) (2 ^ (n + 1))
  have e2 := index_range_nsmul_eq (A := A) (2 ^ n)
  rw [hN (n + 1) (by omega)] at e1
  rw [hN n hn] at e2
  show (nsmulAddMonoidHom (α := A) (2 ^ (n + 1))).range.index =
    2 ^ Module.finrank ℤ A * (nsmulAddMonoidHom (α := A) (2 ^ n)).range.index
  rw [e1, e2]
  ring

theorem main : H1 → H2 → H3 → type_of% @WeierstrassCurve.Affine.Rat.weakBSD := by
  intro h1 h2 h3 E hE
  haveI := h1 E
  obtain ⟨N1, hN1⟩ := card_quotient_range_nsmul_pow_succ (A := E.Point)
  obtain ⟨N2, hN2⟩ := h2 E
  obtain ⟨L, a, hL, ha, N3, hN3⟩ := h3 E
  have e1 := hN1 (max N1 (max N2 N3)) (le_max_left _ _)
  have e2 := (hN2 (max N1 (max N2 N3)) (le_trans (le_max_left _ _) (le_max_right _ _))).2
  obtain ⟨e3, e4⟩ := hN3 (max N1 (max N2 N3)) (le_trans (le_max_right _ _) (le_max_right _ _))
  beta_reduce at e2 e3 e4
  rw [e1, e2] at e4
  have hpow : 2 ^ Module.finrank ℤ E.Point = 2 ^ a :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero e3) ((mul_assoc _ _ _).symm.trans e4)
  have key : Module.finrank ℤ E.Point = a := Nat.pow_right_injective (le_refl 2) hpow
  subst key
  exact ⟨L, hL, ha⟩

end OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1
