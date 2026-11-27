import OMAReductions.R_WeierstrassCurve_Affine_Rat_weakBSD_R1
import Mathlib

-- Reduction WeierstrassCurve.Affine.Rat.weakBSD.R1.H2.R1 of step H2 of
-- WeierstrassCurve.Affine.Rat.weakBSD.R1 (the counts #Ш(E)[2ⁿ] are eventually nonzero and constant).
-- Credit: @carterleffen
--
-- H1: for every elliptic curve E over ℚ, the subgroup Ш(E)[2] of the registered Tate-Shafarevich
--     group is finite (weak Mordell-Weil style finiteness of the 2-Selmer group).
-- H2: for every elliptic curve E over ℚ, Ш(E) has no compatible 2-division tower: no sequence
--     x 0, x 1, ... with x 0 a nonzero element of Ш(E)[2] and 2 • x (n + 1) = x n.
--     Equivalently (given H1) no nonzero element of Ш(E)[2] is divisible by every power of 2.
-- main: pure group theory, valid in every abelian group A. If A[2] is finite then every layer
--     A[2ⁿ] is finite, and if the layers never stabilise, a pigeonhole argument on the finite set
--     A[2] minus zero and on the finite fibres of doubling produces a compatible tower.
--     Finiteness of every layer alone does NOT give stabilisation (ℚ/ℤ has finite layers);
--     the second hypothesis is what excludes a divisible part.

namespace OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H2_R1

def H1 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic],
    Finite {x : E.tateShafarevich // 2 • x = 0}

def H2 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic],
    ¬ ∃ x : ℕ → E.tateShafarevich, x 0 ≠ 0 ∧ 2 • x 0 = 0 ∧ ∀ n, 2 • x (n + 1) = x n

theorem pow_smul_of_le {A : Type*} [AddCommGroup A] {m n : ℕ} (h : m ≤ n) (y : A) :
    2 ^ m • 2 ^ (n - m) • y = 2 ^ n • y := by
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]

/-- `A[2 ^ m] ⊆ A[2 ^ n]` for `m ≤ n`. -/
theorem pow_smul_eq_zero_of_le {A : Type*} [AddCommGroup A] {m n : ℕ} (h : m ≤ n) {a : A}
    (ha : 2 ^ m • a = 0) : 2 ^ n • a = 0 := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_smul, ha, smul_zero]

/-- If `A[2]` is finite, every fibre of doubling is finite. -/
theorem fiber_finite {A : Type*} [AddCommGroup A] (hK : {a : A | 2 • a = 0}.Finite) (z : A) :
    {w : A | 2 • w = z}.Finite := by
  by_cases h : ∃ w₀ : A, 2 • w₀ = z
  · obtain ⟨w₀, h₀⟩ := h
    refine (hK.image (w₀ + ·)).subset fun w hw ↦ ⟨w - w₀, ?_, show w₀ + (w - w₀) = w by abel⟩
    change 2 • (w - w₀) = 0
    rw [nsmul_sub, show 2 • w = z from hw, h₀, sub_self]
  · exact Set.finite_empty.subset fun w hw ↦ absurd ⟨w, hw⟩ h

/-- If `A[2]` is finite, every layer `A[2 ^ n]` is finite. -/
theorem layer_finite {A : Type*} [AddCommGroup A] (hK : {a : A | 2 • a = 0}.Finite) (n : ℕ) :
    {a : A | 2 ^ n • a = 0}.Finite := by
  induction n with
  | zero => exact (Set.finite_singleton (0 : A)).subset fun a ha ↦ by simpa using ha
  | succ n ih =>
    refine (ih.preimage' (f := fun a : A ↦ 2 • a) fun b _ ↦ fiber_finite hK b).subset fun a ha ↦ ?_
    change 2 ^ n • 2 • a = 0
    rw [smul_smul, ← pow_succ]
    exact ha

/-- Pigeonhole: a finite set containing, for every `N`, an element divisible by `2 ^ N` contains
an element divisible by every power of `2`. -/
theorem exists_mem_divisible {A : Type*} [AddCommGroup A] {F : Set A} (hF : F.Finite)
    (h : ∀ N : ℕ, ∃ u ∈ F, ∃ y : A, 2 ^ N • y = u) :
    ∃ u ∈ F, ∀ n : ℕ, ∃ y : A, 2 ^ n • y = u := by
  by_contra hc
  have hc' : ∀ u ∈ F, ∃ n : ℕ, ∀ y : A, 2 ^ n • y ≠ u := by
    intro u hu
    by_contra hn
    refine hc ⟨u, hu, fun n ↦ ?_⟩
    by_contra hy
    exact hn ⟨n, fun y hyu ↦ hy ⟨y, hyu⟩⟩
  choose! m hm using hc'
  obtain ⟨M, hM⟩ := (hF.image m).bddAbove
  obtain ⟨u, hu, y, rfl⟩ := h M
  have hle : m (2 ^ M • y) ≤ M := hM ⟨_, hu, rfl⟩
  exact hm _ hu (2 ^ (M - m (2 ^ M • y)) • y) (pow_smul_of_le hle y)

/-- Finite branching: if `A[2]` is finite, every element divisible by all powers of `2` has a
half with the same property. -/
theorem exists_divisible_half {A : Type*} [AddCommGroup A] (hK : {a : A | 2 • a = 0}.Finite)
    {z : A} (hz : ∀ n : ℕ, ∃ y : A, 2 ^ n • y = z) :
    ∃ w : A, (∀ n : ℕ, ∃ y : A, 2 ^ n • y = w) ∧ 2 • w = z := by
  obtain ⟨w, hw, hd⟩ := exists_mem_divisible (fiber_finite hK z) fun N ↦ by
    obtain ⟨y, hy⟩ := hz (N + 1)
    refine ⟨2 ^ N • y, ?_, y, rfl⟩
    change 2 • 2 ^ N • y = z
    rw [smul_smul, ← pow_succ']
    exact hy
  exact ⟨w, hd, hw⟩

/-- If `A[2]` is finite, a nonzero element of `A[2]` divisible by every power of `2` starts a
compatible tower. -/
theorem tower_of_divisible {A : Type*} [AddCommGroup A] (hK : {a : A | 2 • a = 0}.Finite)
    {x : A} (hx0 : x ≠ 0) (hx2 : 2 • x = 0) (hx : ∀ n : ℕ, ∃ y : A, 2 ^ n • y = x) :
    ∃ t : ℕ → A, t 0 ≠ 0 ∧ 2 • t 0 = 0 ∧ ∀ n, 2 • t (n + 1) = t n := by
  choose half hhalf using fun z : {z : A // ∀ n : ℕ, ∃ y : A, 2 ^ n • y = z} ↦
    exists_divisible_half hK z.2
  let t : ℕ → {z : A // ∀ n : ℕ, ∃ y : A, 2 ^ n • y = z} :=
    fun n ↦ Nat.rec ⟨x, hx⟩ (fun _ z ↦ ⟨half z, (hhalf z).1⟩) n
  exact ⟨fun n ↦ (t n).1, hx0, hx2, fun n ↦ (hhalf (t n)).2⟩

/-- **Stationarity from finite `A[2]` and no tower.** For every abelian group `A`: if `A[2]` is
finite and `A` has no compatible `2`-division tower, the counts `#A[2 ^ n]` are eventually
nonzero and constant. -/
theorem stationary_of_finite_of_no_tower {A : Type*} [AddCommGroup A]
    (hK : {a : A | 2 • a = 0}.Finite)
    (hT : ¬ ∃ x : ℕ → A, x 0 ≠ 0 ∧ 2 • x 0 = 0 ∧ ∀ n, 2 • x (n + 1) = x n) :
    ∃ N : ℕ, ∀ n, N ≤ n → Nat.card {a : A // 2 ^ n • a = 0} ≠ 0 ∧
      Nat.card {a : A // 2 ^ (n + 1) • a = 0} = Nat.card {a : A // 2 ^ n • a = 0} := by
  have hstab : ∃ N : ℕ, ∀ n ≥ N, {a : A | 2 ^ (n + 1) • a = 0} ⊆ {a : A | 2 ^ n • a = 0} := by
    by_contra hc
    refine hT ?_
    have hc' : ∀ N : ℕ, ∃ n ≥ N,
        ¬ {a : A | 2 ^ (n + 1) • a = 0} ⊆ {a : A | 2 ^ n • a = 0} := by
      intro N
      by_contra hn
      exact hc ⟨N, fun n hn' ↦ by
        by_contra hs
        exact hn ⟨n, hn', hs⟩⟩
    obtain ⟨u, ⟨hu2, hu0⟩, hud⟩ := exists_mem_divisible
      (F := {a : A | 2 • a = 0} \ {0}) (hK.subset Set.sdiff_subset) fun N ↦ by
        obtain ⟨n, hn, hs⟩ := hc' N
        obtain ⟨y, hy1, hy0⟩ := Set.not_subset.mp hs
        refine ⟨2 ^ n • y, ⟨?_, hy0⟩, 2 ^ (n - N) • y, pow_smul_of_le hn y⟩
        change 2 • 2 ^ n • y = 0
        rw [smul_smul, ← pow_succ']
        exact hy1
    exact tower_of_divisible hK hu0 hu2 hud
  obtain ⟨N, hN⟩ := hstab
  refine ⟨N, fun n hn ↦ ⟨?_, ?_⟩⟩
  · have hfin : Finite {a : A // 2 ^ n • a = 0} := Set.finite_coe_iff.mpr (layer_finite hK n)
    have hne : Nonempty {a : A // 2 ^ n • a = 0} := ⟨⟨0, smul_zero _⟩⟩
    exact Nat.card_pos.ne'
  · have he : {a : A | 2 ^ (n + 1) • a = 0} = {a : A | 2 ^ n • a = 0} :=
      (hN n hn).antisymm fun a ha ↦ pow_smul_eq_zero_of_le n.le_succ ha
    change Nat.card {a : A | 2 ^ (n + 1) • a = 0} = Nat.card {a : A | 2 ^ n • a = 0}
    rw [he]

theorem main : H1 → H2 → OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1.H2 := by
  intro h1 h2 E hE
  exact stationary_of_finite_of_no_tower (Set.finite_coe_iff.mp (h1 E)) (h2 E)

end OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H2_R1
