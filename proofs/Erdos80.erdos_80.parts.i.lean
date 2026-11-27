import FormalConjectures.ErdosProblems.«80»

/-!
# Proof of Erdős Problem 80 (part i)

Self-contained proof of `Erdos80.erdos_80.parts.i`:
there is no universal polynomial lower bound `f c n > n ^ ε` holding for every `c ∈ (0, 1/2)`.

Following Fox–Loh (2012) together with Alon's simplification and deterministic derandomizations:
1. Take `c = 1 / 12` and, for a large integer `r ≥ 4`, set `d = 24 r^4`, `μ = 4 (r^2 - 1) r^4`,
   `μ₄ = (r^2 - 1) r^4`, and `V = Fin 3 × (Fin d → Fin r)` (`N = 3 r^d` vertices).
2. In the tripartite pre-construction `G₀` on `V`, edges `(0, a) ~ (1, b)` require
   `|‖a - b‖² - μ| ≤ d`, and edges `(0, a) ~ (2, c)` / `(1, b) ~ (2, c)` require
   `|‖·‖² - μ₄| ≤ 2 d`.
3. Second-moment (Chebyshev) concentration on `(Fin r)^d × (Fin r)^d` shows at least
   `(23 / 24) r^(2d) ≥ (1 / 12) N²` pairs `(a, b)` are joined in `G₀`.
4. Greedy sign-balanced midpoint rounding gives every `A`-`B` edge of `G₀` at least one common
   neighbor `c ∈ C`, so passing to the subgraph `G ⊆ G₀` of edges lying in at least one triangle
   preserves all `A`-`B` edges and makes every edge lie in a triangle.
5. Exact integer quadratic identities show that for every edge of `G`, its common neighbors inject
   into `{w : Fin d → ℤ | ∑ (w i)² ≤ 9 d}`, whose cardinality is at most `2^(9d) * 3^d = 1536^d`
   by a finite Rankin bound.
6. Choosing `r > max 4 (N₀ + ⌈1536^(1/ε)⌉)` gives `N = 3 r^d ≥ N₀` and
   `f (1/12) N ≤ bookNumber G ≤ 1536^d < N^ε`, contradicting the assumed lower bound.
-/

namespace Erdos80PartIProof

open SimpleGraph Finset

/- ### 1. Exact 1D second-moment identities on `Fin r` -/

private lemma six_mul_sum_sq (r : ℕ) :
    6 * ∑ u ∈ Finset.range r, ((u : ℤ) + 1) ^ 2 =
      (r : ℤ) * ((r : ℤ) + 1) * (2 * (r : ℤ) + 1) := by
  induction r with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

private lemma six_mul_sum_sq_diff (r : ℕ) :
    6 * ∑ u : Fin r, ∑ v : Fin r, ((u : ℤ) - (v : ℤ)) ^ 2 =
      (r : ℤ) ^ 2 * ((r : ℤ) ^ 2 - 1) := by
  induction r with
  | zero => simp
  | succ k ih =>
      have hsplit :
          ∑ u : Fin (k + 1), ∑ v : Fin (k + 1), ((u : ℤ) - (v : ℤ)) ^ 2 =
            (∑ u : Fin k, ∑ v : Fin k, ((u : ℤ) - (v : ℤ)) ^ 2) +
            2 * ∑ u : Fin k, ((k : ℤ) - (u : ℤ)) ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        simp_rw [Fin.sum_univ_castSucc]
        rw [Finset.sum_add_distrib]
        have hdiag : ((Fin.last k : ℕ) : ℤ) - ((Fin.last k : ℕ) : ℤ) = 0 := by simp
        have hsymm :
            ∑ u : Fin k, (((u : ℕ) : ℤ) - (k : ℤ)) ^ 2 =
              ∑ u : Fin k, ((k : ℤ) - ((u : ℕ) : ℤ)) ^ 2 := by
          refine Finset.sum_congr rfl fun u _ => by ring
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [sub_self, zero_pow two_ne_zero, add_zero, hsymm]
        ring
      have hrev :
          ∑ u : Fin k, ((k : ℤ) - (u : ℤ)) ^ 2 =
            ∑ u ∈ Finset.range k, ((u : ℤ) + 1) ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun u => ((k : ℤ) - (u : ℤ)) ^ 2)]
        rw [← Finset.sum_range_reflect (fun u => ((u : ℤ) + 1) ^ 2) k]
        refine Finset.sum_congr rfl fun u hu => ?_
        have hlt : u < k := Finset.mem_range.mp hu
        have hsub : ((k - 1 - u : ℕ) : ℤ) + 1 = (k : ℤ) - (u : ℤ) := by omega
        rw [hsub]
      rw [hsplit, mul_add, ih, hrev]
      have hsq := six_mul_sum_sq k
      have hmul : 6 * (2 * ∑ u ∈ Finset.range k, ((u : ℤ) + 1) ^ 2) =
          2 * ((k : ℤ) * ((k : ℤ) + 1) * (2 * (k : ℤ) + 1)) := by linarith
      rw [hmul]
      push_cast
      ring

/- ### 2. Chebyshev concentration on `(Fin d → Fin r) × (Fin d → Fin r)` -/

private def sqDist {r d : ℕ} (a b : Fin d → Fin r) : ℤ :=
  ∑ i : Fin d, ((a i : ℤ) - (b i : ℤ)) ^ 2

private lemma sqDist_comm {r d : ℕ} (a b : Fin d → Fin r) :
    sqDist a b = sqDist b a := by
  unfold sqDist
  refine Finset.sum_congr rfl fun i _ => by ring

private def centered1D (r : ℕ) (u v : Fin r) : ℤ :=
  6 * ((u : ℤ) - (v : ℤ)) ^ 2 - ((r : ℤ) ^ 2 - 1)

private lemma sum_centered1D (r : ℕ) :
    ∑ u : Fin r, ∑ v : Fin r, centered1D r u v = 0 := by
  unfold centered1D
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [six_mul_sum_sq_diff]
  ring

private lemma sq_centered1D_le (r : ℕ) (u v : Fin r) :
    (centered1D r u v) ^ 2 ≤ 36 * (r : ℤ) ^ 4 := by
  unfold centered1D
  have hu0 : (0 : ℤ) ≤ (u : ℤ) := Nat.cast_nonneg _
  have hv0 : (0 : ℤ) ≤ (v : ℤ) := Nat.cast_nonneg _
  have hu : (u : ℤ) < (r : ℤ) := Nat.cast_lt.mpr u.isLt
  have hv : (v : ℤ) < (r : ℤ) := Nat.cast_lt.mpr v.isLt
  have hdiff_le : ((u : ℤ) - (v : ℤ)) ^ 2 ≤ (r : ℤ) ^ 2 := by nlinarith
  have hdiff_ge : 0 ≤ ((u : ℤ) - (v : ℤ)) ^ 2 := sq_nonneg _
  have hr1 : 1 ≤ (r : ℤ) := by omega
  have hlo : -(6 * (r : ℤ) ^ 2) ≤ 6 * ((u : ℤ) - (v : ℤ)) ^ 2 - ((r : ℤ) ^ 2 - 1) := by
    nlinarith
  have hhi : 6 * ((u : ℤ) - (v : ℤ)) ^ 2 - ((r : ℤ) ^ 2 - 1) ≤ 6 * (r : ℤ) ^ 2 := by
    nlinarith
  nlinarith

private lemma sum_sq_centered1D_le (r : ℕ) :
    ∑ u : Fin r, ∑ v : Fin r, (centered1D r u v) ^ 2 ≤ 36 * (r : ℤ) ^ 6 := by
  calc
    ∑ u : Fin r, ∑ v : Fin r, (centered1D r u v) ^ 2
        ≤ ∑ _u : Fin r, ∑ _v : Fin r, (36 * (r : ℤ) ^ 4) := by
      refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => sq_centered1D_le r u v
    _ = 36 * (r : ℤ) ^ 6 := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

private lemma sum_prod_centered_offdiag {r d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    ∑ a : Fin d → Fin r, ∑ b : Fin d → Fin r,
      centered1D r (a i) (b i) * centered1D r (a j) (b j) = 0 := by
  let e : (Fin d → Fin r) ≃ Fin r × ({k : Fin d // k ≠ i} → Fin r) :=
    (Equiv.piSplitAt i (fun _ => Fin r))
  have he_i : ∀ p : Fin r × ({k : Fin d // k ≠ i} → Fin r), e.symm p i = p.1 := by
    intro p
    simp [e, Equiv.piSplitAt]
  have he_j : ∀ p : Fin r × ({k : Fin d // k ≠ i} → Fin r),
      e.symm p j = p.2 ⟨j, hij.symm⟩ := by
    intro p
    simp [e, Equiv.piSplitAt, dif_neg hij.symm]
  rw [← Equiv.sum_comp e.symm]
  simp_rw [← Equiv.sum_comp e.symm, he_i, he_j]
  simp_rw [Fintype.sum_prod_type]
  calc
    ∑ x : Fin r, ∑ a' : {k : Fin d // k ≠ i} → Fin r,
        ∑ y : Fin r, ∑ b' : {k : Fin d // k ≠ i} → Fin r,
          centered1D r x y * centered1D r (a' ⟨j, hij.symm⟩) (b' ⟨j, hij.symm⟩)
        = ∑ a' : {k : Fin d // k ≠ i} → Fin r, ∑ b' : {k : Fin d // k ≠ i} → Fin r,
            ∑ x : Fin r, ∑ y : Fin r,
              centered1D r x y * centered1D r (a' ⟨j, hij.symm⟩) (b' ⟨j, hij.symm⟩) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a' _ => ?_
      trans (∑ x : Fin r, ∑ b' : {k : Fin d // k ≠ i} → Fin r, ∑ y : Fin r,
          centered1D r x y * centered1D r (a' ⟨j, hij.symm⟩) (b' ⟨j, hij.symm⟩))
      · refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
      · rw [Finset.sum_comm]
    _ = ∑ a' : {k : Fin d // k ≠ i} → Fin r, ∑ b' : {k : Fin d // k ≠ i} → Fin r,
            (∑ x : Fin r, ∑ y : Fin r, centered1D r x y) *
              centered1D r (a' ⟨j, hij.symm⟩) (b' ⟨j, hij.symm⟩) := by
      refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
      simp_rw [Finset.sum_mul]
    _ = 0 := by
      simp [sum_centered1D]

private lemma sum_sq_centered_diag {r d : ℕ} (hd : 1 ≤ d) (i : Fin d) :
    ∑ a : Fin d → Fin r, ∑ b : Fin d → Fin r, (centered1D r (a i) (b i)) ^ 2 ≤
      36 * (r : ℤ) ^ 4 * ((r : ℤ) ^ d) ^ 2 := by
  let e : (Fin d → Fin r) ≃ Fin r × ({k : Fin d // k ≠ i} → Fin r) :=
    (Equiv.piSplitAt i (fun _ => Fin r))
  have he_i : ∀ p : Fin r × ({k : Fin d // k ≠ i} → Fin r), e.symm p i = p.1 := by
    intro p
    simp [e, Equiv.piSplitAt]
  have hcard_rest : Fintype.card ({k : Fin d // k ≠ i} → Fin r) = r ^ (d - 1) := by
    simp [Fintype.card_pi, Fintype.card_subtype_compl]
  rw [← Equiv.sum_comp e.symm]
  simp_rw [← Equiv.sum_comp e.symm, he_i, Fintype.sum_prod_type]
  have hconst :
      ∑ x : Fin r, ∑ _a' : {k : Fin d // k ≠ i} → Fin r,
        ∑ y : Fin r, ∑ _b' : {k : Fin d // k ≠ i} → Fin r, (centered1D r x y) ^ 2 =
      ((r : ℤ) ^ (d - 1)) ^ 2 * ∑ x : Fin r, ∑ y : Fin r, (centered1D r x y) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, hcard_rest, nsmul_eq_mul, ← Finset.mul_sum]
    push_cast
    ring
  rw [hconst]
  have h1 := sum_sq_centered1D_le r
  have hpow : ((r : ℤ) ^ (d - 1)) ^ 2 * (36 * (r : ℤ) ^ 6) =
      36 * (r : ℤ) ^ 4 * ((r : ℤ) ^ d) ^ 2 := by
    have hr_d : (r : ℤ) ^ d = (r : ℤ) * (r : ℤ) ^ (d - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ']
    rw [hr_d]
    ring
  calc
    ((r : ℤ) ^ (d - 1)) ^ 2 * ∑ x : Fin r, ∑ y : Fin r, (centered1D r x y) ^ 2
        ≤ ((r : ℤ) ^ (d - 1)) ^ 2 * (36 * (r : ℤ) ^ 6) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = 36 * (r : ℤ) ^ 4 * ((r : ℤ) ^ d) ^ 2 := hpow

private lemma sum_sq_centered_total {r d : ℕ} (hd : 1 ≤ d) :
    ∑ a : Fin d → Fin r, ∑ b : Fin d → Fin r,
      (∑ i : Fin d, centered1D r (a i) (b i)) ^ 2 ≤
        36 * (d : ℤ) * (r : ℤ) ^ 4 * ((r : ℤ) ^ d) ^ 2 := by
  have hexp :
      ∑ a : Fin d → Fin r, ∑ b : Fin d → Fin r, (∑ i : Fin d, centered1D r (a i) (b i)) ^ 2 =
        ∑ i : Fin d, ∑ j : Fin d,
          ∑ a : Fin d → Fin r, ∑ b : Fin d → Fin r,
            centered1D r (a i) (b i) * centered1D r (a j) (b j) := by
    simp_rw [sq, Finset.sum_mul_sum]
    trans (∑ a : Fin d → Fin r, ∑ i : Fin d, ∑ b : Fin d → Fin r, ∑ j : Fin d,
        centered1D r (a i) (b i) * centered1D r (a j) (b j))
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      trans (∑ a : Fin d → Fin r, ∑ j : Fin d, ∑ b : Fin d → Fin r,
          centered1D r (a i) (b i) * centered1D r (a j) (b j))
      · refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
      · rw [Finset.sum_comm]
  rw [hexp]
  have hdiag_only :
      ∑ i : Fin d, ∑ j : Fin d,
        ∑ a : Fin d → Fin r, ∑ b : Fin d → Fin r,
          centered1D r (a i) (b i) * centered1D r (a j) (b j) =
      ∑ i : Fin d, ∑ a : Fin d → Fin r, ∑ b : Fin d → Fin r, (centered1D r (a i) (b i)) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp_rw [sq]
    · intro j _ hji
      exact sum_prod_centered_offdiag i j hji.symm
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  rw [hdiag_only]
  calc
    ∑ i : Fin d, ∑ a : Fin d → Fin r, ∑ b : Fin d → Fin r, (centered1D r (a i) (b i)) ^ 2
        ≤ ∑ _i : Fin d, (36 * (r : ℤ) ^ 4 * ((r : ℤ) ^ d) ^ 2) :=
      Finset.sum_le_sum fun i _ => sum_sq_centered_diag hd i
    _ = 36 * (d : ℤ) * (r : ℤ) ^ 4 * ((r : ℤ) ^ d) ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

private lemma card_good_pairs_ge (r : ℕ) (hr : 4 ≤ r) :
    let d := 24 * r ^ 4
    let μ : ℤ := 4 * ((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4
    3 * (r ^ d) ^ 2 ≤
      4 * (Finset.univ.filter (fun p : (Fin d → Fin r) × (Fin d → Fin r) =>
        |sqDist p.1 p.2 - μ| ≤ (d : ℤ))).card := by
  intro d μ
  have hd_pos : 1 ≤ d := by
    have : 1 ≤ r ^ 4 := one_le_pow₀ (by omega)
    omega
  have h6μ : (d : ℤ) * ((r : ℤ) ^ 2 - 1) = 6 * μ := by
    simp only [d, μ]
    push_cast
    ring
  have hS_eq : ∀ a b : Fin d → Fin r,
      ∑ i : Fin d, centered1D r (a i) (b i) = 6 * (sqDist a b - μ) := by
    intro a b
    unfold centered1D sqDist
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, h6μ]
    ring
  let good : Finset ((Fin d → Fin r) × (Fin d → Fin r)) :=
    Finset.univ.filter (fun p => |sqDist p.1 p.2 - μ| ≤ (d : ℤ))
  let bad : Finset ((Fin d → Fin r) × (Fin d → Fin r)) :=
    Finset.univ.filter (fun p => ¬ |sqDist p.1 p.2 - μ| ≤ (d : ℤ))
  have hpart : good.card + bad.card = (r ^ d) ^ 2 := by
    have hunion : good ∪ bad = Finset.univ := by
      ext p
      simp only [good, bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      exact Classical.em _
    have hdisj : Disjoint good bad := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_prod,
      Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fin, sq]
  have hbad_bound : (bad.card : ℤ) * (36 * (d : ℤ) ^ 2) ≤
      36 * (d : ℤ) * (r : ℤ) ^ 4 * ((r : ℤ) ^ d) ^ 2 := by
    calc
      (bad.card : ℤ) * (36 * (d : ℤ) ^ 2)
          = ∑ _p ∈ bad, (36 * (d : ℤ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ bad, (∑ i : Fin d, centered1D r (p.1 i) (p.2 i)) ^ 2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hgt : (d : ℤ) < |sqDist p.1 p.2 - μ| := not_le.mp (Finset.mem_filter.mp hp).2
        rw [hS_eq]
        have hsq : (d : ℤ) ^ 2 ≤ (sqDist p.1 p.2 - μ) ^ 2 := by
          have := sq_le_sq.mpr (show |(d : ℤ)| ≤ |sqDist p.1 p.2 - μ| by
            rw [abs_of_nonneg (Nat.cast_nonneg d)]; exact hgt.le)
          exact this
        linarith
      _ ≤ ∑ p : (Fin d → Fin r) × (Fin d → Fin r),
            (∑ i : Fin d, centered1D r (p.1 i) (p.2 i)) ^ 2 := by
        refine Finset.sum_le_univ_sum_of_nonneg fun p => sq_nonneg _
      _ = ∑ a : Fin d → Fin r, ∑ b : Fin d → Fin r,
            (∑ i : Fin d, centered1D r (a i) (b i)) ^ 2 := Fintype.sum_prod_type _
      _ ≤ 36 * (d : ℤ) * (r : ℤ) ^ 4 * ((r : ℤ) ^ d) ^ 2 := sum_sq_centered_total hd_pos
  have hd_eq : (d : ℤ) = 24 * (r : ℤ) ^ 4 := by simp [d]
  have hbad_24 : 24 * (bad.card : ℤ) ≤ ((r : ℤ) ^ d) ^ 2 := by
    have hpos : (0 : ℤ) < 36 * (d : ℤ) * (r : ℤ) ^ 4 := by
      have : (0 : ℤ) < (r : ℤ) ^ 4 := by positivity
      have : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd_pos
      positivity
    have hrew : (bad.card : ℤ) * (36 * (d : ℤ) ^ 2) =
        (36 * (d : ℤ) * (r : ℤ) ^ 4) * (24 * (bad.card : ℤ)) := by
      rw [hd_eq]; ring
    have hrew2 : 36 * (d : ℤ) * (r : ℤ) ^ 4 * ((r : ℤ) ^ d) ^ 2 =
        (36 * (d : ℤ) * (r : ℤ) ^ 4) * ((r : ℤ) ^ d) ^ 2 := by ring
    rw [hrew, hrew2] at hbad_bound
    exact le_of_mul_le_mul_left hbad_bound hpos
  have hbad_nat : 24 * bad.card ≤ (r ^ d) ^ 2 := by exact_mod_cast hbad_24
  change 3 * (r ^ d) ^ 2 ≤ 4 * good.card
  omega

/- ### 3. Greedy balanced midpoint: every A-B edge lies in a triangle -/

private lemma greedy_signs (R : ℤ) (hR : 0 ≤ R) :
    ∀ (k : ℕ) (x : Fin k → ℤ), (∀ i, |x i| ≤ R) →
      ∃ ε : Fin k → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ |∑ i : Fin k, x i * ε i| ≤ R
  | 0, _, _ => ⟨Fin.elim0, fun i => i.elim0, by simpa using hR⟩
  | k + 1, x, hx => by
      obtain ⟨ε', hε', hS⟩ := greedy_signs R hR k (fun i => x i.castSucc) (fun i => hx i.castSucc)
      let S := ∑ i : Fin k, x i.castSucc * ε' i
      let y := x (Fin.last k)
      have hy : |y| ≤ R := hx (Fin.last k)
      have hS' : |S| ≤ R := hS
      let s : ℤ := if (0 ≤ S ∧ 0 ≤ y) ∨ (S < 0 ∧ y < 0) then -1 else 1
      have hs : s = 1 ∨ s = -1 := by
        dsimp [s]; split_ifs <;> simp
      have hsum_le : |S + y * s| ≤ R := by
        rw [abs_le] at hS' hy ⊢
        dsimp [s]
        split_ifs with h
        · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
        · push Not at h
          rcases h with ⟨h1, h2⟩
          by_cases hS0 : 0 ≤ S
          · have hy0 : y < 0 := h1 hS0
            constructor <;> linarith
          · push Not at hS0
            have hy0 : 0 ≤ y := h2 hS0
            constructor <;> linarith
      refine ⟨Fin.snoc ε' s, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa using hs
        · intro j; simpa using hε' j
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hsum_le

private lemma exists_balanced_midpoint {r : ℕ} (hr : 4 ≤ r) :
    let d := 24 * r ^ 4
    let μ : ℤ := 4 * ((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4
    let μ₄ : ℤ := ((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4
    ∀ a b : Fin d → Fin r, |sqDist a b - μ| ≤ (d : ℤ) →
      ∃ c : Fin d → Fin r, |sqDist c a - μ₄| ≤ 2 * (d : ℤ) ∧ |sqDist b c - μ₄| ≤ 2 * (d : ℤ) := by
  intro d μ μ₄ a b hab
  let x : Fin d → ℤ := fun i =>
    if ((a i).val + (b i).val) % 2 = 1 then (b i : ℤ) - (a i : ℤ) else 0
  have hx : ∀ i, |x i| ≤ (r : ℤ) := by
    intro i
    dsimp [x]
    split_ifs
    · have ha := (a i).isLt
      have hb := (b i).isLt
      rw [abs_le]; constructor <;> omega
    · simp
  obtain ⟨ε, hε, hS⟩ := greedy_signs (r : ℤ) (Nat.cast_nonneg r) d x hx
  let c : Fin d → Fin r := fun i =>
    if hodd : ((a i).val + (b i).val) % 2 = 1 then
      if ε i = 1 then ⟨((a i).val + (b i).val + 1) / 2, by have := (a i).isLt; have := (b i).isLt; omega⟩
      else ⟨((a i).val + (b i).val - 1) / 2, by have := (a i).isLt; have := (b i).isLt; omega⟩
    else ⟨((a i).val + (b i).val) / 2, by have := (a i).isLt; have := (b i).isLt; omega⟩
  have h2c : ∀ i, 2 * (c i : ℤ) =
      (a i : ℤ) + (b i : ℤ) + (if ((a i).val + (b i).val) % 2 = 1 then ε i else 0) := by
    intro i
    dsimp [c]
    split_ifs with hodd h1
    · rw [h1]
      change 2 * ((((a i).val + (b i).val + 1) / 2 : ℕ) : ℤ) = (a i : ℤ) + (b i : ℤ) + 1
      omega
    · have hm1 : ε i = -1 := (hε i).resolve_left h1
      rw [hm1]
      change 2 * ((((a i).val + (b i).val - 1) / 2 : ℕ) : ℤ) = (a i : ℤ) + (b i : ℤ) + -1
      omega
    · change 2 * ((((a i).val + (b i).val) / 2 : ℕ) : ℤ) = (a i : ℤ) + (b i : ℤ) + 0
      omega
  have hca_coord : ∀ i, 4 * ((c i : ℤ) - (a i : ℤ)) ^ 2 =
      ((b i : ℤ) - (a i : ℤ)) ^ 2 + (if ((a i).val + (b i).val) % 2 = 1 then (1 : ℤ) else 0) +
        2 * (x i * ε i) := by
    intro i
    have hc := h2c i
    have h4 : 4 * ((c i : ℤ) - (a i : ℤ)) ^ 2 = (2 * (c i : ℤ) - 2 * (a i : ℤ)) ^ 2 := by ring
    rw [h4, hc]
    dsimp [x]
    split_ifs with hodd
    · rcases hε i with h1 | hm1
      · rw [h1]; ring
      · rw [hm1]; ring
    · ring
  have hbc_coord : ∀ i, 4 * ((b i : ℤ) - (c i : ℤ)) ^ 2 =
      ((b i : ℤ) - (a i : ℤ)) ^ 2 + (if ((a i).val + (b i).val) % 2 = 1 then (1 : ℤ) else 0) -
        2 * (x i * ε i) := by
    intro i
    have hc := h2c i
    have h4 : 4 * ((b i : ℤ) - (c i : ℤ)) ^ 2 = (2 * (b i : ℤ) - 2 * (c i : ℤ)) ^ 2 := by ring
    rw [h4, hc]
    dsimp [x]
    split_ifs with hodd
    · rcases hε i with h1 | hm1
      · rw [h1]; ring
      · rw [hm1]; ring
    · ring
  set oddSum : ℤ := ∑ i : Fin d, (if ((a i).val + (b i).val) % 2 = 1 then (1 : ℤ) else 0)
  have hodd_nonneg : 0 ≤ oddSum := Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hodd_le : oddSum ≤ (d : ℤ) := by
    calc
      oddSum ≤ ∑ _i : Fin d, (1 : ℤ) := Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
      _ = (d : ℤ) := by simp
  have h4ca : 4 * sqDist c a = sqDist a b + oddSum + 2 * ∑ i : Fin d, x i * ε i := by
    unfold sqDist
    rw [Finset.mul_sum]
    simp_rw [hca_coord]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun i _ => by ring
  have h4bc : 4 * sqDist b c = sqDist a b + oddSum - 2 * ∑ i : Fin d, x i * ε i := by
    unfold sqDist
    rw [Finset.mul_sum]
    simp_rw [hbc_coord]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun i _ => by ring
  have hr_le_d : (r : ℤ) ≤ (d : ℤ) := by
    have : r ≤ 24 * r ^ 4 := by
      have : r ≤ r ^ 4 := Nat.le_self_pow (by norm_num) r
      omega
    exact_mod_cast this
  have h4μ₄ : 4 * μ₄ = μ := by simp [μ, μ₄]; ring
  rw [abs_le] at hab hS
  refine ⟨c, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

/- ### 4. Rankin lattice-point ball bound: `|{w ∈ ℤ^d | ∑ (w i)² ≤ 9d}| ≤ 1536^d` -/

private lemma sum_half_pow_Icc_eq (R : ℕ) :
    ∑ m ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (1 / 2 : ℝ) ^ m.natAbs =
      3 - 2 * (1 / 2 : ℝ) ^ R := by
  induction R with
  | zero => norm_num
  | succ k ih =>
      have hsplit : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
          insert ((k + 1 : ℕ) : ℤ)
            (insert (-((k + 1 : ℕ) : ℤ)) (Finset.Icc (-(k : ℤ)) (k : ℤ))) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot1 : ((k + 1 : ℕ) : ℤ) ∉
          insert (-((k + 1 : ℕ) : ℤ)) (Finset.Icc (-(k : ℤ)) (k : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc, not_or]
        omega
      have hnot2 : (-((k + 1 : ℕ) : ℤ)) ∉ Finset.Icc (-(k : ℤ)) (k : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hsplit, Finset.sum_insert hnot1, Finset.sum_insert hnot2, ih]
      have habs1 : (((k + 1 : ℕ) : ℤ)).natAbs = k + 1 := Int.natAbs_natCast (k + 1)
      have habs2 : (-((k + 1 : ℕ) : ℤ)).natAbs = k + 1 := by
        rw [Int.natAbs_neg, Int.natAbs_natCast]
      rw [habs1, habs2]
      ring

private lemma sum_half_pow_Icc_le_three (R : ℕ) :
    ∑ m ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (1 / 2 : ℝ) ^ m.natAbs ≤ 3 := by
  rw [sum_half_pow_Icc_eq]
  linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) R]

private def intBall (d : ℕ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(9 * d : ℤ)) (9 * d : ℤ))).filter
    (fun w => ∑ i : Fin d, (w i) ^ 2 ≤ 9 * (d : ℤ))

private lemma mem_intBall_iff {d : ℕ} (w : Fin d → ℤ) :
    w ∈ intBall d ↔ ∑ i : Fin d, (w i) ^ 2 ≤ 9 * (d : ℤ) := by
  unfold intBall
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
  intro hsum i
  have hsingle : (w i) ^ 2 ≤ ∑ j : Fin d, (w j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
  have hle : (w i) ^ 2 ≤ 9 * (d : ℤ) := hsingle.trans hsum
  have habs_le_sq : |w i| ≤ (w i) ^ 2 := by
    rcases le_or_gt 0 (w i) with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_neg h]; nlinarith
  rw [← abs_le]
  exact habs_le_sq.trans hle

private lemma card_intBall_le (d : ℕ) :
    (intBall d).card ≤ 1536 ^ d := by
  have hreal : ((intBall d).card : ℝ) ≤ (1536 : ℝ) ^ d := by
    let box : Finset (Fin d → ℤ) :=
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(9 * d : ℤ)) (9 * d : ℤ))
    have hsub : intBall d ⊆ box := Finset.filter_subset _ _
    have hstep1 : ((intBall d).card : ℝ) ≤
        (2 : ℝ) ^ (9 * d) * ∑ w ∈ intBall d, ∏ i : Fin d, (1 / 2 : ℝ) ^ (w i).natAbs := by
      rw [Finset.mul_sum]
      trans (∑ _w ∈ intBall d, (1 : ℝ))
      · simp
      · refine Finset.sum_le_sum fun w hw => ?_
        have hsum_sq : ∑ i : Fin d, (w i) ^ 2 ≤ 9 * (d : ℤ) := (mem_intBall_iff w).mp hw
        have hsum_abs : ∑ i : Fin d, (w i).natAbs ≤ 9 * d := by
          have h1 : ∀ i, ((w i).natAbs : ℤ) ≤ (w i) ^ 2 := fun i => by
            rw [Int.natCast_natAbs]
            rcases le_or_gt 0 (w i) with h | h
            · rw [abs_of_nonneg h]; nlinarith
            · rw [abs_of_neg h]; nlinarith
          have h2 : (∑ i : Fin d, ((w i).natAbs : ℤ)) ≤ 9 * (d : ℤ) :=
            (Finset.sum_le_sum fun i _ => h1 i).trans hsum_sq
          exact_mod_cast h2
        rw [Finset.prod_pow_eq_pow_sum]
        have hpow_ge : (1 / 2 : ℝ) ^ (9 * d) ≤ (1 / 2 : ℝ) ^ (∑ i : Fin d, (w i).natAbs) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hsum_abs
        have hmul := mul_le_mul_of_nonneg_left hpow_ge (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (9 * d))
        have hcancel : (2 : ℝ) ^ (9 * d) * (1 / 2 : ℝ) ^ (9 * d) = 1 := by
          rw [← mul_pow]; norm_num
        linarith
    have hstep2 :
        ∑ w ∈ intBall d, ∏ i : Fin d, (1 / 2 : ℝ) ^ (w i).natAbs ≤
        ∑ w ∈ box, ∏ i : Fin d, (1 / 2 : ℝ) ^ (w i).natAbs :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ =>
        Finset.prod_nonneg fun i _ => by positivity
    have hstep3 :
        ∑ w ∈ box, ∏ i : Fin d, (1 / 2 : ℝ) ^ (w i).natAbs ≤ (3 : ℝ) ^ d := by
      have hfac :
          ∏ _i : Fin d, ∑ m ∈ Finset.Icc (-(9 * d : ℤ)) (9 * d : ℤ), (1 / 2 : ℝ) ^ m.natAbs =
          ∑ w ∈ box, ∏ i : Fin d, (1 / 2 : ℝ) ^ (w i).natAbs := by
        simpa [box] using
          (Finset.prod_univ_sum (t := fun _ : Fin d => Finset.Icc (-(9 * d : ℤ)) (9 * d : ℤ))
            (f := fun _ m => (1 / 2 : ℝ) ^ m.natAbs))
      rw [← hfac]
      calc
        ∏ _i : Fin d, ∑ m ∈ Finset.Icc (-(9 * d : ℤ)) (9 * d : ℤ), (1 / 2 : ℝ) ^ m.natAbs
            ≤ ∏ _i : Fin d, (3 : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
            (fun _ _ => ?_)
          have := sum_half_pow_Icc_le_three (9 * d)
          simpa using this
        _ = (3 : ℝ) ^ d := by simp
    have h1536 : (2 : ℝ) ^ (9 * d) * (3 : ℝ) ^ d = (1536 : ℝ) ^ d := by
      rw [pow_mul, ← mul_pow]; norm_num
    calc
      ((intBall d).card : ℝ)
          ≤ (2 : ℝ) ^ (9 * d) * ∑ w ∈ intBall d, ∏ i : Fin d, (1 / 2 : ℝ) ^ (w i).natAbs := hstep1
      _ ≤ (2 : ℝ) ^ (9 * d) * ∑ w ∈ box, ∏ i : Fin d, (1 / 2 : ℝ) ^ (w i).natAbs :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ ≤ (2 : ℝ) ^ (9 * d) * (3 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left hstep3 (by positivity)
      _ = (1536 : ℝ) ^ d := h1536
  exact_mod_cast hreal

/- ### 5. The Fox–Loh tripartite graph and its triangle-filtered subgraph -/

section GraphConstruction

open scoped Classical

private abbrev Pt (r : ℕ) := Fin (24 * r ^ 4) → Fin r
private abbrev Vert (r : ℕ) := Fin 3 × Pt r

private def adjAB (r : ℕ) (a b : Pt r) : Prop :=
  let d : ℤ := (24 * r ^ 4 : ℕ)
  let μ : ℤ := 4 * ((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4
  |sqDist a b - μ| ≤ d

private def adjC (r : ℕ) (x c : Pt r) : Prop :=
  let d : ℤ := (24 * r ^ 4 : ℕ)
  let μ₄ : ℤ := ((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4
  |sqDist x c - μ₄| ≤ 2 * d

private def preGraph (r : ℕ) : SimpleGraph (Vert r) where
  Adj u v :=
    (u.1 = 0 ∧ v.1 = 1 ∧ adjAB r u.2 v.2) ∨
    (u.1 = 1 ∧ v.1 = 0 ∧ adjAB r v.2 u.2) ∨
    (u.1 = 0 ∧ v.1 = 2 ∧ adjC r u.2 v.2) ∨
    (u.1 = 2 ∧ v.1 = 0 ∧ adjC r v.2 u.2) ∨
    (u.1 = 1 ∧ v.1 = 2 ∧ adjC r u.2 v.2) ∨
    (u.1 = 2 ∧ v.1 = 1 ∧ adjC r v.2 u.2)
  symm := ⟨fun u v h => by
    rcases h with h | h | h | h | h | h
    · exact Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)
    · exact Or.inl ⟨h.2.1, h.1, h.2.2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩))))⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
      omega⟩

/-- The triangle-filtered subgraph: keep only edges of `preGraph r` that belong to a triangle. -/
private def flGraph (r : ℕ) : SimpleGraph (Vert r) where
  Adj u v := (preGraph r).Adj u v ∧ ∃ w : Vert r, (preGraph r).Adj u w ∧ (preGraph r).Adj v w
  symm := ⟨fun _ _ h => ⟨((preGraph r).adj_comm _ _).mp h.1,
    let ⟨w, hu, hv⟩ := h.2; ⟨w, hv, hu⟩⟩⟩
  loopless := ⟨fun _ h => (preGraph r).ne_of_adj h.1 rfl⟩

private lemma flGraph_every_edge_has_common {r : ℕ} {u v : Vert r} (h : (flGraph r).Adj u v) :
    ∃ w : Vert r, (flGraph r).Adj u w ∧ (flGraph r).Adj v w := by
  rcases h with ⟨huv, w, huw, hvw⟩
  refine ⟨w, ⟨huw, v, huv, ((preGraph r).adj_comm _ _).mp hvw⟩,
    ⟨hvw, u, ((preGraph r).adj_comm _ _).mp huv, ((preGraph r).adj_comm _ _).mp huw⟩⟩

private lemma flGraph_adj_AB {r : ℕ} (hr : 4 ≤ r) {a b : Pt r} (h : adjAB r a b) :
    (flGraph r).Adj (0, a) (1, b) := by
  have hpre : (preGraph r).Adj (0, a) (1, b) := Or.inl ⟨rfl, rfl, h⟩
  obtain ⟨c, hca, hbc⟩ := exists_balanced_midpoint hr a b h
  refine ⟨hpre, (2, c), ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simpa [adjC, sqDist_comm] using hca⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hbc⟩))))

private lemma preGraph_adj_0 {r : ℕ} (a : Pt r) (w : Vert r) :
    (preGraph r).Adj (0, a) w ↔ (w.1 = 1 ∧ adjAB r a w.2) ∨ (w.1 = 2 ∧ adjC r a w.2) := by
  simp [preGraph]

private lemma preGraph_adj_1 {r : ℕ} (b : Pt r) (w : Vert r) :
    (preGraph r).Adj (1, b) w ↔ (w.1 = 0 ∧ adjAB r w.2 b) ∨ (w.1 = 2 ∧ adjC r b w.2) := by
  simp [preGraph]

private lemma preGraph_adj_2 {r : ℕ} (c : Pt r) (w : Vert r) :
    (preGraph r).Adj (2, c) w ↔ (w.1 = 0 ∧ adjC r w.2 c) ∨ (w.1 = 1 ∧ adjC r w.2 c) := by
  simp [preGraph]

private lemma card_common_AB_le (r : ℕ) (a b : Pt r) (hab : adjAB r a b) :
    (Finset.univ.filter (fun w : Vert r =>
      (preGraph r).Adj (0, a) w ∧ (preGraph r).Adj (1, b) w)).card ≤ 1536 ^ (24 * r ^ 4) := by
  set d := 24 * r ^ 4
  let S := Finset.univ.filter (fun w : Vert r =>
    (preGraph r).Adj (0, a) w ∧ (preGraph r).Adj (1, b) w)
  have hmemS : ∀ w ∈ S, w.1 = 2 ∧ adjC r a w.2 ∧ adjC r b w.2 := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rcases hw.2 with ⟨h0w, h1w⟩
    rw [preGraph_adj_0] at h0w
    rw [preGraph_adj_1] at h1w
    rcases h0w with ⟨h1, _⟩ | ⟨hw2, hac⟩ <;> rcases h1w with ⟨h0, _⟩ | ⟨_, hbc⟩
    · rw [h1] at h0; cases h0
    · rw [h1] at *; simp_all
    · rw [hw2] at h0; cases h0
    · exact ⟨hw2, hac, hbc⟩
  have hle : S.card ≤ (intBall d).card := by
    refine Finset.card_le_card_of_injOn
      (fun w : Vert r => fun i : Fin d => 2 * (w.2 i : ℤ) - (a i : ℤ) - (b i : ℤ)) ?_ ?_
    · intro w hw
      obtain ⟨_, hac, hbc⟩ := hmemS w (Finset.mem_coe.mp hw)
      rw [Finset.mem_coe, mem_intBall_iff]
      have hpar : 2 * ∑ i : Fin d, (2 * (w.2 i : ℤ) - (a i : ℤ) - (b i : ℤ)) ^ 2 =
          4 * sqDist a w.2 + 4 * sqDist b w.2 - 2 * sqDist a b := by
        unfold sqDist
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      unfold adjAB at hab
      unfold adjC at hac hbc
      rw [abs_le] at hab hac hbc
      have h4μ : 4 * (((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4) =
          4 * ((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4 := by ring
      linarith
    · intro w₁ hw₁ w₂ hw₂ heq
      have hw₁2 := (hmemS w₁ (Finset.mem_coe.mp hw₁)).1
      have hw₂2 := (hmemS w₂ (Finset.mem_coe.mp hw₂)).1
      refine Prod.ext (hw₁2.trans hw₂2.symm) ?_
      funext i
      have hi := congrFun heq i
      dsimp at hi
      ext
      omega
  exact hle.trans (card_intBall_le d)

private lemma card_common_AC_le (r : ℕ) (a c : Pt r) (hac : adjC r a c) :
    (Finset.univ.filter (fun w : Vert r =>
      (preGraph r).Adj (0, a) w ∧ (preGraph r).Adj (2, c) w)).card ≤ 1536 ^ (24 * r ^ 4) := by
  set d := 24 * r ^ 4
  let S := Finset.univ.filter (fun w : Vert r =>
    (preGraph r).Adj (0, a) w ∧ (preGraph r).Adj (2, c) w)
  have hmemS : ∀ w ∈ S, w.1 = 1 ∧ adjAB r a w.2 ∧ adjC r w.2 c := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rcases hw.2 with ⟨h0w, h2w⟩
    rw [preGraph_adj_0] at h0w
    rw [preGraph_adj_2] at h2w
    rcases h0w with ⟨hw1, hab⟩ | ⟨h2, _⟩ <;> rcases h2w with ⟨h0, _⟩ | ⟨_, hbc⟩
    · rw [hw1] at h0; cases h0
    · exact ⟨hw1, hab, hbc⟩
    · rw [h2] at h0; cases h0
    · rw [h2] at *; simp_all
  have hle : S.card ≤ (intBall d).card := by
    refine Finset.card_le_card_of_injOn
      (fun w : Vert r => fun i : Fin d => (w.2 i : ℤ) - 2 * (c i : ℤ) + (a i : ℤ)) ?_ ?_
    · intro w hw
      obtain ⟨_, hab, hbc⟩ := hmemS w (Finset.mem_coe.mp hw)
      rw [Finset.mem_coe, mem_intBall_iff]
      have hid : ∑ i : Fin d, ((w.2 i : ℤ) - 2 * (c i : ℤ) + (a i : ℤ)) ^ 2 =
          2 * sqDist w.2 c + 2 * sqDist a c - sqDist a w.2 := by
        unfold sqDist
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      unfold adjAB at hab
      unfold adjC at hac hbc
      rw [abs_le] at hab hac hbc
      have h4μ : 4 * (((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4) =
          4 * ((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4 := by ring
      linarith
    · intro w₁ hw₁ w₂ hw₂ heq
      have hw₁1 := (hmemS w₁ (Finset.mem_coe.mp hw₁)).1
      have hw₂1 := (hmemS w₂ (Finset.mem_coe.mp hw₂)).1
      refine Prod.ext (hw₁1.trans hw₂1.symm) ?_
      funext i
      have hi := congrFun heq i
      dsimp at hi
      ext
      omega
  exact hle.trans (card_intBall_le d)

private lemma card_common_BC_le (r : ℕ) (b c : Pt r) (hbc : adjC r b c) :
    (Finset.univ.filter (fun w : Vert r =>
      (preGraph r).Adj (1, b) w ∧ (preGraph r).Adj (2, c) w)).card ≤ 1536 ^ (24 * r ^ 4) := by
  set d := 24 * r ^ 4
  let S := Finset.univ.filter (fun w : Vert r =>
    (preGraph r).Adj (1, b) w ∧ (preGraph r).Adj (2, c) w)
  have hmemS : ∀ w ∈ S, w.1 = 0 ∧ adjAB r w.2 b ∧ adjC r w.2 c := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rcases hw.2 with ⟨h1w, h2w⟩
    rw [preGraph_adj_1] at h1w
    rw [preGraph_adj_2] at h2w
    rcases h1w with ⟨hw0, hab⟩ | ⟨h2, _⟩ <;> rcases h2w with ⟨_, hac⟩ | ⟨h1, _⟩
    · exact ⟨hw0, hab, hac⟩
    · rw [hw0] at h1; cases h1
    · rw [h2] at *; simp_all
    · rw [h2] at h1; cases h1
  have hle : S.card ≤ (intBall d).card := by
    refine Finset.card_le_card_of_injOn
      (fun w : Vert r => fun i : Fin d => (w.2 i : ℤ) - 2 * (c i : ℤ) + (b i : ℤ)) ?_ ?_
    · intro w hw
      obtain ⟨_, hab, hac⟩ := hmemS w (Finset.mem_coe.mp hw)
      rw [Finset.mem_coe, mem_intBall_iff]
      have hid : ∑ i : Fin d, ((w.2 i : ℤ) - 2 * (c i : ℤ) + (b i : ℤ)) ^ 2 =
          2 * sqDist w.2 c + 2 * sqDist b c - sqDist w.2 b := by
        unfold sqDist
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      unfold adjAB at hab
      unfold adjC at hac hbc
      rw [abs_le] at hab hac hbc
      have h4μ : 4 * (((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4) =
          4 * ((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4 := by ring
      linarith
    · intro w₁ hw₁ w₂ hw₂ heq
      have hw₁0 := (hmemS w₁ (Finset.mem_coe.mp hw₁)).1
      have hw₂0 := (hmemS w₂ (Finset.mem_coe.mp hw₂)).1
      refine Prod.ext (hw₁0.trans hw₂0.symm) ?_
      funext i
      have hi := congrFun heq i
      dsimp at hi
      ext
      omega
  exact hle.trans (card_intBall_le d)

private lemma card_common_flGraph_le (r : ℕ) (u v : Vert r) (huv : (flGraph r).Adj u v) :
    (Finset.univ.filter (fun w : Vert r =>
      (flGraph r).Adj u w ∧ (flGraph r).Adj v w)).card ≤ 1536 ^ (24 * r ^ 4) := by
  have hsub :
      Finset.univ.filter (fun w : Vert r => (flGraph r).Adj u w ∧ (flGraph r).Adj v w) ⊆
      Finset.univ.filter (fun w : Vert r => (preGraph r).Adj u w ∧ (preGraph r).Adj v w) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ w, hw.2.1.1, hw.2.2.1⟩
  refine (Finset.card_le_card hsub).trans ?_
  rcases u with ⟨iu, xu⟩
  rcases v with ⟨iv, xv⟩
  rcases huv.1 with ⟨h0, h1, hab⟩ | ⟨h1, h0, hab⟩ | ⟨h0, h2, hac⟩ | ⟨h2, h0, hac⟩ |
      ⟨h1, h2, hbc⟩ | ⟨h2, h1, hbc⟩
  · subst h0; subst h1; exact card_common_AB_le r xu xv hab
  · subst h1; subst h0
    simpa [and_comm] using card_common_AB_le r xv xu hab
  · subst h0; subst h2; exact card_common_AC_le r xu xv hac
  · subst h2; subst h0
    simpa [and_comm] using card_common_AC_le r xv xu hac
  · subst h1; subst h2; exact card_common_BC_le r xu xv hbc
  · subst h2; subst h1
    simpa [and_comm] using card_common_BC_le r xv xu hbc

/- ### 6. Connecting common neighbors to `SimpleGraph.trianglesContaining` -/

private lemma trianglesContaining_nonempty_of_common {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v w : α} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    (G.trianglesContaining s(u, v)).Nonempty := by
  refine ⟨{u, v, w}, ?_⟩
  rw [SimpleGraph.trianglesContaining, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact huv
    · exact huw
    · exact (G.adj_comm _ _).mp huv
    · exact (hxy rfl).elim
    · exact hvw
    · exact (G.adj_comm _ _).mp huw
    · exact (G.adj_comm _ _).mp hvw
    · exact (hxy rfl).elim
  · have hne_uv : u ≠ v := G.ne_of_adj huv
    have hne_uw : u ≠ w := G.ne_of_adj huw
    have hne_vw : v ≠ w := G.ne_of_adj hvw
    rw [Finset.card_insert_of_notMem (by simp [hne_uv, hne_uw]),
      Finset.card_insert_of_notMem (by simp [hne_vw]), Finset.card_singleton]
  · intro x hx
    rw [Sym2.mem_toFinset, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> simp

private lemma card_trianglesContaining_le_common {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
    (G.trianglesContaining s(u, v)).card ≤
      (Finset.univ.filter (fun w : α => G.Adj u w ∧ G.Adj v w)).card := by
  let C := Finset.univ.filter (fun w : α => G.Adj u w ∧ G.Adj v w)
  have hsub : G.trianglesContaining s(u, v) ⊆ C.image (fun w => ({u, v, w} : Finset α)) := by
    intro t ht
    rw [SimpleGraph.trianglesContaining, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
    rcases ht with ⟨⟨hcl, hcard⟩, hsub_uv⟩
    have hu : u ∈ t := hsub_uv (by simp)
    have hv : v ∈ t := hsub_uv (by simp)
    have hne_uv : u ≠ v := G.ne_of_adj huv
    have hv' : v ∈ t.erase u := Finset.mem_erase.mpr ⟨hne_uv.symm, hv⟩
    have hcard_rem : ((t.erase u).erase v).card = 1 := by
      rw [Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu, hcard]
    obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp hcard_rem
    have hw_mem : w ∈ (t.erase u).erase v := by rw [hw_eq]; simp
    have hne_wv : w ≠ v := (Finset.mem_erase.mp hw_mem).1
    have hw_eu : w ∈ t.erase u := (Finset.mem_erase.mp hw_mem).2
    have hne_wu : w ≠ u := (Finset.mem_erase.mp hw_eu).1
    have hw_t : w ∈ t := (Finset.mem_erase.mp hw_eu).2
    have huw : G.Adj u w := hcl hu hw_t hne_wu.symm
    have hvw : G.Adj v w := hcl hv hw_t hne_wv.symm
    rw [Finset.mem_image]
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, huw, hvw⟩, ?_⟩
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact hu
      · exact hv
      · exact hw_t
    · intro hx
      by_cases hxu : x = u
      · exact Or.inl hxu
      · by_cases hxv : x = v
        · exact Or.inr (Or.inl hxv)
        · right; right
          have hx_rem : x ∈ (t.erase u).erase v :=
            Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, hx⟩⟩
          rw [hw_eq, Finset.mem_singleton] at hx_rem
          exact hx_rem
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/- ### 7. Packaging onto `Fin N` and finishing `Erdos80.erdos_80.parts.i` -/

private lemma exists_admissible_small_book (r : ℕ) (hr : 4 ≤ r) :
    let d := 24 * r ^ 4
    let N := 3 * r ^ d
    ∃ G : SimpleGraph (Fin N),
      Erdos80.Admissible (1 / 12 : ℝ) G ∧ Erdos80.bookNumber G ≤ 1536 ^ d := by
  intro d N
  have hcardV : Fintype.card (Vert r) = N := by
    simp [Vert, Pt, N, d, Fintype.card_prod, Fintype.card_pi, Finset.prod_const]
  let e : Fin N ≃ Vert r := (Fintype.equivFinOfCardEq hcardV).symm
  let G : SimpleGraph (Fin N) := (flGraph r).comap e
  refine ⟨G, ⟨?_, ?_⟩, ?_⟩
  · -- Edge count: #G.edgeFinset ≥ (1 / 12) * N^2
    let good : Finset (Pt r × Pt r) :=
      Finset.univ.filter (fun p => adjAB r p.1 p.2)
    have hgood_le : good.card ≤ G.edgeFinset.card := by
      refine Finset.card_le_card_of_injOn
        (fun p : Pt r × Pt r => s(e.symm (0, p.1), e.symm (1, p.2))) ?_ ?_
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset]
        show (flGraph r).Adj (e (e.symm (0, p.1))) (e (e.symm (1, p.2)))
        simp only [Equiv.apply_symm_apply]
        exact flGraph_adj_AB hr hp.2
      · intro p₁ _ p₂ _ heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, _⟩
        · have h1' := e.symm.injective h1
          have h2' := e.symm.injective h2
          have h1a : p₁.1 = p₂.1 := by simpa using congrArg Prod.snd h1'
          have h2b : p₁.2 = p₂.2 := by simpa using congrArg Prod.snd h2'
          exact Prod.ext h1a h2b
        · have h1' := congrArg Prod.fst (e.symm.injective h1)
          simp at h1'
    have hgood_ge := card_good_pairs_ge r hr
    have hgood_eq : good = Finset.univ.filter (fun p : (Fin d → Fin r) × (Fin d → Fin r) =>
        |sqDist p.1 p.2 - 4 * ((r : ℤ) ^ 2 - 1) * (r : ℤ) ^ 4| ≤ (d : ℤ)) := by
      ext p
      simp [good, adjAB, d]
    have hnat : 3 * (r ^ d) ^ 2 ≤ 4 * G.edgeFinset.card := by
      have h1 : 3 * (r ^ d) ^ 2 ≤ 4 * good.card := by
        rw [hgood_eq]
        exact hgood_ge
      omega
    have hreal : (3 : ℝ) * ((r : ℝ) ^ d) ^ 2 ≤ 4 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast hnat
    have hN : (N : ℝ) = 3 * (r : ℝ) ^ d := by simp [N]
    have h9 : (1 / 12 : ℝ) * (3 * (r : ℝ) ^ d) ^ 2 = (3 / 4 : ℝ) * ((r : ℝ) ^ d) ^ 2 := by ring
    rw [hN, h9]
    have hgoal_div : (3 / 4 : ℝ) * ((r : ℝ) ^ d) ^ 2 ≤ (G.edgeFinset.card : ℝ) := by linarith
    convert hgoal_div using 2
    congr 1
  · -- EveryEdgeInTriangle G
    intro ed hed
    rw [SimpleGraph.mem_edgeFinset] at hed
    induction ed using Sym2.ind with
    | _ x y =>
      have hadj : (flGraph r).Adj (e x) (e y) := hed
      obtain ⟨w, hxw, hyw⟩ := flGraph_every_edge_has_common hadj
      refine trianglesContaining_nonempty_of_common G hadj (w := e.symm w) ?_ ?_
      · simpa [G] using hxw
      · simpa [G] using hyw
  · -- bookNumber G ≤ 1536 ^ d
    unfold Erdos80.bookNumber
    rw [Finset.sup_le_iff]
    intro ed hed
    rw [SimpleGraph.mem_edgeFinset] at hed
    induction ed using Sym2.ind with
    | _ x y =>
      have htri := card_trianglesContaining_le_common G hed
      have hbij :
          (Finset.univ.filter (fun w : Fin N => G.Adj x w ∧ G.Adj y w)).card ≤
          (Finset.univ.filter (fun w : Vert r =>
            (flGraph r).Adj (e x) w ∧ (flGraph r).Adj (e y) w)).card := by
        refine Finset.card_le_card_of_injOn e ?_ (fun _ _ _ _ h => e.injective h)
        intro w hw
        rw [Finset.mem_coe, Finset.mem_filter] at hw ⊢
        exact ⟨Finset.mem_univ _, hw.2.1, hw.2.2⟩
      exact htri.trans (hbij.trans (card_common_flGraph_le r (e x) (e y) hed))

end GraphConstruction

theorem erdos_80_part_i :
    ¬ ∀ c : ℝ, 0 < c → c < 1 / 2 →
      ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ ε < Erdos80.f c n := by
  classical
  intro hall
  obtain ⟨ε, hε, hev⟩ := hall (1 / 12) (by norm_num) (by norm_num)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  let r : ℕ := max 4 (max N₀ (Nat.ceil ((1536 : ℝ) ^ (1 / ε)) + 1))
  have hr4 : 4 ≤ r := le_max_left _ _
  have hrN₀ : N₀ ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hr_gt : (1536 : ℝ) ^ (1 / ε) < (r : ℝ) := by
    have hceil : Nat.ceil ((1536 : ℝ) ^ (1 / ε)) + 1 ≤ r :=
      (le_max_right _ _).trans (le_max_right _ _)
    have h1 : (1536 : ℝ) ^ (1 / ε) ≤ (Nat.ceil ((1536 : ℝ) ^ (1 / ε)) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil ((1536 : ℝ) ^ (1 / ε)) : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hceil
    linarith
  let d : ℕ := 24 * r ^ 4
  let N : ℕ := 3 * r ^ d
  have hd_pos : 1 ≤ d := by
    have : 1 ≤ r ^ 4 := one_le_pow₀ (by omega)
    omega
  have hN_ge : N₀ ≤ N := by
    have h1 : r ≤ r ^ d := Nat.le_self_pow (by omega) r
    omega
  obtain ⟨G, hadm, hbook⟩ := exists_admissible_small_book r hr4
  have hf_le : Erdos80.f (1 / 12 : ℝ) N ≤ Erdos80.bookNumber G :=
    Nat.sInf_le ⟨G, hadm, rfl⟩
  have hf_le_pow : (Erdos80.f (1 / 12 : ℝ) N : ℝ) ≤ (1536 : ℝ) ^ d := by
    exact_mod_cast hf_le.trans hbook
  have h1536_lt_rε : (1536 : ℝ) < (r : ℝ) ^ ε := by
    have h := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ (1536 : ℝ) ^ (1 / ε)) hr_gt hε
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1536), one_div_mul_cancel hε.ne',
      Real.rpow_one] at h
    exact h
  have hpow_lt : (1536 : ℝ) ^ d < (N : ℝ) ^ ε := by
    have h1 : (1536 : ℝ) ^ d < ((r : ℝ) ^ ε) ^ d :=
      pow_lt_pow_left₀ h1536_lt_rε (by norm_num) (by omega)
    have h2 : ((r : ℝ) ^ ε) ^ d = ((r : ℝ) ^ d) ^ ε := by
      rw [← Real.rpow_natCast ((r : ℝ) ^ ε) d, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (r : ℝ)),
        mul_comm, Real.rpow_mul (by positivity : (0 : ℝ) ≤ (r : ℝ)), Real.rpow_natCast]
    have h3 : ((r : ℝ) ^ d) ^ ε ≤ (N : ℝ) ^ ε := by
      refine Real.rpow_le_rpow (by positivity) ?_ hε.le
      have : r ^ d ≤ N := by simp [N]; omega
      exact_mod_cast this
    linarith
  have hlt := hN₀ N hN_ge
  linarith

end Erdos80PartIProof

theorem OMA.solution : type_of% @Erdos80.erdos_80.parts.i :=
  Erdos80PartIProof.erdos_80_part_i
