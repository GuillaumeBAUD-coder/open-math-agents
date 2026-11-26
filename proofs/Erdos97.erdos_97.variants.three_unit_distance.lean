import FormalConjectures.ErdosProblems.«97»
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Finset.SymmDiff

/-!
# Disproof of the Generalized Fixed-k Equidistant Conjecture (Erdős Problem 97)

We disprove `Erdos97.erdos_97.variants.three_unit_distance`: for every natural number `k`,
there exists a nonempty finite set `A ⊂ ℝ²` in strictly convex position (`ConvexIndep A`)
such that every vertex of `A` has at least `k` vertices in `A` at distance `1` from it.

The geometric construction follows Kruer, Kohlmeyer, and Price (Unit Distances in Convex
Polygons, 2026):
1. Strict supporting-line criterion `H(z, w) = Re(conj z * (w - z)) < 0` implies `ConvexIndep`.
2. Commuting products of small rotations indexed by edges of a finite simple bipartite graph.
3. Base-5 coding of the `d`-regular middle levels graph with seed points `a_i(ε)` and exact
   unit-distance edge rotations `w_e(ε)` of order `1 + O(ε^3)`.
4. Perturbation of vertex radii in an open neighborhood to separate all bounded rotation
   products, proved via 2D rectangular finite differences and two applications of the 1D
   mean value theorem on `γ(r, s) = arccos((r^2 + s^2 - 1)/(2rs))`.
5. Core-subgraph vertex peeling to obtain minimum unit-distance degree at least `k`.
-/

open EuclideanGeometry Real Complex Filter Topology

namespace Erdos97Disproof

/- ## Helpers for continuity and limits -/

lemma continuous_complex_mk {α : Type*} [TopologicalSpace α] {f g : α → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => (⟨f x, g x⟩ : ℂ)) := by
  have heq : (fun x => (⟨f x, g x⟩ : ℂ)) = fun x => (f x : ℂ) + (g x : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp
  rw [heq]
  exact (Complex.continuous_ofReal.comp hf).add
    ((Complex.continuous_ofReal.comp hg).mul continuous_const)

lemma tendsto_complex_mk {α : Type*} {l : Filter α} {f g : α → ℝ} {a b : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x => (⟨f x, g x⟩ : ℂ)) l (𝓝 (⟨a, b⟩ : ℂ)) := by
  have heq : (fun x => (⟨f x, g x⟩ : ℂ)) = fun x => (f x : ℂ) + (g x : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp
  have hab : (⟨a, b⟩ : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [heq, hab]
  exact ((Complex.continuous_ofReal.tendsto a).comp hf).add
    (((Complex.continuous_ofReal.tendsto b).comp hg).mul tendsto_const_nhds)

lemma continuousAt_prod_finset {α ι : Type*} [TopologicalSpace α] [DecidableEq ι]
    (s : Finset ι) (f : ι → α → ℂ) (x : α) (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∏ i ∈ s, f i y) x := by
  induction s using Finset.induction with
  | empty => simp [continuousAt_const]
  | insert a t ha ih =>
    have heq : (fun y => ∏ i ∈ insert a t, f i y) = fun y => f a y * ∏ i ∈ t, f i y := by
      funext y; exact Finset.prod_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma continuousAt_sum_finset {α ι : Type*} [TopologicalSpace α] [DecidableEq ι]
    (s : Finset ι) (f : ι → α → ℝ) (x : α) (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  induction s using Finset.induction with
  | empty => simp [continuousAt_const]
  | insert a t ha ih =>
    have heq : (fun y => ∑ i ∈ insert a t, f i y) = fun y => f a y + ∑ i ∈ t, f i y := by
      funext y; exact Finset.sum_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma tendsto_nhdsGT_zero_of_continuous {f : ℝ → ℝ} {c : ℝ} (hc : Continuous f) (h0 : f 0 = c) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  rw [← h0]
  exact (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

/- ## Section 1: Isometry `ℂ → ℝ²` and strict supporting-line criterion -/

noncomputable def cToR2 (z : ℂ) : ℝ² := !₂[z.re, z.im]

lemma cToR2_apply_zero (z : ℂ) : cToR2 z 0 = z.re := by
  simp [cToR2]

lemma cToR2_apply_one (z : ℂ) : cToR2 z 1 = z.im := by
  simp [cToR2]

lemma cToR2_injective : Function.Injective cToR2 := by
  intro z w h
  apply Complex.ext
  · have h0 := congrArg (fun p : ℝ² => p 0) h
    simpa [cToR2_apply_zero] using h0
  · have h1 := congrArg (fun p : ℝ² => p 1) h
    simpa [cToR2_apply_one] using h1

lemma dist_cToR2 (z w : ℂ) : dist (cToR2 z) (cToR2 w) = ‖z - w‖ := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [cToR2_apply_zero, cToR2_apply_one, Real.dist_eq, sq_abs]
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- Supporting-line functional `H(z, w) = ⟨z, w - z⟩ = Re(conj z * (w - z))`. -/
def H (z w : ℂ) : ℝ := z.re * (w.re - z.re) + z.im * (w.im - z.im)

lemma H_eq_re (z w : ℂ) : H z w = (star z * (w - z)).re := by
  simp [H]

lemma two_mul_H (z w : ℂ) : 2 * H z w = ‖w‖ ^ 2 - ‖z‖ ^ 2 - ‖w - z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, H, Complex.sub_re, Complex.sub_im]
  ring

lemma H_lt_zero_of_norm_eq {z w : ℂ} (hnorm : ‖z‖ = ‖w‖) (hne : z ≠ w) : H z w < 0 := by
  have hpos : 0 < ‖w - z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))
  have h2 := two_mul_H z w
  rw [hnorm] at h2
  linarith

lemma abs_H_mul_sub_H_le (z w u v : ℂ) (hu : ‖u‖ = 1) (_hv : ‖v‖ = 1) :
    |H (z * u) (w * v) - H z w| ≤ ‖z‖ * ‖w‖ * (‖u - 1‖ + ‖v - 1‖) := by
  have hdiff : H (z * u) (w * v) - H z w = (star z * w * (star u * v - 1)).re := by
    have h1 : ‖z * u‖ ^ 2 = ‖z‖ ^ 2 := by rw [norm_mul, hu, mul_one]
    have h2 : H (z * u) (w * v) = (star (z * u) * (w * v)).re - ‖z * u‖ ^ 2 := by
      rw [H_eq_re, mul_sub, Complex.sub_re]
      congr 1
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [mul_comm]
      ring
    have h3 : H z w = (star z * w).re - ‖z‖ ^ 2 := by
      rw [H_eq_re, mul_sub, Complex.sub_re]
      congr 1
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [mul_comm]
    have h4 : star (z * u) * (w * v) - star z * w = star z * w * (star u * v - 1) := by
      rw [star_mul]
      ring
    have h5 : (star (z * u) * (w * v)).re - (star z * w).re =
        (star z * w * (star u * v - 1)).re := by
      rw [← Complex.sub_re, h4]
    rw [h2, h3, h1]
    linarith
  rw [hdiff]
  calc |(star z * w * (star u * v - 1)).re|
      ≤ ‖star z * w * (star u * v - 1)‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ * ‖w‖ * ‖star u * v - 1‖ := by simp
    _ ≤ ‖z‖ * ‖w‖ * (‖u - 1‖ + ‖v - 1‖) := by
        gcongr
        have hsplit : star u * v - 1 = star u * (v - 1) + star (u - 1) := by
          simp only [star_sub, star_one]
          ring
        rw [hsplit]
        calc ‖star u * (v - 1) + star (u - 1)‖
            ≤ ‖star u * (v - 1)‖ + ‖star (u - 1)‖ := norm_add_le _ _
          _ = ‖v - 1‖ + ‖u - 1‖ := by rw [norm_mul, norm_star, hu, one_mul, norm_star]
          _ = ‖u - 1‖ + ‖v - 1‖ := add_comm _ _

/-- If `H z w < 0` for all distinct `z, w ∈ P`, then `P.image cToR2` is convex independent. -/
lemma convexIndep_of_H_neg (P : Finset ℂ) (hH : ∀ z ∈ P, ∀ w ∈ P, z ≠ w → H z w < 0) :
    ConvexIndep ((P.image cToR2 : Finset ℝ²) : Set ℝ²) := by
  intro a ha
  rcases Finset.mem_image.mp (Finset.mem_coe.mp ha) with ⟨z, hzP, rfl⟩
  let S : Set ℝ² := {x : ℝ² | z.re * x 0 + z.im * x 1 < z.re * z.re + z.im * z.im}
  have hconv : Convex ℝ S := by
    intro x hx y hy c₁ c₂ hc₁ hc₂ hsum
    change z.re * (c₁ • x + c₂ • y) 0 + z.im * (c₁ • x + c₂ • y) 1 < z.re * z.re + z.im * z.im
    have h0 : (c₁ • x + c₂ • y) 0 = c₁ * x 0 + c₂ * y 0 := by simp
    have h1 : (c₁ • x + c₂ • y) 1 = c₁ * x 1 + c₂ * y 1 := by simp
    rw [h0, h1]
    have hx' : z.re * x 0 + z.im * x 1 < z.re * z.re + z.im * z.im := hx
    have hy' : z.re * y 0 + z.im * y 1 < z.re * z.re + z.im * z.im := hy
    have hcalc :
        z.re * (c₁ * x 0 + c₂ * y 0) + z.im * (c₁ * x 1 + c₂ * y 1) =
          c₁ * (z.re * x 0 + z.im * x 1) + c₂ * (z.re * y 0 + z.im * y 1) := by ring
    rw [hcalc]
    have htarget : z.re * z.re + z.im * z.im =
        c₁ * (z.re * z.re + z.im * z.im) + c₂ * (z.re * z.re + z.im * z.im) := by
      rw [← add_mul, hsum, one_mul]
    rw [htarget]
    by_cases hcz : c₁ = 0
    · have hc2 : c₂ = 1 := by linarith
      rw [hcz, hc2]
      linarith
    · have hc1pos : 0 < c₁ := lt_of_le_of_ne hc₁ (Ne.symm hcz)
      have h1lt : c₁ * (z.re * x 0 + z.im * x 1) < c₁ * (z.re * z.re + z.im * z.im) :=
        mul_lt_mul_of_pos_left hx' hc1pos
      have h2le : c₂ * (z.re * y 0 + z.im * y 1) ≤ c₂ * (z.re * z.re + z.im * z.im) :=
        mul_le_mul_of_nonneg_left (le_of_lt hy') hc₂
      linarith
  have hsub : ((P.image cToR2 : Finset ℝ²) : Set ℝ²) \ {cToR2 z} ⊆ S := by
    intro b hb
    rcases hb with ⟨hbA, hbne⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hbA) with ⟨w, hwP, rfl⟩
    have hne : z ≠ w := by
      intro hzw
      exact hbne (by simp [hzw])
    have hzw := hH z hzP w hwP hne
    change z.re * (cToR2 w) 0 + z.im * (cToR2 w) 1 < z.re * z.re + z.im * z.im
    rw [cToR2_apply_zero, cToR2_apply_one]
    unfold H at hzw
    linarith
  intro hmem
  have hInS : cToR2 z ∈ S := convexHull_min hsub hconv hmem
  change z.re * (cToR2 z) 0 + z.im * (cToR2 z) 1 < z.re * z.re + z.im * z.im at hInS
  rw [cToR2_apply_zero, cToR2_apply_one] at hInS
  exact lt_irrefl _ hInS

/- ## Section 2: Lemma 2.1 (Commuting products of rotations) -/

lemma norm_pow_sub_one_le {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ (n : ℝ) * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hsplit : z ^ (m + 1) - 1 = z * (z ^ m - 1) + (z - 1) := by ring
    rw [hsplit]
    calc ‖z * (z ^ m - 1) + (z - 1)‖
        ≤ ‖z * (z ^ m - 1)‖ + ‖z - 1‖ := norm_add_le _ _
      _ = ‖z ^ m - 1‖ + ‖z - 1‖ := by rw [norm_mul, hz, one_mul]
      _ ≤ (m : ℝ) * ‖z - 1‖ + ‖z - 1‖ := by linarith
      _ = ((m + 1 : ℕ) : ℝ) * ‖z - 1‖ := by push_cast; ring

lemma norm_prod_sub_one_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ = 1) :
    ‖(∏ i ∈ s, f i) - 1‖ ≤ ∑ i ∈ s, ‖f i - 1‖ := by
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : ‖f a‖ = 1 := hf a (Finset.mem_insert_self a t)
    have hft : ∀ i ∈ t, ‖f i‖ = 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsplit : f a * (∏ i ∈ t, f i) - 1 = f a * ((∏ i ∈ t, f i) - 1) + (f a - 1) := by ring
    rw [hsplit]
    calc ‖f a * ((∏ i ∈ t, f i) - 1) + (f a - 1)‖
        ≤ ‖f a * ((∏ i ∈ t, f i) - 1)‖ + ‖f a - 1‖ := norm_add_le _ _
      _ = ‖(∏ i ∈ t, f i) - 1‖ + ‖f a - 1‖ := by rw [norm_mul, hfa, one_mul]
      _ ≤ (∑ i ∈ t, ‖f i - 1‖) + ‖f a - 1‖ := by linarith [ih hft]
      _ = ‖f a - 1‖ + ∑ i ∈ t, ‖f i - 1‖ := add_comm _ _

noncomputable def rotProd {E : Type*} [Fintype E] {q : ℕ} (w : E → ℂ) (a : E → Fin q) : ℂ :=
  ∏ e : E, (w e) ^ (a e : ℕ)

lemma norm_rotProd {E : Type*} [Fintype E] {q : ℕ} (w : E → ℂ)
    (hw : ∀ e, ‖w e‖ = 1) (a : E → Fin q) : ‖rotProd w a‖ = 1 := by
  unfold rotProd
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro e _
  rw [norm_pow, hw e, one_pow]

lemma norm_rotProd_sub_one_le {E : Type*} [Fintype E] [DecidableEq E] {q : ℕ} (w : E → ℂ)
    (hw : ∀ e, ‖w e‖ = 1) (a : E → Fin q) :
    ‖rotProd w a - 1‖ ≤ ((q - 1 : ℕ) : ℝ) * ∑ e : E, ‖w e - 1‖ := by
  unfold rotProd
  calc ‖(∏ e : E, (w e) ^ (a e : ℕ)) - 1‖
      ≤ ∑ e : E, ‖(w e) ^ (a e : ℕ) - 1‖ := by
        apply norm_prod_sub_one_le
        intro e _
        rw [norm_pow, hw e, one_pow]
    _ ≤ ∑ e : E, ((a e : ℕ) : ℝ) * ‖w e - 1‖ := by
        apply Finset.sum_le_sum
        intro e _
        exact norm_pow_sub_one_le (hw e) (a e : ℕ)
    _ ≤ ∑ e : E, ((q - 1 : ℕ) : ℝ) * ‖w e - 1‖ := by
        apply Finset.sum_le_sum
        intro e _
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact_mod_cast Nat.le_sub_one_of_lt (a e).isLt
    _ = ((q - 1 : ℕ) : ℝ) * ∑ e : E, ‖w e - 1‖ := by rw [← Finset.mul_sum]

lemma card_filter_lt_sub_one {E : Type*} [Fintype E] [DecidableEq E] {q : ℕ} (hq : 1 ≤ q) (e : E) :
    q * (Finset.univ.filter fun a : E → Fin q => (a e : ℕ) + 1 < q).card =
      (q - 1) * Fintype.card (E → Fin q) := by
  let S : Finset (E → Fin q) := Finset.univ.filter fun a => (a e : ℕ) + 1 < q
  let F : Fin q → Finset (E → Fin q) := fun r => Finset.univ.filter fun a => a e = r
  have hF_card : ∀ r : Fin q, (F r).card = Fintype.card ({e' : E // e' ≠ e} → Fin q) := by
    intro r
    refine Finset.card_bij (fun a _ => fun x : {e' : E // e' ≠ e} => a x.1) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a₁ ha₁ a₂ ha₂ heq
      funext x
      by_cases hx : x = e
      · subst hx
        have h1 : a₁ x = r := (Finset.mem_filter.mp ha₁).2
        have h2 : a₂ x = r := (Finset.mem_filter.mp ha₂).2
        exact h1.trans h2.symm
      · exact congrFun heq ⟨x, hx⟩
    · intro f _
      refine ⟨fun x => if h : x = e then r else f ⟨x, h⟩, ?_, ?_⟩
      · simp [F]
      · funext ⟨x, hx⟩
        simp [hx]
  have hS_eq : S = (Finset.univ.filter fun r : Fin q => (r : ℕ) + 1 < q).biUnion F := by
    ext a
    simp only [S, F, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro ha; exact ⟨a e, ha, rfl⟩
    · rintro ⟨r, hr, hre⟩; rwa [hre]
  have hdisj : Set.PairwiseDisjoint
      ((Finset.univ.filter fun r : Fin q => (r : ℕ) + 1 < q) : Set (Fin q)) F := by
    intro r₁ _ r₂ _ hne
    change Disjoint (F r₁) (F r₂)
    rw [Finset.disjoint_left]
    intro a h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hS_card : S.card = (q - 1) * Fintype.card ({e' : E // e' ≠ e} → Fin q) := by
    rw [hS_eq, Finset.card_biUnion hdisj]
    have hsum : ∑ r ∈ Finset.univ.filter (fun r : Fin q => (r : ℕ) + 1 < q), (F r).card =
        (Finset.univ.filter (fun r : Fin q => (r : ℕ) + 1 < q)).card *
          Fintype.card ({e' : E // e' ≠ e} → Fin q) := by
      simp [hF_card]
    rw [hsum]
    congr 1
    have hcompl : (Finset.univ.filter fun r : Fin q => (r : ℕ) + 1 < q) =
        Finset.univ.erase ⟨q - 1, Nat.sub_lt hq Nat.one_pos⟩ := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true, Finset.mem_erase, ne_eq,
        Fin.ext_iff]
      have hrlt : (r : ℕ) < q := r.isLt
      omega
    rw [hcompl, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hU_eq : (Finset.univ : Finset (E → Fin q)) = Finset.univ.biUnion F := by
    ext a
    simp [F]
  have hdisjU : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin q)) : Set (Fin q)) F := by
    intro r₁ _ r₂ _ hne
    change Disjoint (F r₁) (F r₂)
    rw [Finset.disjoint_left]
    intro a h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hU_card : Fintype.card (E → Fin q) = q * Fintype.card ({e' : E // e' ≠ e} → Fin q) := by
    rw [← Finset.card_univ, hU_eq, Finset.card_biUnion hdisjU]
    simp [hF_card]
  rw [hS_card, hU_card]
  ring

lemma lemma_2_1 {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R)) {q : ℕ} (hq : 2 ≤ q)
    (b : L ⊕ R → ℂ) (w : E → ℂ)
    (hb_pos : ∀ i, 0 < ‖b i‖) (hb_le : ∀ i, ‖b i‖ ≤ 1)
    (hb_inj : ∀ i j, ‖b i‖ = ‖b j‖ → i = j)
    (hw_unit : ∀ e, ‖w e‖ = 1)
    (hw_dist : ∀ e : E, ‖b (Sum.inl e.1.1) - b (Sum.inr e.1.2) * w e‖ = 1)
    (hH_gap : ∀ i j, i ≠ j → H (b i) (b j) < -2 * (((q - 1 : ℕ) : ℝ) * ∑ e : E, ‖w e - 1‖))
    (hW_inj : Function.Injective (rotProd w : (E → Fin q) → ℂ)) :
    ∃ P : Finset ℂ,
      P.card = Fintype.card (L ⊕ R) * q ^ E.card ∧
      (∀ z ∈ P, ∀ z' ∈ P, z ≠ z' → H z z' < 0) ∧
      q * (∑ p ∈ P, (P.filter fun p' => ‖p - p'‖ = 1).card) ≥
        2 * E.card * (q - 1) * q ^ E.card := by
  classical
  let pt : (L ⊕ R) × (E → Fin q) → ℂ := fun p => b p.1 * rotProd w p.2
  have hpt_inj : Function.Injective pt := by
    intro ⟨i, a⟩ ⟨j, a'⟩ h
    have hnorm : ‖b i‖ = ‖b j‖ := by
      have hn := congrArg norm h
      simp only [pt, norm_mul, norm_rotProd w hw_unit, mul_one] at hn
      exact hn
    have hij : i = j := hb_inj i j hnorm
    subst hij
    have hbi_ne : b i ≠ 0 := norm_pos_iff.mp (hb_pos i)
    have hW : rotProd w a = rotProd w a' := mul_left_cancel₀ hbi_ne h
    exact Prod.ext rfl (hW_inj hW)
  let P : Finset ℂ := Finset.univ.image pt
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hpt_inj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  · intro z hz z' hz' hne
    rcases Finset.mem_image.mp hz with ⟨⟨i, a⟩, _, rfl⟩
    rcases Finset.mem_image.mp hz' with ⟨⟨j, a'⟩, _, rfl⟩
    by_cases hij : i = j
    · subst hij
      apply H_lt_zero_of_norm_eq _ hne
      simp [pt, norm_rotProd w hw_unit]
    · set Hval : ℝ := ((q - 1 : ℕ) : ℝ) * ∑ e : E, ‖w e - 1‖
      have ha1 := norm_rotProd_sub_one_le w hw_unit a
      have ha2 := norm_rotProd_sub_one_le w hw_unit a'
      have hdiff := abs_H_mul_sub_H_le (b i) (b j) (rotProd w a) (rotProd w a')
        (norm_rotProd w hw_unit a) (norm_rotProd w hw_unit a')
      have hprod_le : ‖b i‖ * ‖b j‖ ≤ 1 := by
        calc ‖b i‖ * ‖b j‖ ≤ 1 * 1 := mul_le_mul (hb_le i) (hb_le j) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hsum_nonneg : 0 ≤ ‖rotProd w a - 1‖ + ‖rotProd w a' - 1‖ :=
        add_nonneg (norm_nonneg _) (norm_nonneg _)
      have hbound : |H (pt (i, a)) (pt (j, a')) - H (b i) (b j)| ≤ 2 * Hval := by
        calc |H (pt (i, a)) (pt (j, a')) - H (b i) (b j)|
            ≤ ‖b i‖ * ‖b j‖ * (‖rotProd w a - 1‖ + ‖rotProd w a' - 1‖) := hdiff
          _ ≤ 1 * (‖rotProd w a - 1‖ + ‖rotProd w a' - 1‖) :=
              mul_le_mul_of_nonneg_right hprod_le hsum_nonneg
          _ = ‖rotProd w a - 1‖ + ‖rotProd w a' - 1‖ := one_mul _
          _ ≤ Hval + Hval := add_le_add ha1 ha2
          _ = 2 * Hval := by ring
      have hgap := hH_gap i j hij
      linarith [(abs_le.mp hbound).2]
  · -- Count ordered unit-distance pairs in P ×ˢ P
    let pairs : Finset (ℂ × ℂ) := (P ×ˢ P).filter fun pq => ‖pq.1 - pq.2‖ = 1
    let row : ℂ → Finset (ℂ × ℂ) := fun p => (P.filter fun p' => ‖p - p'‖ = 1).image (fun p' => (p, p'))
    have hsum_eq : ∑ p ∈ P, (P.filter fun p' => ‖p - p'‖ = 1).card = pairs.card := by
      have hbi : pairs = P.biUnion row := by
        ext ⟨p, p'⟩
        simp only [pairs, row, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
          Finset.mem_image]
        constructor
        · rintro ⟨⟨hp, hp'⟩, hd⟩
          exact ⟨p, hp, p', ⟨hp', hd⟩, rfl⟩
        · rintro ⟨a, ha, b', ⟨hb', hd⟩, heq⟩
          rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
          exact ⟨⟨ha, hb'⟩, hd⟩
      have hdisj : Set.PairwiseDisjoint (↑P : Set ℂ) row := by
        intro p₁ _ p₂ _ hne
        change Disjoint (row p₁) (row p₂)
        rw [Finset.disjoint_left]
        intro ⟨x, y⟩ h1 h2
        rcases Finset.mem_image.mp h1 with ⟨_, _, h1eq⟩
        rcases Finset.mem_image.mp h2 with ⟨_, _, h2eq⟩
        exact hne ((Prod.mk.inj h1eq).1.trans (Prod.mk.inj h2eq).1.symm)
      rw [hbi, Finset.card_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro p _
      exact (Finset.card_image_of_injective _ fun _ _ h => (Prod.mk.inj h).2).symm
    rw [hsum_eq]
    let stepIdx : Finset (Σ e : E, E → Fin q) :=
      Finset.univ.sigma fun e : E => Finset.univ.filter fun a : E → Fin q => (a e : ℕ) + 1 < q
    let good : Finset (Bool × Σ e : E, E → Fin q) := Finset.univ ×ˢ stepIdx
    let f : (Bool × Σ e : E, E → Fin q) → ℂ × ℂ := fun x =>
      if h : (x.2.2 x.2.1 : ℕ) + 1 < q then
        let a' : E → Fin q := Function.update x.2.2 x.2.1 ⟨(x.2.2 x.2.1 : ℕ) + 1, h⟩
        if x.1 then (pt (Sum.inr x.2.1.1.2, a'), pt (Sum.inl x.2.1.1.1, x.2.2))
        else (pt (Sum.inl x.2.1.1.1, x.2.2), pt (Sum.inr x.2.1.1.2, a'))
      else (0, 0)
    have hcard_le : good.card ≤ pairs.card := by
      apply Finset.card_le_card_of_injOn f
      · intro ⟨side, ⟨e, a⟩⟩ hx
        have hlt : (a e : ℕ) + 1 < q := by
          simp only [Finset.mem_coe, good, stepIdx, Finset.mem_product, Finset.mem_univ, true_and,
            Finset.mem_sigma, Finset.mem_filter] at hx
          exact hx
        let a' : E → Fin q := Function.update a e ⟨(a e : ℕ) + 1, hlt⟩
        have hW_step : rotProd w a' = rotProd w a * w e := by
          unfold rotProd
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e),
              ← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
          have hrest : ∏ x ∈ Finset.univ.erase e, (w x) ^ (a' x : ℕ) =
              ∏ x ∈ Finset.univ.erase e, (w x) ^ (a x : ℕ) := by
            apply Finset.prod_congr rfl
            intro x hx
            have hne : x ≠ e := (Finset.mem_erase.mp hx).1
            simp [a', Function.update_of_ne hne]
          rw [hrest]
          have hae : (a' e : ℕ) = (a e : ℕ) + 1 := by simp [a']
          rw [hae, pow_succ]
          ring
        have hdist_lr : ‖pt (Sum.inl e.1.1, a) - pt (Sum.inr e.1.2, a')‖ = 1 := by
          simp only [pt, hW_step]
          have hfac : b (Sum.inl e.1.1) * rotProd w a - b (Sum.inr e.1.2) * (rotProd w a * w e) =
              rotProd w a * (b (Sum.inl e.1.1) - b (Sum.inr e.1.2) * w e) := by ring
          rw [hfac, norm_mul, norm_rotProd w hw_unit, one_mul, hw_dist e]
        have hdist_rl : ‖pt (Sum.inr e.1.2, a') - pt (Sum.inl e.1.1, a)‖ = 1 := by
          rw [norm_sub_rev]
          exact hdist_lr
        simp only [Finset.mem_coe, f, hlt, dite_true, pairs, Finset.mem_filter, Finset.mem_product]
        cases side
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
                  Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, hdist_lr⟩
        · simp only [↓reduceIte]
          exact ⟨⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
                  Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, hdist_rl⟩
      · intro ⟨s₁, ⟨e₁, a₁⟩⟩ hx₁ ⟨s₂, ⟨e₂, a₂⟩⟩ hx₂ heq
        have hlt₁ : (a₁ e₁ : ℕ) + 1 < q := by
          simp only [Finset.mem_coe, good, stepIdx, Finset.mem_product, Finset.mem_univ, true_and,
            Finset.mem_sigma, Finset.mem_filter] at hx₁
          exact hx₁
        have hlt₂ : (a₂ e₂ : ℕ) + 1 < q := by
          simp only [Finset.mem_coe, good, stepIdx, Finset.mem_product, Finset.mem_univ, true_and,
            Finset.mem_sigma, Finset.mem_filter] at hx₂
          exact hx₂
        simp only [f, hlt₁, hlt₂, dite_true] at heq
        cases s₁ <;> cases s₂
        · simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at heq
          have h1 := hpt_inj heq.1
          have h2 := hpt_inj heq.2
          have hl : e₁.1.1 = e₂.1.1 := Sum.inl.inj (Prod.mk.inj h1).1
          have hr : e₁.1.2 = e₂.1.2 := Sum.inr.inj (Prod.mk.inj h2).1
          have he : e₁ = e₂ := Subtype.ext (Prod.ext hl hr)
          have ha : a₁ = a₂ := (Prod.mk.inj h1).2
          subst he; subst ha; rfl
        · simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at heq
          have h1 := hpt_inj heq.1
          exact absurd (Prod.mk.inj h1).1 (by simp)
        · simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at heq
          have h1 := hpt_inj heq.1
          exact absurd (Prod.mk.inj h1).1 (by simp)
        · simp only [↓reduceIte, Prod.mk.injEq] at heq
          have h1 := hpt_inj heq.1
          have h2 := hpt_inj heq.2
          have hl : e₁.1.1 = e₂.1.1 := Sum.inl.inj (Prod.mk.inj h2).1
          have hr : e₁.1.2 = e₂.1.2 := Sum.inr.inj (Prod.mk.inj h1).1
          have he : e₁ = e₂ := Subtype.ext (Prod.ext hl hr)
          have ha : a₁ = a₂ := (Prod.mk.inj h2).2
          subst he; subst ha; rfl
    have hgood_card : q * good.card = 2 * E.card * (q - 1) * q ^ E.card := by
      have h1 : good.card = 2 * stepIdx.card := by
        simp [good, Finset.card_product]
      rw [h1]
      have h2 : q * stepIdx.card = E.card * (q - 1) * q ^ E.card := by
        simp only [stepIdx, Finset.card_sigma, Finset.mul_sum]
        have hterm : ∀ e : E,
            q * (Finset.univ.filter fun a : E → Fin q => (a e : ℕ) + 1 < q).card =
              (q - 1) * q ^ E.card := by
          intro e
          rw [card_filter_lt_sub_one (by omega) e, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_coe]
        simp_rw [hterm]
        simp [Finset.sum_const]
        ring
      calc q * (2 * stepIdx.card) = 2 * (q * stepIdx.card) := by ring
        _ = 2 * (E.card * (q - 1) * q ^ E.card) := by rw [h2]
        _ = 2 * E.card * (q - 1) * q ^ E.card := by ring
    calc q * pairs.card ≥ q * good.card := Nat.mul_le_mul_left q hcard_le
      _ = 2 * E.card * (q - 1) * q ^ E.card := hgood_card

/- ## Section 3: Lemma 3.1 (Middle levels graph and base-5 coding) -/

abbrev ML (d : ℕ) := {A : Finset (Fin (2 * d - 1)) // A.card = d - 1}
abbrev MR (d : ℕ) := {B : Finset (Fin (2 * d - 1)) // B.card = d}

def ME (d : ℕ) : Finset (ML d × MR d) :=
  Finset.univ.filter fun p => p.1.1 ⊆ p.2.1

lemma card_ML_eq_card_MR (d : ℕ) (hd : 1 ≤ d) :
    Fintype.card (ML d) = Fintype.card (MR d) := by
  refine Fintype.card_congr
    { toFun := fun A => ⟨A.1ᶜ, by
        rw [Finset.card_compl, Fintype.card_fin, A.2]
        omega⟩
      invFun := fun B => ⟨B.1ᶜ, by
        rw [Finset.card_compl, Fintype.card_fin, B.2]
        omega⟩
      left_inv := fun A => Subtype.ext (compl_compl A.1)
      right_inv := fun B => Subtype.ext (compl_compl B.1) }

lemma ML_nonempty (d : ℕ) (hd : 1 ≤ d) : Nonempty (ML d) := by
  let S : Finset (Fin (2 * d - 1)) := Finset.univ.filter fun i => (i : ℕ) < d - 1
  have hS : S.card = d - 1 := by
    have hbij : S.card = (Finset.range (d - 1)).card := by
      refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro i₁ _ i₂ _ h
        exact Fin.ext h
      · intro m hm
        have hmlt : m < d - 1 := Finset.mem_range.mp hm
        refine ⟨⟨m, by omega⟩, ?_, rfl⟩
        simp [S, hmlt]
    rw [hbij, Finset.card_range]
  exact ⟨⟨S, hS⟩⟩

lemma two_mul_card_ME (d : ℕ) (hd : 1 ≤ d) :
    2 * (ME d).card = d * Fintype.card (ML d ⊕ MR d) := by
  let rowA : ML d → Finset (ML d × MR d) := fun A =>
    (Finset.univ.filter fun B : MR d => A.1 ⊆ B.1).image (fun B => (A, B))
  have hcard : (ME d).card = d * Fintype.card (ML d) := by
    have hbi : ME d = Finset.univ.biUnion rowA := by
      ext ⟨A, B⟩
      simp only [ME, rowA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · intro hsub
        exact ⟨A, B, hsub, rfl⟩
      · rintro ⟨A', B', hsub, heq⟩
        rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        exact hsub
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (ML d)) : Set (ML d)) rowA := by
      intro A₁ _ A₂ _ hne
      change Disjoint (rowA A₁) (rowA A₂)
      rw [Finset.disjoint_left]
      intro ⟨x, y⟩ h1 h2
      rcases Finset.mem_image.mp h1 with ⟨_, _, h1eq⟩
      rcases Finset.mem_image.mp h2 with ⟨_, _, h2eq⟩
      exact hne ((Prod.mk.inj h1eq).1.trans (Prod.mk.inj h2eq).1.symm)
    rw [hbi, Finset.card_biUnion hdisj]
    have hrow : ∀ A : ML d, (rowA A).card = d := by
      intro A
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
      have hcompl_card : A.1ᶜ.card = d := by
        rw [Finset.card_compl, Fintype.card_fin, A.2]
        omega
      refine Eq.trans ?_ hcompl_card
      refine Finset.card_bij
        (fun (B : MR d) (hB : B ∈ Finset.univ.filter fun B : MR d => A.1 ⊆ B.1) =>
          (B.1 \ A.1).min' (by
            have hsub : A.1 ⊆ B.1 := (Finset.mem_filter.mp hB).2
            rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, B.2, A.2]
            omega))
        ?_ ?_ ?_
      · intro B hB
        have hsub : A.1 ⊆ B.1 := (Finset.mem_filter.mp hB).2
        have hmem := Finset.min'_mem (B.1 \ A.1) (by
          rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, B.2, A.2]
          omega)
        exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hmem).2
      · intro B₁ hB₁ B₂ hB₂ heq
        have hsub₁ : A.1 ⊆ B₁.1 := (Finset.mem_filter.mp hB₁).2
        have hsub₂ : A.1 ⊆ B₂.1 := (Finset.mem_filter.mp hB₂).2
        have hc₁ : (B₁.1 \ A.1).card = 1 := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub₁, B₁.2, A.2]; omega
        have hc₂ : (B₂.1 \ A.1).card = 1 := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub₂, B₂.2, A.2]; omega
        rcases Finset.card_eq_one.mp hc₁ with ⟨x₁, hx₁⟩
        rcases Finset.card_eq_one.mp hc₂ with ⟨x₂, hx₂⟩
        have hx : x₁ = x₂ := by
          have := heq
          simp only [hx₁, hx₂, Finset.min'_singleton] at this
          exact this
        apply Subtype.ext
        rw [← Finset.sdiff_union_of_subset hsub₁, ← Finset.sdiff_union_of_subset hsub₂,
            hx₁, hx₂, hx]
      · intro x hx
        have hxnot : x ∉ A.1 := Finset.mem_compl.mp hx
        let B : MR d := ⟨insert x A.1, by rw [Finset.card_insert_of_notMem hxnot, A.2]; omega⟩
        refine ⟨B, ?_, ?_⟩
        · simp [B, Finset.subset_insert]
        · have hsdiff : B.1 \ A.1 = {x} := by
            ext y
            simp only [B, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | hy, hyn⟩
              · rfl
              · exact absurd hy hyn
            · rintro rfl
              exact ⟨Or.inl rfl, hxnot⟩
          simp [hsdiff]
    simp_rw [hrow]
    simp [Finset.sum_const, mul_comm]
  rw [hcard, Fintype.card_sum, card_ML_eq_card_MR d hd]
  ring

def base5X {n : ℕ} (A : Finset (Fin n)) : ℝ :=
  ∑ j ∈ A, (5 : ℝ) ^ (j : ℕ)

def base5T {n : ℕ} (A : Finset (Fin n)) : ℝ :=
  1 + ∑ j ∈ A, (25 : ℝ) ^ (j : ℕ)

lemma base5T_ge_one {n : ℕ} (A : Finset (Fin n)) : 1 ≤ base5T A := by
  unfold base5T
  have h0 : 0 ≤ ∑ j ∈ A, (25 : ℝ) ^ (j : ℕ) := Finset.sum_nonneg fun _ _ => by positivity
  linarith

lemma geom_sum_five (h : ℕ) : 4 * (∑ j ∈ Finset.range h, (5 : ℝ) ^ j) = (5 : ℝ) ^ h - 1 := by
  induction h with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

lemma geom_sum_25 (h : ℕ) : 24 * (∑ j ∈ Finset.range h, (25 : ℝ) ^ j) = (25 : ℝ) ^ h - 1 := by
  induction h with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

lemma sum_sdiff_add_inter {α : Type*} [DecidableEq α] (U V : Finset α) (f : α → ℝ) :
    (∑ j ∈ U \ V, f j) + ∑ j ∈ U ∩ V, f j = ∑ j ∈ U, f j := by
  rw [← Finset.sum_union (Finset.disjoint_sdiff_inter U V), Finset.sdiff_union_inter]

lemma base5_bounds_of_ne {n : ℕ} {A B : Finset (Fin n)} (hne : A ≠ B) :
    base5X A ≠ base5X B ∧
    base5T A ≠ base5T B ∧
    |base5T B - base5T A| < (50 / 27 : ℝ) * (base5X B - base5X A) ^ 2 := by
  have hsd_ne : (symmDiff A B).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (symmDiff_eq_bot.mp h)
  let h : Fin n := (symmDiff A B).max' hsd_ne
  have hh_mem : h ∈ symmDiff A B := Finset.max'_mem _ hsd_ne
  have hh_max : ∀ j ∈ symmDiff A B, j ≤ h := fun j hj => Finset.le_max' _ j hj
  have hmain : ∀ (U V : Finset (Fin n)),
      h ∈ V \ U → (∀ j ∈ symmDiff U V, j ≤ h) →
      (3 / 4 : ℝ) * (5 : ℝ) ^ (h : ℕ) < base5X V - base5X U ∧
      0 < base5T V - base5T U ∧
      base5T V - base5T U < (25 / 24 : ℝ) * (25 : ℝ) ^ (h : ℕ) := by
    intro U V hhV hmax
    have hX_split : base5X V - base5X U =
        (∑ j ∈ V \ U, (5 : ℝ) ^ (j : ℕ)) - (∑ j ∈ U \ V, (5 : ℝ) ^ (j : ℕ)) := by
      unfold base5X
      have h1 := sum_sdiff_add_inter V U (fun j : Fin n => (5 : ℝ) ^ (j : ℕ))
      have h2 := sum_sdiff_add_inter U V (fun j : Fin n => (5 : ℝ) ^ (j : ℕ))
      rw [Finset.inter_comm V U] at h1
      linarith
    have hT_split : base5T V - base5T U =
        (∑ j ∈ V \ U, (25 : ℝ) ^ (j : ℕ)) - (∑ j ∈ U \ V, (25 : ℝ) ^ (j : ℕ)) := by
      unfold base5T
      have h1 := sum_sdiff_add_inter V U (fun j : Fin n => (25 : ℝ) ^ (j : ℕ))
      have h2 := sum_sdiff_add_inter U V (fun j : Fin n => (25 : ℝ) ^ (j : ℕ))
      rw [Finset.inter_comm V U] at h1
      linarith
    have hUV_lt : ∀ j ∈ U \ V, (j : ℕ) < (h : ℕ) := by
      intro j hj
      have hj_sd : j ∈ symmDiff U V := Finset.mem_symmDiff.mpr (Or.inl (Finset.mem_sdiff.mp hj))
      have hj_le : j ≤ h := hmax j hj_sd
      have hj_ne : j ≠ h := by
        intro heq
        subst heq
        exact (Finset.mem_sdiff.mp hhV).2 (Finset.mem_sdiff.mp hj).1
      exact Fin.lt_def.mp (lt_of_le_of_ne hj_le hj_ne)
    have hVU_erase_lt : ∀ j ∈ (V \ U).erase h, (j : ℕ) < (h : ℕ) := by
      intro j hj
      have hjne : j ≠ h := (Finset.mem_erase.mp hj).1
      have hjmem : j ∈ V \ U := (Finset.mem_erase.mp hj).2
      have hj_sd : j ∈ symmDiff U V := Finset.mem_symmDiff.mpr (Or.inr (Finset.mem_sdiff.mp hjmem))
      exact Fin.lt_def.mp (lt_of_le_of_ne (hmax j hj_sd) hjne)
    have hsum_le_range : ∀ (c : ℝ) (_ : 0 ≤ c) (S : Finset (Fin n)),
        (∀ j ∈ S, (j : ℕ) < (h : ℕ)) →
        ∑ j ∈ S, c ^ (j : ℕ) ≤ ∑ k ∈ Finset.range (h : ℕ), c ^ k := by
      intro c hc S hS
      have hmap : ∑ j ∈ S, c ^ (j : ℕ) = ∑ k ∈ S.image (fun j : Fin n => (j : ℕ)), c ^ k := by
        rw [Finset.sum_image]
        intro x _ y _ hxy
        exact Fin.ext hxy
      rw [hmap]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
        exact Finset.mem_range.mpr (hS j hj)
      · intro k _ _
        exact pow_nonneg hc k
    have h5_tail : ∑ j ∈ U \ V, (5 : ℝ) ^ (j : ℕ) ≤ ((5 : ℝ) ^ (h : ℕ) - 1) / 4 := by
      have hle := hsum_le_range 5 (by norm_num) (U \ V) hUV_lt
      have hg := geom_sum_five (h : ℕ)
      linarith
    have h25_tail_UV : ∑ j ∈ U \ V, (25 : ℝ) ^ (j : ℕ) ≤ ((25 : ℝ) ^ (h : ℕ) - 1) / 24 := by
      have hle := hsum_le_range 25 (by norm_num) (U \ V) hUV_lt
      have hg := geom_sum_25 (h : ℕ)
      linarith
    have h25_tail_VU : ∑ j ∈ (V \ U).erase h, (25 : ℝ) ^ (j : ℕ) ≤ ((25 : ℝ) ^ (h : ℕ) - 1) / 24 := by
      have hle := hsum_le_range 25 (by norm_num) ((V \ U).erase h) hVU_erase_lt
      have hg := geom_sum_25 (h : ℕ)
      linarith
    have h5_lower : (5 : ℝ) ^ (h : ℕ) ≤ ∑ j ∈ V \ U, (5 : ℝ) ^ (j : ℕ) :=
      Finset.single_le_sum (f := fun j : Fin n => (5 : ℝ) ^ (j : ℕ)) (fun _ _ => by positivity) hhV
    have h25_lower : (25 : ℝ) ^ (h : ℕ) ≤ ∑ j ∈ V \ U, (25 : ℝ) ^ (j : ℕ) :=
      Finset.single_le_sum (f := fun j : Fin n => (25 : ℝ) ^ (j : ℕ)) (fun _ _ => by positivity) hhV
    have h25_upper : ∑ j ∈ V \ U, (25 : ℝ) ^ (j : ℕ) ≤
        (25 : ℝ) ^ (h : ℕ) + ((25 : ℝ) ^ (h : ℕ) - 1) / 24 := by
      rw [← Finset.add_sum_erase _ _ hhV]
      linarith
    have h25_nonneg : 0 ≤ ∑ j ∈ U \ V, (25 : ℝ) ^ (j : ℕ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have h25_pos : (0 : ℝ) < (25 : ℝ) ^ (h : ℕ) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [hX_split]; linarith
    · rw [hT_split]; linarith
    · rw [hT_split]; linarith
  have h25_eq : (25 : ℝ) ^ (h : ℕ) = ((5 : ℝ) ^ (h : ℕ)) ^ 2 := by
    set m : ℕ := h.val
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rcases Finset.mem_symmDiff.mp hh_mem with hhA | hhB
  · have hsymm : symmDiff B A = symmDiff A B := symmDiff_comm B A
    have ⟨hX, hTpos, hTup⟩ :=
      hmain B A (Finset.mem_sdiff.mpr hhA) (fun j hj => hh_max j (hsymm ▸ hj))
    have h5pos : (0 : ℝ) < (5 : ℝ) ^ (h : ℕ) := by positivity
    refine ⟨by linarith, by linarith, ?_⟩
    have habs : |base5T B - base5T A| = base5T A - base5T B := by
      rw [abs_of_neg (by linarith)]; ring
    rw [habs]
    have hsq : ((3 / 4 : ℝ) * (5 : ℝ) ^ (h : ℕ)) ^ 2 < (base5X A - base5X B) ^ 2 := by nlinarith
    have hsq2 : (base5X B - base5X A) ^ 2 = (base5X A - base5X B) ^ 2 := by ring
    rw [hsq2]
    rw [h25_eq] at hTup
    nlinarith
  · have ⟨hX, hTpos, hTup⟩ := hmain A B (Finset.mem_sdiff.mpr hhB) hh_max
    have h5pos : (0 : ℝ) < (5 : ℝ) ^ (h : ℕ) := by positivity
    refine ⟨by linarith, by linarith, ?_⟩
    rw [abs_of_pos hTpos]
    have hsq : ((3 / 4 : ℝ) * (5 : ℝ) ^ (h : ℕ)) ^ 2 < (base5X B - base5X A) ^ 2 := by nlinarith
    rw [h25_eq] at hTup
    nlinarith

lemma edge_base5_diff {d : ℕ} (hd : 1 ≤ d) {A : ML d} {B : MR d} (hsub : A.1 ⊆ B.1) :
    0 < base5X B.1 - base5X A.1 ∧
    base5T B.1 - base5T A.1 = (base5X B.1 - base5X A.1) ^ 2 := by
  have hcard : (B.1 \ A.1).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, B.2, A.2]
    omega
  rcases Finset.card_eq_one.mp hcard with ⟨j, hj⟩
  have hB : B.1 = insert j A.1 := by
    rw [← Finset.sdiff_union_of_subset hsub, hj, Finset.singleton_union]
  have hjnot : j ∉ A.1 := by
    have : j ∈ B.1 \ A.1 := by rw [hj]; exact Finset.mem_singleton_self j
    exact (Finset.mem_sdiff.mp this).2
  have hX : base5X B.1 - base5X A.1 = (5 : ℝ) ^ (j : ℕ) := by
    unfold base5X
    rw [hB, Finset.sum_insert hjnot]
    ring
  have hT : base5T B.1 - base5T A.1 = (25 : ℝ) ^ (j : ℕ) := by
    unfold base5T
    rw [hB, Finset.sum_insert hjnot]
    ring
  rw [hX, hT]
  set m : ℕ := j.val
  refine ⟨by positivity, ?_⟩
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/- ## Section 4: Lemmas 3.2 & 3.3 (Seed points `a_i(ε)` and exact edge rotations `w_e(ε)`) -/

noncomputable def polyC (x t : ℝ) : ℝ := x ^ 2 + t / 2
noncomputable def polyD (x t : ℝ) : ℝ := -x ^ 2 + t / 2

def vFinset {d : ℕ} : ML d ⊕ MR d → Finset (Fin (2 * d - 1))
  | Sum.inl A => A.1
  | Sum.inr B => B.1

lemma vFinset_injective {d : ℕ} (hd : 1 ≤ d) : Function.Injective (vFinset (d := d)) := by
  intro i j h
  cases i with
  | inl A =>
    cases j with
    | inl A' => exact congrArg Sum.inl (Subtype.ext h)
    | inr B =>
      have hc : A.1.card = B.1.card := congrArg Finset.card h
      rw [A.2, B.2] at hc
      omega
  | inr B =>
    cases j with
    | inl A =>
      have hc : B.1.card = A.1.card := congrArg Finset.card h
      rw [A.2, B.2] at hc
      omega
    | inr B' => exact congrArg Sum.inr (Subtype.ext h)

noncomputable def seedPt {d : ℕ} (i : ML d ⊕ MR d) (ε : ℝ) : ℂ :=
  match i with
  | Sum.inl A =>
    let x := base5X A.1
    let t := base5T A.1
    ⟨ε * x, -1 / 2 + ε ^ 2 * polyC x t⟩
  | Sum.inr B =>
    let x := base5X B.1
    let t := base5T B.1
    ⟨-ε * x, 1 / 2 + ε ^ 2 * polyD x t⟩

lemma H_seedPt_inl {d : ℕ} (A A' : ML d) (ε : ℝ) :
    H (seedPt (Sum.inl A) ε) (seedPt (Sum.inl A') ε) =
      ε ^ 2 * (-(base5X A'.1 - base5X A.1) ^ 2 / 2 - (base5T A'.1 - base5T A.1) / 4) +
      ε ^ 4 * polyC (base5X A.1) (base5T A.1) *
        (polyC (base5X A'.1) (base5T A'.1) - polyC (base5X A.1) (base5T A.1)) := by
  simp only [H, seedPt, polyC]
  ring

lemma H_seedPt_inr {d : ℕ} (B B' : MR d) (ε : ℝ) :
    H (seedPt (Sum.inr B) ε) (seedPt (Sum.inr B') ε) =
      ε ^ 2 * (-(base5X B'.1 - base5X B.1) ^ 2 / 2 + (base5T B'.1 - base5T B.1) / 4) +
      ε ^ 4 * polyD (base5X B.1) (base5T B.1) *
        (polyD (base5X B'.1) (base5T B'.1) - polyD (base5X B.1) (base5T B.1)) := by
  simp only [H, seedPt, polyD]
  ring

lemma norm_sq_seedPt_inl {d : ℕ} (A : ML d) (ε : ℝ) :
    ‖seedPt (Sum.inl A) ε‖ ^ 2 =
      1 / 4 - 1 / 2 * ε ^ 2 * base5T A.1 + ε ^ 4 * (polyC (base5X A.1) (base5T A.1)) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [seedPt, polyC]
  ring

lemma norm_sq_seedPt_inr {d : ℕ} (B : MR d) (ε : ℝ) :
    ‖seedPt (Sum.inr B) ε‖ ^ 2 =
      1 / 4 + 1 / 2 * ε ^ 2 * base5T B.1 + ε ^ 4 * (polyD (base5X B.1) (base5T B.1)) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [seedPt, polyD]
  ring

lemma edge_dist_sq_seedPt {d : ℕ} (hd : 1 ≤ d) {A : ML d} {B : MR d} (hsub : A.1 ⊆ B.1) (ε : ℝ) :
    ‖seedPt (Sum.inr B) ε - seedPt (Sum.inl A) ε‖ ^ 2 =
      1 + ε ^ 4 * (polyD (base5X B.1) (base5T B.1) - polyC (base5X A.1) (base5T A.1)) ^ 2 := by
  have ⟨_, hT⟩ := edge_base5_diff hd hsub
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, seedPt, polyC, polyD]
  set x := base5X A.1
  set y := base5X B.1
  set t := base5T A.1
  set u := base5T B.1
  have hu : u = t + (y - x) ^ 2 := by linarith
  rw [hu]
  ring

noncomputable def edgeZ {d : ℕ} (e : ME d) (ε : ℝ) : ℂ :=
  star (seedPt (Sum.inl e.1.1) ε) * seedPt (Sum.inr e.1.2) ε

noncomputable def edgeTau {d : ℕ} (e : ME d) (ε : ℝ) : ℝ :=
  let x := base5X e.1.1.1
  let t := base5T e.1.1.1
  let y := base5X e.1.2.1
  let u := base5T e.1.2.1
  (x - y) / 2 + ε ^ 2 * (x * polyD y u + y * polyC x t)

noncomputable def edgeM {d : ℕ} (e : ME d) : ℝ :=
  polyD (base5X e.1.2.1) (base5T e.1.2.1) - polyC (base5X e.1.1.1) (base5T e.1.1.1)

noncomputable def edgeF {d : ℕ} (e : ME d) (ε : ℝ) : ℝ :=
  (edgeTau e ε) ^ 2 - ε ^ 2 * (edgeM e) ^ 2 * (edgeZ e ε).re - 1 / 4 * ε ^ 6 * (edgeM e) ^ 4

noncomputable def edgeW {d : ℕ} (e : ME d) (ε : ℝ) : ℂ :=
  (⟨(edgeZ e ε).re + 1 / 2 * ε ^ 4 * (edgeM e) ^ 2, -ε * √(edgeF e ε)⟩ : ℂ) / edgeZ e ε

lemma edgeZ_im {d : ℕ} (e : ME d) (ε : ℝ) : (edgeZ e ε).im = ε * edgeTau e ε := by
  simp only [edgeZ, edgeTau, seedPt, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

lemma edgeZ_re_tendsto {d : ℕ} (e : ME d) :
    Tendsto (fun ε => (edgeZ e ε).re) (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 4 : ℝ)) := by
  have hcont : Continuous (fun ε : ℝ => (edgeZ e ε).re) := by
    unfold edgeZ seedPt
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    fun_prop
  have h0 : (edgeZ e 0).re = -1 / 4 := by
    simp [edgeZ, seedPt]
    ring
  rw [← h0]
  exact (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

lemma edgeTau_tendsto {d : ℕ} (e : ME d) :
    Tendsto (fun ε => edgeTau e ε) (𝓝[>] (0 : ℝ)) (𝓝 ((base5X e.1.1.1 - base5X e.1.2.1) / 2)) := by
  have hcont : Continuous (fun ε : ℝ => edgeTau e ε) := by
    unfold edgeTau; fun_prop
  have h0 : edgeTau e 0 = (base5X e.1.1.1 - base5X e.1.2.1) / 2 := by
    simp [edgeTau]
  rw [← h0]
  exact (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

lemma edgeF_tendsto {d : ℕ} (e : ME d) :
    Tendsto (fun ε => edgeF e ε) (𝓝[>] (0 : ℝ))
      (𝓝 (((base5X e.1.1.1 - base5X e.1.2.1) / 2) ^ 2)) := by
  have hcont : Continuous (fun ε : ℝ => edgeF e ε) := by
    unfold edgeF edgeTau edgeZ seedPt
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    fun_prop
  have h0 : edgeF e 0 = ((base5X e.1.1.1 - base5X e.1.2.1) / 2) ^ 2 := by
    simp [edgeF, edgeTau]
  rw [← h0]
  exact (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

lemma edgeW_eventually {d : ℕ} (hd : 1 ≤ d) (e : ME d) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ‖edgeW e ε‖ = 1 ∧
      ‖seedPt (Sum.inl e.1.1) ε - seedPt (Sum.inr e.1.2) ε * edgeW e ε‖ = 1 ∧
      (star (seedPt (Sum.inl e.1.1) ε) * seedPt (Sum.inr e.1.2) ε * edgeW e ε).im < 0 := by
  have hsub : e.1.1.1 ⊆ e.1.2.1 := (Finset.mem_filter.mp e.2).2
  have hXpos : 0 < base5X e.1.2.1 - base5X e.1.1.1 := (edge_base5_diff hd hsub).1
  have hFlim : 0 < ((base5X e.1.1.1 - base5X e.1.2.1) / 2) ^ 2 := by nlinarith
  have hZneg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (edgeZ e ε).re < 0 :=
    (edgeZ_re_tendsto e).eventually (gt_mem_nhds (by norm_num))
  have hFpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < edgeF e ε :=
    (edgeF_tendsto e).eventually (lt_mem_nhds hFlim)
  have hεpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [hZneg, hFpos, hεpos] with ε hZneg hFpos hεpos
  have hZne : edgeZ e ε ≠ 0 := by
    intro h0
    rw [h0] at hZneg
    simp at hZneg
  set num : ℂ := ⟨(edgeZ e ε).re + 1 / 2 * ε ^ 4 * (edgeM e) ^ 2, -ε * √(edgeF e ε)⟩
  have hnum_norm_sq : ‖num‖ ^ 2 = ‖edgeZ e ε‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [num, edgeZ_im]
    have hsq : √(edgeF e ε) * √(edgeF e ε) = edgeF e ε := Real.mul_self_sqrt (le_of_lt hFpos)
    have h1 : (-ε * √(edgeF e ε)) * (-ε * √(edgeF e ε)) = ε ^ 2 * edgeF e ε := by
      calc (-ε * √(edgeF e ε)) * (-ε * √(edgeF e ε))
          = ε ^ 2 * (√(edgeF e ε) * √(edgeF e ε)) := by ring
        _ = ε ^ 2 * edgeF e ε := by rw [hsq]
    rw [h1]
    unfold edgeF
    ring
  have hw_norm : ‖edgeW e ε‖ = 1 := by
    change ‖num / edgeZ e ε‖ = 1
    rw [norm_div]
    have hnn : ‖num‖ = ‖edgeZ e ε‖ := by
      nlinarith [norm_nonneg num, norm_nonneg (edgeZ e ε)]
    rw [hnn, div_self (norm_ne_zero_iff.mpr hZne)]
  have hZw : edgeZ e ε * edgeW e ε = num := by
    change edgeZ e ε * (num / edgeZ e ε) = num
    exact mul_div_cancel₀ num hZne
  have hdist_sq : ‖seedPt (Sum.inl e.1.1) ε - seedPt (Sum.inr e.1.2) ε * edgeW e ε‖ ^ 2 = 1 := by
    have h1 : ∀ u v : ℂ, ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (star u * v).re := by
      intro u v
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
          Complex.normSq_apply, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re]
      ring
    rw [h1, norm_mul, hw_norm, mul_one]
    have h2 : star (seedPt (Sum.inl e.1.1) ε) * (seedPt (Sum.inr e.1.2) ε * edgeW e ε) =
        edgeZ e ε * edgeW e ε := by
      unfold edgeZ; ring
    rw [h2, hZw]
    have h3 := edge_dist_sq_seedPt hd hsub ε
    rw [norm_sub_rev, h1] at h3
    have hZre : (star (seedPt (Sum.inl e.1.1) ε) * seedPt (Sum.inr e.1.2) ε).re = (edgeZ e ε).re :=
      rfl
    rw [hZre] at h3
    change ‖seedPt (Sum.inl e.1.1) ε‖ ^ 2 + ‖seedPt (Sum.inr e.1.2) ε‖ ^ 2 -
        2 * ((edgeZ e ε).re + 1 / 2 * ε ^ 4 * (edgeM e) ^ 2) = 1
    unfold edgeM
    linarith
  have hdist : ‖seedPt (Sum.inl e.1.1) ε - seedPt (Sum.inr e.1.2) ε * edgeW e ε‖ = 1 := by
    nlinarith [norm_nonneg (seedPt (Sum.inl e.1.1) ε - seedPt (Sum.inr e.1.2) ε * edgeW e ε)]
  refine ⟨hw_norm, hdist, ?_⟩
  change (edgeZ e ε * edgeW e ε).im < 0
  rw [hZw]
  change -ε * √(edgeF e ε) < 0
  have hsqrt : 0 < √(edgeF e ε) := Real.sqrt_pos.mpr hFpos
  nlinarith

lemma edgeW_sub_one_div_sq_tendsto {d : ℕ} (hd : 1 ≤ d) (e : ME d) :
    Tendsto (fun ε => ‖edgeW e ε - 1‖ / ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsub : e.1.1.1 ⊆ e.1.2.1 := (Finset.mem_filter.mp e.2).2
  have hXpos : 0 < base5X e.1.2.1 - base5X e.1.1.1 := (edge_base5_diff hd hsub).1
  set L : ℝ := (base5X e.1.2.1 - base5X e.1.1.1) / 2
  have hLpos : 0 < L := by positivity
  have hTau : Tendsto (fun ε => edgeTau e ε) (𝓝[>] (0 : ℝ)) (𝓝 (-L)) := by
    have heq : (base5X e.1.1.1 - base5X e.1.2.1) / 2 = -L := by
      dsimp [L]; ring
    rw [← heq]
    exact edgeTau_tendsto e
  have hF : Tendsto (fun ε => edgeF e ε) (𝓝[>] (0 : ℝ)) (𝓝 (L ^ 2)) := by
    have heq : ((base5X e.1.1.1 - base5X e.1.2.1) / 2) ^ 2 = L ^ 2 := by
      dsimp [L]; ring
    rw [← heq]
    exact edgeF_tendsto e
  have hsqrtF : Tendsto (fun ε => √(edgeF e ε)) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have h1 := (Real.continuous_sqrt.tendsto (L ^ 2)).comp hF
    rw [Real.sqrt_sq (le_of_lt hLpos)] at h1
    exact h1
  have hdenom : Tendsto (fun ε => √(edgeF e ε) - edgeTau e ε) (𝓝[>] (0 : ℝ)) (𝓝 (2 * L)) := by
    have h1 := hsqrtF.sub hTau
    have h2 : L - (-L) = 2 * L := by ring
    rwa [h2] at h1
  have hZ : Tendsto (fun ε => edgeZ e ε) (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 4 : ℂ)) := by
    have hcont : Continuous (fun ε : ℝ => edgeZ e ε) := by
      unfold edgeZ seedPt
      apply Continuous.mul
      · exact continuous_star.comp (continuous_complex_mk (by fun_prop) (by fun_prop))
      · exact continuous_complex_mk (by fun_prop) (by fun_prop)
    have h0 : edgeZ e 0 = (-1 / 4 : ℂ) := by
      apply Complex.ext
      · simp [edgeZ, seedPt]; ring
      · simp [edgeZ, seedPt]
    rw [← h0]
    exact (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  let qf : ℝ → ℂ := fun ε =>
    (⟨1 / 2 * ε ^ 2 * (edgeM e) ^ 2,
      ε * (edgeM e ^ 2 * (edgeZ e ε).re + 1 / 4 * ε ^ 4 * edgeM e ^ 4) /
        (√(edgeF e ε) - edgeTau e ε)⟩ : ℂ) / edgeZ e ε
  have hqf_tendsto : Tendsto qf (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hre : Tendsto (fun ε : ℝ => 1 / 2 * ε ^ 2 * (edgeM e) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by ring)
    have hnum_im : Tendsto (fun ε : ℝ =>
        ε * (edgeM e ^ 2 * (edgeZ e ε).re + 1 / 4 * ε ^ 4 * edgeM e ^ 4))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_nhdsGT_zero_of_continuous continuous_id rfl
      have hfac : Tendsto (fun ε : ℝ =>
          edgeM e ^ 2 * (edgeZ e ε).re + 1 / 4 * ε ^ 4 * edgeM e ^ 4)
          (𝓝[>] (0 : ℝ)) (𝓝 (edgeM e ^ 2 * (-1 / 4) + 0)) := by
        apply Tendsto.add
        · exact tendsto_const_nhds.mul (edgeZ_re_tendsto e)
        · exact tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by ring)
      have hmul := hid.mul hfac
      rw [zero_mul] at hmul
      exact hmul
    have him : Tendsto (fun ε : ℝ =>
        ε * (edgeM e ^ 2 * (edgeZ e ε).re + 1 / 4 * ε ^ 4 * edgeM e ^ 4) /
          (√(edgeF e ε) - edgeTau e ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hdiv := hnum_im.div hdenom (by linarith)
      rw [zero_div] at hdiv
      exact hdiv
    have hmk : Tendsto (fun ε : ℝ =>
        (⟨1 / 2 * ε ^ 2 * (edgeM e) ^ 2,
          ε * (edgeM e ^ 2 * (edgeZ e ε).re + 1 / 4 * ε ^ 4 * edgeM e ^ 4) /
            (√(edgeF e ε) - edgeTau e ε)⟩ : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 : (0 : ℂ) = ⟨0, 0⟩ := rfl
      rw [h0]
      exact tendsto_complex_mk hre him
    have hZne0 : (-1 / 4 : ℂ) ≠ 0 := by norm_num
    have hdiv := hmk.div hZ hZne0
    rw [zero_div] at hdiv
    exact hdiv
  have hnorm_qf : Tendsto (fun ε => ‖qf ε‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (continuous_norm.tendsto (0 : ℂ)).comp hqf_tendsto
    rw [norm_zero] at h
    exact h
  apply hnorm_qf.congr'
  have hFpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < edgeF e ε :=
    hF.eventually (lt_mem_nhds (by positivity))
  have hdenpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < √(edgeF e ε) - edgeTau e ε :=
    hdenom.eventually (lt_mem_nhds (by linarith))
  have hZne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), edgeZ e ε ≠ 0 :=
    hZ.eventually (isOpen_ne.mem_nhds (by norm_num))
  have hεpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [hFpos, hdenpos, hZne, hεpos] with ε hFpos hdenpos hZne hεpos
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hsum_eq : √(edgeF e ε) + edgeTau e ε =
      (-ε ^ 2 * (edgeM e ^ 2 * (edgeZ e ε).re + 1 / 4 * ε ^ 4 * edgeM e ^ 4)) /
        (√(edgeF e ε) - edgeTau e ε) := by
    have hden_ne : √(edgeF e ε) - edgeTau e ε ≠ 0 := ne_of_gt hdenpos
    rw [eq_div_iff hden_ne]
    have hsq : √(edgeF e ε) ^ 2 = edgeF e ε := Real.sq_sqrt (le_of_lt hFpos)
    have hdiff : (√(edgeF e ε) + edgeTau e ε) * (√(edgeF e ε) - edgeTau e ε) =
        edgeF e ε - (edgeTau e ε) ^ 2 := by nlinarith [hsq]
    rw [hdiff]
    unfold edgeF
    ring
  have hW_eq : edgeW e ε - 1 = (ε ^ 2 : ℝ) * qf ε := by
    unfold edgeW qf
    have hsub1 : (⟨(edgeZ e ε).re + 1 / 2 * ε ^ 4 * (edgeM e) ^ 2, -ε * √(edgeF e ε)⟩ : ℂ) /
        edgeZ e ε - 1 =
      (⟨(edgeZ e ε).re + 1 / 2 * ε ^ 4 * (edgeM e) ^ 2, -ε * √(edgeF e ε)⟩ - edgeZ e ε) /
        edgeZ e ε := by
      field_simp [hZne]
    rw [hsub1, ← mul_div_assoc]
    congr 1
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, edgeZ_im]
      have h1 : -ε * √(edgeF e ε) - ε * edgeTau e ε = -ε * (√(edgeF e ε) + edgeTau e ε) := by
        ring
      rw [h1, hsum_eq]
      ring
  rw [hW_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hε2),
      mul_div_cancel_left₀ _ (ne_of_gt hε2)]

lemma exists_good_seed {d q : ℕ} (hd : 2 ≤ d) (_hq : 2 ≤ q) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ i : ML d ⊕ MR d, 0 < ‖seedPt i ε‖ ∧ ‖seedPt i ε‖ < 1) ∧
      (∀ i j : ML d ⊕ MR d, ‖seedPt i ε‖ = ‖seedPt j ε‖ → i = j) ∧
      (∀ e : ME d, ‖edgeW e ε‖ = 1 ∧
        ‖seedPt (Sum.inl e.1.1) ε - seedPt (Sum.inr e.1.2) ε * edgeW e ε‖ = 1 ∧
        (star (seedPt (Sum.inl e.1.1) ε) * seedPt (Sum.inr e.1.2) ε * edgeW e ε).im < 0) ∧
      (∀ i j : ML d ⊕ MR d, i ≠ j →
        H (seedPt i ε) (seedPt j ε) < -2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖edgeW e ε - 1‖)) := by
  have hd1 : 1 ≤ d := by omega
  -- 1. Moduli eventually in (0, 1)
  have hmod_in : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i : ML d ⊕ MR d, 0 < ‖seedPt i ε‖ ∧ ‖seedPt i ε‖ < 1 := by
    rw [eventually_all]
    intro i
    have hcont : Continuous (fun ε : ℝ => ‖seedPt i ε‖) := by
      cases i with
      | inl A =>
        unfold seedPt
        exact continuous_norm.comp (continuous_complex_mk (by fun_prop) (by fun_prop))
      | inr B =>
        unfold seedPt
        exact continuous_norm.comp (continuous_complex_mk (by fun_prop) (by fun_prop))
    have h0 : ‖seedPt i 0‖ = 1 / 2 := by
      cases i with
      | inl A =>
        rw [Complex.norm_def, Complex.normSq_apply]
        simp only [seedPt, zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero]
        norm_num
      | inr B =>
        rw [Complex.norm_def, Complex.normSq_apply]
        simp only [seedPt, neg_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero]
        norm_num
    have ht : Tendsto (fun ε : ℝ => ‖seedPt i ε‖) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by
      rw [← h0]
      exact (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  -- 2. Moduli eventually pairwise distinct
  have hmod_dist : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ i j : ML d ⊕ MR d, ‖seedPt i ε‖ = ‖seedPt j ε‖ → i = j := by
    have hne_all : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∀ p : (ML d ⊕ MR d) × (ML d ⊕ MR d), p.1 ≠ p.2 → ‖seedPt p.1 ε‖ ^ 2 ≠ ‖seedPt p.2 ε‖ ^ 2 := by
      rw [eventually_all]
      intro ⟨i, j⟩
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · have hvf_ne : vFinset i ≠ vFinset j := fun h => hij (vFinset_injective hd1 h)
        have hTne : base5T (vFinset i) ≠ base5T (vFinset j) := (base5_bounds_of_ne hvf_ne).2.1
        have hdiv : ∃ c : ℝ, c ≠ 0 ∧
            Tendsto (fun ε => (‖seedPt i ε‖ ^ 2 - ‖seedPt j ε‖ ^ 2) / ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
          cases i with
          | inl A =>
            cases j with
            | inl A' =>
              refine ⟨(base5T A'.1 - base5T A.1) / 2, by
                have : base5T A.1 ≠ base5T A'.1 := hTne
                intro h0; exact this (by linarith), ?_⟩
              have ht : Tendsto (fun ε : ℝ =>
                  (base5T A'.1 - base5T A.1) / 2 +
                    ε ^ 2 * (polyC (base5X A.1) (base5T A.1) ^ 2 -
                      polyC (base5X A'.1) (base5T A'.1) ^ 2))
                  (𝓝[>] (0 : ℝ)) (𝓝 ((base5T A'.1 - base5T A.1) / 2)) :=
                tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by ring)
              apply ht.congr'
              filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
              rw [norm_sq_seedPt_inl, norm_sq_seedPt_inl]
              field_simp [ne_of_gt hε]
              ring
            | inr B =>
              have h1 := base5T_ge_one A.1
              have h2 := base5T_ge_one B.1
              refine ⟨-(base5T A.1 + base5T B.1) / 2, by linarith, ?_⟩
              have ht : Tendsto (fun ε : ℝ =>
                  -(base5T A.1 + base5T B.1) / 2 +
                    ε ^ 2 * (polyC (base5X A.1) (base5T A.1) ^ 2 -
                      polyD (base5X B.1) (base5T B.1) ^ 2))
                  (𝓝[>] (0 : ℝ)) (𝓝 (-(base5T A.1 + base5T B.1) / 2)) :=
                tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by ring)
              apply ht.congr'
              filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
              rw [norm_sq_seedPt_inl, norm_sq_seedPt_inr]
              field_simp [ne_of_gt hε]
              ring
          | inr B =>
            cases j with
            | inl A =>
              have h1 := base5T_ge_one A.1
              have h2 := base5T_ge_one B.1
              refine ⟨(base5T B.1 + base5T A.1) / 2, by linarith, ?_⟩
              have ht : Tendsto (fun ε : ℝ =>
                  (base5T B.1 + base5T A.1) / 2 +
                    ε ^ 2 * (polyD (base5X B.1) (base5T B.1) ^ 2 -
                      polyC (base5X A.1) (base5T A.1) ^ 2))
                  (𝓝[>] (0 : ℝ)) (𝓝 ((base5T B.1 + base5T A.1) / 2)) :=
                tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by ring)
              apply ht.congr'
              filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
              rw [norm_sq_seedPt_inr, norm_sq_seedPt_inl]
              field_simp [ne_of_gt hε]
              ring
            | inr B' =>
              refine ⟨(base5T B.1 - base5T B'.1) / 2, by
                have : base5T B.1 ≠ base5T B'.1 := hTne
                intro h0; exact this (by linarith), ?_⟩
              have ht : Tendsto (fun ε : ℝ =>
                  (base5T B.1 - base5T B'.1) / 2 +
                    ε ^ 2 * (polyD (base5X B.1) (base5T B.1) ^ 2 -
                      polyD (base5X B'.1) (base5T B'.1) ^ 2))
                  (𝓝[>] (0 : ℝ)) (𝓝 ((base5T B.1 - base5T B'.1) / 2)) :=
                tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by ring)
              apply ht.congr'
              filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
              rw [norm_sq_seedPt_inr, norm_sq_seedPt_inr]
              field_simp [ne_of_gt hε]
              ring
        rcases hdiv with ⟨c, hcne, ht⟩
        have hne_ev := ht.eventually (isOpen_ne.mem_nhds hcne)
        filter_upwards [hne_ev, self_mem_nhdsWithin] with ε hneε _ _
        intro hsq
        rw [hsq, sub_self, zero_div] at hneε
        exact hneε rfl
    filter_upwards [hne_all] with ε hε i j hnorm
    by_contra hij
    exact hε (i, j) hij (by rw [hnorm])
  -- 3. Edge rotations eventually satisfy all properties
  have hedges : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ e : ME d,
      ‖edgeW e ε‖ = 1 ∧
      ‖seedPt (Sum.inl e.1.1) ε - seedPt (Sum.inr e.1.2) ε * edgeW e ε‖ = 1 ∧
      (star (seedPt (Sum.inl e.1.1) ε) * seedPt (Sum.inr e.1.2) ε * edgeW e ε).im < 0 := by
    rw [eventually_all]
    exact fun e => edgeW_eventually hd1 e
  -- 4. H(a_i, a_j) < -2 H_0 eventually
  have hH0_div : Tendsto
      (fun ε => (2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖edgeW e ε - 1‖)) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsum : Tendsto (fun ε => ∑ e : ME d, ‖edgeW e ε - 1‖ / ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.univ : Finset (ME d))
        (fun e _ => edgeW_sub_one_div_sq_tendsto hd1 e)
    have hmul : Tendsto (fun ε =>
        2 * ((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖edgeW e ε - 1‖ / ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := tendsto_const_nhds (x := 2 * ((q - 1 : ℕ) : ℝ)).mul hsum
      rw [mul_zero] at h
      exact h
    apply hmul.congr
    intro ε
    rw [← Finset.sum_div]
    ring
  have hH_gap : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j : ML d ⊕ MR d, i ≠ j →
      H (seedPt i ε) (seedPt j ε) < -2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖edgeW e ε - 1‖) := by
    have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p : (ML d ⊕ MR d) × (ML d ⊕ MR d), p.1 ≠ p.2 →
        H (seedPt p.1 ε) (seedPt p.2 ε) <
          -2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖edgeW e ε - 1‖) := by
      rw [eventually_all]
      intro ⟨i, j⟩
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · have hH_neg_order : ∃ c : ℝ, 0 < c ∧
            ∀ᶠ ε in 𝓝[>] (0 : ℝ), H (seedPt i ε) (seedPt j ε) / ε ^ 2 < -c := by
          cases i with
          | inl A =>
            cases j with
            | inl A' =>
              have hne : A.1 ≠ A'.1 := fun h => hij (congrArg Sum.inl (Subtype.ext h))
              have ⟨hXne, _, hTbound⟩ := base5_bounds_of_ne hne
              set coeff := -(base5X A'.1 - base5X A.1) ^ 2 / 2 - (base5T A'.1 - base5T A.1) / 4
              have hcoeff_neg : coeff < 0 := by
                have hXsq : 0 < (base5X A'.1 - base5X A.1) ^ 2 :=
                  sq_pos_of_ne_zero (sub_ne_zero.mpr hXne.symm)
                have h1 := (abs_lt.mp hTbound).1
                have h2 := (abs_lt.mp hTbound).2
                unfold coeff
                nlinarith
              refine ⟨-coeff / 2, by linarith, ?_⟩
              have ht : Tendsto (fun ε : ℝ =>
                  coeff + ε ^ 2 * polyC (base5X A.1) (base5T A.1) *
                    (polyC (base5X A'.1) (base5T A'.1) - polyC (base5X A.1) (base5T A.1)))
                  (𝓝[>] (0 : ℝ)) (𝓝 coeff) :=
                tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by ring)
              have hev := ht.eventually (gt_mem_nhds (by linarith : coeff < -(-coeff / 2)))
              filter_upwards [hev, self_mem_nhdsWithin] with ε hεlt (hε : 0 < ε)
              rw [H_seedPt_inl]
              have hdiv_eq :
                  (ε ^ 2 * coeff + ε ^ 4 * polyC (base5X A.1) (base5T A.1) *
                    (polyC (base5X A'.1) (base5T A'.1) - polyC (base5X A.1) (base5T A.1))) / ε ^ 2 =
                  coeff + ε ^ 2 * polyC (base5X A.1) (base5T A.1) *
                    (polyC (base5X A'.1) (base5T A'.1) - polyC (base5X A.1) (base5T A.1)) := by
                field_simp [ne_of_gt hε]
              simpa [coeff, hdiv_eq] using hεlt
            | inr B =>
              refine ⟨1, by norm_num, ?_⟩
              have hcont : Continuous (fun ε : ℝ => H (seedPt (Sum.inl A) ε) (seedPt (Sum.inr B) ε)) := by
                unfold H seedPt; dsimp only; fun_prop
              have h0 : H (seedPt (Sum.inl A) 0) (seedPt (Sum.inr B) 0) = -1 / 2 := by
                simp [H, seedPt]; ring
              have ht : Tendsto (fun ε : ℝ => H (seedPt (Sum.inl A) ε) (seedPt (Sum.inr B) ε))
                  (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 2)) := by
                rw [← h0]; exact (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
              have hev := ht.eventually (gt_mem_nhds (by norm_num : (-1 / 2 : ℝ) < -1 / 4))
              have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 / 2 :=
                Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num)) fun _ hx => hx.2
              filter_upwards [hev, hsmall, self_mem_nhdsWithin] with ε hlt hsm (hε : 0 < ε)
              rw [div_lt_iff₀ (by positivity)]
              nlinarith
          | inr B =>
            cases j with
            | inl A =>
              refine ⟨1, by norm_num, ?_⟩
              have hcont : Continuous (fun ε : ℝ => H (seedPt (Sum.inr B) ε) (seedPt (Sum.inl A) ε)) := by
                unfold H seedPt; dsimp only; fun_prop
              have h0 : H (seedPt (Sum.inr B) 0) (seedPt (Sum.inl A) 0) = -1 / 2 := by
                simp [H, seedPt]; ring
              have ht : Tendsto (fun ε : ℝ => H (seedPt (Sum.inr B) ε) (seedPt (Sum.inl A) ε))
                  (𝓝[>] (0 : ℝ)) (𝓝 (-1 / 2)) := by
                rw [← h0]; exact (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
              have hev := ht.eventually (gt_mem_nhds (by norm_num : (-1 / 2 : ℝ) < -1 / 4))
              have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 / 2 :=
                Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num)) fun _ hx => hx.2
              filter_upwards [hev, hsmall, self_mem_nhdsWithin] with ε hlt hsm (hε : 0 < ε)
              rw [div_lt_iff₀ (by positivity)]
              nlinarith
            | inr B' =>
              have hne : B.1 ≠ B'.1 := fun h => hij (congrArg Sum.inr (Subtype.ext h))
              have ⟨hXne, _, hTbound⟩ := base5_bounds_of_ne hne
              set coeff := -(base5X B'.1 - base5X B.1) ^ 2 / 2 + (base5T B'.1 - base5T B.1) / 4
              have hcoeff_neg : coeff < 0 := by
                have hXsq : 0 < (base5X B'.1 - base5X B.1) ^ 2 :=
                  sq_pos_of_ne_zero (sub_ne_zero.mpr hXne.symm)
                have h1 := (abs_lt.mp hTbound).1
                have h2 := (abs_lt.mp hTbound).2
                unfold coeff
                nlinarith
              refine ⟨-coeff / 2, by linarith, ?_⟩
              have ht : Tendsto (fun ε : ℝ =>
                  coeff + ε ^ 2 * polyD (base5X B.1) (base5T B.1) *
                    (polyD (base5X B'.1) (base5T B'.1) - polyD (base5X B.1) (base5T B.1)))
                  (𝓝[>] (0 : ℝ)) (𝓝 coeff) :=
                tendsto_nhdsGT_zero_of_continuous (by fun_prop) (by ring)
              have hev := ht.eventually (gt_mem_nhds (by linarith : coeff < -(-coeff / 2)))
              filter_upwards [hev, self_mem_nhdsWithin] with ε hεlt (hε : 0 < ε)
              rw [H_seedPt_inr]
              have hdiv_eq :
                  (ε ^ 2 * coeff + ε ^ 4 * polyD (base5X B.1) (base5T B.1) *
                    (polyD (base5X B'.1) (base5T B'.1) - polyD (base5X B.1) (base5T B.1))) / ε ^ 2 =
                  coeff + ε ^ 2 * polyD (base5X B.1) (base5T B.1) *
                    (polyD (base5X B'.1) (base5T B'.1) - polyD (base5X B.1) (base5T B.1)) := by
                field_simp [ne_of_gt hε]
              simpa [coeff, hdiv_eq] using hεlt
        rcases hH_neg_order with ⟨c, hcpos, hHlt⟩
        have hH0_small : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            (2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖edgeW e ε - 1‖)) / ε ^ 2 < c :=
          hH0_div.eventually (gt_mem_nhds hcpos)
        filter_upwards [hHlt, hH0_small, self_mem_nhdsWithin] with ε h1 h2 (hε : 0 < ε) _
        have hε2 : 0 < ε ^ 2 := by positivity
        have h1' : H (seedPt i ε) (seedPt j ε) < -c * ε ^ 2 := (div_lt_iff₀ hε2).mp h1
        have h2' : 2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖edgeW e ε - 1‖) < c * ε ^ 2 :=
          (div_lt_iff₀ hε2).mp h2
        linarith
    filter_upwards [hall] with ε hε i j hij
    exact hε (i, j) hij
  have hall_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧
      (∀ i : ML d ⊕ MR d, 0 < ‖seedPt i ε‖ ∧ ‖seedPt i ε‖ < 1) ∧
      (∀ i j : ML d ⊕ MR d, ‖seedPt i ε‖ = ‖seedPt j ε‖ → i = j) ∧
      (∀ e : ME d, ‖edgeW e ε‖ = 1 ∧
        ‖seedPt (Sum.inl e.1.1) ε - seedPt (Sum.inr e.1.2) ε * edgeW e ε‖ = 1 ∧
        (star (seedPt (Sum.inl e.1.1) ε) * seedPt (Sum.inr e.1.2) ε * edgeW e ε).im < 0) ∧
      (∀ i j : ML d ⊕ MR d, i ≠ j →
        H (seedPt i ε) (seedPt j ε) < -2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖edgeW e ε - 1‖)) := by
    filter_upwards [self_mem_nhdsWithin, hmod_in, hmod_dist, hedges, hH_gap] with
      ε h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  exact hall_ev.exists

/- ## Section 5: Lemma 3.4 (Radius perturbation via 2D finite differences and 1D MVT) -/

noncomputable def cosLaw (r s : ℝ) : ℝ := (r ^ 2 + s ^ 2 - 1) / (2 * r * s)

noncomputable def gammaAngle (r s : ℝ) : ℝ := Real.arccos (cosLaw r s)

def polyP (r s : ℝ) : ℝ := 4 * r ^ 2 * s ^ 2 - (r ^ 2 + s ^ 2 - 1) ^ 2

noncomputable def gammaDr (r s : ℝ) : ℝ := -(r ^ 2 - s ^ 2 + 1) / (r * √(polyP r s))

lemma polyP_eq_mul_one_sub_sq {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    polyP r s = (2 * r * s) ^ 2 * (1 - cosLaw r s ^ 2) := by
  unfold polyP cosLaw
  have hne : 2 * r * s ≠ 0 := by positivity
  field_simp [hne]
  ring

lemma polyP_pos {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h1 : -1 < cosLaw r s) (h2 : cosLaw r s < 1) : 0 < polyP r s := by
  rw [polyP_eq_mul_one_sub_sq hr hs]
  have hsq : 0 < 1 - cosLaw r s ^ 2 := by nlinarith
  positivity

lemma hasDerivAt_gammaAngle_r {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h1 : -1 < cosLaw r s) (h2 : cosLaw r s < 1) :
    HasDerivAt (fun x => gammaAngle x s) (gammaDr r s) r := by
  have hcr : HasDerivAt (fun x => cosLaw x s) ((r ^ 2 - s ^ 2 + 1) / (2 * r ^ 2 * s)) r := by
    have hnum : HasDerivAt (fun x : ℝ => x ^ 2 + s ^ 2 - 1) (2 * r) r := by
      have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
        simpa using hasDerivAt_pow 2 r
      exact (hsq.add_const (s ^ 2)).sub_const 1
    have hden : HasDerivAt (fun x : ℝ => 2 * x * s) (2 * s) r := by
      have hid := ((hasDerivAt_id r).const_mul (2 : ℝ)).mul_const s
      refine hid.congr_deriv ?_
      ring
    have hq := hnum.div hden (by positivity : 2 * r * s ≠ 0)
    refine hq.congr_deriv ?_
    field_simp [ne_of_gt hr, ne_of_gt hs]
    ring
  have harc : HasDerivAt Real.arccos (-(1 / √(1 - cosLaw r s ^ 2))) (cosLaw r s) :=
    Real.hasDerivAt_arccos (ne_of_gt h1) (ne_of_lt h2)
  have hcomp : HasDerivAt (Real.arccos ∘ fun x => cosLaw x s)
      (-(1 / √(1 - cosLaw r s ^ 2)) * ((r ^ 2 - s ^ 2 + 1) / (2 * r ^ 2 * s))) r :=
    HasDerivAt.comp r harc hcr
  change HasDerivAt (Real.arccos ∘ fun x => cosLaw x s) (gammaDr r s) r
  refine hcomp.congr_deriv ?_
  have hsqrt : √(polyP r s) = 2 * r * s * √(1 - cosLaw r s ^ 2) := by
    rw [polyP_eq_mul_one_sub_sq hr hs, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)]
  have h1c : 0 < √(1 - cosLaw r s ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  unfold gammaDr
  rw [hsqrt]
  field_simp [ne_of_gt hr, ne_of_gt hs, ne_of_gt h1c]

lemma hasDerivAt_gammaDr_s {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h1 : -1 < cosLaw r s) (h2 : cosLaw r s < 1) :
    HasDerivAt (fun y => gammaDr r y) (8 * r * s / (polyP r s * √(polyP r s))) s := by
  have hPpos : 0 < polyP r s := polyP_pos hr hs h1 h2
  have hsqrt_pos : 0 < √(polyP r s) := Real.sqrt_pos.mpr hPpos
  have hP' : HasDerivAt (fun y => polyP r y) (4 * s * (r ^ 2 - s ^ 2 + 1)) s := by
    have h1' : HasDerivAt (fun y : ℝ => 4 * r ^ 2 * y ^ 2) (4 * r ^ 2 * (2 * s)) s := by
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
      exact hsq.const_mul (4 * r ^ 2)
    have h2inner : HasDerivAt (fun y : ℝ => r ^ 2 + y ^ 2 - 1) (2 * s) s := by
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
      exact (hsq.const_add (r ^ 2)).sub_const 1
    have h2' : HasDerivAt (fun y : ℝ => (r ^ 2 + y ^ 2 - 1) ^ 2)
        (2 * (r ^ 2 + s ^ 2 - 1) * (2 * s)) s := by
      have hpow : HasDerivAt (fun u : ℝ => u ^ 2) (2 * (r ^ 2 + s ^ 2 - 1)) (r ^ 2 + s ^ 2 - 1) := by
        simpa using hasDerivAt_pow 2 (r ^ 2 + s ^ 2 - 1)
      exact hpow.comp s h2inner
    exact (h1'.sub h2').congr_deriv (by ring)
  have hsqrt' : HasDerivAt (fun y => √(polyP r y))
      (4 * s * (r ^ 2 - s ^ 2 + 1) / (2 * √(polyP r s))) s :=
    hP'.sqrt (ne_of_gt hPpos)
  have hnum' : HasDerivAt (fun y : ℝ => -(r ^ 2 - y ^ 2 + 1)) (2 * s) s := by
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    have hfun : (fun y : ℝ => -(r ^ 2 - y ^ 2 + 1)) = fun y : ℝ => y ^ 2 - r ^ 2 - 1 := by
      funext y; ring
    rw [hfun]
    exact (hsq.sub_const (r ^ 2)).sub_const 1
  have hden' : HasDerivAt (fun y => r * √(polyP r y))
      (r * (4 * s * (r ^ 2 - s ^ 2 + 1) / (2 * √(polyP r s)))) s :=
    hsqrt'.const_mul r
  have hq : HasDerivAt (fun y => -(r ^ 2 - y ^ 2 + 1) / (r * √(polyP r y)))
      ((2 * s * (r * √(polyP r s)) -
          (-(r ^ 2 - s ^ 2 + 1)) * (r * (4 * s * (r ^ 2 - s ^ 2 + 1) / (2 * √(polyP r s))))) /
        (r * √(polyP r s)) ^ 2) s :=
    hnum'.div hden' (by positivity : r * √(polyP r s) ≠ 0)
  refine hq.congr_deriv ?_
  have hsq2 : √(polyP r s) ^ 2 = polyP r s := Real.sq_sqrt (le_of_lt hPpos)
  field_simp [ne_of_gt hr, ne_of_gt hsqrt_pos, ne_of_gt hPpos]
  have hmul : √(polyP r s) * √(polyP r s) = polyP r s := Real.mul_self_sqrt (le_of_lt hPpos)
  nlinarith [hsq2, hmul, show polyP r s = 4 * r ^ 2 * s ^ 2 - (r ^ 2 + s ^ 2 - 1) ^ 2 from rfl]

lemma rect_diff_gamma_ne_zero {r₁ r₂ s₁ s₂ : ℝ} (hr : r₁ < r₂) (hs : s₁ < s₂)
    (hdom : ∀ r ∈ Set.Icc r₁ r₂, ∀ s ∈ Set.Icc s₁ s₂,
      0 < r ∧ 0 < s ∧ -1 < cosLaw r s ∧ cosLaw r s < 1) :
    gammaAngle r₂ s₂ - gammaAngle r₂ s₁ - gammaAngle r₁ s₂ + gammaAngle r₁ s₁ ≠ 0 := by
  intro hzero
  let h : ℝ → ℝ := fun r => gammaAngle r s₂ - gammaAngle r s₁
  let h' : ℝ → ℝ := fun r => gammaDr r s₂ - gammaDr r s₁
  have hh_deriv : ∀ r ∈ Set.Icc r₁ r₂, HasDerivAt h (h' r) r := by
    intro r hr_mem
    have d2 := hdom r hr_mem s₂ (Set.right_mem_Icc.mpr (le_of_lt hs))
    have d1 := hdom r hr_mem s₁ (Set.left_mem_Icc.mpr (le_of_lt hs))
    exact (hasDerivAt_gammaAngle_r d2.1 d2.2.1 d2.2.2.1 d2.2.2.2).sub
      (hasDerivAt_gammaAngle_r d1.1 d1.2.1 d1.2.2.1 d1.2.2.2)
  have hh_cont : ContinuousOn h (Set.Icc r₁ r₂) :=
    fun r hr_mem => (hh_deriv r hr_mem).continuousAt.continuousWithinAt
  obtain ⟨rStar, hrStar_mem, hrStar_eq⟩ := exists_hasDerivAt_eq_slope h h' hr hh_cont
    (fun r hr_mem => hh_deriv r (Set.Ioo_subset_Icc_self hr_mem))
  have hh_diff : h r₂ - h r₁ = 0 := by
    simp only [h]; linarith
  rw [hh_diff, zero_div] at hrStar_eq
  have hrStar_Icc : rStar ∈ Set.Icc r₁ r₂ := Set.Ioo_subset_Icc_self hrStar_mem
  let g : ℝ → ℝ := fun y => gammaDr rStar y
  let g' : ℝ → ℝ := fun y => 8 * rStar * y / (polyP rStar y * √(polyP rStar y))
  have hg_deriv : ∀ y ∈ Set.Icc s₁ s₂, HasDerivAt g (g' y) y := by
    intro y hy_mem
    have dy := hdom rStar hrStar_Icc y hy_mem
    exact hasDerivAt_gammaDr_s dy.1 dy.2.1 dy.2.2.1 dy.2.2.2
  have hg_cont : ContinuousOn g (Set.Icc s₁ s₂) :=
    fun y hy_mem => (hg_deriv y hy_mem).continuousAt.continuousWithinAt
  obtain ⟨sStar, hsStar_mem, hsStar_eq⟩ := exists_hasDerivAt_eq_slope g g' hs hg_cont
    (fun y hy_mem => hg_deriv y (Set.Ioo_subset_Icc_self hy_mem))
  have hg_diff : g s₂ - g s₁ = 0 := hrStar_eq
  rw [hg_diff, zero_div] at hsStar_eq
  have dStar := hdom rStar hrStar_Icc sStar (Set.Ioo_subset_Icc_self hsStar_mem)
  have hPpos : 0 < polyP rStar sStar := polyP_pos dStar.1 dStar.2.1 dStar.2.2.1 dStar.2.2.2
  have hsqrt_pos : 0 < √(polyP rStar sStar) := Real.sqrt_pos.mpr hPpos
  have hg'_pos : 0 < g' sStar := by
    unfold g'
    have hr_pos : 0 < rStar := dStar.1
    have hs_pos : 0 < sStar := dStar.2.1
    positivity
  linarith

lemma continuousOn_eq_of_int_two_pi {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hint : ∀ x ∈ Set.Icc a b, ∃ k : ℤ, f x = (k : ℝ) * (2 * Real.pi)) :
    f a = f b := by
  by_contra hne
  rcases hint a (Set.left_mem_Icc.mpr hab) with ⟨k₁, hk₁⟩
  rcases hint b (Set.right_mem_Icc.mpr hab) with ⟨k₂, hk₂⟩
  have hpi : 0 < 2 * Real.pi := by positivity
  have hk_ne : k₁ ≠ k₂ := by
    intro h
    apply hne
    rw [hk₁, hk₂, h]
  rcases lt_or_gt_of_ne hk_ne with hlt | hgt
  · let mid : ℝ := ((k₁ : ℝ) + 1 / 2) * (2 * Real.pi)
    have hmid_mem : mid ∈ Set.Icc (f a) (f b) := by
      rw [hk₁, hk₂]
      have hk12 : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hlt
      dsimp [mid]
      constructor <;> nlinarith
    obtain ⟨x, hx_mem, hfx⟩ := intermediate_value_Icc hab hcont hmid_mem
    rcases hint x hx_mem with ⟨k, hk⟩
    have heq : (k : ℝ) = (k₁ : ℝ) + 1 / 2 := by
      have : (k : ℝ) * (2 * Real.pi) = ((k₁ : ℝ) + 1 / 2) * (2 * Real.pi) := by
        rw [← hk, hfx]
      exact mul_right_cancel₀ (ne_of_gt hpi) this
    rcases le_or_gt k k₁ with hle | hgt'
    · have : (k : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast hle
      linarith
    · have : (k₁ : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hgt'
      linarith
  · let mid : ℝ := ((k₂ : ℝ) + 1 / 2) * (2 * Real.pi)
    have hmid_mem : mid ∈ Set.Icc (f b) (f a) := by
      rw [hk₁, hk₂]
      have hk21 : (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hgt
      dsimp [mid]
      constructor <;> nlinarith
    obtain ⟨x, hx_mem, hfx⟩ := intermediate_value_Icc' hab hcont hmid_mem
    rcases hint x hx_mem with ⟨k, hk⟩
    have heq : (k : ℝ) = (k₂ : ℝ) + 1 / 2 := by
      have : (k : ℝ) * (2 * Real.pi) = ((k₂ : ℝ) + 1 / 2) * (2 * Real.pi) := by
        rw [← hk, hfx]
      exact mul_right_cancel₀ (ne_of_gt hpi) this
    rcases le_or_gt k k₂ with hle | hgt'
    · have : (k : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast hle
      linarith
    · have : (k₂ : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hgt'
      linarith

noncomputable def wOfRadii {L R : Type*} (E : Finset (L × R)) (θ : E → ℝ)
    (ρ : L ⊕ R → ℝ) (e : E) : ℂ :=
  Complex.exp (((θ e - gammaAngle (ρ (Sum.inl e.1.1)) (ρ (Sum.inr e.1.2))) : ℝ) * Complex.I)

lemma norm_wOfRadii {L R : Type*} (E : Finset (L × R)) (θ : E → ℝ)
    (ρ : L ⊕ R → ℝ) (e : E) : ‖wOfRadii E θ ρ e‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma continuousAt_wOfRadii {L R : Type*} [Fintype L] [Fintype R]
    (E : Finset (L × R)) (θ : E → ℝ) {ρ : L ⊕ R → ℝ}
    (hpos : ∀ v, 0 < ρ v) (e : E) :
    ContinuousAt (fun ρ' => wOfRadii E θ ρ' e) ρ := by
  unfold wOfRadii gammaAngle cosLaw
  have hL : ContinuousAt (fun ρ' : L ⊕ R → ℝ => ρ' (Sum.inl e.1.1)) ρ :=
    (continuous_apply (Sum.inl e.1.1)).continuousAt
  have hR : ContinuousAt (fun ρ' : L ⊕ R → ℝ => ρ' (Sum.inr e.1.2)) ρ :=
    (continuous_apply (Sum.inr e.1.2)).continuousAt
  have hnum : ContinuousAt (fun ρ' : L ⊕ R → ℝ =>
      ρ' (Sum.inl e.1.1) ^ 2 + ρ' (Sum.inr e.1.2) ^ 2 - 1) ρ :=
    ((hL.pow 2).add (hR.pow 2)).sub continuousAt_const
  have hden : ContinuousAt (fun ρ' : L ⊕ R → ℝ =>
      2 * ρ' (Sum.inl e.1.1) * ρ' (Sum.inr e.1.2)) ρ :=
    (continuousAt_const.mul hL).mul hR
  have hden_ne : 2 * ρ (Sum.inl e.1.1) * ρ (Sum.inr e.1.2) ≠ 0 := by
    have h1 := hpos (Sum.inl e.1.1)
    have h2 := hpos (Sum.inr e.1.2)
    positivity
  have hcos : ContinuousAt (fun ρ' : L ⊕ R → ℝ =>
      (ρ' (Sum.inl e.1.1) ^ 2 + ρ' (Sum.inr e.1.2) ^ 2 - 1) /
        (2 * ρ' (Sum.inl e.1.1) * ρ' (Sum.inr e.1.2))) ρ :=
    hnum.div hden hden_ne
  have hgam : ContinuousAt (fun ρ' : L ⊕ R → ℝ =>
      Real.arccos ((ρ' (Sum.inl e.1.1) ^ 2 + ρ' (Sum.inr e.1.2) ^ 2 - 1) /
        (2 * ρ' (Sum.inl e.1.1) * ρ' (Sum.inr e.1.2)))) ρ :=
    Real.continuous_arccos.continuousAt.comp hcos
  have hdiff : ContinuousAt (fun ρ' : L ⊕ R → ℝ =>
      θ e - Real.arccos ((ρ' (Sum.inl e.1.1) ^ 2 + ρ' (Sum.inr e.1.2) ^ 2 - 1) /
        (2 * ρ' (Sum.inl e.1.1) * ρ' (Sum.inr e.1.2)))) ρ :=
    continuousAt_const.sub hgam
  exact Complex.continuous_exp.continuousAt.comp
    ((Complex.continuous_ofReal.continuousAt.comp hdiff).mul continuousAt_const)

set_option maxHeartbeats 400000 in
lemma lemma_3_4_step {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R)) {q : ℕ} (θ : E → ℝ)
    (U : Set (L ⊕ R → ℝ))
    (hU_dom : ∀ ρ ∈ U, (∀ v, 0 < ρ v) ∧
      ∀ e : E, -1 < cosLaw (ρ (Sum.inl e.1.1)) (ρ (Sum.inr e.1.2)) ∧
               cosLaw (ρ (Sum.inl e.1.1)) (ρ (Sum.inr e.1.2)) < 1)
    (a b : E → Fin q) (hab : a ≠ b)
    (W : Set (L ⊕ R → ℝ)) (hW_open : IsOpen W) (hW_ne : W.Nonempty) (hW_sub : W ⊆ U) :
    let bad := {ρ : L ⊕ R → ℝ | rotProd (wOfRadii E θ ρ) a = rotProd (wOfRadii E θ ρ) b}
    IsOpen (W \ bad) ∧ (W \ bad).Nonempty ∧ (W \ bad) ⊆ U := by
  classical
  dsimp only
  let bad : Set (L ⊕ R → ℝ) := {ρ | rotProd (wOfRadii E θ ρ) a = rotProd (wOfRadii E θ ρ) b}
  have hcont_rot : ∀ (c : E → Fin q) (ρ : L ⊕ R → ℝ), ρ ∈ U →
      ContinuousAt (fun ρ' => rotProd (wOfRadii E θ ρ') c) ρ := by
    intro c ρ hρ
    unfold rotProd
    exact continuousAt_prod_finset Finset.univ
      (fun e ρ' => (wOfRadii E θ ρ' e) ^ (c e : ℕ)) ρ
      (fun e _ => (continuousAt_wOfRadii E θ (hU_dom ρ hρ).1 e).pow (c e : ℕ))
  have hopen : IsOpen (W \ bad) := by
    rw [isOpen_iff_mem_nhds]
    intro ρ hρ
    have hρW : ρ ∈ W := hρ.1
    have hρne : rotProd (wOfRadii E θ ρ) a ≠ rotProd (wOfRadii E θ ρ) b := hρ.2
    have h1 := hcont_rot a ρ (hW_sub hρW)
    have h2 := hcont_rot b ρ (hW_sub hρW)
    have hne_ev : ∀ᶠ ρ' in 𝓝 ρ,
        rotProd (wOfRadii E θ ρ') a ≠ rotProd (wOfRadii E θ ρ') b := by
      have hsub_ne : rotProd (wOfRadii E θ ρ) a - rotProd (wOfRadii E θ ρ) b ≠ 0 :=
        sub_ne_zero.mpr hρne
      have hev := (h1.sub h2).eventually (isOpen_ne.mem_nhds hsub_ne)
      filter_upwards [hev] with ρ' h'
      exact sub_ne_zero.mp h'
    have hW_ev : ∀ᶠ ρ' in 𝓝 ρ, ρ' ∈ W := hW_open.mem_nhds hρW
    filter_upwards [hW_ev, hne_ev] with ρ' h1' h2'
    exact ⟨h1', h2'⟩
  have hne : (W \ bad).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hempty
    rcases hW_ne with ⟨ρ₀, hρ₀W⟩
    rcases Metric.isOpen_iff.mp hW_open ρ₀ hρ₀W with ⟨δ, hδpos, hball⟩
    have hex_e : ∃ e₀ : E, a e₀ ≠ b e₀ := by
      by_contra hall
      push Not at hall
      exact hab (funext hall)
    rcases hex_e with ⟨e₀, he₀⟩
    let u₀ : L ⊕ R := Sum.inl e₀.1.1
    let v₀ : L ⊕ R := Sum.inr e₀.1.2
    have huv_ne : u₀ ≠ v₀ := by simp [u₀, v₀]
    let r₁ : ℝ := ρ₀ u₀
    let r₂ : ℝ := ρ₀ u₀ + δ / 2
    let s₁ : ℝ := ρ₀ v₀
    let s₂ : ℝ := ρ₀ v₀ + δ / 2
    have hr : r₁ < r₂ := by dsimp [r₁, r₂]; linarith
    have hs : s₁ < s₂ := by dsimp [s₁, s₂]; linarith
    let upd : ℝ → ℝ → (L ⊕ R → ℝ) := fun r s =>
      Function.update (Function.update ρ₀ u₀ r) v₀ s
    have hupd_mem : ∀ r ∈ Set.Icc r₁ r₂, ∀ s ∈ Set.Icc s₁ s₂, upd r s ∈ W := by
      intro r hr_mem s hs_mem
      apply hball
      rw [Metric.mem_ball, dist_pi_lt_iff hδpos]
      intro x
      by_cases hxv : x = v₀
      · subst hxv
        simp only [upd, Function.update_self, Real.dist_eq]
        rw [abs_of_nonneg (by linarith [hs_mem.1])]
        dsimp [s₁, s₂] at hs_mem
        linarith [hs_mem.2]
      · by_cases hxu : x = u₀
        · subst hxu
          simp only [upd, Function.update_of_ne hxv, Function.update_self, Real.dist_eq]
          rw [abs_of_nonneg (by linarith [hr_mem.1])]
          dsimp [r₁, r₂] at hr_mem
          linarith [hr_mem.2]
        · simp [upd, Function.update_of_ne hxv, Function.update_of_ne hxu, hδpos]
    let Φ : (L ⊕ R → ℝ) → ℝ := fun ρ =>
      ∑ e : E, ((a e : ℝ) - (b e : ℝ)) *
        (θ e - gammaAngle (ρ (Sum.inl e.1.1)) (ρ (Sum.inr e.1.2)))
    have hΦ_int : ∀ ρ ∈ W, ∃ k : ℤ, Φ ρ = (k : ℝ) * (2 * Real.pi) := by
      intro ρ hρW
      have hbad : rotProd (wOfRadii E θ ρ) a = rotProd (wOfRadii E θ ρ) b := hempty hρW
      have hexp_eq : Complex.exp (Complex.ofReal (Φ ρ) * Complex.I) =
          rotProd (wOfRadii E θ ρ) a * (rotProd (wOfRadii E θ ρ) b)⁻¹ := by
        have hsum_cast : Complex.ofReal (Φ ρ) * Complex.I =
            ∑ e : E, ((a e : ℕ) : ℂ) *
              (((θ e - gammaAngle (ρ (Sum.inl e.1.1)) (ρ (Sum.inr e.1.2))) : ℝ) * Complex.I) -
            ∑ e : E, ((b e : ℕ) : ℂ) *
              (((θ e - gammaAngle (ρ (Sum.inl e.1.1)) (ρ (Sum.inr e.1.2))) : ℝ) * Complex.I) := by
          unfold Φ
          rw [Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro e _
          push_cast
          ring
        rw [hsum_cast, Complex.exp_sub, Complex.exp_sum, Complex.exp_sum, div_eq_mul_inv]
        congr 1
        · unfold rotProd wOfRadii
          apply Finset.prod_congr rfl
          intro e _
          rw [← Complex.exp_nat_mul]
        · congr 1
          unfold rotProd wOfRadii
          apply Finset.prod_congr rfl
          intro e _
          rw [← Complex.exp_nat_mul]
      have hne0 : rotProd (wOfRadii E θ ρ) b ≠ 0 := by
        rw [← norm_ne_zero_iff, norm_rotProd _ (norm_wOfRadii E θ ρ)]
        norm_num
      have hexp1 : Complex.exp (Complex.ofReal (Φ ρ) * Complex.I) = 1 := by
        rw [hexp_eq, hbad, mul_inv_cancel₀ hne0]
      rcases Complex.exp_eq_one_iff.mp hexp1 with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h1 : Complex.ofReal (Φ ρ) * Complex.I =
          Complex.ofReal ((k : ℝ) * (2 * Real.pi)) * Complex.I := by
        rw [hk]
        simp only [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_ofNat]
        ring
      exact Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h1)
    have hΦ_cont_r : ∀ s ∈ Set.Icc s₁ s₂, ContinuousOn (fun r => Φ (upd r s)) (Set.Icc r₁ r₂) := by
      intro s hs_mem r hr_mem
      have hρ_pos : ∀ v, 0 < upd r s v := (hU_dom (upd r s) (hW_sub (hupd_mem r hr_mem s hs_mem))).1
      have hterm : ∀ e ∈ (Finset.univ : Finset E),
          ContinuousAt (fun r' : ℝ => ((a e : ℝ) - (b e : ℝ)) *
            (θ e - gammaAngle (upd r' s (Sum.inl e.1.1)) (upd r' s (Sum.inr e.1.2)))) r := by
        intro e _
        have hL_cont : ContinuousAt (fun r' : ℝ => upd r' s (Sum.inl e.1.1)) r := by
          by_cases hlu : (Sum.inl e.1.1 : L ⊕ R) = u₀
          · have hfun : (fun r' : ℝ => upd r' s (Sum.inl e.1.1)) = fun r' : ℝ => r' := by
              funext r'; rw [hlu]; simp [upd]
            rw [hfun]; exact continuousAt_id
          · have hfun : (fun r' : ℝ => upd r' s (Sum.inl e.1.1)) =
                fun _ : ℝ => ρ₀ (Sum.inl e.1.1) := by
              funext r'; simp [upd, Function.update_of_ne hlu]
            rw [hfun]; exact continuousAt_const
        have hR_cont : ContinuousAt (fun r' : ℝ => upd r' s (Sum.inr e.1.2)) r := by
          by_cases hrv : (Sum.inr e.1.2 : L ⊕ R) = v₀
          · have hfun : (fun r' : ℝ => upd r' s (Sum.inr e.1.2)) = fun _ : ℝ => s := by
              funext r'; rw [hrv]; simp [upd]
            rw [hfun]; exact continuousAt_const
          · have hfun : (fun r' : ℝ => upd r' s (Sum.inr e.1.2)) =
                fun _ : ℝ => ρ₀ (Sum.inr e.1.2) := by
              funext r'; simp [upd, Function.update_of_ne hrv]
            rw [hfun]; exact continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.sub continuousAt_const
        unfold gammaAngle cosLaw
        have hnum : ContinuousAt (fun r' : ℝ =>
            upd r' s (Sum.inl e.1.1) ^ 2 + upd r' s (Sum.inr e.1.2) ^ 2 - 1) r :=
          ((hL_cont.pow 2).add (hR_cont.pow 2)).sub continuousAt_const
        have hden : ContinuousAt (fun r' : ℝ =>
            2 * upd r' s (Sum.inl e.1.1) * upd r' s (Sum.inr e.1.2)) r :=
          (continuousAt_const.mul hL_cont).mul hR_cont
        have hden_ne : 2 * upd r s (Sum.inl e.1.1) * upd r s (Sum.inr e.1.2) ≠ 0 := by
          have h1 := hρ_pos (Sum.inl e.1.1)
          have h2 := hρ_pos (Sum.inr e.1.2)
          positivity
        exact Real.continuous_arccos.continuousAt.comp (hnum.div hden hden_ne)
      exact (continuousAt_sum_finset Finset.univ
        (fun e r' => ((a e : ℝ) - (b e : ℝ)) *
          (θ e - gammaAngle (upd r' s (Sum.inl e.1.1)) (upd r' s (Sum.inr e.1.2))))
        r hterm).continuousWithinAt
    have hconst_s₂ : Φ (upd r₁ s₂) = Φ (upd r₂ s₂) :=
      continuousOn_eq_of_int_two_pi (le_of_lt hr)
        (hΦ_cont_r s₂ (Set.right_mem_Icc.mpr (le_of_lt hs)))
        (fun r hr_mem => hΦ_int _ (hupd_mem r hr_mem s₂ (Set.right_mem_Icc.mpr (le_of_lt hs))))
    have hconst_s₁ : Φ (upd r₁ s₁) = Φ (upd r₂ s₁) :=
      continuousOn_eq_of_int_two_pi (le_of_lt hr)
        (hΦ_cont_r s₁ (Set.left_mem_Icc.mpr (le_of_lt hs)))
        (fun r hr_mem => hΦ_int _ (hupd_mem r hr_mem s₁ (Set.left_mem_Icc.mpr (le_of_lt hs))))
    have hrect_zero :
        Φ (upd r₂ s₂) - Φ (upd r₂ s₁) - Φ (upd r₁ s₂) + Φ (upd r₁ s₁) = 0 := by
      linarith
    have hrect_eq :
        Φ (upd r₂ s₂) - Φ (upd r₂ s₁) - Φ (upd r₁ s₂) + Φ (upd r₁ s₁) =
          -((a e₀ : ℝ) - (b e₀ : ℝ)) *
            (gammaAngle r₂ s₂ - gammaAngle r₂ s₁ - gammaAngle r₁ s₂ + gammaAngle r₁ s₁) := by
      unfold Φ
      have hcomb : ∀ (f₁ f₂ f₃ f₄ : E → ℝ),
          (∑ e : E, f₁ e) - (∑ e : E, f₂ e) - (∑ e : E, f₃ e) + (∑ e : E, f₄ e) =
            ∑ e : E, (f₁ e - f₂ e - f₃ e + f₄ e) := by
        intro f₁ f₂ f₃ f₄
        simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      rw [hcomb, Finset.sum_eq_single e₀]
      · have hu : ∀ r s, upd r s (Sum.inl e₀.1.1) = r := by
          intro r s
          change upd r s u₀ = r
          simp [upd]
        have hv : ∀ r s, upd r s (Sum.inr e₀.1.2) = s := by
          intro r s
          change upd r s v₀ = s
          simp [upd]
        simp only [hu, hv]
        ring
      · intro e _ hne
        by_cases hl : e.1.1 = e₀.1.1
        · have hr_ne : e.1.2 ≠ e₀.1.2 := by
            intro h
            exact hne (Subtype.ext (Prod.ext hl h))
          have hv_ne : Sum.inr e.1.2 ≠ v₀ := by simp [v₀, hr_ne]
          have hRconst : ∀ r s, upd r s (Sum.inr e.1.2) = ρ₀ (Sum.inr e.1.2) := by
            intro r s
            simp [upd, Function.update_of_ne hv_ne]
          have hLdep : ∀ r s, upd r s (Sum.inl e.1.1) = r := by
            intro r s
            have hle : (Sum.inl e.1.1 : L ⊕ R) = u₀ := by simp [u₀, hl]
            rw [hle]
            simp [upd]
          simp only [hRconst, hLdep]
          ring
        · have hu_ne : Sum.inl e.1.1 ≠ u₀ := by simp [u₀, hl]
          have hLconst : ∀ r s, upd r s (Sum.inl e.1.1) = ρ₀ (Sum.inl e.1.1) := by
            intro r s
            simp [upd, Function.update_of_ne hu_ne]
          have hRindep : ∀ r₁' r₂' s, upd r₁' s (Sum.inr e.1.2) = upd r₂' s (Sum.inr e.1.2) := by
            intro r₁' r₂' s
            by_cases hrv : (Sum.inr e.1.2 : L ⊕ R) = v₀
            · rw [hrv]; simp [upd]
            · simp [upd, Function.update_of_ne hrv]
          rw [hLconst, hLconst, hLconst, hLconst,
              hRindep r₂ r₁ s₂, hRindep r₂ r₁ s₁]
          ring
      · intro hmem; exact absurd (Finset.mem_univ e₀) hmem
    rw [hrect_eq] at hrect_zero
    have hlam_ne : -((a e₀ : ℝ) - (b e₀ : ℝ)) ≠ 0 := by
      intro h0
      have hnat : (a e₀ : ℕ) = (b e₀ : ℕ) := by
        have : ((a e₀ : ℕ) : ℝ) = ((b e₀ : ℕ) : ℝ) := by linarith
        exact_mod_cast this
      exact he₀ (Fin.ext hnat)
    have hgam_zero :
        gammaAngle r₂ s₂ - gammaAngle r₂ s₁ - gammaAngle r₁ s₂ + gammaAngle r₁ s₁ = 0 :=
      (mul_eq_zero.mp hrect_zero).resolve_left hlam_ne
    apply rect_diff_gamma_ne_zero hr hs _ hgam_zero
    intro r hr_mem s hs_mem
    have hdom' := hU_dom (upd r s) (hW_sub (hupd_mem r hr_mem s hs_mem))
    have hu : upd r s (Sum.inl e₀.1.1) = r := by
      change upd r s u₀ = r
      simp [upd]
    have hv : upd r s (Sum.inr e₀.1.2) = s := by
      change upd r s v₀ = s
      simp [upd]
    have h1 := hdom'.1 (Sum.inl e₀.1.1)
    have h2 := hdom'.1 (Sum.inr e₀.1.2)
    have h3 := hdom'.2 e₀
    rw [hu] at h1 h3
    rw [hv] at h2 h3
    exact ⟨h1, h2, h3.1, h3.2⟩
  exact ⟨hopen, hne, Set.sdiff_subset.trans hW_sub⟩

lemma lemma_3_4 {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R)) {q : ℕ} (_hq : 2 ≤ q) (θ : E → ℝ)
    (U : Set (L ⊕ R → ℝ)) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_dom : ∀ ρ ∈ U, (∀ v, 0 < ρ v) ∧
      ∀ e : E, -1 < cosLaw (ρ (Sum.inl e.1.1)) (ρ (Sum.inr e.1.2)) ∧
               cosLaw (ρ (Sum.inl e.1.1)) (ρ (Sum.inr e.1.2)) < 1) :
    ∃ ρ ∈ U, Function.Injective (rotProd (wOfRadii E θ ρ) : (E → Fin q) → ℂ) := by
  classical
  let bad : (E → Fin q) × (E → Fin q) → Set (L ⊕ R → ℝ) := fun ab =>
    {ρ | rotProd (wOfRadii E θ ρ) ab.1 = rotProd (wOfRadii E θ ρ) ab.2}
  have hind : ∀ S : Finset ((E → Fin q) × (E → Fin q)),
      (∀ ab ∈ S, ab.1 ≠ ab.2) →
      ∃ W : Set (L ⊕ R → ℝ), IsOpen W ∧ W.Nonempty ∧ W ⊆ U ∧
        ∀ ab ∈ S, ∀ ρ ∈ W, ρ ∉ bad ab := by
    intro S
    induction S using Finset.induction with
    | empty =>
      intro _
      exact ⟨U, hU_open, hU_ne, Set.Subset.rfl, fun _ h => absurd h (Finset.notMem_empty _)⟩
    | insert ab T hab ih =>
      intro hne_all
      rcases ih (fun p hp => hne_all p (Finset.mem_insert_of_mem hp)) with
        ⟨W, hW_open, hW_ne, hW_sub, hW_avoid⟩
      rcases lemma_3_4_step E θ U hU_dom ab.1 ab.2
        (hne_all ab (Finset.mem_insert_self ab T)) W hW_open hW_ne hW_sub with
        ⟨hopen', hne', hsub'⟩
      refine ⟨W \ bad ab, hopen', hne', hsub', ?_⟩
      intro p hp ρ hρ
      rcases Finset.mem_insert.mp hp with rfl | hpT
      · exact hρ.2
      · exact hW_avoid p hpT ρ hρ.1
  let allPairs : Finset ((E → Fin q) × (E → Fin q)) :=
    Finset.univ.filter fun ab => ab.1 ≠ ab.2
  rcases hind allPairs (fun _ h => (Finset.mem_filter.mp h).2) with
    ⟨W, _, ⟨ρ, hρW⟩, hW_sub, hW_avoid⟩
  refine ⟨ρ, hW_sub hρW, ?_⟩
  intro a b hab
  by_contra hne
  exact hW_avoid (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩) ρ hρW hab

/- ## Section 6: Lemma 4.1 (Core peeling) and main construction -/

lemma exists_core_min_degree (k q : ℕ) (hq : 1 ≤ q) :
    ∀ (n : ℕ) (P : Finset ℂ), P.card = n → P.Nonempty →
      (2 * k * q + 1) * P.card ≤ q * ∑ p ∈ P, (P.filter fun p' => ‖p - p'‖ = 1).card →
      ∃ Q ⊆ P, Q.Nonempty ∧ ∀ p ∈ Q, k ≤ (Q.filter fun p' => ‖p - p'‖ = 1).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hPcard hPne hsum
    by_cases hgood : ∀ p ∈ P, k ≤ (P.filter fun p' => ‖p - p'‖ = 1).card
    · exact ⟨P, Finset.Subset.rfl, hPne, hgood⟩
    · push Not at hgood
      rcases hgood with ⟨v, hvP, hvdeg⟩
      let P' : Finset ℂ := P.erase v
      have hP'card : P'.card + 1 = P.card := by
        rw [Finset.card_erase_of_mem hvP]
        have hpos : 0 < P.card := Finset.card_pos.mpr hPne
        omega
      have hdeg_step : ∀ p ∈ P',
          (P.filter fun p' => ‖p - p'‖ = 1).card ≤
            (P'.filter fun p' => ‖p - p'‖ = 1).card + (if ‖p - v‖ = 1 then 1 else 0) := by
        intro p _
        have hsub : P.filter (fun p' => ‖p - p'‖ = 1) ⊆
            insert v (P'.filter fun p' => ‖p - p'‖ = 1) := by
          intro x hx
          rcases Finset.mem_filter.mp hx with ⟨hxP, hxd⟩
          by_cases hxv : x = v
          · simp [hxv]
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hxP⟩, hxd⟩)
        by_cases hdv : ‖p - v‖ = 1
        · rw [if_pos hdv]
          calc (P.filter fun p' => ‖p - p'‖ = 1).card
              ≤ (insert v (P'.filter fun p' => ‖p - p'‖ = 1)).card := Finset.card_le_card hsub
            _ ≤ (P'.filter fun p' => ‖p - p'‖ = 1).card + 1 := Finset.card_insert_le _ _
        · rw [if_neg hdv, add_zero]
          apply Finset.card_le_card
          intro x hx
          rcases Finset.mem_filter.mp hx with ⟨hxP, hxd⟩
          have hxv : x ≠ v := by
            intro h; subst h; exact hdv hxd
          exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hxP⟩, hxd⟩
      have hsum_drop :
          ∑ p ∈ P, (P.filter fun p' => ‖p - p'‖ = 1).card ≤
            2 * (P.filter fun p' => ‖v - p'‖ = 1).card +
              ∑ p ∈ P', (P'.filter fun p' => ‖p - p'‖ = 1).card := by
        have hsplit : (P.filter fun p' => ‖v - p'‖ = 1).card +
            ∑ p ∈ P', (P.filter fun p' => ‖p - p'‖ = 1).card =
            ∑ p ∈ P, (P.filter fun p' => ‖p - p'‖ = 1).card :=
          Finset.add_sum_erase P (fun p => (P.filter fun p' => ‖p - p'‖ = 1).card) hvP
        have h1 : ∑ p ∈ P', (P.filter fun p' => ‖p - p'‖ = 1).card ≤
            (∑ p ∈ P', (P'.filter fun p' => ‖p - p'‖ = 1).card) +
              ∑ p ∈ P', (if ‖p - v‖ = 1 then 1 else 0) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum hdeg_step
        have h2 : ∑ p ∈ P', (if ‖p - v‖ = 1 then 1 else 0) =
            (P.filter fun p' => ‖v - p'‖ = 1).card := by
          rw [Finset.sum_boole]
          simp only [Nat.cast_id]
          congr 1
          ext p
          simp only [P', Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨⟨_, hpP⟩, hdist⟩
            exact ⟨hpP, by rwa [norm_sub_rev]⟩
          · rintro ⟨hpP, hdist⟩
            have hpv : p ≠ v := by
              intro h; subst h; simp at hdist
            exact ⟨⟨hpv, hpP⟩, by rwa [norm_sub_rev]⟩
        omega
      have hsum' : (2 * k * q + 1) * P'.card + 1 ≤
          q * ∑ p ∈ P', (P'.filter fun p' => ‖p - p'‖ = 1).card := by
        have hmul : q * ∑ p ∈ P, (P.filter fun p' => ‖p - p'‖ = 1).card ≤
            2 * q * (P.filter fun p' => ‖v - p'‖ = 1).card +
              q * ∑ p ∈ P', (P'.filter fun p' => ‖p - p'‖ = 1).card := by
          have := Nat.mul_le_mul_left q hsum_drop
          linarith
        have hdeg_le : 2 * q * (P.filter fun p' => ‖v - p'‖ = 1).card ≤ 2 * k * q := by
          have hkv : (P.filter fun p' => ‖v - p'‖ = 1).card ≤ k := le_of_lt hvdeg
          nlinarith
        rw [← hP'card] at hsum
        nlinarith
      have hP'ne : P'.Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        rw [hempty] at hsum'
        simp at hsum'
      have hlt : P'.card < n := by omega
      rcases ih P'.card hlt P' rfl hP'ne (by omega) with ⟨Q, hQP', hQne, hQdeg⟩
      exact ⟨Q, hQP'.trans (Finset.erase_subset v P), hQne, hQdeg⟩

lemma exists_convex_k_unit_dist (k : ℕ) :
    ∃ A : Finset ℝ², A.Nonempty ∧ ConvexIndep (A : Set ℝ²) ∧
      Erdos97.HasNUnitDistanceProperty k A := by
  by_cases hk : k = 0
  · subst hk
    refine ⟨{0}, Finset.singleton_nonempty 0, ?_, ?_⟩
    · intro a ha
      have ha0 : a = 0 := Finset.mem_singleton.mp (Finset.mem_coe.mp ha)
      subst ha0
      simp
    · intro p _
      exact Nat.zero_le _
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
    set d : ℕ := 2 * k + 1
    set q : ℕ := 2 * k + 2
    have hd2 : 2 ≤ d := by omega
    have hq2 : 2 ≤ q := by omega
    have hd1 : 1 ≤ d := by omega
    rcases exists_good_seed (d := d) (q := q) hd2 hq2 with
      ⟨ε₀, hε₀, hnorm_in, hnorm_inj, hedges, hH_gap⟩
    let a : ML d ⊕ MR d → ℂ := fun i => seedPt i ε₀
    let w₀ : ME d → ℂ := fun e => edgeW e ε₀
    let ρ₀ : ML d ⊕ MR d → ℝ := fun i => ‖a i‖
    let α : ML d ⊕ MR d → ℂ := fun i => a i / (ρ₀ i : ℂ)
    have hρ₀_pos : ∀ i, 0 < ρ₀ i := fun i => (hnorm_in i).1
    have hρ₀_lt : ∀ i, ρ₀ i < 1 := fun i => (hnorm_in i).2
    have hα_norm : ∀ i, ‖α i‖ = 1 := by
      intro i
      unfold α
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (hρ₀_pos i))]
      exact div_self (ne_of_gt (hρ₀_pos i))
    have ha_eq : ∀ i, (ρ₀ i : ℂ) * α i = a i := by
      intro i
      unfold α
      have hne : (ρ₀ i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hρ₀_pos i))
      exact mul_div_cancel₀ (a i) hne
    let θ : ME d → ℝ := fun e => Complex.arg (α (Sum.inl e.1.1) / α (Sum.inr e.1.2))
    have hθ_exp : ∀ e : ME d,
        Complex.exp ((θ e : ℝ) * Complex.I) = α (Sum.inl e.1.1) / α (Sum.inr e.1.2) := by
      intro e
      have hu_norm : ‖α (Sum.inl e.1.1) / α (Sum.inr e.1.2)‖ = 1 := by
        rw [norm_div, hα_norm, hα_norm, div_one]
      have h := Complex.norm_mul_exp_arg_mul_I (α (Sum.inl e.1.1) / α (Sum.inr e.1.2))
      rw [hu_norm, Complex.ofReal_one, one_mul] at h
      exact h
    have hcos_and_w : ∀ e : ME d,
        -1 < cosLaw (ρ₀ (Sum.inl e.1.1)) (ρ₀ (Sum.inr e.1.2)) ∧
        cosLaw (ρ₀ (Sum.inl e.1.1)) (ρ₀ (Sum.inr e.1.2)) < 1 ∧
        w₀ e = wOfRadii (ME d) θ ρ₀ e := by
      intro e
      set rA := ρ₀ (Sum.inl e.1.1)
      set rB := ρ₀ (Sum.inr e.1.2)
      have hrA : 0 < rA := hρ₀_pos (Sum.inl e.1.1)
      have hrB : 0 < rB := hρ₀_pos (Sum.inr e.1.2)
      set z : ℂ := star (a (Sum.inl e.1.1)) * a (Sum.inr e.1.2) * w₀ e
      have hw₀_norm : ‖w₀ e‖ = 1 := (hedges e).1
      have hnorm_z : ‖z‖ = rA * rB := by
        dsimp only [z]
        rw [norm_mul, norm_mul, norm_star, hw₀_norm, mul_one]
      have hdist1 : ‖a (Sum.inl e.1.1) - a (Sum.inr e.1.2) * w₀ e‖ = 1 := (hedges e).2.1
      have hz_re : z.re = rA * rB * cosLaw rA rB := by
        have h1 : ‖a (Sum.inl e.1.1) - a (Sum.inr e.1.2) * w₀ e‖ ^ 2 =
            ‖a (Sum.inl e.1.1)‖ ^ 2 + ‖a (Sum.inr e.1.2) * w₀ e‖ ^ 2 -
              2 * (star (a (Sum.inl e.1.1)) * (a (Sum.inr e.1.2) * w₀ e)).re := by
          rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
              Complex.normSq_apply, Complex.normSq_apply]
          simp [Complex.sub_re, Complex.sub_im, Complex.mul_re]
          ring
        rw [hdist1, one_pow, norm_mul, hw₀_norm, mul_one] at h1
        have h2 : star (a (Sum.inl e.1.1)) * (a (Sum.inr e.1.2) * w₀ e) = z := by
          unfold z; ring
        rw [h2] at h1
        unfold cosLaw
        have hne : 2 * rA * rB ≠ 0 := by positivity
        field_simp [hne]
        have hrA_eq : ‖a (Sum.inl e.1.1)‖ = rA := rfl
        have hrB_eq : ‖a (Sum.inr e.1.2)‖ = rB := rfl
        rw [hrA_eq, hrB_eq] at h1
        linarith
      have hz_im_neg : z.im < 0 := (hedges e).2.2
      have hz_sq : z.re ^ 2 + z.im ^ 2 = (rA * rB) ^ 2 := by
        have h := Complex.sq_norm z
        rw [hnorm_z, Complex.normSq_apply] at h
        nlinarith
      have hcos_sq_lt : cosLaw rA rB ^ 2 < 1 := by
        have him_pos : 0 < z.im ^ 2 := sq_pos_of_neg hz_im_neg
        have hrab_pos : 0 < (rA * rB) ^ 2 := by positivity
        rw [hz_re] at hz_sq
        nlinarith
      have hcos_gt : -1 < cosLaw rA rB := by nlinarith
      have hcos_lt : cosLaw rA rB < 1 := by nlinarith
      have hz_im : z.im = -(rA * rB * Real.sin (gammaAngle rA rB)) := by
        unfold gammaAngle
        rw [Real.sin_arccos]
        have hsq : (z.im) ^ 2 = (rA * rB * √(1 - cosLaw rA rB ^ 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by nlinarith : 0 ≤ 1 - cosLaw rA rB ^ 2)]
          rw [hz_re] at hz_sq
          nlinarith
        have hnonneg : 0 ≤ rA * rB * √(1 - cosLaw rA rB ^ 2) := by positivity
        nlinarith
      have hz_exp : z = ((rA * rB : ℝ) : ℂ) * Complex.exp ((-(gammaAngle rA rB) : ℝ) * Complex.I) := by
        apply Complex.ext
        · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            Complex.exp_ofReal_mul_I_re, Real.cos_neg]
          rw [hz_re, gammaAngle, Real.cos_arccos (le_of_lt hcos_gt) (le_of_lt hcos_lt)]
        · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
            Complex.exp_ofReal_mul_I_im, Real.sin_neg]
          rw [hz_im]; ring
      have hw_eq : w₀ e = wOfRadii (ME d) θ ρ₀ e := by
        have hαA_ne : α (Sum.inl e.1.1) ≠ 0 := by
          rw [← norm_ne_zero_iff, hα_norm]; norm_num
        have hαB_ne : α (Sum.inr e.1.2) ≠ 0 := by
          rw [← norm_ne_zero_iff, hα_norm]; norm_num
        have hstar_αA : star (α (Sum.inl e.1.1)) = (α (Sum.inl e.1.1))⁻¹ := by
          have h := Complex.mul_conj (α (Sum.inl e.1.1))
          rw [Complex.normSq_eq_norm_sq, hα_norm, one_pow, Complex.ofReal_one] at h
          have h1 : α (Sum.inl e.1.1) * star (α (Sum.inl e.1.1)) = 1 := h
          exact eq_inv_of_mul_eq_one_right h1
        have hz_fac : z = ((rA * rB : ℝ) : ℂ) *
            ((α (Sum.inl e.1.1))⁻¹ * α (Sum.inr e.1.2) * w₀ e) := by
          unfold z
          rw [← ha_eq (Sum.inl e.1.1), ← ha_eq (Sum.inr e.1.2), star_mul, Complex.star_def,
              Complex.conj_ofReal, ← Complex.star_def, hstar_αA]
          push_cast
          ring
        have hrab_ne : ((rA * rB : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
        have hcancel : (α (Sum.inl e.1.1))⁻¹ * α (Sum.inr e.1.2) * w₀ e =
            Complex.exp ((-(gammaAngle rA rB) : ℝ) * Complex.I) :=
          mul_left_cancel₀ hrab_ne (hz_fac.symm.trans hz_exp)
        have hsolve : w₀ e = (α (Sum.inl e.1.1) / α (Sum.inr e.1.2)) *
            Complex.exp ((-(gammaAngle rA rB) : ℝ) * Complex.I) := by
          rw [← hcancel]
          field_simp [hαA_ne, hαB_ne]
        rw [hsolve, ← hθ_exp e, ← Complex.exp_add]
        unfold wOfRadii
        congr 1
        push_cast
        ring
      exact ⟨hcos_gt, hcos_lt, hw_eq⟩
    let bOf : (ML d ⊕ MR d → ℝ) → (ML d ⊕ MR d → ℂ) := fun ρ i => (ρ i : ℂ) * α i
    let U : Set (ML d ⊕ MR d → ℝ) :=
      {ρ | (∀ i, 0 < ρ i ∧ ρ i < 1) ∧
           (∀ i j, i ≠ j → ρ i ≠ ρ j) ∧
           (∀ e : ME d, -1 < cosLaw (ρ (Sum.inl e.1.1)) (ρ (Sum.inr e.1.2)) ∧
                        cosLaw (ρ (Sum.inl e.1.1)) (ρ (Sum.inr e.1.2)) < 1) ∧
           (∀ i j, i ≠ j →
             H (bOf ρ i) (bOf ρ j) <
               -2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖wOfRadii (ME d) θ ρ e - 1‖))}
    have hρ₀_mem : ρ₀ ∈ U := by
      refine ⟨fun i => ⟨hρ₀_pos i, hρ₀_lt i⟩, fun i j hij h => hij (hnorm_inj i j h),
              fun e => ⟨(hcos_and_w e).1, (hcos_and_w e).2.1⟩, ?_⟩
      intro i j hij
      have hb : ∀ x, bOf ρ₀ x = a x := ha_eq
      have hw : ∀ e, wOfRadii (ME d) θ ρ₀ e = w₀ e := fun e => (hcos_and_w e).2.2.symm
      simp_rw [hb, hw]
      exact hH_gap i j hij
    have hU_open : IsOpen U := by
      rw [isOpen_iff_mem_nhds]
      intro ρ hρ
      have hpos : ∀ i, 0 < ρ i := fun i => (hρ.1 i).1
      have h1_ev : ∀ᶠ ρ' in 𝓝 ρ, ∀ i, 0 < ρ' i ∧ ρ' i < 1 := by
        rw [eventually_all]
        intro i
        exact ((continuous_apply i).continuousAt.tendsto).eventually
          (Ioo_mem_nhds (hρ.1 i).1 (hρ.1 i).2)
      have h2_ev : ∀ᶠ ρ' in 𝓝 ρ, ∀ i j, i ≠ j → ρ' i ≠ ρ' j := by
        have hpair : ∀ᶠ ρ' in 𝓝 ρ, ∀ p : (ML d ⊕ MR d) × (ML d ⊕ MR d),
            p.1 ≠ p.2 → ρ' p.1 ≠ ρ' p.2 := by
          rw [eventually_all]
          intro ⟨i, j⟩
          by_cases hij : i = j
          · exact Eventually.of_forall fun _ h => absurd hij h
          · have hsub_cont : ContinuousAt (fun ρ' : ML d ⊕ MR d → ℝ => ρ' i - ρ' j) ρ :=
              (continuous_apply i).continuousAt.sub (continuous_apply j).continuousAt
            have hev := hsub_cont.eventually (isOpen_ne.mem_nhds (sub_ne_zero.mpr (hρ.2.1 i j hij)))
            filter_upwards [hev] with ρ' h' _
            exact sub_ne_zero.mp h'
        filter_upwards [hpair] with ρ' h' i j hij
        exact h' (i, j) hij
      have h3_ev : ∀ᶠ ρ' in 𝓝 ρ, ∀ e : ME d,
          -1 < cosLaw (ρ' (Sum.inl e.1.1)) (ρ' (Sum.inr e.1.2)) ∧
          cosLaw (ρ' (Sum.inl e.1.1)) (ρ' (Sum.inr e.1.2)) < 1 := by
        rw [eventually_all]
        intro e
        have hL := (continuous_apply (Sum.inl e.1.1)).continuousAt (x := ρ)
        have hR := (continuous_apply (Sum.inr e.1.2)).continuousAt (x := ρ)
        have hden_ne : 2 * ρ (Sum.inl e.1.1) * ρ (Sum.inr e.1.2) ≠ 0 := by
          have ha1 := hpos (Sum.inl e.1.1); have hb1 := hpos (Sum.inr e.1.2); positivity
        have hcos : ContinuousAt (fun ρ' : ML d ⊕ MR d → ℝ =>
            cosLaw (ρ' (Sum.inl e.1.1)) (ρ' (Sum.inr e.1.2))) ρ :=
          (((hL.pow 2).add (hR.pow 2)).sub continuousAt_const).div
            ((continuousAt_const.mul hL).mul hR) hden_ne
        exact hcos.eventually (Ioo_mem_nhds (hρ.2.2.1 e).1 (hρ.2.2.1 e).2)
      have h4_ev : ∀ᶠ ρ' in 𝓝 ρ, ∀ i j, i ≠ j →
          H (bOf ρ' i) (bOf ρ' j) <
            -2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖wOfRadii (ME d) θ ρ' e - 1‖) := by
        have hHrad_cont : ContinuousAt (fun ρ' : ML d ⊕ MR d → ℝ =>
            -2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖wOfRadii (ME d) θ ρ' e - 1‖)) ρ := by
          apply ContinuousAt.mul continuousAt_const
          apply ContinuousAt.mul continuousAt_const
          exact continuousAt_sum_finset Finset.univ
            (fun e ρ' => ‖wOfRadii (ME d) θ ρ' e - 1‖) ρ
            (fun e _ => continuous_norm.continuousAt.comp
              ((continuousAt_wOfRadii (ME d) θ hpos e).sub continuousAt_const))
        have hpair : ∀ᶠ ρ' in 𝓝 ρ, ∀ p : (ML d ⊕ MR d) × (ML d ⊕ MR d), p.1 ≠ p.2 →
            H (bOf ρ' p.1) (bOf ρ' p.2) <
              -2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖wOfRadii (ME d) θ ρ' e - 1‖) := by
          rw [eventually_all]
          intro ⟨i, j⟩
          by_cases hij : i = j
          · exact Eventually.of_forall fun _ h => absurd hij h
          · have hb_cont : ∀ x, ContinuousAt (fun ρ' : ML d ⊕ MR d → ℝ => bOf ρ' x) ρ := fun x =>
              (Complex.continuous_ofReal.continuousAt.comp (continuous_apply x).continuousAt).mul
                continuousAt_const
            have hH_cont : ContinuousAt (fun ρ' : ML d ⊕ MR d → ℝ => H (bOf ρ' i) (bOf ρ' j)) ρ := by
              unfold H
              have hi_re := Complex.continuous_re.continuousAt.comp (hb_cont i)
              have hi_im := Complex.continuous_im.continuousAt.comp (hb_cont i)
              have hj_re := Complex.continuous_re.continuousAt.comp (hb_cont j)
              have hj_im := Complex.continuous_im.continuousAt.comp (hb_cont j)
              exact (hi_re.mul (hj_re.sub hi_re)).add (hi_im.mul (hj_im.sub hi_im))
            have hdiff_cont := hH_cont.sub hHrad_cont
            have hlt0 : H (bOf ρ i) (bOf ρ j) -
                (-2 * (((q - 1 : ℕ) : ℝ) * ∑ e : ME d, ‖wOfRadii (ME d) θ ρ e - 1‖)) < 0 :=
              sub_neg.mpr (hρ.2.2.2 i j hij)
            have hev := hdiff_cont.eventually (gt_mem_nhds hlt0)
            filter_upwards [hev] with ρ' h' _
            exact sub_neg.mp h'
        filter_upwards [hpair] with ρ' h' i j hij
        exact h' (i, j) hij
      filter_upwards [h1_ev, h2_ev, h3_ev, h4_ev] with ρ' h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    rcases lemma_3_4 (ME d) hq2 θ U hU_open ⟨ρ₀, hρ₀_mem⟩
      (fun ρ hρ => ⟨fun i => (hρ.1 i).1, hρ.2.2.1⟩) with ⟨ρ, hρU, hW_inj⟩
    have hb_norm : ∀ i, ‖bOf ρ i‖ = ρ i := by
      intro i
      unfold bOf
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (hρU.1 i).1), hα_norm i,
          mul_one]
    have hw_dist : ∀ e : ME d,
        ‖bOf ρ (Sum.inl e.1.1) - bOf ρ (Sum.inr e.1.2) * wOfRadii (ME d) θ ρ e‖ = 1 := by
      intro e
      set rA := ρ (Sum.inl e.1.1)
      set rB := ρ (Sum.inr e.1.2)
      have hrA : 0 < rA := (hρU.1 (Sum.inl e.1.1)).1
      have hrB : 0 < rB := (hρU.1 (Sum.inr e.1.2)).1
      have hαA_ne : α (Sum.inl e.1.1) ≠ 0 := by rw [← norm_ne_zero_iff, hα_norm]; norm_num
      have hαB_ne : α (Sum.inr e.1.2) ≠ 0 := by rw [← norm_ne_zero_iff, hα_norm]; norm_num
      have hstar_αA : star (α (Sum.inl e.1.1)) = (α (Sum.inl e.1.1))⁻¹ := by
        have h := Complex.mul_conj (α (Sum.inl e.1.1))
        rw [Complex.normSq_eq_norm_sq, hα_norm, one_pow, Complex.ofReal_one] at h
        exact eq_inv_of_mul_eq_one_right h
      have hprod_eq : star (bOf ρ (Sum.inl e.1.1)) *
          (bOf ρ (Sum.inr e.1.2) * wOfRadii (ME d) θ ρ e) =
          ((rA * rB : ℝ) : ℂ) * Complex.exp ((-(gammaAngle rA rB) : ℝ) * Complex.I) := by
        unfold bOf wOfRadii
        have hexp_split :
            Complex.exp (((θ e - gammaAngle rA rB : ℝ) : ℂ) * Complex.I) =
              Complex.exp ((θ e : ℂ) * Complex.I) *
                Complex.exp (((-(gammaAngle rA rB) : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [hexp_split, hθ_exp e, star_mul, Complex.star_def, Complex.conj_ofReal,
            ← Complex.star_def, hstar_αA]
        push_cast
        field_simp [hαA_ne, hαB_ne]
        rfl
      have hre : (star (bOf ρ (Sum.inl e.1.1)) *
          (bOf ρ (Sum.inr e.1.2) * wOfRadii (ME d) θ ρ e)).re =
          (rA ^ 2 + rB ^ 2 - 1) / 2 := by
        rw [hprod_eq]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.exp_ofReal_mul_I_re, Real.cos_neg]
        rw [gammaAngle, Real.cos_arccos (le_of_lt (hρU.2.2.1 e).1) (le_of_lt (hρU.2.2.1 e).2)]
        unfold cosLaw
        have hne : 2 * rA * rB ≠ 0 := by positivity
        change rA * rB * ((rA ^ 2 + rB ^ 2 - 1) / (2 * rA * rB)) = (rA ^ 2 + rB ^ 2 - 1) / 2
        field_simp [hne]
      have hsq : ‖bOf ρ (Sum.inl e.1.1) - bOf ρ (Sum.inr e.1.2) * wOfRadii (ME d) θ ρ e‖ ^ 2 = 1 := by
        have h1 : ∀ u v : ℂ, ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (star u * v).re := by
          intro u v
          rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
              Complex.normSq_apply, Complex.normSq_apply]
          simp [Complex.sub_re, Complex.sub_im, Complex.mul_re]
          ring
        rw [h1, hb_norm (Sum.inl e.1.1), norm_mul, hb_norm (Sum.inr e.1.2), norm_wOfRadii,
            mul_one, hre]
        change rA ^ 2 + rB ^ 2 - 2 * ((rA ^ 2 + rB ^ 2 - 1) / 2) = 1
        ring
      nlinarith [norm_nonneg (bOf ρ (Sum.inl e.1.1) - bOf ρ (Sum.inr e.1.2) * wOfRadii (ME d) θ ρ e)]
    rcases lemma_2_1 (ME d) hq2 (bOf ρ) (wOfRadii (ME d) θ ρ)
      (fun i => by rw [hb_norm]; exact (hρU.1 i).1)
      (fun i => by rw [hb_norm]; exact le_of_lt (hρU.1 i).2)
      (fun i j h => by
        rw [hb_norm, hb_norm] at h
        by_contra hij
        exact hρU.2.1 i j hij h)
      (norm_wOfRadii (ME d) θ ρ)
      hw_dist
      hρU.2.2.2
      hW_inj with ⟨P, hPcard, hP_H, hP_pairs⟩
    have hML_pos : 0 < Fintype.card (ML d) := by
      have : Nonempty (ML d) := ML_nonempty d hd1
      exact Fintype.card_pos
    have hPne : P.Nonempty := by
      rw [← Finset.card_pos, hPcard, Fintype.card_sum]
      have hqpow : 0 < q ^ (ME d).card := by positivity
      positivity
    have hsum_ineq : (2 * k * q + 1) * P.card ≤
        q * ∑ p ∈ P, (P.filter fun p' => ‖p - p'‖ = 1).card := by
      have hME := two_mul_card_ME d hd1
      have hbound : 2 * (ME d).card * (q - 1) * q ^ (ME d).card = d * (q - 1) * P.card := by
        rw [hPcard, hME]
        ring
      have hcoeff : 2 * k * q + 1 ≤ d * (q - 1) := by
        dsimp [d, q]
        nlinarith
      calc (2 * k * q + 1) * P.card
          ≤ d * (q - 1) * P.card := Nat.mul_le_mul_right P.card hcoeff
        _ = 2 * (ME d).card * (q - 1) * q ^ (ME d).card := hbound.symm
        _ ≤ q * ∑ p ∈ P, (P.filter fun p' => ‖p - p'‖ = 1).card := hP_pairs
    rcases exists_core_min_degree k q (by omega) P.card P rfl hPne hsum_ineq with
      ⟨Q, hQP, hQne, hQdeg⟩
    refine ⟨Q.image cToR2, hQne.image cToR2, ?_, ?_⟩
    · exact convexIndep_of_H_neg Q (fun z hz w hw hne => hP_H z (hQP hz) w (hQP hw) hne)
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨z, hzQ, rfl⟩
      unfold Erdos97.HasNUnitDistancePointsAt
      have hfilt : (Q.image cToR2).filter (fun q' => dist (cToR2 z) q' = 1) =
          (Q.filter fun w => ‖z - w‖ = 1).image cToR2 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨w, hwQ, rfl⟩, hd'⟩
          exact ⟨w, ⟨hwQ, by rwa [← dist_cToR2]⟩, rfl⟩
        · rintro ⟨w, ⟨hwQ, hd'⟩, rfl⟩
          exact ⟨⟨w, hwQ, rfl⟩, by rwa [dist_cToR2]⟩
      rw [hfilt, Finset.card_image_of_injective _ cToR2_injective]
      exact hQdeg z hzQ

end Erdos97Disproof

theorem OMA.solution : type_of% @Erdos97.erdos_97.variants.three_unit_distance :=
  Erdos97Disproof.exists_convex_k_unit_dist 3
