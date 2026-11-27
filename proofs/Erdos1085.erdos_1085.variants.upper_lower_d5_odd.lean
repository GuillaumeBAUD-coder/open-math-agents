import FormalConjectures.ErdosProblems.«1085»
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-! # The second-order term for unit distances in odd dimension

Erdős and Pach's odd-dimensional bound combines a balanced Lenz configuration,
a uniform point--circle estimate on two-spheres, and the geometric structure of
large extremal sets. The lower construction uses an integer point--line grid in
homogeneous coordinates. For the sphere upper bound, localization into small
cubes converts unit circles into planar arcs to which the crossing inequality
applies. The structural argument follows the weak-to-exact approach to Lenz
stability due to Swanepoel, with finite rank witnesses for common neighbors.
Lean formalization by @JaviSoto, including the earlier coarse quadratic
upper and lower proofs by Ian Qvist (@Genbox, LeftToSolve PRs #161 and #124). -/

/- # Unit distances on an arbitrary two-sphere

A unit neighbor lies on the circle cut out by a plane of fixed inner
product. Subdivide the points and signed centers into cubes at the circle
scale. In a pair of neighboring cubes the Gram determinant excludes two
common incidences, and short quarter-circle arcs project injectively to a
plane. Apply the crossing-number incidence estimate there and sum over the
bounded set of cube offsets. At radius at most one half, a neighbor must
be the antipode.

The grid Euler inequality and crossing-number argument are adapted from
@JaviSoto's earlier Erdős 652 and 1069 formalizations. The spherical
localization, circle-arc construction, and summation are by @JaviSoto. -/


/- # Euler's edge bound for simple graphs drawn by arcs in the plane

Split each arc into two vertex branches and a middle connector. Rounding the compact pieces
together to a fine square grid preserves their intersections and connectedness. This realizes
the graph as a minor of a finite grid subgraph. Discrete integration identifies grid circulations
with the differences of face potentials, a property preserved by contracting connected branch
sets. Rank-nullity and counting the nonzero entries of face boundaries give `E ≤ 3V`.
Credit: @JaviSoto. -/

section

/- Discretization of compact connected drawings by connected subgraphs of the square lattice. -/

open Set Filter Topology

namespace OMA.Grid652

/-- Integer lattice with the four axis-aligned unit steps. -/
def squareGrid : SimpleGraph (ℤ × ℤ) where
  Adj v w := (v.1 = w.1 ∧ |v.2 - w.2| = 1) ∨ (v.2 = w.2 ∧ |v.1 - w.1| = 1)
  symm := ⟨by
    intro v w h
    rcases h with ⟨h,k⟩ | ⟨h,k⟩
    · exact Or.inl ⟨h.symm, (abs_sub_comm _ _).trans k⟩
    · exact Or.inr ⟨h.symm, (abs_sub_comm _ _).trans k⟩⟩
  loopless := ⟨by intro v; simp⟩

noncomputable def snap (p : ℝ × ℝ) : ℤ × ℤ := (⌊p.1⌋, ⌊p.2⌋)

/-- The nine grid vertices centered on the lower-left corner of the unit square containing p. -/
def pixel (p : ℝ × ℝ) : Set (ℤ × ℤ) :=
  {v | |v.1 - (snap p).1| ≤ 1 ∧ |v.2 - (snap p).2| ≤ 1}

def raster (K : Set (ℝ × ℝ)) : Set (ℤ × ℤ) := {v | ∃ p ∈ K, v ∈ pixel p}

lemma snap_mem (p : ℝ × ℝ) : snap p ∈ pixel p := by simp [pixel]

lemma floor_close {a b : ℝ} (hab : |a - b| < 1) : |⌊a⌋ - ⌊b⌋| ≤ 1 := by
  obtain ⟨h₁,h₂⟩ := abs_lt.mp hab
  have h₃ := Int.floor_le a
  have h₄ := Int.floor_le b
  have h₅ := Int.lt_floor_add_one a
  have h₆ := Int.lt_floor_add_one b
  have h₇ : (⌊a⌋ : ℝ) < (⌊b⌋ : ℝ) + 2 := by linarith
  have h₈ : (⌊b⌋ : ℝ) < (⌊a⌋ : ℝ) + 2 := by linarith
  have h₉ : ⌊a⌋ < ⌊b⌋ + 2 := by exact_mod_cast h₇
  have h₁₀ : ⌊b⌋ < ⌊a⌋ + 2 := by exact_mod_cast h₈
  rw [abs_le]
  omega

lemma snap_mem_of_close {p q : ℝ × ℝ} (h : dist q p < 1) : snap q ∈ pixel p := by
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at h
  exact ⟨floor_close h.1, floor_close h.2⟩

lemma pixel_reachable {S : Set (ℤ × ℤ)} {p : ℝ × ℝ} (hS : pixel p ⊆ S)
    {v : ℤ × ℤ} (hv : v ∈ pixel p) :
    (squareGrid.induce S).Reachable ⟨snap p, hS (snap_mem p)⟩ ⟨v, hS hv⟩ := by
  obtain ⟨hx,hy⟩ := hv
  let m : ℤ × ℤ := (v.1, (snap p).2)
  have hm : m ∈ pixel p := ⟨hx, by simp [m]⟩
  have h₁ : (squareGrid.induce S).Reachable ⟨snap p, hS (snap_mem p)⟩ ⟨m, hS hm⟩ := by
    by_cases h : v.1 = (snap p).1
    · have he : (⟨snap p, hS (snap_mem p)⟩ : S) = ⟨m, hS hm⟩ :=
        Subtype.ext (Prod.ext h.symm rfl)
      rw [he]
    · apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.induce_adj]
      apply Or.inr
      have hpos := abs_pos.mpr (sub_ne_zero.mpr h)
      exact ⟨rfl, by rw [abs_sub_comm]; change |v.1 - (snap p).1| = 1; omega⟩
  apply h₁.trans
  by_cases h : v.2 = (snap p).2
  · have he : (⟨m, hS hm⟩ : S) = ⟨v, hS ⟨hx,hy⟩⟩ := Subtype.ext (Prod.ext rfl h.symm)
    rw [he]
  · apply SimpleGraph.Adj.reachable
    rw [SimpleGraph.induce_adj]
    apply Or.inl
    have hpos := abs_pos.mpr (sub_ne_zero.mpr h)
    exact ⟨rfl, by rw [abs_sub_comm]; change |v.2 - (snap p).2| = 1; omega⟩

lemma raster_preconnected {K : Set (ℝ × ℝ)} (hK : IsPreconnected K) :
    (squareGrid.induce (raster K)).Preconnected := by
  let toVertex (p : K) : raster K := ⟨snap p.val, p.val, p.property, snap_mem _⟩
  have sameComponent (p q : K) (h : dist q.val p.val < 1) :
      (squareGrid.induce (raster K)).Reachable (toVertex p) (toVertex q) :=
    pixel_reachable (S := raster K) (p := p.val) (fun _ hv => ⟨p.val, p.property,hv⟩)
      (snap_mem_of_close h)
  intro a b
  obtain ⟨x,hx,hax⟩ := a.property
  obtain ⟨y,hy,hby⟩ := b.property
  let P (z : K) := (squareGrid.induce (raster K)).Reachable (toVertex ⟨x,hx⟩) (toVertex z)
  have hl : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro z
    filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < 1 by norm_num)] with w hw
    have h := sameComponent z w hw
    exact propext ⟨(·.trans h.symm), (·.trans h)⟩
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  have hxy : P ⟨y,hy⟩ := (hl.apply_eq_of_preconnectedSpace ⟨y,hy⟩ ⟨x,hx⟩).symm ▸
    SimpleGraph.Reachable.refl _
  exact (pixel_reachable (S := raster K) (p := x) (fun _ hv => ⟨x,hx,hv⟩) hax).symm.trans
    (hxy.trans (pixel_reachable (S := raster K) (p := y) (fun _ hv => ⟨y,hy,hv⟩) hby))

lemma raster_finite {K : Set (ℝ × ℝ)} (hK : IsCompact K) : (raster K).Finite := by
  obtain ⟨lx,hlx⟩ := (hK.image continuous_fst).bddBelow
  obtain ⟨ly,hly⟩ := (hK.image continuous_snd).bddBelow
  obtain ⟨ux,hux⟩ := (hK.image continuous_fst).bddAbove
  obtain ⟨uy,huy⟩ := (hK.image continuous_snd).bddAbove
  apply (Set.finite_Icc (⌊lx⌋ - 1, ⌊ly⌋ - 1) (⌊ux⌋ + 1, ⌊uy⌋ + 1)).subset
  rintro v ⟨p,hp,hx,hy⟩
  have ax' : ⌊lx⌋ ≤ ⌊p.1⌋ := Int.floor_mono (hlx ⟨p,hp,rfl⟩)
  have ay' : ⌊ly⌋ ≤ ⌊p.2⌋ := Int.floor_mono (hly ⟨p,hp,rfl⟩)
  have bx' : ⌊p.1⌋ ≤ ⌊ux⌋ := Int.floor_mono (hux ⟨p,hp,rfl⟩)
  have by'' : ⌊p.2⌋ ≤ ⌊uy⌋ := Int.floor_mono (huy ⟨p,hp,rfl⟩)
  change |v.1 - ⌊p.1⌋| ≤ 1 at hx
  change |v.2 - ⌊p.2⌋| ≤ 1 at hy
  rw [abs_le] at hx hy
  exact ⟨⟨by dsimp; omega, by dsimp; omega⟩, ⟨by dsimp; omega, by dsimp; omega⟩⟩

noncomputable def scale (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1/h, p.2/h)

lemma scale_continuous (h : ℝ) : Continuous (scale h) :=
  (continuous_fst.div_const h).prodMk (continuous_snd.div_const h)

def rasterAt (h : ℝ) (K : Set (ℝ × ℝ)) := raster (scale h '' K)

private lemma pixel_error {z : ℤ} {p h : ℝ} (hh : 0 < h) (hz : |z - ⌊p/h⌋| ≤ 1) :
    |h * z - p| < 2*h := by
  have h₁ := Int.floor_le (p/h)
  have h₂ := Int.lt_floor_add_one (p/h)
  obtain ⟨hx,hy⟩ := abs_le.mp hz
  have hx' : (-1 : ℝ) ≤ z - (⌊p/h⌋ : ℤ) := by exact_mod_cast hx
  have hy' : (z : ℝ) - (⌊p/h⌋ : ℤ) ≤ 1 := by exact_mod_cast hy
  have h₃ := (le_div_iff₀ hh).mp h₁
  have h₄ := (div_lt_iff₀ hh).mp h₂
  rw [abs_lt]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hx' hh.le,
    mul_le_mul_of_nonneg_right hy' hh.le]

lemma rasterAt_thickening {z : ℤ × ℤ} {h : ℝ} {K : Set (ℝ × ℝ)}
    (hh : 0 < h) (hz : z ∈ rasterAt h K) :
    (h * z.1, h * z.2) ∈ Metric.thickening (2*h) K := by
  obtain ⟨_,⟨p,hp,rfl⟩,hx,hy⟩ := hz
  apply Metric.mem_thickening_iff.mpr
  refine ⟨p,hp,?_⟩
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  exact ⟨pixel_error hh hx, pixel_error hh hy⟩

lemma eventually_rasterAt_disjoint_iff {K L : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hL : IsCompact L) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), Disjoint (rasterAt h K) (rasterAt h L) ↔ Disjoint K L := by
  by_cases hd : Disjoint K L
  · obtain ⟨r,hr,hsep⟩ := hd.exists_thickenings hK hL.isClosed
    have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < r/2 :=
      eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (by positivity))
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhr
    refine ⟨fun _ => hd,fun _ => Set.disjoint_left.mpr ?_⟩
    intro z hz hw
    have hlt : 2*h ≤ r := by linarith
    exact Set.disjoint_left.mp hsep
      (Metric.thickening_mono hlt _ (rasterAt_thickening hh hz))
      (Metric.thickening_mono hlt _ (rasterAt_thickening hh hw))
  · filter_upwards with h
    refine ⟨fun hgrid => ?_, fun hdis => (hd hdis).elim⟩
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp hgrid
      (show snap (scale h p) ∈ rasterAt h K from ⟨_,⟨p,hp,rfl⟩,snap_mem _⟩)
      (show snap (scale h p) ∈ rasterAt h L from ⟨_,⟨p,hq,rfl⟩,snap_mem _⟩)

/-- A finite family of compact connected plane sets admits finite connected lattice models
    with exactly the same intersection relation, and the mesh may be chosen arbitrarily fine. -/
theorem finite_grid_realization {ι : Type*} [Finite ι] (K : ι → Set (ℝ × ℝ))
    (hc : ∀ i, IsCompact (K i)) (hp : ∀ i, IsPreconnected (K i)) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (∀ i, (rasterAt h (K i)).Finite ∧ (squareGrid.induce (rasterAt h (K i))).Preconnected) ∧
      (∀ i j, Disjoint (rasterAt h (K i)) (rasterAt h (K j)) ↔ Disjoint (K i) (K j)) := by
  have pairs : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∀ i j, Disjoint (rasterAt h (K i)) (rasterAt h (K j)) ↔ Disjoint (K i) (K j) := by
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      eventually_rasterAt_disjoint_iff (hc i) (hc j)
  filter_upwards [pairs] with h hh
  exact ⟨fun i => ⟨raster_finite ((hc i).image (scale_continuous h)),
    raster_preconnected ((hp i).image _ (scale_continuous h).continuousOn)⟩, hh⟩

open scoped EuclideanGeometry

def coords (p : ℝ²) : ℝ × ℝ := (p 0, p 1)

lemma coords_injective : Function.Injective coords := by
  intro p q h
  ext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

lemma coords_continuous : Continuous coords :=
  (PiLp.continuous_apply 2 _ 0).prodMk (PiLp.continuous_apply 2 _ 1)

/-- Joint rasterization for the formal conjecture's Euclidean-space model, including empty sets. -/
theorem plane_grid_realization {ι : Type*} [Finite ι] (K : ι → Set ℝ²)
    (hc : ∀ i, IsCompact (K i)) (hp : ∀ i, IsPreconnected (K i)) :
    ∃ A : ι → Set (ℤ × ℤ),
      (∀ i, (A i).Finite ∧ (squareGrid.induce (A i)).Preconnected) ∧
      (∀ i j, Disjoint (A i) (A j) ↔ Disjoint (K i) (K j)) := by
  obtain ⟨h, h₁, h₂⟩ := (finite_grid_realization (fun i => coords '' K i)
    (fun i => (hc i).image coords_continuous)
    (fun i => (hp i).image _ coords_continuous.continuousOn)).exists
  exact ⟨_,h₁,fun i j => (h₂ i j).trans (Set.disjoint_image_iff coords_injective)⟩


end OMA.Grid652

/- Face potentials under deletion and contraction of finite directed networks. -/

open scoped BigOperators

namespace OMA.Grid652

variable {W V E J F : Type*}

noncomputable def atom (w : W) (u : W) : ℚ := by classical exact if w = u then 1 else 0

/-- Push a function of finite support forward, summing its coefficients over each fiber. -/
noncomputable def push [Fintype W] (f : W → V) : (W → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun z := ∑ w, z w • atom (f w)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a z := by simp [Finset.smul_sum, mul_smul]

lemma push_atom [Fintype W] (f : W → V) (w : W) : push f (atom w) = atom (f w) := by
  classical
  change (∑ u, (if w = u then (1 : ℚ) else 0) • atom (f u)) = _
  simp [ite_smul]

lemma push_comp [Fintype W] [Fintype V] {U : Type*} (f : W → V) (g : V → U)
    (z : W → ℚ) : push g (push f z) = push (g ∘ f) z := by
  change push g (∑ w, z w • atom (f w)) = _
  simp only [map_sum, map_smul, push_atom]
  rfl

lemma push_id [Fintype W] (z : W → ℚ) : push id z = z := by
  classical
  ext w
  simp [push, atom]

noncomputable def net [Fintype E] (s t : E → V) : (E → ℚ) →ₗ[ℚ] (V → ℚ) :=
  push t - push s

lemma net_atom [Fintype E] (s t : E → V) (e : E) : net s t (atom e) = atom (t e) - atom (s e) := by
  simp [net, push_atom]

lemma net_push [Fintype W] [Fintype E] (s t : E → W) (π : W → V) (z : E → ℚ) :
    push π (net s t z) = net (π ∘ s) (π ∘ t) z := by simp [net, map_sub, push_comp]

lemma net_sum [Fintype E] [Fintype J] (s t : E ⊕ J → W) (z : E → ℚ) (w : J → ℚ) :
    net s t (Sum.elim z w) =
      net (s ∘ Sum.inl) (t ∘ Sum.inl) z + net (s ∘ Sum.inr) (t ∘ Sum.inr) w := by
  simp [net, push, Fintype.sum_sum_type]
  abel

/-- An exact dual means the divergence-free flows are exactly the edge differences of
    face potentials. The face on either side need not be different. -/
def ExactDual [Fintype E] (s t : E → V) (l r : E → F) : Prop :=
  ∀ z : E → ℚ, net s t z = 0 ↔ ∃ c : F → ℚ, ∀ e, z e = c (l e) - c (r e)

/-- Connectedness of a fiber is needed only to route the difference of two unit sources
    along its internal edges. The equivalence closure of edge endpoint pairs suffices. -/
lemma atom_sub_mem_range_of_joined [Fintype J] (s t : J → W) {a b : W}
    (h : Relation.EqvGen (fun x y => ∃ j, s j = x ∧ t j = y) a b) :
    atom b - atom a ∈ LinearMap.range (net s t) := by
  induction h with
  | rel a b h =>
    obtain ⟨j,rfl,rfl⟩ := h
    exact ⟨atom j,net_atom s t j⟩
  | refl a => simp
  | symm a b _ ih => simpa using (LinearMap.range (net s t)).neg_mem ih
  | trans a b c _ _ ih₁ ih₂ =>
    convert (LinearMap.range (net s t)).add_mem ih₂ ih₁ using 1
    abel

lemma mem_internal_range [Fintype J] [Fintype W] [Fintype V] (s t : J → W)
    (π : W → V) (anchor : V → W)
    (joined : ∀ w, Relation.EqvGen (fun x y => ∃ j, s j = x ∧ t j = y) (anchor (π w)) w)
    {b : W → ℚ} (hb : push π b = 0) :
    b ∈ LinearMap.range (net s t) := by
  have h₁ : (∑ w, b w • (atom w - atom (anchor (π w)))) ∈ LinearMap.range (net s t) :=
    Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (atom_sub_mem_range_of_joined s t (joined w))
  have h₂ : push (anchor ∘ π) b = 0 := by rw [← push_comp, hb, map_zero]
  simp only [smul_sub, Finset.sum_sub_distrib] at h₁
  change push id b - push (anchor ∘ π) b ∈ _ at h₁
  simpa [push_id, h₂] using h₁

/-- Contract connected internal branch sets by forgetting their edges in the dual. -/
theorem exactDual_contract [Fintype E] [Fintype J] [Fintype W] [Fintype V]
    (s t : E ⊕ J → W) (l r : E ⊕ J → F) (hD : ExactDual s t l r)
    (π : W → V) (anchor : V → W) (internal : ∀ j : J, π (s (.inr j)) = π (t (.inr j)))
    (joined : ∀ w, Relation.EqvGen
      (fun x y => ∃ j : J, s (.inr j) = x ∧ t (.inr j) = y) (anchor (π w)) w) :
    ExactDual (π ∘ s ∘ Sum.inl) (π ∘ t ∘ Sum.inl) (l ∘ Sum.inl) (r ∘ Sum.inl) := by
  have collapsed (w : J → ℚ) : push π (net (s ∘ Sum.inr) (t ∘ Sum.inr) w) = 0 := by
    rw [net_push]
    have heq : π ∘ s ∘ Sum.inr = π ∘ t ∘ Sum.inr := funext internal
    simp [heq, net]
  intro z
  constructor
  · intro hz
    obtain ⟨w,hw⟩ := mem_internal_range (s ∘ Sum.inr) (t ∘ Sum.inr) π anchor joined
      (b := -net (s ∘ Sum.inl) (t ∘ Sum.inl) z) (by rw [map_neg, net_push, hz, neg_zero])
    have hfull : net s t (Sum.elim z w) = 0 := by rw [net_sum, hw, add_neg_cancel]
    obtain ⟨c,hc⟩ := (hD _).mp hfull
    exact ⟨c,fun e => hc (.inl e)⟩
  · rintro ⟨c,hc⟩
    let w (j : J) := c (l (.inr j)) - c (r (.inr j))
    have hfull : net s t (Sum.elim z w) = 0 :=
      (hD _).mpr ⟨c,fun e => by cases e with | inl e => exact hc e | inr j => rfl⟩
    have hh := congrArg (push π) hfull
    simpa only [net_sum, map_add, collapsed, add_zero, net_push, map_zero] using hh

abbrev GridPoint := ℤ × ℤ
abbrev GridEdge := GridPoint ⊕ GridPoint

/-- Each oriented edge is indexed by its head, with horizontal edges in the left summand. -/
def gridHead : GridEdge → GridPoint := Sum.elim id id
def gridTail : GridEdge → GridPoint :=
  Sum.elim (fun p => (p.1-1,p.2)) (fun p => (p.1,p.2-1))
def faceLeft : GridEdge → GridPoint :=
  Sum.elim id (fun p => (p.1+1,p.2))
def faceRight : GridEdge → GridPoint :=
  Sum.elim (fun p => (p.1,p.2+1)) id

/-- A discrete integral on all integer coordinates, based at zero. -/
def primitive (f : ℤ → ℚ) (x : ℤ) : ℚ :=
  x.inductionOn' 0 0 (fun i _ a => a + f i) (fun i _ a => a - f (i-1))

lemma primitive_zero (f : ℤ → ℚ) : primitive f 0 = 0 := Int.inductionOn'_self

lemma primitive_succ (f : ℤ → ℚ) (x : ℤ) : primitive f (x+1) = primitive f x + f x := by
  by_cases hx : 0 ≤ x
  · exact Int.inductionOn'_add_one hx
  · have he : primitive f (x+1-1) = primitive f (x+1) - f (x+1-1) :=
      Int.inductionOn'_sub_one (by omega : x+1 ≤ (0:ℤ))
    simp only [add_sub_cancel_right] at he
    linarith

lemma grid_integral (H V : ℤ → ℤ → ℚ)
    (hdiv : ∀ i j, H (i+1) j + V i (j+1) = H i j + V i j) :
    ∃ c : GridPoint → ℚ, (∀ i j, H i j = c (i,j) - c (i,j+1)) ∧
      (∀ i j, V i j = c (i+1,j) - c (i,j)) := by
  let c (p : GridPoint) := primitive (fun i => V i p.2) p.1 - primitive (H 0) p.2
  have hv (i j : ℤ) : c (i+1,j) = c (i,j) + V i j := by simp [c, primitive_succ]; ring
  refine ⟨c,?_,fun i j => by rw [hv]; ring⟩
  intro i j
  have step (i : ℤ) :
      (H i j = c (i,j) - c (i,j+1)) ↔ (H (i+1) j = c (i+1,j) - c (i+1,j+1)) := by
    rw [hv, hv]
    constructor <;> intro hh <;> linarith [hdiv i j]
  refine Int.inductionOn' i 0 ?_ (fun n _ => (step n).mp) ?_
  · simp [c,primitive_zero,primitive_succ]
  · intro n _ ih
    apply (step (n-1)).mpr
    simpa using ih

lemma push_inj_apply [Fintype E] (f : E → W) (hf : Function.Injective f) (z : E → ℚ) (e : E) :
    push f z (f e) = z e := by
  classical
  simp [push, atom, hf.eq_iff, mul_ite]

lemma push_outside [Fintype E] (f : E → W) (z : E → ℚ) (w : W) (hw : w ∉ Set.range f) :
    push f z w = 0 := by
  classical
  have hn : ∀ e, f e ≠ w := fun e he => hw ⟨e,he⟩
  simp [push,atom,hn]

private lemma head_atom (e : GridEdge) (i j : ℤ) :
    atom (gridHead e) (i,j) = atom e (.inl (i,j)) + atom e (.inr (i,j)) := by
  classical
  cases e with
  | inl p => by_cases h : p = (i,j) <;> simp [gridHead,atom,h]
  | inr p => by_cases h : p = (i,j) <;> simp [gridHead,atom,h]

private lemma tail_atom (e : GridEdge) (i j : ℤ) :
    atom (gridTail e) (i,j) = atom e (.inl (i+1,j)) + atom e (.inr (i,j+1)) := by
  classical
  rcases e with ⟨x,y⟩ | ⟨x,y⟩ <;> simp [gridTail,atom,Prod.mk.injEq,sub_eq_iff_eq_add]

lemma grid_net_apply [Fintype E] (key : E → GridEdge) (z : E → ℚ) (i j : ℤ) :
    net (gridTail ∘ key) (gridHead ∘ key) z (i,j) =
      (push key z (.inl (i,j)) + push key z (.inr (i,j))) -
      (push key z (.inl (i+1,j)) + push key z (.inr (i,j+1))) := by
  classical
  simp [net, push, head_atom, tail_atom, mul_add, Finset.sum_add_distrib]

def missing (key : E → GridEdge) (a b : GridPoint) : Prop :=
  ∃ d ∉ Set.range key, faceLeft d = a ∧ faceRight d = b

/-- Every finite subgraph of the infinite square lattice has an exact dual. Faces are
    obtained by identifying neighboring unit squares across all omitted grid edges. -/
theorem grid_exactDual [Fintype E] (key : E → GridEdge) (inj : Function.Injective key) :
    ExactDual (gridTail ∘ key) (gridHead ∘ key)
      (Quot.mk (missing key) ∘ faceLeft ∘ key) (Quot.mk (missing key) ∘ faceRight ∘ key) := by
  classical
  intro z
  let H (i j : ℤ) := push key z (.inl (i,j))
  let V (i j : ℤ) := push key z (.inr (i,j))
  have diviff : net (gridTail ∘ key) (gridHead ∘ key) z = 0 ↔
      ∀ i j, H (i+1) j + V i (j+1) = H i j + V i j := by
    constructor
    · intro hz i j
      have he := congrFun hz (i,j)
      rw [grid_net_apply] at he
      exact (sub_eq_zero.mp he).symm
    · intro he
      funext ⟨i,j⟩
      exact (grid_net_apply key z i j).trans (sub_eq_zero.mpr (he i j).symm)
  rw [diviff]
  constructor
  · intro hdiv
    obtain ⟨c,hH,hV⟩ := grid_integral H V hdiv
    have hgrad (e : GridEdge) : push key z e = c (faceLeft e) - c (faceRight e) := by
      rcases e with ⟨i,j⟩ | ⟨i,j⟩
      · exact hH i j
      · exact hV i j
    have compat : ∀ a b, missing key a b → c a = c b := by
      rintro _ _ ⟨e,he,rfl,rfl⟩
      exact sub_eq_zero.mp ((hgrad e).symm.trans (push_outside key z e he))
    exact ⟨Quot.lift c compat,fun e => (push_inj_apply key inj z e).symm.trans (hgrad (key e))⟩
  · rintro ⟨c,hc⟩
    let q := Quot.mk (missing key)
    have he (d : GridEdge) : push key z d = c (q (faceLeft d)) - c (q (faceRight d)) := by
      by_cases hd : d ∈ Set.range key
      · obtain ⟨e,rfl⟩ := hd
        exact (push_inj_apply key inj z e).trans (hc e)
      · have hq : q (faceLeft d) = q (faceRight d) := Quot.sound ⟨d,hd,rfl,rfl⟩
        simp [hq, push_outside key z d hd]
    intro i j
    dsimp only [H,V]
    rw [he,he,he,he]
    simp [faceLeft,faceRight]

end OMA.Grid652

/- A linear-algebraic Euler bound from the two faces on either side of an edge.
    Neither facial walks nor a choice of spanning trees are required. -/

open Set Matrix Module
open scoped BigOperators

namespace OMA.Grid652

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
variable {k : Type*} [Field k]

omit [Fintype V] in
/-- A nonzero circulation on a finite simple graph uses at least three edges. Both the
    ordinary oriented incidence matrix and the unsigned matrix over ZMod 2 satisfy this. -/
lemma circulation_support_card [DecidableEq k] (edge : E → Finset V)
    (two : ∀ e, (edge e).card = 2) (simple : Function.Injective edge)
    (M : Matrix V E k) (suppM : ∀ v e, M v e ≠ 0 ↔ v ∈ edge e)
    {z : E → k} (hne : z ≠ 0) (hcycle : M.mulVec z = 0) :
    3 ≤ (Finset.univ.filter fun e => z e ≠ 0).card := by
  classical
  let S := Finset.univ.filter fun e => z e ≠ 0
  have hs {e : E} : e ∈ S ↔ z e ≠ 0 := by simp [S]
  have another {e : E} (he : e ∈ S) {v : V} (hv : v ∈ edge e) :
      ∃ f ∈ S.erase e, v ∈ edge f := by
    by_contra! no
    have eq : (M.mulVec z) v = M v e * z e := by
      apply Finset.sum_eq_single e
      · intro f _ hfe
        by_cases hf : f ∈ S
        · have hvf := no f (Finset.mem_erase.mpr ⟨hfe,hf⟩)
          have hM : M v f = 0 := not_ne_iff.mp (fun hp => hvf ((suppM v f).mp hp))
          simp [hM]
        · have hz : z f = 0 := by simpa [S] using hf
          simp [hz]
      · simp
    have hzero : (M.mulVec z) v = 0 := congrFun hcycle v
    exact (mul_ne_zero ((suppM v e).mpr hv) (hs.mp he)) (eq.symm.trans hzero)
  by_contra! hcard
  have hz : ∃ e, z e ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨e,he⟩ := hz
  have hem := hs.mpr he
  have hone : (S.erase e).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hem]
    change S.card < 3 at hcard
    omega
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [two]; decide : 0 < (edge e).card)
  obtain ⟨f,hf,_⟩ := another hem hv
  have sub : edge e ⊆ edge f := by
    intro w hw
    obtain ⟨g,hg,hwg⟩ := another hem hw
    exact (Finset.card_le_one.mp hone g hg f hf) ▸ hwg
  have heq : e = f := simple (Finset.eq_of_subset_of_card_le sub (by rw [two,two]))
  exact (Finset.mem_erase.mp hf).1 heq.symm

/-- Boundary of one dual face. Its value on a primal edge is determined by the two
    adjacent faces, which may coincide. -/
noncomputable def faceBoundary (l r : E → F) (f : F) (e : E) : k := by
  classical exact (if l e = f then 1 else 0) - (if r e = f then 1 else 0)

/-- Euler's weak edge bound for graphs whose cycle space is generated by edge differences
    of face potentials and whose individual face boundaries have zero divergence. -/
theorem euler_of_face_potentials (edge : E → Finset V) (two : ∀ e, (edge e).card = 2)
    (simple : Function.Injective edge) (M : Matrix V E k) (suppM : ∀ v e, M v e ≠ 0 ↔ v ∈ edge e)
    (l r : E → F) (hface : ∀ f, M.mulVec (faceBoundary l r f) = 0)
    (hfill : ∀ z : E → k, M.mulVec z = 0 → ∃ c : F → k, ∀ e, z e = c (l e) - c (r e)) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  classical
  let B := faceBoundary (k := k) l r
  let A : Finset F := Finset.univ.filter fun f => B f ≠ 0
  have doubleCount : A.card • (3 : ℕ) ≤ (Finset.univ : Finset E).card • 2 := by
    apply Finset.card_nsmul_le_card_nsmul (fun f e => B f e ≠ 0)
    · intro f hf
      exact circulation_support_card edge two simple M suppM
        (Finset.mem_filter.mp hf).2 (hface f)
    · intro e _
      apply le_trans (Finset.card_le_card (t := {l e,r e}) ?_) Finset.card_le_two
      intro f hf
      by_contra! hn
      have hz := (Finset.mem_filter.mp hf).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      exact hz (by simp [B, faceBoundary, Ne.symm hn.1, Ne.symm hn.2])
  let column (f : A) := B f.val
  have hspan : LinearMap.ker M.mulVecLin ≤ Submodule.span k (Set.range column) := by
    intro z hz
    obtain ⟨c,hc⟩ := hfill z (by exact hz)
    have hcomb : z = ∑ f : F, c f • B f := by
      ext e
      rw [hc]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, B, faceBoundary,
        mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
      simp
    rw [hcomb]
    apply Submodule.sum_mem
    intro f _
    by_cases hf : f ∈ A
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨f,hf⟩,rfl⟩)
    · have hzero : B f = 0 := by simpa [A] using hf
      simp [hzero]
  have hker := (Submodule.finrank_mono hspan).trans (finrank_range_le_card (R := k) column)
  have hrange := (LinearMap.range M.mulVecLin).finrank_le
  have htotal := M.mulVecLin.finrank_range_add_finrank_ker
  simp only [finrank_pi, Fintype.card_coe] at hker hrange htotal
  have hcount : A.card * 3 ≤ Fintype.card E * 2 := by simpa using doubleCount
  omega

end OMA.Grid652

/- Every simple graph represented by disjoint connected branch sets in a finite square-grid
    subgraph has at most three times as many edges as vertices. -/

open Set Matrix Module

namespace OMA.Grid652

variable {W V E J F : Type*}

lemma exactDual_bound [DecidableEq V] [Fintype V] [Fintype E] (s t : E → V)
    (different : ∀ e, s e ≠ t e)
    (simple : Function.Injective (fun e => ({s e,t e} : Finset V)))
    (l r : E → F) (hD : ExactDual s t l r) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  classical
  let D := Finset.univ.image l ∪ Finset.univ.image r
  let L (e : E) : D := ⟨l e,Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  let R (e : E) : D := ⟨r e,Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  let M (v : V) (e : E) := atom (t e) v - atom (s e) v
  have eq (z : E → ℚ) : Matrix.mulVec M z = net s t z := by
    ext v
    simp [Matrix.mulVec,dotProduct,M,net,push,mul_comm,mul_sub,Finset.sum_sub_distrib]
  apply euler_of_face_potentials (fun e => ({s e,t e} : Finset V)) (fun e => by simp [different e])
    simple M _ L R
  · intro f
    rw [eq]
    apply (hD _).mpr
    refine ⟨fun p => atom p f.val,fun e => ?_⟩
    simp only [faceBoundary,atom]
    have h₁ : (L e = f) ↔ l e = f.val := Subtype.ext_iff
    have h₂ : (R e = f) ↔ r e = f.val := Subtype.ext_iff
    simp [h₁,h₂]
  · intro z hz
    obtain ⟨c,hc⟩ := (hD _).mp ((eq z).symm.trans hz)
    exact ⟨fun p => c p.val,hc⟩
  · intro v e
    by_cases h : s e = v
    · subst v
      simp [M,atom,(different e).symm]
    · by_cases h' : t e = v
      · subst v
        simp [M,atom,h]
      · simp [M,atom,h,h',Ne.symm h,Ne.symm h']

/-- Extending a finite network along an injective vertex map leaves its cycle space unchanged. -/
lemma injective_net [Fintype E] [Fintype W] (s t : E → W) (p : W → V)
    (hp : Function.Injective p) (z : E → ℚ) :
    net (p ∘ s) (p ∘ t) z = 0 ↔ net s t z = 0 := by
  rw [← net_push]
  refine ⟨fun h => funext fun w => ?_,fun h => by simp [h]⟩
  exact (push_inj_apply p hp _ w).symm.trans (congrFun h (p w))

/-- Exact planar edge bound for any simple grid minor: the finite network has one
    extra edge per desired graph edge and arbitrary connected internal branch edges. -/
theorem euler_grid_minor [DecidableEq V] [Fintype E] [Fintype J] [Fintype W] [Fintype V]
    (s t : E ⊕ J → W) (p : W → GridPoint) (hp : Function.Injective p)
    (key : E ⊕ J → GridEdge) (inj : Function.Injective key)
    (tail : gridTail ∘ key = p ∘ s) (head : gridHead ∘ key = p ∘ t)
    (π : W → V) (anchor : V → W)
    (internal : ∀ j : J, π (s (.inr j)) = π (t (.inr j)))
    (joined : ∀ w, Relation.EqvGen
      (fun x y => ∃ j : J, s (.inr j) = x ∧ t (.inr j) = y) (anchor (π w)) w)
    (different : ∀ e : E, π (s (.inl e)) ≠ π (t (.inl e)))
    (simple : Function.Injective (fun e : E => ({π (s (.inl e)),π (t (.inl e))} : Finset V))) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  let l := Quot.mk (missing key) ∘ faceLeft ∘ key
  let r := Quot.mk (missing key) ∘ faceRight ∘ key
  have hD : ExactDual s t l r := by
    intro z
    have hD := grid_exactDual key inj z
    rw [tail,head,injective_net s t p hp] at hD
    exact hD
  exact exactDual_bound _ _ different simple _ _ (exactDual_contract s t l r hD π anchor internal joined)

end OMA.Grid652

/- Turn a family of disjoint vertex patches and disjoint edge connectors into a grid minor. -/

open Set

namespace OMA.Grid652

variable {X V E : Type*}

/-- Follow a walk until it first touches the target, retaining its connected prefix. -/
lemma before_target (G : SimpleGraph X) {C T : Set X} {a b : C}
    (p : (G.induce C).Walk a b) (ha : a.val ∉ T) (hb : b.val ∈ T) :
    ∃ D : Set X, D ⊆ C ∧ a.val ∈ D ∧ Disjoint D T ∧ (G.induce D).Preconnected ∧
      ∃ x ∈ D, ∃ y ∈ T, G.Adj x y := by
  classical
  induction p with
  | nil => exact (ha hb).elim
  | @cons a u b au p ih =>
    by_cases hu : u.val ∈ T
    · refine ⟨{a.val},Set.singleton_subset_iff.mpr a.property,rfl,?_,?_,a.val,rfl,u.val,hu,au⟩
      · simpa using ha
      · intro x y
        have he : x = y := Subtype.ext (x.property.trans y.property.symm)
        rw [he]
    · obtain ⟨D,hDC,huD,hd,hc,tail⟩ := ih hu hb
      let S : Set X := {a.val,u.val}
      have aS : a.val ∈ S := by simp [S]
      have uS : u.val ∈ S := by simp [S]
      refine ⟨S ∪ D,Set.union_subset ?_ hDC, Or.inl aS,disjoint_union_left.mpr ⟨?_,hd⟩,?_,?_⟩
      · intro x hx
        rcases hx with rfl | h
        · exact a.property
        · exact h ▸ u.property
      · intro I hS hT x hx
        rcases hS hx with he | he
        · exact ha (he ▸ hT hx)
        · exact hu (he ▸ hT hx)
      · exact (G.induce_union_connected (G.induce_pair_connected_of_adj au).preconnected hc
          ⟨u.val,uS,huD⟩).preconnected
      · obtain ⟨x,hx,y,hy,hxy⟩ := tail
        exact ⟨x,Or.inr hx,y,hy,hxy⟩

lemma patches_reach {G : SimpleGraph X} {A B : Set X} (h : A ⊆ B)
    {x y : A} (p : (G.induce A).Reachable x y) :
    (G.induce B).Reachable ⟨x.val,h x.property⟩ ⟨y.val,h y.property⟩ := by
  exact p.map (⟨Set.inclusion h,fun {a b} ha => ha⟩ : G.induce A →g G.induce B)

/-- A bipartite incidence model whose connector patches meet only their two prescribed
    end patches can be refined to disjoint connected branch sets with a single adjacency
    for each edge. -/
theorem shrink_connectors [Finite E] (G : SimpleGraph X) (s t : E → V)
    (hne : ∀ e, s e ≠ t e) (B : V → Set X) (C : E → Set X)
    (Bfin : ∀ v, (B v).Finite) (Cfin : ∀ e, (C e).Finite)
    (Bne : ∀ v, (B v).Nonempty) (Bconn : ∀ v, (G.induce (B v)).Preconnected)
    (Cconn : ∀ e, (G.induce (C e)).Preconnected)
    (BB : ∀ v w, v ≠ w → Disjoint (B v) (B w)) (CC : ∀ e f, e ≠ f → Disjoint (C e) (C f))
    (touch : ∀ e v, ¬Disjoint (C e) (B v) ↔ s e = v ∨ t e = v) :
    ∃ R : V → Set X, (∀ v, (R v).Finite ∧ (R v).Nonempty ∧ (G.induce (R v)).Preconnected) ∧
      (∀ v w, v ≠ w → Disjoint (R v) (R w)) ∧
      ∀ e, ∃ x ∈ R (s e), ∃ y ∈ R (t e), G.Adj x y := by
  classical
  have expandBranch (e : E) : ∃ D : Set X, D ⊆ C e ∧ (D ∩ B (s e)).Nonempty ∧
      Disjoint D (B (t e)) ∧ (G.induce D).Preconnected ∧ ∃ x ∈ D, ∃ y ∈ B (t e), G.Adj x y := by
    obtain ⟨x,hx,hxs⟩ := Set.not_disjoint_iff.mp ((touch e (s e)).mpr (Or.inl rfl))
    obtain ⟨y,hy,hyt⟩ := Set.not_disjoint_iff.mp ((touch e (t e)).mpr (Or.inr rfl))
    have hxt := Set.disjoint_left.mp (BB _ _ (hne e)) hxs
    obtain ⟨p⟩ := Cconn e ⟨x,hx⟩ ⟨y,hy⟩
    obtain ⟨D,hDC,hxD,hdt,hD,htouch⟩ := before_target G p hxt hyt
    exact ⟨D,hDC,⟨x,hxD,hxs⟩,hdt,hD,htouch⟩
  choose D sub inter avoid conn bridge using expandBranch
  let R (v : V) := B v ∪ ⋃ e : {e // s e = v}, D e.val
  have Bsub (v : V) : B v ⊆ R v := Set.subset_union_left
  have Dsub (e : E) : D e ⊆ R (s e) := fun x hx => Or.inr (Set.mem_iUnion.mpr ⟨⟨e,rfl⟩,hx⟩)
  have avoid' (e : E) (v : V) (h : s e ≠ v) : Disjoint (D e) (B v) := by
    by_cases ht : t e = v
    · exact ht ▸ avoid e
    · apply Disjoint.mono_left (sub e)
      by_contra! hh
      exact ((touch e v).mp hh).elim h ht
  refine ⟨R,?_,?_,?_⟩
  · intro v
    refine ⟨(Bfin v).union (Set.finite_iUnion fun e => (Cfin e.val).subset (sub e.val)),
      (Bne v).mono (Bsub v),?_⟩
    obtain ⟨a,ha⟩ := Bne v
    have reaches (p : R v) : (G.induce (R v)).Reachable ⟨a,Bsub v ha⟩ p := by
      rcases p with ⟨p,hp | hp⟩
      · exact patches_reach (Bsub v) (Bconn v ⟨a,ha⟩ ⟨p,hp⟩)
      · obtain ⟨⟨e,rfl⟩,he⟩ := Set.mem_iUnion.mp hp
        obtain ⟨d,hd,hb⟩ := inter e
        exact (patches_reach (Bsub _) (Bconn _ ⟨a,ha⟩ ⟨d,hb⟩)).trans
          (patches_reach (Dsub e) (conn e ⟨d,hd⟩ ⟨p,he⟩))
    exact fun p q => (reaches p).symm.trans (reaches q)
  · intro v w hvw
    apply Set.disjoint_left.mpr
    rintro x (hx | hx) (hy | hy)
    · exact Set.disjoint_left.mp (BB _ _ hvw) hx hy
    · obtain ⟨⟨e,he⟩,hy'⟩ := Set.mem_iUnion.mp hy
      exact Set.disjoint_left.mp (avoid' e v (he ▸ hvw.symm)) hy' hx
    · obtain ⟨⟨e,he⟩,hx'⟩ := Set.mem_iUnion.mp hx
      exact Set.disjoint_left.mp (avoid' e w (he ▸ hvw)) hx' hy
    · obtain ⟨⟨e,he⟩,hx'⟩ := Set.mem_iUnion.mp hx
      obtain ⟨⟨f,hf⟩,hy'⟩ := Set.mem_iUnion.mp hy
      have hef : e ≠ f := fun h => hvw (he.symm.trans ((congrArg s h).trans hf))
      exact Set.disjoint_left.mp (CC _ _ hef) (sub _ hx') (sub _ hy')
  · intro e
    obtain ⟨x,hx,y,hy,h⟩ := bridge e
    exact ⟨x,Dsub e hx,y,Bsub _ hy,h⟩

/-- An undirected grid adjacency has a canonical horizontal or vertical orientation. -/
lemma grid_arrow {x y : GridPoint} (h : squareGrid.Adj x y) :
    (∃ d, gridTail d = x ∧ gridHead d = y) ∨ (∃ d, gridTail d = y ∧ gridHead d = x) := by
  obtain ⟨i,j⟩ := x
  obtain ⟨k,m⟩ := y
  rcases h with ⟨h,hd⟩ | ⟨h,hd⟩
  · change i = k at h
    subst k
    change |j - m| = 1 at hd
    rcases abs_choice (j-m) with hab | hab
    · exact Or.inr ⟨.inr (i,j),Prod.ext rfl (by dsimp [gridTail]; omega),rfl⟩
    · exact Or.inl ⟨.inr (i,m),Prod.ext rfl (by dsimp [gridTail]; omega),rfl⟩
  · change j = m at h
    subst m
    change |i - k| = 1 at hd
    rcases abs_choice (i-k) with hab | hab
    · exact Or.inr ⟨.inl (i,j),Prod.ext (by dsimp [gridTail]; omega) rfl,rfl⟩
    · exact Or.inl ⟨.inl (k,j),Prod.ext (by dsimp [gridTail]; omega) rfl,rfl⟩

/-- Construct the finite grid minor from the branch-set formulation. The orientation of
    each selected bridge follows the canonical orientation of its lattice edge. -/
theorem grid_branch_bound [DecidableEq V] [Fintype V] [Fintype E] (s t : E → V)
    (hne : ∀ e, s e ≠ t e) (simple : Function.Injective (fun e => ({s e,t e} : Finset V)))
    (R : V → Set GridPoint)
    (Rprop : ∀ v, (R v).Finite ∧ (R v).Nonempty ∧ (squareGrid.induce (R v)).Preconnected)
    (Rdis : ∀ v w, v ≠ w → Disjoint (R v) (R w))
    (bridge : ∀ e, ∃ x ∈ R (s e), ∃ y ∈ R (t e), squareGrid.Adj x y) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  classical
  let (v : V) : Fintype (R v) := (Rprop v).1.fintype
  let W := (v : V) × R v
  let pos (w : W) : GridPoint := w.2.val
  have posinj : Function.Injective pos := by
    rintro ⟨v,x⟩ ⟨w,y⟩ he
    have hvw : v = w := by
      by_contra h
      exact Set.disjoint_left.mp (Rdis _ _ h) x.property ((show x.val = y.val from he) ▸ y.property)
    subst w
    exact congrArg (Sigma.mk v) (Subtype.ext he)
  have chooseBridge (e : E) : ∃ (a b : W) (d : GridEdge),
      (a.1 = s e ∧ b.1 = t e ∨ a.1 = t e ∧ b.1 = s e) ∧
      gridTail d = pos a ∧ gridHead d = pos b := by
    obtain ⟨x,hx,y,hy,hxy⟩ := bridge e
    rcases grid_arrow hxy with ⟨d,hd1,hd2⟩ | ⟨d,hd1,hd2⟩
    · exact ⟨⟨_,x,hx⟩,⟨_,y,hy⟩,d,Or.inl ⟨rfl,rfl⟩,hd1,hd2⟩
    · exact ⟨⟨_,y,hy⟩,⟨_,x,hx⟩,d,Or.inr ⟨rfl,rfl⟩,hd1,hd2⟩
  choose a b d owners tail head using chooseBridge
  have pairEq (e : E) : ({(a e).1,(b e).1} : Finset V) = {s e,t e} := by
    rcases owners e with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simp [ha,hb]
    · rw [ha,hb,Finset.pair_comm]
  have distinct (e : E) : (a e).1 ≠ (b e).1 := by
    rcases owners e with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa [ha,hb] using hne e
    · simpa [ha,hb] using (hne e).symm
  let J := {p : W × W // p.1.1 = p.2.1 ∧ ∃ k, gridTail k = pos p.1 ∧ gridHead k = pos p.2}
  have hJ (j : J) := j.property.2
  choose d' jt jh using hJ
  let src : E ⊕ J → W := Sum.elim a (fun j => j.val.1)
  let dst : E ⊕ J → W := Sum.elim b (fun j => j.val.2)
  let key : E ⊕ J → GridEdge := Sum.elim d d'
  have T (k : E ⊕ J) : gridTail (key k) = pos (src k) := by
    rcases k with e | j
    · exact tail e
    · exact jt j
  have H (k : E ⊕ J) : gridHead (key k) = pos (dst k) := by
    rcases k with e | j
    · exact head e
    · exact jh j
  have inj : Function.Injective key := by
    intro k k' he
    have hs := posinj ((T k).symm.trans ((congrArg gridTail he).trans (T k')))
    have ht := posinj ((H k).symm.trans ((congrArg gridHead he).trans (H k')))
    rcases k with e | j <;> rcases k' with f | i
    · apply congrArg Sum.inl
      apply simple
      exact (pairEq e).symm.trans ((congrArg₂ (fun x y : W => ({x.1,y.1} : Finset V)) hs ht).trans
        (pairEq f))
    · exfalso
      exact distinct e ((congrArg Sigma.fst hs).trans (i.property.1.trans (congrArg Sigma.fst ht).symm))
    · exfalso
      exact distinct f ((congrArg Sigma.fst hs).symm.trans (j.property.1.trans (congrArg Sigma.fst ht)))
    · exact congrArg Sum.inr (Subtype.ext (Prod.ext hs ht))
  let anchor (v : V) : W := ⟨v, Classical.choose (Rprop v).2.1, Classical.choose_spec (Rprop v).2.1⟩
  let rel (x y : W) := ∃ j : J, src (.inr j) = x ∧ dst (.inr j) = y
  have step {v : V} {x y : R v} (adj : (squareGrid.induce (R v)).Adj x y) :
      Relation.EqvGen rel (⟨v,x⟩ : W) ⟨v,y⟩ := by
    rcases grid_arrow adj with h | h
    · exact .rel _ _ ⟨⟨(⟨v,x⟩,⟨v,y⟩),rfl,h⟩,rfl,rfl⟩
    · exact .symm _ _ (.rel _ _ ⟨⟨(⟨v,y⟩,⟨v,x⟩),rfl,h⟩,rfl,rfl⟩)
  have joins {v : V} {x y : R v} (p : (squareGrid.induce (R v)).Walk x y) :
      Relation.EqvGen rel (⟨v,x⟩ : W) ⟨v,y⟩ := by
    induction p with
    | nil => exact .refl _
    | cons adj _ ih => exact .trans _ _ _ (step adj) ih
  apply euler_grid_minor src dst pos posinj key inj (funext T) (funext H) Sigma.fst anchor
    (fun j => j.property.1) _ distinct
  · intro e f he
    exact simple ((pairEq e).symm.trans (he.trans (pairEq f)))
  · rintro ⟨v,w⟩
    obtain ⟨p⟩ := (Rprop v).2.2 (anchor v).2 w
    exact joins p

open scoped EuclideanGeometry

/-- The Euler edge bound directly in terms of disjoint compact connected Euclidean patches
    and disjoint compact connected edge corridors with the prescribed incidence relation. -/
theorem grid_patch_bound [DecidableEq V] [Fintype V] [Fintype E] (s t : E → V)
    (hne : ∀ e, s e ≠ t e) (simple : Function.Injective (fun e => ({s e,t e} : Finset V)))
    (B : V → Set ℝ²) (C : E → Set ℝ²)
    (Bprop : ∀ v, (B v).Nonempty ∧ IsCompact (B v) ∧ IsPreconnected (B v))
    (Cprop : ∀ e, IsCompact (C e) ∧ IsPreconnected (C e))
    (BB : ∀ v w, v ≠ w → Disjoint (B v) (B w)) (CC : ∀ e f, e ≠ f → Disjoint (C e) (C f))
    (touch : ∀ e v, ¬Disjoint (C e) (B v) ↔ s e = v ∨ t e = v) :
    Fintype.card E ≤ 3 * Fintype.card V := by
  let K : V ⊕ E → Set ℝ² := Sum.elim B C
  obtain ⟨A,info,dis⟩ := plane_grid_realization K
    (fun i => by cases i with | inl v => exact (Bprop v).2.1 | inr e => exact (Cprop e).1)
    (fun i => by cases i with | inl v => exact (Bprop v).2.2 | inr e => exact (Cprop e).2)
  have nonempty (v : V) : (A (.inl v)).Nonempty := by
    by_contra! hn
    have hD := (dis (.inl v) (.inl v)).mp (by simp [hn])
    exact (Bprop v).1.ne_empty (disjoint_self.mp hD)
  obtain ⟨R,hR,hdis,hbridge⟩ := shrink_connectors squareGrid s t hne (A ∘ Sum.inl) (A ∘ Sum.inr)
    (fun v => (info (.inl v)).1) (fun e => (info (.inr e)).1) nonempty
    (fun v => (info (.inl v)).2) (fun e => (info (.inr e)).2)
    (fun v w h => (dis _ _).mpr (BB v w h)) (fun e f h => (dis _ _).mpr (CC e f h))
    (fun e v => (not_congr (dis (.inr e) (.inl v))).trans (touch e v))
  exact grid_branch_bound s t hne simple R hR hdis hbridge

end OMA.Grid652

/- Splitting a finite plane drawing into disjoint vertex stars and the
middle thirds of its arcs, with exactly the original incidence relation. -/
namespace OMA.Grid652
open Set
open scoped EuclideanGeometry Classical

private noncomputable def loCut : unitInterval := ⟨1/3, by constructor <;> norm_num⟩
private noncomputable def hiCut : unitInterval := ⟨2/3, by constructor <;> norm_num⟩

private lemma cuts : (0 : unitInterval) < loCut ∧ loCut < hiCut ∧ hiCut < 1 := by
  change (0:ℝ) < 1/3 ∧ (1:ℝ)/3 < 2/3 ∧ (2:ℝ)/3 < 1
  norm_num

private structure DrawArc (Q : Finset ℝ²) where
  src : Q
  dst : Q
  path : Path (src : ℝ²) (dst : ℝ²)
  inj : Function.Injective path
  vertex : ∀ (v : Q), (v : ℝ²) ∈ range path → v = src ∨ v = dst

private def DrawArc.tip {Q} (d : DrawArc Q) : Bool → Q
  | false => d.src
  | true => d.dst

private def outerTimes : Bool → Set unitInterval
  | false => Icc 0 loCut
  | true => Icc hiCut 1

private def DrawArc.outer {Q} (d : DrawArc Q) (b : Bool) : Set ℝ² :=
  d.path '' outerTimes b

private def DrawArc.middle {Q} (d : DrawArc Q) : Set ℝ² :=
  d.path '' Icc loCut hiCut

private lemma DrawArc.outer_props {Q} (d : DrawArc Q) (b : Bool) :
    (d.tip b : ℝ²) ∈ d.outer b ∧ IsCompact (d.outer b) ∧ IsPreconnected (d.outer b) := by
  cases b
  · exact ⟨⟨0, ⟨le_rfl, cuts.1.le⟩, d.path.source⟩, isCompact_Icc.image d.path.continuous,
      isPreconnected_Icc.image _ d.path.continuous.continuousOn⟩
  · exact ⟨⟨1, ⟨cuts.2.2.le, le_rfl⟩, d.path.target⟩, isCompact_Icc.image d.path.continuous,
      isPreconnected_Icc.image _ d.path.continuous.continuousOn⟩

private lemma DrawArc.outer_vertex {Q} (d : DrawArc Q) (b : Bool) (v : Q)
    (h : (v : ℝ²) ∈ d.outer b) : v = d.tip b := by
  obtain ⟨t, ht, hv⟩ := h
  rcases d.vertex v ⟨t, hv⟩ with hx | hy
  · cases b
    · exact hx
    · have he : t = 0 := d.inj (hv.trans ((congrArg Subtype.val hx).trans d.path.source.symm))
      have hle : hiCut ≤ 0 := he ▸ ht.1
      exact ((cuts.1.trans cuts.2.1).not_ge hle).elim
  · cases b
    · have he : t = 1 := d.inj (hv.trans ((congrArg Subtype.val hy).trans d.path.target.symm))
      have hle : 1 ≤ loCut := he ▸ ht.2
      exact ((cuts.2.1.trans cuts.2.2).not_ge hle).elim
    · exact hy

private lemma DrawArc.middle_avoids {Q} (d : DrawArc Q) (v : Q) :
    (v : ℝ²) ∉ d.middle := by
  rintro ⟨t, ht, hv⟩
  rcases d.vertex v ⟨t, hv⟩ with hx | hy
  · have he : t = 0 := d.inj (hv.trans ((congrArg Subtype.val hx).trans d.path.source.symm))
    exact cuts.1.not_ge (he ▸ ht.1)
  · have he : t = 1 := d.inj (hv.trans ((congrArg Subtype.val hy).trans d.path.target.symm))
    exact cuts.2.2.not_ge (he ▸ ht.2)

private lemma DrawArc.side_unique {Q} (d : DrawArc Q) {b c : Bool} {z : ℝ²}
    (hb : z ∈ d.outer b) (hc : z ∈ d.outer c) : b = c := by
  obtain ⟨t, ht, rfl⟩ := hb
  obtain ⟨u, hu, he⟩ := hc
  have := d.inj he
  subst u
  cases b <;> cases c
  · rfl
  · exact (cuts.2.1.not_ge (le_trans hu.1 ht.2)).elim
  · exact (cuts.2.1.not_ge (le_trans ht.1 hu.2)).elim
  · rfl

private lemma DrawArc.middle_meets {Q} (d : DrawArc Q) (b : Bool) :
    (d.middle ∩ d.outer b).Nonempty := by
  cases b
  · exact ⟨d.path loCut, ⟨loCut, ⟨le_rfl, cuts.2.1.le⟩, rfl⟩,
      ⟨loCut, ⟨cuts.1.le, le_rfl⟩, rfl⟩⟩
  · exact ⟨d.path hiCut, ⟨hiCut, ⟨cuts.2.1.le, le_rfl⟩, rfl⟩,
      ⟨hiCut, ⟨le_rfl, cuts.2.2.le⟩, rfl⟩⟩

/-- Each branch set consists of its vertex and the adjacent outer thirds. Each
connector is a middle third. The compact pieces can then be rasterized jointly. -/
theorem split_drawing (Q : Finset ℝ²) (S : Finset Q) (E : Finset ℕ)
    (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²)
    (hd : ∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
      ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = range γ ∧
        ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i)
    (hcross : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → curve i ∩ curve j ⊆
      Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) :
    ∃ (B : S → Set ℝ²) (C : E → Set ℝ²),
      (∀ v, (B v).Nonempty ∧ IsCompact (B v) ∧ IsPreconnected (B v)) ∧
      (∀ e, IsCompact (C e) ∧ IsPreconnected (C e)) ∧
      (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ e f, e ≠ f → Disjoint (C e) (C f)) ∧
      (∀ e v, ¬ Disjoint (C e) (B v) ↔ v.val ∈ edge e.val) := by
  classical
  have arcs (e : E) : ∃ d : DrawArc Q, edge e.val = {d.src,d.dst} ∧
      curve e.val = range d.path := by
    obtain ⟨x,y,_,hed,γ,hi,hγ,hv⟩ := hd e e.2
    refine ⟨⟨x,y,γ,hi,fun v h => ?_⟩, hed, hγ⟩
    simpa only [hed, Finset.mem_insert, Finset.mem_singleton] using hv v (hγ ▸ h)
  choose d ends full using arcs
  have crossing {e f : E} (hef : e ≠ f) {z : ℝ²} (he : z ∈ range (d e).path)
      (hf : z ∈ range (d f).path) : ∃ v : Q, (v : ℝ²) = z := by
    have h := hcross e e.2 f f.2 (fun h => hef (Subtype.ext h))
      ⟨(full e).symm ▸ he, (full f).symm ▸ hf⟩
    exact ⟨h.choose,h.choose_spec.2⟩
  let tips (v : S) := {p : E × Bool // (d p.1).tip p.2 = v.val}
  let part (v : S) : Option (tips v) → Set ℝ²
    | none => {(v.val : ℝ²)}
    | some p => (d p.val.1).outer p.val.2
  let B (v : S) := ⋃ k, part v k
  have piece (v : S) (k : Option (tips v)) :
      (v.val : ℝ²) ∈ part v k ∧ IsCompact (part v k) ∧ IsPreconnected (part v k) := by
    cases k with
    | none => exact ⟨mem_singleton _, isCompact_singleton, isPreconnected_singleton⟩
    | some p => simpa only [part, ← p.property] using (d p.val.1).outer_props p.val.2
  have memB {v : S} {z : ℝ²} (h : z ∈ B v) :
      z = (v.val : ℝ²) ∨ ∃ e b, (d e).tip b = v.val ∧ z ∈ (d e).outer b := by
    obtain ⟨k,hk⟩ := mem_iUnion.mp h
    cases k with
    | none => exact Or.inl hk
    | some p => exact Or.inr ⟨_,_,p.property,hk⟩
  have vertexB {v : S} (x : Q) (h : (x : ℝ²) ∈ B v) : x = v.val := by
    rcases memB h with hx | ⟨e,b,ht,hx⟩
    · exact Subtype.ext hx
    · exact ((d e).outer_vertex b x hx).trans ht
  have wholeOuter {e : E} {b z} (h : z ∈ (d e).outer b) : z ∈ range (d e).path :=
    ⟨h.choose, h.choose_spec.2⟩
  have wholeMiddle {e : E} {z} (h : z ∈ (d e).middle) : z ∈ range (d e).path :=
    ⟨h.choose, h.choose_spec.2⟩
  refine ⟨B,fun e => (d e).middle, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact ⟨⟨_,mem_iUnion.mpr ⟨none,(piece v none).1⟩⟩,
      isCompact_iUnion (fun k => (piece v k).2.1),
      isPreconnected_iUnion ⟨_,mem_iInter.mpr (fun k => (piece v k).1)⟩
        (fun k => (piece v k).2.2)⟩
  · exact fun e => ⟨isCompact_Icc.image (d e).path.continuous,
      isPreconnected_Icc.image _ (d e).path.continuous.continuousOn⟩
  · intro v w hne
    apply disjoint_left.mpr
    intro z hv hw
    apply hne
    apply Subtype.ext
    rcases memB hv with rfl | ⟨e,b,ht,he⟩
    · exact vertexB _ hw
    rcases memB hw with rfl | ⟨f,c,hu,hf⟩
    · exact (vertexB _ hv).symm
    by_cases h : e = f
    · subst f
      rw [← ht, ← hu, (d e).side_unique he hf]
    · obtain ⟨x,rfl⟩ := crossing h (wholeOuter he) (wholeOuter hf)
      exact (vertexB x hv).symm.trans (vertexB x hw)
  · intro e f hne
    apply disjoint_left.mpr
    intro z he hf
    obtain ⟨x,rfl⟩ := crossing hne (wholeMiddle he) (wholeMiddle hf)
    exact (d e).middle_avoids x he
  · intro e v
    constructor
    · intro hn
      obtain ⟨z, he, hv⟩ := not_disjoint_iff.mp hn
      rcases memB hv with rfl | ⟨f,b,ht,hf⟩
      · exact ((d e).middle_avoids _ he).elim
      by_cases h : e = f
      · subst f
        rw [ends, ← ht]
        cases b <;> simp [DrawArc.tip]
      · obtain ⟨x,rfl⟩ := crossing h (wholeMiddle he) (wholeOuter hf)
        exact ((d e).middle_avoids x he).elim
    · intro hv
      have side : ∃ b, (d e).tip b = v.val := by
        rw [ends, Finset.mem_insert, Finset.mem_singleton] at hv
        exact hv.elim (fun h => ⟨false,h.symm⟩) (fun h => ⟨true,h.symm⟩)
      obtain ⟨b,hb⟩ := side
      obtain ⟨z,hz,hleg⟩ := (d e).middle_meets b
      exact not_disjoint_iff.mpr ⟨z,hz,mem_iUnion.mpr ⟨some (⟨(e,b),hb⟩ : tips v),hleg⟩⟩

end OMA.Grid652

namespace OMA.Grid652
open Set
open scoped EuclideanGeometry Classical

theorem plane_drawing_bound (Q : Finset ℝ²) (S : Finset Q) (E : Finset ℕ)
    (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²)
    (hd : ∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
      ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = range γ ∧
        ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i)
    (inside : ∀ i ∈ E, edge i ⊆ S) (inj : Set.InjOn edge (E : Set ℕ))
    (cross : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → curve i ∩ curve j ⊆
      Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) : E.card ≤ 3 * S.card := by
  classical
  have ep (e : E) : ∃ s t : S, s ≠ t ∧ edge e.val = {s.val,t.val} := by
    obtain ⟨x,y,hne,hed,_⟩ := hd e e.2
    have hx := inside e e.2 (show x ∈ edge e.val by simp [hed])
    have hy := inside e e.2 (show y ∈ edge e.val by simp [hed])
    exact ⟨⟨x,hx⟩,⟨y,hy⟩,fun h => hne (congrArg Subtype.val h),hed⟩
  choose s t hne hed using ep
  have simple : Function.Injective (fun e => ({s e,t e} : Finset S)) := by
    intro e f h
    apply Subtype.ext
    apply inj e.2 f.2
    rw [hed e, hed f]
    simpa using congrArg (Finset.image (Subtype.val : S → Q)) h
  obtain ⟨B,C,hB,hC,hBB,hCC,ht⟩ := split_drawing Q S E edge curve hd cross
  have touch (e : E) (v : S) : ¬ Disjoint (C e) (B v) ↔ s e = v ∨ t e = v := by
    rw [ht, hed e, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.imp (fun h => Subtype.ext h.symm) (fun h => Subtype.ext h.symm)
    · exact fun h => h.imp (fun h => congrArg Subtype.val h.symm) (fun h => congrArg Subtype.val h.symm)
  simpa using grid_patch_bound s t hne simple B C hB hC hBB hCC touch

end OMA.Grid652

end


namespace OMA.Crossing

open Finset

private theorem samples_containing {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (A : Finset V) :
    (univ.filter (fun f : V → Fin (r+1) => A ⊆ (univ.filter (fun v => f v = 0)))).card =
      (r+1)^(Fintype.card V-A.card) := by
  classical
  let t (v : V) : Finset (Fin (r+1)) := if v ∈ A then {0} else univ
  have he : univ.filter (fun f : V → Fin (r+1) => A ⊆ (univ.filter (fun v => f v = 0))) = Fintype.piFinset t := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h v
      by_cases hv : v ∈ A
      · have hv' := h hv
        simpa [t,hv] using hv'
      · simp [t,hv]
    · intro h v hv
      have hv' := h v
      simpa [t,hv] using hv'
  rw [he, Fintype.card_piFinset]
  have hc (v : V) : (t v).card = if v ∈ A then 1 else r+1 := by
    by_cases hv : v ∈ A <;> simp [t,hv]
  simp_rw [hc]
  rw [prod_ite]
  simp [show (univ.filter fun v => v ∉ A) = Aᶜ by ext; simp, card_compl]

private theorem sum_surviving {V α : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (E : Finset α) (verts : α → Finset V) (hj : ∀ e ∈ E, (verts e).card = j) :
    ∑ f : V → Fin (r+1), (E.filter (fun e => verts e ⊆ (univ.filter (fun v => f v = 0)))).card =
      E.card * (r+1)^(Fintype.card V-j) := by
  classical
  calc
    _ = ∑ e ∈ E, (univ.filter (fun f : V → Fin (r+1) => verts e ⊆ (univ.filter (fun v => f v = 0)))).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := (univ : Finset (V → Fin (r+1)))) (t := E)
        (fun (f : V → Fin (r+1)) (e : α) => verts e ⊆ univ.filter (fun v => f v = 0))
    _ = _ := by
      simp only [samples_containing]
      rw [sum_congr rfl (fun e he => by rw [hj e he])]
      simp

/-- Suppose every induced subdrawing satisfies the linear planarization inequality:
the number of surviving edges is at most three times the vertices plus the surviving
crossings. For edges supported on pairs and crossings supported on four distinct vertices,
sampling a 1/r fraction of the vertices amplifies this to a cubic crossing bound. -/
theorem sample_crossing_bound {V α β : Type*} [Fintype V] [DecidableEq V]
    (E : Finset α) (C : Finset β) (edge : α → Finset V) (cross : β → Finset V)
    (he : ∀ e ∈ E, (edge e).card = 2) (hc : ∀ c ∈ C, (cross c).card = 4)
    (hV : 4 ≤ Fintype.card V)
    (planar : ∀ S : Finset V, (E.filter (fun e => edge e ⊆ S)).card ≤
        3 * S.card + (C.filter (fun c => cross c ⊆ S)).card)
    (r : ℕ) (hr : 1 ≤ r) :
    E.card * r^2 ≤ 3 * Fintype.card V * r^3 + C.card := by
  classical
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  let n := Fintype.card V
  have h := sum_le_sum (s := (univ : Finset (V → Fin (r+1)))) (fun f _ => planar ((univ.filter (fun v => f v = 0))))
  have hvertex (f : V → Fin (r+1)) :
      (univ.filter (fun e : V => ({e} : Finset V) ⊆ (univ.filter (fun v => f v = 0)))).card = ((univ.filter (fun v => f v = 0))).card := by simp
  have hvertices := sum_surviving (V := V) r 1 univ (fun e : V => {e}) (by simp)
  simp_rw [hvertex,card_univ] at hvertices
  rw [sum_add_distrib, ← mul_sum, hvertices, sum_surviving _ _ _ _ he, sum_surviving _ _ _ _ hc] at h
  have hpow (j : ℕ) (hj : j ≤ 4) :
      (r+1)^(Fintype.card V-j) = (r+1)^(4-j) * (r+1)^(Fintype.card V-4) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow 2 (by decide), hpow 1 (by decide)] at h
  norm_num at h
  apply Nat.le_of_mul_le_mul_right _ (pow_pos (by omega : 0 < r+1) (n-4))
  simpa only [n, Nat.succ_eq_add_one, add_mul, mul_assoc] using h

/-- A drawing with at least 12 edges per vertex and the planarization inequality
has at least e³/(288 v²) crossings. -/
theorem cubic_crossing_bound {V α β : Type*} [Fintype V] [DecidableEq V]
    (E : Finset α) (C : Finset β) (edge : α → Finset V) (cross : β → Finset V)
    (he : ∀ e ∈ E, (edge e).card = 2) (hc : ∀ c ∈ C, (cross c).card = 4)
    (hV : 4 ≤ Fintype.card V) (hdense : 12 * Fintype.card V ≤ E.card)
    (planar : ∀ S : Finset V, (E.filter (fun e => edge e ⊆ S)).card ≤
        3 * S.card + (C.filter (fun c => cross c ⊆ S)).card) :
    E.card^3 ≤ 288 * (Fintype.card V)^2 * C.card := by
  let n := Fintype.card V
  let r := E.card / (6*n)
  have hn : 0 < n := by dsimp [n]; omega
  have hr : 1 ≤ r := (Nat.le_div_iff_mul_le (by omega)).mpr (by dsimp [n] at *; omega)
  have hsplit := sample_crossing_bound E C edge cross he hc hV planar r hr
  have hu : r * (6*n) ≤ E.card := Nat.div_mul_le_self _ _
  have hq : E.card ≤ 12*n*r := by
    have hlt : E.card < (r+1)*(6*n) := (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self r)
    have hrr : r+1 ≤ 2*r := by omega
    exact hlt.le.trans ((Nat.mul_le_mul_right _ hrr).trans_eq (by ring))
  have hcross : E.card*r^2 ≤ 2*C.card := by
    change E.card * r^2 ≤ 3*n*r^3 + C.card at hsplit
    nlinarith only [hsplit, Nat.mul_le_mul_right (r^2) hu]
  calc
    E.card^3 = E.card^2 * E.card := by ring
    _ ≤ (12*n*r)^2 * E.card := by gcongr
    _ = (144*n^2) * (E.card*r^2) := by ring
    _ ≤ (144*n^2) * (2*C.card) := Nat.mul_le_mul_left _ hcross
    _ = _ := by change _ = 288*n^2*C.card; ring

end OMA.Crossing


/- The balanced incidence bound for a family of simple intervals in the plane
where any two carriers intersect in at most one point. -/
namespace OMA.Pseudo1085
open Finset
open scoped EuclideanGeometry Classical

structure Arc where
  point : ℝ → ℝ²
  lo : ℝ
  hi : ℝ
  continuous : Continuous point
  inj : Set.InjOn point (Set.Icc lo hi)

def Arc.carrier (p : Arc) := p.point '' Set.Icc p.lo p.hi

noncomputable def neighbors (Q : Finset ℝ²) (p : Arc) := Q.filter (· ∈ p.carrier)

structure Chain (Q : Finset ℝ²) (p : Arc) where
  n : ℕ
  param : Fin (n+1) ↪o ℝ
  dom : ∀ i, param i ∈ Set.Icc p.lo p.hi
  vertex_mem : ∀ i, p.point (param i) ∈ neighbors Q p
  covers : ∀ x ∈ neighbors Q p, ∃ i, p.point (param i) = x

private noncomputable def build (Q : Finset ℝ²) (p : Arc) (hpos : 0 < (neighbors Q p).card) :
    {A : Chain Q p // A.n+1 = (neighbors Q p).card} := by
  apply Classical.choice
  let U := neighbors Q p
  have rep (x : U) : ∃ u ∈ Set.Icc p.lo p.hi, p.point u = x.val := (mem_filter.mp x.property).2
  let t (x : U) := (rep x).choose
  have td (x : U) := (rep x).choose_spec.1
  have ht (x : U) : p.point (t x)=x.val := (rep x).choose_spec.2
  have inj : Function.Injective t := fun x y h => Subtype.ext ((ht x).symm.trans ((congrArg p.point h).trans (ht y)))
  let F := (univ : Finset U).image t
  have count : F.card = U.card := (card_image_of_injective _ inj).trans (by simp)
  let m := U.card-1
  have hm : m+1=U.card := by change 0 < U.card at hpos; dsimp [m]; omega
  let θ := F.orderEmbOfFin (count.trans hm.symm)
  have origin (i : Fin (m+1)) : ∃ x : U, t x=θ i := by
    obtain ⟨x,_,hx⟩ := mem_image.mp (F.orderEmbOfFin_mem (count.trans hm.symm) i)
    exact ⟨x,hx⟩
  refine ⟨⟨⟨m,θ,?_,?_,?_⟩,hm⟩⟩
  · intro i; obtain ⟨x,h⟩ := origin i; exact h ▸ td x
  · intro i; obtain ⟨x,h⟩ := origin i; rw [←h,ht]; exact x.property
  · intro x hx
    let v : U := ⟨x,hx⟩
    have hf : t v ∈ F := mem_image.mpr ⟨v,mem_univ _,rfl⟩
    obtain ⟨i,hi⟩ := (F.orderIsoOfFin (count.trans hm.symm)).surjective ⟨t v,hf⟩
    exact ⟨i,(congrArg p.point (congrArg Subtype.val hi)).trans (ht v)⟩

namespace Chain
variable {Q : Finset ℝ²} {p : Arc} (A : Chain Q p)

noncomputable def pt (i : Fin (A.n+1)) : Q :=
  ⟨_,(mem_filter.mp (A.vertex_mem i)).1⟩

noncomputable def edge (i : Fin A.n) : Finset Q := {A.pt i.castSucc, A.pt i.succ}

noncomputable def path (i : Fin A.n) : Path (A.pt i.castSucc : ℝ²) (A.pt i.succ : ℝ²) :=
  (Path.segment (A.param i.castSucc) (A.param i.succ)).map (p.continuous)

def curve (i : Fin A.n) : Set ℝ² := Set.range (A.path i)

theorem pt_inj : Function.Injective A.pt :=
  fun _ _ h => A.param.injective (p.inj (A.dom _) (A.dom _) (congrArg Subtype.val h))

theorem ends_ne (i : Fin A.n) : A.pt i.castSucc ≠ A.pt i.succ :=
  fun e => Fin.castSucc_lt_succ.ne (A.pt_inj e)

theorem edge_card (i : Fin A.n) : (A.edge i).card = 2 := by simp [edge,A.ends_ne]

private theorem dom_edge (i : Fin A.n) {r : ℝ} (hr : r ∈ Set.Icc (A.param i.castSucc) (A.param i.succ)) :
    r ∈ Set.Icc p.lo p.hi := ⟨(A.dom _).1.trans hr.1,hr.2.trans (A.dom _).2⟩

theorem path_inj (i : Fin A.n) : Function.Injective (A.path i) := by
  let γ := Path.segment (A.param i.castSucc) (A.param i.succ)
  have dom (u : unitInterval) : γ u ∈ Set.Icc p.lo p.hi := by
    apply A.dom_edge i
    have hr : γ u ∈ Set.range γ := ⟨u,rfl⟩
    rwa [show Set.range γ = _ from Path.range_segment ..,segment_eq_Icc (A.param.monotone Fin.castSucc_lt_succ.le)] at hr
  intro x y h
  exact Path.segment_injective_of_ne (A.param.strictMono Fin.castSucc_lt_succ).ne (p.inj (dom x) (dom y) h)

theorem asInterval (i : Fin A.n) :
    A.curve i = p.point '' Set.Icc (A.param i.castSucc) (A.param i.succ) := by
  change Set.range (p.point ∘ _) = _
  rw [Set.range_comp, Path.range_segment, segment_eq_Icc (A.param.monotone Fin.castSucc_lt_succ.le)]

theorem on (i : Fin A.n) {x : ℝ²} (hx : x ∈ A.curve i) : x ∈ p.carrier := by
  obtain ⟨r,hr,rfl⟩ := A.asInterval i ▸ hx
  exact ⟨r,A.dom_edge i hr,rfl⟩

theorem mem_iff (i : Fin A.n) (v : Q) : (v : ℝ²) ∈ A.curve i ↔ v ∈ A.edge i := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := A.covers v (mem_filter.mpr ⟨v.property,A.on i h⟩)
    obtain ⟨r,hr,he⟩ := A.asInterval i ▸ h
    obtain rfl : r = A.param j := p.inj (A.dom_edge i hr) (A.dom _) (he.trans hj.symm)
    have h₁ := A.param.le_iff_le.mp hr.1
    have h₂ := A.param.le_iff_le.mp hr.2
    have alleq : j = i.castSucc ∨ j = i.succ := by
      change i.val ≤ j.val at h₁
      change j.val ≤ i.val + 1 at h₂
      by_cases hj' : j.val = i.val
      · exact Or.inl (Fin.ext hj')
      · exact Or.inr (Fin.ext (by change j.val = i.val+1; omega))
    have e : A.pt j = v := Subtype.ext hj
    rcases alleq with rfl | rfl <;> simp [edge,← e]
  · intro h
    rcases mem_insert.mp h with rfl | h
    · exact ⟨0, (A.path i).source⟩
    obtain rfl := mem_singleton.mp h
    exact ⟨1, (A.path i).target⟩

theorem uniqueOutside {i j : Fin A.n} {x : ℝ²} (hx : x ∉ Q)
    (hi : x ∈ A.curve i) (hj : x ∈ A.curve j) : i = j := by
  obtain ⟨r,hr,rfl⟩ := A.asInterval i ▸ hi
  obtain ⟨s,hs,eq⟩ := A.asInterval j ▸ hj
  obtain rfl := p.inj (A.dom_edge j hs) (A.dom_edge i hr) eq
  have forbid {u v : Fin A.n} (hlt : u < v) (hu : s ≤ A.param u.succ)
      (hv : A.param v.castSucc ≤ s) : False := by
    have ord : A.param u.succ ≤ A.param v.castSucc := A.param.monotone (by simpa using hlt)
    have heq := le_antisymm hv (hu.trans ord)
    exact hx (heq ▸ (mem_filter.mp (A.vertex_mem v.castSucc)).1)
  rcases lt_trichotomy i j with h | h | h
  · exact (forbid h hr.2 hs.1).elim
  · exact h
  · exact (forbid h hs.2 hr.1).elim

theorem simple {i j : Fin A.n} (he : A.edge i = A.edge j) : i = j := by
  have low (u v : Fin A.n) (h : A.edge u = A.edge v) : v ≤ u := by
    have hh : A.pt u.castSucc ∈ A.edge v := h ▸ mem_insert_self _ _
    rcases mem_insert.mp hh with hh | hh
    · exact le_of_eq ((Fin.castSucc_inj.mp (A.pt_inj hh)).symm)
    · have hv := congrArg Fin.val (A.pt_inj (mem_singleton.mp hh))
      change u.val = v.val + 1 at hv
      exact Fin.le_def.mpr (by omega)
  exact le_antisymm (low j i he.symm) (low i j he)

end Chain
variable {ι : Type*} {Q : Finset ℝ²} {L : Finset ι} {C : ι → Arc}
  (A : (l : L) → Chain Q (C l.val))

private abbrev Tag := (l : L) × Fin (A l).n
private noncomputable abbrev endpoints (e : Tag A) := (A e.1).edge e.2
private abbrev carrier (e : Tag A) := (A e.1).curve e.2

def Separated {ι : Type*} (L : Finset ι) (C : ι → Arc) : Prop :=
  ∀ {a b : L}, a ≠ b → ∀ {x y}, x ∈ (C a).carrier → x ∈ (C b).carrier →
    y ∈ (C a).carrier → y ∈ (C b).carrier → x = y

private lemma tagged_simple (sep : Separated L C) : Function.Injective (endpoints A) := by
  rintro ⟨l,i⟩ ⟨r,j⟩ eq
  change (A l).edge i = (A r).edge j at eq
  have same : l = r := by
    by_contra h
    obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (show 1 < ((A l).edge i).card by rw [Chain.edge_card]; decide)
    have onl (v : Q) (hv : v ∈ (A l).edge i) : v.val ∈ (C l.val).carrier := (A l).on i (((A l).mem_iff i v).mpr hv)
    have onr (v : Q) (hv : v ∈ (A l).edge i) : v.val ∈ (C r.val).carrier := (A r).on j (((A r).mem_iff j v).mpr (eq ▸ hv))
    exact hxy (Subtype.ext (sep h
      (onl x hx) (onr x hx) (onl y hy) (onr y hy)))
  subst r
  obtain rfl := (A l).simple eq
  rfl

private noncomputable def bad : Finset (Tag A × Tag A) :=
  univ.filter fun e => e.1 ≠ e.2 ∧ ∃ z : ℝ², z ∉ Q ∧ z ∈ carrier A e.1 ∧ z ∈ carrier A e.2

private lemma centers_ne {a b : Tag A} (h : (a,b) ∈ bad A) : a.1 ≠ b.1 := by
  rcases a with ⟨l,i⟩; rcases b with ⟨r,j⟩
  obtain ⟨hne,z,hz,hi,hj⟩ := (mem_filter.mp h).2
  change l ≠ r
  rintro rfl
  have eq : i = j := (A l).uniqueOutside hz hi hj
  subst j
  exact hne rfl

private lemma bad_card (sep : Separated L C) : (bad A).card ≤ L.card^2 := by
  let code (u : bad A) : L × L := (u.val.1.1,u.val.2.1)
  have inj : Function.Injective code := by
    rintro ⟨⟨⟨l,i⟩,⟨r,j⟩⟩,hu⟩ ⟨⟨⟨l',i'⟩,⟨r',j'⟩⟩,hv⟩ eq
    obtain ⟨e₁,e₂⟩ : l = l' ∧ r = r' := Prod.mk.inj eq
    subst l'; subst r'
    obtain ⟨_,x,hx,hi,hj⟩ := (mem_filter.mp hu).2
    obtain ⟨_,y,hy,hi',hj'⟩ := (mem_filter.mp hv).2
    have hne : l ≠ r := centers_ne A hu
    obtain rfl := sep hne
      ((A l).on i hi) ((A r).on j hj) ((A l).on i' hi') ((A r).on j' hj')
    obtain rfl := (A l).uniqueOutside hy hi hi'
    obtain rfl := (A r).uniqueOutside hy hj hj'
    rfl
  simpa [sq] using Fintype.card_le_of_injective code inj

private lemma four (sep : Separated L C) {a b : Tag A} (hab : (a,b) ∈ bad A) :
    (endpoints A a ∪ endpoints A b).card = 4 := by
  obtain ⟨_,z,hz,ha,hb⟩ := (mem_filter.mp hab).2
  have hd : Disjoint (endpoints A a) (endpoints A b) := by
    refine disjoint_left.mpr fun v hv hw => ?_
    have e : (v : ℝ²) = z := sep (centers_ne A hab)
      ((A _).on a.2 (((A _).mem_iff a.2 v).mpr hv)) ((A _).on b.2 (((A _).mem_iff b.2 v).mpr hw))
      ((A _).on a.2 ha) ((A _).on b.2 hb)
    exact hz (e ▸ v.property)
  rw [card_union_of_disjoint hd,Chain.edge_card,Chain.edge_card]

theorem drawing (Q : Finset ℝ²) (L : Finset ι) (C : ι → Arc) (sep : Separated L C)
    (hpos : ∀ l : L, 0 < (neighbors Q (C l)).card) :
  ∃ (E : Finset ℕ) (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²) (C : Finset (ℕ × ℕ)),
  (∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
    ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = Set.range γ ∧
      ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i) ∧
  Set.InjOn edge (E : Set ℕ) ∧
  (∀ i ∈ E, ∀ j ∈ E, i ≠ j → (i,j) ∉ C → curve i ∩ curve j ⊆ Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) ∧
  (∀ ij ∈ C, (edge ij.1 ∪ edge ij.2).card = 4) ∧
  (∑ l : L, (neighbors Q ((‹ι → Arc›) l)).card) = E.card + L.card ∧ C.card ≤ L.card^2 := by
  let A (p : L) := (build Q (C p) (hpos p)).val
  have count (p : L) : (neighbors Q (C p)).card = (A p).n + 1 :=
    (build Q (C p) (hpos p)).property.symm
  let encode (e : Tag A) : ℕ := (Fintype.equivFin (Tag A) e).val
  have inj : Function.Injective encode := Fin.val_injective.comp (Fintype.equivFin _).injective
  let both := Prod.map encode encode
  let E := univ.image encode
  let C := (bad A).image both
  let edge := Function.extend encode (endpoints A) (fun _ => ∅)
  let curve := Function.extend encode (carrier A) (fun _ => ∅)
  have e_eq (x : Tag A) : edge (encode x) = endpoints A x := inj.extend_apply _ _ x
  have c_eq (x : Tag A) : curve (encode x) = carrier A x := inj.extend_apply _ _ x
  have hE : E.card = Fintype.card (Tag A) := (card_image_of_injective univ inj).trans card_univ
  refine ⟨E,edge,curve,C,?_,?_,?_,?_,?_,card_image_le.trans (bad_card A sep)⟩
  · intro i hi
    obtain ⟨⟨l,j⟩,_,rfl⟩ := mem_image.mp hi
    rw [e_eq,c_eq]
    exact ⟨_,_,(A l).ends_ne j,rfl,(A l).path j,(A l).path_inj j,rfl,fun v => ((A l).mem_iff j v).mp⟩
  · intro i hi j hj he
    obtain ⟨x,_,rfl⟩ := mem_image.mp hi
    obtain ⟨y,_,rfl⟩ := mem_image.mp hj
    rw [e_eq,e_eq] at he
    exact congrArg encode (tagged_simple A sep he)
  · intro i hi j hj hne he z hz
    obtain ⟨a,_,rfl⟩ := mem_image.mp hi
    obtain ⟨b,_,rfl⟩ := mem_image.mp hj
    obtain ⟨ha,hb⟩ := hz
    rw [c_eq] at ha hb
    have hzQ : z ∈ Q := by
      by_contra h
      exact he (mem_image.mpr ⟨(a,b),mem_filter.mpr ⟨mem_univ _,fun eq => hne (congrArg encode eq),z,h,ha,hb⟩,rfl⟩)
    refine ⟨⟨z,hzQ⟩,?_,rfl⟩
    rw [e_eq,e_eq]
    exact mem_inter.mpr ⟨((A a.1).mem_iff _ _).mp ha,((A b.1).mem_iff _ _).mp hb⟩
  · intro ij hij
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hij
    change (edge (encode a) ∪ edge (encode b)).card = 4
    rw [e_eq,e_eq]
    exact four A sep hab
  · rw [hE,Fintype.card_sigma]
    simp [count,sum_add_distrib]

/-- Removing the first edge of each crossing suffices for every induced subdrawing. -/
theorem induced_edges {Q : Finset ℝ²} (E : Finset ℕ) (edge : ℕ → Finset Q)
    (curve : ℕ → Set ℝ²) (C : Finset (ℕ × ℕ))
    (drawn : ∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
      ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = Set.range γ ∧
        ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i)
    (inj : Set.InjOn edge (E : Set ℕ))
    (meet : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → (i,j) ∉ C → curve i ∩ curve j ⊆ Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q))
    (S : Finset Q) : (E.filter (fun i => edge i ⊆ S)).card ≤ 3 * S.card +
      (C.filter (fun ij => edge ij.1 ∪ edge ij.2 ⊆ S)).card := by
  let F := E.filter (fun i => edge i ⊆ S)
  let K := C.filter (fun ij => edge ij.1 ∪ edge ij.2 ⊆ S)
  let G := F \ K.image Prod.fst
  have hsub {i} (hi : i ∈ G) : i ∈ F := (mem_sdiff.mp hi).1
  have hE {i} (hi : i ∈ G) : i ∈ E := (mem_filter.mp (hsub hi)).1
  have hgood : G.card ≤ 3 * S.card := by
    apply OMA.Grid652.plane_drawing_bound Q S G edge curve (fun i hi => drawn i (hE hi))
      (fun _ hi => (mem_filter.mp (hsub hi)).2) (fun _ hi _ hj eq => inj (hE hi) (hE hj) eq)
    intro i hi j hj hij
    apply meet i (hE hi) j (hE hj) hij
    intro hc
    exact (mem_sdiff.mp hi).2 (mem_image.mpr ⟨(i,j), mem_filter.mpr
      ⟨hc, union_subset (mem_filter.mp (hsub hi)).2 (mem_filter.mp (hsub hj)).2⟩, rfl⟩)
  calc F.card ≤ G.card + (K.image Prod.fst).card := card_le_card_sdiff_add_card
       _ ≤ 3 * S.card + K.card := Nat.add_le_add hgood card_image_le


noncomputable def incidences {ι : Type*} (Q : Finset ℝ²) (L : Finset ι) (C : ι → Arc) :=
  (L ×ˢ Q).filter (fun z => z.2 ∈ (C z.1).carrier)

/-- Székely's balanced incidence estimate in a common planar chart. -/
theorem balanced {ι : Type*} (Q : Finset ℝ²) (L : Finset ι) (family : ι → Arc)
    (sep : Separated L family) (n : ℕ) (hn : 1 ≤ n) (hQ : Q.card ≤ n) (hL : L.card ≤ n) :
    ((incidences Q L family).card : ℝ) ≤ 14*(n:ℝ)^(4/3:ℝ) := by
  classical
  let r (i : ι) := (neighbors Q (family i)).card
  have card : (incidences Q L family).card = ∑ i ∈ L, r i := by
    simp only [incidences,r,neighbors,Finset.card_filter,Finset.sum_product]
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlinear : (n:ℝ) ≤ (n:ℝ)^(4/3:ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1:ℝ) ≤ 4/3)
  by_cases h4 : 4 ≤ Q.card
  · let R := L.filter (fun i => 0 < r i)
    have sepR : Separated R family := by
      intro a b hab
      exact @sep ⟨a,(mem_filter.mp a.property).1⟩ ⟨b,(mem_filter.mp b.property).1⟩
        (fun eq => hab (Subtype.ext (congrArg (fun x : L => x.val) eq)))
    obtain ⟨E,edge,curve,C,drawn,inj,meet,four,he,hc⟩ :=
      drawing Q R family sepR (fun i => (mem_filter.mp i.property).2)
    have hR : R.card ≤ n := (card_filter_le ..).trans hL
    have htotal : (incidences Q L family).card ≤ E.card + 2*n := by
      have heq : (∑ l ∈ R, r l) = E.card + R.card := by rw [←sum_coe_sort]; exact he
      have hrl : (∑ l ∈ R, r l) = ∑ l ∈ L, r l := by
        refine sum_subset (filter_subset ..) (fun i hi hr => ?_)
        by_contra! h; exact hr (mem_filter.mpr ⟨hi,Nat.pos_of_ne_zero h⟩)
      rw [card,←hrl,heq]; omega
    by_cases dense : 12*Q.card ≤ E.card
    · have two (i) (hi : i ∈ E) : (edge i).card = 2 := by
        obtain ⟨x,y,hne,he,_⟩ := drawn i hi
        simp [he,hne]
      have hbound := OMA.Crossing.cubic_crossing_bound E C edge (fun ij => edge ij.1 ∪ edge ij.2)
        two four (by simpa using h4) (by simpa using dense)
        (induced_edges E edge curve C drawn inj meet)
      simp only [Fintype.card_coe] at hbound
      have hc' : C.card ≤ n^2 := hc.trans (Nat.pow_le_pow_left hR 2)
      have hcube : E.card^3 ≤ 343*n^4 := calc
        _ ≤ 288*Q.card^2*C.card := hbound
        _ ≤ 343*n^2*n^2 := by gcongr; norm_num
        _ = _ := by ring
      have heR : (E.card:ℝ) ≤ 7*(n:ℝ)^(4/3:ℝ) := by
        apply le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity)
        rw [mul_pow,←Real.rpow_natCast ((n:ℝ)^(4/3:ℝ)),←Real.rpow_mul (by positivity)]
        norm_num
        exact_mod_cast hcube
      have hi : ((incidences Q L family).card:ℝ) ≤ E.card + 2*n := by exact_mod_cast htotal
      linarith
    · have ht : (incidences Q L family).card ≤ 14*n := by omega
      have htr : ((incidences Q L family).card:ℝ) ≤ 14*n := by exact_mod_cast ht
      linarith
  · have h : (incidences Q L family).card ≤ 3*n := calc
      _ ≤ (L ×ˢ Q).card := card_filter_le ..
      _ = L.card * Q.card := card_product ..
      _ ≤ n*3 := Nat.mul_le_mul hL (by omega)
      _ = _ := Nat.mul_comm ..
    have hr : ((incidences Q L family).card:ℝ) ≤ 3*n := by exact_mod_cast h
    linarith


end OMA.Pseudo1085




/- Local geometry for incidences of equal-radius circles on a two-sphere. -/
namespace OMA.SphereLocal1085
open Matrix RealInnerProductSpace
open scoped Matrix
abbrev E := EuclideanSpace ℝ (Fin 3)

private theorem gram_zero (v : Fin 4 → E) :
    (Matrix.of fun i j => inner ℝ (v i) (v j)).det = 0 := by
  let A : Matrix (Fin 4) (Fin 3) ℝ := fun i j => v i j
  have innerA : (Matrix.of fun i j => inner ℝ (v i) (v j)) = A*A.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.transpose_apply]
    simp [PiLp.inner_apply,A,mul_comm]
  rw [innerA]
  by_contra h
  have rank := Matrix.rank_of_det_ne_zero h
  have bound := (Matrix.rank_mul_le_left A A.transpose).trans A.rank_le_card_width
  simp [rank] at bound

private theorem block_det (s a b h : ℝ) :
    (!![s,a,h,h; a,s,h,h; h,h,s,b; h,h,b,s]).det =
      (s-a)*(s-b)*((s+a)*(s+b)-4*h^2) := by
  simp [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.det_unique,Fin.succAbove]
  ring

/-- Opposite edges of a spherical incidence rectangle cannot both be short:
`δ` is the squared Euclidean radius of each incidence circle. -/
theorem local_unique (a b x y : E) (s h δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (radius : s*δ=s^2-h^2)
    (na : ‖a‖^2=s) (nb : ‖b‖^2=s) (nx : ‖x‖^2=s) (ny : ‖y‖^2=s)
    (ax : inner ℝ a x=h) (ay : inner ℝ a y=h)
    (bx : inner ℝ b x=h) (by' : inner ℝ b y=h)
    (ab : dist a b ^ 2 ≤ δ) (xy : dist x y ^ 2 ≤ δ) : a=b ∨ x=y := by
  by_contra! bad
  rcases bad with ⟨hab,hxy⟩
  let c := inner ℝ a b
  let k := inner ℝ x y
  have gram : (Matrix.of fun i j : Fin 4 => inner ℝ (![a,b,x,y] i) (![a,b,x,y] j)) =
      !![s,c,h,h; c,s,h,h; h,h,s,k; h,h,k,s] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [c,k,na,nb,nx,ny,ax,ay,bx,by'] <;>
      first | exact real_inner_comm .. | rw [real_inner_comm]; assumption
  have det := gram_zero ![a,b,x,y]
  rw [gram,block_det] at det
  have ac : dist a b ^ 2 = 2*(s-c) := by rw [dist_eq_norm,norm_sub_sq_real,na,nb]; dsimp [c]; ring
  have xk : dist x y ^ 2 = 2*(s-k) := by rw [dist_eq_norm,norm_sub_sq_real,nx,ny]; dsimp [k]; ring
  have sc : 0 < s-c := by nlinarith [sq_pos_of_pos (dist_pos.mpr hab)]
  have sk : 0 < s-k := by nlinarith [sq_pos_of_pos (dist_pos.mpr hxy)]
  have eq := (mul_eq_zero.mp det).resolve_left (mul_pos sc sk).ne'
  rw [ac] at ab
  rw [xk] at xy
  nlinarith only [eq,radius,mul_pos hs hδ,mul_le_mul_of_nonneg_left ab hs.le,
    mul_le_mul_of_nonneg_left xy hs.le,mul_nonneg sc.le sk.le]

/-- All incident points are within `√(2δ)` of one fixed choice of sign of the
center. This keeps the number of neighboring cubes bounded as the radius varies. -/
theorem local_distance (a x : E) (s h δ : ℝ) (hs : 0 < s) (hδ : 0 ≤ δ)
    (radius : s*δ=s^2-h^2) (na : ‖a‖^2=s) (nx : ‖x‖^2=s) (ax : inner ℝ a x=h) :
    dist (if 0 ≤ h then a else -a) x ^ 2 ≤ 2*δ := by
  have ha : |h| ≤ s := by
    rw [← sq_le_sq₀ (abs_nonneg _) hs.le,sq_abs]
    nlinarith [mul_nonneg hs.le hδ]
  have ha' := (abs_le.mp ha)
  split_ifs with hh
  · rw [dist_eq_norm,norm_sub_sq_real,na,nx,ax]
    apply le_of_mul_le_mul_left (a := s) _ hs
    nlinarith [mul_nonneg hh (sub_nonneg.mpr ha'.2)]
  · rw [dist_eq_norm,norm_sub_sq_real,norm_neg,na,nx,inner_neg_left,ax]
    apply le_of_mul_le_mul_left (a := s) _ hs
    nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge hh)) (show 0 ≤ s+h by linarith)]

end OMA.SphereLocal1085


/- A unit-distance circle on a sphere decomposes into four arcs on which
the distance from the initial endpoint increases with the parameter. This
keeps the consecutive arcs through a small point cloud in its neighborhood. -/
namespace OMA.SphereQuarter1085
open RealInnerProductSpace
open scoped EuclideanGeometry

private abbrev V := EuclideanSpace ℝ (Fin 3)
private abbrev W := EuclideanSpace ℝ (Fin 2)
private instance : Fact (Module.finrank ℝ V = 2+1) := ⟨by simp⟩

private noncomputable def frame (a : V) (ha : a ≠ 0) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2 ha).repr.symm

private def signed (b : Bool) (t : ℝ) := if b then t else -t
private theorem sign_sq (b : Bool) (t : ℝ) : (signed b t)^2=t^2 := by cases b <;> simp [signed]
private theorem sign_diff_sq (b : Bool) (x y : ℝ) :
    (signed b x - signed b y)^2=(x-y)^2 := by cases b <;> simp [signed]; ring
private theorem signed_abs (x : ℝ) : ∃ b, signed b |x|=x := by
  by_cases h : 0 ≤ x
  · exact ⟨true,by simp [signed,abs_of_nonneg h]⟩
  · exact ⟨false,by simp [signed,abs_of_neg (lt_of_not_ge h)]⟩

private noncomputable def xy (δ : ℝ) (b : Bool × Bool) (t : ℝ) : W :=
  !₂[signed b.1 t,signed b.2 (Real.sqrt (δ-t^2))]

noncomputable def pt (a : V) (ha : a ≠ 0) (s h δ : ℝ) (b : Bool × Bool) (t : ℝ) : V :=
  (h/s) • a + (frame a ha (xy δ b t) : V)

theorem continuous_pt (a : V) (ha : a ≠ 0) (s h δ : ℝ) (b : Bool × Bool) :
    Continuous (pt a ha s h δ b) := by
  have hxy : Continuous (xy δ b) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    rcases b with ⟨b,c⟩
    fin_cases i <;> cases b <;> cases c <;> simp [signed] <;> fun_prop
  exact continuous_const.add (continuous_subtype_val.comp ((frame a ha).continuous.comp hxy))

private theorem circle_eq (δ : ℝ) (b : Bool × Bool) {t : ℝ} (ht : 0 ≤ δ-t^2) :
    ‖xy δ b t‖^2=δ := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  change (signed _ _)^2+(signed _ _)^2=_
  rw [sign_sq,sign_sq,Real.sq_sqrt ht]
  ring

theorem on (a : V) (ha : a ≠ 0) (s h δ : ℝ) (hs : 0 < s) (na : ‖a‖^2 = s)
    (rad : s*δ=s^2-h^2) (b : Bool × Bool) {t : ℝ} (ht : t^2 ≤ δ) :
    ‖pt a ha s h δ b t‖^2=s ∧ inner ℝ a (pt a ha s h δ b t)=h := by
  let w := frame a ha (xy δ b t)
  have ort : inner ℝ a (w:V)=0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  have wn : ‖(w:V)‖^2=δ := by
    change ‖(frame a ha) (xy δ b t)‖^2=_
    rw [LinearIsometryEquiv.norm_map,circle_eq _ _ (sub_nonneg.mpr ht)]
  change ‖(h/s) • a + (w:V)‖^2 = s ∧ _
  constructor
  · rw [norm_add_sq_real,real_inner_smul_left,ort,wn,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,na]
    field_simp
    nlinarith [congrArg (fun x : ℝ => s*x) rad]
  · change inner ℝ a ((h/s) • a + (w:V))=h
    rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,na,ort]
    field_simp
    simp

theorem covers (a : V) (ha : a ≠ 0) (s h δ : ℝ) (hs : 0 < s) (na : ‖a‖^2 = s)
    (rad : s*δ=s^2-h^2) (x : V) (nx : ‖x‖^2=s) (hx : inner ℝ a x=h) :
    ∃ (b : Bool × Bool) (t : ℝ), 0 ≤ t ∧ t^2 ≤ δ ∧ pt a ha s h δ b t=x := by
  let v := x-(h/s) • a
  have hv : v ∈ (ℝ ∙ a)ᗮ := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    dsimp [v]
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,na,hx]
    field_simp
    simp
  let z := (frame a ha).symm ⟨v,hv⟩
  have hvn : ‖v‖^2=δ := by
    dsimp [v]
    rw [norm_sub_sq_real,nx,real_inner_smul_right,real_inner_comm a x,hx,norm_smul,mul_pow,
      Real.norm_eq_abs,sq_abs,na]
    field_simp
    nlinarith [congrArg (fun x : ℝ => s*x) rad]
  have zn : (z 0)^2+(z 1)^2=δ := by
    have hzn : ‖z‖^2=δ := by simpa [z] using hvn
    rwa [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two] at hzn
  obtain ⟨b,hb⟩ := signed_abs (z 0)
  obtain ⟨c,hc⟩ := signed_abs (z 1)
  have hz : xy δ (b,c) |z 0|=z := by
    ext i
    fin_cases i
    · exact hb
    · change signed c (Real.sqrt (δ-|z 0|^2))=_
      rw [sq_abs,show δ-(z 0)^2=(z 1)^2 by linarith,Real.sqrt_sq_eq_abs]
      exact hc
  refine ⟨(b,c),|z 0|,abs_nonneg _,by rw [sq_abs]; nlinarith [sq_nonneg (z 1)],?_⟩
  simp [pt,hz,z,v]

private theorem sqdist (a : V) (ha : a ≠ 0) (s h δ : ℝ) (b : Bool × Bool) (x y : ℝ) :
    dist (pt a ha s h δ b x) (pt a ha s h δ b y)^2 =
      (x-y)^2 + (Real.sqrt (δ-x^2)-Real.sqrt (δ-y^2))^2 := by
  change dist (_+(frame a ha (xy δ b x):V)) (_+(frame a ha (xy δ b y):V))^2 = _
  rw [dist_add_left]
  change dist (frame a ha (xy δ b x)) (frame a ha (xy δ b y))^2 = _
  rw [LinearIsometryEquiv.dist_map,EuclideanSpace.dist_sq_eq,Fin.sum_univ_two]
  simp [xy,Real.dist_eq,sign_diff_sq]

theorem injective_pt (a : V) (ha : a ≠ 0) (s h δ : ℝ) (b : Bool × Bool) :
    Function.Injective (pt a ha s h δ b) := by
  intro x y he
  have eq := sqdist a ha s h δ b x y
  rw [he,dist_self,zero_pow (by decide : 2≠0)] at eq
  nlinarith [sq_nonneg (Real.sqrt (δ-x^2)-Real.sqrt (δ-y^2)),sq_nonneg (x-y)]

theorem between (a : V) (ha : a ≠ 0) (s h δ : ℝ) (b : Bool × Bool) {x z y : ℝ}
    (hx : 0 ≤ x) (hxz : x ≤ z) (hzy : z ≤ y) :
    dist (pt a ha s h δ b x) (pt a ha s h δ b z) ≤ dist (pt a ha s h δ b x) (pt a ha s h δ b y) := by
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  rw [sqdist,sqdist]
  have xz : x^2 ≤ z^2 := by gcongr
  have zy : z^2 ≤ y^2 := by gcongr; exact hx.trans hxz
  have fz := Real.sqrt_le_sqrt (sub_le_sub_left xz δ)
  have fy := Real.sqrt_le_sqrt (sub_le_sub_left zy δ)
  nlinarith [mul_self_le_mul_self (sub_nonneg.mpr hxz) (sub_le_sub_right hzy x),
    mul_self_le_mul_self (sub_nonneg.mpr fz) (sub_le_sub_left fy (Real.sqrt (δ-x^2)))]

/-- Coordinate deletion gives a continuous injection on the spherical cap of radius
`R/3` about any point on the radius-`R` sphere. -/
theorem cap_chart (z : V) (R : ℝ) (hR : 0 < R) (hz : ‖z‖=R) :
    ∃ proj : V → W, Continuous proj ∧ Set.InjOn proj {x | ‖x‖=R ∧ dist x z ≤ R/3} := by
  have hmax : ∃ i : Fin 3, R/2 ≤ |z i| := by
    by_contra! h
    have se := EuclideanSpace.real_norm_sq_eq z
    rw [hz,Fin.sum_univ_three] at se
    have each (i : Fin 3) : (z i)^2 < (R/2)^2 := by
      rw [← sq_abs]
      exact (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mpr (h i)
    nlinarith [each 0,each 1,each 2,sq_pos_of_pos hR]
  obtain ⟨i,hi⟩ := hmax
  let proj (u : V) : W := WithLp.toLp 2 (fun j => u (i.succAbove j))
  refine ⟨proj,(PiLp.continuous_toLp 2 _).comp (continuous_pi fun j =>
    PiLp.continuous_apply 2 _ (i.succAbove j)),?_⟩
  intro x hx y hy he
  obtain ⟨xn,xd⟩ := hx
  obtain ⟨yn,yd⟩ := hy
  have same (j : Fin 2) : x (i.succAbove j) = y (i.succAbove j) := congrArg (fun u : W => u j) he
  have xn' := EuclideanSpace.real_norm_sq_eq x
  have yn' := EuclideanSpace.real_norm_sq_eq y
  rw [xn,Fin.sum_univ_succAbove _ i] at xn'
  rw [yn,Fin.sum_univ_succAbove _ i] at yn'
  simp_rw [same] at xn'
  have eq : (x i)^2=(y i)^2 := by linarith
  have xb := (PiLp.dist_apply_le x z i).trans xd
  have yb := (PiLp.dist_apply_le y z i).trans yd
  rw [Real.dist_eq,abs_le] at xb yb
  have coord : x i = y i := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp eq) with h|h
    · exact h
    · rcases le_total 0 (z i) with h'|h'
      · rw [abs_of_nonneg h'] at hi; linarith
      · rw [abs_of_nonpos h'] at hi; linarith
  ext j
  by_cases h : j=i
  · exact h ▸ coord
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq h
    exact same k

end OMA.SphereQuarter1085




/- The incidence estimate inside one pair of small spherical patches. -/
namespace OMA.SpherePatch1085
open Finset RealInnerProductSpace
open scoped EuclideanGeometry Classical
private abbrev V := EuclideanSpace ℝ (Fin 3)
private abbrev W := EuclideanSpace ℝ (Fin 2)
private abbrev Quad := Bool × Bool
private def region (s ρ : ℝ) (z : V) := {x : V | ‖x‖^2=s ∧ dist x z ≤ ρ/4}

private theorem make_arc (Q : Finset V) (a z : V) (ha : a ≠ 0) (s h ρ : ℝ)
    (hs : 0<s) (hr : 0<ρ) (na : ‖a‖^2=s) (rad : s*ρ^2=s^2-h^2)
    (small : ∀ x ∈ Q, ∀ y ∈ Q, dist x y ≤ ρ/10) (hz : z∈Q)
    (proj : V → W) (pc : Continuous proj) (pi : Set.InjOn proj (region s ρ z)) (b : Quad) :
    ∃ A : Pseudo1085.Arc,
      (∀ t : ℝ, 0 ≤ t → t^2 ≤ ρ^2 → SphereQuarter1085.pt a ha s h (ρ^2) b t ∈ Q →
        proj (SphereQuarter1085.pt a ha s h (ρ^2) b t) ∈ A.carrier) ∧
      ∀ x ∈ A.carrier, ∃ u ∈ region s ρ z, proj u=x ∧ inner ℝ a u=h := by
  let f := SphereQuarter1085.pt a ha s h (ρ^2) b
  have finj : Function.Injective f := SphereQuarter1085.injective_pt ..
  let T := (Q.preimage f finj.injOn).filter (fun t => 0 ≤ t ∧ t^2≤ρ^2)
  have mem (t : ℝ) : t∈T ↔ f t∈Q ∧ 0≤t ∧ t^2≤ρ^2 := by simp [T]
  by_cases hT : T.Nonempty
  · let u := T.min' hT
    let v := T.max' hT
    have hu := (mem u).mp (T.min'_mem hT)
    have hv := (mem v).mp (T.max'_mem hT)
    have good {t : ℝ} (ht : t∈Set.Icc u v) : f t∈region s ρ z ∧ inner ℝ a (f t)=h := by
      have hsq : t^2 ≤ ρ^2 := (sq_le_sq₀ (hu.2.1.trans ht.1) (hu.2.1.trans (ht.1.trans ht.2))).mpr ht.2 |>.trans hv.2.2
      obtain ⟨hn,hi⟩ := SphereQuarter1085.on a ha s h (ρ^2) hs na rad b hsq
      have bd : dist (f u) (f t) ≤ dist (f u) (f v) :=
        SphereQuarter1085.between a ha s h (ρ^2) b hu.2.1 ht.1 ht.2
      have du := dist_triangle_left (f t) z (f u)
      have dx := small _ hu.1 _ hv.1
      have dz := small _ hu.1 _ hz
      exact ⟨⟨hn,by linarith⟩,hi⟩
    let A : Pseudo1085.Arc := ⟨proj ∘ f,u,v,pc.comp (SphereQuarter1085.continuous_pt ..),
      fun _ hx _ hy he => finj (pi (good hx).1 (good hy).1 he)⟩
    refine ⟨A,?_,?_⟩
    · intro t ht hsq hQ
      have hmem := (mem t).mpr ⟨hQ,ht,hsq⟩
      exact ⟨t,⟨T.min'_le _ hmem,T.le_max' _ hmem⟩,rfl⟩
    · rintro x ⟨t,ht,rfl⟩
      exact ⟨f t,(good ht).1,rfl,(good ht).2⟩
  · let A : Pseudo1085.Arc := ⟨proj ∘ f,1,0,pc.comp (SphereQuarter1085.continuous_pt ..),
      by simp⟩
    refine ⟨A,?_,?_⟩
    · intro t ht hsq hQ
      exact (hT ⟨t,(mem t).mpr ⟨hQ,ht,hsq⟩⟩).elim
    · rintro x ⟨t,ht,_⟩
      have he : (1:ℝ)≤0 := ht.1.trans ht.2
      norm_num at he

/-- Uniform incidence estimate for two diameter-`ρ/10` patches, where `ρ` is the
radius of the spherical incidence circles, `s` the squared sphere radius, and
`h` the prescribed inner product. -/
theorem local_bound (P Q : Finset V) (s h ρ : ℝ) (hs : 0<s) (hr : 0<ρ)
    (rad : s*ρ^2=s^2-h^2) (pn : ∀ a∈P, ‖a‖^2=s) (qn : ∀ x∈Q, ‖x‖^2=s)
    (pd : ∀ a∈P, ∀ b∈P, dist a b≤ρ/10) (qd : ∀ x∈Q, ∀ y∈Q, dist x y≤ρ/10) :
    (((P ×ˢ Q).filter (fun z => inner ℝ z.1 z.2=h)).card:ℝ) ≤
      56*((P.card:ℝ)+Q.card)^(4/3:ℝ) := by
  classical
  by_cases hQ : Q.Nonempty
  case neg =>
    rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
    simp
    positivity
  obtain ⟨z,hz⟩ := hQ
  let R := Real.sqrt s
  have hR : 0<R := Real.sqrt_pos.mpr hs
  have sqR : R^2=s := Real.sq_sqrt hs.le
  have hρ : ρ ≤ R := by
    have ht : ρ^2 ≤ s := (le_of_mul_le_mul_left (a := s) (by nlinarith [sq_nonneg h]) hs)
    nlinarith [sq_nonneg (ρ-R)]
  have nz : ‖z‖=R := by nlinarith [qn z hz,norm_nonneg z]
  obtain ⟨proj,pc,pi'⟩ := SphereQuarter1085.cap_chart z R hR nz
  have pi : Set.InjOn proj (region s ρ z) := pi'.mono (by
    intro x hx; obtain ⟨hn,hd⟩ := hx
    exact ⟨by nlinarith [norm_nonneg x],by linarith⟩)
  have qreg (x : V) (hx : x∈Q) : x∈region s ρ z := ⟨qn x hx,by linarith [qd x hx z hz]⟩
  have nzp (a : P) : a.val ≠ 0 := by
    intro eq; have h := pn a a.property; rw [eq] at h; simp at h; linarith
  choose A covers source using fun (b : Quad) (a : P) =>
    make_arc Q a z (nzp a) s h ρ hs hr (pn a a.property) rad qd hz proj pc pi b
  let Q' := Q.image proj
  let n := P.card + Q.card
  have hn : 1≤n := by dsimp [n]; have := card_pos.mpr ⟨z,hz⟩; omega
  let L : Finset P := univ
  let J (b : Quad) := Pseudo1085.incidences Q' L (A b)
  have sep (q : Quad) : Pseudo1085.Separated L (A q) := by
    intro a b hab x y hax hbx hay hby
    obtain ⟨u,hu,ux,au⟩ := source q a.val x hax
    obtain ⟨u',hu',ux',bu⟩ := source q b.val x hbx
    obtain ⟨v,hv,vy,av⟩ := source q a.val y hay
    obtain ⟨v',hv',vy',bv⟩ := source q b.val y hby
    obtain rfl : u=u' := pi hu hu' (ux.trans ux'.symm)
    obtain rfl : v=v' := pi hv hv' (vy.trans vy'.symm)
    have ab := pd _ a.val.property _ b.val.property
    have uv := dist_triangle_left u v z
    rw [dist_comm z u,dist_comm z v] at uv
    have uvd : dist u v ≤ ρ := by linarith [hu.2,hv.2]
    have uv' := SphereLocal1085.local_unique a.val b.val u v s h (ρ^2) hs (sq_pos_of_pos hr)
      rad (pn _ a.val.property) (pn _ b.val.property) hu.1 hv.1 au av bu bv
      ((sq_le_sq₀ dist_nonneg hr.le).mpr (by linarith)) ((sq_le_sq₀ dist_nonneg hr.le).mpr uvd)
    obtain rfl : u=v := uv'.resolve_left (fun eq => hab (Subtype.ext (Subtype.ext eq)))
    exact ux.symm.trans vy
  have hj (b : Quad) : ((J b).card:ℝ) ≤ 14*(n:ℝ)^(4/3:ℝ) := by
    apply Pseudo1085.balanced Q' L (A b) (sep b) n hn
    · exact card_image_le.trans (Nat.le_add_left ..)
    · simp [L,n]
  let I := (P ×ˢ Q).filter (fun z => inner ℝ z.1 z.2=h)
  let enc (t : I) : P × W := (⟨t.val.1,(mem_product.mp (mem_filter.mp t.property).1).1⟩,proj t.val.2)
  have ei : Function.Injective enc := by
    intro a b he
    have eq := congrArg Prod.snd he
    exact Subtype.ext (Prod.ext (congrArg (fun z : P × W => z.1.val) he)
      (pi (qreg _ (mem_product.mp (mem_filter.mp a.property).1).2)
        (qreg _ (mem_product.mp (mem_filter.mp b.property).1).2) eq))
  have sub : (univ : Finset I).image enc ⊆ univ.biUnion J := by
    intro _ he
    obtain ⟨t,_,rfl⟩ := mem_image.mp he
    have ⟨hp,hq⟩ := mem_product.mp (mem_filter.mp t.property).1
    let a : P := ⟨t.val.1,hp⟩
    obtain ⟨b,u,hu,hsq,heq⟩ := SphereQuarter1085.covers a (nzp a) s h (ρ^2) hs (pn _ hp)
      rad t.val.2 (qn _ hq) (mem_filter.mp t.property).2
    have hei := covers b a u hu hsq (heq.symm ▸ hq)
    rw [heq] at hei
    exact mem_biUnion.mpr ⟨b,mem_univ _,mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _,mem_image_of_mem proj hq⟩,hei⟩⟩
  have cnt := (card_le_card sub).trans card_biUnion_le
  rw [card_image_of_injective _ ei,card_univ,Fintype.card_coe] at cnt
  have sum : (I.card:ℝ) ≤ ∑ b, ((J b).card:ℝ) := by exact_mod_cast cnt
  calc
    _ ≤ _ := sum.trans (sum_le_sum (fun i _ => hj i))
    _ = 56*((P.card:ℝ)+Q.card)^(4/3:ℝ) := by simp [n]; ring

end OMA.SpherePatch1085


/- Sum local incidence estimates over pairs of nearby cubes. -/
namespace OMA.CubeSum1085
open Finset

def cell {α G : Type*} [DecidableEq G] (A : Finset α) (key : α → G) (i : G) : Finset α :=
  A.filter fun x => key x = i

private theorem sum_cells {α G : Type*} [DecidableEq G] (A : Finset α)
    (key : α → G) (I : Finset G) : (∑ i ∈ I, (cell A key i).card) ≤ A.card := by
  unfold cell
  rw [sum_card_fiberwise_eq_card_filter]
  exact card_filter_le _ _

private theorem exponent (x : ℝ) (hx : 0 ≤ x) :
    x^(4/3:ℝ) = x^(1/3:ℝ)*x := by
  rw [show (4/3:ℝ) = 1/3+1 by norm_num, Real.rpow_add_one' hx (by norm_num)]

theorem window_bound {α β G : Type*} [AddCommGroup G] [DecidableEq G]
    [DecidableEq α] [DecidableEq β] (P : Finset α) (A : Finset β)
    (kp : α → G) (ka : β → G) (D : Finset G) (E : Finset (α × β))
    (hE : E ⊆ P ×ˢ A) (near : ∀ e ∈ E, ka e.2 - kp e.1 ∈ D)
    {C : ℝ} (hC : 0 ≤ C)
    (localCount : ∀ i j, ((E ∩ (cell P kp i ×ˢ cell A ka j)).card : ℝ) ≤
      C * ((cell P kp i).card + (cell A ka j).card : ℝ)^(4/3:ℝ)) :
    (E.card : ℝ) ≤ D.card * C * ((P.card : ℝ) + A.card)^(4/3:ℝ) := by
  classical
  let I := P.image kp
  let N : ℝ := P.card + A.card
  have hN : 0 ≤ N := by dsimp [N]; positivity
  let T (d : G) := E.filter fun e => ka e.2 - kp e.1 = d
  have total : E.card = ∑ d ∈ D, (T d).card := card_eq_sum_card_fiberwise near
  have forOffset (d : G) : ((T d).card : ℝ) ≤ C * N^(4/3:ℝ) := by
    let v (i : G) : ℝ := (cell P kp i).card + (cell A ka (d+i)).card
    have hv (i) : 0 ≤ v i := by dsimp [v]; positivity
    have hvN (i) : v i ≤ N := by
      dsimp [v,N,cell]
      exact_mod_cast Nat.add_le_add (card_filter_le _ _) (card_filter_le _ _)
    have mass : ∑ i ∈ I, v i ≤ N := by
      have ha : ∑ i ∈ I, (cell A ka (d+i)).card ≤ A.card := by
        have hid i : cell A ka (d+i) = cell A (fun a => ka a-d) i := by
          ext a
          simp only [cell,mem_filter,sub_eq_iff_eq_add]
          rw [add_comm d i]
        simp_rw [hid]
        exact sum_cells A _ I
      dsimp [v,N]
      rw [sum_add_distrib]
      exact_mod_cast Nat.add_le_add (sum_cells P kp I) ha
    have maps : ((T d : Finset (α × β)) : Set (α × β)).MapsTo (fun e => kp e.1) I := by
      intro e he
      exact mem_image_of_mem _ (mem_product.mp (hE (mem_filter.mp he).1)).1
    have sub (i) : ((T d).filter fun e => kp e.1 = i) ⊆
        E ∩ (cell P kp i ×ˢ cell A ka (d+i)) := by
      intro e he
      rcases mem_filter.mp he with ⟨ht,hi⟩
      rcases mem_filter.mp ht with ⟨h0,hk⟩
      obtain ⟨hp,ha⟩ := mem_product.mp (hE h0)
      refine mem_inter.mpr ⟨h0,mem_product.mpr ⟨mem_filter.mpr ⟨hp,hi⟩,
        mem_filter.mpr ⟨ha,?_⟩⟩⟩
      simpa only [hi] using (sub_eq_iff_eq_add.mp hk)
    rw [card_eq_sum_card_fiberwise maps, Nat.cast_sum]
    calc
      _ ≤ ∑ i ∈ I, (C*N^(1/3:ℝ)) * v i := by
        apply sum_le_sum
        intro i _
        refine (Nat.cast_le.mpr (card_le_card (sub i))).trans ((localCount i (d+i)).trans ?_)
        change C * (v i)^(4/3:ℝ) ≤ _
        rw [exponent _ (hv i),← mul_assoc]
        gcongr
        exact hvN i
      _ ≤ C * N^(4/3:ℝ) := by
        rw [← Finset.mul_sum,exponent _ hN,← mul_assoc]
        exact mul_le_mul_of_nonneg_left mass (mul_nonneg hC (Real.rpow_nonneg hN _))
  rw [total,Nat.cast_sum]
  calc
    _ ≤ ∑ _d ∈ D, C*N^(4/3:ℝ) := sum_le_sum fun d _ => forOffset d
    _ = _ := by simp [N,mul_assoc]

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Cube := Fin 3 → ℤ

noncomputable def box (ρ : ℝ) (x : Space) : Cube := fun i => ⌊x i / (ρ/100)⌋

def offsetCode (t : Fin 3 → Fin 403) : Cube := fun i => ((t i).val : ℤ) - 201

def offsets : Finset Cube := Finset.univ.image offsetCode

private theorem coord_window {ρ : ℝ} (hρ : 0 < ρ) (x : Space) (i : Fin 3) :
    (box ρ x i : ℝ)*(ρ/100) ≤ x i ∧ x i < ((box ρ x i : ℝ)+1)*(ρ/100) := by
  have hw : 0 < ρ/100 := by positivity
  exact ⟨(le_div_iff₀ hw).mp (Int.floor_le _),(div_lt_iff₀ hw).mp (Int.lt_floor_add_one _)⟩

theorem diameter {ρ : ℝ} (hρ : 0 < ρ) {x y : Space} (hk : box ρ x = box ρ y) :
    dist x y ≤ ρ/10 := by
  have coord (i : Fin 3) : dist (x i) (y i) ≤ ρ/100 := by
    have hx := coord_window hρ x i
    have hy := coord_window hρ y i
    rw [hk] at hx
    rw [Real.dist_eq,abs_le]
    constructor <;> linarith only [hx.1,hx.2,hy.1,hy.2]
  apply (sq_le_sq₀ dist_nonneg (by positivity : 0 ≤ ρ/10)).mp
  rw [EuclideanSpace.dist_sq_eq]
  calc
    _ ≤ ∑ _i : Fin 3, (ρ/100)^2 := Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ dist_nonneg (coord i) 2
    _ ≤ _ := by simp; nlinarith [sq_nonneg ρ]

theorem neighbors {ρ : ℝ} (hρ : 0 < ρ) {x y : Space}
    (h : dist x y ^2 ≤ 2*ρ^2) : box ρ x - box ρ y ∈ offsets := by
  have hw : 0 < ρ/100 := by positivity
  have hxy : dist x y ≤ 2*ρ := by
    apply (sq_le_sq₀ dist_nonneg (by positivity : 0 ≤ 2*ρ)).mp
    nlinarith [sq_nonneg ρ]
  have hb (i : Fin 3) : (-201 : ℤ) ≤ box ρ x i - box ρ y i ∧ box ρ x i - box ρ y i ≤ 201 := by
    have hd := (PiLp.dist_apply_le x y i).trans hxy
    rw [Real.dist_eq,abs_le] at hd
    have l1 := Int.floor_le (x i/(ρ/100))
    have l2 := Int.floor_le (y i/(ρ/100))
    have u1 := Int.lt_floor_add_one (x i/(ρ/100))
    have u2 := Int.lt_floor_add_one (y i/(ρ/100))
    have hl : x i/(ρ/100) - y i/(ρ/100) ≤ 200 := by
      rw [← sub_div,div_le_iff₀ hw]; linarith only [hd.2]
    have hr : y i/(ρ/100) - x i/(ρ/100) ≤ 200 := by
      rw [← sub_div,div_le_iff₀ hw]; linarith only [hd.1]
    unfold box
    constructor
    · exact_mod_cast (by linarith only [l1,l2,u1,u2,hl,hr] :
        (-201:ℝ) ≤ (⌊x i / (ρ/100)⌋:ℝ) - (⌊y i / (ρ/100)⌋:ℝ))
    · exact_mod_cast (by linarith only [l1,l2,u1,u2,hl,hr] :
        (⌊x i / (ρ/100)⌋:ℝ) - (⌊y i / (ρ/100)⌋:ℝ) ≤ 201)
  let t (i : Fin 3) : Fin 403 := ⟨(box ρ x i - box ρ y i + 201).toNat, by
    obtain ⟨_,_⟩ := hb i
    omega⟩
  have he : offsetCode t = box ρ x - box ρ y := by
    funext i
    change ((box ρ x i - box ρ y i + 201).toNat : ℤ) - 201 = _
    change _ = box ρ x i - box ρ y i
    obtain ⟨_,_⟩ := hb i
    omega
  simp only [offsets,Finset.mem_image,Finset.mem_univ,true_and]
  exact ⟨t,he⟩

end OMA.CubeSum1085



/- Global point--circle incidence bound on a sphere. -/

namespace OMA.CubeSum1085
open Finset RealInnerProductSpace
open scoped Classical

set_option maxRecDepth 8192 in
theorem sphere_count (P Q : Finset Space) (s h ρ : ℝ) (hs : 0 < s) (hr : 0 < ρ)
    (rad : s*ρ^2=s^2-h^2) (pn : ∀ a ∈ P, ‖a‖^2=s) (qn : ∀ x ∈ Q, ‖x‖^2=s) :
    (((P ×ˢ Q).filter (fun e => inner ℝ e.1 e.2=h)).card : ℝ) ≤
      (offsets.card:ℝ)*56*((P.card:ℝ)+Q.card)^(4/3:ℝ) := by
  classical
  let key (a : Space) := box ρ (if 0 ≤ h then a else -a)
  let E := (P ×ˢ Q).filter fun e => inner ℝ e.1 e.2=h
  refine window_bound P Q key (box ρ) offsets E (filter_subset _ _) ?_ (by norm_num : (0:ℝ) ≤ 56) ?_
  · intro e he
    have he' : e ∈ P ×ˢ Q ∧ inner ℝ e.1 e.2 = h := (Finset.mem_filter.mp he)
    have hpq : e.1 ∈ P ∧ e.2 ∈ Q := Finset.mem_product.mp he'.1
    have hd := OMA.SphereLocal1085.local_distance e.1 e.2 s h (ρ^2) hs (sq_nonneg _) rad
      (pn _ hpq.1) (qn _ hpq.2) he'.2
    rw [dist_comm] at hd
    exact neighbors hr hd
  · intro i j
    have eq : E ∩ (cell P key i ×ˢ cell Q (box ρ) j) =
        (cell P key i ×ˢ cell Q (box ρ) j).filter (fun e => inner ℝ e.1 e.2 = h) := by
      ext z
      simp only [E,mem_inter,mem_filter,mem_product,cell]
      tauto
    rw [eq]
    apply OMA.SpherePatch1085.local_bound _ _ s h ρ hs hr rad
    · intro a ha
      exact pn _ (mem_filter.mp ha).1
    · intro x hx
      exact qn _ (mem_filter.mp hx).1
    · intro a ha b hb
      have e := (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm
      change key a = key b at e
      dsimp only [key] at e
      split_ifs at e with hh
      · exact diameter hr e
      · simpa only [dist_neg_neg] using diameter hr e
    · intro x hx y hy
      exact diameter hr ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)

end OMA.CubeSum1085


/- Transfer the incidence bound to unit distances, including the threshold
at which a neighbor is necessarily antipodal. -/
namespace OMA.SphereRadius1085
open RealInnerProductSpace Finset
open scoped Classical
abbrev V := EuclideanSpace ℝ (Fin 3)

theorem unit_le_incident (Q : Finset V) (s : ℝ) (norm : ∀ x∈Q, ‖x‖^2=s) :
    unitDistNum Q ≤ ((Q ×ˢ Q).filter fun z => inner ℝ z.1 z.2 = s-1/2).card := by
  apply card_le_card_of_injOn (s := Q.sym2.filter fun e => dist e.out.1 e.out.2=1) (fun e => e.out)
  · intro e he
    obtain ⟨hq,hd⟩ := mem_filter.mp he
    have hx := mem_sym2_iff.mp hq _ e.out_fst_mem
    have hy := mem_sym2_iff.mp hq _ e.out_snd_mem
    have h := norm_sub_sq_real e.out.1 e.out.2
    rw [←dist_eq_norm,hd,norm _ hx,norm _ hy] at h
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hx,hy⟩,by linarith⟩
  · intro a _ b _ h
    exact a.out_eq.symm.trans ((congrArg (fun p : V × V => Sym2.mk p.1 p.2) h).trans b.out_eq)

theorem small (Q : Finset V) (s : ℝ) (hs : s≤1/4) (norm : ∀ x∈Q, ‖x‖^2=s) :
    unitDistNum Q ≤ Q.card := by
  apply (unit_le_incident Q s norm).trans
  let I := (Q ×ˢ Q).filter fun z => inner ℝ z.1 z.2 = s-1/2
  have antipodal (p : V × V) (hp : p∈I) : p.2 = -p.1 := by
    obtain ⟨hp,hd⟩ := mem_filter.mp hp
    obtain ⟨hx,hy⟩ := mem_product.mp hp
    have eq := norm_add_sq_real p.1 p.2
    rw [norm _ hx,norm _ hy,hd] at eq
    have hz : ‖p.1+p.2‖=0 := by nlinarith [sq_nonneg ‖p.1+p.2‖]
    exact eq_neg_of_add_eq_zero_right (norm_eq_zero.mp hz)
  apply Finset.card_le_card_of_injOn (s := I) (t := Q) Prod.fst
  · intro p hp
    exact (mem_product.mp (mem_filter.mp hp).1).1
  · intro p hp q hq h
    exact Prod.ext h ((antipodal p hp).trans ((congrArg Neg.neg h).trans (antipodal q hq).symm))

theorem parameters (s : ℝ) (hs : 1/4 < s) :
    0<s ∧ 0<Real.sqrt (1-1/(4*s)) ∧ s*(Real.sqrt (1-1/(4*s)))^2 = s^2-(s-1/2)^2 := by
  have hp : 0<s := by linarith
  have h : 0 < 1-1/(4*s) := sub_pos.mpr ((div_lt_one (by positivity)).mpr (by linarith))
  refine ⟨hp,Real.sqrt_pos.mpr h,?_⟩
  rw [Real.sq_sqrt h.le]
  field_simp
  ring

theorem sphere_bound {K : ℝ} (hK : 1 ≤ K)
    (global : ∀ (Q : Finset V) (s h ρ : ℝ), 0<s → 0<ρ → s*ρ^2=s^2-h^2 →
      (∀ x∈Q, ‖x‖^2=s) →
      (((Q ×ˢ Q).filter (fun z => inner ℝ z.1 z.2=h)).card:ℝ) ≤ K*(Q.card:ℝ)^(4/3:ℝ))
    (Q : Finset V) (s : ℝ) (norm : ∀ x∈Q, ‖x‖^2=s) :
    (unitDistNum Q:ℝ) ≤ K*(Q.card:ℝ)^(4/3:ℝ) := by
  by_cases hs : s ≤ 1/4
  · have le : (unitDistNum Q:ℝ) ≤ Q.card := by exact_mod_cast small Q s hs norm
    have p : (Q.card:ℝ) ≤ (Q.card:ℝ)^(4/3:ℝ) := by
      rcases Nat.eq_zero_or_pos Q.card with h|h
      · rw [h,Nat.cast_zero,Real.zero_rpow (by norm_num : (4/3:ℝ)≠0)]
      · simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h : (1:ℝ)≤Q.card)
          (by norm_num : (1:ℝ)≤4/3)
    exact le.trans (p.trans (le_mul_of_one_le_left (by positivity) hK))
  · obtain ⟨hs',hr,eq⟩ := parameters s (lt_of_not_ge hs)
    exact (Nat.cast_le.mpr (unit_le_incident Q s norm)).trans (global Q s _ _ hs' hr eq norm)

/-- Apply a two-set ordered incidence estimate to a single point set. -/
theorem of_global (B : ℝ) (hB : 0 ≤ B)
    (global : ∀ (P Q : Finset V) (s h ρ : ℝ), 0<s → 0<ρ → s*ρ^2=s^2-h^2 →
      (∀ a∈P, ‖a‖^2=s) → (∀ x∈Q, ‖x‖^2=s) →
      (((P ×ˢ Q).filter (fun z => inner ℝ z.1 z.2=h)).card:ℝ) ≤
        B*((P.card:ℝ)+Q.card)^(4/3:ℝ)) :
    ∃ K > (0:ℝ), ∀ (Q : Finset V) (s : ℝ), (∀ x∈Q, ‖x‖^2=s) →
      (unitDistNum Q:ℝ) ≤ K*(Q.card:ℝ)^(4/3:ℝ) := by
  let K := 1 + B*(2:ℝ)^(4/3:ℝ)
  have hK : 1 ≤ K := le_add_of_nonneg_right (mul_nonneg hB (by positivity))
  refine ⟨K,by linarith,fun Q s ns => sphere_bound hK ?_ Q s ns⟩
  intro P u h ρ hu hr eq nu
  have hh := global P P u h ρ hu hr eq nu nu
  rw [←two_mul,Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity),←mul_assoc] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (by positivity))

end OMA.SphereRadius1085

theorem OMA.Odd1085.sphere_bound : ∃ K > (0:ℝ),
    ∀ (Q : Finset (EuclideanSpace ℝ (Fin 3))) (s : ℝ), (∀ x∈Q, ‖x‖^2=s) →
    (unitDistNum Q:ℝ) ≤ K*(Q.card:ℝ)^(4/3:ℝ) :=
  OMA.SphereRadius1085.of_global ((OMA.CubeSum1085.offsets.card:ℝ)*56)
    (by positivity) OMA.CubeSum1085.sphere_count


/- Integer point-line incidences give many orthogonal pairs on the sphere in three dimensions. -/

namespace OMA.SphereGrid1085
open Finset Filter
open scoped EuclideanGeometry Classical RealInnerProductSpace

private abbrev V := EuclideanSpace ℝ (Fin 3)

private noncomputable def scale (v : V) : ℝ := Real.sqrt (1/2) / ‖v‖

private lemma scale_pos {v : V} (hv : v ≠ 0) : 0 < scale v :=
  div_pos (Real.sqrt_pos.mpr (by norm_num)) (norm_pos_iff.mpr hv)

private lemma scaled_norm {v : V} (hv : v ≠ 0) :
    ‖scale v • v‖^2 = 1 / 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (scale_pos hv)]
  simp [scale, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)]

private def point (xy : ℕ × ℕ) : V := !₂[(xy.1:ℝ),xy.2,1]
private def line (ab : ℕ × ℕ) : V := !₂[(ab.1:ℝ),-1,ab.2]
private noncomputable def P (xy : ℕ × ℕ) : V := scale (point xy) • point xy
private noncomputable def L (ab : ℕ × ℕ) : V := scale (line ab) • line ab

private lemma point_ne (xy : ℕ × ℕ) : point xy ≠ 0 := by
  intro h
  simpa [point] using congrArg (fun v : V => v 2) h

private lemma line_ne (ab : ℕ × ℕ) : line ab ≠ 0 := by
  intro h
  simpa [line] using congrArg (fun v : V => v 1) h

private lemma P_inj : Function.Injective P := by
  intro x y he
  have h (i : Fin 3) : scale (point x)*(point x i) = scale (point y)*(point y i) :=
    congrArg (fun v : V => v i) he
  have hs : scale (point x) = scale (point y) := by simpa [point] using h 2
  have hi (i : Fin 3) : point x i = point y i :=
    mul_left_cancel₀ (scale_pos (point_ne y)).ne' (hs ▸ h i)
  apply Prod.ext
  · exact_mod_cast (show (x.1:ℝ) = y.1 from hi 0)
  · exact_mod_cast (show (x.2:ℝ) = y.2 from hi 1)

private lemma L_inj : Function.Injective L := by
  intro x y he
  have h (i : Fin 3) : scale (line x)*(line x i) = scale (line y)*(line y i) :=
    congrArg (fun v : V => v i) he
  have hs : scale (line x) = scale (line y) := by simpa [line] using h 1
  have hi (i : Fin 3) : line x i = line y i :=
    mul_left_cancel₀ (scale_pos (line_ne y)).ne' (hs ▸ h i)
  apply Prod.ext
  · exact_mod_cast (show (x.1:ℝ) = y.1 from hi 0)
  · exact_mod_cast (show (x.2:ℝ) = y.2 from hi 2)

private lemma P_ne_L (x y : ℕ × ℕ) : P x ≠ L y := by
  intro he
  have h : scale (point x) * (x.2:ℝ) = scale (line y) * (-1) :=
    congrArg (fun v : V => v 1) he
  have hx := mul_nonneg (scale_pos (point_ne x)).le (Nat.cast_nonneg (α:=ℝ) x.2)
  linarith [scale_pos (line_ne y)]

private lemma incident (x a b : ℕ) : dist (P (x,a*x+b)) (L (a,b)) = 1 := by
  have h : inner ℝ (point (x,a*x+b)) (line (a,b)) = 0 := by
    simp [point, line, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  have hs : inner ℝ (P (x,a*x+b)) (L (a,b)) = 0 := by
    simp [P,L,real_inner_smul_left,real_inner_smul_right,h]
  rw [dist_eq_norm]
  have hsq := norm_sub_sq_real (P (x,a*x+b)) (L (a,b))
  rw [hs,show ‖P (x,a*x+b)‖^2 = 1/2 from scaled_norm (point_ne _),
    show ‖L (a,b)‖^2 = 1/2 from scaled_norm (line_ne _)] at hsq
  nlinarith [norm_nonneg (P (x,a*x+b)-L (a,b))]

/-- A height-`t²` grid and its positive-slope lines yield `t⁴` distinct unit pairs. -/
theorem grid (t : ℕ) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 3)), A.card ≤ 3*t^3 ∧
      (∀ x ∈ A, ‖x‖^2 = 1/2) ∧ t^4 ≤ unitDistNum A := by
  let pts := range t ×ˢ range (2*t^2)
  let lines := range t ×ˢ range (t^2)
  let A := pts.image P ∪ lines.image L
  refine ⟨A, ?_, ?_, ?_⟩
  · calc
      A.card ≤ (pts.image P).card + (lines.image L).card := card_union_le _ _
      _ ≤ pts.card + lines.card := add_le_add card_image_le card_image_le
      _ = 3*t^3 := by simp [pts,lines]; ring
  · intro v hv
    rcases mem_union.mp hv with h | h
    · obtain ⟨xy,_,rfl⟩ := mem_image.mp h
      exact scaled_norm (point_ne xy)
    · obtain ⟨ab,_,rfl⟩ := mem_image.mp h
      exact scaled_norm (line_ne ab)
  let enc (p : ℕ × (ℕ × ℕ)) := Sym2.mk (P (p.1,p.2.1*p.1+p.2.2)) (L p.2)
  have inject : Function.Injective enc := by
    rintro ⟨x,a,b⟩ ⟨y,c,d⟩ he
    rcases Sym2.eq_iff.mp he with ⟨hp,hl⟩ | ⟨hp,-⟩
    · have hx : x = y := congrArg (fun xy : ℕ × ℕ => xy.1) (P_inj hp)
      exact Prod.ext hx (L_inj hl)
    · exact (P_ne_L _ _ hp).elim
  have maps : ∀ p ∈ range t ×ˢ lines, enc p ∈ A.sym2.filter (fun e => dist e.out.1 e.out.2 = 1) := by
    rintro ⟨x,a,b⟩ hp
    obtain ⟨hx,hab⟩ := mem_product.mp hp
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    have hax : a*x ≤ t^2 := by
      rw [sq]; exact Nat.mul_le_mul (mem_range.mp ha).le (mem_range.mp hx).le
    have hb' : b < t^2 := mem_range.mp hb
    have hxy : (x,a*x+b) ∈ pts := mem_product.mpr ⟨hx,mem_range.mpr (by omega)⟩
    apply mem_filter.mpr
    refine ⟨mk_mem_sym2_iff.mpr ⟨mem_union_left _ (mem_image_of_mem P hxy),mem_union_right _ (mem_image_of_mem L hab)⟩,?_⟩
    have h : Sym2.mk (enc (x,a,b)).out.1 (enc (x,a,b)).out.2 =
      Sym2.mk (P (x,a*x+b)) (L (a,b)) := (enc (x,a,b)).out_eq
    rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · rw [h₁,h₂]; exact incident x a b
    · rw [h₁,h₂,dist_comm]; exact incident x a b
  have lower := card_le_card_of_injOn enc maps inject.injOn
  change _ ≤ unitDistNum A at lower
  simpa [lines, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using lower

/-- A set of exactly `m` points on the radius-`1/√2` sphere with many unit distances. -/
theorem sphere (m : ℕ) (hm : 3 ≤ m) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 3)), A.card = m ∧
      (∀ x ∈ A, ‖x‖^2 = 1/2) ∧ (1/81:ℝ)*m^(4/3:ℝ) ≤ unitDistNum A := by
  let t := Nat.nthRoot 3 (m/3)
  have ht : 1 ≤ t := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr (by simp; omega)
  have hlo : t^3 ≤ m/3 := Nat.pow_nthRoot_le (.inl (by decide))
  have hhi : m/3 < (t+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hbudget : 3*t^3 ≤ m := by omega
  have hmid : m ≤ 3*(t+1)^3 := by omega
  have hup : m ≤ (3*t)^3 := calc
    m ≤ 3*(t+1)^3 := hmid
    _ ≤ 3*(2*t)^3 := by gcongr; omega
    _ ≤ (3*t)^3 := by ring_nf; omega
  have hreal : (m:ℝ)^(4/3:ℝ) ≤ 81*(t:ℝ)^4 := calc
    _ ≤ (((3*t:ℕ):ℝ)^3)^(4/3:ℝ) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hup) (by norm_num)
    _ = 81*(t:ℝ)^4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      ring
  obtain ⟨A, hAc, hAn, hAe⟩ := grid t
  let extra := (range m).image fun k => P (k,0)
  have hc : extra.card = m := by
    rw [Finset.card_image_of_injective, card_range]
    exact fun i j h => congrArg (fun xy : ℕ × ℕ => xy.1) (P_inj h)
  have hcard : m ≤ (A ∪ extra).card := hc ▸ card_le_card subset_union_right
  obtain ⟨Q,hAQ,hQsub,hQcard⟩ := exists_subsuperset_card_eq
    (show A ⊆ A ∪ extra from subset_union_left) (hAc.trans hbudget) hcard
  refine ⟨Q,hQcard,?_,?_⟩
  · intro x hx
    rcases mem_union.mp (hQsub hx) with h | h
    · exact hAn _ h
    · obtain ⟨k,_,rfl⟩ := mem_image.mp h
      exact scaled_norm (point_ne _)
  · have hmono : unitDistNum A ≤ unitDistNum Q := by
      exact card_le_card (filter_subset_filter _ (Finset.sym2_mono hAQ))
    have hcount : (t:ℝ)^4 ≤ (unitDistNum Q:ℝ) := by exact_mod_cast hAe.trans hmono
    linarith

end OMA.SphereGrid1085

/- The odd-dimensional Lenz construction with a three-dimensional configuration
on the sphere of squared radius one half and equicardinal orthogonal circles. -/
namespace OMA.OddLift1085
open Finset Filter
open scoped Classical Topology

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
private noncomputable def U {X : Type*} [MetricSpace X] (s : Finset X) :=
  s.sym2.filter fun e => dist e.out.1 e.out.2 = 1

private theorem memU {X : Type*} [MetricSpace X] {s : Finset X} {a b : X} :
    Sym2.mk a b ∈ U s ↔ a ∈ s ∧ b ∈ s ∧ dist a b = 1 := by
  let e := Sym2.mk a b
  have h : Sym2.mk e.out.1 e.out.2 = Sym2.mk a b := e.out_eq
  have hd : dist e.out.1 e.out.2 = dist a b := by
    rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> rw [h₁,h₂]
    exact dist_comm ..
  change e ∈ s.sym2.filter _ ↔ _
  simp only [mem_filter,hd]
  exact (and_congr_left fun _ => mk_mem_sym2_iff).trans and_assoc

private theorem unit_image_le {X Y : Type*} [MetricSpace X] [MetricSpace Y] [DecidableEq Y] (a : Finset X)
    (f : X → Y) (hi : Function.Injective f) (hd : ∀ x y, dist (f x) (f y) = dist x y) :
    unitDistNum a ≤ unitDistNum (a.image f) := by
  classical
  apply Finset.card_le_card_of_injOn (s := U a) (t := U (a.image f)) (Sym2.map f)
  · refine Sym2.ind fun x y h => ?_
    obtain ⟨hx,hy,hdxy⟩ := memU.mp h
    apply memU.mpr
    exact ⟨mem_image_of_mem _ hx,mem_image_of_mem _ hy,(hd ..).trans hdxy⟩
  · exact (Sym2.map.injective hi).injOn

private theorem cross_lower {X : Type*} [MetricSpace X] [DecidableEq X] (a b : Finset X) (dis : Disjoint a b)
    (h : ∀ x ∈ a, ∀ y ∈ b, dist x y = 1) :
    unitDistNum a + a.card*b.card ≤ unitDistNum (a∪b) := by
  classical
  let enc (p : X × X) := Sym2.mk p.1 p.2
  let B := (a ×ˢ b).image enc
  have inj : Set.InjOn enc (↑(a ×ˢ b) : Set (X × X)) := by
    rintro ⟨x,y⟩ h₁ ⟨u,v⟩ h₂ he
    rw [SetLike.mem_coe,mem_product] at h₁ h₂
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rfl
    · exact False.elim (Finset.disjoint_left.mp dis h₁.1 h₂.2)
  have card : B.card = a.card*b.card := (card_image_of_injOn inj).trans (card_product ..)
  have subA : U a ⊆ U (a ∪ b) := by
    refine Sym2.ind fun x y hx => ?_
    obtain ⟨hx,hy,hd⟩ := memU.mp hx
    exact memU.mpr ⟨mem_union_left _ hx,mem_union_left _ hy,hd⟩
  have subB : B ⊆ U (a ∪ b) := by
    intro e he
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := mem_image.mp he
    obtain ⟨hx,hy⟩ := mem_product.mp hxy
    exact memU.mpr ⟨mem_union_left _ hx,mem_union_right _ hy,h x hx y hy⟩
  have dab : Disjoint (U a) B := by
    apply Finset.disjoint_left.mpr
    intro e ha hb
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := mem_image.mp hb
    exact Finset.disjoint_left.mp dis (memU.mp ha).2.1 (mem_product.mp hxy).2
  have le := card_le_card (Finset.union_subset subA subB)
  rw [card_union_of_disjoint dab,card] at le
  exact le

private noncomputable def lhs {d : ℕ} (x : E d) : E (d+2) :=
  WithLp.toLp 2 (Fin.addCases (fun i => x i) (fun _ : Fin 2 => (0:ℝ)))
private noncomputable def rhs (d : ℕ) (y : E 2) : E (d+2) :=
  WithLp.toLp 2 (Fin.addCases (fun _ : Fin d => (0:ℝ)) (fun i => y i))

private theorem lhs_norm {d : ℕ} (x : E d) : ‖lhs x‖^2 = ‖x‖^2 := by
  simp [EuclideanSpace.real_norm_sq_eq,lhs,Fin.sum_univ_add]

private theorem rhs_norm (d : ℕ) (x : E 2) : ‖rhs d x‖^2 = ‖x‖^2 := by
  simp [EuclideanSpace.real_norm_sq_eq,rhs,Fin.sum_univ_add]

private theorem lhs_dist {d : ℕ} (x y : E d) : dist (lhs x) (lhs y) = dist x y := by
  simp [EuclideanSpace.dist_eq,lhs,Fin.sum_univ_add]

private theorem rhs_dist (d : ℕ) (x y : E 2) : dist (rhs d x) (rhs d y) = dist x y := by
  simp [EuclideanSpace.dist_eq,rhs,Fin.sum_univ_add]

private theorem orth_dist {d : ℕ} (x : E d) (y : E 2) :
    dist (lhs x) (rhs d y)^2 = ‖x‖^2 + ‖y‖^2 := by
  simp [EuclideanSpace.dist_sq_eq,EuclideanSpace.real_norm_sq_eq,lhs,rhs,Fin.sum_univ_add,
    Real.dist_eq]

private noncomputable def circlePoint (i : ℕ) : E 2 :=
  let t : ℝ := 1/(i+4 : ℝ)
  !₂[t,Real.sqrt (1/2-t^2)]

private theorem circle_norm (i : ℕ) : ‖circlePoint i‖^2 = 1/2 := by
  let t : ℝ := 1/(i+4 : ℝ)
  have ht : 0 < t := by dsimp [t]; positivity
  have hle : t ≤ 1/4 := by dsimp [t]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith [Nat.cast_nonneg (α := ℝ) i]
  have hr : 0 ≤ 1/2-t^2 := by nlinarith
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  change t^2 + (Real.sqrt (1/2-t^2))^2 = _
  rw [Real.sq_sqrt hr]; ring

private theorem circle_inj : Function.Injective circlePoint := by
  intro i j h
  have e := congrArg (fun x : E 2 => x 0) h
  change 1/(i+4 : ℝ) = 1/(j+4 : ℝ) at e
  simpa using e

private theorem enlarge {d : ℕ} (s : Finset (E d)) (m : ℕ)
    (hs : ∀ x ∈ s, ‖x‖^2 = 1/2) : ∃ t : Finset (E (d+2)), t.card = s.card+m ∧
      (∀ x ∈ t, ‖x‖^2 = 1/2) ∧ unitDistNum s+s.card*m ≤ unitDistNum t := by
  classical
  let a := s.image lhs
  let b := (range m).image (fun i => rhs d (circlePoint i))
  have hil : Function.Injective (@lhs d) := fun x y h => dist_eq_zero.mp (by rw [← lhs_dist x y,h,dist_self])
  have hir : Function.Injective (rhs d) := fun x y h => dist_eq_zero.mp (by rw [← rhs_dist d x y,h,dist_self])
  have ha : a.card = s.card := card_image_of_injective _ hil
  have hb : b.card = m := (card_image_of_injective _ (hir.comp circle_inj)).trans (card_range _)
  have cross (x) (hx : x ∈ a) (y) (hy : y ∈ b) : dist x y = 1 := by
    obtain ⟨x,hxs,rfl⟩ := mem_image.mp hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hy
    have eq := orth_dist x (circlePoint i)
    rw [hs x hxs,circle_norm] at eq
    nlinarith [dist_nonneg (x := lhs x) (y := rhs d (circlePoint i))]
  have dis : Disjoint a b := Finset.disjoint_left.mpr (fun x hx hy => by simpa using cross x hx x hy)
  refine ⟨a∪b,by simp [card_union_of_disjoint dis,ha,hb],?_,?_⟩
  · intro x hx
    rcases mem_union.mp hx with hx|hx
    · obtain ⟨x,hxs,rfl⟩ := mem_image.mp hx
      exact (lhs_norm x).trans (hs x hxs)
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact (rhs_norm d _).trans (circle_norm i)
  · have lo := cross_lower a b dis cross
    rw [ha,hb] at lo
    have hle : unitDistNum s ≤ unitDistNum a := by simpa [a] using unit_image_le s lhs hil lhs_dist
    exact (Nat.add_le_add_right hle _).trans lo

private theorem lift (t m : ℕ) (a : Finset (E 3)) (hc : a.card = m)
    (hs : ∀ x ∈ a, ‖x‖^2 = 1/2) :
    ∃ s : Finset (E (3+2*t)), s.card = (t+1)*m ∧ (∀ x ∈ s, ‖x‖^2 = 1/2) ∧
      t*(t+1)*m^2+2*unitDistNum a ≤ 2*unitDistNum s := by
  induction t with
  | zero => exact ⟨a,by simpa using hc,hs,by simp⟩
  | succ t ih =>
    obtain ⟨s,cs,ns,es⟩ := ih
    obtain ⟨b,cb,nb,eb⟩ := enlarge s m ns
    rw [cs] at cb eb
    exact ⟨b,cb.trans (by ring),nb,by nlinarith⟩

private theorem attained_lower {d : ℕ} [NeZero d] (s : Finset (E d)) {n : ℕ} (h : s.card ≤ n) :
    unitDistNum s ≤ Erdos1085.f d n := by
  classical
  obtain ⟨B,sub,card⟩ := Infinite.exists_superset_card_eq s n h
  have hmono : unitDistNum s ≤ unitDistNum B := by
    apply Finset.card_le_card (s := U s) (t := U B)
    refine Sym2.ind fun x y he => ?_
    obtain ⟨hx,hy,hd⟩ := memU.mp he
    exact memU.mpr ⟨sub hx,sub hy,hd⟩
  apply hmono.trans
  apply le_ciSup₂ (f := fun (b : Finset (E d)) (_ : b.card = n) => unitDistNum b) _ B card
  refine ⟨n.choose 2,?_⟩
  intro k hk
  obtain ⟨T,hT⟩ := Set.mem_iUnion.mp hk
  obtain ⟨c,rfl⟩ := Set.mem_range.mp hT
  simpa only [c] using unitDistNum_le_choose_two T

/-- Lift many unit distances on the three-dimensional sphere of squared radius
one half to the second-order lower bound in every odd dimension at least five. -/
theorem lower (sphere : ∃ c > (0:ℝ), ∀ᶠ m : ℕ in atTop, ∃ a : Finset (E 3), a.card = m ∧
    (∀ x ∈ a, ‖x‖^2 = 1/2) ∧ c*(m:ℝ)^(4/3:ℝ) ≤ unitDistNum a)
    {d : ℕ} (hd : 5 ≤ d) (hodd : Odd d) :
    ∃ C > (0:ℝ), ∀ᶠ n : ℕ in atTop,
      ↑(d/2-1)/(2*↑(d/2))*(n:ℝ)^2 + C*(n:ℝ)^(4/3:ℝ) ≤ Erdos1085.f d n := by
  obtain ⟨c,hc,hs⟩ := sphere
  let p := d/2
  let t := p-1
  have dom : 3+2*t=d := by obtain ⟨u,hu⟩ := hodd; dsimp [p,t]; omega
  have hp : 0 < p := by dsimp [p]; omega
  have ht : t+1=p := by dsimp [t]; omega
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp
  let e : ℝ := 4/3
  let C := c / (2*(2*p:ℝ)^e)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  have grow : Tendsto (fun n : ℕ => (n:ℝ)^(1/3:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp tendsto_natCast_atTop_atTop
  filter_upwards [(Nat.tendsto_div_const_atTop hp.ne').eventually hs,
    eventually_ge_atTop p, grow.eventually_ge_atTop ((p:ℝ)/C)] with n hs hn hlarge
  let m := n/p
  obtain ⟨a,ca,na,ea⟩ := hs
  obtain ⟨s,cs,_,es⟩ := lift t m a ca na
  have hpm : p*m ≤ n := by dsimp [m]; simpa [mul_comm] using Nat.div_mul_le_self n p
  have hn' : n < p*m+p := by
    have hrem := Nat.mod_lt n hp
    have hdec := Nat.mod_add_div n p
    dsimp [m]; omega
  have hmn : 1 ≤ m := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hn)
  have hpad : s.card ≤ n := by rw [cs,ht]; exact hpm
  have : NeZero (3+2*t) := ⟨by omega⟩
  have hf := (attained_lower s hpad).trans_eq (congrArg (fun u => Erdos1085.f u n) dom)
  have hbound : t*(t+1)*m^2 + 2*unitDistNum a ≤ 2*Erdos1085.f d n :=
    es.trans (Nat.mul_le_mul_left 2 hf)
  rw [ht] at hbound
  have hboundR : (t:ℝ)*p*m^2+2*(unitDistNum a:ℝ) ≤ 2*(Erdos1085.f d n : ℝ) := by exact_mod_cast hbound
  have pm : (p:ℝ)*m ≤ n := by exact_mod_cast hpm
  have near : (n:ℝ) < p*m+p := by exact_mod_cast hn'
  have m1 : (1:ℝ) ≤ m := by exact_mod_cast hmn
  have tt : (t:ℝ)+1=p := by exact_mod_cast ht
  have nm : (n:ℝ) ≤ 2*(p:ℝ)*m := by nlinarith [mul_le_mul_of_nonneg_left m1 hpR.le]
  have powbd := Real.rpow_le_rpow (by positivity : 0 ≤ (n:ℝ)) nm (by norm_num [e] : 0 ≤ e)
  rw [Real.mul_rpow (by positivity) (by positivity)] at powbd
  have Cmul : 2*C*(2*(p:ℝ))^e=c := by dsimp [C]; field_simp
  have gain : 2*C*(n:ℝ)^e ≤ (unitDistNum a : ℝ) := calc
    _ ≤ 2*C*((2*(p:ℝ))^e*(m:ℝ)^e) := mul_le_mul_of_nonneg_left powbd (by positivity)
    _ = c*(m:ℝ)^e := by rw [← mul_assoc,Cmul]
    _ ≤ _ := ea
  have hlarge' : (p:ℝ) ≤ C*(n:ℝ)^(1/3:ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hC).mp hlarge
  have loss : (p:ℝ)*n ≤ C*(n:ℝ)^e := by
    rw [show e=1/3+1 by norm_num [e],Real.rpow_add_one' (by positivity) (by norm_num : (1/3:ℝ)+1≠0)]
    nlinarith [mul_le_mul_of_nonneg_right hlarge' (Nat.cast_nonneg (α := ℝ) n)]
  have gap : (n:ℝ)^2-((p:ℝ)*m)^2 ≤ 2*p*n := by
    have := mul_le_mul (show (n:ℝ)-p*m ≤ p by linarith)
      (show (n:ℝ)+p*m ≤ 2*n by linarith) (by positivity : 0 ≤ (n:ℝ)+p*m) hpR.le
    nlinarith
  have weight : (t:ℝ)/(2*p) ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have scale : (t:ℝ)/(2*p)*(p*m)^2 = (t:ℝ)*p*m^2/2 := by field_simp
  have square_le : ((p:ℝ)*m)^2 ≤ (n:ℝ)^2 := by gcongr
  change (t:ℝ)/(2*p)*(n:ℝ)^2 + C*(n:ℝ)^e ≤ _
  nlinarith [mul_le_mul_of_nonneg_right weight
    (sub_nonneg.mpr square_le)]

end OMA.OddLift1085

/- Counting within and between the parts of a unit-distance configuration.
The inter-part count is bounded by the number of edges of a complete multipartite
graph; no geometric restriction on those pairs is required. -/

namespace OMA.OddUpper1085
open Finset Filter
open scoped Classical Topology

private noncomputable def U {X : Type*} [MetricSpace X] (s : Finset X) :=
  s.sym2.filter fun e => dist e.out.1 e.out.2 = 1

private theorem memU {X : Type*} [MetricSpace X] {s : Finset X} {x y : X} :
    Sym2.mk x y ∈ U s ↔ x ∈ s ∧ y ∈ s ∧ dist x y = 1 := by
  let e := Sym2.mk x y
  have he : Sym2.mk e.out.1 e.out.2 = Sym2.mk x y := e.out_eq
  have hd : dist e.out.1 e.out.2 = dist x y := by
    rcases Sym2.eq_iff.mp he with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> rw [h₁,h₂]
    exact dist_comm ..
  change e ∈ s.sym2.filter _ ↔ _
  simp only [mem_filter,hd]
  exact (and_congr_left fun _ => mk_mem_sym2_iff).trans and_assoc

private theorem union_bound {X : Type*} [MetricSpace X] [DecidableEq X] (a b : Finset X) :
    unitDistNum (a∪b) ≤ unitDistNum a+unitDistNum b+a.card*b.card := by
  classical
  let enc (xy : X × X) := Sym2.mk xy.1 xy.2
  let C := (a ×ˢ b).image enc
  have sub : U (a∪b) ⊆ U a∪U b∪C := by
    refine Sym2.ind fun x y he => ?_
    obtain ⟨hx,hy,hd⟩ := memU.mp he
    rcases mem_union.mp hx with hx|hx <;> rcases mem_union.mp hy with hy|hy
    · exact mem_union_left _ (mem_union_left _ (memU.mpr ⟨hx,hy,hd⟩))
    · exact mem_union_right _ (mem_image.mpr ⟨(x,y),mem_product.mpr ⟨hx,hy⟩,rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨(y,x),mem_product.mpr ⟨hy,hx⟩,Sym2.eq_swap⟩)
    · exact mem_union_left _ (mem_union_right _ (memU.mpr ⟨hx,hy,hd⟩))
  have hC : C.card ≤ a.card*b.card := card_image_le.trans_eq (card_product ..)
  exact (card_le_card sub).trans ((card_union_le ..).trans (Nat.add_le_add (card_union_le ..) hC))

private theorem partition_count {X ι : Type*} [MetricSpace X] [DecidableEq X]
    (B : ι → Finset X) (hdis : Pairwise fun i j => Disjoint (B i) (B j)) (s : Finset ι) :
    2*unitDistNum (s.biUnion B) + ∑ i ∈ s, (B i).card^2 ≤
      (s.biUnion B).card^2 + 2*∑ i ∈ s, unitDistNum (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [unitDistNum]
  | @insert i s hi ih =>
    have hd : Disjoint (B i) (s.biUnion B) :=
      (Finset.disjoint_biUnion_right ..).2 (fun j hj => hdis (fun h => hi (h ▸ hj)))
    have hu := union_bound (B i) (s.biUnion B)
    rw [biUnion_insert,card_union_of_disjoint hd,sum_insert hi,sum_insert hi]
    nlinarith

/-- Unit-distance upper bound for a partition into `p` parts. The error constant
does not increase on summing over the parts. -/
theorem partition_bound {X : Type*} [MetricSpace X] [DecidableEq X] {p n : ℕ} (hp : 0 < p)
    (B : Fin p → Finset X) (hdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hN : (univ.biUnion B).card = n) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ i, (unitDistNum (B i):ℝ) ≤ K*((B i).card:ℝ)^(4/3:ℝ)) :
    (unitDistNum (univ.biUnion B):ℝ) ≤ ↑(p-1)/(2*(p:ℝ))*(n:ℝ)^2+K*(n:ℝ)^(4/3:ℝ) := by
  classical
  have cardN : ∑ i, (B i).card = n := (Finset.card_biUnion (fun _ _ _ _ hij => hdis hij)).symm.trans hN
  have count := partition_count B hdis univ
  rw [hN] at count
  have countR : 2*(unitDistNum (univ.biUnion B):ℝ) + ∑ i, ((B i).card:ℝ)^2 ≤
      (n:ℝ)^2 + 2*∑ i, (unitDistNum (B i):ℝ) := by exact_mod_cast count
  have total : ∑ i, ((B i).card:ℝ) = n := by exact_mod_cast cardN
  have square : (n:ℝ)^2 ≤ p*∑ i, ((B i).card:ℝ)^2 := by
    simpa [total] using Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin p)) (fun _ => (1:ℝ))
      (fun i => ((B i).card:ℝ))
  have exponent (u : ℕ) : (u:ℝ)^(4/3:ℝ) = (u:ℝ)^(1/3:ℝ)*u := by
    rw [show (4/3:ℝ)=1/3+1 by norm_num,Real.rpow_add_one' (by positivity) (by norm_num)]
  have sumE : ∑ i, (unitDistNum (B i):ℝ) ≤ K*(n:ℝ)^(4/3:ℝ) := calc
    _ ≤ ∑ i, (K*(n:ℝ)^(1/3:ℝ))*((B i).card:ℝ) := by
      apply sum_le_sum
      intro i _
      have hi : (B i).card ≤ n := by
        rw [← cardN]
        exact single_le_sum (fun j _ => Nat.zero_le ((B j).card)) (mem_univ i)
      apply (hB i).trans
      rw [exponent,← mul_assoc]
      gcongr
    _ = _ := by rw [← Finset.mul_sum,total,exponent,mul_assoc]
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have bound : (n:ℝ)^2 / p ≤ ∑ i, ((B i).card:ℝ)^2 :=
    (div_le_iff₀ hpR).mpr (by simpa only [mul_comm] using square)
  have coeff : ↑(p-1)/(2*(p:ℝ))*(n:ℝ)^2 = ((n:ℝ)^2 - (n:ℝ)^2/p)/2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    field_simp
    ring
  rw [coeff]
  linarith

/-- An extremal configuration admitting such a partition eventually yields the
upper half of the Erdős–Pach bound. -/
theorem upper_of_extremal_partition {d : ℕ} (hd : 5 ≤ d) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ᶠ n : ℕ in atTop, ∃ B : Fin (d/2) → Finset (EuclideanSpace ℝ (Fin d)),
      (Pairwise fun i j => Disjoint (B i) (B j)) ∧ (univ.biUnion B).card = n ∧
      Erdos1085.f d n ≤ unitDistNum (univ.biUnion B) ∧
      ∀ i, (unitDistNum (B i):ℝ) ≤ K*((B i).card:ℝ)^(4/3:ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (Erdos1085.f d n:ℝ) ≤ ↑(d/2-1)/(2*↑(d/2))*(n:ℝ)^2+K*(n:ℝ)^(4/3:ℝ) := by
  filter_upwards [h] with n hn
  obtain ⟨B,dis,card,extremal,bounds⟩ := hn
  exact (Nat.cast_le.mpr extremal).trans (partition_bound (by omega) B dis card hK bounds)

end OMA.OddUpper1085

/- Unit neighbors on a circular core and on a three-dimensional spherical core. -/

namespace OMA.Slices1085
open Finset EuclideanGeometry
open scoped Classical

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
noncomputable def neigh {d : ℕ} (C : Finset (E d)) (x : E d) := C.filter fun q => dist x q = 1
private noncomputable def plane {d : ℕ} (a : Fin 3 → E d) :=
  Submodule.span ℝ (Set.range (fun t : Fin 2 => a t.succ-a 0))

theorem triangle {d : ℕ} {C : Finset (E d)} (hc : Cospherical (C:Set (E d)))
    {a : Fin 3 → E d} (ha : ∀ t, a t ∈ C) (hi : Function.Injective a) :
    LinearIndependent ℝ (fun t : Fin 2 => a t.succ-a 0) := by
  have h := hc.affineIndependent (p:=a) (by rintro _ ⟨i,rfl⟩; exact ha i) hi
  have H := (affineIndependent_iff_linearIndependent_vsub ℝ a 0).mp h
  exact H.comp (fun t : Fin 2 => ⟨t.succ,t.succ_ne_zero⟩)
    (fun i j he => Fin.succ_injective _ (congrArg Subtype.val he))

private lemma triple {V : Type*} (C : Finset V) (h : 3 ≤ C.card) :
    ∃ a : Fin 3 → V, Function.Injective a ∧ ∀ t, a t ∈ C := by
  let e := Fintype.equivFin C
  have hs : 3 ≤ Fintype.card C := by simpa using h
  exact ⟨fun t => (e.symm (Fin.castLE hs t)).val,
    Subtype.val_injective.comp (e.symm.injective.comp (Fin.castLE_injective hs)),
    fun t => (e.symm (Fin.castLE hs t)).property⟩

private lemma direction {d : ℕ} (C : Finset (E d)) (hc : Cospherical (C:Set (E d)))
    (x : E d) (a : Fin 3 → E d) (ha : ∀ t, a t ∈ neigh C x) :
    ∃ H : Submodule ℝ (E d), plane a ≤ H ∧ H ≤ vectorSpan ℝ (C:Set (E d)) ∧
      ∀ q ∈ C, dist x q = 1 ↔ q-a 0 ∈ H := by
  obtain ⟨o,r,ho⟩ := hc
  let W := vectorSpan ℝ (C:Set (E d))
  let H := W ⊓ (ℝ ∙ (x-o))ᗮ
  have base := (mem_filter.mp (ha 0)).2
  have atC (t) : a t ∈ C := (mem_filter.mp (ha t)).1
  have rel (q) (hq : q ∈ C) : dist x q = 1 ↔ q-a 0 ∈ H := by
    have hw : q-a 0 ∈ W := vsub_mem_vectorSpan ℝ hq (atC 0)
    change dist x q = 1 ↔ (q-a 0 ∈ W ∧ q-a 0 ∈ (ℝ ∙ (x-o))ᗮ)
    rw [and_iff_right hw,Submodule.mem_orthogonal_singleton_iff_inner_right,inner_sub_left,inner_sub_right,inner_sub_right]
    have dsq (v w : E d) : (dist v w)^2 = ‖v‖^2 - 2*inner ℝ v w + ‖w‖^2 := by
      rw [dist_eq_norm,norm_sub_sq_real]
    have e₀ := dsq x (a 0)
    rw [base] at e₀
    have e₁ := dsq o q
    have e₂ := dsq o (a 0)
    rw [dist_comm,ho q hq] at e₁
    rw [dist_comm,ho (a 0) (atC 0)] at e₂
    have ed := dsq x q
    constructor
    · intro h; rw [h] at ed; linarith
    · intro h; nlinarith [show 0 ≤ dist x q from dist_nonneg]
  refine ⟨H,Submodule.span_le.mpr ?_,inf_le_left,rel⟩
  rintro _ ⟨j,rfl⟩
  exact (rel _ (atC _)).mp ((mem_filter.mp (ha j.succ)).2)

theorem circle {d : ℕ} (C : Finset (E d)) (hc : Cospherical (C:Set (E d)))
    (hd : Module.finrank ℝ (vectorSpan ℝ (C:Set (E d))) ≤ 2)
    (x : E d) (h : ¬∀ q ∈ C, dist x q = 1) : (neigh C x).card ≤ 2 := by
  by_contra! hn
  obtain ⟨a,hi,ha⟩ := triple _ hn
  obtain ⟨H,hP,hW,rel⟩ := direction C hc x a ha
  have dim : Module.finrank ℝ (plane a) = 2 := by
    exact (finrank_span_eq_card (triangle (a:=a) hc (fun t => (mem_filter.mp (ha t)).1) hi)).trans (Fintype.card_fin _)
  have eq := Submodule.eq_of_le_of_finrank_le hW (hd.trans (dim ▸ Submodule.finrank_mono hP))
  apply h
  intro q hq
  apply (rel q hq).mpr
  rw [eq]
  exact vsub_mem_vectorSpan ℝ hq (mem_filter.mp (ha 0)).1

private lemma slice {d : ℕ} (C : Finset (E d)) (hc : Cospherical (C:Set (E d)))
    (hd : Module.finrank ℝ (vectorSpan ℝ (C:Set (E d))) ≤ 3)
    (x : E d) (h : ¬∀ q ∈ C, dist x q = 1)
    (a : Fin 3 → E d) (hi : Function.Injective a) (ha : ∀ t, a t ∈ neigh C x) :
    ∀ q ∈ C, dist x q = 1 ↔ q-a 0 ∈ plane a := by
  obtain ⟨H,hP,hW,rel⟩ := direction C hc x a ha
  have neq : H ≠ vectorSpan ℝ (C:Set (E d)) := by
    intro he
    apply h
    intro q hq
    apply (rel _ hq).mpr
    rw [he]
    exact vsub_mem_vectorSpan ℝ hq (mem_filter.mp (ha 0)).1
  have dimH := Submodule.finrank_lt_finrank_of_lt (hW.lt_of_ne neq)
  have dimP : Module.finrank ℝ (plane a) = 2 := by
    exact (finrank_span_eq_card (triangle (a:=a) hc (fun t => (mem_filter.mp (ha t)).1) hi)).trans (Fintype.card_fin _)
  have he := Submodule.eq_of_le_of_finrank_le hP (by omega)
  simpa only [he] using rel

theorem sphere {d : ℕ} (C : Finset (E d)) (hc : Cospherical (C:Set (E d)))
    (hd : Module.finrank ℝ (vectorSpan ℝ (C:Set (E d))) ≤ 3)
    (x y : E d) (hx : ¬∀ q ∈ C, dist x q = 1) (hy : ¬∀ q ∈ C, dist y q = 1)
    (hn : 3 ≤ (neigh C x ∩ neigh C y).card) : neigh C x = neigh C y := by
  obtain ⟨a,hi,ha⟩ := triple _ hn
  have sx := slice C hc hd x hx a hi (fun i => (mem_inter.mp (ha i)).1)
  have sy := slice C hc hd y hy a hi (fun i => (mem_inter.mp (ha i)).2)
  ext q
  simp only [neigh,mem_filter]
  exact and_congr_right fun h => (sx q h).trans (sy q h).symm

end OMA.Slices1085

/- Extremal sets have many neighbors at each vertex when a large common
neighborhood can be reached from a circular core. -/

namespace OMA.Replace1085
open Finset EuclideanGeometry
open scoped Classical

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

private noncomputable def circ (n : ℕ) : E 2 :=
  let t : ℝ := 1/(n+2:ℝ)
  !₂[t,Real.sqrt (1-t^2)]

private lemma circ_norm (n : ℕ) : ‖circ n‖=1 := by
  let t : ℝ := 1/(n+2:ℝ)
  have ht : 0<t := by dsimp [t]; positivity
  have ht' : t≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hr : 0 ≤ 1-t^2 := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht')]
  have h := EuclideanSpace.real_norm_sq_eq (circ n)
  rw [Fin.sum_univ_two] at h
  change ‖circ n‖^2=t^2+(Real.sqrt (1-t^2))^2 at h
  rw [Real.sq_sqrt hr] at h
  nlinarith [norm_nonneg (circ n)]

private lemma circ_inj : Function.Injective circ := by
  intro i j h
  have e := congrArg (fun p : E 2 => p 0) h
  change 1/(i+2:ℝ)=1/(j+2:ℝ) at e
  simpa using e

/-- If three noncollinear points all see `T` at unit distance, infinitely many
points do: rotate one of the three around its triangle's circumcenter. -/
theorem fresh {d : ℕ} (a : Fin 3 → E d)
    (tri : LinearIndependent ℝ (fun i : Fin 2 => a i.succ-a 0)) (T S : Finset (E d))
    (hT : T.Nonempty) (adj : ∀ i, ∀ y ∈ T, dist (a i) y=1) :
    ∃ z ∉ S, ∀ y ∈ T, dist z y=1 := by
  classical
  obtain ⟨b,hb⟩ := hT
  let v (i : Fin 2) := a i.succ-a 0
  let W := Submodule.span ℝ (Set.range v)
  have dim : Module.finrank ℝ W = 2 := (finrank_span_eq_card tri).trans (Fintype.card_fin _)
  let iso := ((stdOrthonormalBasis ℝ W).reindex (finCongr dim)).repr
  let o := a 0 + W.starProjection (b-a 0)
  have off (y : E d) (hy : y ∈ T) : y-o ∈ Wᗮ := by
    have diff : y-b ∈ Wᗮ := by
      intro w hw
      refine Submodule.span_induction (p:=fun w _ => inner ℝ w (y-b)=0) ?_ (by simp) ?_ ?_ hw
      · rintro _ ⟨i,rfl⟩
        have sq (x z : E d) (h : dist x z=1) : ‖x‖^2 - 2*inner ℝ x z+‖z‖^2=1 := by
          rw [←norm_sub_sq_real,←dist_eq_norm,h]; norm_num
        simp only [v,inner_sub_left,inner_sub_right]
        linarith only [sq _ _ (adj i.succ _ hy),sq _ _ (adj i.succ _ hb),
          sq _ _ (adj 0 _ hy),sq _ _ (adj 0 _ hb)]
      · intro x z _ _ hx hz; simp [inner_add_left,hx,hz]
      · intro x z _ hz; simp [real_inner_smul_left,hz]
    rw [show y-o = (y-b)+(b-a 0-W.starProjection (b-a 0)) by dsimp [o]; abel]
    exact Wᗮ.add_mem diff (W.sub_starProjection_mem_orthogonal (b-a 0))
  have w₀ : a 0-o ∈ W := by
    change a 0-(a 0+W.starProjection _ ) ∈ W
    simpa using W.neg_mem (W.starProjection_apply_mem (b-a 0))
  have w₁ : a 1-o ∈ W := by
    have hv : a 1-a 0 ∈ W := Submodule.subset_span ⟨(0:Fin 2),rfl⟩
    convert W.add_mem hv w₀ using 1; abel
  have pyth (x y : E d) (hx : x-o ∈ W) (hy : y ∈ T) :
      (dist x y)^2=‖x-o‖^2+‖y-o‖^2 := by
    rw [dist_eq_norm,show x-y=(x-o)-(y-o) by abel,norm_sub_sq_real,
      Submodule.inner_right_of_mem_orthogonal hx (off y hy),mul_zero,sub_zero]
  let r := ‖a 0-o‖
  have hr : 0<r := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro hr
    have hh := pyth (a 1) b w₁ hb
    have hg := pyth (a 0) b w₀ hb
    rw [adj _ _ hb] at hh hg
    change 0=‖a 0-o‖ at hr
    have eq₀ := sub_eq_zero.mp (norm_eq_zero.mp hr.symm)
    have eq₁ : a 1=o := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith only [hh,hg,hr]))
    exact tri.ne_zero 0 (sub_eq_zero.mpr (eq₁.trans eq₀.symm))
  let f (i : ℕ) : E d := o + (iso.symm (r • circ i) : W)
  have hf (i : ℕ) : f i-o ∈ W := by simpa [f] using (iso.symm (r • circ i)).property
  have hnorm (i : ℕ) : ‖f i-o‖=r := by
    simp only [f,add_sub_cancel_left]
    change ‖iso.symm (r • circ i)‖ = r
    rw [iso.symm.norm_map,norm_smul,Real.norm_eq_abs,abs_of_pos hr,circ_norm,mul_one]
  have inj : Function.Injective f := by
    intro i j he
    have hW : iso.symm (r • circ i) = iso.symm (r • circ j) :=
      Subtype.ext (add_left_cancel he)
    exact circ_inj ((smul_right_injective _ hr.ne') (iso.symm.injective hW))
  by_contra! bad
  have sub : (range (S.card+1)).image f ⊆ S := by
    rintro z hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp hz
    by_contra hn
    obtain ⟨y,hy,hno⟩ := bad (f i) hn
    have he := pyth (f i) y (hf i) hy
    rw [hnorm] at he
    have hbase := pyth (a 0) y w₀ hy
    rw [adj _ y hy] at hbase
    change (1:ℝ)^2 = r^2+‖y-o‖^2 at hbase
    exact hno (by nlinarith [show 0 ≤ dist (f i) y from dist_nonneg])
  have h := card_le_card sub
  rw [card_image_of_injective _ inj,card_range] at h
  omega

private noncomputable def unit {Z : Type*} [MetricSpace Z] (S : Finset Z) :=
  S.sym2.filter fun e => dist e.out.1 e.out.2 = 1

private lemma mem_unit {Z : Type*} [MetricSpace Z] {S : Finset Z} {x y : Z} :
    Sym2.mk x y ∈ unit S ↔ x ∈ S ∧ y ∈ S ∧ dist x y=1 := by
  let e := Sym2.mk x y
  have h : Sym2.mk e.out.1 e.out.2 = Sym2.mk x y := e.out_eq
  have hd : dist e.out.1 e.out.2 = dist x y := by
    rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> rw [h₁,h₂]
    exact dist_comm ..
  change e ∈ S.sym2.filter _ ↔ _
  simp only [mem_filter,hd]
  exact (and_congr_left fun _ => mk_mem_sym2_iff).trans and_assoc

lemma append_count {d : ℕ} (A : Finset (E d)) (x : E d) (hx : x ∉ A) :
    unitDistNum (insert x A) = (OMA.Slices1085.neigh A x).card + unitDistNum A := by
  classical
  let N := OMA.Slices1085.neigh A x
  let p := Sym2.mk x
  have inj : Function.Injective p := by
    intro a b he
    rcases Sym2.eq_iff.mp he with h | h
    · exact h.2
    · exact h.2.trans h.1
  have U : unit (insert x A) = N.image p ∪ unit A := by
    ext e
    constructor
    · induction e using Sym2.ind with | _ a b =>
      intro h
      obtain ⟨ha,hb,hd⟩ := mem_unit.mp h
      rcases mem_insert.mp ha with hax | hA
      · subst a
        have hb' : b∈A := (mem_insert.mp hb).resolve_left (fun eq => by simp [eq] at hd)
        exact mem_union_left _ (mem_image_of_mem p (mem_filter.mpr ⟨hb',hd⟩))
      · rcases mem_insert.mp hb with hbx | hB
        · subst b
          apply mem_union_left
          exact mem_image.mpr ⟨a,mem_filter.mpr ⟨hA,(dist_comm _ _).trans hd⟩,Sym2.eq_swap⟩
        · exact mem_union_right _ (mem_unit.mpr ⟨hA,hB,hd⟩)
    · intro h
      rcases mem_union.mp h with h | h
      · obtain ⟨y,hy,rfl⟩ := mem_image.mp h
        exact mem_unit.mpr ⟨mem_insert_self ..,mem_insert_of_mem (mem_filter.mp hy).1,(mem_filter.mp hy).2⟩
      · exact filter_subset_filter _ (sym2_mono (subset_insert ..)) h
  have dis : Disjoint (N.image p) (unit A) := by
    apply disjoint_left.mpr
    rintro _ he hl
    obtain ⟨y,_,rfl⟩ := mem_image.mp he
    exact hx (mem_unit.mp hl).1
  change (unit (insert x A)).card = N.card + (unit A).card
  rw [U,card_union_of_disjoint dis,card_image_of_injective _ inj]

/-- Replacing one vertex by a fresh common neighbor converts extremality into
a uniform degree bound. The one lost point accounts for a possibly erased member of T. -/
theorem deficit {d : ℕ} (S T : Finset (E d)) (sub : T ⊆ S) (z : E d) (hz : z ∉ S)
    (hit : ∀ y ∈ T, dist z y=1)
    (opt : ∀ B : Finset (E d), B.card=S.card → unitDistNum B ≤ unitDistNum S)
    (x : E d) (hx : x∈S) :
    (S \ OMA.Slices1085.neigh S x).card + T.card ≤ S.card+1 := by
  classical
  let A := S.erase x
  have hzA : z ∉ A := fun h => hz (mem_of_mem_erase h)
  have hxA : x ∉ A := by simp [A]
  have hrec : insert x A = S := insert_erase hx
  have sz : (insert z A).card = S.card := by rw [←hrec,card_insert_of_notMem hzA,card_insert_of_notMem hxA]
  have O := opt _ sz
  rw [append_count A z hzA,←hrec,append_count A x hxA] at O
  have ht : T.erase x ⊆ OMA.Slices1085.neigh A z := by
    intro y hy
    obtain ⟨hyx,hyT⟩ := mem_erase.mp hy
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨hyx,sub hyT⟩,hit _ hyT⟩
  have hdiff := card_sdiff_add_card_eq_card (show OMA.Slices1085.neigh S x ⊆ S from filter_subset ..)
  have hsub : OMA.Slices1085.neigh A x ⊆ OMA.Slices1085.neigh S x :=
    filter_subset_filter _ (erase_subset ..)
  have hT := card_le_card ht
  have hN := card_le_card hsub
  by_cases hxt : x ∈ T
  · rw [card_erase_of_mem hxt] at hT; omega
  · rw [erase_eq_of_notMem hxt] at hT; omega

end OMA.Replace1085

/- Pairwise unit-linked anchor triangles force their common unit neighbors
onto a sphere in a three-dimensional affine space. -/

namespace OMA.Anchors1085
open Finset
open scoped Classical

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

private lemma four {d : ℕ} {a b c e : E d} (hac : dist a c = 1) (hae : dist a e = 1)
    (hbc : dist b c = 1) (hbe : dist b e = 1) : inner ℝ (a-b) (c-e) = 0 := by
  have sq (x y : E d) (h : dist x y = 1) : ‖x‖^2 - 2*inner ℝ x y + ‖y‖^2 = 1 := by
    rw [←norm_sub_sq_real,←dist_eq_norm,h]; norm_num
  simp only [inner_sub_left,inner_sub_right]
  linarith only [sq _ _ hac,sq _ _ hae,sq _ _ hbc,sq _ _ hbe]

private lemma joint_indep {d k : ℕ} (v : Fin k → Fin 2 → E d)
    (hv : ∀ i, LinearIndependent ℝ (v i))
    (ho : ∀ i j, i ≠ j → ∀ t u, inner ℝ (v i t) (v j u) = 0) :
    LinearIndependent ℝ (fun z : Fin k × Fin 2 => v z.1 z.2) := by
  rw [Fintype.linearIndependent_iff]
  intro c h
  let s (i : Fin k) := ∑ t, c (i,t) • v i t
  have hs : ∑ i, s i = 0 := by simpa [s,Fintype.sum_prod_type] using h
  have orth (i j : Fin k) (hne : i ≠ j) : inner ℝ (s i) (s j) = 0 := by
    simp [s,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,ho i j hne]
  rintro ⟨i,t⟩
  have hi : s i = 0 := by
    apply (inner_self_eq_zero (𝕜:=ℝ)).mp
    calc
      inner ℝ (s i) (s i) = ∑ j, inner ℝ (s i) (s j) :=
        (sum_eq_single i (fun j _ hji => orth i j hji.symm) (by simp)).symm
      _ = 0 := by rw [←inner_sum,hs,inner_zero_right]
  exact (Fintype.linearIndependent_iff.mp (hv i)) (fun u => c (i,u)) hi t

/-- A common-neighbor class of `k` mutually unit-linked noncollinear triangles
in dimension `2k+3` embeds isometrically on a sphere in ℝ³. -/
theorem common {d k : ℕ} (hd : d = 2*k+3) (hk : 0 < k)
    (a : Fin k → Fin 3 → E d) (tri : ∀ i, LinearIndependent ℝ (fun t : Fin 2 => a i t.succ-a i 0))
    (cross : ∀ i j, i ≠ j → ∀ t u, dist (a i t) (a j u) = 1)
    (Q : Finset (E d)) (adj : ∀ x ∈ Q, ∀ i t, dist x (a i t) = 1) :
    ∃ (f : E d → E 3) (r : ℝ), (∀ x ∈ Q, ‖f x‖ = r) ∧
      ∀ x ∈ Q, ∀ y ∈ Q, dist (f x) (f y) = dist x y := by
  let v (i : Fin k) (t : Fin 2) := a i t.succ-a i 0
  let D (z : Fin k × Fin 2) := v z.1 z.2
  let W := Submodule.span ℝ (Set.range D)
  let K := Wᗮ
  have joint : LinearIndependent ℝ D :=
    joint_indep v tri fun i j hij t u => four (cross i j hij _ _) (cross i j hij _ _)
      (cross i j hij _ _) (cross i j hij _ _)
  have dimW : Module.finrank ℝ W = k*2 := by simpa [W] using finrank_span_eq_card joint
  have dimK : Module.finrank ℝ K = 3 := by
    have H := W.finrank_add_finrank_orthogonal
    rw [dimW,finrank_euclideanSpace_fin] at H
    change Module.finrank ℝ Wᗮ = _; omega
  let iso := ((stdOrthonormalBasis ℝ K).reindex (finCongr dimK)).repr
  let z := a ⟨0,hk⟩ 0
  let f (x : E d) := iso (K.orthogonalProjectionOnto (x-z))
  have diff (x : E d) (hx : x ∈ Q) (y : E d) (hy : y ∈ Q) : x-y ∈ K := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => inner ℝ w (x-y) = 0) ?_ (by simp) ?_ ?_ hw
    · rintro _ ⟨⟨i,t⟩,rfl⟩
      rw [real_inner_comm]
      exact four (adj x hx i _) (adj x hx i _) (adj y hy i _) (adj y hy i _)
    · intro b c _ _ hb hc; simp [inner_add_left,hb,hc]
    · intro b c _ hc; simp [real_inner_smul_left,hc]
  have dis (x : E d) (hx : x ∈ Q) (y : E d) (hy : y ∈ Q) : dist (f x) (f y) = dist x y := by
    rw [show dist (f x) (f y) = dist (K.orthogonalProjectionOnto (x-z)) (K.orthogonalProjectionOnto (y-z)) from iso.dist_map ..,
      dist_eq_norm,←map_sub,sub_sub_sub_cancel_right,←Submodule.norm_coe,
      Submodule.coe_orthogonalProjectionOnto_apply,Submodule.starProjection_eq_self_iff.mpr (diff x hx y hy),←dist_eq_norm]
  by_cases h : Q.Nonempty
  · obtain ⟨o,ho⟩ := h
    refine ⟨f,‖f o‖,?_,dis⟩
    intro x hx
    have hx' : ‖x-z‖=1 := (dist_eq_norm x z).symm.trans (adj x hx _ _)
    have ho' : ‖o-z‖=1 := (dist_eq_norm o z).symm.trans (adj o ho _ _)
    have proj : W.orthogonalProjectionOnto (x-z) = W.orthogonalProjectionOnto (o-z) := by
      rw [←sub_eq_zero,←map_sub,sub_sub_sub_cancel_right]
      exact W.orthogonalProjectionOnto_apply_of_mem_orthogonal (diff x hx o ho)
    have ex := Submodule.norm_sq_eq_add_norm_sq_projection (x-z) W
    have eo := Submodule.norm_sq_eq_add_norm_sq_projection (o-z) W
    rw [hx',proj] at ex; rw [ho'] at eo
    simp only [f,iso.norm_map]
    change ‖Wᗮ.orthogonalProjectionOnto (x-z)‖ = ‖Wᗮ.orthogonalProjectionOnto (o-z)‖
    nlinarith [norm_nonneg (Wᗮ.orthogonalProjectionOnto (x-z)),norm_nonneg (Wᗮ.orthogonalProjectionOnto (o-z))]
  · exact ⟨f,0,fun _ hx => (h ⟨_,hx⟩).elim,dis⟩

private noncomputable def unit {Z : Type*} [MetricSpace Z] (S : Finset Z) :=
  S.sym2.filter fun e => dist e.out.1 e.out.2 = 1

private theorem mem_unit {Z : Type*} [MetricSpace Z] {S : Finset Z} {x y : Z} :
      Sym2.mk x y ∈ unit S ↔ x ∈ S ∧ y ∈ S ∧ dist x y = 1 := by
    let e := Sym2.mk x y
    have h : Sym2.mk e.out.1 e.out.2 = Sym2.mk x y := e.out_eq
    have hd : dist e.out.1 e.out.2 = dist x y := by
      rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> rw [h₁,h₂]
      exact dist_comm ..
    change e ∈ S.sym2.filter _ ↔ _
    simp only [mem_filter,hd]
    exact (and_congr_left fun _ => mk_mem_sym2_iff).trans and_assoc

theorem image_count {X Y : Type*} [MetricSpace X] [MetricSpace Y] [DecidableEq Y] (A : Finset X)
    (f : X → Y) (hf : ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) = dist x y) :
    (A.image f).card = A.card ∧ unitDistNum A ≤ unitDistNum (A.image f) := by
  classical
  have inj : Set.InjOn f (A:Set X) := by
    intro x hx y hy he
    exact dist_eq_zero.mp (by rw [←hf x hx y hy,he,dist_self])
  refine ⟨card_image_of_injOn inj,?_⟩
  apply Finset.card_le_card_of_injOn (s:=unit A) (t:=unit (A.image f)) (Sym2.map f)
  · refine Sym2.ind fun x y he => ?_
    obtain ⟨hx,hy,hd⟩ := mem_unit.mp he
    exact mem_unit.mpr ⟨mem_image_of_mem f hx,mem_image_of_mem f hy,(hf x hx y hy).trans hd⟩
  · intro e he g hg H
    induction e using Sym2.ind with | _ x y =>
    induction g using Sym2.ind with | _ v w =>
    obtain ⟨hx,hy,-⟩ := mem_unit.mp he
    obtain ⟨hv,hw,-⟩ := mem_unit.mp hg
    rcases Sym2.eq_iff.mp H with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Sym2.eq_iff.mpr (.inl ⟨inj hx hv h₁,inj hy hw h₂⟩)
    · exact Sym2.eq_iff.mpr (.inr ⟨inj hx hw h₁,inj hy hv h₂⟩)

/-- A purely finite anchor condition suffices for the `p` small-sphere partition.
The condition does not prescribe coordinates, radii, or a Lenz decomposition. -/
theorem partition_isometric {d k : ℕ} (hd : d=2*k+3) (hk : 0<k) (S : Finset (E d))
    (a : Fin (k+1) → Fin 3 → E d)
    (tri : ∀ i, LinearIndependent ℝ (fun t : Fin 2 => a i t.succ-a i 0))
    (cross : ∀ i j, i ≠ j → ∀ t u, dist (a i t) (a j u) = 1)
    (cover : ∀ x ∈ S, ∃ i, ∀ j, j ≠ i → ∀ t, dist x (a j t) = 1) :
    ∃ B : Fin (k+1) → Finset (E d), (Pairwise fun i j => Disjoint (B i) (B j)) ∧
      univ.biUnion B = S ∧ ∀ i, ∃ (g : E d → E 3) (r : ℝ),
        (∀ x ∈ B i, ‖g x‖=r) ∧ ∀ x ∈ B i, ∀ y ∈ B i, dist (g x) (g y)=dist x y := by
  classical
  let col (x : E d) : Fin (k+1) := if h : x ∈ S then (cover x h).choose else 0
  let B (i : Fin (k+1)) := S.filter (fun x => col x = i)
  refine ⟨B,?_,?_,?_⟩
  · intro i j hij
    exact disjoint_left.mpr (fun _ hx hy => hij ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2))
  · ext x; simp [B]
  · intro i
    have hadj (x) (hx : x ∈ B i) (j : Fin k) (t : Fin 3) : dist x (a (i.succAbove j) t) = 1 := by
      obtain ⟨hs,hi⟩ := mem_filter.mp hx
      have hcol : (cover x hs).choose = i := by simpa [col,hs] using hi
      exact (cover x hs).choose_spec _ (hcol ▸ i.succAbove_ne j) _
    exact common hd hk (fun j => a (i.succAbove j)) (fun j => tri _)
      (fun j l h => cross _ _ (Fin.succAbove_right_injective.ne h)) (B i) hadj

end OMA.Anchors1085

/- Recover fixed common-neighbor anchors from the approximate Lenz partition.
The finite counting argument separates Swanepoel's stability input from
incidences on the large circular and spherical core blocks. -/

namespace OMA.Core1085
open Finset
open scoped Classical

/-- All but one core has circular neighborhoods, and proper slices of the
distinguished spherical core coincide once they share three points. -/
theorem anchors {V : Type*} [DecidableEq V] {k m : ℕ} (hm : 2 ≤ m) (S : Finset V)
    (C : Fin (k+1) → Finset V) (N : V → Finset V)
    (sub : ∀ i, C i ⊆ S) (dis : Pairwise fun i j => Disjoint (C i) (C j))
    (large : ∀ i, 10*m ≤ (C i).card) (degree : ∀ x ∈ S, (S \ N x).card ≤ 12*m)
    (circle : ∀ x ∈ S, ∀ i ≠ 0, ¬ C i ⊆ N x → (C i ∩ N x).card ≤ 2)
    (sphere : ∀ x ∈ S, ∀ y ∈ S, ¬ C 0 ⊆ N x → ¬ C 0 ⊆ N y →
      3 ≤ ((C 0 ∩ N x) ∩ (C 0 ∩ N y)).card → C 0 ∩ N x = C 0 ∩ N y) :
    ∃ a : Fin (k+1) → Fin 3 → V, (∀ i, Function.Injective (a i)) ∧
      (∀ i j, a i j ∈ C i) ∧ ∀ x ∈ S, ∃ i, ∀ j, j ≠ i → ∀ t, a j t ∈ N x := by
  classical
  let miss (x : V) (i : Fin (k+1)) := C i \ N x
  have count (x) (i) : (miss x i).card + (C i ∩ N x).card = (C i).card := card_sdiff_add_card_inter ..
  have pair (x) (hx : x ∈ S) (i j) (hne : i ≠ j) :
      (miss x i).card + (miss x j).card ≤ 12*m := by
    have hd : Disjoint (miss x i) (miss x j) := (dis hne).mono sdiff_subset sdiff_subset
    rw [←card_union_of_disjoint hd]
    apply (card_le_card _).trans (degree x hx)
    apply union_subset
    · intro y hy; exact mem_sdiff.mpr ⟨sub i (mem_sdiff.mp hy).1,(mem_sdiff.mp hy).2⟩
    · intro y hy; exact mem_sdiff.mpr ⟨sub j (mem_sdiff.mp hy).1,(mem_sdiff.mp hy).2⟩
  let bad (x : V) (i : Fin (k+1)) := i ≠ 0 ∧ ¬ C i ⊆ N x
  have cost (x) (hx : x ∈ S) (i) (hi : bad x i) : 10*m ≤ (miss x i).card + 2 := by
    have h := circle x hx i hi.1 hi.2
    have := large i; have := count x i; omega
  have uniq (x) (hx : x ∈ S) (i j) (hi : bad x i) (hj : bad x j) : i=j := by
    by_contra h
    have H := pair x hx i j h; have := cost x hx i hi; have := cost x hx j hj; omega
  have near (x) (hx : x ∈ S) (hb : ∃ i, bad x i) : (miss x 0).card ≤ 2*m+2 := by
    obtain ⟨i,hi⟩ := hb
    have := cost x hx i hi; have := pair x hx i 0 hi.1; omega
  have base : ∃ T ⊆ C 0, 3 ≤ T.card ∧ ∀ x ∈ S, (∃ i, bad x i) → T ⊆ N x := by
    by_cases H : ∃ x ∈ S, (∃ i, bad x i) ∧ ¬ C 0 ⊆ N x
    · obtain ⟨o,ho,bo,po⟩ := H
      let T := C 0 ∩ N o
      have cb := count o 0
      have nb := near o ho bo
      have lb := large 0
      refine ⟨T,inter_subset_left,by dsimp [T]; omega,?_⟩
      intro x hx bx
      by_cases full : C 0 ⊆ N x
      · exact inter_subset_left.trans full
      · have compare := card_inter_add_card_union T (C 0 ∩ N x)
        have cap : (T ∪ (C 0 ∩ N x)).card ≤ (C 0).card :=
          card_le_card (union_subset inter_subset_left inter_subset_left)
        have shared : 3 ≤ (T ∩ (C 0 ∩ N x)).card := by
          have := near x hx bx; have := count x 0; dsimp [T] at *; omega
        have same := sphere o ho x hx po full shared
        change C 0 ∩ N o ⊆ _
        exact same ▸ inter_subset_right
    · refine ⟨C 0,Subset.rfl,by have := large 0; omega,?_⟩
      intro x hx bx
      by_contra hn; exact H ⟨x,hx,bx,hn⟩
  obtain ⟨T,hT,hTc,hTN⟩ := base
  let blocks (i : Fin (k+1)) := if i=0 then T else C i
  have subB (i) : blocks i ⊆ C i := by by_cases h : i=0 <;> simp [blocks,h,hT]
  have bigB (i) : 3 ≤ (blocks i).card := by
    by_cases h : i=0
    · simpa [blocks,h] using hTc
    · simpa [blocks,h] using (by have := large i; omega : 3 ≤ (C i).card)
  have three (i) : ∃ a : Fin 3 → V, Function.Injective a ∧ ∀ t, a t ∈ blocks i := by
    let e := Fintype.equivFin (blocks i)
    have hs : 3 ≤ Fintype.card (blocks i) := by simpa using bigB i
    exact ⟨fun t => (e.symm (Fin.castLE hs t)).val,
      Subtype.val_injective.comp (e.symm.injective.comp (Fin.castLE_injective hs)),
      fun t => (e.symm (Fin.castLE hs t)).property⟩
  choose a hin ha using three
  refine ⟨a,hin,fun i t => subB i (ha i t),?_⟩
  intro x hx
  by_cases hb : ∃ i, bad x i
  · obtain ⟨i,hi⟩ := hb
    refine ⟨i,?_⟩
    intro j hji t
    by_cases hj : j=0
    · subst j
      exact hTN x hx ⟨i,hi⟩ (by simpa [blocks] using ha 0 t)
    · have full : C j ⊆ N x := by
        by_contra hh; exact hji (uniq x hx j i ⟨hj,hh⟩ hi)
      exact full (subB j (ha j t))
  · refine ⟨0,?_⟩
    intro j hj t
    have full : C j ⊆ N x := by by_contra hh; exact hb ⟨j,hj,hh⟩
    exact full (subB j (ha j t))

end OMA.Core1085

/- Approximate spherical core stability suffices for the sharp odd-dimensional upper bound. -/

namespace OMA.Upgrade1085
open Finset EuclideanGeometry
open scoped Classical

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The weak quantitative part of geometric stability used here: one spherical core,
the remaining circular cores, all with complete cross distances. The unassigned
exceptional points are not required to lie on any sphere. -/
def Approximate (d k n : ℕ) : Prop :=
  ∃ (S : Finset (E d)) (C : Fin (k+1) → Finset (E d)) (m : ℕ),
    S.card=n ∧ Erdos1085.f d n ≤ unitDistNum S ∧ 2 ≤ m ∧ n+1 ≤ 10*m*k+12*m ∧
    (∀ i, C i ⊆ S) ∧ (Pairwise fun i j => Disjoint (C i) (C j)) ∧
    (∀ i, 10*m ≤ (C i).card) ∧ (∀ i, Cospherical (C i : Set (E d))) ∧
    Module.finrank ℝ (vectorSpan ℝ (C 0 : Set (E d))) ≤ 3 ∧
    (∀ i ≠ 0, Module.finrank ℝ (vectorSpan ℝ (C i : Set (E d))) ≤ 2) ∧
    ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, dist x y=1

private lemma incidence_triangle {d : ℕ} (C : Finset (E d)) (h : 3 ≤ C.card) :
    ∃ a : Fin 3 → E d, Function.Injective a ∧ ∀ t, a t ∈ C := by
  let e := Fintype.equivFin C
  have hs : 3 ≤ Fintype.card C := by simpa using h
  exact ⟨fun t => (e.symm (Fin.castLE hs t)).val,
    Subtype.val_injective.comp (e.symm.injective.comp (Fin.castLE_injective hs)),
    fun t => (e.symm (Fin.castLE hs t)).property⟩

private lemma le_f {d n : ℕ} (B : Finset (E d)) (hn : B.card=n) :
    unitDistNum B ≤ Erdos1085.f d n := by
  unfold Erdos1085.f
  refine le_ciSup₂ (f := fun (A : Finset (E d)) (_ : A.card=n) => unitDistNum A) ?_ B hn
  refine ⟨n.choose 2,?_⟩
  intro k hk
  obtain ⟨T,hT⟩ := Set.mem_iUnion.mp hk
  obtain ⟨c,rfl⟩ := Set.mem_range.mp hT
  simpa only [c] using unitDistNum_le_choose_two T

theorem upgrade_isometric {d k n : ℕ} (hd : d=2*k+3) (hk : 0<k) (stable : Approximate d k n) :
    ∃ B : Fin (k+1) → Finset (E d), (Pairwise fun i j => Disjoint (B i) (B j)) ∧
      (univ.biUnion B).card=n ∧ Erdos1085.f d n ≤ unitDistNum (univ.biUnion B) ∧
      ∀ i, ∃ (g : E d → E 3) (r : ℝ), (∀ x ∈ B i, ‖g x‖=r) ∧
        ∀ x ∈ B i, ∀ y ∈ B i, dist (g x) (g y)=dist x y := by
  classical
  obtain ⟨S,C,m,hSn,ext,hm,size,sub,dis,large,sph,h₃,h₂,cross⟩ := stable
  let N := OMA.Slices1085.neigh S
  let T := univ.biUnion fun j : Fin k => C j.succ
  have hTsub : T ⊆ S := by
    intro y hy
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hy
    exact sub _ hj
  have sizeT : 10*m*k ≤ T.card := by
    dsimp [T]
    rw [card_biUnion (by intro i _ j _ hij; exact dis (Fin.succ_injective _ |>.ne hij))]
    calc
      10*m*k = ∑ _i : Fin k, 10*m := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum (fun i _ => large _)
  obtain ⟨a,ai,aC⟩ := incidence_triangle (C 0) (by have := large 0; omega)
  have hTpos : T.Nonempty := by
    rw [←Finset.card_pos]; exact lt_of_lt_of_le (by positivity) sizeT
  have hit (i : Fin 3) (y) (hy : y ∈ T) : dist (a i) y = 1 := by
    obtain ⟨j,_,h⟩ := mem_biUnion.mp hy
    exact cross 0 j.succ (Fin.succ_ne_zero j).symm _ (aC i) _ h
  obtain ⟨z,hz,hzT⟩ := OMA.Replace1085.fresh a (OMA.Slices1085.triangle (sph 0) aC ai) T S hTpos hit
  have deg (x) (hx : x ∈ S) : (S \ N x).card ≤ 12*m := by
    have hh := OMA.Replace1085.deficit S T hTsub z hz hzT
      (fun B hc => (le_f B (hc.trans hSn)).trans ext) x hx
    change (S \ N x).card+T.card ≤ S.card+1 at hh
    omega
  have meet (i) (x) : C i ∩ N x = OMA.Slices1085.neigh (C i) x := by
    ext q
    simp only [mem_inter,OMA.Slices1085.neigh,N,mem_filter]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,sub _ h.1,h.2⟩⟩
  have proper (i) (x) (h : ¬C i ⊆ N x) : ¬∀ y∈C i, dist x y =1 := by
    intro e
    exact h (fun y hy => mem_filter.mpr ⟨sub _ hy,e _ hy⟩)
  obtain ⟨anchor,inject,member,cover⟩ := OMA.Core1085.anchors hm S C N sub dis large deg
    (fun x _ i hi h => (meet i x) ▸ OMA.Slices1085.circle _ (sph i) (h₂ i hi) x (proper _ _ h))
    (by
      intro x hx y hy px py shared
      simp only [meet] at shared ⊢
      exact OMA.Slices1085.sphere _ (sph 0) h₃ x y (proper _ _ px) (proper _ _ py) shared)
  obtain ⟨B,db,union,blocks⟩ := OMA.Anchors1085.partition_isometric hd hk S anchor
    (fun i => OMA.Slices1085.triangle (sph i) (member i) (inject i))
    (fun i j hij t u => cross i j hij _ (member i t) _ (member j u))
    (by intro x hx; obtain ⟨i,hi⟩ := cover x hx
        exact ⟨i,fun j hji t => (mem_filter.mp (hi j hji t)).2⟩)
  exact ⟨B,db,union ▸ hSn,union ▸ ext,blocks⟩

theorem upgrade {d k n : ℕ} (hd : d=2*k+3) (hk : 0<k) (stable : Approximate d k n) :
    ∃ B : Fin (k+1) → Finset (E d), (Pairwise fun i j => Disjoint (B i) (B j)) ∧
      (univ.biUnion B).card=n ∧ Erdos1085.f d n ≤ unitDistNum (univ.biUnion B) ∧
      ∀ i, ∃ (A : Finset (E 3)) (r : ℝ), A.card=(B i).card ∧
        (∀ x ∈ A, ‖x‖=r) ∧ unitDistNum (B i) ≤ unitDistNum A := by
  obtain ⟨B,dis,card,ext,h⟩ := upgrade_isometric hd hk stable
  refine ⟨B,dis,card,ext,?_⟩
  intro i
  obtain ⟨g,r,hr,hdist⟩ := h i
  have count := OMA.Anchors1085.image_count (B i) g hdist
  refine ⟨(B i).image g,r,count.1,?_,count.2⟩
  rintro x hx
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
  exact hr y hy

end OMA.Upgrade1085

/- From near-extremal unit-distance density and a large partial partition
with sparse interiors to large, almost completely linked classes. -/

namespace OMA.Trim1085
open Finset Filter
open scoped Classical

private noncomputable def unit {Z : Type*} [MetricSpace Z] (S : Finset Z) :=
  S.sym2.filter fun e => dist e.out.1 e.out.2 = 1

private lemma mem_unit {Z : Type*} [MetricSpace Z] {S : Finset Z} {x y : Z} :
    Sym2.mk x y ∈ unit S ↔ x ∈ S ∧ y ∈ S ∧ dist x y=1 := by
  let e := Sym2.mk x y
  have h : Sym2.mk e.out.1 e.out.2 = Sym2.mk x y := e.out_eq
  have hd : dist e.out.1 e.out.2 = dist x y := by
    rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> rw [h₁,h₂]
    exact dist_comm ..
  change e ∈ S.sym2.filter _ ↔ _
  simp only [mem_filter,hd]
  exact (and_congr_left fun _ => mk_mem_sym2_iff).trans and_assoc

private lemma append_count {X : Type*} [MetricSpace X] (A : Finset X) (x : X) (hx : x ∉ A) :
    unitDistNum (insert x A) = ((A.filter fun y => dist x y=1)).card + unitDistNum A := by
  classical
  let N := (A.filter fun y => dist x y=1)
  let p := Sym2.mk x
  have inj : Function.Injective p := by
    intro a b he
    rcases Sym2.eq_iff.mp he with h | h
    · exact h.2
    · exact h.2.trans h.1
  have U : unit (insert x A) = N.image p ∪ unit A := by
    ext e
    constructor
    · induction e using Sym2.ind with | _ a b =>
      intro h
      obtain ⟨ha,hb,hd⟩ := mem_unit.mp h
      rcases mem_insert.mp ha with hax | hA
      · subst a
        have hb' : b∈A := (mem_insert.mp hb).resolve_left (fun eq => by simp [eq] at hd)
        exact mem_union_left _ (mem_image_of_mem p (mem_filter.mpr ⟨hb',hd⟩))
      · rcases mem_insert.mp hb with hbx | hB
        · subst b
          apply mem_union_left
          exact mem_image.mpr ⟨a,mem_filter.mpr ⟨hA,(dist_comm _ _).trans hd⟩,Sym2.eq_swap⟩
        · exact mem_union_right _ (mem_unit.mpr ⟨hA,hB,hd⟩)
    · intro h
      rcases mem_union.mp h with h | h
      · obtain ⟨y,hy,rfl⟩ := mem_image.mp h
        exact mem_unit.mpr ⟨mem_insert_self ..,mem_insert_of_mem (mem_filter.mp hy).1,(mem_filter.mp hy).2⟩
      · exact filter_subset_filter _ (sym2_mono (subset_insert ..)) h
  have dis : Disjoint (N.image p) (unit A) := by
    apply disjoint_left.mpr
    rintro _ he hl
    obtain ⟨y,_,rfl⟩ := mem_image.mp he
    exact hx (mem_unit.mp hl).1
  change (unit (insert x A)).card = N.card + (unit A).card
  rw [U,card_union_of_disjoint dis,card_image_of_injective _ inj]


private noncomputable def miss {X : Type*} [MetricSpace X] (x : X) (A : Finset X) :=
  (A.filter (fun y => dist x y ≠ 1)).card

/-- Count all ordered nonedges, including diagonal pairs. -/
private theorem missing_identity {X : Type*} [MetricSpace X] (A : Finset X) :
    (∑ x ∈ A, miss x A) + 2*unitDistNum A = A.card^2 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [miss,unitDistNum]
  | @insert x A hx ih =>
    let good := (A.filter fun y => dist x y=1).card
    have step (z : X) : miss z (insert x A) = miss z A + if dist x z=1 then 0 else 1 := by
      unfold miss
      by_cases h : dist z x = 1
      · simp [filter_insert,h,dist_comm x z]
      · simp [filter_insert,h,dist_comm x z,hx]
    have count : (∑ z ∈ A, if dist x z=1 then 0 else 1) = miss x A := by
      simp [miss,Finset.sum_ite]
    have together : good + miss x A = A.card := by
      exact card_filter_add_card_filter_not _
    rw [sum_insert hx,step,append_count A x hx,card_insert_of_notMem hx]
    simp_rw [step]
    rw [sum_add_distrib,count]
    simp only [dist_self,zero_ne_one,if_false]
    change _ + 2*(good + unitDistNum A) = _
    nlinarith

private noncomputable def deficit {X : Type*} [MetricSpace X] {p : ℕ}
    (A : Fin p → Finset X) (i : Fin p) (x : X) := ∑ j ∈ univ.erase i, miss x (A j)

private theorem count {X : Type*} [MetricSpace X] {p : ℕ} (S : Finset X)
    (A : Fin p → Finset X) (sub : ∀ i, A i ⊆ S)
    (dis : Pairwise fun i j => Disjoint (A i) (A j)) :
    (∑ i, ∑ x ∈ A i, deficit A i x) + ∑ i, (A i).card^2 + 2*unitDistNum S ≤
      S.card^2 + 2*∑ i, unitDistNum (A i) := by
  classical
  let U := univ.biUnion A
  have us : U ⊆ S := by intro x hx; obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx; exact sub i hi
  have per (i : Fin p) (x : X) : deficit A i x + miss x (A i) ≤ miss x S := by
    rw [deficit,sum_erase_add _ _ (mem_univ i)]
    let B (j : Fin p) := (A j).filter (fun y => dist x y≠1)
    have ds : ((univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint B :=
      fun i _ j _ h => (dis h).mono (filter_subset ..) (filter_subset ..)
    calc
      _ = (univ.biUnion B).card := (card_biUnion ds).symm
      _ ≤ _ := card_le_card (by
        intro y hy
        obtain ⟨j,_,hy⟩ := mem_biUnion.mp hy
        exact mem_filter.mpr ⟨sub j (mem_filter.mp hy).1,(mem_filter.mp hy).2⟩)
  have double : (∑ i, ∑ x ∈ A i, deficit A i x) + (∑ i, ∑ x ∈ A i, miss x (A i)) ≤
      ∑ x∈S,miss x S := calc
    _ = ∑ i, ∑ x ∈ A i, (deficit A i x + miss x (A i)) := by simp only [sum_add_distrib]
    _ ≤ ∑ i, ∑ x ∈ A i, miss x S := sum_le_sum fun i _ => sum_le_sum fun x _ => per i x
    _ = ∑ x ∈ U, miss x S := (sum_biUnion (fun i _ j _ hij => dis hij)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg us (by intros; omega)
  have inside : (∑ i, ∑ x ∈ A i, miss x (A i)) + 2*∑ i, unitDistNum (A i) =
      ∑ i, (A i).card^2 := by
    rw [mul_sum,←sum_add_distrib]
    exact sum_congr rfl (fun i _ => missing_identity (A i))
  have e := missing_identity S
  omega

/-- The same quadratic slack controls both the missing cross edges and the
squared deviation of each block size from the balanced size. -/
private theorem variance {p : ℕ} (hp : 1 ≤ p) (n η D : ℝ) (a : Fin p → ℝ)
    (hn : 0 ≤ n) (hη : 0 ≤ η) (cover : n-η*n ≤ ∑ i, a i)
    (edges : D + ∑ i, (a i)^2 ≤ n^2/p + 4*η*n^2) :
    D + ∑ i, (a i - n/p)^2 ≤ 6*η*n^2 := by
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have expand : (∑ i, (a i-n/p)^2) =
      (∑ i, (a i)^2) - (2*n/p)*(∑ i, a i) + (p:ℝ)*(n/p)^2 := by
    simp_rw [show ∀ i, (a i-n/p)^2 = (a i)^2 - (2*n/p)*a i + (n/p)^2 by intro i; ring,
      sum_add_distrib,sum_sub_distrib,←mul_sum]
    simp
  have low := mul_le_mul_of_nonneg_left cover (by positivity : 0 ≤ 2*n/(p:ℝ))
  have scale : (p:ℝ)*(n/p)^2 = n^2/p := by field_simp
  have low' : (2*n/p)*(n-η*n) = 2*(n^2/p) - 2*(η*n^2/p) := by ring
  have smaller : η*n^2/(p:ℝ) ≤ η*n^2 := div_le_self (by positivity) hp'
  rw [expand,scale]
  rw [low'] at low
  linarith

/-- Delete from each class the vertices with more than e missing neighbors
across all other classes together. -/
private theorem trim {X : Type*} [MetricSpace X] {p e : ℕ} (A : Fin p → Finset X)
    (bound : (∑ i, ∑ x ∈ A i, deficit A i x) ≤ e^2) :
    ∃ B : Fin p → Finset X, (∀ i, B i ⊆ A i) ∧ (∀ i, (A i).card ≤ (B i).card + e) ∧
      ∀ i j, i ≠ j → ∀ x∈B i, ((B j).filter fun y => dist x y ≠ 1).card ≤ e := by
  classical
  let B (i : Fin p) := (A i).filter (fun x => deficit A i x ≤ e)
  refine ⟨B,fun _ => filter_subset ..,?_,?_⟩
  · intro i
    let C := (A i).filter (fun x => ¬ deficit A i x ≤ e)
    have h : C.card * (e+1) ≤ e^2 := calc
      _ = ∑ _x ∈ C, (e+1) := by simp
      _ ≤ ∑ x ∈ C, deficit A i x := sum_le_sum (fun x hx => by
        have := (mem_filter.mp hx).2
        omega)
      _ ≤ ∑ x ∈ A i, deficit A i x := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; omega)
      _ ≤ _ := (single_le_sum (fun j _ => Nat.zero_le (∑ x ∈ A j, deficit A j x)) (mem_univ i)).trans bound
    have small : C.card ≤ e := by
      by_contra! he
      have hh := Nat.mul_le_mul_right (e+1) (show e+1 ≤ C.card by omega)
      nlinarith
    have size : (B i).card+C.card = (A i).card := card_filter_add_card_filter_not _
    omega
  · intro i j hij x hx
    have part : miss x (A j) ≤ deficit A i x :=
      single_le_sum (fun u _ => Nat.zero_le (miss x (A u))) (mem_erase.mpr ⟨hij.symm,mem_univ _⟩)
    exact (card_le_card (filter_subset_filter _ (filter_subset ..))).trans (part.trans (mem_filter.mp hx).2)

/-- Choose the deletion threshold and the target class size with room for
the later geometric purification. -/
private theorem budgets (p F L : ℕ) (hp : 0<p) (gap : 10*p<L) :
    ∃ δ > (0:ℝ), ∀ᶠ n : ℕ in atTop, ∃ m e : ℕ, 2 ≤ m ∧ n+1 ≤ L*m ∧
      δ*n ≤ e ∧ (10*m+(F+2)*e:ℕ) ≤ (n:ℝ)/p := by
  let g : ℝ := 1/(p:ℝ)-10/(L:ℝ)
  have hp' : (0:ℝ)<p := by exact_mod_cast hp
  have hL : (0:ℝ)<L := by exact_mod_cast (by omega : 0<L)
  have hg : 0<g := by
    dsimp [g]
    apply sub_pos.mpr ((div_lt_div_iff₀ hL hp').mpr ?_)
    exact_mod_cast (by simpa using gap : 10*p<1*L)
  let δ := g/(2*((F:ℝ)+2))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have rate : ((F:ℝ)+2)*δ = g/2 := by dsimp [δ]; field_simp
  refine ⟨δ,hδ,?_⟩
  filter_upwards [eventually_ge_atTop L, tendsto_natCast_atTop_atTop.eventually_ge_atTop
    (2*((F:ℝ)+12)/g)] with n hn big
  let m := n/L+1
  let e := ⌈δ*(n:ℝ)⌉₊
  have hLnat : 0<L := by omega
  have hm : 2 ≤ m := by have h := (Nat.le_div_iff_mul_le hLnat).mpr (by simpa using hn : 1*L≤n); dsimp [m]; omega
  refine ⟨m,e,hm,Nat.lt_mul_div_succ n hLnat,Nat.le_ceil _,?_⟩
  have m' : (m:ℝ) ≤ (n:ℝ)/L+1 := by
    dsimp [m]; push_cast; exact add_le_add_left Nat.cast_div_le 1
  have e' : (e:ℝ) ≤ δ*n+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have room := (div_le_iff₀ hg).mp big
  have h1 := mul_le_mul_of_nonneg_left e' (by positivity : (0:ℝ)≤(F:ℝ)+2)
  have h2 := mul_le_mul_of_nonneg_left m' (by norm_num : (0:ℝ)≤10)
  rw [mul_add,←mul_assoc,rate] at h1
  push_cast
  dsimp [g] at h1 room
  simp only [div_eq_mul_inv] at h1 h2 room ⊢
  linarith only [h1,h2,room]

theorem extract {X : Type*} [MetricSpace X] {k : ℕ} (hk : 0<k) :
    ∃ η > (0:ℝ), ∀ᶠ n : ℕ in atTop, ∀ (S : Finset X) (A : Fin (k+1) → Finset X),
    S.card=n → (∀ i, A i ⊆ S) → (Pairwise fun i j => Disjoint (A i) (A j)) →
    ((S \ univ.biUnion A).card:ℝ) ≤ η*n → (∑ i, (unitDistNum (A i):ℝ)) ≤ η*(n:ℝ)^2 →
    ((k:ℝ)/(2*(k+1))-η)*(n:ℝ)^2 ≤ unitDistNum S →
    ∃ (B : Fin (k+1) → Finset X) (m e : ℕ),
      (∀ i, B i ⊆ A i) ∧ 2 ≤ m ∧ n+1 ≤ 10*m*k+12*m ∧
      (∀ i, 10*m+(k+1)*(2*k+5)*e ≤ (B i).card) ∧
      ∀ i j, i≠j → ∀ x∈B i, ((B j).filter fun y => dist x y ≠ 1).card ≤ e := by
  let p := k+1
  let F := (k+1)*(2*k+5)
  let L := 10*k+12
  have hp : 0<p := by dsimp [p]; omega
  obtain ⟨δ,hδ,hs⟩ := budgets p F L hp (by dsimp [p,L]; omega)
  let η := δ^2/6
  have hη : 0<η := by dsimp [η]; positivity
  refine ⟨η,hη,?_⟩
  filter_upwards [hs] with n hn
  obtain ⟨m,e,hm,lower,threshold,budget⟩ := hn
  intro S A card sub dis outside interior edges
  let D := ∑ i, ∑ x ∈ A i, deficit A i x
  let a (i : Fin p) : ℝ := (A i).card
  have hsize : (∑ i, (A i).card) + (S \ univ.biUnion A).card = n := by
    rw [←card_biUnion (by intro i _ j _ hij; exact dis hij),←card]
    rw [add_comm]
    apply card_sdiff_add_card_eq_card
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    exact sub i hi
  have hsizeR : (∑ i, a i) + ((S \ univ.biUnion A).card:ℝ) = n := by dsimp only [a,p]; exact_mod_cast hsize
  have raw := count S A sub dis
  rw [card] at raw
  have rawR : (D:ℝ) + (∑ i, (a i)^2) + 2*(unitDistNum S:ℝ) ≤
      (n:ℝ)^2 + 2*∑ i, (unitDistNum (A i):ℝ) := by dsimp only [a,D,p]; exact_mod_cast raw
  have algebra : 2*((k:ℝ)/(2*((k:ℝ)+1)))*(n:ℝ)^2 = (n:ℝ)^2 - (n:ℝ)^2/p := by
    dsimp [p]; push_cast; field_simp; ring
  have hd := variance (show 1≤p by omega) n η D a (by positivity) hη.le
    (by linarith) (by nlinarith only [rawR,interior,edges,algebra])
  have db : 6*η*(n:ℝ)^2 ≤ (e:ℝ)^2 := by
    calc
      _ = (δ*n)^2 := by dsimp [η]; ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) threshold 2
  have dv := hd.trans db
  have vs : 0 ≤ ∑ i, (a i-(n:ℝ)/p)^2 := sum_nonneg (by intros; positivity)
  obtain ⟨B,bsub,retained,linked⟩ := trim A (e:=e) (by
    change D ≤ e^2
    exact_mod_cast (by linarith : (D:ℝ) ≤ (e:ℝ)^2))
  refine ⟨B,m,e,bsub,hm,?_,?_,linked⟩
  · apply lower.trans_eq; dsimp [L]; ring
  · intro i
    have one : (a i-(n:ℝ)/p)^2 ≤ ∑ j, (a j-(n:ℝ)/p)^2 :=
      single_le_sum (fun j _ => sq_nonneg (a j-(n:ℝ)/p)) (mem_univ i)
    have bound : (a i-(n:ℝ)/p)^2 ≤ (e:ℝ)^2 := by linarith [Nat.cast_nonneg (α:=ℝ) D]
    have hi : (n:ℝ)/p ≤ a i+e := by
      have h := sq_le_sq.mp bound
      rw [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) e)] at h
      linarith [(abs_le.mp h).1]
    have left : a i ≤ ((B i).card:ℝ)+e := by dsimp only [a]; exact_mod_cast retained i
    have rb : 10*(m:ℝ)+((F:ℝ)+2)*e ≤ (n:ℝ)/p := by exact_mod_cast budget
    change 10*m+F*e ≤ (B i).card
    exact_mod_cast (by linarith : 10*(m:ℝ)+(F:ℝ)*e ≤ (B i).card)

end OMA.Trim1085

/- Unit-distance adjacency has linear rank at most `d+2` after the
paraboloid lift. A nearly complete multipartite graph therefore contains
large exactly cross-unit subconfigurations. -/

namespace OMA.Purify1085
open Finset EuclideanGeometry
open scoped Classical

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- At most `d+2` witnesses determine the entire set of common unit neighbors. -/
theorem witnesses {d : ℕ} (A : Finset (E d)) :
    ∃ T ⊆ A, T.card ≤ d+2 ∧ ∀ x : E d, (∀ t ∈ T, dist t x=1) → ∀ q ∈ A, dist q x=1 := by
  classical
  let lift (x : E d) : E d × (ℝ × ℝ) := (x,‖x‖^2,1)
  let X := lift '' (A:Set (E d))
  obtain ⟨V,sub,card,span,_⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℝ X
  let T := V.image Prod.fst
  have type (v) (hv : v ∈ V) : ∃ a ∈ A, lift a=v := sub hv
  refine ⟨T,?_,?_,?_⟩
  · rintro _ hy; obtain ⟨v,hv,rfl⟩ := mem_image.mp hy
    obtain ⟨a,ha,rfl⟩ := type v hv; exact ha
  · apply card_image_le.trans
    rw [card]
    exact (Submodule.finrank_le _).trans_eq (by simp [Module.finrank_prod])
  · intro x h q hq
    let L (v : E d × (ℝ × ℝ)) := v.2.1 + (‖x‖^2-1)*v.2.2 - 2*inner ℝ v.1 x
    have eq (y : E d) : L (lift y)=0 ↔ dist y x=1 := by
      have e := norm_sub_sq_real y x
      rw [←dist_eq_norm] at e
      change ‖y‖^2 + (‖x‖^2-1)*1 - 2*inner ℝ y x=0 ↔ _
      constructor
      · intro hy; nlinarith [show 0 ≤ dist y x from dist_nonneg]
      · intro hd; rw [hd] at e; linarith
    apply (eq _).mp
    have mem : lift q ∈ Submodule.span ℝ (V : Set (E d × (ℝ × ℝ))) := by
      rw [span]; exact Submodule.subset_span ⟨q,hq,rfl⟩
    refine Submodule.span_induction (p := fun w _ => L w = 0) ?_ ?_ ?_ ?_ mem
    · intro v hv
      obtain ⟨y,hy,rfl⟩ := type v hv
      exact (eq _).mpr (h _ (mem_image_of_mem Prod.fst hv))
    · simp [L]
    · intro u v _ _ hu hv
      change L (u+v) = 0
      simp only [L,Prod.fst_add,Prod.snd_add,inner_add_left] at *
      linarith
    · intro c u _ hu
      change c*u.2.1 + (‖x‖^2-1)*(c*u.2.2) - 2*inner ℝ (c • u.1) x=0
      change u.2.1 + (‖x‖^2-1)*u.2.2 - 2*inner ℝ u.1 x=0 at hu
      rw [real_inner_smul_left]
      linear_combination c*hu

/-- Removing at most `p(d+2)e` points per class turns cross-neighbor deficits
of size `e` into exact unit distances between every two retained classes. -/
theorem purify {d p e : ℕ} (A : Fin p → Finset (E d))
    (near : ∀ i j, i ≠ j → ∀ x ∈ A i, ((A j).filter (fun y => dist x y ≠ 1)).card ≤ e) :
    ∃ C : Fin p → Finset (E d), (∀ i, C i ⊆ A i) ∧
      (∀ i, (A i).card ≤ (C i).card + p*(d+2)*e) ∧
      ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, dist x y = 1 := by
  classical
  choose T sub card sees using fun i => witnesses (A i)
  let bad (i j : Fin p) := (T j).biUnion (fun x => (A i).filter (fun y => dist x y ≠ 1))
  let allBad (i : Fin p) := (univ.erase i).biUnion (bad i)
  let C (i : Fin p) := A i \ allBad i
  refine ⟨C,fun _ => sdiff_subset,?_,?_⟩
  · intro i
    have small (j : Fin p) (h : j ∈ univ.erase i) : (bad i j).card ≤ (d+2)*e := calc
      _ ≤ ∑ x ∈ T j, ((A i).filter (fun y => dist x y ≠ 1)).card := card_biUnion_le
      _ ≤ ∑ _x ∈ T j, e := sum_le_sum fun x hx => near j i (mem_erase.mp h).1 x (sub j hx)
      _ ≤ (d+2)*e := by simpa using Nat.mul_le_mul_right e (card j)
    have bound : (allBad i).card ≤ p*(d+2)*e := calc
      _ ≤ ∑ j ∈ univ.erase i, (bad i j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ univ.erase i, (d+2)*e := sum_le_sum small
      _ ≤ p*((d+2)*e) := by
        simpa using Nat.mul_le_mul_right ((d+2)*e) (show p-1 ≤ p by omega)
      _ = _ := by ring
    exact (card_le_card_sdiff_add_card (s:=A i) (t:=allBad i)).trans (Nat.add_le_add_left bound _)
  · intro i j hij x hx y hy
    have seesX : ∀ t ∈ T j, dist t x=1 := by
      intro t ht
      by_contra h
      exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨j,mem_erase.mpr ⟨hij.symm,mem_univ _⟩,
        mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨(mem_sdiff.mp hx).1,h⟩⟩⟩)
    exact (dist_comm _ _).trans (sees j x seesX y (mem_sdiff.mp hy).1)

end OMA.Purify1085

/- Mutually unit-linked finite blocks occupy orthogonal affine directions. -/

namespace OMA.RankParts1085
open Finset EuclideanGeometry
open scoped Classical DirectSum Pointwise

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

private lemma four {d : ℕ} {a b c e : E d} (hac : dist a c = 1) (hae : dist a e = 1)
    (hbc : dist b c = 1) (hbe : dist b e = 1) : inner ℝ (a-b) (c-e) = 0 := by
  have sq (x y : E d) (h : dist x y = 1) : ‖x‖^2 - 2*inner ℝ x y + ‖y‖^2 = 1 := by
    rw [←norm_sub_sq_real,←dist_eq_norm,h]; norm_num
  simp only [inner_sub_left,inner_sub_right]
  linarith only [sq _ _ hac,sq _ _ hae,sq _ _ hbc,sq _ _ hbe]

theorem rank_sum {d : ℕ} {ι : Type*} [Fintype ι] (C : ι → Finset (E d))
    (cross : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, dist x y=1) :
    ∑ i, Module.finrank ℝ (vectorSpan ℝ (C i : Set (E d))) ≤ d := by
  classical
  let W (i : ι) := vectorSpan ℝ (C i : Set (E d))
  have orth (i j : ι) (hij : i ≠ j) : (W i).IsOrtho (W j) := by
    simp only [W,vectorSpan_def]
    apply Submodule.isOrtho_span.mpr
    rintro _ ⟨a,ha,b,hb,rfl⟩ _ ⟨c,hc,e,he,rfl⟩
    exact four (cross i j hij a ha c hc) (cross i j hij a ha e he)
      (cross i j hij b hb c hc) (cross i j hij b hb e he)
  have family : OrthogonalFamily ℝ (fun i => W i) (fun i => (W i).subtypeₗᵢ) :=
    fun i j h u v => (Submodule.isOrtho_iff_inner_eq.mp (orth i j h)) _ u.property _ v.property
  have h := LinearMap.finrank_le_finrank_of_injective family.independent.dfinsupp_lsum_injective
  change Module.finrank ℝ (⨁ i, W i) ≤ Module.finrank ℝ (E d) at h
  simpa only [Module.finrank_directSum,finrank_euclideanSpace_fin] using h

theorem rank_two {d : ℕ} (C : Finset (E d)) (hs : Cospherical (C:Set (E d)))
    (hc : 3 ≤ C.card) : 2 ≤ Module.finrank ℝ (vectorSpan ℝ (C : Set (E d))) := by
  let e := Fintype.equivFin C
  have hN : 3 ≤ Fintype.card C := by simpa using hc
  let a (t : Fin 3) : E d := (e.symm (Fin.castLE hN t)).val
  have ai : Function.Injective a :=
    Subtype.val_injective.comp (e.symm.injective.comp (Fin.castLE_injective hN))
  have ha (t) : a t ∈ C := (e.symm (Fin.castLE hN t)).property
  have indep := OMA.Slices1085.triangle hs ha ai
  have inc : Submodule.span ℝ (Set.range (fun t : Fin 2 => a t.succ-a 0)) ≤ vectorSpan ℝ (C : Set (E d)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact vsub_mem_vectorSpan ℝ (ha _) (ha _)
  have := Submodule.finrank_mono inc
  rwa [finrank_span_eq_card indep,Fintype.card_fin] at this

theorem classify {d k : ℕ} (hd : d=2*k+3) (hk : 0<k) (C : Fin (k+1) → Finset (E d))
    (hc : ∀ i, 3 ≤ (C i).card)
    (cross : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, dist x y=1) :
    (∀ i, Cospherical (C i : Set (E d))) ∧ ∃ σ : Equiv.Perm (Fin (k+1)),
      Module.finrank ℝ (vectorSpan ℝ (C (σ 0) : Set (E d))) ≤ 3 ∧
      ∀ j ≠ 0, Module.finrank ℝ (vectorSpan ℝ (C (σ j) : Set (E d))) ≤ 2 := by
  classical
  have sph (i) : Cospherical (C i : Set (E d)) := by
    have hsize : Nontrivial (Fin (k+1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨j,hj⟩ := exists_ne i
    obtain ⟨y,hy⟩ := card_pos.mp (by have := hc j; omega : 0 < (C j).card)
    exact ⟨y,1,fun x hx => cross i j hj.symm x hx y hy⟩
  let r (i : Fin (k+1)) := Module.finrank ℝ (vectorSpan ℝ (C i : Set (E d)))
  have minr (i) : 2 ≤ r i := rank_two _ (sph i) (hc i)
  have total := rank_sum C cross
  change ∑ i, r i ≤ d at total
  have shift : (∑ i, (r i - 2)) + 2*(k+1) = ∑ i, r i := by
    rw [show 2*(k+1)=∑ _i : Fin (k+1), 2 by simp [Nat.mul_comm],←sum_add_distrib]
    exact sum_congr rfl (fun i _ => Nat.sub_add_cancel (minr i))
  have excess : (∑ i, (r i - 2)) ≤ 1 := by omega
  have bound (i) : r i ≤ 3 := by
    have hi := single_le_sum (s:=univ) (f:=fun i => r i-2) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  refine ⟨sph,?_⟩
  by_cases high : ∃ i, 2 < r i
  · obtain ⟨i,hi⟩ := high
    let σ := Equiv.swap 0 i
    refine ⟨σ,bound _,?_⟩
    intro j hj
    have hji : σ j ≠ i := by
      intro h
      exact hj (σ.injective (h.trans (Equiv.swap_apply_left 0 i).symm))
    have hh := sum_le_sum_of_subset (f:=fun j => r j-2) (subset_univ {σ j,i})
    rw [sum_pair hji] at hh
    change r (σ j) ≤ 2
    omega
  · exact ⟨Equiv.refl _,bound _,fun j _ => Nat.le_of_not_gt (fun H => high ⟨j,H⟩)⟩

end OMA.RankParts1085

/- Pure graph stability, with no metric description of its classes,
implies the approximate Lenz configuration. -/

namespace OMA.GraphCore1085
open Finset
open scoped Classical

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem toApproximate {d k n m e : ℕ} (hd : d=2*k+3) (hk : 0<k)
    (S : Finset (E d)) (hS : S.card=n) (opt : Erdos1085.f d n ≤ unitDistNum S)
    (A : Fin (k+1) → Finset (E d)) (sub : ∀ i, A i ⊆ S)
    (dis : Pairwise fun i j => Disjoint (A i) (A j))
    (hm : 2 ≤ m) (size : n+1 ≤ (10*k+12)*m)
    (large : ∀ i, 10*m+(k+1)*(d+2)*e ≤ (A i).card)
    (near : ∀ i j, i ≠ j → ∀ x ∈ A i, ((A j).filter (fun y => dist x y ≠ 1)).card ≤ e) :
    OMA.Upgrade1085.Approximate d k n := by
  obtain ⟨C,hC,num,cross⟩ := OMA.Purify1085.purify A near
  have big (i) : 10*m ≤ (C i).card := by have := num i; have := large i; omega
  obtain ⟨sph,σ,h₃,h₂⟩ := OMA.RankParts1085.classify hd hk C (fun i => by have := big i; omega) cross
  refine ⟨S,fun i => C (σ i),m,hS,opt,hm,?_,fun i => (hC _).trans (sub _),?_,fun i => big _,
    fun i => sph _,h₃,h₂,?_⟩
  · exact size.trans_eq (by ring)
  · exact fun i j hij => (dis (σ.injective.ne hij)).mono (hC _) (hC _)
  · exact fun i j hij => cross _ _ (σ.injective.ne hij)

end OMA.GraphCore1085

namespace OMA.Odd1085
open Filter

theorem lower {d : ℕ} (hd : 5 ≤ d) (ho : Odd d) :
    ∃ C > (0:ℝ), ∀ᶠ n : ℕ in atTop,
      ↑(d/2-1)/(2*↑(d/2))*(n:ℝ)^2 + C*(n:ℝ)^(4/3:ℝ) ≤ Erdos1085.f d n :=
  OMA.OddLift1085.lower (by
    refine ⟨1/81,by norm_num,?_⟩
    filter_upwards [eventually_ge_atTop 3] with m hm
    exact OMA.SphereGrid1085.sphere m hm) hd ho

/-- Combine weak geometric stability with the lower construction and the spherical incidence bound. -/
theorem of_core (core : ∀ k : ℕ, 0<k →
    ∀ᶠ n : ℕ in atTop, OMA.Upgrade1085.Approximate (2*k+3) k n) :
    type_of% @Erdos1085.erdos_1085.variants.upper_lower_d5_odd := by
  intro d hd ho
  let k := d/2-1
  have hk : 0<k := by dsimp [k]; omega
  have hdim : d=2*k+3 := by obtain ⟨u,hu⟩ := ho; dsimp [k]; omega
  have parts : d/2=k+1 := by omega
  have stable : ∀ᶠ n : ℕ in atTop, OMA.Upgrade1085.Approximate d k n := hdim ▸ core k hk
  obtain ⟨K,hK,hs⟩ := sphere_bound
  have upper := OMA.OddUpper1085.upper_of_extremal_partition hd hK.le (by
    filter_upwards [stable] with n hn
    obtain ⟨B,dis,card,ext,blocks⟩ := OMA.Upgrade1085.upgrade hdim hk hn
    rw [parts]
    refine ⟨B,dis,card,ext,?_⟩
    intro i
    obtain ⟨A,r,hA,hr,hcount⟩ := blocks i
    have bound := hs A (r^2) (fun x hx => congrArg (fun t : ℝ => t^2) (hr x hx))
    rw [hA] at bound
    exact (Nat.cast_le.mpr hcount).trans bound)
  obtain ⟨c,hc,lo⟩ := lower hd ho
  exact ⟨c,hc,K,lo.and upper⟩

end OMA.Odd1085

/- Pruning by maximizing a quadratic potential over all induced subsets.
  The unit-distance corollary uses the coarse Erdős upper estimate and Lenz
  lower estimate separately, so any checked versions of these bounds suffice. -/

namespace OMA.Prune1085
open Finset Filter Real
open scoped Classical

/-- An edge count with its one-vertex deletion identity admits a large induced
  subset of high minimum degree whenever its upper and lower errors are small. -/
theorem potential {V : Type*} [DecidableEq V] (S : Finset V) (edges : Finset V → ℕ)
    (degree : Finset V → V → ℕ) (α β η L R : ℝ) (hβ : 0 ≤ β) (hgap : β < α)
    (drop : ∀ T ⊆ S, ∀ x ∈ T, edges T = edges (T.erase x) + degree T x)
    (lower : α*(S.card:ℝ)^2-L ≤ edges S)
    (upper : ∀ T ⊆ S, (edges T:ℝ) ≤ α*(T.card:ℝ)^2+R)
    (budget : L+R+β*(S.card:ℝ) ≤ η*(α-β)*(S.card:ℝ)^2) :
    ∃ T ⊆ S, (1-η)*(S.card:ℝ) ≤ T.card ∧ ∀ x ∈ T, 2*β*(T.card:ℝ) ≤ degree T x := by
  classical
  let F (A : Finset V) : ℝ := edges A - β*(A.card:ℝ)*(A.card+1)
  obtain ⟨T,hT,maximum⟩ := S.powerset.exists_max_image F (powerset_nonempty _)
  have sub := mem_powerset.mp hT
  have full := maximum S (mem_powerset.mpr (Subset.rfl))
  have bound := upper T sub
  have cardle : (T.card:ℝ) ≤ S.card := by exact_mod_cast card_le_card sub
  have t0 := Nat.cast_nonneg (α:=ℝ) T.card
  have n0 := Nat.cast_nonneg (α:=ℝ) S.card
  have base : (α-β)*(S.card:ℝ)*((S.card:ℝ)-T.card) ≤ L+R+β*(S.card:ℝ) := by
    dsimp only [F] at full
    nlinarith only [full,bound,lower,mul_nonneg hβ t0,
      mul_nonneg (sub_nonneg.mpr hgap.le) (mul_nonneg t0 (sub_nonneg.mpr cardle))]
  refine ⟨T,sub,?_,?_⟩
  · by_cases h : (S.card:ℝ) = 0
    · rw [h,mul_zero]; exact t0
    · have hpn : 0 < (α-β)*(S.card:ℝ) := mul_pos (sub_pos.mpr hgap) (lt_of_le_of_ne n0 (Ne.symm h))
      have he : (α-β)*(S.card:ℝ)*((S.card:ℝ)-T.card) ≤
          (α-β)*(S.card:ℝ)*(η*(S.card:ℝ)) := (base.trans budget).trans_eq (by ring)
      linarith only [(mul_le_mul_iff_of_pos_left hpn).mp he]
  · intro x hx
    have he := maximum (T.erase x) (mem_powerset.mpr ((erase_subset _ _).trans sub))
    have hc : (T.erase x).card+1 = T.card := card_erase_add_one hx
    have hcR : ((T.erase x).card:ℝ)+1 = T.card := by exact_mod_cast hc
    have hd : (edges T:ℝ) = edges (T.erase x) + (degree T x:ℝ) := by exact_mod_cast drop T sub x hx
    dsimp only [F] at he
    rw [← hcR] at he ⊢
    nlinarith only [he,hd]

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

private lemma unit_drop {d : ℕ} (T : Finset (E d)) (x : E d) (hx : x ∈ T) :
    unitDistNum T = unitDistNum (T.erase x) + (OMA.Slices1085.neigh T x).card := by
  classical
  have h := OMA.Replace1085.append_count (T.erase x) x (by simp)
  rw [insert_erase hx] at h
  have hn : OMA.Slices1085.neigh (T.erase x) x = OMA.Slices1085.neigh T x := by
    ext y
    simp only [OMA.Slices1085.neigh,mem_filter,mem_erase]
    exact ⟨fun a => ⟨a.1.2,a.2⟩, fun a => ⟨⟨fun h => by simp [h] at a,a.1⟩,a.2⟩⟩
  rw [hn, Nat.add_comm] at h
  exact h

private lemma unit_le_f {d : ℕ} (S : Finset (E d)) : unitDistNum S ≤ Erdos1085.f d S.card := by
  apply le_ciSup₂ (f := fun (A : Finset (E d)) (_ : A.card=S.card) => unitDistNum A) _ S rfl
  refine ⟨S.card.choose 2,?_⟩
  intro k hk
  obtain ⟨T,hT⟩ := Set.mem_iUnion.mp hk
  obtain ⟨c,rfl⟩ := Set.mem_range.mp hT
  simpa only [c] using unitDistNum_le_choose_two T

/-- A coarse asymptotic edge bound and a matching Lenz lower bound suffice to
  prune every extremal set. No geometric restriction on the retained subset
  is imposed in advance. -/
theorem eventually_prune {d : ℕ} (α : ℝ) (hα : 0 < α)
    (upper : ∀ ε > (0:ℝ), ∀ᶠ n : ℕ in atTop, (Erdos1085.f d n:ℝ) ≤ (α+ε)*(n:ℝ)^2)
    (lower : ∃ C : ℝ, ∀ n : ℕ, α*(n:ℝ)^2-C ≤ Erdos1085.f d n)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Finset (E d), S.card=n → Erdos1085.f d n ≤ unitDistNum S →
      ∃ T ⊆ S, (1-η)*(n:ℝ) ≤ T.card ∧ ∀ x ∈ T,
        (2*α-δ)*(T.card:ℝ) ≤ (OMA.Slices1085.neigh T x).card := by
  let β := α-min (δ/2) (α/2)
  have hb : 0 ≤ β := by dsimp [β]; linarith [min_le_right (δ/2) (α/2)]
  have hg : β < α := by dsimp [β]; have := lt_min (half_pos hδ) (half_pos hα); linarith
  have hslope : 2*α-δ ≤ 2*β := by dsimp [β]; linarith [min_le_left (δ/2) (α/2)]
  let ε := η*(α-β)/4
  have hε : 0 < ε := div_pos (mul_pos hη (sub_pos.mpr hg)) (by norm_num)
  obtain ⟨C,hl⟩ := lower
  obtain ⟨N,hN⟩ := eventually_atTop.mp (upper ε hε)
  let K := (N:ℝ)^2
  have hK : 0 ≤ K := sq_nonneg _
  have hu (T : Finset (E d)) : (unitDistNum T:ℝ) ≤ (α+ε)*(T.card:ℝ)^2+K := by
    by_cases h : N ≤ T.card
    · exact (show (unitDistNum T:ℝ) ≤ Erdos1085.f d T.card by exact_mod_cast unit_le_f T).trans
        ((hN _ h).trans (le_add_of_nonneg_right hK))
    · have hk : (T.card:ℝ)^2 ≤ K := by
        dsimp [K]
        gcongr; exact_mod_cast (by omega : T.card ≤ N)
      have trivial : (unitDistNum T:ℝ) ≤ (T.card:ℝ)^2 := by
        exact_mod_cast ((unitDistNum_le_choose_two T).trans (Nat.choose_le_pow _ _))
      exact (trivial.trans hk).trans (le_add_of_nonneg_left (by positivity))
  obtain ⟨N₀,hN₀⟩ := exists_nat_ge ((|C|+K+β)/ε)
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
  intro S hcard hext
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) hn)
  have hNb : (|C|+K+β)/ε ≤ n := hN₀.trans (by exact_mod_cast (le_trans (le_max_left _ _) hn))
  have hbnd := (div_le_iff₀ hε).mp hNb
  have hbudget : C + (ε*(S.card:ℝ)^2+K) + β*(S.card:ℝ) ≤ η*(α-β)*(S.card:ℝ)^2 := by
    rw [hcard]
    have h1 := mul_le_mul_of_nonneg_right hbnd (Nat.cast_nonneg (α:=ℝ) n)
    have h2 := mul_le_mul_of_nonneg_left hn1 (add_nonneg (abs_nonneg C) hK)
    have he : η*(α-β) = 4*ε := by dsimp [ε]; ring
    rw [he]
    nlinarith only [h1,h2,le_abs_self C,mul_nonneg hε.le (sq_nonneg (n:ℝ))]
  obtain ⟨T,sub,size,deg⟩ := potential S unitDistNum (fun A x => (OMA.Slices1085.neigh A x).card)
    α β η C (ε*(S.card:ℝ)^2+K) hb hg (fun A _ x hx => unit_drop A x hx)
    (by rw [hcard]; exact (hl n).trans (by exact_mod_cast hext))
    (fun A hA => by
      have hc : (A.card:ℝ)^2 ≤ (S.card:ℝ)^2 := by gcongr
      nlinarith only [hu A,mul_le_mul_of_nonneg_left hc hε.le]) hbudget
  exact ⟨T,sub,hcard ▸ size,fun x hx => (mul_le_mul_of_nonneg_right hslope
    (Nat.cast_nonneg (α:=ℝ) _)).trans (deg x hx)⟩

end OMA.Prune1085

/- The quadratic upper and lower estimates below are the accepted LeftToSolve
  proofs by Ian Qvist (@Genbox), PR #161 (upper, commit c2d5a90) and PR #124
  (Lenz lower, commit 23902d4), reproduced here so the pruning result has
  no unproved dependence on statements in the original problem module.
  https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/161
  https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/124 -/

open Filter
open scoped EuclideanGeometry Finset InnerProductSpace Sym2 Topology

theorem OMA.unit_distance_closed_quadrilateral {d : ℕ} (a b c e : ℝ^d)
    (hac : dist a c = 1) (hae : dist a e = 1) (hbc : dist b c = 1) (hbe : dist b e = 1) :
    ⟪a - b, c - e⟫_ℝ = 0 := by
  simp only [dist_eq_norm] at hac hae hbc hbe
  have h₁ := congrArg (· ^ 2) hac
  have h₂ := congrArg (· ^ 2) hae
  have h₃ := congrArg (· ^ 2) hbc
  have h₄ := congrArg (· ^ 2) hbe
  simp only [norm_sub_sq_real, one_pow] at h₁ h₂ h₃ h₄
  simp only [inner_sub_left, inner_sub_right]
  linarith

theorem OMA.unit_distance_equipartite_dimension {r d : ℕ} (hr : 1 < r)
    (v : Fin r × Fin 3 → ℝ^d) (hv : Function.Injective v)
    (hcross : ∀ (i j : Fin r) (a b : Fin 3), i ≠ j → dist (v (i, a)) (v (j, b)) = 1) :
    r * 2 ≤ d := by
  classical
  let w (i : Fin r) (k : Fin 2) : ℝ^d := v (i, k.succ) - v (i, 0)
  have hblock (i : Fin r) : LinearIndependent ℝ (w i) := by
    let a : Fin r := ⟨0, by omega⟩
    let b : Fin r := ⟨1, hr⟩
    have hab : a ≠ b := by
      intro h
      have hval : (0 : ℕ) = 1 := congrArg Fin.val h
      omega
    obtain ⟨j, hj⟩ : ∃ j : Fin r, i ≠ j := by
      by_cases hi : i = a
      · exact ⟨b, hi ▸ hab⟩
      · exact ⟨a, hi⟩
    let point (k : Fin 3) := v (i, k)
    have hsphere : EuclideanGeometry.Cospherical (Set.range point) := by
      refine ⟨v (j, 0), 1, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact hcross i j k 0 hj
    have hinj : Function.Injective point := by
      intro a b hab
      exact congrArg Prod.snd (hv hab)
    have hlin := (affineIndependent_iff_linearIndependent_vsub ℝ point 0).mp
      (hsphere.affineIndependent (by rfl) hinj)
    exact hlin.comp (fun k : Fin 2 => ⟨k.succ, Fin.succ_ne_zero k⟩)
      (fun _ _ h => Fin.succ_injective _ (congrArg Subtype.val h))
  have hortho (i j : Fin r) (a b : Fin 2) (hij : i ≠ j) :
      ⟪w i a, w j b⟫_ℝ = 0 :=
    OMA.unit_distance_closed_quadrilateral _ _ _ _ (hcross i j a.succ b.succ hij)
      (hcross i j a.succ 0 hij) (hcross i j 0 b.succ hij) (hcross i j 0 0 hij)
  have hall : LinearIndependent ℝ (fun k : Fin r × Fin 2 => w k.1 k.2) := by
    apply linearIndependent_iff'.mpr
    intro s f hf
    let g (k : Fin r × Fin 2) := if k ∈ s then f k else 0
    have hsum : ∑ k : Fin r × Fin 2, g k • w k.1 k.2 = 0 := by
      simpa only [g, ite_smul, zero_smul, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter] using hf
    let z (i : Fin r) := ∑ k : Fin 2, g (i, k) • w i k
    have hzsum : ∑ i, z i = 0 := by
      rw [Fintype.sum_prod_type] at hsum
      exact hsum
    have horthz (i j : Fin r) (hij : i ≠ j) : ⟪z i, z j⟫_ℝ = 0 := by
      simp only [z, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      simp [hortho, hij]
    have hz (i : Fin r) : z i = 0 := by
      have h := congrArg (inner ℝ (z i)) hzsum
      rw [inner_sum, inner_zero_right, Finset.sum_eq_single i] at h
      · exact inner_self_eq_zero.mp h
      · exact fun j _ hji => horthz i j hji.symm
      · simp
    intro k hk
    have h := (linearIndependent_iff'.mp (hblock k.1)) Finset.univ
      (fun u => g (k.1, u)) (hz k.1) k.2 (Finset.mem_univ _)
    simpa [g, hk] using h
  simpa only [Fintype.card_prod, Fintype.card_fin, finrank_euclideanSpace_fin]
    using hall.fintype_card_le_finrank

noncomputable def OMA.unit_dist_graph {d : ℕ} (S : Finset (ℝ^d)) : SimpleGraph S where
  Adj u v := dist (u : ℝ^d) (v : ℝ^d) = 1
  symm := ⟨fun _ _ h => (dist_comm _ _).trans h⟩
  loopless := ⟨fun u h => by
    change dist (u : ℝ^d) (u : ℝ^d) = 1 at h
    simp at h⟩

theorem OMA.unit_dist_graph_free (d : ℕ) (hd : 4 ≤ d) (S : Finset (ℝ^d)) :
    (SimpleGraph.completeEquipartiteGraph (d / 2 + 1) 3).Free (OMA.unit_dist_graph S) := by
  rintro ⟨f⟩
  let v (k : Fin (d / 2 + 1) × Fin 3) : ℝ^d := f k
  have hv : Function.Injective v := fun _ _ h => f.injective (Subtype.ext h)
  have hc (i j : Fin (d / 2 + 1)) (a b : Fin 3) (hij : i ≠ j) :
      dist (v (i, a)) (v (j, b)) = 1 :=
    f.toHom.map_adj (SimpleGraph.completeEquipartiteGraph_adj.mpr hij)
  have := OMA.unit_distance_equipartite_dimension (by omega) v hv hc
  omega

open scoped Classical in
theorem OMA.unit_dist_num_le_edges (d : ℕ) (S : Finset (ℝ^d)) :
    unitDistNum S ≤ (OMA.unit_dist_graph S).edgeFinset.card := by
  classical
  unfold unitDistNum
  apply Finset.card_le_card_of_surjOn (Sym2.map (fun v : S => (v : ℝ^d)))
  intro e he
  obtain ⟨hmem, hdist⟩ := Finset.mem_filter.mp he
  have hrepr : s(e.out.1, e.out.2) = e := Quot.out_eq _
  have hp := Finset.mk_mem_sym2_iff.mp (show s(e.out.1, e.out.2) ∈ S.sym2 by rwa [hrepr])
  let x : S := ⟨e.out.1, hp.1⟩
  let y : S := ⟨e.out.2, hp.2⟩
  refine ⟨s(x, y), ?_, hrepr⟩
  exact SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet (G := OMA.unit_dist_graph S)).mpr hdist)

theorem OMA.unit_dist_le_extremal (d : ℕ) (hd : 4 ≤ d) (n : ℕ) :
    Erdos1085.f d n ≤ SimpleGraph.extremalNumber n
      (SimpleGraph.completeEquipartiteGraph (d / 2 + 1) 3) := by
  classical
  unfold Erdos1085.f
  apply ciSup_le'
  intro S
  apply ciSup_le'
  intro hS
  refine (OMA.unit_dist_num_le_edges d S).trans ?_
  have hs : Fintype.card S = n := (Fintype.card_coe S).trans hS
  rw [← hs]
  exact SimpleGraph.card_edgeFinset_le_extremalNumber (OMA.unit_dist_graph_free d hd S)

theorem OMA.equipartite_extremal_quadratic (p : ℕ) (hp : 0 < p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ n : ℕ,
      (SimpleGraph.extremalNumber n (SimpleGraph.completeEquipartiteGraph (p + 1) 3) : ℝ) ≤
      (1 - 1 / (p : ℝ) + ε) / 2 * ((n : ℝ) * ((n : ℝ) + 1)) + K := by
  classical
  let H := SimpleGraph.completeEquipartiteGraph (p + 1) 3
  let c : ℝ := (1 - 1 / (p : ℝ) + ε) / 2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : 0 ≤ 1 - 1 / (p : ℝ) := sub_nonneg.mpr
    ((div_le_iff₀ hpR).mpr (by simpa only [one_mul] using hp₁))
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hH : H ≠ ⊥ := by
    rw [ne_eq, SimpleGraph.completeEquipartiteGraph_eq_bot_iff]
    omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (SimpleGraph.eventually_completeEquipartiteGraph_isContained_of_minDegree hε p 3)
  let M := max 1 N
  refine ⟨(M : ℝ) ^ 2, ?_⟩
  intro n
  change (SimpleGraph.extremalNumber n H : ℝ) ≤
    c * ((n : ℝ) * ((n : ℝ) + 1)) + (M : ℝ) ^ 2
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < M
    · have hsmall : SimpleGraph.extremalNumber n H ≤ n ^ 2 := by
        rw [← Fintype.card_fin n, SimpleGraph.extremalNumber_le_iff]
        intro G _ hG
        exact G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)
      have hsq : (SimpleGraph.extremalNumber n H : ℝ) ≤ (M : ℝ) ^ 2 := by
        exact_mod_cast hsmall.trans (Nat.pow_le_pow_left hn.le 2)
      exact hsq.trans (le_add_of_nonneg_left (by positivity))
    · have hMn := le_of_not_gt hn
      have hNn : N ≤ n := (le_max_right 1 N).trans hMn
      have h1n : 1 ≤ n := (le_max_left 1 N).trans hMn
      let _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
      obtain ⟨G, hDec, hG⟩ := SimpleGraph.exists_isExtremal_free (V := Fin n) hH
      let _ := hDec
      have hmin : (G.minDegree : ℝ) < (1 - 1 / (p : ℝ) + ε) * n := by
        exact lt_of_not_ge (fun h => hG.prop (hN n hNn h))
      obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
      have hedge : G.edgeFinset.card = SimpleGraph.extremalNumber n H := by
        simpa only [Fintype.card_fin] using SimpleGraph.card_edgeFinset_of_isExtremal_free hG
      have hdeleteNat : G.edgeFinset.card ≤
          SimpleGraph.extremalNumber (n - 1) H + G.degree v := by
        have hdel := SimpleGraph.card_edgeFinset_deleteIncidenceSet_le_extremalNumber hG.prop v
        rw [G.card_edgeFinset_deleteIncidenceSet v, Fintype.card_fin] at hdel
        omega
      have hdelete : (SimpleGraph.extremalNumber n H : ℝ) ≤
          (SimpleGraph.extremalNumber (n - 1) H : ℝ) + (G.minDegree : ℝ) := by
        rw [← hedge, hv]
        exact_mod_cast hdeleteNat
      have hprev := ih (n - 1) (by omega)
      rw [Nat.cast_sub h1n, Nat.cast_one] at hprev
      dsimp [c] at hprev ⊢
      nlinarith only [hdelete, hprev, hmin]

theorem OMA.unit_dist_eventual_upper (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (Erdos1085.f d n : ℝ) ≤
      (((d / 2 - 1 : ℕ) : ℝ) / (2 * ((d / 2 : ℕ) : ℝ)) + ε) * (n : ℝ) ^ 2 := by
  let p := d / 2
  have hp : 0 < p := by dsimp [p]; omega
  let c₀ : ℝ := ((p - 1 : ℕ) : ℝ) / (2 * (p : ℝ))
  let c : ℝ := (1 - 1 / (p : ℝ) + ε) / 2
  have hc : c = c₀ + ε / 2 := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    simp only [c, c₀, Nat.cast_sub hp, Nat.cast_one]
    field_simp
  obtain ⟨K, hK⟩ := OMA.equipartite_extremal_quadratic p hp ε hε
  have hsmall : Tendsto (fun n : ℕ => c + c * (n : ℝ)⁻¹ + K * ((n : ℝ)⁻¹) ^ 2)
      atTop (𝓝 c) := by
    have hn := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      ((tendsto_const_nhds (x := c)).add (hn.const_mul c)).add ((hn.pow 2).const_mul K)
  have hlim : ∀ᶠ n : ℕ in atTop, c + c * (n : ℝ)⁻¹ + K * ((n : ℝ)⁻¹) ^ 2 < c₀ + ε :=
    (tendsto_order.mp hsmall).2 _ (by rw [hc]; linarith)
  filter_upwards [hlim, eventually_gt_atTop (0 : ℕ)] with n hn hpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  have hf : (Erdos1085.f d n : ℝ) ≤
      (SimpleGraph.extremalNumber n (SimpleGraph.completeEquipartiteGraph (p + 1) 3) : ℝ) := by
    exact_mod_cast OMA.unit_dist_le_extremal d hd n
  calc
    (Erdos1085.f d n : ℝ) ≤ c * ((n : ℝ) * ((n : ℝ) + 1)) + K :=
      hf.trans (hK n)
    _ = (c + c * (n : ℝ)⁻¹ + K * ((n : ℝ)⁻¹) ^ 2) * (n : ℝ) ^ 2 := by
      field_simp
    _ ≤ (c₀ + ε) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hn.le (sq_nonneg _)



open scoped EuclideanGeometry Finset Sym2

theorem OMA.lenz_realization (d p n : ℕ) (hp : 0 < p) (hd : 2 * p ≤ d) :
    ∃ v : Fin n ↪ (ℝ^d), ∀ i j : Fin n, (i : ℕ) % p ≠ (j : ℕ) % p → dist (v i) (v j) = 1 := by
  classical
  let a (i : Fin n) : Fin d := ⟨2 * ((i : ℕ) % p), by
    have := Nat.mod_lt (i : ℕ) hp
    omega⟩
  let b (i : Fin n) : Fin d := ⟨2 * ((i : ℕ) % p) + 1, by
    have := Nat.mod_lt (i : ℕ) hp
    omega⟩
  have hab (i j : Fin n) : a i ≠ b j := by
    intro h
    have hval := congrArg Fin.val h
    change 2 * ((i : ℕ) % p) = 2 * ((j : ℕ) % p) + 1 at hval
    omega
  have ha (i j : Fin n) : a i = a j ↔ (i : ℕ) % p = (j : ℕ) % p := by
    rw [← Fin.val_inj]
    change 2 * ((i : ℕ) % p) = 2 * ((j : ℕ) % p) ↔ _
    omega
  have hb (i j : Fin n) : b i = b j ↔ (i : ℕ) % p = (j : ℕ) % p := by
    rw [← Fin.val_inj]
    change 2 * ((i : ℕ) % p) + 1 = 2 * ((j : ℕ) % p) + 1 ↔ _
    omega
  let x (i : Fin n) : ℝ := 1 / ((i.val : ℝ) + 4)
  let y (i : Fin n) : ℝ := Real.sqrt (1 / 2 - x i ^ 2)
  have hx (i : Fin n) : 0 < x i := by
    dsimp [x]
    positivity
  have hxy (i : Fin n) : x i ^ 2 + y i ^ 2 = 1 / 2 := by
    have hbound : x i ≤ 1 / 4 := by
      have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      dsimp [x]
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    have hrad : 0 ≤ 1 / 2 - x i ^ 2 := by nlinarith [hx i]
    dsimp [y]
    rw [Real.sq_sqrt hrad]
    ring
  let v (i : Fin n) : ℝ^d :=
    WithLp.toLp 2 (fun c => if c = a i then x i else if c = b i then y i else 0)
  have hv (i : Fin n) (c : Fin d) :
      v i c = if c = a i then x i else if c = b i then y i else 0 := rfl
  have hnorm (i : Fin n) : (∑ c, (v i c) ^ 2) = 1 / 2 := by
    have hterm (c : Fin d) :
        (v i c) ^ 2 = (if c = a i then x i ^ 2 else 0) + (if c = b i then y i ^ 2 else 0) := by
      rw [hv]
      by_cases h : c = a i
      · subst c
        simp [hab]
      · by_cases h' : c = b i <;> simp [h, h', (hab i i).symm]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simpa using hxy i
  have hinj : Function.Injective v := by
    intro i j hij
    have hcoord : v i (a i) = v j (a i) := congrArg (fun z : ℝ^d => z (a i)) hij
    rw [hv, hv, if_pos rfl] at hcoord
    by_cases h : a i = a j
    · rw [if_pos h] at hcoord
      have hval : (i.val : ℝ) + 4 = (j.val : ℝ) + 4 := by
        have hc : (1 : ℝ) / ((i.val : ℝ) + 4) = 1 / ((j.val : ℝ) + 4) := hcoord
        have hm := (div_eq_div_iff (by positivity) (by positivity)).mp hc
        simpa only [one_mul] using hm.symm
      apply Fin.ext
      exact_mod_cast (add_right_cancel hval)
    · rw [if_neg h, if_neg (hab i j)] at hcoord
      exact (ne_of_gt (hx i) hcoord).elim
  refine ⟨⟨v, hinj⟩, fun i j h => ?_⟩
  change dist (v i) (v j) = 1
  have hterm (c : Fin d) : (v i c - v j c) ^ 2 = (v i c) ^ 2 + (v j c) ^ 2 := by
    by_cases hci : c = a i
    · subst c
      have hzero : v j (a i) = 0 := by
        simp [hv, (ha i j).not.mpr h, hab]
      rw [hzero]
      ring
    · by_cases hci' : c = b i
      · subst c
        have hzero : v j (b i) = 0 := by
          simp [hv, (hab j i).symm, (hb i j).not.mpr h]
        rw [hzero]
        ring
      · have hzero : v i c = 0 := by simp [hv, hci, hci']
        rw [hzero]
        ring
  have hsq : dist (v i) (v j) ^ 2 = 1 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simp_rw [PiLp.sub_apply, hterm]
    rw [Finset.sum_add_distrib, hnorm i, hnorm j]
    norm_num
  nlinarith [dist_nonneg (x := v i) (y := v j)]

theorem OMA.lenz_turan_le (d p n : ℕ) (hp : 0 < p) (hd : 2 * p ≤ d) :
    (SimpleGraph.turanGraph n p).edgeFinset.card ≤ Erdos1085.f d n := by
  classical
  obtain ⟨v, hv⟩ := OMA.lenz_realization d p n hp hd
  let S : Finset (ℝ^d) := Finset.univ.map v
  have hS : S.card = n := by simp [S]
  have hedge : (SimpleGraph.turanGraph n p).edgeFinset.card ≤ unitDistNum S := by
    unfold unitDistNum
    apply Finset.card_le_card_of_injOn (Sym2.map v)
    · intro e he
      induction e using Sym2.inductionOn with
      | _ i j =>
        have hij : (i : ℕ) % p ≠ (j : ℕ) % p :=
          SimpleGraph.turanGraph_adj.mp ((SimpleGraph.mem_edgeSet (G := SimpleGraph.turanGraph n p)).mp
            ((SimpleGraph.mem_edgeFinset (G := SimpleGraph.turanGraph n p)).mp he))
        have hi : v i ∈ S := Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
        have hj : v j ∈ S := Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
        change s(v i, v j) ∈ _
        refine Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr ⟨hi, hj⟩, ?_⟩
        have hout := Quot.out_eq s(v i, v j)
        change s((Quot.out s(v i, v j)).1, (Quot.out s(v i, v j)).2) = s(v i, v j) at hout
        rcases Sym2.eq_iff.mp hout with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · rw [h₁, h₂]
          exact hv i j hij
        · rw [h₁, h₂, dist_comm]
          exact hv i j hij
    · exact (Sym2.map.injective v.injective).injOn
  refine hedge.trans ?_
  unfold Erdos1085.f
  refine le_ciSup₂ (f := fun (T : Finset (ℝ^d)) (_ : T.card = n) => unitDistNum T) ?_ S hS
  refine ⟨n.choose 2, ?_⟩
  intro k hk
  rcases Set.mem_iUnion.mp hk with ⟨T, hT⟩
  obtain ⟨hcard, rfl⟩ := Set.mem_range.mp hT
  simpa only [hcard] using unitDistNum_le_choose_two T

theorem OMA.lenz_turan_bound (n p : ℕ) (hp : 0 < p) :
    ((p - 1 : ℕ) : ℝ) / (2 * (p : ℝ)) * (n : ℝ) ^ 2 - ((p : ℝ) ^ 2 + 1) ≤
      ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) := by
  let r := n % p
  let A := (n ^ 2 - r ^ 2) * (p - 1)
  let B := 2 * p
  have hB : 0 < B := by dsimp [B]; omega
  have hrn : r ≤ n := Nat.mod_le _ _
  have hrp : r ≤ p := (Nat.mod_lt _ hp).le
  have hsub : r ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hrn _
  have hfloor : A < (A / B + 1) * B := by
    apply (Nat.div_lt_iff_lt_mul hB).mp
    omega
  have hfloorR : (A : ℝ) < ((A / B : ℕ) + (1 : ℝ)) * (B : ℝ) := by
    exact_mod_cast hfloor
  have hdiv : (A : ℝ) / (B : ℝ) - 1 ≤ ((A / B : ℕ) : ℝ) := by
    have hBR : (0 : ℝ) < B := by exact_mod_cast hB
    linarith [(div_lt_iff₀ hBR).mpr hfloorR]
  have hAr : (A : ℝ) = ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) * ((p - 1 : ℕ) : ℝ) := by
    simp only [A, Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_pow]
  have hBr : (B : ℝ) = 2 * (p : ℝ) := by simp [B]
  have hcoef : ((p - 1 : ℕ) : ℝ) / (2 * (p : ℝ)) ≤ 1 := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have h : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsquares : (r : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hrp 2
  have herror :
      ((p - 1 : ℕ) : ℝ) / (2 * (p : ℝ)) * (r : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by
    calc
      _ ≤ 1 * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hsquares
  rw [hAr, hBr, sub_mul, sub_div] at hdiv
  rw [SimpleGraph.card_edgeFinset_turanGraph]
  change _ ≤ ((A / B + r.choose 2 : ℕ) : ℝ)
  push_cast
  rw [mul_div_assoc, mul_comm ((n : ℝ) ^ 2), mul_div_assoc, mul_comm ((r : ℝ) ^ 2)] at hdiv
  linarith [Nat.cast_nonneg (α := ℝ) (r.choose 2)]

theorem OMA.Prune1085.lenz : type_of% @Erdos1085.erdos_1085.variants.lower_d4_lenz := by
  intro d hd
  let p := d / 2
  have hp : 0 < p := by dsimp [p]; omega
  have hpd : 2 * p ≤ d := by dsimp [p]; omega
  refine ⟨(p : ℝ) ^ 2 + 1, fun n => ?_⟩
  exact (OMA.lenz_turan_bound n p hp).trans (by exact_mod_cast OMA.lenz_turan_le d p n hp hpd)

namespace OMA.Prune1085

theorem extremal_unit_core {d : ℕ} (hd : 4 ≤ d) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ S : Finset (EuclideanSpace ℝ (Fin d)), S.card=n →
      Erdos1085.f d n ≤ unitDistNum S → ∃ T ⊆ S, (1-η)*(n:ℝ) ≤ T.card ∧
      ∀ x ∈ T, (1-1/((d/2:ℕ):ℝ)-δ)*(T.card:ℝ) ≤ (OMA.Slices1085.neigh T x).card := by
  let p := d/2
  let α : ℝ := ((p-1:ℕ):ℝ)/(2*(p:ℝ))
  have hp : 2 ≤ p := by dsimp [p]; omega
  have hp' : 0 < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hα : 0 < α := div_pos (by exact_mod_cast (by omega : 0 < p-1)) (by positivity)
  have h : 2*α=1-1/(p:ℝ) := by
    dsimp only [α]
    rw [Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_one]
    field_simp
  have H := eventually_prune α hα (OMA.unit_dist_eventual_upper d hd) (lenz hd) hδ hη
  simpa only [h] using H

end OMA.Prune1085

/- Realize extremal unit-distance counts as ordinary finite simple graphs. -/

namespace OMA.UnitGraph1085
open Finset
open scoped Classical

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem attained {d : ℕ} [NeZero d] (n : ℕ) :
    ∃ S : Finset (E d), S.card=n ∧ Erdos1085.f d n ≤ unitDistNum S := by
  classical
  let X : Set ℕ := {k | ∃ S : Finset (E d), S.card=n ∧ unitDistNum S=k}
  obtain ⟨A,ha⟩ := Infinite.exists_subset_card_eq (E d) n
  have hX : X.Nonempty := ⟨_,A,ha,rfl⟩
  have finite : X.Finite := (Set.finite_Iic (n.choose 2)).subset (by
    rintro k ⟨S,hS,rfl⟩; simpa only [Set.mem_Iic,hS] using unitDistNum_le_choose_two S)
  obtain ⟨S,hS,hs⟩ : ∃ S : Finset (E d), S.card=n ∧ unitDistNum S=sSup X := hX.csSup_mem finite
  refine ⟨S,hS,?_⟩
  rw [hs,Erdos1085.f]
  exact ciSup_le' (fun Q => ciSup_le' (fun h => le_csSup finite.bddAbove ⟨Q,h,rfl⟩))

def graph {V X : Type*} [MetricSpace X] (v : V → X) : SimpleGraph V where
  Adj i j := dist (v i) (v j)=1
  symm := ⟨fun i j h => (dist_comm ..).trans h⟩
  loopless := ⟨fun i h => by simp at h⟩

noncomputable instance {V X : Type*} [MetricSpace X] (v : V → X) : DecidableRel (graph v).Adj :=
  fun _ _ => Classical.propDecidable _

private noncomputable def unit {Z : Type*} [MetricSpace Z] (S : Finset Z) :=
  S.sym2.filter fun e => dist e.out.1 e.out.2 = 1

private lemma mem_unit {Z : Type*} [MetricSpace Z] {S : Finset Z} {x y : Z} :
    Sym2.mk x y ∈ unit S ↔ x ∈ S ∧ y ∈ S ∧ dist x y=1 := by
  let e := Sym2.mk x y
  have h : Sym2.mk e.out.1 e.out.2 = Sym2.mk x y := e.out_eq
  have hd : dist e.out.1 e.out.2 = dist x y := by
    rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> rw [h₁,h₂]
    exact dist_comm ..
  change e ∈ S.sym2.filter _ ↔ _
  simp only [mem_filter,hd]
  exact (and_congr_left fun _ => mk_mem_sym2_iff).trans and_assoc

theorem edge_count {d : ℕ} {V : Type*} [Fintype V] (v : V → E d) (hi : Function.Injective v) :
    (graph v).edgeFinset.card = unitDistNum (univ.image v) := by
  classical
  have eq : unit (univ.image v) = (graph v).edgeFinset.image (Sym2.map v) := by
    ext e
    constructor
    · induction e using Sym2.ind with | _ x y =>
      intro h
      obtain ⟨hx,hy,hd⟩ := mem_unit.mp h
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨Sym2.mk i j,SimpleGraph.mem_edgeFinset.mpr hd,rfl⟩
    · intro h
      obtain ⟨z,hz,rfl⟩ := mem_image.mp h
      induction z using Sym2.ind with | _ x y =>
      exact mem_unit.mpr ⟨mem_image_of_mem _ (mem_univ _),mem_image_of_mem _ (mem_univ _),
        SimpleGraph.mem_edgeFinset.mp hz⟩
  change _ = (unit _).card
  rw [eq,card_image_of_injective _ (Sym2.map.injective hi)]

theorem induce_count {d : ℕ} {V : Type*} (v : V → E d) (hi : Function.Injective v)
    (A : Finset V) :
    ((graph v).induce (A:Set V)).edgeFinset.card = unitDistNum (A.image v) := by
  classical
  let w (i : A) := v i.val
  have h := edge_count w (hi.comp Subtype.val_injective)
  change (graph w).edgeFinset.card = _
  rw [h]; congr 1
  ext y
  simp [w]

noncomputable def enumerate {X : Type*} (S : Finset X) {n : ℕ} (hn : S.card=n) : Fin n ↪ X :=
  (S.equivFinOfCardEq hn).symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩

theorem enumerate_image {X : Type*} [DecidableEq X] (S : Finset X) {n : ℕ} (hn : S.card=n) :
    univ.image (enumerate S hn) = S := by
  ext x
  constructor
  · rintro hx; obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact ((S.equivFinOfCardEq hn).symm i).property
  · intro hx
    exact mem_image.mpr ⟨S.equivFinOfCardEq hn ⟨x,hx⟩,mem_univ _,by simp [enumerate]⟩

theorem degree {d : ℕ} {V : Type*} [Fintype V] (v : V → E d) (hi : Function.Injective v) (i : V) :
    (graph v).degree i = (OMA.Slices1085.neigh (univ.image v) (v i)).card := by
  classical
  have h : ((graph v).neighborFinset i).image v = OMA.Slices1085.neigh (univ.image v) (v i) := by
    ext x
    constructor
    · intro hx
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ _), (graph v).mem_neighborFinset _ _ |>.mp hj⟩
    · intro hx
      obtain ⟨xQ,hd⟩ := mem_filter.mp hx
      obtain ⟨j,_,rfl⟩ := mem_image.mp xQ
      exact mem_image.mpr ⟨j,((graph v).mem_neighborFinset _ _).mpr hd,rfl⟩
  rw [←h,card_image_of_injective _ hi]; rfl

end OMA.UnitGraph1085

/- The forbidden complete multipartite graph for odd-dimensional unit distances. -/

namespace OMA.SeedMetric1085
open Finset EuclideanGeometry SimpleGraph
open scoped Classical

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem no_complete {d k : ℕ} (hd : d=2*k+3) {V : Type*} (G : SimpleGraph V)
    (v : V → E d) (hv : Function.Injective v) (edges : ∀ x y, G.Adj x y → dist (v x) (v y)=1) :
    ¬ completeEquipartiteGraph (k+2) 3 ⊑ G := by
  classical
  intro contains
  obtain ⟨f,hf⟩ := SimpleGraph.isContained_iff_exists_le_comap.mp contains
  let a (i : Fin (k+2)) (t : Fin 3) := v (f (i,t))
  let C (i : Fin (k+2)) := univ.image (a i)
  have inj (i) : Function.Injective (a i) := fun t u h => congrArg Prod.snd (f.injective (hv h))
  have card (i) : (C i).card = 3 := (card_image_of_injective _ (inj i)).trans (by simp)
  have cross (i j) (hij : i≠j) : ∀ x ∈ C i, ∀ y ∈ C j, dist x y=1 := by
    rintro x hx y hy
    obtain ⟨t,_,rfl⟩ := mem_image.mp hx
    obtain ⟨u,_,rfl⟩ := mem_image.mp hy
    apply edges
    exact hf (show (completeEquipartiteGraph (k+2) 3).Adj (i,t) (j,u) from completeEquipartiteGraph_adj.mpr hij)
  have sph (i) : Cospherical (C i : Set (E d)) := by
    obtain ⟨j,hj⟩ := exists_ne i
    exact ⟨a j 0,1,fun x hx => cross i j hj.symm x hx _ (mem_image_of_mem _ (mem_univ _))⟩
  have lower (i) := OMA.RankParts1085.rank_two (C i) (sph i) (card i).ge
  have h := (sum_le_sum (s:=univ) (fun i _ => lower i)).trans (OMA.RankParts1085.rank_sum C cross)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  change (k+2)*2 ≤ d at h
  omega

/-- If every member of a designated class sees all three points in every other
anchor triangle, its unit edges are edges on a single three-dimensional sphere. -/
theorem class_sphere {d k : ℕ} (hd : d=2*k+3) (hk : 0<k) {V : Type*}
    (G : SimpleGraph V) (v : V → E d) (hv : Function.Injective v)
    (edges : ∀ x y, G.Adj x y → dist (v x) (v y)=1)
    (b : Fin (k+1) → Fin 3 → V) (bInj : ∀ i, Function.Injective (b i))
    (links : ∀ i j, i ≠ j → ∀ t u, G.Adj (b i t) (b j u))
    (i : Fin (k+1)) (A : Finset V)
    (hit : ∀ x ∈ A, ∀ j, j ≠ i → ∀ t, G.Adj x (b j t)) :
    ∃ (T : Finset (E 3)) (r : ℝ), T.card=A.card ∧ (∀ y∈T, ‖y‖=r) ∧
      unitDistNum (A.image v) ≤ unitDistNum T := by
  classical
  let a (j : Fin (k+1)) (t : Fin 3) := v (b j t)
  have cross (j l) (h : j ≠ l) (t u) : dist (a j t) (a l u)=1 := edges _ _ (links j l h t u)
  have tri (j : Fin (k+1)) : LinearIndependent ℝ (fun t : Fin 2 => a j t.succ-a j 0) := by
    have hsize : Nontrivial (Fin (k+1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨l,hl⟩ := exists_ne j
    have sph : Cospherical ((univ.image (a j) : Finset _) : Set (E d)) := by
      refine ⟨a l 0,1,?_⟩
      rintro _ h; obtain ⟨t,_,rfl⟩ := mem_image.mp h
      exact cross j l hl.symm t 0
    exact OMA.Slices1085.triangle sph (fun t => mem_image_of_mem _ (mem_univ t)) (hv.comp (bInj j))
  obtain ⟨f,r,hr,hi⟩ := OMA.Anchors1085.common hd hk (fun j => a (i.succAbove j)) (fun j => tri _)
    (fun j l hjl => cross _ _ (Fin.succAbove_right_injective.ne hjl)) (A.image v) (by
      rintro y hy j t
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      exact edges _ _ (hit x hx _ (i.succAbove_ne j) t))
  have count := OMA.Anchors1085.image_count (A.image v) f hi
  refine ⟨(A.image v).image f,r,count.1.trans (card_image_of_injective _ hv),?_,count.2⟩
  intro y hy
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
  exact hr _ hx

end OMA.SeedMetric1085

/- Turn partial graph classes from seed counting back into geometric blocks,
with a negligible total number of internal unit distances. -/

namespace OMA.Transport1085
open Finset Filter
open scoped Classical

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem small_interiors (p : ℕ) (K η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (p:ℝ)*K*(n:ℝ)^(4/3:ℝ) ≤ η*(n:ℝ)^2 := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(2/3:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/3)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop ((p:ℝ)*K/η),eventually_ge_atTop (1:ℕ)] with n hn hn1
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hη).mp hn) (Real.rpow_nonneg (Nat.cast_nonneg n) (4/3:ℝ))
  calc
    _ ≤ η*((n:ℝ)^(2/3:ℝ)*(n:ℝ)^(4/3:ℝ)) := h.trans_eq (by ring)
    _ = η*(n:ℝ)^2 := by
      rw [←Real.rpow_add (by exact_mod_cast hn1 : 0<(n:ℝ))]
      norm_num

theorem classes {d k n : ℕ} (hd : d=2*k+3) (hk : 0<k) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V → E d) (vinj : Function.Injective v) (S : Finset (E d))
    (card : S.card=n) (vS : ∀ x, v x ∈ S) (edges : ∀ x y, G.Adj x y → dist (v x) (v y)=1)
    (b : Fin (k+1) → Fin 3 → V) (bInj : ∀ i, Function.Injective (b i))
    (links : ∀ i j, i ≠ j → ∀ t u, G.Adj (b i t) (b j u))
    (B : Fin (k+1) → Finset V) (dis : Pairwise fun i j => Disjoint (B i) (B j))
    (hit : ∀ i, ∀ x ∈ B i, ∀ j, j≠i → ∀ t, G.Adj x (b j t))
    (K : ℝ) (hK : 0≤K)
    (sphere : ∀ (T : Finset (E 3)) (s : ℝ), (∀ x∈T, ‖x‖^2=s) → (unitDistNum T:ℝ) ≤ K*T.card^(4/3:ℝ)) :
    ∃ A : Fin (k+1) → Finset (E d), (∀ i, A i ⊆ S) ∧ (Pairwise fun i j => Disjoint (A i) (A j)) ∧
      (S \ univ.biUnion A).card + (univ.biUnion B).card = n ∧
      (∑ i, (unitDistNum (A i):ℝ)) ≤ ((k+1:ℕ):ℝ)*K*(n:ℝ)^(4/3:ℝ) := by
  classical
  let A (i : Fin (k+1)) := (B i).image v
  have sub (i) : A i ⊆ S := by
    rintro y h; obtain ⟨x,_,rfl⟩ := mem_image.mp h; exact vS x
  have da : Pairwise fun i j => Disjoint (A i) (A j) := by
    intro i j hij
    apply disjoint_left.mpr
    intro y hi hj
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
    obtain ⟨z,hz,he⟩ := mem_image.mp hj
    exact disjoint_left.mp (dis hij) hx (vinj he ▸ hz)
  have us : univ.biUnion A ⊆ S := by
    intro y hy; obtain ⟨i,_,h⟩ := mem_biUnion.mp hy; exact sub i h
  refine ⟨A,sub,da,?_,?_⟩
  · have cA := card_biUnion (s:=univ) (t:=A) (fun i _ j _ h => da h)
    have cB := card_biUnion (s:=univ) (t:=B) (fun i _ j _ h => dis h)
    have hc : (univ.biUnion A).card = (univ.biUnion B).card := by
      rw [cA,cB]; exact sum_congr rfl (fun i _ => card_image_of_injective _ vinj)
    exact hc ▸ (card_sdiff_add_card_eq_card us).trans card
  · have hlocal (i) : (unitDistNum (A i):ℝ) ≤ K*(n:ℝ)^(4/3:ℝ) := by
      obtain ⟨T,r,hc,hr,hu⟩ := OMA.SeedMetric1085.class_sphere hd hk G v vinj edges b bInj links i (B i) (hit i)
      have h := sphere T (r^2) (fun x hx => congrArg (fun t : ℝ => t^2) (hr x hx))
      rw [hc] at h
      have hB : (B i).card ≤ n := (card_image_of_injective (B i) vinj).symm.le.trans ((card_le_card (sub i)).trans_eq card)
      exact (show (unitDistNum (A i):ℝ) ≤ unitDistNum T by exact_mod_cast hu).trans (h.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hB) (by norm_num)) hK))
    simpa [mul_assoc] using sum_le_sum (s:=univ) (fun i _ => hlocal i)

end OMA.Transport1085

/- An almost-complete multipartite seed classifies nearly all vertices of a
graph that excludes a larger complete multipartite graph with three per part. -/
namespace OMA.Seed1085
open Finset SimpleGraph
open scoped Classical

private theorem three {V : Type*} (S : Finset V) (hs : 3 ≤ S.card) :
    ∃ f : Fin 3 ↪ V, ∀ b, f b ∈ S := by
  let e := Fintype.equivFin S
  have h : 3 ≤ Fintype.card S := by simpa using hs
  let f (i : Fin 3) := e.symm (Fin.castLE h i)
  exact ⟨⟨fun i => (f i).1, fun _ _ he =>
    Fin.ext (Fin.mk.inj (e.symm.injective (Subtype.ext he)))⟩, fun i => (f i).2⟩

/-- A cone over p fixed triples contains at most two vertices. -/
theorem common_small {V : Type*} [Fintype V] {p L : ℕ}
    (G : SimpleGraph V) (free : (completeEquipartiteGraph (p+1) 3).Free G)
    (seed : Copy (completeEquipartiteGraph p L) G)
    (pick : Fin p → (Fin 3 ↪ Fin L)) :
    (univ.filter (fun x : V => ∀ i b, G.Adj x (seed (i,pick i b)))).card ≤ 2 := by
  classical
  by_contra! h
  obtain ⟨z,hz⟩ := three (univ.filter (fun x : V => ∀ i b, G.Adj x (seed (i,pick i b)))) h
  have cross (b i t) : G.Adj (z b) (seed (i,pick i t)) :=
    (mem_filter.mp (hz b)).2 i t
  let a (i : Fin (p+1)) (b : Fin 3) : V :=
    Fin.cases (z b) (fun j => seed (j,pick j b)) i
  have adj (i j) (b c) (hij : i ≠ j) : G.Adj (a i b) (a j c) := by
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact (hij rfl).elim
    · exact cross ..
    · exact (cross ..).symm
    · rename_i i j
      exact seed.toHom.map_adj (completeEquipartiteGraph_adj.mpr (fun eq => hij (congrArg Fin.succ eq)))
  have inj (i : Fin (p+1)) : Function.Injective (a i) := by
    cases i using Fin.cases
    · exact z.injective
    · rename_i i
      intro b c eq
      exact (pick i).injective (congrArg Prod.snd (seed.injective eq))
  apply free
  refine ⟨⟨⟨fun u => a u.1 u.2, ?_⟩,?_⟩⟩
  · intro u v h
    exact adj u.1 v.1 u.2 v.2 (completeEquipartiteGraph_adj.mp h)
  · intro u v eq
    by_cases he : u.1 = v.1
    · obtain ⟨i,b⟩ := u
      obtain ⟨j,c⟩ := v
      change i=j at he
      subst j
      exact Prod.ext rfl (inj i eq)
    · exact ((adj _ _ u.2 v.2 he).ne eq).elim

/-- Only a bounded number of vertices see three or more members in every seed class. -/
theorem exceptional_bound {V : Type*} [Fintype V] {p L : ℕ}
    (G : SimpleGraph V) (free : (completeEquipartiteGraph (p+1) 3).Free G)
    (seed : Copy (completeEquipartiteGraph p L) G) :
    (univ.filter (fun x : V => ∀ i : Fin p,
      3 ≤ (univ.filter (fun t : Fin L => G.Adj x (seed (i,t)))).card)).card ≤
        2 * Fintype.card (Fin p → (Fin 3 ↪ Fin L)) := by
  classical
  let bad := univ.filter (fun x : V => ∀ i : Fin p,
    3 ≤ (univ.filter (fun t : Fin L => G.Adj x (seed (i,t)))).card)
  have pick (x : bad) (i : Fin p) :
      ∃ f : Fin 3 ↪ Fin L, ∀ b, G.Adj x.val (seed (i,f b)) := by
    obtain ⟨f,hf⟩ := three _ ((mem_filter.mp x.property).2 i)
    exact ⟨f,fun b => (mem_filter.mp (hf b)).2⟩
  choose pick hpick using pick
  have cover : bad ⊆ univ.biUnion (fun v : Fin p → (Fin 3 ↪ Fin L) =>
      univ.filter (fun x : V => ∀ i b, G.Adj x (seed (i,v i b)))) := by
    intro x hx
    exact mem_biUnion.mpr ⟨pick ⟨x,hx⟩,mem_univ _,mem_filter.mpr ⟨mem_univ _,hpick ⟨x,hx⟩⟩⟩
  refine (card_le_card cover).trans (card_biUnion_le.trans ?_)
  calc
    _ ≤ ∑ _v : (Fin p → (Fin 3 ↪ Fin L)), 2 := sum_le_sum (fun v _ => common_small G free seed v)
    _ = _ := by simp [Nat.mul_comm]

/-- Number of vertices in a seed class missed by a vertex. -/
def misses {V : Type*} {p L : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (seed : Copy (completeEquipartiteGraph p L) G) (x : V) (i : Fin p) : ℕ :=
  (univ.filter fun a : Fin L => ¬G.Adj x (seed (i,a))).card

/-- Counting from the seed side, the non-neighbours of all pL seed vertices
can use at most pLH incidences. -/
theorem total_misses {V : Type*} [Fintype V] {p L H : ℕ} (G : SimpleGraph V)
    (seed : Copy (completeEquipartiteGraph p L) G)
    (degree : ∀ i a, (univ.filter (fun x : V => ¬G.Adj x (seed (i,a)))).card ≤ H) :
    ∑ x : V, ∑ i : Fin p, misses G seed x i ≤ p*L*H := by
  classical
  have he (x) (i) : misses G seed x i =
      ∑ a : Fin L, (if G.Adj x (seed (i,a)) then 0 else 1) := by
    simp [misses,Finset.sum_ite]
  simp_rw [he]
  rw [sum_comm]
  calc
    _ = ∑ i : Fin p, ∑ a : Fin L, ∑ x : V, (if G.Adj x (seed (i,a)) then 0 else 1) := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ ≤ ∑ _i : Fin p, ∑ _a : Fin L, H := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro a _
      simpa [sum_ite] using degree i a
    _ = _ := by simp [Nat.mul_assoc]

/-- Give every nonexceptional point a class in which it has at most two
neighbors. Most of the missing incidences are consumed in the assigned class. -/
theorem choose_classes {V : Type*} [Fintype V] {p L H : ℕ} (hp : 0<p)
    (G : SimpleGraph V) (free : (completeEquipartiteGraph (p+1) 3).Free G)
    (seed : Copy (completeEquipartiteGraph p L) G)
    (degree : ∀ i a, (univ.filter (fun x : V => ¬G.Adj x (seed (i,a)))).card ≤ H) :
    ∃ f : V → Fin p, (∑ x : V, ∑ i : Fin p, if f x=i then 0 else misses G seed x i) +
      (Fintype.card V - 2*Fintype.card (Fin p → (Fin 3 ↪ Fin L))) * (L-2) ≤ p*L*H := by
  classical
  let bad := univ.filter (fun x : V => ∀ i : Fin p,
    3 ≤ (univ.filter fun a : Fin L => G.Adj x (seed (i,a))).card)
  have hb : bad.card ≤ 2*Fintype.card (Fin p → (Fin 3 ↪ Fin L)) := exceptional_bound G free seed
  have existsClass (x : V) : ∃ i : Fin p, x ∈ bad ∨ L-2 ≤ misses G seed x i := by
    by_cases h : x ∈ bad
    · exact ⟨⟨0,hp⟩,Or.inl h⟩
    have hh : ¬∀ i : Fin p, 3 ≤ (univ.filter fun a : Fin L => G.Adj x (seed (i,a))).card := by
      intro hz
      exact h (mem_filter.mpr ⟨mem_univ _,hz⟩)
    push Not at hh
    obtain ⟨i,hi⟩ := hh
    have he := Finset.card_filter_add_card_filter_not
      (s:=univ) (fun a : Fin L => G.Adj x (seed (i,a)))
    simp only [card_univ,Fintype.card_fin] at he
    exact ⟨i,Or.inr (by unfold misses; omega)⟩
  choose f hf using existsClass
  refine ⟨f,?_⟩
  have decomp (x) : (∑ i : Fin p, if f x=i then 0 else misses G seed x i) + misses G seed x (f x) =
      ∑ i : Fin p, misses G seed x i := by
    have hex (i : Fin p) : (if f x=i then 0 else misses G seed x i) +
        (if f x=i then misses G seed x i else 0) = misses G seed x i := by split_ifs <;> simp
    simpa only [sum_add_distrib,sum_ite_eq,mem_univ,if_true] using Finset.sum_congr (s₁:=univ) rfl (fun i _ => hex i)
  have used : (Fintype.card V - bad.card)*(L-2) ≤ ∑ x : V, misses G seed x (f x) := by
    calc
      _ = ∑ x ∈ univ \ bad, (L-2) := by simp [card_sdiff_of_subset (subset_univ bad)]
      _ ≤ ∑ x ∈ univ \ bad, misses G seed x (f x) := sum_le_sum fun x hx => (hf x).resolve_left (mem_sdiff.mp hx).2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
  calc
    _ ≤ (∑ x : V, ∑ i : Fin p, if f x=i then 0 else misses G seed x i) +
        ∑ x : V, misses G seed x (f x) := by
      apply Nat.add_le_add_left
      exact (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hb _)).trans used
    _ = ∑ x : V, ∑ i : Fin p, misses G seed x i := by rw [← sum_add_distrib]; exact sum_congr rfl fun x _ => decomp x
    _ ≤ _ := total_misses G seed degree

private def loss {V : Type*} [Fintype V] {p L : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (seed : Copy (completeEquipartiteGraph p L) G)
    (f : V → Fin p) (i : Fin p) (t : Fin L) : Finset V :=
  univ.filter fun x => f x ≠ i ∧ ¬G.Adj x (seed (i,t))

private theorem total_loss {V : Type*} [Fintype V] {p L : ℕ} (G : SimpleGraph V)
    (seed : Copy (completeEquipartiteGraph p L) G) (f : V → Fin p) :
    (∑ i : Fin p, ∑ t : Fin L, (loss G seed f i t).card) =
      ∑ x : V, ∑ i : Fin p, if f x=i then 0 else misses G seed x i := by
  classical
  have hc (i t) : (loss G seed f i t).card =
      ∑ x : V, if f x≠i ∧ ¬G.Adj x (seed (i,t)) then 1 else 0 := by
    simp [loss]
  simp_rw [hc]
  conv_lhs => enter [2,i]; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro i _
  by_cases h : f x=i
  · simp [h]
  · simp [h,misses,sum_ite]

private theorem inexpensive_triple {L T : ℕ} (hL : 3 ≤ L) (w : Fin L → ℕ)
    (hw : ∑ a, w a ≤ (L-2)*T) : ∃ t : Fin 3 ↪ Fin L, ∀ b, w (t b) ≤ T := by
  classical
  let good := univ.filter fun j => w j ≤ T
  have hg : 3 ≤ good.card := by
    by_contra! h
    let high := univ.filter fun j => ¬ w j ≤ T
    have hsum : good.card + high.card = L := by
      simpa only [good, high, card_univ, Fintype.card_fin] using
        card_filter_add_card_filter_not (s:=univ) (fun a : Fin L => w a ≤ T)
    have hh : L-2 ≤ high.card := by omega
    have he := calc
      (L-2)*(T+1) ≤ high.card*(T+1) := Nat.mul_le_mul_right _ hh
      _ = ∑ _a ∈ high, (T+1) := by simp
      _ ≤ ∑ a ∈ high, w a := sum_le_sum fun a ha => by have := (mem_filter.mp ha).2; omega
      _ ≤ ∑ a, w a := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
    rw [Nat.mul_add,Nat.mul_one] at he
    omega
  obtain ⟨t,ht⟩ := three good hg
  exact ⟨t,fun b => (mem_filter.mp (ht b)).2⟩

theorem extract {V : Type*} [Fintype V] [DecidableEq V] {p L H T : ℕ} (hp : 0<p) (hL : 3≤L)
    (G : SimpleGraph V) (free : (completeEquipartiteGraph (p+1) 3).Free G)
    (seed : Copy (completeEquipartiteGraph p L) G)
    (degree : ∀ i a, (univ.filter (fun x : V => ¬G.Adj x (seed (i,a)))).card ≤ H)
    (budget : p*L*H ≤ (Fintype.card V - 2*Fintype.card (Fin p → (Fin 3 ↪ Fin L)))*(L-2) +
      (L-2)*T) :
    ∃ (t : Fin p → (Fin 3 ↪ Fin L)) (A : Fin p → Finset V),
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (univ \ univ.biUnion A).card ≤ p*3*T ∧
      ∀ i x, x ∈ A i → ∀ j, j≠i → ∀ b, G.Adj x (seed (j,t j b)) := by
  classical
  obtain ⟨f,hf⟩ := choose_classes hp G free seed degree
  have htotal : ∑ i : Fin p, ∑ a : Fin L, (loss G seed f i a).card ≤ (L-2)*T := by
    rw [total_loss]
    omega
  have hchoose (i : Fin p) := inexpensive_triple hL (fun a => (loss G seed f i a).card)
    ((single_le_sum (f:=fun j => ∑ a : Fin L, (loss G seed f j a).card)
      (fun j _ => Nat.zero_le _) (mem_univ i)).trans htotal)
  choose t ht using hchoose
  let A (i : Fin p) := univ.filter fun x : V => f x=i ∧
    ∀ j, j≠i → ∀ b, G.Adj x (seed (j,t j b))
  refine ⟨t,A,?_,?_,fun i x hx => (mem_filter.mp hx).2.2⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    exact hij ((mem_filter.mp hxi).2.1.symm.trans (mem_filter.mp hxj).2.1)
  · let lost (u : Fin p × Fin 3) := loss G seed f u.1 (t u.1 u.2)
    have hsub : univ \ univ.biUnion A ⊆ univ.biUnion lost := by
      intro x hx
      have hn : x ∉ A (f x) := fun h => (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨f x,mem_univ _,h⟩)
      have hh : ¬∀ j, j≠f x → ∀ b, G.Adj x (seed (j,t j b)) := by
        exact fun h => hn (mem_filter.mpr ⟨mem_univ _,rfl,h⟩)
      push Not at hh
      obtain ⟨j,hnj,b,hb⟩ := hh
      exact mem_biUnion.mpr ⟨(j,b),mem_univ _,mem_filter.mpr ⟨mem_univ _,hnj.symm,hb⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc
      _ ≤ ∑ _u : Fin p × Fin 3, T := sum_le_sum (fun u _ => ht u.1 u.2)
      _ = _ := by simp

end OMA.Seed1085

/- Minimum degree above the (p−1)-part threshold supplies arbitrarily large
  fixed p-partite seeds. The difference of the thresholds is 1/(p(p−1)). -/

namespace OMA.DenseSeed1085
open Filter SimpleGraph

theorem of_minDegree {p L : ℕ} (hp : 2 ≤ p) {δ : ℝ} (hδ : δ ≤ 1/(2*(p:ℝ)*(p-1))) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : SimpleGraph (Fin m)) [DecidableRel G.Adj],
      (1-1/(p:ℝ)-δ)*(m:ℝ) ≤ G.minDegree → Nonempty (Copy (completeEquipartiteGraph p L) G) := by
  let ε : ℝ := 1/(2*(p:ℝ)*(p-1))
  have hpR : (1:ℝ) < p := by exact_mod_cast hp
  have hp₀ : (0:ℝ) < p := by linarith
  have hp₁ : (0:ℝ) < p-1 := by linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heq : 1-1/((p-1:ℕ):ℝ)+ε = 1-1/(p:ℝ)-ε := by
    rw [Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_one]
    dsimp [ε]
    field_simp
    ring
  filter_upwards [eventually_completeEquipartiteGraph_isContained_of_minDegree hε (p-1) L]
    with m hm
  intro G _ hG
  have h := hm (G:=G) (show (1-1/((p-1:ℕ):ℝ)+ε)*(m:ℝ) ≤ G.minDegree by
    rw [heq]
    exact (mul_le_mul_of_nonneg_right (by dsimp [ε]; linarith only [hδ]) (Nat.cast_nonneg m)).trans hG)
  have hs : p-1+1=p := by omega
  exact (congrArg (fun t => Nonempty (Copy (completeEquipartiteGraph t L) G)) hs).mp h

theorem of_degree {p L : ℕ} (hp : 2 ≤ p) {δ : ℝ} (hδ : δ ≤ 1/(2*(p:ℝ)*(p-1))) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : SimpleGraph (Fin m)) [DecidableRel G.Adj],
      (∀ x, (1-1/(p:ℝ)-δ)*(m:ℝ) ≤ G.degree x) → Nonempty (Copy (completeEquipartiteGraph p L) G) := by
  filter_upwards [of_minDegree (L:=L) hp hδ, eventually_ge_atTop 1] with m hm hm₁
  intro G _ hG
  have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨x,hx⟩ := G.exists_minimal_degree_vertex
  exact hm G (hx ▸ hG x)

end OMA.DenseSeed1085

/- Numerical parameters for pruning a dense graph and selecting three
anchors in each class of a large complete multipartite seed. -/

namespace OMA.SeedStab1085
open Finset SimpleGraph Filter
open scoped Classical

private theorem floor_bound (N p : ℕ) (hp : 0<p) :
    (N:ℝ)/p ≤ ((N/p : ℕ):ℝ)+1 := by
  apply (div_le_iff₀ (by exact_mod_cast hp : (0:ℝ)<p)).mpr
  rw [mul_comm]
  exact_mod_cast (Nat.lt_mul_div_succ N hp).le

private theorem cap {N p L : ℕ} (hp : 0<p) (hL : 0<L) {δ : ℝ}
    (hδ : δ ≤ 1/((p:ℝ)*L)) (G : SimpleGraph (Fin N))
    (degree : ∀ x, (1-1/(p:ℝ)-δ)*(N:ℝ) ≤ (G.degree x:ℝ)) (v : Fin N) :
    (univ.filter (fun x => ¬ G.Adj x v)).card ≤ N/p+N/(p*L)+2 := by
  classical
  have he := card_filter_add_card_filter_not (s:=univ) (G.Adj v)
  rw [← G.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree, card_univ,Fintype.card_fin] at he
  have hsame : (univ.filter fun x => ¬G.Adj x v) = univ.filter fun x => ¬G.Adj v x := by
    ext x
    simp [G.adj_comm]
  rw [hsame]
  have heR : (G.degree v : ℝ) + ((univ.filter (fun x => ¬G.Adj v x)).card:ℝ) = N := by
    exact_mod_cast he
  have h1 := floor_bound N p hp
  have h2 := floor_bound N (p*L) (Nat.mul_pos hp hL)
  rw [Nat.cast_mul] at h2
  have hh := mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg N)
  have hN := degree v
  apply Nat.cast_le (α:=ℝ).mp
  push_cast
  simp only [div_eq_mul_inv,one_mul] at h1 h2 hh hN
  linarith only [h1,h2,heR,hh,hN]

private theorem budget {p b N E : ℕ} (hb : 0<b)
    (hn : (16*b)*E + 2*(p*(16*b+2)) + 16*b + E ≤ N) :
    p*(16*b+2)*(N/p+N/(p*(16*b+2))+2) ≤
      (N-E)*(16*b+2-2) + (16*b+2-2)*(N/b) := by
  let L := 16*b+2
  have h1 : p*L*(N/p) ≤ L*N := by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
      Nat.mul_le_mul_left L (Nat.div_mul_le_self N p)
  have h2 : p*L*(N/(p*L)) ≤ N := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self N (p*L)
  have h3 : p*L*(N/p+N/(p*L)+2) ≤ L*N + N + 2*(p*L) := by
    rw [Nat.mul_add,Nat.mul_add]
    omega
  have h4 : 16*N ≤ 16*b*(N/b) + 16*b := by
    have h := Nat.mul_le_mul_left 16 (Nat.lt_mul_div_succ N hb).le
    simpa only [Nat.mul_add,Nat.mul_one,Nat.mul_assoc] using h
  have hnE : E ≤ N := by omega
  have hcancel := congrArg (fun x => (16*b)*x) (Nat.sub_add_cancel hnE)
  simp only [Nat.mul_add] at hcancel
  change p*L*_ ≤ _
  refine h3.trans ?_
  simp only [L,Nat.add_sub_cancel]
  nlinarith only [h4,hcancel,hn,Nat.zero_le N]

theorem almost_partition (p : ℕ) (hp : 2 ≤ p) (η : ℝ) (hη : 0 < η) :
    ∃ δ > (0:ℝ), ∀ᶠ N : ℕ in atTop, ∀ (G : SimpleGraph (Fin N)),
      (completeEquipartiteGraph (p+1) 3).Free G →
      (∀ x, (1-1/(p:ℝ)-δ)*(N:ℝ) ≤ (G.degree x:ℝ)) →
      ∃ (b : Fin p × Fin 3 → Fin N), Function.Injective b ∧
        (∀ i j : Fin p, i≠j → ∀ u v : Fin 3, G.Adj (b (i,u)) (b (j,v))) ∧
        ∃ B : Fin p → Finset (Fin N), Pairwise (fun i j => Disjoint (B i) (B j)) ∧
          (((univ : Finset (Fin N)) \ univ.biUnion B).card:ℝ) ≤ η*N ∧
          ∀ i x, x∈B i → ∀ j, j≠i → ∀ u, G.Adj x (b (j,u)) := by
  classical
  obtain ⟨b,hb⟩ := exists_nat_gt ((p:ℝ)*3/η)
  have bp : 0 < b := by
    have : (0:ℝ) ≤ (p:ℝ)*3/η := by positivity
    exact_mod_cast this.trans_lt hb
  have hp0 : 0 < p := by omega
  have hpR : (1:ℝ) < p := by exact_mod_cast hp
  let L := 16*b+2
  have lp : 0 < L := by dsimp [L]; omega
  have hL : 3 ≤ L := by dsimp [L]; omega
  let δ : ℝ := min (1/((p:ℝ)*L)) (1/(2*(p:ℝ)*(p-1)))
  have hδ : 0 < δ := by dsimp [δ]; apply lt_min <;> positivity
  let E := 2*Fintype.card (Fin p → (Fin 3 ↪ Fin L))
  refine ⟨δ,hδ,?_⟩
  filter_upwards [OMA.DenseSeed1085.of_degree (L:=L) hp (min_le_right _ _ : δ ≤ _),
    eventually_ge_atTop ((16*b)*E+2*(p*L)+16*b+E)] with N hasSeed hN
  intro G free degree
  obtain ⟨seed⟩ := hasSeed G degree
  obtain ⟨t,A,dis,cover,hit⟩ := OMA.Seed1085.extract
    (H:=N/p+N/(p*L)+2) (T:=N/b) hp0 hL G free seed
    (fun i a => cap hp0 lp (min_le_left _ _) G degree (seed (i,a))) (by
      simpa only [Fintype.card_fin] using budget bp hN)
  let anchor (u : Fin p × Fin 3) := seed (u.1,t u.1 u.2)
  refine ⟨anchor,?_,?_,A,dis,?_,hit⟩
  · rintro ⟨i,a⟩ ⟨j,c⟩ h
    have he := seed.injective h
    have h1 : i=j := congrArg Prod.fst he
    subst j
    exact Prod.ext rfl ((t i).injective (congrArg Prod.snd he))
  · intro i j h u v
    exact seed.toHom.map_adj (completeEquipartiteGraph_adj.mpr h)
  · have h1 : (p:ℝ)*3 ≤ η*b := by
      have := (div_lt_iff₀ hη).mp hb
      linarith
    have h2 : ((N/b:ℕ):ℝ)*(b:ℝ) ≤ N := by exact_mod_cast Nat.div_mul_le_self N b
    refine ((Nat.cast_le (α:=ℝ)).mpr cover).trans ?_
    push_cast
    calc
      _ ≤ (η*b)*((N/b:ℕ):ℝ) := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      _ ≤ η*N := by rw [mul_assoc,mul_comm (b:ℝ)]; exact mul_le_mul_of_nonneg_left h2 hη.le

end OMA.SeedStab1085

/- Recover approximate geometric stability from a high-minimum-degree
multipartite seed, the Erdős–Stone bound, and spherical incidences. -/

namespace OMA.Almost1085
open Finset Filter
open scoped Classical

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def SeedStatement : Prop :=
  ∀ (p : ℕ), 2 ≤ p → ∀ (η : ℝ), 0<η → ∃ δ > (0:ℝ),
    ∀ᶠ N : ℕ in atTop, ∀ (G : SimpleGraph (Fin N)), (SimpleGraph.completeEquipartiteGraph (p+1) 3).Free G →
    (∀ x, (1-1/(p:ℝ)-δ)*(N:ℝ) ≤ (G.degree x:ℝ)) →
    ∃ b : Fin p × Fin 3 → Fin N, Function.Injective b ∧
      (∀ i j : Fin p, i≠j → ∀ u v : Fin 3, G.Adj (b (i,u)) (b (j,v))) ∧
      ∃ B : Fin p → Finset (Fin N), Pairwise (fun i j => Disjoint (B i) (B j)) ∧
        (((univ : Finset (Fin N)) \ univ.biUnion B).card:ℝ) ≤ η*N ∧
        ∀ i x, x ∈ B i → ∀ j, j≠i → ∀ u, G.Adj x (b (j,u))

def SphereStatement : Prop := ∃ K > (0:ℝ), ∀ (Q : Finset (E 3)) (s : ℝ),
  (∀ x ∈ Q, ‖x‖^2=s) → (unitDistNum Q:ℝ) ≤ K*(Q.card:ℝ)^(4/3:ℝ)

theorem eventual (seed : SeedStatement) (sphere : SphereStatement) (k : ℕ) (hk : 0<k) :
    ∀ᶠ n : ℕ in atTop, OMA.Upgrade1085.Approximate (2*k+3) k n := by
  classical
  let d := 2*k+3
  have hd : 4≤d := by dsimp [d]; omega
  have hp : d/2=k+1 := by dsimp [d]; omega
  let : NeZero d := ⟨by omega⟩
  obtain ⟨η,hη,trim⟩ := OMA.Trim1085.extract (X:=E d) hk
  let ρ := min (η/4) (1/4)
  have hρ : 0<ρ := lt_min (by positivity) (by norm_num)
  have hρη : ρ ≤ η/4 := min_le_left ..
  have hρ4 : ρ ≤ 1/4 := min_le_right ..
  obtain ⟨δ,hδ,event⟩ := seed (k+1) (by omega) ρ hρ
  obtain ⟨N,hN⟩ := eventually_atTop.mp event
  obtain ⟨K,hK,sbound⟩ := sphere
  obtain ⟨C,lower⟩ := OMA.Prune1085.lenz (d:=d) hd
  rw [hp] at lower
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at lower
  filter_upwards [trim,OMA.Prune1085.extremal_unit_core hd hδ hρ,
    OMA.Transport1085.small_interiors (k+1) K η hη,eventually_ge_atTop (2*N),
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (C/η),
    eventually_ge_atTop (1:ℕ)] with n trimN pruneN smallN hnN hnC hn1
  obtain ⟨S,hSn,opt⟩ := OMA.UnitGraph1085.attained (d:=d) n
  obtain ⟨T,hTS,hTlarge,hTdeg⟩ := pruneN S hSn opt
  let v := OMA.UnitGraph1085.enumerate T rfl
  have enum : univ.image v = T := OMA.UnitGraph1085.enumerate_image T rfl
  have vT (x : Fin T.card) : v x ∈ T :=
    (congrArg (fun U : Finset (E d) => v x ∈ U) enum).mp (mem_image_of_mem _ (mem_univ x))
  have hTc : T.card ≤ n := (card_le_card hTS).trans_eq hSn
  have hm : N ≤ T.card := by
    have h : (N:ℝ) ≤ T.card := by
      have hn : (2:ℝ)*N ≤ n := by exact_mod_cast hnN
      nlinarith [mul_nonneg (sub_nonneg.mpr hρ4) (Nat.cast_nonneg (α:=ℝ) n)]
    exact_mod_cast h
  let G := OMA.UnitGraph1085.graph v
  have edge (x y) (h : G.Adj x y) : dist (v x) (v y)=1 := h
  have free : (SimpleGraph.completeEquipartiteGraph (k+1+1) 3).Free G :=
    OMA.SeedMetric1085.no_complete (d:=d) rfl G v v.injective edge
  have degree (x : Fin T.card) : (1-1/((k+1:ℕ):ℝ)-δ)*(T.card:ℝ) ≤ G.degree x := by
    rw [show G.degree x = _ from OMA.UnitGraph1085.degree v v.injective x,enum]
    rw [hp] at hTdeg
    exact hTdeg (v x) (vT x)
  obtain ⟨b,binj,links,B,dis,houtside,hit⟩ := hN _ hm G free degree
  obtain ⟨A,subA,disA,outA,insA⟩ := OMA.Transport1085.classes (d:=d) rfl hk G v v.injective S hSn
    (fun x => hTS (vT x)) edge
    (fun i t => b (i,t)) (fun i t u h => congrArg Prod.snd (binj h)) links B dis hit K hK.le sbound
  have outs : ((S \ univ.biUnion A).card:ℝ) ≤ η*n := by
    have tsize : ((univ \ univ.biUnion B).card:ℝ) + (univ.biUnion B).card = T.card := by
      exact_mod_cast (card_sdiff_add_card_eq_card (subset_univ (univ.biUnion B))).trans (by simp)
    have osize : ((S \ univ.biUnion A).card:ℝ) + (univ.biUnion B).card = n := by exact_mod_cast outA
    nlinarith [mul_le_mul_of_nonneg_left (by exact_mod_cast hTc : (T.card:ℝ)≤n) hρ.le,
      mul_nonneg (sub_nonneg.mpr hρη) (Nat.cast_nonneg (α:=ℝ) n)]
  have dens : ((k:ℝ)/(2*(k+1))-η)*(n:ℝ)^2 ≤ unitDistNum S := by
    have ηn := (div_le_iff₀ hη).mp hnC
    have hn1R : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have ηn2 : C ≤ η*(n:ℝ)^2 := ηn.trans (by
      nlinarith [mul_nonneg hη.le (mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (sub_nonneg.mpr hn1R))])
    have opR : (Erdos1085.f d n:ℝ) ≤ unitDistNum S := by exact_mod_cast opt
    nlinarith only [lower n,opR,ηn2]
  obtain ⟨A',m,e,sub',hm',size,large,near⟩ := trimN S A hSn subA disA
    (by convert outs using 2; apply congrArg Finset.card; ext x; simp)
    (insA.trans smallN) dens
  exact OMA.GraphCore1085.toApproximate rfl hk S hSn opt A' (fun i => (sub' i).trans (subA i))
    (fun i j hij => (disA hij).mono (sub' i) (sub' j)) hm' (size.trans_eq (by ring)) large near

end OMA.Almost1085

theorem OMA.solution : type_of% @Erdos1085.erdos_1085.variants.upper_lower_d5_odd :=
  OMA.Odd1085.of_core (OMA.Almost1085.eventual OMA.SeedStab1085.almost_partition OMA.Odd1085.sphere_bound)
