import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R4
import Mathlib

/-!
# The one-holed disc polygon admits no plane atlas

Proves step `PoincareConjecture.poincare_conjecture.variants.dimension_two.R1.H4.R4.H3`.

Statement. Let `D` be the closed unit disc in `ℂ`, `z t = exp (2 π i t)`, and let `R true 0 1`
be the polygon relation of the reduction for one hole and no handles: it relates
`z (-x/3)` to `z (-(3 - x)/3) = z (x/3)` for `x ∈ [0, 1]`, that is, it folds the boundary arc of
arguments in `[-2π/3, 2π/3]` along the real axis and leaves the arc of arguments in
`(2π/3, 4π/3)` free. The step says that `Quot (R true 0 1)` (topologically a closed disc, whose
boundary circle is the image of the free arc) carries no
`ChartedSpace (EuclideanSpace ℝ (Fin 2))` structure.

Method: the two-dimensional case of invariance of the boundary, by a continuous logarithm.

1. Points of `D` with real part `< -1/2` are not related to anything (`rel_re`), so the quotient
   map is injective on them (`mk_inj_of_re_lt`) and restricts to an open embedding on every open
   set of such points (`isOpenEmbedding_mk_of_subset`).
2. A chart of the quotient at the class of `-1` therefore gives an open subset `V` of `D`
   containing `-1` together with an open embedding `g : V → ℂ` (`exists_chart`).
3. That is impossible (`core`). Choose `ε` with `ball (-1) ε ∩ D ⊆ V`. The set
   `A ε = (ball (-1) ε ∩ D) \ {-1}` is convex (`-1` is an extreme point of `D`), hence simply
   connected and locally path connected. So `g - g(-1)`, which has no zero on `A ε`, has a
   continuous logarithm there (`exists_log`, from Mathlib's lifting theorem for the covering map
   `exp`), and transporting it along the embedding gives a continuous logarithm of `w - c` on
   `g '' A ε` (`image_log`), where `c = g (-1)`. But `g '' (ball (-1) ε ∩ D)` is an open
   neighbourhood of `c`, so `g '' A ε` contains a punctured disc around `c`, on which `w - c`
   has no continuous logarithm (`no_log`: go once round a circle).

Prior art and credit. This is the classical fact that a boundary point of a surface with
boundary has no plane neighbourhood (invariance of the boundary in dimension two, by the
fundamental group of the punctured plane); no novelty is claimed. No textbook proof was re-read
for this file. The lifting theorem used is Mathlib's
(`Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts`). The reduction file says its
polygon normal forms follow the public repository `classification-of-surfaces`; its code was
not read, and it is not known whether it contains this lemma.

Independent adversarial review (one reviewer, not told the author's conclusions, with its own
scripts and three Lean runs of its own): no fatal or major objection. It checked by `Iff.rfl`
that the definitions here are definitionally those of `H3`, proved in Lean both directions of
the reading of `R true 0 1` (so the relation is not vacuous), and re-tested the relation and the
convexity statement numerically. Strongest objection: the sketch of `no_log` named
`IsPreconnected.constant_of_mapsTo`, which needs a discreteness fact Mathlib does not state for
the range of the integer cast, so a worker could lose time there. Disposition: accepted as a
remark on the sketch only; the proof of `no_log` in this file does not use that lemma (it uses
the intermediate value theorem for `|G|` and the value `1/2`), and it compiles. Minor remarks
(two deprecated lemma names in sketches, a miscounted composition in the sketch of
`exists_chart`, `A ε` being a half-disc only for small `ε`) do not affect any statement.
The reviewer did NOT machine-check `isOpenEmbedding_mk_restrict`, `exists_chart`, `no_log` or
`core`; those are checked by Lean in this file.
-/

open Set Topology

namespace OMA.Disc

/-- The closed unit disc (the same term as `D` in the step). -/
abbrev D : Set ℂ := Metric.closedBall (0 : ℂ) 1

/-- The boundary parametrisation of the step. -/
noncomputable def z (t : ℝ) : D := ⟨Real.fourierChar t, (Real.fourierChar t).2.le⟩

/-- The polygon relation of the step, copied verbatim. -/
def R (o : Bool) (p n : ℕ) (u v : D) : Prop :=
  let d : ℝ := (if o then 4 else 2) * p + 3 * n
  let edge (s t : ℝ) := u = z (s / d) ∧ v = z (t / d)
  (∃ (i : Fin p) (x : Icc (0 : ℝ) 1), if o then
      edge (4 * i + x) (4 * i + 3 - x) ∨ edge (4 * i + 1 + x) (4 * i + 4 - x)
    else edge (2 * i + x) (2 * i + 1 + x)) ∨
    ∃ (i : Fin n) (x : Icc (0 : ℝ) 1), edge (-(3 * i + x)) (-(3 * i + 3 - x))

/-- The quotient space of the step. -/
abbrev Q : Type := Quot (R true 0 1)

/-- The boundary point `-1` of the disc. -/
def bpt : D := ⟨-1, by simp⟩

/-- The punctured half-disc around `-1`. -/
def A (ε : ℝ) : Set ℂ := (Metric.ball (-1 : ℂ) ε ∩ Metric.closedBall (0 : ℂ) 1) \ {-1}

/- ## Part A: the quotient near the free boundary arc -/

/-- rel_re (A1).
Statement: two related points of the disc both have real part at least `-1/2`.
Sketch: unfold `R true 0 1`. The first disjunct quantifies over `Fin 0` and is false. In the
second, `i : Fin 1` is `0` and `d = 4 * 0 + 3 * 1 = 3`, so `u = z (-(3 * 0 + x) / 3)` and
`v = z (-(3 * 0 + 3 - x) / 3)` with `x ∈ [0, 1]`. By `Real.fourierChar_apply` the complex number
under `z t` is `exp (2 π t * I)`, whose real part is `cos (2 π t)`. For `u`: `cos (-2πx/3) =
cos (2πx/3)`; for `v`: `cos (2π(-1 + x/3)) = cos (2πx/3)` by periodicity. Since
`0 ≤ 2πx/3 ≤ 2π/3 ≤ π` and `cos` is antitone on `[0, π]`,
`cos (2πx/3) ≥ cos (2π/3) = -1/2` (`Real.cos_pi_div_three` and `cos (π - y) = - cos y`).
Source: direct computation from the definition in the reduction file.
Estimate: 60 to 100 lines.
Tested: `tests.py` part 1 evaluates the relation literally as written (general `o p n` formula at
`true 0 1`) on 3001 values of `x`, exact symbolic values at `x = 0, 1/2, 1`; minimum real part
is exactly `-1/2`, attained at `x = 1` only.
Depends on: nothing. -/
lemma rel_re (u v : D) (h : R true 0 1 u v) :
    -1 / 2 ≤ (u : ℂ).re ∧ -1 / 2 ≤ (v : ℂ).re := by
  have hz : ∀ t : ℝ, ((z t : D) : ℂ).re = Real.cos (2 * Real.pi * t) := by
    intro t
    show ((Real.fourierChar t : Circle) : ℂ).re = _
    rw [Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re]
  have hcos : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → -1 / 2 ≤ Real.cos (2 * Real.pi * x / 3) := by
    intro x hx0 hx1
    have hpi := Real.pi_pos
    have h1 : Real.cos (2 * Real.pi / 3) ≤ Real.cos (2 * Real.pi * x / 3) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · positivity
      · linarith
      · have : Real.pi * x ≤ Real.pi := by nlinarith
        linarith
    have h2 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      have h3 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
      rw [h3, Real.cos_pi_sub, Real.cos_pi_div_three]
      norm_num
    linarith
  simp only [R] at h
  rcases h with ⟨i, _⟩ | ⟨i, x, hu, hv⟩
  · exact i.elim0
  · have c1 : ∀ T : ℝ, T = -(x : ℝ) / 3 → -1 / 2 ≤ Real.cos (2 * Real.pi * T) := by
      rintro T rfl
      have h4 := hcos x x.2.1 x.2.2
      rw [show 2 * Real.pi * (-(x : ℝ) / 3) = -(2 * Real.pi * x / 3) by ring, Real.cos_neg]
      exact h4
    have c2 : ∀ T : ℝ, T = -(3 - (x : ℝ)) / 3 → -1 / 2 ≤ Real.cos (2 * Real.pi * T) := by
      rintro T rfl
      have h4 := hcos x x.2.1 x.2.2
      rw [show 2 * Real.pi * (-(3 - (x : ℝ)) / 3) = 2 * Real.pi * x / 3 - 2 * Real.pi by ring,
        Real.cos_sub_two_pi]
      exact h4
    rw [hu, hv, hz, hz]
    exact ⟨c1 _ (by simp), c2 _ (by simp)⟩

/-- mk_inj_of_re_lt (A2).
Statement: a point with real part `< -1/2` is alone in its class.
Sketch: `Quot.eq` turns the hypothesis into `Relation.EqvGen (R true 0 1) u v`. Prove by induction
on `EqvGen` the symmetric claim: if `EqvGen r a b` and (`re a < -1/2` or `re b < -1/2`) then
`a = b`. `rel`: contradicts `rel_re`. `refl`: trivial. `symm`: swap the disjunction.
`trans a b c`: if `re a < -1/2` then `a = b`, so `re b < -1/2` and `b = c`; symmetrically from `c`.
Source: elementary.
Estimate: 30 to 50 lines.
Tested: `tests.py` part 2 builds the generated equivalence on a discretised disc boundary (720
boundary points plus interior grid points) by union-find and checks every point with real part
`< -1/2` is a singleton class.
Depends on: `rel_re`. -/
lemma mk_inj_of_re_lt (u v : D) (hu : (u : ℂ).re < -1 / 2)
    (h : Quot.mk (R true 0 1) u = Quot.mk (R true 0 1) v) : u = v := by
  have key : ∀ a b : D, Relation.EqvGen (R true 0 1) a b →
      ((a : ℂ).re < -1 / 2 ∨ (b : ℂ).re < -1 / 2) → a = b := by
    intro a b hab
    induction hab with
    | rel a b hr =>
      intro hlt
      obtain ⟨h1, h2⟩ := rel_re a b hr
      exfalso
      rcases hlt with hlt | hlt <;> linarith
    | refl a => intro _; rfl
    | symm a b _ ih => intro hlt; exact (ih hlt.symm).symm
    | trans a b c _ _ ih1 ih2 =>
      intro hlt
      rcases hlt with hlt | hlt
      · have hab := ih1 (Or.inl hlt)
        subst hab
        exact ih2 (Or.inl hlt)
      · have hbc := ih2 (Or.inr hlt)
        subst hbc
        exact ih1 (Or.inr hlt)
  exact key u v (Quot.eqvGen_exact h) (Or.inl hu)

theorem isOpenEmbedding_mk_of_subset (V : Set D) (hV : IsOpen V)
    (hVW : ∀ u ∈ V, (u : ℂ).re < -1 / 2) :
    IsOpenEmbedding (fun u : V => (Quot.mk (R true 0 1) u.1 : Q)) := by
  have hcont : Continuous (fun u : V => (Quot.mk (R true 0 1) u.1 : Q)) :=
    continuous_quot_mk.comp continuous_subtype_val
  have hinj : Function.Injective (fun u : V => (Quot.mk (R true 0 1) u.1 : Q)) := by
    intro a b hab
    exact Subtype.ext (mk_inj_of_re_lt a.1 b.1 (hVW a.1 a.2) hab)
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj ?_
  intro S hS
  have hpre : (Quot.mk (R true 0 1)) ⁻¹'
      ((fun u : V => (Quot.mk (R true 0 1) u.1 : Q)) '' S) = Subtype.val '' S := by
    ext w
    constructor
    · rintro ⟨a, haS, ha⟩
      have haw : a.1 = w := mk_inj_of_re_lt a.1 w (hVW a.1 a.2) ha
      exact ⟨a, haS, haw⟩
    · rintro ⟨a, haS, rfl⟩
      exact ⟨a, haS, rfl⟩
  rw [← isQuotientMap_quot_mk.isOpen_preimage, hpre]
  exact hV.isOpenMap_subtype_val S hS

/-- isOpenEmbedding_mk_restrict (A3).
Statement: the quotient map restricted to `{u ∈ D | re u < -1/2}` is an open embedding.
Sketch: use `IsOpenEmbedding.of_continuous_injective_isOpenMap` (or
`isOpenEmbedding_of_continuous_injective_open`, whichever name this Mathlib has). Continuity:
`continuous_quot_mk.comp continuous_subtype_val`. Injectivity: `mk_inj_of_re_lt` and
`Subtype.ext`. Open map: the topology on `Quot r` is coinduced by `Quot.mk r`
(`isOpen_coinduced`, or `isQuotientMap_quot_mk.isOpen_preimage`), so for an open `S` of the
subtype it is enough that the preimage under `Quot.mk` of the image of `S` is open in `D`; by
`mk_inj_of_re_lt` (applied in both directions) that preimage is exactly `Subtype.val '' S`, which
is open because `{u : D | re u < -1/2}` is open in `D` (`isOpen_lt`, continuity of
`re ∘ Subtype.val`) and `IsOpen.isOpenMap_subtype_val`.
Source: elementary general topology (a saturated open set of a quotient).
Estimate: 60 to 100 lines.
Tested: not testable numerically; the only arithmetic input is `mk_inj_of_re_lt`.
Depends on: `mk_inj_of_re_lt`. -/
lemma isOpenEmbedding_mk_restrict :
    IsOpenEmbedding (fun u : {u : D // (u : ℂ).re < -1 / 2} => (Quot.mk (R true 0 1) u.1 : Q)) :=
  isOpenEmbedding_mk_of_subset {u : D | (u : ℂ).re < -1 / 2}
    (isOpen_lt (Complex.continuous_re.comp continuous_subtype_val) continuous_const)
    (fun _ hu => hu)

/-- exists_chart (A4).
Statement: a plane atlas on the quotient yields an open subset `V` of the disc containing `-1`
and an open embedding of `V` into `ℂ`.
Sketch: let `q = Quot.mk _ bpt` and `e = chartAt (EuclideanSpace ℝ (Fin 2)) q`, an
`OpenPartialHomeomorph` with `q ∈ e.source` (`mem_chart_source`) and `e.source` open. Put
`V = {u : D | re u < -1/2 ∧ Quot.mk _ u ∈ e.source}`: open (continuity of `Quot.mk`), and it
contains `bpt` since `re (-1) = -1`. Let `T : EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ` be
`Complex.orthonormalBasisOneI.repr.symm.toHomeomorph` (any homeomorphism will do) and
`g u = T (e (Quot.mk _ u))`. It is an open embedding as a composition of three open embeddings:
`V → {u // re u < -1/2}` (inclusion of an open subset), then `isOpenEmbedding_mk_restrict`
corestricted to `e.source`, then `e.isOpenEmbedding_restrict` (the restriction of `e` to its
source), then `T`. One clean way: show `fun u : V => (Quot.mk _ u.1 : Q)` is an open embedding
with range inside `e.source`, and use that `e` is continuous, injective and open on `e.source`
(`e.continuousOn`, `e.injOn`, `e.isOpen_image_of_subset_source`).
Source: unfolding the definition of a charted space.
Estimate: 100 to 180 lines.
Tested: not testable numerically.
Depends on: `isOpenEmbedding_mk_restrict`. -/
lemma exists_chart [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Q] :
    ∃ (V : Set D) (g : V → ℂ), IsOpen V ∧ bpt ∈ V ∧ IsOpenEmbedding g := by
  obtain ⟨q, hq⟩ : ∃ q : Q, q = Quot.mk (R true 0 1) bpt := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : OpenPartialHomeomorph Q (EuclideanSpace ℝ (Fin 2)),
      e = chartAt (EuclideanSpace ℝ (Fin 2)) q := ⟨_, rfl⟩
  have hqe : q ∈ e.source := by rw [he]; exact mem_chart_source _ q
  let T : EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ := Complex.orthonormalBasisOneI.repr.symm.toHomeomorph
  obtain ⟨V, hVdef⟩ : ∃ V : Set D,
      V = {u : D | (u : ℂ).re < -1 / 2} ∩ (Quot.mk (R true 0 1)) ⁻¹' e.source := ⟨_, rfl⟩
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact (isOpen_lt (Complex.continuous_re.comp continuous_subtype_val) continuous_const).inter
      (e.open_source.preimage continuous_quot_mk)
  have hb : bpt ∈ V := by
    rw [hVdef]
    refine ⟨?_, ?_⟩
    · show ((-1 : ℂ)).re < -1 / 2
      norm_num
    · show Quot.mk (R true 0 1) bpt ∈ e.source
      rw [← hq]; exact hqe
  have hVW : ∀ u ∈ V, (u : ℂ).re < -1 / 2 := by
    intro u hu
    rw [hVdef] at hu
    exact hu.1
  have hVs' : ∀ u ∈ V, (Quot.mk (R true 0 1) u : Q) ∈ e.source := by
    intro u hu
    rw [hVdef] at hu
    exact hu.2
  have hVs : ∀ u : V, (Quot.mk (R true 0 1) u.1 : Q) ∈ e.source := fun u => hVs' u.1 u.2
  have hm := isOpenEmbedding_mk_of_subset V hVopen hVW
  have hem : IsOpenEmbedding (fun u : V => e (Quot.mk (R true 0 1) u.1 : Q)) := by
    refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
    · exact e.continuousOn.comp_continuous hm.continuous hVs
    · intro a b hab
      exact hm.injective (e.injOn (hVs a) (hVs b) hab)
    · intro S hS
      have himg : (fun u : V => e (Quot.mk (R true 0 1) u.1 : Q)) '' S
          = e '' ((fun u : V => (Quot.mk (R true 0 1) u.1 : Q)) '' S) := by
        rw [Set.image_image]
      rw [himg]
      refine e.isOpen_image_of_subset_source (hm.isOpenMap S hS) ?_
      rintro _ ⟨u, _, rfl⟩
      exact hVs u
  exact ⟨V, fun u => T (e (Quot.mk (R true 0 1) u.1 : Q)), hVopen, hb,
    T.isOpenEmbedding.comp hem⟩

/- ## Part B: a half-disc neighbourhood of a boundary point is not a plane domain -/

/-- no_log (B1).
Statement: `w - c` has no continuous logarithm on a punctured disc around `c`.
Sketch: suppose `ℓ` is one. Put `γ t = c + (r/2) * exp (t * I)` for real `t`; it lies in the
punctured ball, and `F t = ℓ (γ t) - t * I` is continuous on `ℝ` with
`exp (F t) = (r/2) * exp (t * I) * exp (-(t * I)) = r/2`. Hence `exp (F t) = exp (F 0)` and by
`Complex.exp_eq_exp_iff_exists_int` there is an integer `n t` with
`F t = F 0 + n t * (2 π I)`. The function `t ↦ (F t - F 0) / (2 π I)` is continuous and
integer valued on the connected space `ℝ`, hence constant (for instance: its real part is
continuous with values in the range of `Int.cast`, use `IsPreconnected.constant_of_mapsTo`
with the discrete topology on `ℤ`, or the intermediate value theorem), equal to its value `0` at
`t = 0`. So `F (2π) = F 0`. But `γ (2π) = γ 0` (`Complex.exp_two_pi_mul_I`), so
`F (2π) - F 0 = -(2π) * I ≠ 0`. Contradiction.
Source: the standard proof that the circle has no continuous logarithm.
Estimate: 80 to 140 lines.
Tested: `tests.py` part 4 follows the continuous branch of `log (γ t - c)` numerically round the
circle for 50 random `(c, r)`; the increment is `2πi` to 1e-9 every time.
Depends on: nothing. -/
lemma no_log (c : ℂ) (r : ℝ) (hr : 0 < r) :
    ¬ ∃ ℓ : ℂ → ℂ, ContinuousOn ℓ (Metric.ball c r \ {c}) ∧
      ∀ w ∈ Metric.ball c r \ {c}, Complex.exp (ℓ w) = w - c := by
  rintro ⟨ℓ, hcont, hexp⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → ℂ, ∀ t, γ t = c + ((r / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) :=
    ⟨_, fun _ => rfl⟩
  have hn : ∀ t : ℝ, ‖((r / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ = r / 2 := by
    intro t
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hγsub : ∀ t, γ t - c = ((r / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
    intro t; rw [hγ]; ring
  have hγmem : ∀ t, γ t ∈ Metric.ball c r \ {c} := by
    intro t
    constructor
    · rw [Metric.mem_ball, dist_eq_norm, hγsub, hn]
      linarith
    · intro h
      have h' : γ t = c := h
      have h0 : γ t - c = 0 := by rw [h']; ring
      have h1 := hn t
      rw [← hγsub, h0, norm_zero] at h1
      linarith
  have hγc : Continuous γ := by
    have : γ = fun t : ℝ => c + ((r / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := funext hγ
    rw [this]
    fun_prop
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℂ, ∀ t, F t = ℓ (γ t) - (t : ℂ) * Complex.I := ⟨_, fun _ => rfl⟩
  have hFc : Continuous F := by
    have h1 : Continuous fun t => ℓ (γ t) := hcont.comp_continuous hγc hγmem
    have : F = fun t : ℝ => ℓ (γ t) - (t : ℂ) * Complex.I := funext hF
    rw [this]
    exact h1.sub (by fun_prop)
  have e1 : ∀ s : ℝ, Complex.exp (F s) = ((r / 2 : ℝ) : ℂ) := by
    intro s
    rw [hF, Complex.exp_sub, hexp _ (hγmem s), hγsub, mul_div_assoc,
      div_self (Complex.exp_ne_zero _), mul_one]
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hint : ∀ t, ∃ n : ℤ, F t = F 0 + n * (2 * Real.pi * Complex.I) := fun t =>
    Complex.exp_eq_exp_iff_exists_int.mp (by rw [e1, e1])
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ t, G t = ((F t - F 0) / (2 * Real.pi * Complex.I)).re :=
    ⟨_, fun _ => rfl⟩
  have hGc : Continuous G := by
    have : G = fun t : ℝ => ((F t - F 0) / (2 * Real.pi * Complex.I)).re := funext hG
    rw [this]
    exact Complex.continuous_re.comp ((hFc.sub continuous_const).div_const _)
  have hGint : ∀ t, ∃ n : ℤ, G t = n := by
    intro t
    obtain ⟨n, hn'⟩ := hint t
    refine ⟨n, ?_⟩
    rw [hG, hn', add_sub_cancel_left, mul_div_assoc, div_self h2pi, mul_one]
    simp
  have hG0 : G 0 = 0 := by rw [hG]; simp
  have hGconst : ∀ t, G t = 0 := by
    intro t
    by_contra hne
    obtain ⟨n, hn'⟩ := hGint t
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hn')
    have hc' : Continuous fun s => |G s| := continuous_abs.comp hGc
    have h0 : |G 0| ≤ 1 / 2 := by rw [hG0]; norm_num
    have h1 : (1 : ℝ) / 2 ≤ |G t| := by
      rw [hn']
      have h5 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
      linarith
    have hmem : (1 : ℝ) / 2 ∈ Set.uIcc (|G 0|) (|G t|) := Set.mem_uIcc.mpr (Or.inl ⟨h0, h1⟩)
    obtain ⟨s, _, hs⟩ := intermediate_value_uIcc (a := 0) (b := t) hc'.continuousOn hmem
    obtain ⟨m, hm⟩ := hGint s
    have hs' : |(m : ℝ)| = 1 / 2 := by rw [← hm]; exact hs
    have h3 : ((2 * |m| : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h4 : (2 * |m| : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hγper : γ (2 * Real.pi) = γ 0 := by
    rw [hγ, hγ]
    simp [Complex.exp_two_pi_mul_I]
  have hlast : F (2 * Real.pi) - F 0 = -(2 * Real.pi * Complex.I) := by
    rw [hF, hF, hγper]
    push_cast
    ring
  have hG2 := hGconst (2 * Real.pi)
  rw [hG, hlast, neg_div, div_self h2pi] at hG2
  norm_num at hG2

/-- convex_A (B2).
Statement: for `ε > 0` the punctured half-disc `A ε` is convex and nonempty.
Sketch: nonempty: with `δ = min ε 1 / 2` the real point `-1 + δ` has distance `δ < ε` from `-1`,
norm `1 - δ ≤ 1`, and is not `-1`. Convex: `ball (-1) ε ∩ closedBall 0 1` is convex
(`(convex_ball _ _).inter (convex_closedBall _ _)`). For `a, b ∈ A ε` and `s, t ≥ 0`, `s + t = 1`,
the point `s • a + t • b` is in that intersection; it remains to see it is not `-1`. Every point
`w` of the closed unit disc has `re w ≥ -1` (`Complex.abs_re_le_norm`), with equality only for
`w = -1` (if `re w = -1` and `‖w‖ ≤ 1` then `im w = 0` from `re^2 + im^2 ≤ 1`). If
`s • a + t • b = -1` then `s * re a + t * re b = -1` with `re a, re b ≥ -1`; if `s > 0` this forces
`re a = -1` (else the sum is `> -1`), so `a = -1`, contradiction; if `s = 0` then `b = -1`,
contradiction. (Equivalently: `-1` is an extreme point of the disc, and
`Convex.mem_extremePoints_iff_convex_diff` applies.)
Source: elementary convexity.
Estimate: 50 to 90 lines.
Tested: `tests.py` part 3: 200000 random pairs in `A ε` for `ε ∈ {0.05, 0.3, 1, 2.5}` with random
weights, exact rational arithmetic; every convex combination is in `A ε`; also checks that
`re w = -1`, `|w| ≤ 1` forces `w = -1` symbolically.
Depends on: nothing. -/
lemma convex_A {ε : ℝ} (hε : 0 < ε) : Convex ℝ (A ε) ∧ (A ε).Nonempty := by
  have hre : ∀ w : ℂ, w ∈ Metric.closedBall (0 : ℂ) 1 → -1 ≤ w.re ∧ (w.re = -1 → w = -1) := by
    intro w hw
    have hn : ‖w‖ ≤ 1 := by simpa using hw
    have hsq : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
      have h1 := Complex.sq_norm w
      rw [Complex.normSq_apply] at h1
      nlinarith [norm_nonneg w]
    refine ⟨(abs_le.mp ((Complex.abs_re_le_norm w).trans hn)).1, fun h => ?_⟩
    have him : w.im = 0 := by
      have h' := hsq
      rw [h] at h'
      norm_num at h'
      exact h'
    exact Complex.ext (by simp [h]) (by simp [him])
  constructor
  · intro a ha b hb s t hs ht hst
    have hconv : Convex ℝ (Metric.ball (-1 : ℂ) ε ∩ Metric.closedBall (0 : ℂ) 1) :=
      (convex_ball _ _).inter (convex_closedBall _ _)
    refine ⟨hconv ha.1 hb.1 hs ht hst, ?_⟩
    intro hmem
    have heq : s • a + t • b = -1 := hmem
    have hrea := hre a ha.1.2
    have hreb := hre b hb.1.2
    have hane : a.re ≠ -1 := fun h => ha.2 (hrea.2 h)
    have hbne : b.re ≠ -1 := fun h => hb.2 (hreb.2 h)
    have hre_eq : s * a.re + t * b.re = -1 := by
      simpa using congrArg Complex.re heq
    have ha' : -1 < a.re := lt_of_le_of_ne hrea.1 (Ne.symm hane)
    have hb' : -1 < b.re := lt_of_le_of_ne hreb.1 (Ne.symm hbne)
    have h1 : 0 ≤ s * (a.re + 1) := mul_nonneg hs (by linarith)
    have h2 : 0 ≤ t * (b.re + 1) := mul_nonneg ht (by linarith)
    have h3 : s * (a.re + 1) + t * (b.re + 1) = 0 := by
      have h0 : s * (a.re + 1) + t * (b.re + 1) = (s * a.re + t * b.re) + (s + t) := by ring
      rw [h0, hre_eq, hst]; norm_num
    have h4 : s * (a.re + 1) = 0 := by linarith
    have h5 : t * (b.re + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h4 with hs0 | h
    · rcases mul_eq_zero.mp h5 with ht0 | h'
      · linarith
      · linarith
    · linarith
  · have hδ : 0 < min ε 1 / 2 := by positivity
    have hδ1 : min ε 1 / 2 < ε := by
      have := min_le_left ε 1
      linarith
    have hδ2 : min ε 1 / 2 ≤ 1 / 2 := by
      have := min_le_right ε 1
      linarith
    refine ⟨((-1 + min ε 1 / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h0 : ((-1 + min ε 1 / 2 : ℝ) : ℂ) - (-1) = ((min ε 1 / 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [h0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
      exact hδ1
    · rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    · intro h
      have h' : ((-1 + min ε 1 / 2 : ℝ) : ℂ) = -1 := h
      have h2 := congrArg Complex.re h'
      rw [Complex.ofReal_re] at h2
      simp at h2
      linarith

/-- The punctured half-disc is simply connected and locally path connected (from `convex_A`
and Mathlib). -/
theorem simplyConnected_A {ε : ℝ} (hε : 0 < ε) :
    SimplyConnectedSpace (A ε) ∧ LocallyPathConnectedSpace (A ε) := by
  obtain ⟨hc, hne⟩ := convex_A hε
  have := hc.contractibleSpace hne
  exact ⟨inferInstance, hc.locallyPathConnectedSpace⟩

/-- exists_log (B3).
Statement: a continuous nowhere-zero complex function on a simply connected, locally path
connected space has a continuous logarithm.
Sketch: this is Mathlib's `Complex.exists_continuousOn_eqOn_exp_comp` (file
`Mathlib/Analysis/Complex/BranchLogRoot.lean`) with `U = Set.univ`, or directly its one-step
proof: pick `x₀` (a simply connected space is nonempty; if you prefer, treat the empty case by
`isEmpty_or_nonempty`), and apply
`Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts ⟨h, hc⟩ (Complex.exp_log (h0 x₀)) h0`
to get `L : C(X, ℂ)` with `exp ∘ L = h`.
Source: Mathlib, as named.
Estimate: 20 to 40 lines.
Tested: not a numerical statement; it is a specialisation of a Mathlib theorem whose statement
was read.
Depends on: nothing. -/
lemma exists_log (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] (h : X → ℂ) (hc : Continuous h) (h0 : ∀ x, h x ≠ 0) :
    ∃ L : X → ℂ, Continuous L ∧ ∀ x, Complex.exp (L x) = h x := by
  have hpc : PathConnectedSpace X := inferInstance
  obtain ⟨x₀⟩ := hpc.nonempty
  rcases Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (⟨h, hc⟩ : C(X, ℂ)) (Complex.exp_log (h0 x₀)) (fun x => h0 x) with ⟨f, ⟨-, hf⟩, -⟩
  exact ⟨f, map_continuous f, fun x => by simpa using congr($hf x)⟩

/-- image_log (B4).
Statement: if `f` embeds a simply connected, locally path connected space in `ℂ` and misses
`c`, then `w - c` has a continuous logarithm on the range of `f`.
Sketch: `exists_log` for `h x = f x - c` (nonzero because `c ∉ range f`) gives `L`. Let
`φ = hf.toHomeomorph : X ≃ₜ range f` (`Topology.IsEmbedding.toHomeomorph`) and define
`ℓ w = if hw : w ∈ range f then L (φ.symm ⟨w, hw⟩) else 0`. Then `ContinuousOn ℓ (range f)` by
`continuousOn_iff_continuous_restrict` (the restriction is `L ∘ φ.symm`), and for `w = f x`
one has `φ.symm ⟨f x, _⟩ = x`, so `exp (ℓ w) = f x - c = w - c`.
Source: elementary.
Estimate: 40 to 80 lines.
Tested: not testable numerically.
Depends on: `exists_log`. -/
lemma image_log (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] (f : X → ℂ) (c : ℂ) (hf : IsEmbedding f) (hc : c ∉ range f) :
    ∃ ℓ : ℂ → ℂ, ContinuousOn ℓ (range f) ∧ ∀ w ∈ range f, Complex.exp (ℓ w) = w - c := by
  classical
  obtain ⟨L, hL, hexp⟩ := exists_log X (fun x => f x - c) (hf.continuous.sub continuous_const)
    (fun x hx => hc ⟨x, sub_eq_zero.mp hx⟩)
  let φ : X ≃ₜ range f := hf.toHomeomorph
  refine ⟨fun w => if hw : w ∈ range f then L (φ.symm ⟨w, hw⟩) else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hres : (range f).domRestrict
        (fun w => if hw : w ∈ range f then L (φ.symm ⟨w, hw⟩) else 0) = L ∘ φ.symm := by
      funext w
      show (if hw : (w : ℂ) ∈ range f then L (φ.symm ⟨w, hw⟩) else 0) = L (φ.symm w)
      rw [dif_pos w.2]
    rw [hres]
    exact hL.comp φ.symm.continuous
  · rintro w ⟨x, rfl⟩
    have hw : f x ∈ range f := ⟨x, rfl⟩
    have hx : φ.symm ⟨f x, hw⟩ = x := by
      apply φ.injective
      rw [φ.apply_symm_apply]
      exact Subtype.ext rfl
    show Complex.exp (if hw : f x ∈ range f then L (φ.symm ⟨f x, hw⟩) else 0) = f x - c
    rw [dif_pos hw, hx, hexp]

/-- core (B5).
Statement: no open subset of the closed disc containing the boundary point `-1` embeds openly
in the plane.
Sketch: `V` is open in the subtype `D` and contains `bpt`, so (`Metric.isOpen_iff`; the distance
on a subtype is the distance in `ℂ`) there is `ε > 0` such that every `u : D` with
`dist (u : ℂ) (-1) < ε` is in `V`. So there is a map `ι : A ε → V`,
`ι a = ⟨⟨a, _⟩, _⟩` (a point of `A ε` is in the closed ball and within `ε` of `-1`), continuous
and an embedding (`Subtype.val ∘ Subtype.val ∘ ι = Subtype.val`, use `IsEmbedding.of_comp` or
`Topology.IsEmbedding.subtypeVal` and `IsEmbedding.codRestrict`). Let `c = g ⟨bpt, hb⟩` and
`f = g ∘ ι`: an embedding (`hg.isEmbedding.comp`), and `c ∉ range f` because `g` is injective and
`ι a ≠ ⟨bpt, hb⟩` (points of `A ε` are not `-1`). With the instances from `simplyConnected_A`,
`image_log` gives `ℓ` continuous on `range f` with `exp (ℓ w) = w - c` there.
Next, `N = {v : V | dist ((v : D) : ℂ) (-1) < ε}` is open in `V`, so `g '' N` is open in `ℂ`
(`hg.isOpenMap`), and it contains `c`; take `r > 0` with `ball c r ⊆ g '' N`. If
`w ∈ ball c r \ {c}` then `w = g v` with `v ∈ N`, and `v ≠ ⟨bpt, hb⟩` (else `w = c`), so the
complex number under `v` is in `A ε` and `w ∈ range f`. Thus `ball c r \ {c} ⊆ range f`, and
`ℓ` (with `ContinuousOn.mono`) contradicts `no_log c r`.
Source: the standard proof of invariance of the boundary in dimension two.
Estimate: 150 to 250 lines.
Tested: not testable numerically; ingredients `no_log` and `convex_A` are tested.
Depends on: `no_log`, `simplyConnected_A` (proved above from `convex_A`), `image_log`. -/
lemma core (V : Set D) (hV : IsOpen V) (hb : bpt ∈ V) (g : V → ℂ) (hg : IsOpenEmbedding g) :
    False := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV bpt hb
  have hAD : ∀ a : A ε, (a : ℂ) ∈ D := fun a => a.2.1.2
  have hAV : ∀ a : A ε, (⟨a, hAD a⟩ : D) ∈ V := by
    intro a
    apply hball
    show dist ((a : ℂ)) (-1) < ε
    exact a.2.1.1
  obtain ⟨ι, hι⟩ : ∃ ι : A ε → V, ∀ a, ((ι a : D) : ℂ) = a :=
    ⟨fun a => ⟨⟨a, hAD a⟩, hAV a⟩, fun _ => rfl⟩
  have hιc : Continuous ι := by
    have h1 : Continuous fun a : A ε => ((ι a : D) : ℂ) := by
      have : (fun a : A ε => ((ι a : D) : ℂ)) = Subtype.val := funext hι
      rw [this]; exact continuous_subtype_val
    have h2 : Continuous fun a : A ε => (ι a : D) :=
      (IsEmbedding.subtypeVal).continuous_iff.mpr h1
    exact (IsEmbedding.subtypeVal).continuous_iff.mpr h2
  have hιe : IsEmbedding ι := by
    refine IsEmbedding.of_comp hιc (continuous_subtype_val.comp continuous_subtype_val) ?_
    have : ((Subtype.val : D → ℂ) ∘ (Subtype.val : V → D)) ∘ ι = Subtype.val := funext hι
    rw [this]; exact IsEmbedding.subtypeVal
  obtain ⟨hsc, hlpc⟩ := simplyConnected_A hε
  have : SimplyConnectedSpace (A ε) := hsc
  have : LocallyPathConnectedSpace (A ε) := hlpc
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = g ⟨bpt, hb⟩ := ⟨_, rfl⟩
  have hfemb : IsEmbedding (g ∘ ι) := hg.isEmbedding.comp hιe
  have hcnot : c ∉ range (g ∘ ι) := by
    rintro ⟨a, ha⟩
    have h1 : ι a = ⟨bpt, hb⟩ := hg.injective (by rw [← hc]; exact ha)
    have h2 : ((ι a : D) : ℂ) = -1 := by rw [h1]; rfl
    rw [hι] at h2
    exact a.2.2 h2
  obtain ⟨ℓ, hℓc, hℓe⟩ := image_log (A ε) (g ∘ ι) c hfemb hcnot
  obtain ⟨N, hNdef⟩ : ∃ N : Set V, N = {v : V | dist ((v : D) : ℂ) (-1) < ε} := ⟨_, rfl⟩
  have hN : IsOpen N := by
    rw [hNdef]
    exact isOpen_lt ((continuous_subtype_val.comp continuous_subtype_val).dist continuous_const)
      continuous_const
  have hgN : IsOpen (g '' N) := hg.isOpenMap N hN
  have hcN : c ∈ g '' N := by
    refine ⟨⟨bpt, hb⟩, ?_, hc.symm⟩
    rw [hNdef]
    show dist (-1 : ℂ) (-1) < ε
    rw [dist_self]; exact hε
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hgN c hcN
  have hsub : Metric.ball c r \ {c} ⊆ range (g ∘ ι) := by
    rintro w ⟨hw, hwc⟩
    obtain ⟨v, hvN, rfl⟩ := hrsub hw
    rw [hNdef] at hvN
    have hvne : ((v : D) : ℂ) ≠ -1 := by
      intro h
      apply hwc
      have hv : v = ⟨bpt, hb⟩ := Subtype.ext (Subtype.ext h)
      rw [hv, ← hc]
      exact rfl
    have hvA : ((v : D) : ℂ) ∈ A ε := ⟨⟨hvN, (v : D).2⟩, hvne⟩
    refine ⟨⟨_, hvA⟩, ?_⟩
    show g (ι ⟨_, hvA⟩) = g v
    exact congrArg g (Subtype.ext (Subtype.ext (hι ⟨_, hvA⟩)))
  exact no_log c r hr ⟨ℓ, hℓc.mono hsub, fun w hw => hℓe w (hsub hw)⟩

/- ## Assembly -/

theorem disc_no_atlas : ¬ Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2)) Q) := by
  rintro ⟨cs⟩
  obtain ⟨V, g, hV, hb, hg⟩ := @exists_chart cs
  exact core V hV hb g hg

theorem main :
    OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R4.H3 :=
  disc_no_atlas

end OMA.Disc

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R4.H3 :=
  OMA.Disc.main
