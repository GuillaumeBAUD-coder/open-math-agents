import FormalConjectures.ErdosProblems.«95»
import Mathlib

/-! The Elekes–Sharir lines in coordinates (height, twice center-x, twice center-y).
We adapt our Guth–Katz incidence proof (originally built for Erdős 89 and 100,
including Elekes–Sharir setup inspired by @marcusbuffett and Mario Ullrich's
Apache-2.0 Borsuk–Ulam proof) directly to Erdős 95 (Guth–Katz quadruple energy bound). -/
namespace OMA
open Filter Finset Asymptotics EuclideanGeometry
open scoped Classical
abbrev Point := EuclideanSpace ℝ (Fin 2)
abbrev Space := ℝ × ℝ × ℝ
abbrev Pair := Point × Point

structure ESLine where
  x : ℝ
  y : ℝ
  u : ℝ
  v : ℝ

def ESLine.atHeight (l : ESLine) (t : ℝ) : Space :=
  (t, l.x + t*l.u, l.y + t*l.v)

def ESLine.Contains (l : ESLine) (p : Space) : Prop := l.atHeight p.1 = p

def esLine (a b : Point) : ESLine :=
  ⟨a 0 + b 0, a 1 + b 1, b 1 - a 1, a 0 - b 0⟩

private theorem point_ext {a b : Point} (hx : a 0 = b 0) (hy : a 1 = b 1) : a = b := by
  ext i
  fin_cases i <;> assumption

theorem esLine_injective : Function.Injective (fun p : Pair ↦ esLine p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  change esLine a b = esLine c d at he
  obtain ⟨hx,hy,hu,hv⟩ : a 0 + b 0 = c 0 + d 0 ∧ a 1 + b 1 = c 1 + d 1 ∧
      b 1 - a 1 = d 1 - c 1 ∧ a 0 - b 0 = c 0 - d 0 := by
    simpa [esLine, ESLine.mk.injEq] using he
  exact Prod.ext (point_ext (by linarith) (by linarith)) (point_ext (by linarith) (by linarith))

/-- Two nontranslated segments of equal length determine intersecting lines.
Height zero includes half-turns. -/
theorem exists_meeting_height (a b c d : Point)
    (hlen : dist a b = dist c d) (hne : b - a ≠ d - c) :
    ∃ t : ℝ, (esLine a c).atHeight t = (esLine b d).atHeight t := by
  have hs := congrArg (fun r : ℝ ↦ r^2) hlen
  simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs] at hs
  let U := (c 1 - a 1) - (d 1 - b 1)
  let V := (a 0 - c 0) - (b 0 - d 0)
  let X := (b 0 + d 0) - (a 0 + c 0)
  let Y := (b 1 + d 1) - (a 1 + c 1)
  have det : X*V = Y*U := by dsimp [X,Y,U,V]; nlinarith only [hs]
  have nz : U ≠ 0 ∨ V ≠ 0 := by
    by_contra! h
    apply hne
    apply point_ext
    · change b 0 - a 0 = d 0 - c 0
      dsimp [V] at h; linarith [h.2]
    · change b 1 - a 1 = d 1 - c 1
      dsimp [U] at h; linarith [h.1]
  suffices h : ∃ t : ℝ, t * U = X ∧ t * V = Y by
    obtain ⟨t,hx,hy⟩ := h
    dsimp [X,Y,U,V] at hx hy
    refine ⟨t, Prod.ext rfl (Prod.ext ?_ ?_)⟩ <;>
      simp only [esLine, ESLine.atHeight] <;> linarith only [hx,hy]
  by_cases hu : U = 0
  · have hv := nz.resolve_left (not_not_intro hu)
    have hx : X = 0 := (mul_eq_zero.mp (by simpa [hu] using det)).resolve_right hv
    exact ⟨Y / V, by simp [hu,hx], div_mul_cancel₀ _ hv⟩
  · refine ⟨X / U, div_mul_cancel₀ _ hu, ?_⟩
    field_simp
    linarith only [det]

noncomputable def incidentPairs (A : Finset Point) (p : Space) : Finset Pair :=
  (A ×ˢ A).filter fun ab ↦ (esLine ab.1 ab.2).Contains p

private theorem same_source {a b d : Point} {p : Space}
    (hb : (esLine a b).Contains p) (hd : (esLine a d).Contains p) : b = d := by
  have e := hb.trans hd.symm
  simp only [ESLine.atHeight, esLine, Prod.mk.injEq, true_and] at e
  have hx : b 0 - d 0 = -p.1 * (b 1 - d 1) := by linarith [e.1]
  have hy : b 1 - d 1 = p.1 * (b 0 - d 0) := by linarith [e.2]
  rw [hy] at hx
  have h : (1+p.1^2)*(b 0-d 0) = 0 := by linarith only [hx]
  have hx' := (mul_eq_zero.mp h).resolve_left (by positivity)
  rw [hx', mul_zero] at hy
  exact point_ext (sub_eq_zero.mp hx') (sub_eq_zero.mp hy)

theorem incidentPairs_card_le (A : Finset Point) (p : Space) :
    (incidentPairs A p).card ≤ A.card := by
  apply card_le_card_of_injOn Prod.fst
  · intro q hq
    exact (mem_product.mp (mem_filter.mp hq).1).1
  · rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    change a = c at he
    subst c
    exact Prod.ext rfl (same_source (mem_filter.mp hab).2 (mem_filter.mp hcd).2)


/-- At most one line from each source lies in a fixed affine plane. -/
theorem plane_line_cap (A : Finset Point) (g h i j : ℝ) (hn : g ≠ 0 ∨ h ≠ 0 ∨ i ≠ 0) :
    ((A ×ˢ A).filter (fun ab ↦ ∀ t : ℝ, let p := (esLine ab.1 ab.2).atHeight t
      g * p.2.1 + h * p.2.2 + i*t = j)).card ≤ A.card := by
  apply card_le_card_of_injOn Prod.fst
  · intro q hq
    exact (mem_product.mp (mem_filter.mp hq).1).1
  · rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    change a = c at he
    subst c
    have hb := (mem_filter.mp hab).2
    have hd := (mem_filter.mp hcd).2
    have b0 := hb 0
    have b1 := hb 1
    have d0 := hd 0
    have d1 := hd 1
    simp only [esLine, ESLine.atHeight, zero_mul, one_mul, mul_zero, mul_one,
      add_zero] at b0 b1 d0 d1
    have nz : g^2 + h^2 ≠ 0 := by
      intro e
      have hg : g = 0 := by nlinarith [sq_nonneg h, sq_nonneg g]
      have hh : h = 0 := by nlinarith [sq_nonneg g, sq_nonneg h]
      rcases hn with hg'|hh'|hi
      · exact hg' hg
      · exact hh' hh
      · apply hi
        rw [hg, hh] at b0 b1
        linarith only [b0,b1]
    have e : g*(b 0-d 0) + h*(b 1-d 1) = 0 := by linarith only [b0,d0]
    have f : g*(b 1-d 1) - h*(b 0-d 0) = 0 := by linarith only [b0,d0,b1,d1]
    have ex : (g^2+h^2)*(b 0-d 0) = 0 := by linear_combination g*e - h*f
    have ey : (g^2+h^2)*(b 1-d 1) = 0 := by linear_combination h*e + g*f
    exact Prod.ext rfl (point_ext (sub_eq_zero.mp ((mul_eq_zero.mp ex).resolve_left nz))
      (sub_eq_zero.mp ((mul_eq_zero.mp ey).resolve_left nz)))

/-- Finite-set form of the two rich-point estimates for the Elekes–Sharir lines. -/
def RichPointBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ A : Finset Point, ∀ k : ℕ, 2 ≤ k → k ≤ A.card →
    ∀ B : Finset Space, (∀ p ∈ B, k ≤ (incidentPairs A p).card) →
      (B.card : ℝ) * (k : ℝ)^2 ≤ C * (A.card : ℝ)^3

private noncomputable def nontranslations (A : Finset Point) :=
  (A.offDiag ×ˢ A.offDiag).filter fun q ↦
    dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧ q.1.2 - q.1.1 ≠ q.2.2 - q.2.1

private noncomputable def meetingPoint (q : Pair × Pair) : Space :=
  let l := esLine q.1.1 q.2.1
  let m := esLine q.1.2 q.2.2
  l.atHeight (if h : ∃ t, l.atHeight t = m.atHeight t then h.choose else 0)

private theorem meeting_mem {A : Finset Point} {q : Pair × Pair}
    (hq : q ∈ nontranslations A) :
    ((q.1.1,q.2.1),(q.1.2,q.2.2)) ∈ (incidentPairs A (meetingPoint q)).offDiag := by
  obtain ⟨hp,hd,hn⟩ := mem_filter.mp hq
  obtain ⟨hp1,hp2⟩ := mem_product.mp hp
  obtain ⟨ha,hb,hab⟩ := mem_offDiag.mp hp1
  obtain ⟨hc,he,_⟩ := mem_offDiag.mp hp2
  have hh := exists_meeting_height _ _ _ _ hd hn
  have hm : meetingPoint q = (esLine q.1.1 q.2.1).atHeight hh.choose := by
    simp only [meetingPoint, dif_pos hh]
  rw [hm]
  refine mem_offDiag.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨ha,hc⟩,rfl⟩,
    mem_filter.mpr ⟨mem_product.mpr ⟨hb,he⟩,hh.choose_spec.symm⟩,
    fun e ↦ hab (congrArg Prod.fst e)⟩

private theorem nontranslations_le (A : Finset Point) :
    (nontranslations A).card ≤ ∑ p ∈ (nontranslations A).image meetingPoint,
      (incidentPairs A p).offDiag.card := by
  rw [card_eq_sum_card_image meetingPoint (nontranslations A)]
  apply sum_le_sum
  intro p _
  apply card_le_card_of_injOn (fun q : Pair × Pair ↦ ((q.1.1,q.2.1),(q.1.2,q.2.2)))
  · intro q hq
    obtain ⟨hm,rfl⟩ := mem_filter.mp hq
    exact meeting_mem hm
  · intro q _ r _ he
    simpa [Prod.ext_iff, and_assoc, and_left_comm, and_comm] using he

private theorem multiplicity_layers (r : ℕ) :
    r*r-r ≤ ∑ k ∈ Icc 2 r, 2*k := by
  induction r with
  | zero => simp
  | succ r ih =>
    by_cases hr : 1 ≤ r
    · rw [sum_Icc_succ_top (by omega)]
      rw [Nat.succ_mul, Nat.mul_succ]
      have : r ≤ r*r := by nlinarith
      omega
    · have : r = 0 := by omega
      subst r
      simp

private theorem energy_of_rich {C : ℝ} (hC : 0 < C) (A : Finset Point)
    (h : ∀ k : ℕ, 2 ≤ k → k ≤ A.card → ∀ B : Finset Space,
      (∀ p ∈ B, k ≤ (incidentPairs A p).card) →
      (B.card : ℝ) * (k : ℝ)^2 ≤ C * (A.card : ℝ)^3) :
    ((nontranslations A).card : ℝ) ≤
      (2*C*(A.card : ℝ)^3) * (1 + Real.log (A.card : ℝ)) := by
  let B := (nontranslations A).image meetingPoint
  let m (p : Space) := (incidentPairs A p).card
  let K := Icc 2 A.card
  have layer (p : Space) : (incidentPairs A p).offDiag.card ≤
      ∑ k ∈ K, if k ≤ m p then 2*k else 0 := by
    rw [← sum_filter, offDiag_card]
    have e : K.filter (fun k ↦ k ≤ m p) = Icc 2 (m p) := by
      ext k
      simp only [K, mem_filter, mem_Icc]
      have := incidentPairs_card_le A p
      change m p ≤ A.card at this
      omega
    rw [e]
    exact multiplicity_layers _
  have count : (nontranslations A).card ≤ ∑ k ∈ K, (B.filter (fun p ↦ k ≤ m p)).card * (2*k) := by
    calc
      _ ≤ ∑ p ∈ B, (incidentPairs A p).offDiag.card := nontranslations_le A
      _ ≤ ∑ p ∈ B, ∑ k ∈ K, if k ≤ m p then 2*k else 0 := sum_le_sum fun p _ ↦ layer p
      _ = _ := by rw [sum_comm]; simp [← sum_filter]
  have countR : ((nontranslations A).card : ℝ) ≤
      ∑ k ∈ K, ((B.filter (fun p ↦ k ≤ m p)).card : ℝ) * (2*k) := by exact_mod_cast count
  calc
    _ ≤ _ := countR
    _ ≤ ∑ k ∈ K, (2*C*(A.card : ℝ)^3) * (k : ℝ)⁻¹ := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hk2,hkn⟩ := mem_Icc.mp hk
      have hi := h k hk2 hkn (B.filter (fun p ↦ k ≤ m p)) fun _ hp ↦ (mem_filter.mp hp).2
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      rw [← div_eq_mul_inv, le_div_iff₀ hkpos]
      linarith only [hi]
    _ = (2*C*(A.card : ℝ)^3) * ∑ k ∈ K, (k : ℝ)⁻¹ := (mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := harmonic_le_one_add_log A.card
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
      apply le_trans _ hh
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨h₁,h₂⟩ := mem_Icc.mp hk
        exact mem_Icc.mpr ⟨by omega,h₂⟩
      · intros; positivity

private theorem equal_displacement_count (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    let P := A.offDiag
    ((P ×ˢ P).filter (fun q ↦ q.1.2 - q.1.1 = q.2.2 - q.2.1)).card ≤ A.card^3 := by
  classical
  dsimp only
  rw [pow_succ, pow_two, ← card_product, ← card_product]
  apply card_le_card_of_injOn (fun q ↦ (q.1, q.2.1))
  · intro q hq
    obtain ⟨hp,hq⟩ := mem_product.mp (mem_filter.mp hq).1
    exact mem_product.mpr
      ⟨mem_product.mpr ⟨(mem_offDiag.mp hp).1, (mem_offDiag.mp hp).2.1⟩,
        (mem_offDiag.mp hq).1⟩
  · intro q hq q' hq' heq
    change (q.1, q.2.1) = (q'.1, q'.2.1) at heq
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj heq
    have hqE := (mem_filter.mp hq).2
    have hq'E := (mem_filter.mp hq').2
    rw [h₁, h₂] at hqE
    have h₃ : q.2.2 = q'.2.2 := sub_left_inj.mp (hqE.symm.trans hq'E)
    exact Prod.ext h₁ (Prod.ext h₂ h₃)

/-- Ordered congruent-segment quadruples upper-bound `4 * ∑ u, distanceMultiplicity A u ^ 2`. -/
private theorem four_mul_sum_mult_sq_le (A : Finset ℝ²) :
    4 * ∑ u ∈ distanceSet A, (distanceMultiplicity A u) ^ 2 ≤
      ((A.offDiag ×ˢ A.offDiag).filter fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2).card := by
  classical
  let P := A.offDiag
  let E := (P ×ˢ P).filter fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2
  have hmaps : ∀ z ∈ E, dist z.1.1 z.1.2 ∈ distanceSet A := by
    intro z hz
    exact Finset.mem_image_of_mem _ (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  let F := P.filter fun z => dist z.1 z.2 = u
  have hfib : (E.filter fun z => dist z.1.1 z.1.2 = u) = F ×ˢ F := by
    ext ⟨a, b⟩
    simp only [E, F, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, he⟩, hu⟩
      exact ⟨⟨ha, hu⟩, hb, he.symm.trans hu⟩
    · rintro ⟨⟨ha, ha'⟩, hb, hb'⟩
      exact ⟨⟨⟨ha, hb⟩, ha'.trans hb'.symm⟩, ha'⟩
  rw [hfib, Finset.card_product, ← sq]
  have hmul : 2 * distanceMultiplicity A u ≤ F.card := by
    unfold distanceMultiplicity
    exact Nat.mul_div_le F.card 2
  calc
    4 * (distanceMultiplicity A u) ^ 2 = (2 * distanceMultiplicity A u) ^ 2 := by ring
    _ ≤ F.card ^ 2 := Nat.pow_le_pow_left hmul 2

/-- Rich-point bounds from multiplicity two through |A| imply the exact
Erdős 95 Guth–Katz quadruple energy bound. Translations cost at most |A|³. -/
theorem solution_of_incidence (rich : RichPointBound) :
    type_of% @Erdos95.erdos_95.variants.guth_katz := by
  obtain ⟨C,hC,rich⟩ := rich
  refine ⟨(1 + 3 * C) / 2, by positivity, ?_⟩
  intro A hA
  let E := (A.offDiag ×ˢ A.offDiag).filter fun q ↦ dist q.1.1 q.1.2 = dist q.2.1 q.2.2
  let T := (A.offDiag ×ˢ A.offDiag).filter fun q ↦ q.1.2-q.1.1 = q.2.2-q.2.1
  have sub : E ⊆ T ∪ nontranslations A := by
    intro q hq
    obtain ⟨hp,hd⟩ := mem_filter.mp hq
    by_cases he : q.1.2-q.1.1 = q.2.2-q.2.1
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,he⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,hd,he⟩)
  have ct : E.card ≤ A.card^3 + (nontranslations A).card :=
    (card_le_card sub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (equal_displacement_count A) _))
  have ct' : (E.card : ℝ) ≤ (A.card : ℝ)^3 + (nontranslations A).card := by exact_mod_cast ct
  have h₁ := energy_of_rich hC A (rich A)
  have h4nat := four_mul_sum_mult_sq_le A
  have h4 : 4 * ∑ u ∈ distanceSet A, (distanceMultiplicity A u : ℝ) ^ 2 ≤ (E.card : ℝ) := by
    exact_mod_cast h4nat
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog : (1 : ℝ) ≤ 2 * Real.log (A.card : ℝ) := by
    have h2le : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA
    have hmono : Real.log 2 ≤ Real.log (A.card : ℝ) := Real.log_le_log (by norm_num) h2le
    linarith
  have h₂ := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (1 + 2 * C) * (A.card : ℝ) ^ 3 by positivity)
  linarith only [h4, ct', h₁, h₂]


section Quadrics
open MvPolynomial
private abbrev Poly₂ := MvPolynomial (Fin 2) ℂ

/-- General affine quadratic, in coordinates (x,y,z). -/
def quadratic {R : Type*} [CommRing R] (c : Fin 10 → R) (x y z : R) : R :=
  (c 0*x+c 1*y+c 2*z+c 3)*x + (c 4*y+c 5*z+c 6)*y + (c 7*z+c 8)*z+c 9

private def leftCoord (a : Point) : ℂ := ⟨a 0,-a 1⟩
private def rightCoord (b : Point) : ℂ := ⟨b 0,b 1⟩

private noncomputable def slicePoly (c : Fin 10 → ℝ) : Poly₂ :=
  quadratic (fun i ↦ C (c i : ℂ)) (X 0 + X 1) (C Complex.I * (X 0 - X 1)) (C Complex.I)

private theorem eval_slice (c : Fin 10 → ℝ) (v : Fin 2 → ℂ) :
    eval v (slicePoly c) = quadratic (fun i ↦ (c i : ℂ))
      (v 0+v 1) (Complex.I*(v 0-v 1)) Complex.I := by
  simp [slicePoly, quadratic]

private theorem slice_degree (c : Fin 10 → ℝ) : (slicePoly c).totalDegree ≤ 2 := by
  let x : Poly₂ := X 0 + X 1
  let y : Poly₂ := C Complex.I * (X 0 - X 1)
  have hx : x.totalDegree ≤ 1 := (totalDegree_add ..).trans (by simp)
  have hy : y.totalDegree ≤ 1 := by
    apply (totalDegree_mul ..).trans
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_sub ..).trans (by simp)
  have mulC (a : ℂ) (p : Poly₂) {d : ℕ} (hd : p.totalDegree ≤ d) :
      (C a*p).totalDegree ≤ d :=
    (totalDegree_mul ..).trans (by simpa only [totalDegree_C, zero_add] using hd)
  have cc (a : ℂ) : (C a : Poly₂).totalDegree ≤ 1 := by simp
  have sumD (p q : Poly₂) {d : ℕ} (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
      (p+q).totalDegree ≤ d := (totalDegree_add ..).trans (max_le hp hq)
  have prodD (p q : Poly₂) (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) :
      (p*q).totalDegree ≤ 2 := (totalDegree_mul ..).trans (Nat.add_le_add hp hq)
  change (quadratic _ x y _).totalDegree ≤ 2
  unfold quadratic
  apply sumD
  · apply sumD
    · apply sumD
      · apply prodD _ _ _ hx
        exact sumD _ _ (sumD _ _ (sumD _ _ (mulC _ _ hx) (mulC _ _ hy))
          (mulC _ _ (cc _))) (cc _)
      · apply prodD _ _ _ hy
        exact sumD _ _ (sumD _ _ (mulC _ _ hy) (mulC _ _ (cc _))) (cc _)
    · exact prodD _ _ (sumD _ _ (mulC _ _ (cc _)) (cc _)) (cc _)
  · simp

private theorem line_slice_zero (c : Fin 10 → ℝ) (a b : Point)
    (h : ∀ t : ℝ, let p := (esLine a b).atHeight t; quadratic c p.2.1 p.2.2 t = 0) :
    eval ![leftCoord a,rightCoord b] (slicePoly c) = 0 := by
  have h0 := h 0
  have hp := h 1
  have hm := h (-1)
  simp only [esLine, ESLine.atHeight, quadratic, zero_mul, mul_zero, one_mul, mul_one,
    neg_one_mul, mul_neg_one, add_zero] at h0 hp hm
  rw [eval_slice]
  apply Complex.ext <;>
    simp [quadratic, leftCoord, rightCoord, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im]
  · linear_combination 2*h0 - hp/2 - hm/2
  · linear_combination hp/2 - hm/2

/-- A zero slice at imaginary height forces the original real quadratic to be
a scalar multiple of 1+z². -/
private theorem degenerate_slice (c : Fin 10 → ℝ) (hz : slicePoly c = 0) (x y t : ℝ) :
    quadratic c x y t = c 7 * (1+t^2) := by
  let v : Fin 2 → ℂ := ![((x : ℂ)-Complex.I*y)/2, ((x : ℂ)+Complex.I*y)/2]
  have h := eval_slice c v
  have hx : v 0 + v 1 = (x : ℂ) := by dsimp [v]; ring
  have hy : Complex.I*(v 0 - v 1) = (y : ℂ) := by
    dsimp [v]
    linear_combination (-(y : ℂ))*Complex.I_mul_I
  rw [hz, map_zero, hx, hy] at h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [quadratic, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at hr hi
  unfold quadratic
  linear_combination -hr - t*hi

/-- Every proper affine quadric contains at most 4|A| Elekes–Sharir lines.
At imaginary height each endpoint pair is a point of a Cartesian grid in ℂ².
Schwartz–Zippel bounds the number on the specialized quadratic. -/
theorem quadric_line_cap (A : Finset Point) (c : Fin 10 → ℝ)
    (proper : ∃ x y z : ℝ, quadratic c x y z ≠ 0) :
    ((A ×ˢ A).filter (fun ab ↦ ∀ t : ℝ, let p := (esLine ab.1 ab.2).atHeight t
      quadratic c p.2.1 p.2.2 t = 0)).card ≤ 4*A.card := by
  classical
  let L := (A ×ˢ A).filter (fun ab ↦ ∀ t : ℝ, let p := (esLine ab.1 ab.2).atHeight t
    quadratic c p.2.1 p.2.2 t = 0)
  change L.card ≤ _
  obtain hL | ⟨ab,hab⟩ := L.eq_empty_or_nonempty
  · simp [hL]
  have hq := (mem_filter.mp hab).2
  have hn : slicePoly c ≠ 0 := by
    intro hz
    have hh := hq 0
    dsimp only at hh
    rw [degenerate_slice c hz] at hh
    norm_num at hh
    obtain ⟨x,y,z,hxyz⟩ := proper
    exact hxyz (by rw [degenerate_slice c hz, hh, zero_mul])
  let S := A.image leftCoord ∪ A.image rightCoord
  have hs : S.Nonempty := ⟨_,mem_union_left _ (mem_image_of_mem _ (mem_product.mp (mem_filter.mp hab).1).1)⟩
  let V := (Fintype.piFinset fun _ : Fin 2 ↦ S).filter (fun v ↦ eval v (slicePoly c) = 0)
  have inj : L.card ≤ V.card := by
    apply card_le_card_of_injOn (fun ab : Pair ↦ ![leftCoord ab.1,rightCoord ab.2])
    · intro q hq
      obtain ⟨hm,h⟩ := mem_filter.mp hq
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_,line_slice_zero c _ _ h⟩
      intro i
      fin_cases i
      · exact mem_union_left _ (mem_image_of_mem _ (mem_product.mp hm).1)
      · exact mem_union_right _ (mem_image_of_mem _ (mem_product.mp hm).2)
    · intro q _ r _ he
      have h₀ := congrFun he 0
      have h₁ := congrFun he 1
      change leftCoord q.1 = leftCoord r.1 at h₀
      change rightCoord q.2 = rightCoord r.2 at h₁
      exact Prod.ext (point_ext (congrArg Complex.re h₀)
        (neg_inj.mp (congrArg Complex.im h₀)))
        (point_ext (congrArg Complex.re h₁) (congrArg Complex.im h₁))
  have hspos : 0 < (S.card : ℚ≥0) := by exact_mod_cast hs.card_pos
  have hz := schwartz_zippel_totalDegree hn S
  change (V.card : ℚ≥0) / (S.card : ℚ≥0)^2 ≤ _ at hz
  rw [div_le_div_iff₀ (by positivity) hspos] at hz
  have h' : (V.card : ℚ≥0)*S.card ≤ ((slicePoly c).totalDegree * (S.card : ℚ≥0))*S.card := by
    simpa [pow_two,mul_assoc] using hz
  have hV : V.card ≤ (slicePoly c).totalDegree * S.card := by
    exact_mod_cast (le_of_mul_le_mul_right h' hspos)
  have hS : S.card ≤ A.card + A.card := (card_union_le ..).trans (Nat.add_le_add card_image_le card_image_le)
  exact inj.trans (hV.trans ((Nat.mul_le_mul (slice_degree c) hS).trans (by omega)))
end Quadrics


/-- Guth–Katz incidence estimate restricted to lines transverse to the height
planes. Every such line has the unique parametrization used by ESLine. -/
def LineIncidenceBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (L : Finset ESLine), L.card = n^2 →
    (∀ g h i j : ℝ, (g ≠ 0 ∨ h ≠ 0 ∨ i ≠ 0) →
      (L.filter (fun l ↦ ∀ t : ℝ, let p := l.atHeight t
        g*p.2.1 + h*p.2.2 + i*t = j)).card ≤ n) →
    (∀ c : Fin 10 → ℝ, (∃ x y z : ℝ, quadratic c x y z ≠ 0) →
      (L.filter (fun l ↦ ∀ t : ℝ, let p := l.atHeight t
        quadratic c p.2.1 p.2.2 t = 0)).card ≤ 4*n) →
    ∀ k : ℕ, 2 ≤ k → k ≤ n → ∀ B : Finset Space,
      (∀ p ∈ B, k ≤ (L.filter (fun l ↦ l.Contains p)).card) →
        (B.card : ℝ) * (k : ℝ)^2 ≤ C * (n : ℝ)^3

theorem rich_of_line_incidence (h : LineIncidenceBound) : RichPointBound := by
  classical
  obtain ⟨C,hC,bound⟩ := h
  refine ⟨C,hC,?_⟩
  intro A
  let f (ab : Pair) := esLine ab.1 ab.2
  let L := (A ×ˢ A).image f
  have cardL : L.card = A.card^2 := by
    rw [card_image_iff.mpr esLine_injective.injOn, card_product, pow_two]
  have filterL (P : ESLine → Prop) :
      (L.filter P).card = ((A ×ˢ A).filter fun ab ↦ P (f ab)).card := by
    unfold L
    rw [filter_image, card_image_iff.mpr esLine_injective.injOn]
  have core := bound A.card L cardL
  apply fun k hk hkn B hb ↦ core ?_ ?_ k hk hkn B (fun p hp ↦ by rw [filterL]; exact hb p hp)
  · intro g h i j hn
    rw [filterL]
    exact plane_line_cap A g h i j hn
  · intro c hc
    rw [filterL]
    exact quadric_line_cap A c hc

/-- The complete distinct-distance reduction, with the incidence theorem as
its single remaining hypothesis. -/
theorem solution_of_line_incidence (h : LineIncidenceBound) :
    type_of% @Erdos95.erdos_95.variants.guth_katz :=
  solution_of_incidence (rich_of_line_incidence h)

/-- Reversed displacements contribute at most one fourth endpoint per triple. -/
theorem halfturn_count (A : Finset Point) :
    ((A.offDiag ×ˢ A.offDiag).filter fun q ↦ q.1.2-q.1.1 = -(q.2.2-q.2.1)).card ≤ A.card^3 := by
  refine le_trans (Finset.card_le_card_of_injOn (fun q => (q.1.1, q.1.2, q.2.1))
    (t := A ×ˢ A ×ˢ A) ?_ ?_) ?_
  · intro q hq
    have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    obtain ⟨hpq, -⟩ := hq'
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpq
    have h1' := Finset.mem_offDiag.mp h1
    have h2' := Finset.mem_offDiag.mp h2
    simp only [Finset.mem_coe, Finset.mem_product]
    exact ⟨h1'.1, h1'.2.1, h2'.1⟩
  · intro q hq q' hq' heq
    have h := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    have h' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq')).2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨e1, e2, e3⟩ := heq
    have k : q.2.2 = q.2.1 - (q.1.2 - q.1.1) := by rw [h]; abel
    have k' : q'.2.2 = q'.2.1 - (q'.1.2 - q'.1.1) := by rw [h']; abel
    refine Prod.ext (Prod.ext e1 e2) (Prod.ext e3 ?_)
    rw [k, k', e1, e2, e3]
  · rw [Finset.card_product, Finset.card_product]
    exact le_of_eq (by ring)

end OMA

namespace OMA
open Finset MvPolynomial
open scoped Classical

/-- The odd-map formulation of Borsuk–Ulam, restricted to maps extending
continuously over the ambient coefficient space. -/
def OddZero (m : ℕ) : Prop :=
  ∀ F : (Fin (m+1) → ℝ) → (Fin m → ℝ), Continuous F →
    (∀ v, F (-v) = -F v) → ∃ v, v ≠ 0 ∧ F v = 0

/-- Positive precisely when a strict majority of the sample has positive
value. The products keep the test continuous even at ties. -/
private noncomputable def majority {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  ∑ u ∈ s.powerset.filter (fun u ↦ s.card < 2*u.card), ∏ a ∈ u, max (f a) 0

private theorem majority_pos {α : Type*} (s : Finset α) (f : α → ℝ) :
    0 < majority s f ↔ s.card < 2*(s.filter fun a ↦ 0 < f a).card := by
  classical
  unfold majority
  rw [sum_pos_iff_of_nonneg (fun _ _ ↦ prod_nonneg fun _ _ ↦ le_max_right _ _)]
  constructor
  · rintro ⟨u,hu,hp⟩
    obtain ⟨hus,hm⟩ := mem_filter.mp hu
    apply lt_of_lt_of_le hm
    gcongr
    intro a ha
    refine mem_filter.mpr ⟨mem_powerset.mp hus ha,?_⟩
    by_contra! h
    have hz := prod_eq_zero (f := fun x ↦ max (f x) 0) ha (max_eq_right h)
    linarith
  · intro h
    refine ⟨_,mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _),h⟩,?_⟩
    exact prod_pos fun a ha ↦ (mem_filter.mp ha).2.trans_le (le_max_left _ _)

private theorem bisected_of_equal {α : Type*} (s : Finset α) (f : α → ℝ)
    (h : majority s f = majority s (fun a ↦ -f a)) :
    2*(s.filter fun a ↦ 0 < f a).card ≤ s.card ∧
    2*(s.filter fun a ↦ f a < 0).card ≤ s.card := by
  classical
  have dis : Disjoint (s.filter fun a ↦ 0 < f a) (s.filter fun a ↦ f a < 0) := by
    refine disjoint_left.mpr fun a ha hb ↦ ?_
    exact (mem_filter.mp ha).2.not_gt (mem_filter.mp hb).2
  have total := card_le_card (union_subset (filter_subset (0 < f ·) s) (filter_subset (f · < 0) s))
  rw [card_union_of_disjoint dis] at total
  have iff' := (majority_pos s f).symm.trans ((show 0 < majority s f ↔
      0 < majority s (fun a ↦ -f a) by rw [h]).trans (majority_pos s _))
  simp only [neg_pos] at iff'
  omega

/-- Simultaneously bisect m finite sets with a nonzero polynomial from any
m+1 independent polynomials. No perturbation or limiting measure is needed. -/
theorem polynomial_bisection_of_odd_zero {m r : ℕ} (bu : OddZero m)
    (S : Fin m → Finset (Fin r → ℝ)) (b : Fin (m+1) → MvPolynomial (Fin r) ℝ)
    (ind : LinearIndependent ℝ b) :
    ∃ v : Fin (m+1) → ℝ, let P := ∑ i, v i • b i
      P ≠ 0 ∧ ∀ j, 2*((S j).filter fun x ↦ 0 < eval x P).card ≤ (S j).card ∧
        2*((S j).filter fun x ↦ eval x P < 0).card ≤ (S j).card := by
  classical
  let w (v : Fin (m+1) → ℝ) (x : Fin r → ℝ) := ∑ i, v i * eval x (b i)
  let F (v : Fin (m+1) → ℝ) (j : Fin m) := majority (S j) (w v) - majority (S j) (w (-v))
  have cont : Continuous F := by
    apply continuous_pi
    intro j
    dsimp [F, majority, w]
    fun_prop
  have odd : ∀ v, F (-v) = -F v := by intro v; ext j; simp [F]
  obtain ⟨v,hv,hzero⟩ := bu F cont odd
  refine ⟨v,?_,?_⟩
  · intro h
    apply hv
    ext i
    exact (linearIndependent_iff'.mp ind univ v h i (mem_univ i))
  · intro j
    have h := congrFun hzero j
    change majority (S j) (w v) - majority (S j) (w (-v)) = 0 at h
    have neg : w (-v) = fun a ↦ -(w v a) := by funext a; simp [w, ← sum_neg_distrib]
    rw [neg] at h
    simpa [w] using bisected_of_equal (S j) (w v) (sub_eq_zero.mp h)
end OMA

namespace OMA
open Finset MvPolynomial
open scoped Classical
private abbrev Coord := Fin 3 → ℝ
private abbrev Poly₃ := MvPolynomial (Fin 3) ℝ

/-- Use monomials whose three exponents are each at most d. -/
theorem polynomial_ham_sandwich {m d r : ℕ} (bu : OddZero m) (hm : m < (d+1)^r)
    (S : Fin m → Finset (Fin r → ℝ)) :
    ∃ P : MvPolynomial (Fin r) ℝ, P ≠ 0 ∧ P.totalDegree ≤ r*d ∧ ∀ j,
      2*((S j).filter fun x ↦ 0 < eval x P).card ≤ (S j).card ∧
      2*((S j).filter fun x ↦ eval x P < 0).card ≤ (S j).card := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin (m+1) ↪ (Fin r → Fin (d+1))) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hm)
  let f (i : Fin (m+1)) : Fin r →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun j ↦ (e i j).val)
  have hf : Function.Injective f := by
    intro i j h
    apply e.injective
    funext k
    exact Fin.ext (congrArg (fun s : Fin r →₀ ℕ ↦ s k) h)
  let b := (basisMonomials (Fin r) ℝ) ∘ f
  have ind : LinearIndependent ℝ b := (basisMonomials _ _).linearIndependent.comp f hf
  obtain ⟨v,hP,hb⟩ := polynomial_bisection_of_odd_zero bu S b ind
  refine ⟨_,hP,totalDegree_finsetSum_le ?_,hb⟩
  intro i _
  apply (totalDegree_smul_le ..).trans
  change ((basisMonomials (Fin r) ℝ) (f i)).totalDegree ≤ _
  rw [coe_basisMonomials, totalDegree_monomial _ one_ne_zero, Finsupp.sum_fintype _ _ (by simp)]
  calc
    _ ≤ ∑ _ : Fin r, d := sum_le_sum fun j _ ↦ Nat.le_of_lt_succ (e i j).isLt
    _ = _ := by simp

/-- A j-stage partition: at most 2^j disjoint open sign regions cover the
complement of the zero set. A region may have several connected components. -/
def SignPartition {r : ℕ} (S : Finset (Fin r → ℝ)) (j : ℕ) (P : MvPolynomial (Fin r) ℝ) : Prop :=
  ∃ U : Fin (2^j) → Set (Fin r → ℝ), (∀ i, IsOpen (U i)) ∧
    (∀ i k, i ≠ k → Disjoint (U i) (U k)) ∧
    (∀ x, eval x P ≠ 0 ↔ ∃ i, x ∈ U i) ∧
    ∀ i, 2^j * (S.filter fun x ↦ x ∈ U i).card ≤ S.card

private def partitionDegree : ℕ → ℕ
  | 0 => 0
  | j+1 => partitionDegree j + 3 * 2^(j/3+1)

private theorem partition_degree_bound (j : ℕ) :
    partitionDegree j + 18 = 6 * (3+j%3) * 2^(j/3) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [partitionDegree, pow_succ]
    by_cases hr : j%3 = 2
    · rw [show (j+1)%3 = 0 by omega, show (j+1)/3 = j/3+1 by omega, pow_succ]
      rw [hr] at ih
      omega
    · rw [show (j+1)%3 = j%3+1 by omega, show (j+1)/3 = j/3 by omega]
      linarith only [ih]

private theorem partition_step_dim {r d : ℕ} {S : Finset (Fin r → ℝ)} {j : ℕ}
    {P : MvPolynomial (Fin r) ℝ}
    (part : SignPartition S j P) (bu : OddZero (2^j)) (hm : 2^j < (d+1)^r) :
    ∃ Q : MvPolynomial (Fin r) ℝ, Q ≠ 0 ∧ Q.totalDegree ≤ r*d ∧ SignPartition S (j+1) (P*Q) := by
  classical
  obtain ⟨U,ho,hd,hcov,hs⟩ := part
  let T (i : Fin (2^j)) := S.filter (fun x ↦ x ∈ U i)
  obtain ⟨Q,hQ,hdeg,hbis⟩ := polynomial_ham_sandwich bu hm T
  refine ⟨Q,hQ,hdeg,?_⟩
  let e : Fin (2^j) × Fin 2 ≃ Fin (2^(j+1)) := finProdFinEquiv
  let V (i : Fin (2^j)) (k : Fin 2) := U i ∩
    (if k = 0 then {x : Fin r → ℝ | 0 < eval x Q} else {x | eval x Q < 0})
  refine ⟨fun t ↦ V (e.symm t).1 (e.symm t).2,?_,?_,?_,?_⟩
  · intro t
    apply (ho _).inter
    split
    · exact isOpen_lt continuous_const Q.continuous_eval
    · exact isOpen_lt Q.continuous_eval continuous_const
  · intro t u htu
    obtain ⟨⟨i,k⟩,rfl⟩ := e.surjective t
    obtain ⟨⟨i',k'⟩,rfl⟩ := e.surjective u
    simp only [Equiv.symm_apply_apply]
    by_cases h : i = i'
    · subst i'
      have hkk : k ≠ k' := by rintro rfl; exact htu rfl
      fin_cases k <;> fin_cases k' <;>
        simp_all [V, Set.disjoint_left]
      all_goals intros; linarith
    · exact (hd i i' h).mono Set.inter_subset_left Set.inter_subset_left
  · intro x
    rw [map_mul, mul_ne_zero_iff, hcov]
    constructor
    · rintro ⟨⟨i,hi⟩,hx⟩
      rcases lt_or_gt_of_ne hx with hn|hp
      · exact ⟨e (i,1), by simp [V,hi,hn]⟩
      · exact ⟨e (i,0), by simp [V,hi,hp]⟩
    · rintro ⟨t,ht⟩
      obtain ⟨⟨i,k⟩,rfl⟩ := e.surjective t
      simp only [Equiv.symm_apply_apply] at ht
      refine ⟨⟨i,ht.1⟩,?_⟩
      fin_cases k
      · exact ne_of_gt (by simpa [V] using ht.2)
      · exact ne_of_lt (by simpa [V] using ht.2)
  · intro t
    obtain ⟨⟨i,k⟩,rfl⟩ := e.surjective t
    simp only [Equiv.symm_apply_apply, pow_succ, Nat.mul_assoc]
    apply le_trans _ (hs i)
    apply Nat.mul_le_mul_left
    fin_cases k
    · simpa [V,T,filter_filter] using (hbis i).1
    · simpa [V,T,filter_filter] using (hbis i).2

private theorem partition_step {S : Finset Coord} {j : ℕ} {P : Poly₃}
    (part : SignPartition S j P) (bu : OddZero (2^j)) :
    ∃ Q : Poly₃, Q ≠ 0 ∧ Q.totalDegree ≤ 3*2^(j/3+1) ∧ SignPartition S (j+1) (P*Q) := by
  classical
  let d := 2^(j/3+1)
  have hm : 2^j < (d+1)^3 := by
    have h : 2^j ≤ d^3 := by
      dsimp [d]
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact h.trans_lt (Nat.pow_lt_pow_left (by omega) (by decide))
  exact partition_step_dim part bu hm

/-- Polynomial partitioning of any finite sample, conditional only on the
odd-map zero theorem in the bisection dimensions. -/
theorem polynomial_partition_of_odd_zero (bu : ∀ m, OddZero m) (S : Finset Coord) (j : ℕ) :
    ∃ P : Poly₃, P ≠ 0 ∧ P.totalDegree ≤ 30*2^(j/3) ∧ SignPartition S j P := by
  classical
  suffices h : ∃ P : Poly₃, P ≠ 0 ∧ P.totalDegree ≤ partitionDegree j ∧ SignPartition S j P by
    obtain ⟨P,hP,hd,hpart⟩ := h
    refine ⟨P,hP,hd.trans ?_,hpart⟩
    have hb := partition_degree_bound j
    have hrem : j%3 ≤ 2 := by omega
    nlinarith [Nat.mul_le_mul_right (2^(j/3)) (Nat.mul_le_mul_left 6 (Nat.add_le_add_left hrem 3))]
  induction j with
  | zero =>
    exact ⟨1,one_ne_zero,by simp [partitionDegree],fun _ ↦ Set.univ,fun _ ↦ isOpen_univ,
      fun i k h ↦ False.elim (h (Subsingleton.elim (α := Fin 1) i k)),by simp,by simp⟩
  | succ j ih =>
    obtain ⟨P,hP,hd,hpart⟩ := ih
    obtain ⟨Q,hQ,hdeg,hnew⟩ := partition_step hpart (bu _)
    exact ⟨P*Q,mul_ne_zero hP hQ,(totalDegree_mul ..).trans (Nat.add_le_add hd hdeg),hnew⟩
end OMA

namespace OMA
open Finset MvPolynomial
/-- A line meeting a degree-D wall in more than D distinct parameters lies
entirely on the wall. -/
theorem line_wall_alternative {r : ℕ} (P : MvPolynomial (Fin r) ℝ) (a v : Fin r → ℝ) :
    (∀ t : ℝ, eval (fun i ↦ a i + t*v i) P = 0) ∨
    ∀ Z : Finset ℝ, (∀ t ∈ Z, eval (fun i ↦ a i + t*v i) P = 0) →
      Z.card ≤ P.totalDegree := by
  classical
  let f (i : Fin r) : Polynomial ℝ := Polynomial.C (a i) + Polynomial.X * Polynomial.C (v i)
  let F := eval₂Hom Polynomial.C f
  have hf (i) : (f i).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  have degree : (F P).natDegree ≤ P.totalDegree := by
    conv_lhs => rw [P.as_sum, map_sum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro s hs
    change (eval₂Hom Polynomial.C f (monomial s (coeff s P))).natDegree ≤ _
    rw [eval₂Hom_monomial]
    apply Polynomial.natDegree_mul_le.trans
    rw [Polynomial.natDegree_C, zero_add]
    apply (Polynomial.natDegree_prod_le ..).trans
    apply le_trans _ (le_totalDegree hs)
    apply sum_le_sum
    intro i _
    exact Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))
  have ev (t : ℝ) : (F P).eval t = eval (fun i ↦ a i + t*v i) P := by
    change Polynomial.evalRingHom t (eval₂Hom _ _ _) = _
    rw [map_eval₂Hom]
    apply eval₂Hom_congr
    · ext; simp
    · funext i
      simp [f]
      exact mul_comm _ _
    · rfl
  by_cases h : F P = 0
  · left; intro t; rw [← ev,h,Polynomial.eval_zero]
  · right; intro Z hZ
    apply le_trans _ degree
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    exact (Polynomial.mem_roots h).mpr ((ev t).trans (hZ t ht))
end OMA

namespace OMA
open Finset MvPolynomial
open scoped Classical
/-- An affine line visits at most D+1 regions of any disjoint open partition
of the complement of a degree-D wall. -/
theorem line_region_count {r : ℕ} {ι : Type*} [Fintype ι] (U : ι → Set (Fin r → ℝ))
    (ho : ∀ i, IsOpen (U i)) (hd : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (P : MvPolynomial (Fin r) ℝ) (hc : ∀ x, eval x P ≠ 0 ↔ ∃ i, x ∈ U i)
    (a v : Fin r → ℝ) :
    (univ.filter (fun i ↦ ∃ t : ℝ, (fun j ↦ a j+t*v j) ∈ U i)).card ≤ P.totalDegree+1 := by
  classical
  let l (t : ℝ) (j : Fin r) := a j + t*v j
  let H := univ.filter (fun i ↦ ∃ t, l t ∈ U i)
  change H.card ≤ _
  have hcont : Continuous l := by unfold l; fun_prop
  obtain hall | hb := line_wall_alternative P a v
  · have emp : H = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨t,ht⟩ := (mem_filter.mp hi).2
      exact (hc _).2 ⟨i,ht⟩ (hall t)
    simp [emp]
  let Z := {t : ℝ | eval (l t) P = 0}
  have hfin : Z.Finite := by
    by_contra hinf
    obtain ⟨T,hT,ht⟩ := Set.Infinite.exists_subset_card_eq hinf (P.totalDegree+1)
    have := hb T (fun t h ↦ hT h)
    omega
  let R := hfin.toFinset
  have hR (t : ℝ) : t ∈ R ↔ eval (l t) P = 0 := hfin.mem_toFinset
  have hsize := hb R (fun t h ↦ (hR t).1 h)
  let rank (t : ℝ) := (R.filter (· < t)).card
  have same {t u : ℝ} {i j : ι} (htu : t ≤ u) (hi : l t ∈ U i) (hj : l u ∈ U j)
      (hr : rank t = rank u) : i = j := by
    have mono : R.filter (· < t) ⊆ R.filter (· < u) := by
      intro x hx
      obtain ⟨hx,hl⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hx,hl.trans_le htu⟩
    have eqf := eq_of_subset_of_card_le mono hr.ge
    have outside (z : ℝ) (hz : z ∈ Set.Icc t u) : eval (l z) P ≠ 0 := by
      intro he
      have hzu : z < u := lt_of_le_of_ne hz.2 (by rintro rfl; exact (hc _).2 ⟨j,hj⟩ he)
      have mem : z ∈ R.filter (· < u) := mem_filter.mpr ⟨(hR z).2 he,hzu⟩
      rw [← eqf] at mem
      exact hz.1.not_gt (mem_filter.mp mem).2
    by_contra hij
    let V := ⋃ k : {k : ι // k ≠ i}, l ⁻¹' U k
    have hV : IsOpen V := isOpen_iUnion (fun k ↦ (ho _).preimage hcont)
    have dis : Disjoint (l ⁻¹' U i) V := by
      apply Set.disjoint_left.mpr
      intro x hx hVx
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hVx
      exact Set.disjoint_left.mp (hd i k k.2.symm) hx hk
    have cov : Set.Icc t u ⊆ (l ⁻¹' U i) ∪ V := by
      intro x hx
      obtain ⟨k,hk⟩ := (hc _).mp (outside _ hx)
      by_cases he : k = i
      · subst k; exact Or.inl hk
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k,he⟩,hk⟩)
    have inU := isPreconnected_Icc.subset_left_of_subset_union ((ho i).preimage hcont) hV dis
      cov ⟨t,⟨le_rfl,htu⟩,hi⟩
    exact Set.disjoint_left.mp (hd i j hij) (inU (Set.right_mem_Icc.mpr htu)) hj
  let t (i : ι) : ℝ := if h : ∃ t, l t ∈ U i then h.choose else 0
  have hit (i : ι) (h : i ∈ H) : l (t i) ∈ U i := by
    have hi := (mem_filter.mp h).2
    simpa only [t, dif_pos hi] using hi.choose_spec
  have le : H.card ≤ (range (R.card+1)).card := by
    apply card_le_card_of_injOn (fun i ↦ rank (t i))
    · intro i _
      exact mem_range.mpr (Nat.lt_succ_of_le (card_filter_le ..))
    · intro i hi j hj he
      rcases le_total (t i) (t j) with h|h
      · exact same h (hit i hi) (hit j hj) he
      · exact (same h (hit j hj) (hit i hi) he.symm).symm
  rw [card_range] at le
  omega
end OMA

namespace OMA
open Finset MvPolynomial
open scoped Classical

/-- Prescribing a degree budget D gives between (D/60)³ and D³ sign-region
indices, with at most |S| divided by the number of indices in each region. -/
theorem partition_of_degree_budget (bu : ∀ m, OddZero m) (S : Finset (Fin 3 → ℝ))
    (D : ℕ) (hD : 0 < D) : ∃ (j : ℕ) (P : MvPolynomial (Fin 3) ℝ),
    P ≠ 0 ∧ P.totalDegree ≤ D ∧ 2^j ≤ D^3 ∧ D^3 ≤ 60^3 * 2^j ∧ SignPartition S j P := by
  classical
  by_cases h : 30 ≤ D
  · let k := Nat.log 2 (D/30)
    have hlow := Nat.pow_log_le_self 2 (by omega : D/30 ≠ 0)
    have hhigh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (D/30)
    change 2^k ≤ D/30 at hlow
    change D/30 < 2^(k+1) at hhigh
    rw [pow_succ] at hhigh
    have lo : 30*2^k ≤ D := by omega
    have hi : D ≤ 60*2^k := by omega
    obtain ⟨P,hp,hd,hpart⟩ := polynomial_partition_of_odd_zero bu S (k*3)
    refine ⟨k*3,P,hp,hd.trans (by simpa using lo),?_,?_,hpart⟩
    · rw [pow_mul]
      exact Nat.pow_le_pow_left (by omega) _
    · simpa [pow_mul, mul_pow] using Nat.pow_le_pow_left hi 3
  · have hpart : SignPartition S 0 1 :=
      ⟨fun _ ↦ Set.univ,fun _ ↦ isOpen_univ,
        fun i k hk ↦ False.elim (hk (Subsingleton.elim (α := Fin 1) i k)),by simp,by simp⟩
    refine ⟨0,1,one_ne_zero,by simp,by simpa using Nat.one_le_pow 3 D hD,?_,hpart⟩
    simpa using Nat.pow_le_pow_left (show D ≤ 60 by omega) 3

/-- Summed over the line family, the total number of line–region incidences
is at most (D+1)|L|. The index type can distinguish lines even if their
parametrizations coincide. -/
theorem total_line_region_count {r : ℕ} {ι κ : Type*} [Fintype ι] (L : Finset κ)
    (U : ι → Set (Fin r → ℝ)) (ho : ∀ i, IsOpen (U i))
    (hd : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (P : MvPolynomial (Fin r) ℝ)
    (hc : ∀ x, eval x P ≠ 0 ↔ ∃ i, x ∈ U i) (a v : κ → Fin r → ℝ) :
    (∑ i, (L.filter (fun l ↦ ∃ t : ℝ, (fun j ↦ a l j+t*v l j) ∈ U i)).card) ≤
      L.card * (P.totalDegree+1) := by
  classical
  let hits (i : ι) (l : κ) := ∃ t : ℝ, (fun j ↦ a l j+t*v l j) ∈ U i
  change (∑ i, (L.filter (hits i)).card) ≤ _
  simp_rw [card_filter]
  rw [sum_comm]
  calc
    _ ≤ ∑ _ ∈ L, (P.totalDegree+1) := by
      apply sum_le_sum
      intro l _
      simpa only [card_filter] using line_region_count U ho hd P hc (a l) (v l)
    _ = _ := by simp

end OMA

namespace OMA
open Finset MvPolynomial
open scoped Classical

private theorem cell_count_linear {s l M A B : ℝ} (hs : 0 ≤ s) (hl : 0 ≤ l)
    (ha : 0 ≤ A) (hb : 0 ≤ B) (hcap : s ≤ M) (hst : s ≤ A*l^2 + B*l) :
    s ≤ (Real.sqrt (2*A*M) + 2*B)*l := by
  have hm := hs.trans hcap
  by_cases h : s ≤ 2*B*l
  · nlinarith [mul_nonneg (Real.sqrt_nonneg (2*A*M)) hl]
  · have h₁ : s ≤ (2*A)*l^2 := by linarith
    have h₂ := mul_le_mul hcap h₁ hs hm
    have h₃ := Real.sq_sqrt (show 0 ≤ 2*A*M by positivity)
    have he : s^2 ≤ (Real.sqrt (2*A*M)*l)^2 := by
      nlinarith only [h₂,congrArg (fun x : ℝ ↦ x*l^2) h₃]
    have hle := le_of_sq_le_sq he (mul_nonneg (Real.sqrt_nonneg _) hl)
    nlinarith [mul_nonneg hb hl]

/-- Cellular incidence estimate. If k-rich points on any subfamily of the
input lines satisfy the planar bound A|L|²+B|L|, then the points outside a
partition wall obey the displayed bound. For Szemerédi–Trotter take
A=C/k³ and B=C/k. -/
theorem cellular_incidence_bound {ι κ : Type*} [Fintype ι]
    (S : Finset (Fin 3 → ℝ)) (L : Finset κ) (a v : κ → Fin 3 → ℝ)
    (k : ℕ) (A B M : ℝ) (ha : 0 ≤ A) (hb : 0 ≤ B)
    (rich : ∀ x ∈ S, k ≤ (L.filter fun l ↦ ∃ t : ℝ, x = (fun j ↦ a l j+t*v l j)).card)
    (st : ∀ T ⊆ S, ∀ F ⊆ L,
      (∀ x ∈ T, k ≤ (F.filter fun l ↦ ∃ t : ℝ, x = (fun j ↦ a l j+t*v l j)).card) →
      (T.card : ℝ) ≤ A*(F.card : ℝ)^2 + B*F.card)
    (U : ι → Set (Fin 3 → ℝ)) (ho : ∀ i, IsOpen (U i))
    (hd : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (P : MvPolynomial (Fin 3) ℝ)
    (hc : ∀ x, eval x P ≠ 0 ↔ ∃ i, x ∈ U i)
    (hcap : ∀ i, ((S.filter fun x ↦ x ∈ U i).card : ℝ) ≤ M) :
    ((S.filter fun x ↦ eval x P ≠ 0).card : ℝ) ≤
      (Real.sqrt (2*A*M)+2*B) * (L.card * (P.totalDegree+1) : ℝ) := by
  classical
  let T (i : ι) := S.filter (fun x ↦ x ∈ U i)
  let F (i : ι) := L.filter (fun l ↦ ∃ t : ℝ, (fun j ↦ a l j+t*v l j) ∈ U i)
  let D := Real.sqrt (2*A*M)+2*B
  have cover : S.filter (fun x ↦ eval x P ≠ 0) = univ.biUnion T := by
    ext x
    simp only [T, mem_filter, hc, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨hx,i,hi⟩
      exact ⟨i,hx,hi⟩
    · rintro ⟨i,hx,hi⟩
      exact ⟨hx,i,hi⟩
  have sc : (S.filter fun x ↦ eval x P ≠ 0).card ≤ ∑ i, (T i).card := by
    rw [cover]
    exact card_biUnion_le
  have bound (i : ι) : ((T i).card : ℝ) ≤ D * (F i).card := by
    apply cell_count_linear (by positivity) (by positivity) ha hb (hcap i)
    apply st _ (filter_subset ..) _ (filter_subset ..)
    intro x hx
    apply (rich x (mem_filter.mp hx).1).trans
    apply card_le_card
    intro l hl
    obtain ⟨hl,⟨t,ht⟩⟩ := mem_filter.mp hl
    apply mem_filter.mpr
    exact ⟨mem_filter.mpr ⟨hl,t,ht ▸ (mem_filter.mp hx).2⟩,t,ht⟩
  have lc := total_line_region_count L U ho hd P hc a v
  have lc' : (∑ i, ((F i).card : ℝ)) ≤ (L.card : ℝ)*(P.totalDegree+1) := by exact_mod_cast lc
  calc
    _ ≤ ∑ i, ((T i).card : ℝ) := by exact_mod_cast sc
    _ ≤ ∑ i, D * (F i).card := sum_le_sum fun i _ ↦ bound i
    _ = D * ∑ i, ((F i).card : ℝ) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left lc' (by dsimp [D]; positivity)
end OMA

namespace OMA
open Finset MvPolynomial
open scoped Classical

/-- Coordinates of a line in the order (height, horizontal x, horizontal y). -/
def ESLine.coords (l : ESLine) (t : ℝ) : Fin 3 → ℝ :=
  ![t,l.x+t*l.u,l.y+t*l.v]

private def complexCoords (l : ESLine) (t : ℂ) : Fin 3 → ℂ :=
  ![t,(l.x : ℂ)+t*l.u,(l.y : ℂ)+t*l.v]

private theorem linear_subst_degree {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (c : R →+* S) (g : σ → MvPolynomial τ S) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (P : MvPolynomial σ R) :
    (eval₂Hom (C.comp c) g P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum,map_sum]
  apply totalDegree_finsetSum_le
  intro s hs
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul ..).trans
  rw [RingHom.comp_apply,totalDegree_C,zero_add]
  apply (totalDegree_finsetProd ..).trans
  apply le_trans _ (le_totalDegree hs)
  apply sum_le_sum
  intro i _
  exact (totalDegree_pow ..).trans (by simpa using Nat.mul_le_mul_left (s i) (hg i))

private abbrev ComplexSurface := MvPolynomial (Fin 3) ℂ
private noncomputable def sliceVars : Fin 3 → Poly₂ :=
  ![C Complex.I,X 0+X 1,C Complex.I*(X 0-X 1)]
private noncomputable def heightSlice (P : ComplexSurface) : Poly₂ :=
  eval₂Hom C sliceVars P

private theorem heightSlice_degree (P : ComplexSurface) :
    (heightSlice P).totalDegree ≤ P.totalDegree := by
  apply linear_subst_degree (RingHom.id ℂ)
  intro i
  fin_cases i
  · simp [sliceVars]
  · exact (totalDegree_add ..).trans (by simp)
  · apply (totalDegree_mul ..).trans
    rw [totalDegree_C,zero_add]
    exact (totalDegree_sub ..).trans (by simp)

private theorem eval_heightSlice (P : ComplexSurface) (w : Fin 2 → ℂ) :
    eval w (heightSlice P) = eval ![Complex.I, w 0+w 1, Complex.I*(w 0-w 1)] P := by
  unfold heightSlice
  rw [map_eval₂Hom]
  apply eval₂Hom_congr
  · ext; simp
  · funext i
    fin_cases i <;> simp [sliceVars]
  · rfl

private theorem slice_factor {P : ComplexSurface} (hz : heightSlice P = 0) :
    ∃ Q : ComplexSurface, P = (X 0-C Complex.I)*Q := by
  let e := finSuccEquiv ℂ 2
  have root : (e P).eval (C Complex.I) = 0 := by
    apply MvPolynomial.funext
    intro w
    rw [eval_polynomial_eval_finSuccEquiv]
    let v : Fin 2 → ℂ := ![(w 0-Complex.I*w 1)/2,(w 0+Complex.I*w 1)/2]
    have hx : v 0 + v 1 = w 0 := by dsimp [v]; ring
    have hy : Complex.I*(v 0-v 1) = w 1 := by
      dsimp [v]
      linear_combination -(w 1)*Complex.I_mul_I
    have he := eval_heightSlice P v
    rw [hz,map_zero,hx,hy] at he
    convert he.symm using 2
    · apply congrArg eval
      funext i; fin_cases i <;> simp <;> rfl
    · simp
  obtain ⟨q,hq⟩ := Polynomial.dvd_iff_isRoot.mpr root
  refine ⟨e.symm q,e.injective ?_⟩
  rw [map_mul,map_sub,e.apply_symm_apply,hq]
  simp [e,finSuccEquiv_apply]

private theorem trace_at_I {P : ComplexSurface} {l : ESLine}
    (h : ∀ t : ℝ, eval (complexCoords l t) P = 0) :
    eval (complexCoords l Complex.I) P = 0 := by
  let g : Fin 3 → Polynomial ℂ := ![Polynomial.X, Polynomial.C (l.x : ℂ) +
    Polynomial.X*Polynomial.C (l.u : ℂ), Polynomial.C (l.y : ℂ)+Polynomial.X*Polynomial.C (l.v : ℂ)]
  let q := eval₂Hom Polynomial.C g P
  have ev (t : ℂ) : q.eval t = eval (complexCoords l t) P := by
    change Polynomial.evalRingHom t (eval₂Hom _ _ _) = _
    rw [map_eval₂Hom]
    apply eval₂Hom_congr
    · ext; simp
    · funext i
      fin_cases i <;> simp [g,complexCoords] <;> exact mul_comm _ _
    · rfl
  have z : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
    rintro _ ⟨r,rfl⟩
    exact (ev (r : ℂ)).trans (h r)
  rw [← ev,z,Polynomial.eval_zero]

private theorem grid_zero_count (A : Finset Point) (L : Finset Pair) (hL : L ⊆ A ×ˢ A)
    (P : Poly₂) (hP : P ≠ 0) (hv : ∀ q ∈ L, eval ![leftCoord q.1,rightCoord q.2] P = 0) :
    L.card ≤ P.totalDegree*(2*A.card) := by
  classical
  obtain h | ⟨q,hq⟩ := L.eq_empty_or_nonempty
  · simp [h]
  let S := A.image leftCoord ∪ A.image rightCoord
  have hs : S.Nonempty := ⟨_,mem_union_left _ (mem_image_of_mem _ (mem_product.mp (hL hq)).1)⟩
  let V := (Fintype.piFinset fun _ : Fin 2 ↦ S).filter (fun v ↦ eval v P = 0)
  have inj : L.card ≤ V.card := by
    apply card_le_card_of_injOn (fun ab : Pair ↦ ![leftCoord ab.1,rightCoord ab.2])
    · intro ab hab
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_,hv ab hab⟩
      intro i
      fin_cases i
      · exact mem_union_left _ (mem_image_of_mem _ (mem_product.mp (hL hab)).1)
      · exact mem_union_right _ (mem_image_of_mem _ (mem_product.mp (hL hab)).2)
    · intro ab _ cd _ he
      have h₀ := congrFun he 0
      have h₁ := congrFun he 1
      change leftCoord ab.1 = leftCoord cd.1 at h₀
      change rightCoord ab.2 = rightCoord cd.2 at h₁
      exact Prod.ext (point_ext (congrArg Complex.re h₀) (neg_inj.mp (congrArg Complex.im h₀)))
        (point_ext (congrArg Complex.re h₁) (congrArg Complex.im h₁))
  have hspos : 0 < (S.card : ℚ≥0) := by exact_mod_cast hs.card_pos
  have sz := schwartz_zippel_totalDegree hP S
  change (V.card : ℚ≥0) / (S.card : ℚ≥0)^2 ≤ _ at sz
  rw [div_le_div_iff₀ (by positivity) hspos] at sz
  have h' : (V.card : ℚ≥0)*S.card ≤ (P.totalDegree * (S.card : ℚ≥0))*S.card := by
    simpa [pow_two,mul_assoc] using sz
  have hV : V.card ≤ P.totalDegree * S.card := by exact_mod_cast le_of_mul_le_mul_right h' hspos
  exact inj.trans (hV.trans (Nat.mul_le_mul_left _ (by
    rw [two_mul]; exact (card_union_le ..).trans (Nat.add_le_add card_image_le card_image_le))))

private theorem surface_cap_complex (P : ComplexSurface) (hP : P ≠ 0)
    (A : Finset Point) (L : Finset Pair) (hL : L ⊆ A ×ˢ A)
    (vanish : ∀ q ∈ L, ∀ t : ℝ, eval (complexCoords (esLine q.1 q.2) t) P = 0) :
    L.card ≤ P.totalDegree*(2*A.card) := by
  classical
  by_cases hz : heightSlice P = 0
  · obtain ⟨Q,he⟩ := slice_factor hz
    let F : ComplexSurface := X 0 - C Complex.I
    have hF : F.totalDegree ≠ 0 := by
      intro h
      have e := totalDegree_eq_zero_iff_eq_C.mp h
      have e₀ := congrArg (fun p : ComplexSurface ↦ eval (fun _ ↦ 0) p) e
      have e₁ := congrArg (fun p : ComplexSurface ↦ eval (fun _ ↦ 1) p) e
      simp only [F,map_sub,eval_X,eval_C] at e₀ e₁
      exact one_ne_zero (by linear_combination e₁ - e₀ : (1 : ℂ) = 0)
    have hQ : Q ≠ 0 := by rintro rfl; simp_all
    have deg : P.totalDegree = F.totalDegree + Q.totalDegree := by
      rw [he,totalDegree_mul_of_isDomain (by rintro h; simp [F,h] at hF) hQ]
    have lt : Q.totalDegree < P.totalDegree := by omega
    have small := surface_cap_complex Q hQ A L hL (by
      intro q hq t
      have ht := vanish q hq t
      rw [he,map_mul,map_sub,eval_X,eval_C] at ht
      apply (mul_eq_zero.mp ht).resolve_left
      intro h
      have bad := congrArg Complex.im (sub_eq_zero.mp h)
      simp [complexCoords] at bad)
    exact small.trans (Nat.mul_le_mul_right _ lt.le)
  · apply le_trans _ (Nat.mul_le_mul_right _ (heightSlice_degree P))
    apply grid_zero_count A L hL _ hz
    intro q hq
    rw [eval_heightSlice]
    convert trace_at_I (vanish q hq) using 2
    apply congrArg eval
    funext i
    fin_cases i <;> apply Complex.ext <;>
      simp [complexCoords,leftCoord,rightCoord,esLine,Complex.mul_re,Complex.mul_im] <;> ring
termination_by P.totalDegree

/-- A real surface of degree d contains at most 2d|A| lines from the full
Elekes–Sharir family. Remove factors of z-i before using the complex slice. -/
theorem surface_line_cap (P : MvPolynomial (Fin 3) ℝ) (hp : P ≠ 0) (A : Finset Point) :
    ((A ×ˢ A).filter (fun q ↦ ∀ t : ℝ, eval ((esLine q.1 q.2).coords t) P = 0)).card ≤
      P.totalDegree * (2*A.card) := by
  classical
  let Q := MvPolynomial.map Complex.ofRealHom P
  have hn : Q ≠ 0 := (map_injective _ Complex.ofReal_injective).ne (by simpa using hp)
  have hd : Q.totalDegree ≤ P.totalDegree := by
    unfold Q
    rw [map_eq_eval₂Hom_C_comp]
    apply linear_subst_degree Complex.ofRealHom X
    simp
  apply le_trans _ (Nat.mul_le_mul_right _ hd)
  apply surface_cap_complex Q hn _ _ (filter_subset ..)
  intro q hq t
  have h := (mem_filter.mp hq).2 t
  let l := esLine q.1 q.2
  have ec : complexCoords l (t : ℂ) = fun j ↦ ((l.coords t j : ℝ) : ℂ) := by
    funext i
    fin_cases i <;> simp [complexCoords,ESLine.coords]
  rw [show esLine q.1 q.2 = l from rfl, ec]
  change eval _ (MvPolynomial.map _ P) = _
  rw [eval_map]
  have eq := map_eval₂Hom (RingHom.id ℝ) (l.coords t) Complex.ofRealHom P
  change Complex.ofRealHom (eval (l.coords t) P) = _ at eq
  rw [h,map_zero] at eq
  exact eq.symm
end OMA

namespace OMA
open Finset MvPolynomial
open scoped Classical

private def base (q : Pair) : Coord := ![0,(esLine q.1 q.2).x,(esLine q.1 q.2).y]
private def dir (q : Pair) : Coord := ![1,(esLine q.1 q.2).u,(esLine q.1 q.2).v]
private def onLine (x : Coord) (q : Pair) : Prop :=
  ∃ t : ℝ, x = (fun j ↦ base q j + t*dir q j)
private theorem param (q : Pair) (t : ℝ) :
    (fun j ↦ base q j + t*dir q j) = (esLine q.1 q.2).coords t := by
  funext j
  fin_cases j <;> simp [base,dir,ESLine.coords]

def RichOn (S : Finset (Fin 3 → ℝ)) (F : Finset Pair) (k : ℕ) : Prop :=
  ∀ x ∈ S, k ≤ (F.filter (onLine x)).card

/-- The classical Szemerédi–Trotter rich-point estimate, in the form obtained
by a generic planar projection of each finite family of distinct lines. -/
def PlanarIncidenceBound : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (A : Finset Point) (F : Finset Pair), F ⊆ A ×ˢ A →
    ∀ (k : ℕ), 2 ≤ k → ∀ S : Finset (Fin 3 → ℝ), RichOn S F k →
      (S.card : ℝ) ≤ C/(k : ℝ)^3 * (F.card : ℝ)^2 + C/k * F.card

private def contained (P : Poly₃) (q : Pair) : Prop :=
  ∀ t : ℝ, eval ((esLine q.1 q.2).coords t) P = 0

private theorem transverse_count (P : Poly₃) (q : Pair) (hq : ¬ contained P q)
    (S : Finset Coord) (hz : ∀ x ∈ S, eval x P = 0) :
    (S.filter (fun x ↦ onLine x q)).card ≤ P.totalDegree := by
  classical
  have ht : ∀ x, onLine x q → x = (esLine q.1 q.2).coords (x 0) := by
    rintro x ⟨t,rfl⟩
    rw [param]
    rfl
  let T := S.filter (fun x ↦ onLine x q)
  let Z := T.image (fun x ↦ x 0)
  have inj : Z.card = T.card := by
    apply card_image_iff.mpr
    intro x hx y hy he
    exact (ht x (mem_filter.mp hx).2).trans ((congrArg (esLine q.1 q.2).coords he).trans (ht y (mem_filter.mp hy).2).symm)
  rw [← show T.card = (S.filter fun x ↦ onLine x q).card from rfl, ← inj]
  rcases line_wall_alternative P (base q) (dir q) with all|bound
  · exact (hq (fun t ↦ by simpa only [param] using all t)).elim
  · apply bound
    intro t h
    obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    rw [param,← ht x (mem_filter.mp hx).2]
    exact hz x (mem_filter.mp hx).1

private theorem wall_split (P : Poly₃) (F : Finset Pair) (S : Finset Coord) (k : ℕ)
    (hk : 2 ≤ k) (rich : RichOn S F k) (hz : ∀ x ∈ S, eval x P = 0) :
    ∃ G : Finset Coord, S.card*k ≤ G.card*k + 3*P.totalDegree*F.card ∧
      RichOn G (F.filter (contained P)) (max 2 ((k+1)/2)) := by
  classical
  let W := F.filter (contained P)
  let V := F.filter (fun q ↦ ¬ contained P q)
  let G := S.filter (fun x ↦ 3*(V.filter (onLine x)).card < k)
  let B := S.filter (fun x ↦ ¬ 3*(V.filter (onLine x)).card < k)
  have split : G.card+B.card = S.card := card_filter_add_card_filter_not ..
  have inc : ∑ x ∈ B, (V.filter (onLine x)).card = ∑ q ∈ V, (B.filter (fun x ↦ onLine x q)).card := by
    simp_rw [card_filter]; rw [sum_comm]
  have bad : B.card*k ≤ 3*P.totalDegree*F.card := by
    calc
      _ = ∑ _ ∈ B, k := by simp
      _ ≤ ∑ x ∈ B, 3*(V.filter (onLine x)).card :=
        sum_le_sum fun x hx ↦ Nat.le_of_not_gt (mem_filter.mp hx).2
      _ = 3*∑ q ∈ V, (B.filter (fun x ↦ onLine x q)).card := by rw [← mul_sum,inc]
      _ ≤ 3*∑ _ ∈ V, P.totalDegree := Nat.mul_le_mul_left _ (sum_le_sum fun q hq ↦
        transverse_count P q (mem_filter.mp hq).2 B fun x hx ↦ hz x (mem_filter.mp hx).1)
      _ ≤ _ := by
        simp only [sum_const,nsmul_eq_mul,Nat.cast_id]
        have hv : V.card ≤ F.card := card_filter_le ..
        nlinarith only [Nat.mul_le_mul_right (3*P.totalDegree) hv]
  refine ⟨G,by rw [← split,add_mul]; omega,?_⟩
  intro x hx
  obtain ⟨hs,hgood⟩ := mem_filter.mp hx
  have total := card_filter_add_card_filter_not (s := F.filter (onLine x)) (contained P)
  have eq : (W.filter (onLine x)).card + (V.filter (onLine x)).card =
      (F.filter (onLine x)).card := by simpa [W,V,filter_filter,and_comm] using total
  have := rich x hs
  change max 2 ((k+1)/2) ≤ (W.filter (onLine x)).card
  omega

private theorem cell_fraction {C n m k d s : ℝ} (hC : 1 ≤ C) (hn : 0 < n) (hk : 0 < k)
    (hm : 0 ≤ m) (hd : 1 ≤ d) (hs : 0 ≤ s) (hm₂ : m ≤ n^2)
    (lo : 64*n*k*d ≤ m) (hi : m ≤ 128*n*k*d)
    (large : 10^12*C*n*m ≤ s*k^2) :
    (Real.sqrt (2*(C/k^3)*(s*60^3/d^3))+2*(C/k))*(m*(d+1)) ≤ s/2 := by
  have hc : 0 ≤ C := by linarith
  have hd' : 0 < d := by linarith
  let u := Real.sqrt (2*(C/k^3)*(s*60^3/d^3))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 := Real.sq_sqrt (show 0 ≤ 2*(C/k^3)*(s*60^3/d^3) by positivity)
  change u^2 = _ at hu2
  field_simp at hu2
  have sumb : 512*60^3*C*m*m ≤ s*k^3*d := by
    calc
      _ ≤ 512*60^3*C*(128*n*k*d)*m := by gcongr
      _ ≤ (10^12*C*n*m)*(k*d) := by
        nlinarith only [show 0 ≤ C*n*m*(k*d) by positivity]
      _ ≤ (s*k^2)*(k*d) := by gcongr
      _ = _ := by ring
  have quad : (8*u*m*d)^2 ≤ s^2 := by
    apply le_of_mul_le_mul_right (a := k^3*d^3) _ (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right sumb (show 0 ≤ s*d^2 by positivity),
      congrArg (fun r : ℝ ↦ 64*m^2*d^2*r) hu2,
      show 0 ≤ C*m^2*d^2*s by positivity]
  have root := le_of_sq_le_sq quad hs
  have dk : 64*k*d ≤ n := by
    apply le_of_mul_le_mul_left (a := n) _ hn
    nlinarith only [lo,hm₂]
  have lin : 16*(C/k)*m*d ≤ s := by
    apply le_of_mul_le_mul_right (a := k^2) _ (by positivity)
    have h : C/k*k = C := div_mul_cancel₀ _ hk.ne'
    nlinarith only [mul_le_mul_of_nonneg_right dk (show 0 ≤ C*m by positivity), large,
      congrArg (fun x : ℝ ↦ 16*x*m*d*k) h, show 0 ≤ C*n*m by positivity]
  change (u+2*(C/k))*(m*(d+1)) ≤ _
  nlinarith only [root,lin,mul_le_mul_of_nonneg_left hd (show 0 ≤ (u+2*(C/k))*m by positivity)]

private theorem induction_rich (bu : ∀ m, OddZero m) {C : ℝ} (hC : 1 ≤ C)
    (A : Finset Point)
    (st : ∀ F : Finset Pair, F ⊆ A ×ˢ A → ∀ k : ℕ, 2 ≤ k →
      ∀ S : Finset Coord, RichOn S F k →
        (S.card : ℝ) ≤ C/(k : ℝ)^3*(F.card : ℝ)^2 + C/k * F.card)
    (F : Finset Pair) (hF : F ⊆ A ×ˢ A) (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ A.card)
    (S : Finset Coord) (rich : RichOn S F k) :
    (S.card : ℝ)*(k : ℝ)^2 ≤ 10^12*C*A.card*F.card := by
  classical
  let n := A.card
  let m := F.card
  let s := S.card
  change (s : ℝ)*(k : ℝ)^2 ≤ 10^12*C*n*m
  have hn : 0 < n := by dsimp [n]; omega
  have kp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have np : (0 : ℝ) < n := by exact_mod_cast hn
  have cp : 0 < C := by linarith
  have mcap : m ≤ n^2 := by simpa [m,n,pow_two] using card_le_card hF
  by_cases small : m < 128*n*k
  · have sb := st F hF k hk S rich
    change (s : ℝ) ≤ C/(k : ℝ)^3*(m : ℝ)^2+C/k*m at sb
    have sm : (m : ℝ) ≤ 128*n*k := by exact_mod_cast small.le
    have kn : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hmul := (le_div_iff₀ (pow_pos kp 3)).mp (show (s : ℝ) ≤
        (C*m^2 + C*m*k^2)/(k : ℝ)^3 from by
      convert sb using 1; field_simp)
    apply le_of_mul_le_mul_right (a := (k : ℝ)) _ kp
    nlinarith only [hmul,mul_le_mul_of_nonneg_right sm (show 0 ≤ C*m by positivity),
      mul_le_mul_of_nonneg_right kn (show 0 ≤ C*m*k by positivity),
      show 0 ≤ C*n*m*k by positivity]
  push Not at small
  let b := 64*n*k
  let d := m/b
  have bp : 0 < b := by dsimp [b]; positivity
  have bm : b ≤ m := by dsimp [b]; nlinarith only [small,show 0 ≤ n*k by positivity]
  have dp : 0 < d := Nat.div_pos bm bp
  have lo : b*d ≤ m := by simpa [d,Nat.mul_comm] using Nat.div_mul_le_self m b
  have hi : m ≤ 2*b*d := by
    have hr := Nat.mod_lt m bp
    have he := Nat.mod_add_div m b
    have hb : b ≤ b*d := by simpa using Nat.mul_le_mul_left b dp
    dsimp [d] at hb ⊢
    nlinarith only [hr,he,hb]
  by_contra! large
  obtain ⟨j,P,hP,deg,_,budget,U,ho,dis,cov,cap⟩ := partition_of_degree_budget bu S d dp
  let M : ℝ := s*60^3/(d : ℝ)^3
  have rd : 0 < (d : ℝ) := by exact_mod_cast dp
  have cap' (i) : ((S.filter fun x ↦ x ∈ U i).card : ℝ) ≤ M := by
    apply (le_div_iff₀ (pow_pos rd 3)).mpr
    exact_mod_cast (show (S.filter fun x ↦ x ∈ U i).card * d^3 ≤ s*60^3 by
      calc
        _ ≤ (S.filter fun x ↦ x ∈ U i).card * (60^3*2^j) := Nat.mul_le_mul_left _ budget
        _ ≤ _ := by nlinarith only [Nat.mul_le_mul_right (60^3) (cap i)])
  let O := S.filter fun x ↦ eval x P ≠ 0
  let Z := S.filter fun x ↦ eval x P = 0
  have out := cellular_incidence_bound S F base dir k (C/(k:ℝ)^3) (C/k) M
    (by positivity) (by positivity) rich (fun T _ L hL ↦ st L (hL.trans hF) k hk T)
    U ho dis P cov cap'
  have out' : (O.card : ℝ) ≤ (s : ℝ)/2 := by
    apply out.trans
    apply le_trans _ (cell_fraction (d := (d : ℝ)) hC np kp (Nat.cast_nonneg m) (by exact_mod_cast (show 1 ≤ d from dp))
      (Nat.cast_nonneg s) (by exact_mod_cast mcap) (by exact_mod_cast lo)
      (by exact_mod_cast (show m ≤ 128*n*k*d by dsimp [b] at hi; nlinarith only [hi])) large.le)
    gcongr
  let W := F.filter (contained P)
  have wc : W.card ≤ d*(2*n) := by
    apply (card_le_card (filter_subset_filter _ hF)).trans
    exact (surface_line_cap P hP A).trans (Nat.mul_le_mul_right _ deg)
  have shrink : W.card*32 ≤ m := by
    have hk1 : 1 ≤ k := by omega
    have := Nat.mul_le_mul_right (64*n*d) hk1
    dsimp [b] at lo
    nlinarith only [Nat.mul_le_mul_right 32 wc,this,lo]
  have lt : W.card < F.card := by
    change W.card < m
    have hm := bp.trans_le bm
    omega
  let t := max 2 ((k+1)/2)
  have tk : t ≤ k := by dsimp [t]; omega
  have kt : k ≤ 2*t := by dsimp [t]; omega
  obtain ⟨G,hz,good⟩ := wall_split P F Z k hk (fun x hx ↦ rich x (mem_filter.mp hx).1)
    (fun x hx ↦ (mem_filter.mp hx).2)
  have ih := induction_rich bu hC A st W ((filter_subset ..).trans hF) t (le_max_left ..)
    (tk.trans hkn) G good
  have gbound : (G.card : ℝ)*(k : ℝ)^2 ≤ (s : ℝ)*k^2/8 := by
    have e : (k : ℝ)^2 ≤ (2*(t : ℝ))^2 := by gcongr; exact_mod_cast kt
    have w : (W.card : ℝ)*32 ≤ m := by exact_mod_cast shrink
    nlinarith only [mul_le_mul_of_nonneg_left e (Nat.cast_nonneg G.card),ih,
      mul_le_mul_of_nonneg_left w (show 0 ≤ 10^12*C*n by positivity),large.le]
  have dk : d*k ≤ n := by
    dsimp [b] at lo
    have := Nat.mul_le_mul_left (n*d*k) (by decide : 1 ≤ 64)
    have := Nat.le_of_mul_le_mul_left (c := n) (a := d*k) (b := n) (by nlinarith only [lo,mcap,this]) hn
    exact this
  have z' : Z.card*k ≤ G.card*k + 3*d*m := by
    apply hz.trans
    change _ ≤ G.card*k+3*d*F.card
    gcongr
  have zr : (Z.card : ℝ)*k^2 ≤ (G.card : ℝ)*k^2+3*(n : ℝ)*m := by
    exact_mod_cast (show Z.card*k^2 ≤ G.card*k^2+3*n*m by
      nlinarith only [Nat.mul_le_mul_right k z',Nat.mul_le_mul_right (3*m) dk])
  have sumN : Z.card+O.card = s := card_filter_add_card_filter_not ..
  have sumR : (Z.card : ℝ)+O.card = s := by exact_mod_cast sumN
  have baseN : (n : ℝ)*m ≤ C*n*m := by
    nlinarith only [mul_le_mul_of_nonneg_right hC (show 0 ≤ (n : ℝ)*m by positivity)]
  have ss : 0 < (s : ℝ)*(k : ℝ)^2 := lt_of_le_of_lt (by positivity) large
  nlinarith only [congrArg (fun x : ℝ ↦ x*k^2) sumR,gbound,zr,
    mul_le_mul_of_nonneg_right out' (sq_nonneg (k : ℝ)),large,baseN,ss]
termination_by F.card

/-- Specializing to Elekes–Sharir lines, Borsuk–Ulam and the planar
Szemerédi–Trotter bound suffice for the plane distinct-distances theorem.
The surface line cap applies at every step of the induction. -/
theorem solution_of_borsuk_ulam_and_planar_incidence (bu : ∀ m, OddZero m)
    (st : PlanarIncidenceBound) : type_of% @Erdos95.erdos_95.variants.guth_katz := by
  apply solution_of_incidence
  obtain ⟨C,hC,st⟩ := st
  refine ⟨10^12*C, by positivity, ?_⟩
  intro A k hk hkn B hb
  let vec (p : Space) : Coord := ![p.1,p.2.1,p.2.2]
  have rich : RichOn (B.image vec) (A ×ˢ A) k := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    apply (hb p hp).trans
    apply card_le_card
    intro q hq
    obtain ⟨hq,ht⟩ := mem_filter.mp hq
    apply mem_filter.mpr
    refine ⟨hq,p.1,?_⟩
    rw [param]
    exact congrArg vec ht.symm
  have h := induction_rich bu hC A (st A) (A ×ˢ A) (Subset.rfl) k hk hkn (B.image vec) rich
  have inj : Function.Injective vec := by
    intro p q e
    exact Prod.ext (congrFun e 0) (Prod.ext (congrFun e 1) (congrFun e 2))
  rw [card_image_iff.mpr inj.injOn,card_product,Nat.cast_mul] at h
  nlinarith only [h]

end OMA

namespace OMA
open Finset
open scoped Classical
private abbrev XY := ℝ × ℝ

/-- The planar rich-point theorem for ordinary graphs y=b+mx. -/
def SzemerediTrotter : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (L S : Finset (ℝ × ℝ)) (k : ℕ), 2 ≤ k →
    (∀ p ∈ S, k ≤ (L.filter fun l ↦ p.2 = l.1+p.1*l.2).card) →
    (S.card : ℝ) ≤ C/(k : ℝ)^3*(L.card : ℝ)^2 + C/k*L.card

private def projectXY (c : ℝ) (p : XY) : ℝ := p.1+c*p.2

private theorem generic_projection (T : Finset XY) :
    ∃ c : ℝ, Set.InjOn (projectXY c) T := by
  classical
  let bad := (T ×ˢ T).image fun z ↦ (z.2.1-z.1.1)/(z.1.2-z.2.2)
  obtain ⟨c,hc⟩ := Infinite.exists_notMem_finset bad
  refine ⟨c,?_⟩
  intro x hx y hy he
  change x.1+c*x.2 = y.1+c*y.2 at he
  by_cases h : x.2 = y.2
  · exact Prod.ext (by linarith [show c*x.2=c*y.2 by rw [h]]) h
  · exfalso
    apply hc
    apply mem_image.mpr
    refine ⟨(x,y),mem_product.mpr ⟨hx,hy⟩,?_⟩
    apply (div_eq_iff (sub_ne_zero.mpr h)).mpr
    linarith

theorem planar_incidence_of_szemeredi_trotter (st : SzemerediTrotter) : PlanarIncidenceBound := by
  classical
  obtain ⟨C,hC,st⟩ := st
  refine ⟨C,hC,?_⟩
  intro A F _ k hk S rich
  let xy (x : Coord) : XY := (x 1,x 2)
  let b (q : Pair) : XY := ((esLine q.1 q.2).x,(esLine q.1 q.2).y)
  let v (q : Pair) : XY := ((esLine q.1 q.2).u,(esLine q.1 q.2).v)
  let T := S.image xy ∪ F.image b ∪ F.image v
  obtain ⟨c,hc⟩ := generic_projection T
  let pt (x : Coord) : XY := (x 0,projectXY c (xy x))
  let line (q : Pair) : XY := (projectXY c (b q),projectXY c (v q))
  have pi' : Set.InjOn pt S := by
    intro x hx y hy he
    have hxy := hc (mem_union_left _ (mem_union_left _ (mem_image_of_mem xy hx)))
      (mem_union_left _ (mem_union_left _ (mem_image_of_mem xy hy))) (congrArg Prod.snd he)
    funext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  have li : Set.InjOn line F := by
    intro q hq r hr he
    have hb := hc (mem_union_left _ (mem_union_right _ (mem_image_of_mem b hq)))
      (mem_union_left _ (mem_union_right _ (mem_image_of_mem b hr))) (congrArg Prod.fst he)
    have hv := hc (mem_union_right _ (mem_image_of_mem v hq))
      (mem_union_right _ (mem_image_of_mem v hr)) (congrArg Prod.snd he)
    apply esLine_injective
    obtain ⟨hx,hy⟩ := Prod.mk.inj hb
    obtain ⟨hu,hw⟩ := Prod.mk.inj hv
    cases e : esLine q.1 q.2
    cases f : esLine r.1 r.2
    simp_all
  have h := st (F.image line) (S.image pt) k hk (by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    apply (rich x hx).trans
    apply card_le_card_of_injOn line
    · intro q hq
      obtain ⟨hq,t,ht⟩ := mem_filter.mp hq
      refine mem_filter.mpr ⟨mem_image_of_mem line hq,?_⟩
      rw [ht,param]
      dsimp [line,pt,xy,b,v,projectXY,ESLine.coords]
      ring
    · exact li.mono (filter_subset ..))
  simpa only [card_image_iff.mpr li,card_image_iff.mpr pi'] using h

theorem solution_of_borsuk_ulam_and_szemeredi_trotter (bu : ∀ m, OddZero m) (st : SzemerediTrotter) :
    type_of% @Erdos95.erdos_95.variants.guth_katz :=
  solution_of_borsuk_ulam_and_planar_incidence bu (planar_incidence_of_szemeredi_trotter st)
end OMA

namespace OMA
open Finset MvPolynomial
open scoped Classical
private abbrev Coord₂ := Fin 2 → ℝ

private def planePartitionDegree : ℕ → ℕ
  | 0 => 0
  | j+1 => planePartitionDegree j + 2*2^(j/2+1)

private theorem plane_partition (bu : ∀ m, OddZero m) (S : Finset Coord₂) (j : ℕ) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧ P.totalDegree ≤ 12*2^(j/2) ∧ SignPartition S j P := by
  have hd (i : ℕ) : planePartitionDegree i + 8 = 4*(2+i%2)*2^(i/2) := by
    induction i with
    | zero => decide
    | succ i ih =>
      rw [planePartitionDegree,pow_succ]
      by_cases hr : i%2 = 1
      · rw [show (i+1)%2 = 0 by omega,show (i+1)/2 = i/2+1 by omega,pow_succ]
        rw [hr] at ih
        omega
      · rw [show (i+1)%2 = 1 by omega,show (i+1)/2 = i/2 by omega]
        rw [show i%2 = 0 by omega] at ih
        omega
  suffices ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧ P.totalDegree ≤ planePartitionDegree j ∧ SignPartition S j P by
    obtain ⟨P,hp,hh,part⟩ := this
    refine ⟨P,hp,hh.trans ?_,part⟩
    nlinarith only [hd j,Nat.mul_le_mul_right (2^(j/2)) (show 4*(2+j%2) ≤ 12 by omega)]
  induction j with
  | zero =>
    exact ⟨1,one_ne_zero,by simp [planePartitionDegree],fun _ ↦ Set.univ,fun _ ↦ isOpen_univ,
      fun i k h ↦ False.elim (h (Subsingleton.elim (α := Fin 1) i k)),by simp,by simp⟩
  | succ j ih =>
    obtain ⟨P,hp,hh,part⟩ := ih
    have m : 2^j < (2^(j/2+1)+1)^2 := by
      apply lt_of_le_of_lt _ (Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by decide : 2 ≠ 0))
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    obtain ⟨Q,hq,hD,hnew⟩ := partition_step_dim part (bu _) m
    exact ⟨P*Q,mul_ne_zero hp hq,(totalDegree_mul ..).trans (Nat.add_le_add hh hD),hnew⟩

private def graphPoint (l : XY) (t : ℝ) : Coord₂ := ![t,l.1+t*l.2]
private def graphInc (p : Coord₂) (l : XY) : Prop := p 1 = l.1 + p 0*l.2
private theorem graph_repr {p : Coord₂} {l : XY} (h : graphInc p l) : p = graphPoint l (p 0) := by
  funext i; fin_cases i
  · rfl
  · exact h

/-- Ordered pairs on one side determine at most one member of the other.
This elementary bound is applied inside a cell and, with the roles reversed,
on the partition wall. -/
private theorem incidence_pair_bound {X Y : Type*} (S : Finset X) (L : Finset Y)
    (R : X → Y → Prop) (uniq : ∀ a b, a ∈ S → b ∈ S → a ≠ b → ∀ l ∈ L, ∀ m ∈ L,
      R a l → R b l → R a m → R b m → l = m) :
    ∑ a ∈ S, (L.filter (R a)).card ≤ L.card+S.card^2 := by
  classical
  let T (l : Y) := S.filter (fun x ↦ R x l)
  have total : ∑ a ∈ S, (L.filter (R a)).card = ∑ l ∈ L, (T l).card := by
    simp only [card_filter,T]
    rw [sum_comm]
  have pairs : ∑ l ∈ L, (T l).offDiag.card ≤ S.card^2 := by
    rw [← card_biUnion]
    · apply (card_le_card (t := S ×ˢ S) ?_).trans (by rw [card_product,pow_two])
      intro ab hab
      obtain ⟨l,_,hl⟩ := mem_biUnion.mp hab
      obtain ⟨ha,hb,_⟩ := mem_offDiag.mp hl
      exact mem_product.mpr ⟨(mem_filter.mp ha).1,(mem_filter.mp hb).1⟩
    · intro l hl m hm hne
      refine disjoint_left.mpr fun ab hab hab' ↦ ?_
      obtain ⟨ha,hb,hn⟩ := mem_offDiag.mp hab
      obtain ⟨ha',hb',_⟩ := mem_offDiag.mp hab'
      exact hne (uniq ab.1 ab.2 (mem_filter.mp ha).1 (mem_filter.mp hb).1 hn
        l hl m hm (mem_filter.mp ha).2 (mem_filter.mp hb).2 (mem_filter.mp ha').2 (mem_filter.mp hb').2)
  rw [total]
  calc
    _ ≤ ∑ l ∈ L, (1+(T l).offDiag.card) := by
      apply sum_le_sum
      intro l _
      rw [offDiag_card]
      generalize (T l).card = n
      rcases n with _ | n
      · simp
      · nlinarith [Nat.sub_add_cancel (show n+1 ≤ (n+1)*(n+1) by nlinarith)]
    _ ≤ _ := by simpa [sum_add_distrib] using Nat.add_le_add_left pairs L.card

private theorem graph_through_two {p q : Coord₂} {l m : XY} (hne : p ≠ q)
    (hp : graphInc p l) (hq : graphInc q l) (hp' : graphInc p m) (hq' : graphInc q m) : l = m := by
  have h : p 0 ≠ q 0 := by
    intro eq
    exact hne ((graph_repr hp).trans ((congrArg (graphPoint l) eq).trans (graph_repr hq).symm))
  unfold graphInc at *
  have z : (p 0-q 0)*(l.2-m.2) = 0 := by linarith
  have e := sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left (sub_ne_zero.mpr h))
  exact Prod.ext (by rw [e] at hp; linarith) e

private theorem two_graphs_meet_once {p q : Coord₂} {l m : XY} (hne : l ≠ m)
    (hp : graphInc p l) (hq : graphInc q l) (hp' : graphInc p m) (hq' : graphInc q m) : p = q :=
  Classical.byContradiction fun he ↦ hne (graph_through_two he hp hq hp' hq')
end OMA

namespace OMA
open Finset MvPolynomial
open scoped Classical
private abbrev RealPoly₂ := MvPolynomial (Fin 2) ℝ
private def planarWall (P : RealPoly₂) (l : XY) := ∀ t : ℝ, eval (graphPoint l t) P = 0

private theorem graph_alt (P : RealPoly₂) (l : XY) :
    planarWall P l ∨ ∀ T : Finset ℝ, (∀ t ∈ T, eval (graphPoint l t) P = 0) → T.card ≤ P.totalDegree := by
  have eq (t : ℝ) : (fun j ↦ ![(0 : ℝ),l.1] j + t*![1,l.2] j) = graphPoint l t := by
    funext i; fin_cases i <;> simp [graphPoint]
  simpa only [planarWall,eq] using line_wall_alternative P ![0,l.1] ![1,l.2]

private theorem plane_wall_cap (P : RealPoly₂) (hP : P ≠ 0) (L : Finset XY) :
    (L.filter (planarWall P)).card ≤ P.totalDegree := by
  classical
  obtain ⟨x,hx⟩ : ∃ x : Coord₂, eval x P ≠ 0 := by
    by_contra! h
    exact hP (MvPolynomial.funext fun x ↦ by simp [h])
  let R := {t : ℝ | eval (graphPoint (x 1,0) t) P = 0}
  have hfin : R.Finite := by
    obtain hall|h := graph_alt P (x 1,0)
    · have eq : graphPoint (x 1,0) (x 0) = x := by funext i; fin_cases i <;> simp [graphPoint]
      exact (hx (eq ▸ hall (x 0))).elim
    · by_contra hinf
      obtain ⟨T,hT,hc⟩ := Set.Infinite.exists_subset_card_eq hinf (P.totalDegree+1)
      have := h T (fun t ht ↦ hT ht)
      omega
  let bad := (L ×ˢ L).image (fun z ↦ (z.2.1-z.1.1)/(z.1.2-z.2.2))
  obtain ⟨t,ht⟩ := Infinite.exists_notMem_finset (bad ∪ hfin.toFinset)
  have ht' : t ∉ bad := fun h ↦ ht (mem_union_left _ h)
  have hx' : t ∉ R := fun h ↦ ht (mem_union_right _ (hfin.mem_toFinset.mpr h))
  let W := L.filter (planarWall P)
  let f (l : XY) := l.1+t*l.2
  have inj : Set.InjOn f W := by
    intro l hl m hm he
    change l.1+t*l.2=m.1+t*m.2 at he
    by_cases eq : l.2 = m.2
    · rw [eq] at he
      exact Prod.ext (by linarith) eq
    · exfalso
      apply ht'
      exact mem_image.mpr ⟨(l,m),mem_product.mpr ⟨(mem_filter.mp hl).1,(mem_filter.mp hm).1⟩,
        (div_eq_iff (sub_ne_zero.mpr eq)).mpr (by linarith)⟩
  change W.card ≤ _
  rw [← card_image_iff.mpr inj]
  have ev (y : ℝ) : (fun j ↦ ![t,(0 : ℝ)] j + y*![0,1] j) = ![t,y] := by
    funext i; fin_cases i <;> simp
  obtain hall|h := line_wall_alternative P ![t,0] ![0,1]
  · apply False.elim (hx' ?_)
    have he := hall (x 1)
    simpa only [R, Set.mem_ofPred_eq,graphPoint, mul_zero, add_zero,ev] using he
  · apply h
    intro y hy
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hy
    rw [ev]
    exact (mem_filter.mp hl).2 t

private theorem planar_wall_points (P : RealPoly₂) (hP : P ≠ 0)
    (Z : Finset Coord₂) (L : Finset XY) (k : ℕ)
    (hz : ∀ p ∈ Z, eval p P = 0) (hr : ∀ p ∈ Z, k ≤ (L.filter (graphInc p)).card) :
    k*Z.card ≤ Z.card + 2*P.totalDegree*L.card := by
  classical
  let W := L.filter (planarWall P)
  let V := L.filter (fun l ↦ ¬planarWall P l)
  have counts (p : Coord₂) : (L.filter (graphInc p)).card =
      (W.filter (graphInc p)).card + (V.filter (graphInc p)).card := by
    simpa [W,V,filter_filter,and_comm] using
      (card_filter_add_card_filter_not (s := L.filter (graphInc p)) (planarWall P)).symm
  have cw : ∑ p ∈ Z, (W.filter (graphInc p)).card ≤ Z.card+W.card^2 := by
    have := incidence_pair_bound W Z (fun l p ↦ graphInc p l) (fun l m _ _ h p _ q _ ↦
      fun h₁ h₂ h₃ h₄ ↦ two_graphs_meet_once h h₁ h₃ h₂ h₄)
    simpa only [card_filter,sum_comm (s := W) (t := Z)] using this
  have cv : ∑ p ∈ Z, (V.filter (graphInc p)).card ≤ V.card*P.totalDegree := by
    have swap : ∑ p ∈ Z, (V.filter (graphInc p)).card =
        ∑ l ∈ V, (Z.filter fun p ↦ graphInc p l).card := by simp_rw [card_filter]; rw [sum_comm]
    rw [swap]
    calc
      _ ≤ ∑ _ ∈ V, P.totalDegree := by
        apply sum_le_sum
        intro l hl
        let T := Z.filter fun p ↦ graphInc p l
        have inj : Set.InjOn (fun p : Coord₂ ↦ p 0) T := by
          intro p hp q hq he
          exact (graph_repr (mem_filter.mp hp).2).trans
            ((congrArg (graphPoint l) he).trans (graph_repr (mem_filter.mp hq).2).symm)
        change T.card ≤ _
        rw [← card_image_iff.mpr inj]
        apply (graph_alt P l).resolve_left (mem_filter.mp hl).2
        intro t ht
        obtain ⟨p,hp,rfl⟩ := mem_image.mp ht
        rw [← graph_repr (mem_filter.mp hp).2]
        exact hz p (mem_filter.mp hp).1
      _ = _ := by simp
  have ck : k*Z.card ≤ ∑ p ∈ Z, (L.filter (graphInc p)).card := by
    simpa [Nat.mul_comm] using sum_le_sum hr
  simp_rw [counts,sum_add_distrib] at ck
  have wD := plane_wall_cap P hP L
  change W.card ≤ _ at wD
  have wL : W.card ≤ L.card := card_filter_le .. 
  have vL : V.card ≤ L.card := card_filter_le ..
  nlinarith only [ck,cw,cv,Nat.mul_le_mul wD wL,Nat.mul_le_mul_right P.totalDegree vL]

private theorem plane_cellular_points (S : Finset Coord₂) (L : Finset XY) (k j : ℕ)
    (P : RealPoly₂) (part : SignPartition S j P)
    (hr : ∀ p ∈ S, k ≤ (L.filter (graphInc p)).card) (capK : 4*S.card ≤ k*2^j) :
    4*k*(S.filter fun p ↦ eval p P ≠ 0).card ≤ 4*L.card*(P.totalDegree+1)+k*S.card := by
  classical
  obtain ⟨U,ho,hd,hcov,hcap⟩ := part
  let T (i) := S.filter fun p ↦ p ∈ U i
  let F (i) := L.filter fun l ↦ ∃ t : ℝ, graphPoint l t ∈ U i
  have eq (l : XY) (t : ℝ) : (fun j ↦ ![(0:ℝ),l.1] j+t*![1,l.2] j) = graphPoint l t := by
    funext j; fin_cases j <;> simp [graphPoint]
  have budget : ∑ i, (F i).card ≤ L.card*(P.totalDegree+1) := by
    simpa only [eq,F] using total_line_region_count L U ho hd P hcov
      (fun l ↦ ![0,l.1]) (fun l ↦ ![1,l.2])
  have cell (i) : k*(T i).card ≤ (F i).card+(T i).card^2 := by
    apply le_trans _ (incidence_pair_bound (T i) (F i) graphInc (fun _ _ _ _ hn _ _ _ _ ↦
      graph_through_two hn))
    have deg (p) (hp : p ∈ T i) : k ≤ ((F i).filter (graphInc p)).card := by
      apply (hr p (mem_filter.mp hp).1).trans
      apply card_le_card
      intro l hl
      obtain ⟨hl,inc⟩ := mem_filter.mp hl
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hl,p 0,graph_repr inc ▸ (mem_filter.mp hp).2⟩,inc⟩
    simpa [Nat.mul_comm] using sum_le_sum deg
  have hc (i) : 4*(T i).card ≤ k := by
    apply Nat.le_of_mul_le_mul_left (c := 2^j) _ (by positivity)
    nlinarith only [Nat.mul_le_mul_left 4 (hcap i),capK]
  let O := S.filter fun p ↦ eval p P ≠ 0
  have cov : O = univ.biUnion T := by
    ext p
    simp only [O,T,mem_filter,hcov,mem_biUnion,mem_univ,true_and]
    grind
  have cnt : ∑ i, (T i).card = O.card := by
    rw [cov,card_biUnion]
    intro i _ j _ hij
    exact disjoint_left.mpr fun p hi hj ↦ Set.disjoint_left.mp (hd i j hij)
      (mem_filter.mp hi).2 (mem_filter.mp hj).2
  have bounds (i) : 4*k*(T i).card ≤ 4*(F i).card + k*(T i).card := by
    nlinarith only [Nat.mul_le_mul_left 4 (cell i),Nat.mul_le_mul_right (T i).card (hc i)]
  have total := sum_le_sum (s := univ) (fun i _ ↦ bounds i)
  simp only [sum_add_distrib, ← mul_sum,cnt] at total
  have sub : O.card ≤ S.card := card_filter_le ..
  change 4*k*O.card ≤ _
  nlinarith only [total,Nat.mul_le_mul_left 4 budget,Nat.mul_le_mul_left k sub]
end OMA

namespace OMA
open Finset MvPolynomial
open scoped Classical

private theorem planar_rich_bound (bu : ∀ m, OddZero m) (S : Finset Coord₂) (L : Finset XY)
    (k : ℕ) (hk : 2 ≤ k) (rich : ∀ p ∈ S, k ≤ (L.filter (graphInc p)).card) :
    (S.card : ℝ) ≤ 10^6/(k : ℝ)^3 * (L.card : ℝ)^2 + 10^6/k * L.card := by
  classical
  let s := S.card
  let m := L.card
  let a := 4*s/k+1
  let j := Nat.log 2 a + 1
  have kp : 0 < k := by omega
  have low : a < 2^j := Nat.lt_pow_succ_log_self (by decide) a
  have high : 2^j ≤ 2*a := by
    dsimp [j]
    rw [pow_succ]
    have ha : a ≠ 0 := Nat.succ_ne_zero _
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 ha)
  have jl : 4*s ≤ k*2^j := by
    have e := Nat.lt_mul_div_succ (4*s) kp
    exact e.le.trans (Nat.mul_le_mul_left k low.le)
  have jh : 2^j*k ≤ 8*s+2*k := by
    have e := Nat.div_mul_le_self (4*s) k
    dsimp [a] at high
    nlinarith only [Nat.mul_le_mul_right k high,e]
  obtain ⟨P,hP,deg,part⟩ := plane_partition bu S j
  let d := P.totalDegree
  let O := S.filter fun x ↦ eval x P ≠ 0
  let Z := S.filter fun x ↦ eval x P = 0
  have out := plane_cellular_points S L k j P part rich jl
  have wall := planar_wall_points P hP Z L k (fun x hx ↦ (mem_filter.mp hx).2)
    (fun x hx ↦ rich x (mem_filter.mp hx).1)
  have sum : Z.card + O.card = s := card_filter_add_card_filter_not ..
  change 4*k*O.card ≤ 4*m*(d+1)+k*s at out
  change k*Z.card ≤ Z.card+2*d*m at wall
  have inc : k*s ≤ 12*(d+1)*m := by
    nlinarith only [out,wall,congrArg (fun x ↦ k*x) sum,Nat.mul_le_mul_right s hk,
      sum,show 0 ≤ O.card by omega,show 0 ≤ m by omega]
  have d1 : d+1 ≤ 13*2^(j/2) := by
    change d ≤ _ at deg
    have one : 0 < 2^(j/2) := by positivity
    omega
  have dy : (2^(j/2))^2 ≤ 2^j := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have sq : (d+1)^2*k ≤ 169*(8*s+2*k) := by
    have x := Nat.pow_le_pow_left d1 2
    nlinarith only [Nat.mul_le_mul_right k x,Nat.mul_le_mul_right (169*k) dy,jh]
  have finalN : s^2*k^3 ≤ 24336*m^2*(8*s+2*k) := by
    have x := Nat.pow_le_pow_left inc 2
    nlinarith only [Nat.mul_le_mul_right k x,Nat.mul_le_mul_right (144*m^2) sq]
  change (s : ℝ) ≤ _
  have kr : (0 : ℝ) < k := by exact_mod_cast kp
  have f : (s : ℝ)^2*k^3 ≤ 24336*(m : ℝ)^2*(8*s+2*k) := by exact_mod_cast finalN
  by_cases hs : s = 0
  · rw [hs,Nat.cast_zero]; positivity
  have sp : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs
  by_cases h : k ≤ s
  · apply le_trans _ (le_add_of_nonneg_right (by positivity))
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos kr 3)]
    apply le_of_mul_le_mul_left (a := (s : ℝ)) _ sp
    have hr : (k : ℝ) ≤ s := by exact_mod_cast h
    nlinarith only [f,mul_le_mul_of_nonneg_right hr (show 0 ≤ 48672*(m : ℝ)^2 by positivity),
      show 0 ≤ (m : ℝ)^2*s by positivity]
  · apply le_trans _ (le_add_of_nonneg_left (by positivity))
    rw [div_mul_eq_mul_div, le_div_iff₀ kr]
    have hr : (s : ℝ) ≤ k := by exact_mod_cast (by omega : s ≤ k)
    have q : ((s : ℝ)*k)^2 ≤ (10^6*(m : ℝ))^2 := by
      apply le_of_mul_le_mul_right (a := (k : ℝ)) _ kr
      nlinarith only [f,mul_le_mul_of_nonneg_right hr (show 0 ≤ 194688*(m : ℝ)^2 by positivity),
        show 0 ≤ (m : ℝ)^2*k by positivity]
    exact le_of_sq_le_sq q (by positivity)

theorem szemeredi_trotter_of_borsuk_ulam (bu : ∀ m, OddZero m) : SzemerediTrotter := by
  classical
  refine ⟨10^6,by norm_num,?_⟩
  intro L S k hk rich
  let f (p : XY) : Coord₂ := ![p.1,p.2]
  have inj : Function.Injective f := fun _ _ h ↦ Prod.ext (congrFun h 0) (congrFun h 1)
  have h := planar_rich_bound bu (S.image f) L k hk (by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    exact rich p hp)
  simpa only [card_image_iff.mpr inj.injOn] using h

/-- For the concrete Elekes–Sharir family, polynomial partitioning in
dimensions two and three and the complex-slice surface cap give the
distinct-distance estimate from the odd-map zero theorem alone. -/
theorem solution_of_borsuk_ulam (bu : ∀ m, OddZero m) :
    type_of% @Erdos95.erdos_95.variants.guth_katz :=
  solution_of_borsuk_ulam_and_szemeredi_trotter bu (szemeredi_trotter_of_borsuk_ulam bu)

end OMA

/- Adapted for Lean 4.33.1 from Mario Ullrich, Lean-ContMeasurements, revision
 79a7bed5c4335dcef05ed8c2b5da0b7285e37c9c. Source modules GridSimplex, Tucker,
 and BorsukUlam (through borsukUlam_pi).
 https://github.com/mario-ullrich/Lean-ContMeasurements/tree/79a7bed5c4335dcef05ed8c2b5da0b7285e37c9c
 The Apache 2.0 license follows.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

section
/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/

/-
# Simplices of the Kuhn triangulation of an integer grid

The cube `[-N, N]ⁿ` carries a standard triangulation, due to Kuhn and Freudenthal, whose
vertices are the integer points and whose simplices are described purely by the order
relation: a set of integer points spans a simplex exactly when it is a **chain** for the
coordinatewise order and any two of its points differ by at most one in every coordinate.
This file sets up that description and the elementary facts a combinatorial argument on
the triangulation needs.

Two quantities are attached to a simplex `s`.  A label `(i, true)` is a **sign** of `s`
when some vertex has positive `i`-th coordinate, and `(i, false)` when some vertex has
negative `i`-th coordinate; the **directions** of `s` are the coordinates occurring in its
signs.  Since all vertices of a simplex differ by at most one in each coordinate, a
simplex never carries both signs in the same coordinate, so it has as many signs as
directions.

A simplex therefore has at most one more vertex than it has directions, and the
counting argument below runs over the ways of adding one vertex without adding a sign
outside a prescribed set of labels.  There are two, except at the boundary of the cube,
where one of them leaves the grid.

## Main results

* `IsSimplex.not_mem_signs_negLabel` — a simplex lies in one closed orthant: its signs
  contain no pair of opposite labels.
* `IsSimplex.card_le_card_directions_succ` — a simplex has at most one more vertex than it
  has directions.  This is what makes the counting argument finite.
* `card_extensions_eq_one` — with one more vertex than directions, a simplex extends in
  exactly one way when one further label is allowed.
* `extensions_eq_empty` — with one more vertex than directions, a simplex does not extend
  at all when no further label is allowed.
* `card_extensions_eq_two`, `card_extensions_eq_one_of_isExtremal` — with as many vertices
  as directions, a simplex extends in exactly two ways, or in one when a coordinate sits
  at the boundary of the cube.
* `IsSimplex.neg`, `mem_signs_neg` — reflection in the origin maps simplices to simplices
  and reverses every sign.
-/

open Finset
open scoped Pointwise

namespace GridSimplex

variable {n N : ℕ} {s : Finset (Fin n → ℤ)}

/- ### The grid -/

/-- The integer points of the cube `[-N, N]ⁿ`. -/
def grid (n N : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-- Membership in the grid, coordinatewise. -/
@[simp]
theorem mem_grid {v : Fin n → ℤ} :
    v ∈ grid n N ↔ ∀ i, -(N : ℤ) ≤ v i ∧ v i ≤ (N : ℤ) := by
  simp only [grid, Fintype.mem_piFinset, Finset.mem_Icc]

/-- The grid is symmetric under reflection in the origin. -/
theorem neg_mem_grid {v : Fin n → ℤ} (hv : v ∈ grid n N) : -v ∈ grid n N := by
  rw [mem_grid] at hv ⊢
  intro i
  have := hv i
  simp only [Pi.neg_apply]
  omega

/-- The origin belongs to the grid. -/
theorem zero_mem_grid : (0 : Fin n → ℤ) ∈ grid n N := by simp

/-- A grid point lies on the boundary of the cube when one of its coordinates is
extremal. -/
def IsBoundary (N : ℕ) (v : Fin n → ℤ) : Prop := ∃ i, v i = (N : ℤ) ∨ v i = -(N : ℤ)

/-- Reflection preserves the boundary. -/
theorem isBoundary_neg {v : Fin n → ℤ} (hv : IsBoundary N v) : IsBoundary N (-v) := by
  obtain ⟨i, hi⟩ := hv
  refine ⟨i, ?_⟩
  simp only [Pi.neg_apply]
  omega

/- ### Labels -/

/-- A coordinate together with a sign: `true` stands for `+`, `false` for `−`. -/
abbrev Label (n : ℕ) := Fin n × Bool

/-- The opposite label. -/
def negLabel (p : Label n) : Label n := (p.1, !p.2)

/-- Reversing a label twice does nothing. -/
@[simp]
theorem negLabel_negLabel (p : Label n) : negLabel (negLabel p) = p := by
  simp [negLabel]

/-- Reversing a label keeps its coordinate. -/
@[simp]
theorem negLabel_fst (p : Label n) : (negLabel p).1 = p.1 := rfl

/-- `negLabel` has no fixed point. -/
theorem negLabel_ne (p : Label n) : negLabel p ≠ p := by
  simp [negLabel, Prod.ext_iff]

/-- Membership in a set of labels closed under nothing: reflecting the label instead of the
set. -/
theorem mem_image_negLabel {t : Finset (Label n)} {p : Label n} :
    p ∈ t.image negLabel ↔ negLabel p ∈ t := by
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
    rwa [negLabel_negLabel]
  · intro h
    exact Finset.mem_image.2 ⟨negLabel p, h, negLabel_negLabel p⟩

/- ### Simplices -/

/-- A simplex of the Kuhn triangulation of the grid: a nonempty set of grid points that is
a chain for the coordinatewise order and whose points differ by at most one in every
coordinate.

These are exactly the faces of the triangulation; a top-dimensional one is a chain
`v < v + e_{i₁} < v + e_{i₁} + e_{i₂} < …`. -/
structure IsSimplex (N : ℕ) (s : Finset (Fin n → ℤ)) : Prop where
  /-- A simplex has a vertex. -/
  nonempty : s.Nonempty
  /-- Its vertices are grid points. -/
  subset_grid : s ⊆ grid n N
  /-- Its vertices are comparable. -/
  chain : IsChain (· ≤ ·) (s : Set (Fin n → ℤ))
  /-- Its vertices differ by at most one in every coordinate. -/
  sub_le_one : ∀ x ∈ s, ∀ y ∈ s, ∀ i, y i - x i ≤ 1

/-- A simplex lies in one closed orthant: no coordinate is positive at one vertex and
negative at another. -/
theorem IsSimplex.not_lt_zero_of_pos (hs : IsSimplex N s) {x y : Fin n → ℤ} (hx : x ∈ s)
    (hy : y ∈ s) {i : Fin n} (hxi : 0 < x i) : ¬ y i < 0 := by
  intro hyi
  have h := hs.sub_le_one y hy x hx i
  omega

/-- A nonempty subset of a simplex is a simplex. -/
theorem IsSimplex.subset {t : Finset (Fin n → ℤ)} (hs : IsSimplex N s) (hts : t ⊆ s)
    (ht : t.Nonempty) : IsSimplex N t where
  nonempty := ht
  subset_grid := hts.trans hs.subset_grid
  chain := hs.chain.mono (by exact_mod_cast hts)
  sub_le_one x hx y hy i := hs.sub_le_one x (hts hx) y (hts hy) i

/-- A single grid point is a simplex. -/
theorem isSimplex_singleton {v : Fin n → ℤ} (hv : v ∈ grid n N) :
    IsSimplex N ({v} : Finset (Fin n → ℤ)) where
  nonempty := Finset.singleton_nonempty v
  subset_grid := Finset.singleton_subset_iff.2 hv
  chain := by
    rintro x hx y hy hne
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    exact absurd (hx.trans hy.symm) hne
  sub_le_one := by
    intro x hx y hy i
    rw [Finset.mem_singleton] at hx hy
    subst hx
    subst hy
    omega


/- ### Signs and directions -/

/-- The signs of `s`: the label `(i, true)` occurs when some vertex has positive `i`-th
coordinate, and `(i, false)` when some vertex has negative `i`-th coordinate. -/
def signs (s : Finset (Fin n → ℤ)) : Finset (Label n) :=
  Finset.univ.filter fun p => ∃ x ∈ s, if p.2 then 0 < x p.1 else x p.1 < 0

/-- The positive sign in a coordinate occurs when some vertex is positive there. -/
@[simp]
theorem mem_signs_true {i : Fin n} : (i, true) ∈ signs s ↔ ∃ x ∈ s, 0 < x i := by
  simp [signs]

/-- The negative sign in a coordinate occurs when some vertex is negative there. -/
@[simp]
theorem mem_signs_false {i : Fin n} : (i, false) ∈ signs s ↔ ∃ x ∈ s, x i < 0 := by
  simp [signs]

/-- The directions of `s`: the coordinates occurring in its signs. -/
def directions (s : Finset (Fin n → ℤ)) : Finset (Fin n) := (signs s).image Prod.fst

/-- A coordinate is a direction exactly when some vertex is nonzero there. -/
@[simp]
theorem mem_directions {i : Fin n} : i ∈ directions s ↔ ∃ x ∈ s, x i ≠ 0 := by
  constructor
  · intro hi
    obtain ⟨p, hp, hpi⟩ := Finset.mem_image.1 hi
    obtain ⟨j, b⟩ := p
    simp only at hpi
    subst hpi
    cases b
    · obtain ⟨x, hx, hxj⟩ := mem_signs_false.1 hp
      exact ⟨x, hx, by omega⟩
    · obtain ⟨x, hx, hxj⟩ := mem_signs_true.1 hp
      exact ⟨x, hx, by omega⟩
  · rintro ⟨x, hx, hxi⟩
    rcases lt_or_gt_of_ne hxi with h | h
    · exact Finset.mem_image.2 ⟨(i, false), mem_signs_false.2 ⟨x, hx, h⟩, rfl⟩
    · exact Finset.mem_image.2 ⟨(i, true), mem_signs_true.2 ⟨x, hx, h⟩, rfl⟩

/-- Signs of a subset are signs. -/
theorem signs_subset {t : Finset (Fin n → ℤ)} (hts : t ⊆ s) : signs t ⊆ signs s := by
  rintro ⟨i, b⟩ hp
  cases b
  · obtain ⟨x, hx, hxi⟩ := mem_signs_false.1 hp
    exact mem_signs_false.2 ⟨x, hts hx, hxi⟩
  · obtain ⟨x, hx, hxi⟩ := mem_signs_true.1 hp
    exact mem_signs_true.2 ⟨x, hts hx, hxi⟩

/-- Directions of a subset are directions. -/
theorem directions_subset {t : Finset (Fin n → ℤ)} (hts : t ⊆ s) :
    directions t ⊆ directions s :=
  Finset.image_subset_image (signs_subset hts)

/-- A simplex lies in one closed orthant: its signs contain no pair of opposite labels. -/
theorem IsSimplex.not_mem_signs_negLabel (hs : IsSimplex N s) {p : Label n}
    (hp : p ∈ signs s) : negLabel p ∉ signs s := by
  obtain ⟨i, b⟩ := p
  cases b
  · intro hq
    obtain ⟨x, hx, hxi⟩ := mem_signs_false.1 hp
    obtain ⟨y, hy, hyi⟩ := mem_signs_true.1 hq
    exact hs.not_lt_zero_of_pos hy hx hyi hxi
  · intro hq
    obtain ⟨x, hx, hxi⟩ := mem_signs_true.1 hp
    obtain ⟨y, hy, hyi⟩ := mem_signs_false.1 hq
    exact hs.not_lt_zero_of_pos hx hy hxi hyi

/-- On the signs of a simplex the coordinate determines the label, so a simplex has as many
signs as directions. -/
theorem IsSimplex.card_signs (hs : IsSimplex N s) :
    (signs s).card = (directions s).card := by
  refine (Finset.card_image_of_injOn ?_).symm
  rintro ⟨i, b⟩ hp ⟨j, c⟩ hq hij
  simp only at hij
  subst hij
  cases b <;> cases c
  · rfl
  · exact absurd hq (hs.not_mem_signs_negLabel hp)
  · exact absurd hq (hs.not_mem_signs_negLabel hp)
  · rfl

/-- The origin alone carries no sign. -/
@[simp]
theorem signs_singleton_zero : signs ({0} : Finset (Fin n → ℤ)) = ∅ := by
  ext p
  obtain ⟨i, c⟩ := p
  cases c
  · simp [mem_signs_false]
  · simp [mem_signs_true]

/-- The origin alone has no direction. -/
@[simp]
theorem directions_singleton_zero : directions ({0} : Finset (Fin n → ℤ)) = ∅ := by
  rw [directions, signs_singleton_zero, Finset.image_empty]

/-- A simplex with no direction and a single vertex is the origin alone. -/
theorem eq_singleton_zero (hs : IsSimplex N s) (h1 : s.card = 1)
    (hd : (directions s).card = 0) : s = {0} := by
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h1
  have hzero : ∀ i, x i = 0 := by
    intro i
    by_contra hcon
    have hmem : i ∈ directions ({x} : Finset (Fin n → ℤ)) :=
      mem_directions.2 ⟨x, Finset.mem_singleton_self x, hcon⟩
    rw [Finset.card_eq_zero.1 hd] at hmem
    exact absurd hmem (Finset.notMem_empty i)
  have : x = 0 := by
    ext i
    exact hzero i
  rw [this]


/- ### The least vertex -/

/-- A nonempty finite chain of integer vectors has a least element: the one of smallest
coordinate sum. -/
theorem exists_isLeast_of_isChain {t : Finset (Fin n → ℤ)} (ht : t.Nonempty)
    (hc : IsChain (· ≤ ·) (t : Set (Fin n → ℤ))) : ∃ a ∈ t, ∀ x ∈ t, a ≤ x := by
  obtain ⟨a, ha, hmin⟩ := t.exists_min_image (fun x => ∑ i, x i) ht
  refine ⟨a, ha, fun x hx => ?_⟩
  rcases eq_or_ne a x with rfl | hne
  · exact le_rfl
  · rcases hc ha hx hne with h | h
    · exact h
    · exfalso
      obtain ⟨j, hj⟩ := Function.ne_iff.1 (Ne.symm hne)
      have hlt : ∑ i, x i < ∑ i, a i :=
        Finset.sum_lt_sum (fun i _ => h i) ⟨j, Finset.mem_univ j, lt_of_le_of_ne (h j) hj⟩
      exact absurd (hmin x hx) (not_le.2 hlt)

/-- A nonempty finite chain of integer vectors has a greatest element. -/
theorem exists_isGreatest_of_isChain {t : Finset (Fin n → ℤ)} (ht : t.Nonempty)
    (hc : IsChain (· ≤ ·) (t : Set (Fin n → ℤ))) : ∃ b ∈ t, ∀ x ∈ t, x ≤ b := by
  obtain ⟨b, hb, hmax⟩ := t.exists_max_image (fun x => ∑ i, x i) ht
  refine ⟨b, hb, fun x hx => ?_⟩
  rcases eq_or_ne b x with rfl | hne
  · exact le_rfl
  · rcases hc hb hx hne with h | h
    · exfalso
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
      have hlt : ∑ i, b i < ∑ i, x i :=
        Finset.sum_lt_sum (fun i _ => h i) ⟨j, Finset.mem_univ j, lt_of_le_of_ne (h j) hj⟩
      exact absurd (hmax x hx) (not_le.2 hlt)
    · exact h

/-- A simplex has a least vertex. -/
theorem IsSimplex.exists_bot (hs : IsSimplex N s) : ∃ a ∈ s, ∀ x ∈ s, a ≤ x :=
  exists_isLeast_of_isChain hs.nonempty hs.chain

/-- A simplex has a greatest vertex. -/
theorem IsSimplex.exists_top (hs : IsSimplex N s) : ∃ b ∈ s, ∀ x ∈ s, x ≤ b :=
  exists_isGreatest_of_isChain hs.nonempty hs.chain

/-- The grid is an order interval: a point between two grid points is a grid point. -/
theorem mem_grid_of_le_of_le {u w v : Fin n → ℤ} (hu : u ∈ grid n N) (hv : v ∈ grid n N)
    (huw : u ≤ w) (hwv : w ≤ v) : w ∈ grid n N := by
  rw [mem_grid] at hu hv ⊢
  intro i
  have h1 := hu i
  have h2 := hv i
  have h3 : u i ≤ w i := Pi.le_def.1 huw i
  have h4 : w i ≤ v i := Pi.le_def.1 hwv i
  omega

/-- Measured from the least vertex, every coordinate of every vertex is either the base
value or one more. -/
theorem IsSimplex.eq_or_eq_add_one (hs : IsSimplex N s) {a x : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ y ∈ s, a ≤ y) (hx : x ∈ s) (i : Fin n) : x i = a i ∨ x i = a i + 1 := by
  have h1 : a i ≤ x i := hbot x hx i
  have h2 : x i - a i ≤ 1 := hs.sub_le_one a ha x hx i
  omega

/-- The coordinates in which `x` exceeds the base point `a`. -/
def step (a x : Fin n → ℤ) : Finset (Fin n) := Finset.univ.filter fun i => a i < x i

/-- Membership in the step set, unfolded. -/
@[simp]
theorem mem_step {a x : Fin n → ℤ} {i : Fin n} : i ∈ step a x ↔ a i < x i := by
  simp [step]

/-- Along the chain the step set can only grow. -/
theorem step_subset_step {a x y : Fin n → ℤ} (hxy : x ≤ y) : step a x ⊆ step a y := by
  intro i hi
  rw [mem_step] at hi ⊢
  exact lt_of_lt_of_le hi (hxy i)

/-- Lowering the base point can only enlarge the step set. -/
theorem step_subset_step_base {a w x : Fin n → ℤ} (hwa : w ≤ a) : step a x ⊆ step w x := by
  intro i hi
  rw [mem_step] at hi ⊢
  exact lt_of_le_of_lt (Pi.le_def.1 hwa i) hi

/-- Strictly along the chain the step set grows strictly: a coordinate where `x` and `y`
differ is at its base value in `x`. -/
theorem IsSimplex.step_ssubset (hs : IsSimplex N s) {a x y : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) (hne : x ≠ y) :
    step a x ⊂ step a y := by
  refine ⟨step_subset_step hxy, fun hsub => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.1 hne
  have hlt : x j < y j := lt_of_le_of_ne (hxy j) hj
  have hax : a j ≤ x j := hbot x hx j
  have hxj : x j = a j := by
    rcases hs.eq_or_eq_add_one ha hbot hy j with h | h <;> omega
  have h1 : j ∉ step a x := by simp [hxj]
  have h2 : j ∈ step a y := by rw [mem_step, ← hxj]; exact hlt
  exact h1 (hsub h2)

/-- Every step set consists of directions: a coordinate that grows along the simplex is
nonzero at one of its ends. -/
theorem step_subset_directions {a x : Fin n → ℤ} (ha : a ∈ s) (hx : x ∈ s) :
    step a x ⊆ directions s := by
  intro i hi
  rw [mem_step] at hi
  rw [mem_directions]
  rcases lt_trichotomy (a i) 0 with h | h | h
  · exact ⟨a, ha, by omega⟩
  · exact ⟨x, hx, by omega⟩
  · exact ⟨a, ha, by omega⟩

/-- Every vertex is the least vertex raised by one in the coordinates of its step set. -/
theorem IsSimplex.eq_add_ite (hs : IsSimplex N s) {a x : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ y ∈ s, a ≤ y) (hx : x ∈ s) (j : Fin n) :
    x j = a j + (if j ∈ step a x then 1 else 0) := by
  rcases hs.eq_or_eq_add_one ha hbot hx j with h | h
  · rw [if_neg (by simp [h]), h, add_zero]
  · rw [if_pos (by simp [h]), h]

/- ### Ranks -/

/-- The rank of a vertex relative to a base point: the number of coordinates in which it is
larger.  Measured from the least vertex of a simplex, the rank increases strictly along
that simplex, so it numbers the vertices. -/
def rank (a x : Fin n → ℤ) : ℕ := (step a x).card

/-- The rank increases strictly along a simplex. -/
theorem IsSimplex.rank_lt_rank (hs : IsSimplex N s) {a x y : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
    rank a x < rank a y :=
  Finset.card_lt_card (hs.step_ssubset ha hbot hx hy hxy.le hxy.ne)

/-- The rank is injective on a simplex. -/
theorem IsSimplex.injOn_rank (hs : IsSimplex N s) {a : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) : Set.InjOn (rank a) s := by
  intro x hx y hy hxy
  by_contra hne
  rcases hs.chain hx hy hne with h | h
  · exact absurd hxy (hs.rank_lt_rank ha hbot hx hy (lt_of_le_of_ne h hne)).ne
  · exact absurd hxy.symm
      (hs.rank_lt_rank ha hbot hy hx (lt_of_le_of_ne h (Ne.symm hne))).ne

/-- The rank reflects the order: a vertex of smaller rank is smaller. -/
theorem IsSimplex.lt_of_rank_lt (hs : IsSimplex N s) {a x y : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hx : x ∈ s) (hy : y ∈ s) (h : rank a x < rank a y) :
    x < y := by
  rcases eq_or_ne x y with rfl | hne
  · exact absurd h (lt_irrefl _)
  rcases hs.chain hx hy hne with hle | hle
  · exact lt_of_le_of_ne hle hne
  · exact absurd (hs.rank_lt_rank ha hbot hy hx (lt_of_le_of_ne hle (Ne.symm hne)))
      (by omega)

/-- **A simplex has at most one more vertex than its total step set has coordinates.**

The rank is injective on the simplex and takes values between `0` and the number of
coordinates in which the greatest vertex exceeds the least one. -/
theorem IsSimplex.card_le_card_step_succ (hs : IsSimplex N s) {a b : Fin n → ℤ}
    (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b) :
    s.card ≤ (step a b).card + 1 := by
  have himg : s.image (rank a) ⊆ Finset.range ((step a b).card + 1) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2
      (Nat.lt_succ_of_le (Finset.card_le_card (step_subset_step (htop x hx))))
  calc s.card = (s.image (rank a)).card :=
        (Finset.card_image_of_injOn (hs.injOn_rank ha hbot)).symm
    _ ≤ (Finset.range ((step a b).card + 1)).card := Finset.card_le_card himg
    _ = (step a b).card + 1 := Finset.card_range _

/-- **A simplex has at most one more vertex than it has directions.**

Every coordinate in which the greatest vertex exceeds the least one is a direction. -/
theorem IsSimplex.card_le_card_directions_succ (hs : IsSimplex N s) :
    s.card ≤ (directions s).card + 1 := by
  obtain ⟨a, ha, hbot⟩ := hs.exists_bot
  obtain ⟨b, hb, htop⟩ := hs.exists_top
  exact (hs.card_le_card_step_succ ha hbot htop).trans
    (Nat.succ_le_succ (Finset.card_le_card (step_subset_directions ha hb)))

/- ### Saturated simplices

A simplex with one more vertex than its total step set has coordinates is as long as it
can be: its ranks then run through every value from `0` upwards, so consecutive vertices
differ by a single unit step.  This is what pins down the ways of extending it by one
vertex. -/

/-- A simplex with one more vertex than it has directions is saturated: every direction is
already a coordinate in which the greatest vertex exceeds the least one. -/
theorem IsSimplex.card_eq_card_step_succ (hs : IsSimplex N s) {a b : Fin n → ℤ}
    (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (hb : b ∈ s) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (directions s).card + 1) : s.card = (step a b).card + 1 := by
  have h1 := hs.card_le_card_step_succ ha hbot htop
  have h2 : (step a b).card ≤ (directions s).card :=
    Finset.card_le_card (step_subset_directions ha hb)
  omega

/-- A saturated simplex realises every rank up to the size of its total step set. -/
theorem IsSimplex.image_rank (hs : IsSimplex N s) {a b : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (step a b).card + 1) :
    s.image (rank a) = Finset.range ((step a b).card + 1) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2
      (Nat.lt_succ_of_le (Finset.card_le_card (step_subset_step (htop x hx))))
  · rw [Finset.card_range, Finset.card_image_of_injOn (hs.injOn_rank ha hbot), hcard]

/-- Hence every rank below the size of the total step set occurs at a vertex. -/
theorem IsSimplex.exists_rank_eq (hs : IsSimplex N s) {a b : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (step a b).card + 1) {r : ℕ} (hr : r ≤ (step a b).card) :
    ∃ z ∈ s, rank a z = r := by
  have hmem : r ∈ s.image (rank a) := by
    rw [hs.image_rank ha hbot htop hcard]
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hr)
  obtain ⟨z, hz, hzr⟩ := Finset.mem_image.1 hmem
  exact ⟨z, hz, hzr⟩

/-- In a saturated simplex, consecutive vertices have consecutive ranks. -/
theorem IsSimplex.rank_eq_succ (hs : IsSimplex N s) {a b x y : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (step a b).card + 1) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) : rank a y = rank a x + 1 := by
  have hlt : rank a x < rank a y := hs.rank_lt_rank ha hbot hx hy hxy
  by_contra hne
  have hle : rank a x + 1 ≤ (step a b).card := by
    have hy' : rank a y ≤ (step a b).card :=
      Finset.card_le_card (step_subset_step (htop y hy))
    omega
  obtain ⟨z, hz, hzr⟩ := hs.exists_rank_eq ha hbot htop hcard hle
  exact hcons z hz ⟨hs.lt_of_rank_lt ha hbot hx hz (by omega),
    hs.lt_of_rank_lt ha hbot hz hy (by omega)⟩

/-- In a saturated simplex, the step set of the successor of a vertex adds exactly one
coordinate. -/
theorem IsSimplex.exists_step_eq_insert (hs : IsSimplex N s) {a b x y : Fin n → ℤ}
    (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (step a b).card + 1) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) :
    ∃ i ∉ step a x, step a y = insert i (step a x) := by
  have hsub : step a x ⊆ step a y := step_subset_step hxy.le
  have hcards : (step a x).card + 1 = (step a y).card :=
    (hs.rank_eq_succ ha hbot htop hcard hx hy hxy hcons).symm
  obtain ⟨i, hi, hins⟩ := Finset.exists_eq_insert_iff.2 ⟨hsub, hcards⟩
  exact ⟨i, hi, hins.symm⟩

/-- **Consecutive vertices of a saturated simplex differ by one unit step.** -/
theorem IsSimplex.exists_eq_add_single (hs : IsSimplex N s) {a b x y : Fin n → ℤ}
    (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (step a b).card + 1) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) :
    ∃ i, x i + 1 = y i ∧ ∀ j, j ≠ i → x j = y j := by
  obtain ⟨i, hi, hstep⟩ := hs.exists_step_eq_insert ha hbot htop hcard hx hy hxy hcons
  refine ⟨i, ?_, ?_⟩
  · rw [hs.eq_add_ite ha hbot hx i, hs.eq_add_ite ha hbot hy i, hstep]
    simp [hi]
  · intro j hj
    rw [hs.eq_add_ite ha hbot hx j, hs.eq_add_ite ha hbot hy j, hstep]
    simp [Finset.mem_insert, hj]

/- ### Extending a simplex by one vertex

A vertex added to a simplex sits below all of it, above all of it, or strictly between two
consecutive vertices.  In each position the added vertex is adjacent in the chain to a
vertex of the original simplex, so in a saturated simplex it differs from that vertex by a
single unit step. -/

/-- Inserting a vertex that is comparable with every vertex of a simplex and differs from
each by at most one in every coordinate again gives a simplex. -/
theorem IsSimplex.insert_vertex (hs : IsSimplex N s) {w : Fin n → ℤ} (hw : w ∈ grid n N)
    (hcomp : ∀ z ∈ s, w ≤ z ∨ z ≤ w)
    (hspan : ∀ z ∈ s, ∀ i, z i - w i ≤ 1 ∧ w i - z i ≤ 1) :
    IsSimplex N (insert w s) where
  nonempty := Finset.insert_nonempty _ _
  subset_grid := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hxs
    · exact hw
    · exact hs.subset_grid hxs
  chain := by
    rintro x hx y hy hne
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rcases hx with rfl | hxs
    · rcases hy with rfl | hys
      · exact absurd rfl hne
      · exact hcomp y hys
    · rcases hy with rfl | hys
      · exact (hcomp x hxs).symm
      · exact hs.chain hxs hys hne
  sub_le_one := by
    intro x hx y hy i
    rcases Finset.mem_insert.1 hx with rfl | hxs
    · rcases Finset.mem_insert.1 hy with rfl | hys
      · omega
      · exact (hspan y hys i).1
    · rcases Finset.mem_insert.1 hy with rfl | hys
      · exact (hspan x hxs i).2
      · exact hs.sub_le_one x hxs y hys i

/-- A new vertex that is neither below some vertex nor above another lies strictly between
two consecutive vertices.  Applied to the least and the greatest vertex, this is the
trichotomy for the position of a new vertex in the chain. -/
theorem exists_between_of_insert {w a b : Fin n → ℤ}
    (hchain : IsChain (· ≤ ·) ((insert w s : Finset (Fin n → ℤ)) : Set (Fin n → ℤ)))
    (hws : w ∉ s) (ha : a ∈ s) (hb : b ∈ s) (h1 : ¬ w < a) (h2 : ¬ b < w) :
    ∃ x ∈ s, ∃ y ∈ s, x < w ∧ w < y ∧ ∀ z ∈ s, ¬(x < z ∧ z < y) := by
  classical
  have hsub : (s : Set (Fin n → ℤ)) ⊆ ((insert w s : Finset (Fin n → ℤ)) : Set _) := by
    intro z hz
    exact_mod_cast Finset.mem_insert_of_mem (by exact_mod_cast hz)
  have hchain' : IsChain (· ≤ ·) (s : Set (Fin n → ℤ)) := hchain.mono hsub
  have hmemw : w ∈ (insert w s : Finset (Fin n → ℤ)) := Finset.mem_insert_self _ _
  have hcomp : ∀ z ∈ s, z < w ∨ w < z := by
    intro z hz
    have hzw : z ≠ w := fun h => hws (h ▸ hz)
    rcases hchain (hsub (by exact_mod_cast hz)) (by exact_mod_cast hmemw) hzw with h | h
    · exact Or.inl (lt_of_le_of_ne h hzw)
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hzw))
  -- `w` is above the least vertex and below the greatest one.
  have haw : a < w := by
    rcases hcomp a ha with h | h
    · exact h
    · exact absurd h h1
  have hwb : w < b := by
    rcases hcomp b hb with h | h
    · exact absurd h h2
    · exact h
  -- The largest vertex below `w` and the smallest one above it.
  set L : Finset (Fin n → ℤ) := s.filter (fun z => z < w) with hL
  set R : Finset (Fin n → ℤ) := s.filter (fun z => w < z) with hR
  have hLs : L ⊆ s := Finset.filter_subset _ _
  have hRs : R ⊆ s := Finset.filter_subset _ _
  have hLne : L.Nonempty := ⟨a, Finset.mem_filter.2 ⟨ha, haw⟩⟩
  have hRne : R.Nonempty := ⟨b, Finset.mem_filter.2 ⟨hb, hwb⟩⟩
  obtain ⟨x, hxL, hxmax⟩ :=
    exists_isGreatest_of_isChain hLne (hchain'.mono (by exact_mod_cast hLs))
  obtain ⟨y, hyR, hymin⟩ :=
    exists_isLeast_of_isChain hRne (hchain'.mono (by exact_mod_cast hRs))
  obtain ⟨hxs, hxw⟩ := Finset.mem_filter.1 hxL
  obtain ⟨hys, hwy⟩ := Finset.mem_filter.1 hyR
  refine ⟨x, hxs, y, hys, hxw, hwy, ?_⟩
  rintro z hz ⟨hxz, hzy⟩
  rcases hcomp z hz with h | h
  · exact absurd (lt_of_lt_of_le hxz (hxmax z (Finset.mem_filter.2 ⟨hz, h⟩))) (lt_irrefl x)
  · exact absurd (lt_of_lt_of_le hzy (hymin z (Finset.mem_filter.2 ⟨hz, h⟩))) (lt_irrefl z)

/-- A vertex above the whole simplex is one unit step above its greatest vertex. -/
theorem IsSimplex.exists_eq_top_add_single {w a b : Fin n → ℤ}
    (ht : IsSimplex N (insert w s)) (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z) (hb : b ∈ s)
    (htop : ∀ z ∈ s, z ≤ b) (hbw : b < w)
    (hcard : (insert w s).card = (step a w).card + 1) :
    ∃ i, b i + 1 = w i ∧ ∀ j, j ≠ i → b j = w j := by
  have hbot' : ∀ z ∈ insert w s, a ≤ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_trans (hbot b hb) hbw.le
    · exact hbot z hzs
  have htop' : ∀ z ∈ insert w s, z ≤ w := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_rfl
    · exact le_trans (htop z hzs) hbw.le
  refine ht.exists_eq_add_single (Finset.mem_insert_of_mem ha) hbot' htop' hcard
    (Finset.mem_insert_of_mem hb) (Finset.mem_insert_self _ _) hbw ?_
  rintro z hz ⟨hbz, hzw⟩
  rcases Finset.mem_insert.1 hz with rfl | hzs
  · exact absurd hzw (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le hbz (htop z hzs)) (lt_irrefl b)

/-- A vertex below the whole simplex is one unit step below its least vertex. -/
theorem IsSimplex.exists_eq_add_single_bot {w a b : Fin n → ℤ}
    (ht : IsSimplex N (insert w s)) (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z)
    (htop : ∀ z ∈ s, z ≤ b) (hwa : w < a)
    (hcard : (insert w s).card = (step w b).card + 1) :
    ∃ i, w i + 1 = a i ∧ ∀ j, j ≠ i → w j = a j := by
  have hbot' : ∀ z ∈ insert w s, w ≤ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_rfl
    · exact le_of_lt (lt_of_lt_of_le hwa (hbot z hzs))
  have htop' : ∀ z ∈ insert w s, z ≤ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_trans hwa.le (htop a ha)
    · exact htop z hzs
  refine ht.exists_eq_add_single (Finset.mem_insert_self _ _) hbot' htop' hcard
    (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem ha) hwa ?_
  rintro z hz ⟨hwz, hza⟩
  rcases Finset.mem_insert.1 hz with rfl | hzs
  · exact absurd hwz (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le hza (hbot z hzs)) (lt_irrefl z)

/-- A vertex added below a simplex lowers a coordinate that is constant on it. -/
theorem IsSimplex.const_of_insert_bot {w a : Fin n → ℤ} {p : Fin n}
    (ht : IsSimplex N (insert w s)) (hbot : ∀ z ∈ s, a ≤ z)
    (hwp : w p + 1 = a p) : ∀ z ∈ s, z p = a p := by
  intro z hz
  have h1 : z p - w p ≤ 1 :=
    ht.sub_le_one w (Finset.mem_insert_self _ _) z (Finset.mem_insert_of_mem hz) p
  have h2 : a p ≤ z p := Pi.le_def.1 (hbot z hz) p
  omega

/-- A vertex added above a simplex raises a coordinate that is constant on it. -/
theorem IsSimplex.const_of_insert_top {w b : Fin n → ℤ} {p : Fin n}
    (ht : IsSimplex N (insert w s)) (htop : ∀ z ∈ s, z ≤ b)
    (hwp : b p + 1 = w p) : ∀ z ∈ s, z p = b p := by
  intro z hz
  have h1 : w p - z p ≤ 1 :=
    ht.sub_le_one z (Finset.mem_insert_of_mem hz) w (Finset.mem_insert_self _ _) p
  have h2 : z p ≤ b p := Pi.le_def.1 (htop z hz) p
  omega

/- ### Raising and lowering a coordinate

The vertices that extend a simplex differ from one of its vertices in a single coordinate,
by one. -/

/-- The point obtained from `x` by raising the coordinate `p` by one. -/
def raise (x : Fin n → ℤ) (p : Fin n) : Fin n → ℤ := Function.update x p (x p + 1)

/-- The point obtained from `x` by lowering the coordinate `p` by one. -/
def lower (x : Fin n → ℤ) (p : Fin n) : Fin n → ℤ := Function.update x p (x p - 1)

/-- Raising changes the chosen coordinate. -/
@[simp]
theorem raise_apply_self (x : Fin n → ℤ) (p : Fin n) : raise x p p = x p + 1 := by
  simp [raise]

/-- Raising leaves the other coordinates alone. -/
@[simp]
theorem raise_apply_of_ne (x : Fin n → ℤ) {p j : Fin n} (h : j ≠ p) : raise x p j = x j := by
  simp [raise, h]

/-- Lowering changes the chosen coordinate. -/
@[simp]
theorem lower_apply_self (x : Fin n → ℤ) (p : Fin n) : lower x p p = x p - 1 := by
  simp [lower]

/-- Lowering leaves the other coordinates alone. -/
@[simp]
theorem lower_apply_of_ne (x : Fin n → ℤ) {p j : Fin n} (h : j ≠ p) : lower x p j = x j := by
  simp [lower, h]

/-- Raising a coordinate increases the point. -/
theorem le_raise (x : Fin n → ℤ) (p : Fin n) : x ≤ raise x p := by
  refine Pi.le_def.2 fun j => ?_
  rcases eq_or_ne j p with rfl | h
  · simp
  · simp [h]

/-- Lowering a coordinate decreases the point. -/
theorem lower_le (x : Fin n → ℤ) (p : Fin n) : lower x p ≤ x := by
  refine Pi.le_def.2 fun j => ?_
  rcases eq_or_ne j p with rfl | h
  · simp
  · simp [h]

/-- Raising in different coordinates gives different points. -/
theorem raise_ne_raise {x : Fin n → ℤ} {p q : Fin n} (h : p ≠ q) : raise x p ≠ raise x q :=
  fun hcon => by simpa [h, raise_apply_of_ne x h] using congrFun hcon p

/- ### Extremal faces

A simplex on which one coordinate takes the same extreme value `N` or `-N` at every vertex
lies in a face of the cube.  These are the simplices the parity argument pairs up by
reflection. -/

/-- One coordinate is constantly `N`, or constantly `-N`, on `s`. -/
def IsExtremal (N : ℕ) (s : Finset (Fin n → ℤ)) : Prop :=
  ∃ c, (∀ z ∈ s, z c = (N : ℤ)) ∨ ∀ z ∈ s, z c = -(N : ℤ)

/-- Reflection preserves extremality. -/
theorem IsExtremal.neg (h : IsExtremal N s) : IsExtremal N (-s) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rcases hc with hc | hc
  · refine Or.inr fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hz
    simp [hc y hy]
  · refine Or.inl fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hz
    simp [hc y hy]

/-- **Reflection has no fixed extremal face.**  An extremal face and its reflection differ,
because the extreme coordinate would have to take both values `N` and `-N`. -/
theorem IsExtremal.neg_ne (h : IsExtremal N s) (hs : s.Nonempty) (hN : 0 < N) : -s ≠ s := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨z, hz⟩ := hs
  intro hcon
  have hmem : -z ∈ s := hcon ▸ Finset.mem_neg.2 ⟨z, hz, rfl⟩
  have hN' : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  rcases hc with hc | hc
  · have h1 := hc z hz
    have h2 := hc (-z) hmem
    simp only [Pi.neg_apply] at h2
    omega
  · have h1 := hc z hz
    have h2 := hc (-z) hmem
    simp only [Pi.neg_apply] at h2
    omega

/- ### Inserting a vertex

Three ways of extending a simplex by one vertex: between two consecutive vertices, one
unit step below the least, and one unit step above the greatest.  In each case the
resulting set is again a simplex, and under the stated conditions it carries no new
sign. -/

/-- Inserting a vertex between two consecutive vertices gives a simplex. -/
theorem IsSimplex.insert_between (hs : IsSimplex N s) {x y w : Fin n → ℤ} (hx : x ∈ s)
    (hy : y ∈ s) (hxw : x ≤ w) (hwy : w ≤ y) (hcons : ∀ z ∈ s, ¬(x < z ∧ z < y)) :
    IsSimplex N (insert w s) := by
  refine hs.insert_vertex
    (mem_grid_of_le_of_le (hs.subset_grid hx) (hs.subset_grid hy) hxw hwy) ?_ ?_
  · intro z hz
    rcases eq_or_ne z x with rfl | hzx
    · exact Or.inr hxw
    rcases hs.chain hz hx hzx with h | h
    · exact Or.inr (h.trans hxw)
    · have hxz : x < z := lt_of_le_of_ne h (Ne.symm hzx)
      rcases eq_or_ne z y with rfl | hzy
      · exact Or.inl hwy
      rcases hs.chain hz hy hzy with h' | h'
      · exact absurd ⟨hxz, lt_of_le_of_ne h' hzy⟩ (hcons z hz)
      · exact Or.inl (hwy.trans h')
  · intro z hz i
    refine ⟨?_, ?_⟩
    · have h1 : x i ≤ w i := Pi.le_def.1 hxw i
      have h2 : z i - x i ≤ 1 := hs.sub_le_one x hx z hz i
      omega
    · have h1 : w i ≤ y i := Pi.le_def.1 hwy i
      have h2 : y i - z i ≤ 1 := hs.sub_le_one z hz y hy i
      omega

/-- Inserting the least vertex with one constant coordinate lowered gives a simplex. -/
theorem IsSimplex.insert_lower (hs : IsSimplex N s) {a : Fin n → ℤ} {p : Fin n} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hconst : ∀ z ∈ s, z p = a p) (hgrid : -(N : ℤ) ≤ a p - 1) :
    IsSimplex N (insert (lower a p) s) := by
  refine hs.insert_vertex ?_ ?_ ?_
  · rw [mem_grid]
    intro i
    have hai := mem_grid.1 (hs.subset_grid ha) i
    rcases eq_or_ne i p with rfl | hne
    · rw [lower_apply_self]; omega
    · rw [lower_apply_of_ne _ hne]; omega
  · intro z hz
    refine Or.inl (Pi.le_def.2 fun i => ?_)
    have h1 : a i ≤ z i := Pi.le_def.1 (hbot z hz) i
    rcases eq_or_ne i p with rfl | hne
    · rw [lower_apply_self]; omega
    · rw [lower_apply_of_ne _ hne]; omega
  · intro z hz i
    have h1 : a i ≤ z i := Pi.le_def.1 (hbot z hz) i
    have h2 : z i - a i ≤ 1 := hs.sub_le_one a ha z hz i
    rcases eq_or_ne i p with rfl | hne
    · have h3 := hconst z hz
      rw [lower_apply_self]; omega
    · rw [lower_apply_of_ne _ hne]; omega

/-- Inserting the greatest vertex with one constant coordinate raised gives a simplex. -/
theorem IsSimplex.insert_raise (hs : IsSimplex N s) {b : Fin n → ℤ} {p : Fin n} (hb : b ∈ s)
    (htop : ∀ z ∈ s, z ≤ b) (hconst : ∀ z ∈ s, z p = b p) (hgrid : b p + 1 ≤ (N : ℤ)) :
    IsSimplex N (insert (raise b p) s) := by
  refine hs.insert_vertex ?_ ?_ ?_
  · rw [mem_grid]
    intro i
    have hbi := mem_grid.1 (hs.subset_grid hb) i
    rcases eq_or_ne i p with rfl | hne
    · rw [raise_apply_self]; omega
    · rw [raise_apply_of_ne _ hne]; omega
  · intro z hz
    refine Or.inr (Pi.le_def.2 fun i => ?_)
    have h1 : z i ≤ b i := Pi.le_def.1 (htop z hz) i
    rcases eq_or_ne i p with rfl | hne
    · rw [raise_apply_self]; omega
    · rw [raise_apply_of_ne _ hne]; omega
  · intro z hz i
    have h1 : z i ≤ b i := Pi.le_def.1 (htop z hz) i
    have h2 : b i - z i ≤ 1 := hs.sub_le_one z hz b hb i
    rcases eq_or_ne i p with rfl | hne
    · have h3 := hconst z hz
      rw [raise_apply_self]; omega
    · rw [raise_apply_of_ne _ hne]; omega

/-- Inserting a vertex that is positive only where the simplex already is, and negative
only where it already is, adds no sign. -/
theorem signs_insert_subset {w : Fin n → ℤ}
    (h : ∀ i, (0 < w i → ∃ z ∈ s, 0 < z i) ∧ (w i < 0 → ∃ z ∈ s, z i < 0)) :
    signs (insert w s) ⊆ signs s := by
  rintro ⟨i, c⟩ hp
  cases c
  · obtain ⟨x, hx, hxi⟩ := mem_signs_false.1 hp
    rcases Finset.mem_insert.1 hx with rfl | hxs
    · exact mem_signs_false.2 ((h i).2 hxi)
    · exact mem_signs_false.2 ⟨x, hxs, hxi⟩
  · obtain ⟨x, hx, hxi⟩ := mem_signs_true.1 hp
    rcases Finset.mem_insert.1 hx with rfl | hxs
    · exact mem_signs_true.2 ((h i).1 hxi)
    · exact mem_signs_true.2 ⟨x, hxs, hxi⟩

/-- A vertex inserted between two vertices of the simplex adds no sign. -/
theorem signs_insert_subset_of_between {x y w : Fin n → ℤ} (hx : x ∈ s) (hy : y ∈ s)
    (hxw : x ≤ w) (hwy : w ≤ y) : signs (insert w s) ⊆ signs s :=
  signs_insert_subset fun i =>
    ⟨fun hpos => ⟨y, hy, lt_of_lt_of_le hpos (Pi.le_def.1 hwy i)⟩,
      fun hneg => ⟨x, hx, lt_of_le_of_lt (Pi.le_def.1 hxw i) hneg⟩⟩

/-- Lowering a constant nonzero coordinate of the least vertex adds no sign. -/
theorem signs_insert_lower_subset {a : Fin n → ℤ} {p : Fin n} (ha : a ∈ s)
    (hconst : ∀ z ∈ s, z p = a p) (hne : a p ≠ 0) :
    signs (insert (lower a p) s) ⊆ signs s := by
  refine signs_insert_subset fun i => ?_
  rcases eq_or_ne i p with rfl | hne'
  · rw [lower_apply_self]
    exact ⟨fun h => ⟨a, ha, by omega⟩, fun h => ⟨a, ha, by omega⟩⟩
  · rw [lower_apply_of_ne _ hne']
    exact ⟨fun h => ⟨a, ha, h⟩, fun h => ⟨a, ha, h⟩⟩

/-- Raising a constant nonzero coordinate of the greatest vertex adds no sign. -/
theorem signs_insert_raise_subset {b : Fin n → ℤ} {p : Fin n} (hb : b ∈ s)
    (hconst : ∀ z ∈ s, z p = b p) (hne : b p ≠ 0) :
    signs (insert (raise b p) s) ⊆ signs s := by
  refine signs_insert_subset fun i => ?_
  rcases eq_or_ne i p with rfl | hne'
  · rw [raise_apply_self]
    exact ⟨fun h => ⟨b, hb, by omega⟩, fun h => ⟨b, hb, by omega⟩⟩
  · rw [raise_apply_of_ne _ hne']
    exact ⟨fun h => ⟨b, hb, h⟩, fun h => ⟨b, hb, h⟩⟩

/- ### Excluding positions for a new vertex

Which of the three positions a new vertex can take is decided by the size of the total
step set, compared with the number of directions the enlarged simplex is allowed. -/

/-- A coordinate in which the greatest vertex does not exceed the least one is constant. -/
theorem const_of_not_mem_step {a b : Fin n → ℤ} (hbot : ∀ z ∈ s, a ≤ z)
    (htop : ∀ z ∈ s, z ≤ b) {p : Fin n} (hp : p ∉ step a b) : ∀ z ∈ s, z p = a p := by
  intro z hz
  have h1 : a p ≤ z p := Pi.le_def.1 (hbot z hz) p
  have h2 : z p ≤ b p := Pi.le_def.1 (htop z hz) p
  have h3 : ¬ a p < b p := by simpa [mem_step] using hp
  omega

/-- If the enlarged simplex has no more directions than the total step set has
coordinates, no vertex can be added below the least one. -/
theorem IsSimplex.not_lt_of_insert {w a b : Fin n → ℤ} (ht : IsSimplex N (insert w s))
    (ha : a ∈ s) (hb : b ∈ s) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : (directions (insert w s)).card ≤ (step a b).card) : ¬ w < a := by
  intro hwa
  obtain ⟨p, hp⟩ : ∃ p, w p < a p := by
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hwa.ne
    exact ⟨p, lt_of_le_of_ne (Pi.le_def.1 hwa.le p) hp⟩
  have hab : a p ≤ b p := Pi.le_def.1 (htop a ha) p
  by_cases hmem : p ∈ step a b
  · rw [mem_step] at hmem
    have := ht.sub_le_one w (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb) p
    omega
  · have hsub : step a b ⊆ step w b := step_subset_step_base hwa.le
    have hpw : p ∈ step w b := mem_step.2 (by omega)
    have h1 : (step w b).card ≤ (directions (insert w s)).card :=
      Finset.card_le_card (step_subset_directions (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hb))
    have h2 := Finset.card_lt_card (ssubset_iff_of_subset hsub |>.2 ⟨p, hpw, hmem⟩)
    omega

/-- If the enlarged simplex has no more directions than the total step set has
coordinates, no vertex can be added above the greatest one. -/
theorem IsSimplex.not_gt_of_insert {w a b : Fin n → ℤ} (ht : IsSimplex N (insert w s))
    (ha : a ∈ s) (hb : b ∈ s) (hbot : ∀ z ∈ s, a ≤ z)
    (hcard : (directions (insert w s)).card ≤ (step a b).card) : ¬ b < w := by
  intro hbw
  obtain ⟨p, hp⟩ : ∃ p, b p < w p := by
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hbw.ne
    exact ⟨p, lt_of_le_of_ne (Pi.le_def.1 hbw.le p) hp⟩
  have hab : a p ≤ b p := Pi.le_def.1 (hbot b hb) p
  by_cases hmem : p ∈ step a b
  · rw [mem_step] at hmem
    have := ht.sub_le_one a (Finset.mem_insert_of_mem ha) w (Finset.mem_insert_self _ _) p
    omega
  · have hsub : step a b ⊆ step a w := step_subset_step hbw.le
    have hpw : p ∈ step a w := mem_step.2 (by omega)
    have h1 : (step a w).card ≤ (directions (insert w s)).card :=
      Finset.card_le_card (step_subset_directions (Finset.mem_insert_of_mem ha)
        (Finset.mem_insert_self _ _))
    have h2 := Finset.card_lt_card (ssubset_iff_of_subset hsub |>.2 ⟨p, hpw, hmem⟩)
    omega

/-- A saturated simplex admits no new vertex between its least and its greatest. -/
theorem IsSimplex.not_between_of_saturated {w a b : Fin n → ℤ}
    (ht : IsSimplex N (insert w s)) (ha : a ∈ s) (hbot : ∀ z ∈ s, a ≤ z)
    (htop : ∀ z ∈ s, z ≤ b) (hws : w ∉ s) (haw : a ≤ w) (hwb : w ≤ b)
    (hcard : s.card = (step a b).card + 1) : False := by
  have hbot' : ∀ z ∈ insert w s, a ≤ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact haw
    · exact hbot z hzs
  have htop' : ∀ z ∈ insert w s, z ≤ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact hwb
    · exact htop z hzs
  have h := ht.card_le_card_step_succ (Finset.mem_insert_of_mem ha) hbot' htop'
  rw [Finset.card_insert_of_notMem hws] at h
  omega

/- ### Counting the extensions

How many vertices extend a simplex to a larger simplex whose signs stay inside a
prescribed set of labels.  The three counts below are the three shapes a simplex can have
relative to its number of directions. -/

open scoped Classical in
/-- The vertices extending `s` to a larger simplex all of whose signs lie in `t`. -/
noncomputable def extensions (N : ℕ) (s : Finset (Fin n → ℤ)) (t : Finset (Label n)) :
    Finset (Fin n → ℤ) :=
  (grid n N).filter fun w => w ∉ s ∧ IsSimplex N (insert w s) ∧ signs (insert w s) ⊆ t

/-- Membership in `extensions`, unfolded.  The grid condition is automatic. -/
theorem mem_extensions {t : Finset (Label n)} {w : Fin n → ℤ} :
    w ∈ extensions N s t ↔ w ∉ s ∧ IsSimplex N (insert w s) ∧ signs (insert w s) ⊆ t := by
  classical
  rw [extensions, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.2.1.subset_grid (Finset.mem_insert_self _ _), h⟩⟩

/-- An extension has no more directions than the allowed labels. -/
theorem card_directions_insert_le {t : Finset (Label n)} {w : Fin n → ℤ}
    (hw : w ∈ extensions N s t) : (directions (insert w s)).card ≤ t.card := by
  obtain ⟨-, ht, hsub⟩ := mem_extensions.1 hw
  rw [← ht.card_signs]
  exact Finset.card_le_card hsub

/-- **A simplex with one more vertex than it has directions has no extension keeping its
signs.**  This is the shape of a happy simplex with a repeated label. -/
theorem extensions_eq_empty (hs : IsSimplex N s)
    (hcard : s.card = (directions s).card + 1) : extensions N s (signs s) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  obtain ⟨hws, ht, -⟩ := mem_extensions.1 hw
  have h1 : (directions (insert w s)).card ≤ (signs s).card := card_directions_insert_le hw
  rw [hs.card_signs] at h1
  have h2 := ht.card_le_card_directions_succ
  rw [Finset.card_insert_of_notMem hws] at h2
  omega

/-- A coordinate carrying neither sign vanishes on the simplex. -/
theorem eq_zero_of_not_mem_signs {j : Fin n} (hpos : ((j, true) : Label n) ∉ signs s)
    (hneg : ((j, false) : Label n) ∉ signs s) : ∀ z ∈ s, z j = 0 := by
  intro z hz
  rcases lt_trichotomy (z j) 0 with h | h | h
  · exact absurd (mem_signs_false.2 ⟨z, hz, h⟩) hneg
  · exact h
  · exact absurd (mem_signs_true.2 ⟨z, hz, h⟩) hpos

/-- **Allowing one new positive label, a simplex with one more vertex than it has
directions extends only by raising that coordinate above its greatest vertex.** -/
theorem extensions_eq_singleton_raise (hs : IsSimplex N s) (hN : 0 < N)
    (hcard : s.card = (directions s).card + 1) {b : Fin n → ℤ} (hb : b ∈ s)
    (htop : ∀ z ∈ s, z ≤ b) {j : Fin n} (hpos : ((j, true) : Label n) ∉ signs s)
    (hneg : ((j, false) : Label n) ∉ signs s) :
    extensions N s (insert (j, true) (signs s)) = {raise b j} := by
  have hzero := eq_zero_of_not_mem_signs hpos hneg
  obtain ⟨a, ha, hbot⟩ := hs.exists_bot
  have hbj : b j = 0 := hzero b hb
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hmem : raise b j ∈ extensions N s (insert (j, true) (signs s)) := by
    refine mem_extensions.2 ⟨?_, ?_, ?_⟩
    · intro hcon
      have h := hzero _ hcon
      rw [raise_apply_self] at h
      omega
    · refine hs.insert_raise hb htop (fun z hz => by rw [hzero z hz, hbj]) ?_
      omega
    · rintro ⟨i, d⟩ hq
      by_cases hij : i = j
      · subst hij
        cases d
        · exfalso
          obtain ⟨z, hz, hzi⟩ := mem_signs_false.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · rw [raise_apply_self] at hzi; omega
          · rw [hzero z hzs] at hzi; omega
        · exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem ?_
        cases d
        · obtain ⟨z, hz, hzi⟩ := mem_signs_false.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · exact mem_signs_false.2 ⟨b, hb, by rwa [raise_apply_of_ne _ hij] at hzi⟩
          · exact mem_signs_false.2 ⟨z, hzs, hzi⟩
        · obtain ⟨z, hz, hzi⟩ := mem_signs_true.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · exact mem_signs_true.2 ⟨b, hb, by rwa [raise_apply_of_ne _ hij] at hzi⟩
          · exact mem_signs_true.2 ⟨z, hzs, hzi⟩
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, fun w hw => ?_⟩
  obtain ⟨hws, ht, hsub⟩ := mem_extensions.1 hw
  have hcardins : (insert w s).card = s.card + 1 := Finset.card_insert_of_notMem hws
  have hdle : (directions (insert w s)).card ≤ (directions s).card + 1 := by
    rw [← ht.card_signs]
    calc (signs (insert w s)).card ≤ (insert ((j, true) : Label n) (signs s)).card :=
          Finset.card_le_card hsub
      _ ≤ (signs s).card + 1 := Finset.card_insert_le _ _
      _ = (directions s).card + 1 := by rw [hs.card_signs]
  have hdge := ht.card_le_card_directions_succ
  have hdeq : (directions (insert w s)).card = (directions s).card + 1 := by omega
  have hwj : 0 < w j := by
    rcases lt_trichotomy (w j) 0 with h | h | h
    · exfalso
      have hq : ((j, false) : Label n) ∈ signs (insert w s) :=
        mem_signs_false.2 ⟨w, Finset.mem_insert_self _ _, h⟩
      rcases Finset.mem_insert.1 (hsub hq) with heq | hq'
      · exact absurd heq (by simp)
      · exact hneg hq'
    · exfalso
      have hsub' : signs (insert w s) ⊆ signs s := by
        intro q hq
        rcases Finset.mem_insert.1 (hsub hq) with heq | hq'
        · exfalso
          subst heq
          obtain ⟨z, hz, hzi⟩ := mem_signs_true.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · omega
          · rw [hzero z hzs] at hzi; omega
        · exact hq'
      have hdsub : directions (insert w s) ⊆ directions s :=
        Finset.image_subset_image hsub'
      have := Finset.card_le_card hdsub
      omega
    · exact h
  have hbw : b < w := by
    have hne : b ≠ w := by
      intro hcon
      rw [← hcon] at hwj
      omega
    rcases ht.chain (Finset.mem_insert_of_mem hb) (Finset.mem_insert_self _ _) hne with h | h
    · exact lt_of_le_of_ne h hne
    · exact absurd (Pi.le_def.1 h j) (by omega)
  have hbot' : ∀ z ∈ insert w s, a ≤ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_trans (hbot b hb) hbw.le
    · exact hbot z hzs
  have htop' : ∀ z ∈ insert w s, z ≤ w := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_rfl
    · exact le_trans (htop z hzs) hbw.le
  have hstep : (insert w s).card = (step a w).card + 1 :=
    ht.card_eq_card_step_succ (Finset.mem_insert_of_mem ha) hbot'
      (Finset.mem_insert_self _ _) htop' (by omega)
  obtain ⟨i, hi1, hi2⟩ := ht.exists_eq_top_add_single ha hbot hb htop hbw hstep
  have hij : i = j := by
    by_contra hcon
    have h := hi2 j fun hjj => hcon hjj.symm
    omega
  subst hij
  refine funext fun j' => ?_
  rcases eq_or_ne j' i with rfl | hne
  · rw [raise_apply_self]; omega
  · rw [raise_apply_of_ne _ hne]; exact (hi2 j' hne).symm

/-- **Allowing one new negative label, a simplex with one more vertex than it has
directions extends only by lowering that coordinate below its least vertex.** -/
theorem extensions_eq_singleton_lower (hs : IsSimplex N s) (hN : 0 < N)
    (hcard : s.card = (directions s).card + 1) {a : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) {j : Fin n} (hpos : ((j, true) : Label n) ∉ signs s)
    (hneg : ((j, false) : Label n) ∉ signs s) :
    extensions N s (insert (j, false) (signs s)) = {lower a j} := by
  have hzero := eq_zero_of_not_mem_signs hpos hneg
  obtain ⟨b, hb, htop⟩ := hs.exists_top
  have haj : a j = 0 := hzero a ha
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hmem : lower a j ∈ extensions N s (insert (j, false) (signs s)) := by
    refine mem_extensions.2 ⟨?_, ?_, ?_⟩
    · intro hcon
      have h := hzero _ hcon
      rw [lower_apply_self] at h
      omega
    · refine hs.insert_lower ha hbot (fun z hz => by rw [hzero z hz, haj]) ?_
      omega
    · rintro ⟨i, d⟩ hq
      by_cases hij : i = j
      · subst hij
        cases d
        · exact Finset.mem_insert_self _ _
        · exfalso
          obtain ⟨z, hz, hzi⟩ := mem_signs_true.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · rw [lower_apply_self] at hzi; omega
          · rw [hzero z hzs] at hzi; omega
      · refine Finset.mem_insert_of_mem ?_
        cases d
        · obtain ⟨z, hz, hzi⟩ := mem_signs_false.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · exact mem_signs_false.2 ⟨a, ha, by rwa [lower_apply_of_ne _ hij] at hzi⟩
          · exact mem_signs_false.2 ⟨z, hzs, hzi⟩
        · obtain ⟨z, hz, hzi⟩ := mem_signs_true.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · exact mem_signs_true.2 ⟨a, ha, by rwa [lower_apply_of_ne _ hij] at hzi⟩
          · exact mem_signs_true.2 ⟨z, hzs, hzi⟩
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, fun w hw => ?_⟩
  obtain ⟨hws, ht, hsub⟩ := mem_extensions.1 hw
  have hcardins : (insert w s).card = s.card + 1 := Finset.card_insert_of_notMem hws
  have hdle : (directions (insert w s)).card ≤ (directions s).card + 1 := by
    rw [← ht.card_signs]
    calc (signs (insert w s)).card ≤ (insert ((j, false) : Label n) (signs s)).card :=
          Finset.card_le_card hsub
      _ ≤ (signs s).card + 1 := Finset.card_insert_le _ _
      _ = (directions s).card + 1 := by rw [hs.card_signs]
  have hdge := ht.card_le_card_directions_succ
  have hdeq : (directions (insert w s)).card = (directions s).card + 1 := by omega
  have hwj : w j < 0 := by
    rcases lt_trichotomy (w j) 0 with h | h | h
    · exact h
    · exfalso
      have hsub' : signs (insert w s) ⊆ signs s := by
        intro q hq
        rcases Finset.mem_insert.1 (hsub hq) with heq | hq'
        · exfalso
          subst heq
          obtain ⟨z, hz, hzi⟩ := mem_signs_false.1 hq
          rcases Finset.mem_insert.1 hz with rfl | hzs
          · omega
          · rw [hzero z hzs] at hzi; omega
        · exact hq'
      have hdsub : directions (insert w s) ⊆ directions s :=
        Finset.image_subset_image hsub'
      have := Finset.card_le_card hdsub
      omega
    · exfalso
      have hq : ((j, true) : Label n) ∈ signs (insert w s) :=
        mem_signs_true.2 ⟨w, Finset.mem_insert_self _ _, h⟩
      rcases Finset.mem_insert.1 (hsub hq) with heq | hq'
      · exact absurd heq (by simp)
      · exact hpos hq'
  have hwa : w < a := by
    have hne : w ≠ a := by
      intro hcon
      rw [hcon] at hwj
      omega
    rcases ht.chain (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem ha) hne with h | h
    · exact lt_of_le_of_ne h hne
    · exact absurd (Pi.le_def.1 h j) (by omega)
  have hbot' : ∀ z ∈ insert w s, w ≤ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_rfl
    · exact le_trans hwa.le (hbot z hzs)
  have htop' : ∀ z ∈ insert w s, z ≤ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hzs
    · exact le_trans hwa.le (htop a ha)
    · exact htop z hzs
  have hstep : (insert w s).card = (step w b).card + 1 :=
    ht.card_eq_card_step_succ (Finset.mem_insert_self _ _) hbot'
      (Finset.mem_insert_of_mem hb) htop' (by omega)
  obtain ⟨i, hi1, hi2⟩ := ht.exists_eq_add_single_bot ha hbot htop hwa hstep
  have hij : i = j := by
    by_contra hcon
    have h := hi2 j fun hjj => hcon hjj.symm
    omega
  subst hij
  refine funext fun j' => ?_
  rcases eq_or_ne j' i with rfl | hne
  · rw [lower_apply_self]; omega
  · rw [lower_apply_of_ne _ hne]; exact hi2 j' hne

/-- **A simplex with one more vertex than it has directions extends in exactly one way when
one further label is allowed.**

This is the shape of a happy simplex whose labels are distinct: it has one label beyond
its signs, and that label decides which end of the chain grows. -/
theorem card_extensions_eq_one (hs : IsSimplex N s) (hN : 0 < N)
    (hcard : s.card = (directions s).card + 1) {l : Label n} (hl : l ∉ signs s)
    (hl' : negLabel l ∉ signs s) : (extensions N s (insert l (signs s))).card = 1 := by
  obtain ⟨j, d⟩ := l
  have hpos : ((j, true) : Label n) ∉ signs s := by
    cases d
    · simpa [negLabel] using hl'
    · exact hl
  have hneg : ((j, false) : Label n) ∉ signs s := by
    cases d
    · exact hl
    · simpa [negLabel] using hl'
  cases d
  · obtain ⟨a, ha, hbot⟩ := hs.exists_bot
    rw [extensions_eq_singleton_lower hs hN hcard ha hbot hpos hneg, Finset.card_singleton]
  · obtain ⟨b, hb, htop⟩ := hs.exists_top
    rw [extensions_eq_singleton_raise hs hN hcard hb htop hpos hneg, Finset.card_singleton]

/- ### Simplices with as many vertices as directions

The remaining shape.  Such a simplex is one vertex short of filling its chain, and the
missing vertex can be supplied in exactly two ways, unless one coordinate sits at the
boundary of the cube, which blocks one of them. -/

/-- A point has rank zero relative to itself. -/
@[simp]
theorem rank_self (a : Fin n → ℤ) : rank a a = 0 := by
  simp [rank, step]

/-- **A simplex whose total step set spans all of its directions has exactly two extensions
keeping its signs.**

Its ranks miss a single value; the two vertices on either side of the gap differ by two
unit steps, and the new vertex takes one of the two intermediate positions. -/
theorem card_extensions_eq_two_of_full (hs : IsSimplex N s) {a b : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hb : b ∈ s) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (directions s).card) (hfull : (step a b).card = s.card) :
    (extensions N s (signs s)).card = 2 := by
  classical
  -- the ranks of `s` miss exactly one value below `s.card`
  have hrsub : s.image (rank a) ⊆ Finset.range (s.card + 1) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    refine Finset.mem_range.2 (Nat.lt_succ_of_le ?_)
    rw [← hfull]
    exact Finset.card_le_card (step_subset_step (htop x hx))
  have hrcard : (s.image (rank a)).card = s.card :=
    Finset.card_image_of_injOn (hs.injOn_rank ha hbot)
  have hmiss : (Finset.range (s.card + 1) \ s.image (rank a)).card = 1 := by
    rw [Finset.card_sdiff_of_subset hrsub, Finset.card_range, hrcard]
    omega
  obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hmiss
  have hrmem : r ∈ Finset.range (s.card + 1) ∧ r ∉ s.image (rank a) :=
    Finset.mem_sdiff.1 (by rw [hr]; exact Finset.mem_singleton_self r)
  have hrothers : ∀ c, c ≤ s.card → c ≠ r → ∃ z ∈ s, rank a z = c := by
    intro c hc hcr
    have hcimg : c ∈ s.image (rank a) := by
      by_contra hcon
      have hmem : c ∈ Finset.range (s.card + 1) \ s.image (rank a) :=
        Finset.mem_sdiff.2 ⟨Finset.mem_range.2 (by omega), hcon⟩
      rw [hr] at hmem
      exact hcr (Finset.mem_singleton.1 hmem)
    obtain ⟨z, hz, hzc⟩ := Finset.mem_image.1 hcimg
    exact ⟨z, hz, hzc⟩
  have hr0 : r ≠ 0 := by
    intro h
    exact hrmem.2 (Finset.mem_image.2 ⟨a, ha, by rw [rank_self, h]⟩)
  have hrk : r ≠ s.card := by
    intro h
    exact hrmem.2 (Finset.mem_image.2 ⟨b, hb, by rw [h]; exact hfull⟩)
  have hrlt : r < s.card := by
    have := Finset.mem_range.1 hrmem.1
    omega
  -- the two vertices on either side of the gap
  obtain ⟨x, hx, hxr⟩ := hrothers (r - 1) (by omega) (by omega)
  obtain ⟨y, hy, hyr⟩ := hrothers (r + 1) (by omega) (by omega)
  have hxy : x < y := hs.lt_of_rank_lt ha hbot hx hy (by omega)
  have hcons : ∀ z ∈ s, ¬(x < z ∧ z < y) := by
    rintro z hz ⟨h1, h2⟩
    have h3 := hs.rank_lt_rank ha hbot hx hz h1
    have h4 := hs.rank_lt_rank ha hbot hz hy h2
    exact hrmem.2 (Finset.mem_image.2 ⟨z, hz, by omega⟩)
  -- they differ by two unit steps
  have hstepsub : step a x ⊆ step a y := step_subset_step hxy.le
  have hxc : (step a x).card = r - 1 := hxr
  have hyc : (step a y).card = r + 1 := hyr
  have hdiff : (step a y \ step a x).card = 2 := by
    rw [Finset.card_sdiff_of_subset hstepsub]
    omega
  obtain ⟨p, q, hpq, hpq2⟩ := Finset.card_eq_two.1 hdiff
  have hpmem : p ∈ step a y ∧ p ∉ step a x :=
    Finset.mem_sdiff.1 (by rw [hpq2]; exact Finset.mem_insert_self _ _)
  have hqmem : q ∈ step a y ∧ q ∉ step a x :=
    Finset.mem_sdiff.1 (by rw [hpq2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
  -- each of the two intermediate positions is an extension
  have hcand : ∀ p', p' ∈ step a y → p' ∉ step a x →
      raise x p' ∈ extensions N s (signs s) ∧ step a (raise x p') = insert p' (step a x) := by
    intro p' hp1 hp2
    have hxp : x p' = a p' := by
      have h := hs.eq_add_ite ha hbot hx p'
      rw [if_neg hp2] at h
      omega
    have hyp : y p' = a p' + 1 := by
      have h := hs.eq_add_ite ha hbot hy p'
      rw [if_pos hp1] at h
      omega
    have hle1 : x ≤ raise x p' := le_raise x p'
    have hle2 : raise x p' ≤ y := by
      refine Pi.le_def.2 fun j => ?_
      rcases eq_or_ne j p' with rfl | hne
      · rw [raise_apply_self]; omega
      · rw [raise_apply_of_ne _ hne]; exact Pi.le_def.1 hxy.le j
    have hstep' : step a (raise x p') = insert p' (step a x) := by
      ext j
      rcases eq_or_ne j p' with rfl | hne
      · refine ⟨fun _ => Finset.mem_insert_self _ _, fun _ => ?_⟩
        rw [mem_step, raise_apply_self]
        omega
      · rw [mem_step, raise_apply_of_ne _ hne, Finset.mem_insert]
        simp only [hne, false_or, mem_step]
    refine ⟨mem_extensions.2 ⟨?_, hs.insert_between hx hy hle1 hle2 hcons,
      signs_insert_subset_of_between hx hy hle1 hle2⟩, hstep'⟩
    intro hcon
    have hrank : rank a (raise x p') = r := by
      show (step a (raise x p')).card = r
      rw [hstep', Finset.card_insert_of_notMem hp2]
      omega
    exact hrmem.2 (Finset.mem_image.2 ⟨_, hcon, hrank⟩)
  obtain ⟨hpext, -⟩ := hcand p hpmem.1 hpmem.2
  obtain ⟨hqext, -⟩ := hcand q hqmem.1 hqmem.2
  -- and there are no others
  have hsetf : extensions N s (signs s) = {raise x p, raise x q} := by
    refine Finset.Subset.antisymm (fun w hw => ?_) (fun w hw => ?_)
    · obtain ⟨hws, ht, hsubs⟩ := mem_extensions.1 hw
      have hdle : (directions (insert w s)).card ≤ (step a b).card := by
        rw [← ht.card_signs]
        calc (signs (insert w s)).card ≤ (signs s).card := Finset.card_le_card hsubs
          _ = (directions s).card := hs.card_signs
          _ = (step a b).card := by omega
      obtain ⟨x', hx', y', hy', hx'w, hwy', hcons'⟩ :=
        exists_between_of_insert ht.chain hws ha hb (ht.not_lt_of_insert ha hb htop hdle)
          (ht.not_gt_of_insert ha hb hbot hdle)
      have hbot' : ∀ z ∈ insert w s, a ≤ z := by
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hzs
        · exact le_trans (hbot x' hx') hx'w.le
        · exact hbot z hzs
      have htop' : ∀ z ∈ insert w s, z ≤ b := by
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hzs
        · exact le_trans hwy'.le (htop y' hy')
        · exact htop z hzs
      -- the rank of the new vertex is the missing one
      have hrw : rank a w = r := by
        have hwle : rank a w ≤ s.card := by
          rw [← hfull]
          exact Finset.card_le_card (step_subset_step (htop' w (Finset.mem_insert_self _ _)))
        by_contra hcon
        obtain ⟨z, hz, hzr⟩ := hrothers (rank a w) hwle hcon
        have hwz : w = z := ht.injOn_rank (Finset.mem_insert_of_mem ha) hbot'
          (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hz) hzr.symm
        exact hws (by rw [hwz]; exact hz)
      have h3 : r < rank a y' := by
        rw [← hrw]
        exact ht.rank_lt_rank (Finset.mem_insert_of_mem ha) hbot'
          (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hy') hwy'
      have h1 : rank a x' < r := by
        rw [← hrw]
        exact ht.rank_lt_rank (Finset.mem_insert_of_mem ha) hbot'
          (Finset.mem_insert_of_mem hx') (Finset.mem_insert_self _ _) hx'w
      -- so the two neighbours are the two vertices on either side of the gap
      have hxx : x' = x := by
        by_contra hcon
        have h2 : rank a x' ≠ r - 1 := fun h =>
          hcon (hs.injOn_rank ha hbot hx' hx (by omega))
        obtain ⟨z, hz, hzr⟩ := hrothers (r - 1) (by omega) (by omega)
        exact hcons' z hz ⟨hs.lt_of_rank_lt ha hbot hx' hz (by omega),
          hs.lt_of_rank_lt ha hbot hz hy' (by omega)⟩
      have hyy : y' = y := by
        by_contra hcon
        have h2 : rank a y' ≠ r + 1 := fun h =>
          hcon (hs.injOn_rank ha hbot hy' hy (by omega))
        obtain ⟨z, hz, hzr⟩ := hrothers (r + 1) (by omega) (by omega)
        exact hcons' z hz ⟨hs.lt_of_rank_lt ha hbot hx' hz (by omega),
          hs.lt_of_rank_lt ha hbot hz hy' (by omega)⟩
      subst hxx
      subst hyy
      -- the new vertex adds exactly one of the two coordinates
      have hsub1 : step a x' ⊆ step a w := step_subset_step hx'w.le
      have hsub2 : step a w ⊆ step a y' := step_subset_step hwy'.le
      obtain ⟨i, hi1, hi2⟩ := Finset.exists_eq_insert_iff.2
        ⟨hsub1, show (step a x').card + 1 = (step a w).card by
          have : (step a w).card = r := hrw
          omega⟩
      have hiw : i ∈ step a w := by rw [← hi2]; exact Finset.mem_insert_self _ _
      have hi3 : i ∈ step a y' \ step a x' := Finset.mem_sdiff.2 ⟨hsub2 hiw, hi1⟩
      rw [hpq2] at hi3
      have hweq : w = raise x' i := by
        refine funext fun j => ?_
        have hwj := ht.eq_add_ite (Finset.mem_insert_of_mem ha) hbot'
          (Finset.mem_insert_self _ _) j
        have hxj := hs.eq_add_ite ha hbot hx' j
        rcases eq_or_ne j i with rfl | hne
        · rw [raise_apply_self, hwj, hxj, if_pos hiw, if_neg hi1]
          omega
        · rw [raise_apply_of_ne _ hne, hwj, hxj]
          have hiff : j ∈ step a w ↔ j ∈ step a x' := by
            rw [← hi2]
            simp only [Finset.mem_insert, hne, false_or]
          by_cases hj : j ∈ step a x'
          · rw [if_pos (hiff.2 hj), if_pos hj]
          · rw [if_neg fun h => hj (hiff.1 h), if_neg hj]
      rcases Finset.mem_insert.1 hi3 with rfl | hi4
      · rw [hweq]; exact Finset.mem_insert_self _ _
      · rw [Finset.mem_singleton] at hi4
        subst hi4
        rw [hweq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rcases Finset.mem_insert.1 hw with rfl | hw'
      · exact hpext
      · rw [Finset.mem_singleton] at hw'
        subst hw'
        exact hqext
  rw [hsetf, Finset.card_insert_of_notMem (by simpa using raise_ne_raise hpq),
    Finset.card_singleton]

/-- A saturated simplex with as many vertices as directions has exactly one constant
direction, and it is nonzero there. -/
theorem exists_const_direction {a b : Fin n → ℤ}
    (hbot : ∀ z ∈ s, a ≤ z) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (directions s).card) (hsat : s.card = (step a b).card + 1)
    (hsub : step a b ⊆ directions s) :
    ∃ c, (∀ i, i ∈ directions s → i ∉ step a b → i = c) ∧ (∀ z ∈ s, z c = a c) ∧
      a c ≠ 0 := by
  have hcs : (directions s \ step a b).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hcs
  obtain ⟨hcd, hcstep⟩ : c ∈ directions s ∧ c ∉ step a b :=
    Finset.mem_sdiff.1 (by rw [hc]; exact Finset.mem_singleton_self c)
  refine ⟨c, ?_, const_of_not_mem_step hbot htop hcstep, ?_⟩
  · intro i hi1 hi2
    have hmem : i ∈ directions s \ step a b := Finset.mem_sdiff.2 ⟨hi1, hi2⟩
    rw [hc] at hmem
    exact Finset.mem_singleton.1 hmem
  · obtain ⟨z, hz, hzc⟩ := mem_directions.1 hcd
    rwa [const_of_not_mem_step hbot htop hcstep z hz] at hzc

/-- Lowering the constant direction below the least vertex is an extension. -/
theorem lower_mem_extensions (hs : IsSimplex N s) {a : Fin n → ℤ} {c : Fin n} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hconst : ∀ z ∈ s, z c = a c) (hne : a c ≠ 0)
    (hgrid : -(N : ℤ) ≤ a c - 1) : lower a c ∈ extensions N s (signs s) := by
  refine mem_extensions.2 ⟨?_, hs.insert_lower ha hbot hconst hgrid,
    signs_insert_lower_subset ha hconst hne⟩
  intro hcon
  have h := hconst _ hcon
  rw [lower_apply_self] at h
  omega

/-- Raising the constant direction above the greatest vertex is an extension. -/
theorem raise_mem_extensions (hs : IsSimplex N s) {b : Fin n → ℤ} {c : Fin n} (hb : b ∈ s)
    (htop : ∀ z ∈ s, z ≤ b) (hconst : ∀ z ∈ s, z c = b c) (hne : b c ≠ 0)
    (hgrid : b c + 1 ≤ (N : ℤ)) : raise b c ∈ extensions N s (signs s) := by
  refine mem_extensions.2 ⟨?_, hs.insert_raise hb htop hconst hgrid,
    signs_insert_raise_subset hb hconst hne⟩
  intro hcon
  have h := hconst _ hcon
  rw [raise_apply_self] at h
  omega

/-- **A saturated simplex with as many vertices as directions extends only at the two ends
of its chain, in its one constant direction.** -/
theorem extensions_subset_of_saturated (hs : IsSimplex N s) {a b : Fin n → ℤ} (ha : a ∈ s)
    (hbot : ∀ z ∈ s, a ≤ z) (hb : b ∈ s) (htop : ∀ z ∈ s, z ≤ b)
    (hcard : s.card = (directions s).card) (hsat : s.card = (step a b).card + 1)
    {c : Fin n} (huniq : ∀ i, i ∈ directions s → i ∉ step a b → i = c) :
    extensions N s (signs s) ⊆ {lower a c, raise b c} := by
  intro w hw
  obtain ⟨hws, ht, hsubs⟩ := mem_extensions.1 hw
  have hdle : (directions (insert w s)).card ≤ (step a b).card + 1 := by
    rw [← ht.card_signs]
    calc (signs (insert w s)).card ≤ (signs s).card := Finset.card_le_card hsubs
      _ = (directions s).card := hs.card_signs
      _ = (step a b).card + 1 := by omega
  have hcardins : (insert w s).card = s.card + 1 := Finset.card_insert_of_notMem hws
  -- the new vertex lies below the least or above the greatest one
  have hpos : w < a ∨ b < w := by
    by_cases h1 : w < a
    · exact Or.inl h1
    by_cases h2 : b < w
    · exact Or.inr h2
    exfalso
    obtain ⟨x, hx, y, hy, hxw, hwy, -⟩ :=
      exists_between_of_insert ht.chain hws ha hb h1 h2
    exact ht.not_between_of_saturated ha hbot htop hws
      (le_trans (hbot x hx) hxw.le) (le_trans hwy.le (htop y hy)) hsat
  rcases hpos with hwa | hbw
  · have hbot' : ∀ z ∈ insert w s, w ≤ z := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hzs
      · exact le_rfl
      · exact le_of_lt (lt_of_lt_of_le hwa (hbot z hzs))
    have htop' : ∀ z ∈ insert w s, z ≤ b := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hzs
      · exact le_trans hwa.le (htop a ha)
      · exact htop z hzs
    have hstepw : (insert w s).card = (step w b).card + 1 := by
      have h1 : step a b ⊆ step w b := step_subset_step_base hwa.le
      have h2 : (step w b).card ≤ (directions (insert w s)).card :=
        Finset.card_le_card (step_subset_directions (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem hb))
      have h3 := ht.card_le_card_step_succ (Finset.mem_insert_self _ _) hbot' htop'
      have h4 := Finset.card_le_card h1
      omega
    obtain ⟨i, hi1, hi2⟩ := ht.exists_eq_add_single_bot ha hbot htop hwa hstepw
    have hconsti : ∀ z ∈ s, z i = a i := ht.const_of_insert_bot hbot hi1
    have hai : a i ≠ 0 := by
      intro h0
      have hmem : ((i, false) : Label n) ∈ signs (insert w s) :=
        mem_signs_false.2 ⟨w, Finset.mem_insert_self _ _, by omega⟩
      obtain ⟨z, hz, hzi⟩ := mem_signs_false.1 (hsubs hmem)
      rw [hconsti z hz] at hzi
      omega
    have hic : i = c := by
      refine huniq i (mem_directions.2 ⟨a, ha, hai⟩) ?_
      simp only [mem_step]
      have := hconsti b hb
      omega
    subst hic
    have hweq : w = lower a i := by
      refine funext fun j => ?_
      rcases eq_or_ne j i with rfl | hne
      · rw [lower_apply_self]; omega
      · rw [lower_apply_of_ne _ hne]; exact hi2 j hne
    rw [hweq]
    exact Finset.mem_insert_self _ _
  · have hbot' : ∀ z ∈ insert w s, a ≤ z := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hzs
      · exact le_trans (hbot b hb) hbw.le
      · exact hbot z hzs
    have htop' : ∀ z ∈ insert w s, z ≤ w := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hzs
      · exact le_rfl
      · exact le_trans (htop z hzs) hbw.le
    have hstepw : (insert w s).card = (step a w).card + 1 := by
      have h1 : step a b ⊆ step a w := step_subset_step hbw.le
      have h2 : (step a w).card ≤ (directions (insert w s)).card :=
        Finset.card_le_card (step_subset_directions (Finset.mem_insert_of_mem ha)
          (Finset.mem_insert_self _ _))
      have h3 := ht.card_le_card_step_succ (Finset.mem_insert_of_mem ha) hbot' htop'
      have h4 := Finset.card_le_card h1
      omega
    obtain ⟨i, hi1, hi2⟩ := ht.exists_eq_top_add_single ha hbot hb htop hbw hstepw
    have hconsti : ∀ z ∈ s, z i = b i := ht.const_of_insert_top htop hi1
    have hbi : b i ≠ 0 := by
      intro h0
      have hmem : ((i, true) : Label n) ∈ signs (insert w s) :=
        mem_signs_true.2 ⟨w, Finset.mem_insert_self _ _, by omega⟩
      obtain ⟨z, hz, hzi⟩ := mem_signs_true.1 (hsubs hmem)
      rw [hconsti z hz] at hzi
      omega
    have hic : i = c := by
      refine huniq i (mem_directions.2 ⟨b, hb, hbi⟩) ?_
      simp only [mem_step]
      have := hconsti a ha
      omega
    subst hic
    have hweq : w = raise b i := by
      refine funext fun j => ?_
      rcases eq_or_ne j i with rfl | hne
      · rw [raise_apply_self]; omega
      · rw [raise_apply_of_ne _ hne]; exact (hi2 j hne).symm
    rw [hweq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- **A simplex with as many vertices as directions and no extremal coordinate has exactly
two extensions keeping its signs.** -/
theorem card_extensions_eq_two (hs : IsSimplex N s)
    (hcard : s.card = (directions s).card) (hext : ¬ IsExtremal N s) :
    (extensions N s (signs s)).card = 2 := by
  obtain ⟨a, ha, hbot⟩ := hs.exists_bot
  obtain ⟨b, hb, htop⟩ := hs.exists_top
  have hsub : step a b ⊆ directions s := step_subset_directions ha hb
  have hle : s.card ≤ (step a b).card + 1 := hs.card_le_card_step_succ ha hbot htop
  have hle2 : (step a b).card ≤ (directions s).card := Finset.card_le_card hsub
  rcases eq_or_lt_of_le hle2 with heq | hlt
  · exact card_extensions_eq_two_of_full hs ha hbot hb htop hcard (by omega)
  · have hsat : s.card = (step a b).card + 1 := by omega
    obtain ⟨c, huniq, hconst, hne⟩ :=
      exists_const_direction hbot htop hcard hsat hsub
    have hgrid := mem_grid.1 (hs.subset_grid ha) c
    have hbc : b c = a c := hconst b hb
    have hcN : a c ≠ (N : ℤ) := fun h =>
      hext ⟨c, Or.inl fun z hz => by rw [hconst z hz, h]⟩
    have hcN' : a c ≠ -(N : ℤ) := fun h =>
      hext ⟨c, Or.inr fun z hz => by rw [hconst z hz, h]⟩
    have h1 : lower a c ∈ extensions N s (signs s) :=
      lower_mem_extensions hs ha hbot hconst hne (by omega)
    have h2 : raise b c ∈ extensions N s (signs s) :=
      raise_mem_extensions hs hb htop (fun z hz => by rw [hconst z hz, hbc]) (by omega)
        (by omega)
    have hset : extensions N s (signs s) = {lower a c, raise b c} :=
      Finset.Subset.antisymm
        (extensions_subset_of_saturated hs ha hbot hb htop hcard hsat huniq) (by
          intro w hw
          rcases Finset.mem_insert.1 hw with rfl | hw'
          · exact h1
          · rw [Finset.mem_singleton] at hw'
            subst hw'
            exact h2)
    have hne2 : lower a c ∉ ({raise b c} : Finset (Fin n → ℤ)) := by
      simp only [Finset.mem_singleton]
      intro hcon
      have h := congrFun hcon c
      rw [lower_apply_self, raise_apply_self, hbc] at h
      omega
    rw [hset, Finset.card_insert_of_notMem hne2, Finset.card_singleton]

/-- **A simplex with as many vertices as directions and one extremal coordinate has exactly
one extension keeping its signs.**  The cube blocks the other one. -/
theorem card_extensions_eq_one_of_isExtremal (hs : IsSimplex N s) (hN : 0 < N)
    (hcard : s.card = (directions s).card) (hext : IsExtremal N s) :
    (extensions N s (signs s)).card = 1 := by
  obtain ⟨a, ha, hbot⟩ := hs.exists_bot
  obtain ⟨b, hb, htop⟩ := hs.exists_top
  obtain ⟨d, hd⟩ := hext
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hsub : step a b ⊆ directions s := step_subset_directions ha hb
  have hle : s.card ≤ (step a b).card + 1 := hs.card_le_card_step_succ ha hbot htop
  have hle2 : (step a b).card ≤ (directions s).card := Finset.card_le_card hsub
  have hda : a d = (N : ℤ) ∨ a d = -(N : ℤ) := by
    rcases hd with h | h
    · exact Or.inl (h a ha)
    · exact Or.inr (h a ha)
  have hdb : b d = a d := by
    rcases hd with h | h
    · rw [h a ha, h b hb]
    · rw [h a ha, h b hb]
  have hdd : d ∈ directions s := mem_directions.2 ⟨a, ha, by omega⟩
  have hds : d ∉ step a b := by
    simp only [mem_step]
    omega
  have hlt : (step a b).card < (directions s).card :=
    lt_of_le_of_ne hle2 fun hcon => hds (by
      rw [Finset.eq_of_subset_of_card_le hsub (le_of_eq hcon.symm)]
      exact hdd)
  have hsat : s.card = (step a b).card + 1 := by omega
  obtain ⟨c, huniq, hconst, hne⟩ := exists_const_direction hbot htop hcard hsat hsub
  have hdc : d = c := huniq d hdd hds
  subst hdc
  have hgrid := mem_grid.1 (hs.subset_grid ha) d
  have hsubset := extensions_subset_of_saturated hs ha hbot hb htop hcard hsat huniq
  rcases hda with hac | hac
  · -- the coordinate sits at `N`, so only lowering it is possible
    have h1 : lower a d ∈ extensions N s (signs s) :=
      lower_mem_extensions hs ha hbot hconst hne (by omega)
    have h2 : raise b d ∉ extensions N s (signs s) := by
      intro hcon
      obtain ⟨-, ht, -⟩ := mem_extensions.1 hcon
      have h := mem_grid.1 (ht.subset_grid (Finset.mem_insert_self _ _)) d
      rw [raise_apply_self] at h
      omega
    refine Finset.card_eq_one.2 ⟨lower a d, Finset.Subset.antisymm (fun w hw => ?_)
      (fun w hw => ?_)⟩
    · rcases Finset.mem_insert.1 (hsubset hw) with heq | heq
      · rw [heq]
        exact Finset.mem_singleton_self _
      · rw [Finset.mem_singleton] at heq
        subst heq
        exact absurd hw h2
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact h1
  · -- the coordinate sits at `-N`, so only raising it is possible
    have h1 : raise b d ∈ extensions N s (signs s) :=
      raise_mem_extensions hs hb htop (fun z hz => by rw [hconst z hz, hdb]) (by omega)
        (by omega)
    have h2 : lower a d ∉ extensions N s (signs s) := by
      intro hcon
      obtain ⟨-, ht, -⟩ := mem_extensions.1 hcon
      have h := mem_grid.1 (ht.subset_grid (Finset.mem_insert_self _ _)) d
      rw [lower_apply_self] at h
      omega
    refine Finset.card_eq_one.2 ⟨raise b d, Finset.Subset.antisymm (fun w hw => ?_)
      (fun w hw => ?_)⟩
    · rcases Finset.mem_insert.1 (hsubset hw) with heq | heq
      · subst heq
        exact absurd hw h2
      · rw [Finset.mem_singleton] at heq
        rw [heq]
        exact Finset.mem_singleton_self _
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact h1

/- ### Reflection -/

/-- The reflection of a simplex in the origin is a simplex. -/
theorem IsSimplex.neg (hs : IsSimplex N s) : IsSimplex N (-s) where
  nonempty := hs.nonempty.neg
  subset_grid := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hx
    exact neg_mem_grid (hs.subset_grid hy)
  chain := by
    rintro x hx y hy hne
    obtain ⟨x', hx', rfl⟩ := Finset.mem_neg.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_neg.1 hy
    have hne' : x' ≠ y' := fun h => hne (by rw [h])
    rcases hs.chain hx' hy' hne' with h | h
    · refine Or.inr (Pi.le_def.2 fun i => ?_)
      have := Pi.le_def.1 h i
      simp only [Pi.neg_apply]
      omega
    · refine Or.inl (Pi.le_def.2 fun i => ?_)
      have := Pi.le_def.1 h i
      simp only [Pi.neg_apply]
      omega
  sub_le_one := by
    intro x hx y hy i
    obtain ⟨x', hx', rfl⟩ := Finset.mem_neg.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_neg.1 hy
    have h1 := hs.sub_le_one x' hx' y' hy' i
    have h2 := hs.sub_le_one y' hy' x' hx' i
    simp only [Pi.neg_apply]
    omega

/-- Reflection reverses every sign. -/
theorem mem_signs_neg {p : Label n} : p ∈ signs (-s) ↔ negLabel p ∈ signs s := by
  obtain ⟨i, b⟩ := p
  cases b
  · rw [mem_signs_false]
    show (∃ x ∈ -s, x i < 0) ↔ (i, true) ∈ signs s
    rw [mem_signs_true]
    constructor
    · rintro ⟨x, hx, hxi⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hx
      exact ⟨y, hy, by simpa using hxi⟩
    · rintro ⟨y, hy, hyi⟩
      exact ⟨-y, Finset.mem_neg.2 ⟨y, hy, rfl⟩, by simpa using hyi⟩
  · rw [mem_signs_true]
    show (∃ x ∈ -s, 0 < x i) ↔ (i, false) ∈ signs s
    rw [mem_signs_false]
    constructor
    · rintro ⟨x, hx, hxi⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hx
      exact ⟨y, hy, by simpa using hxi⟩
    · rintro ⟨y, hy, hyi⟩
      exact ⟨-y, Finset.mem_neg.2 ⟨y, hy, rfl⟩, by simpa using hyi⟩

/-- Reflection reverses the set of signs. -/
theorem signs_neg (s : Finset (Fin n → ℤ)) : signs (-s) = (signs s).image negLabel := by
  ext p
  rw [mem_signs_neg, mem_image_negLabel]

/-- Reflection preserves the directions, since reversing a label keeps its coordinate. -/
theorem directions_neg (s : Finset (Fin n → ℤ)) : directions (-s) = directions s := by
  rw [directions, directions, signs_neg, Finset.image_image]
  exact Finset.image_congr fun p _ => negLabel_fst p

end GridSimplex
end

section
/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/

/-
# Tucker's lemma

Tucker's lemma is the combinatorial form of the Borsuk–Ulam theorem.  Label every point of
the integer cube `[-N, N]ⁿ` by a coordinate together with a sign, so that antipodal
boundary points receive opposite labels.  Then some simplex of the Kuhn triangulation
carries two opposite labels.

The proof is a parity argument.  Call a simplex **happy** when every sign it carries also
occurs as a label on it, and call a happy simplex a **door** of a larger one when it is
that one with a vertex deleted and already carries all of its signs.  Counting the doors
from their two ends makes the total number of doors at a happy simplex even, so an even
number of happy simplices have an odd number of them.

Assuming no simplex carries two opposite labels, a happy simplex comes in one of three
shapes, according to whether it has as many vertices as directions or one more, and
whether its labels are distinct.  Each shape has exactly two doors, with two exceptions:
the origin alone, and the simplices with one coordinate at the boundary of the cube.
Reflection in the origin pairs the latter up, so an odd number of happy simplices have an
odd number of doors.  That is the contradiction.

## Main results

* `GridSimplex.IsHappy` — a simplex all of whose signs occur as labels on it.
* `GridSimplex.odd_deg_iff` — the happy simplices with an odd number of doors are the
  origin alone and those with a coordinate at the boundary of the cube.
* `GridSimplex.tucker` — Tucker's lemma.
-/

namespace Finset

/-- **A finite set carrying a fixed-point-free involution has even cardinality.**  Its
elements fall into pairs. -/
theorem even_card_of_involutive {α : Type*} [DecidableEq α] {B : Finset α} {f : α → α}
    (hmaps : ∀ x ∈ B, f x ∈ B) (hinv : ∀ x ∈ B, f (f x) = x) (hne : ∀ x ∈ B, f x ≠ x) :
    Even B.card := by
  suffices h : ∀ m : ℕ, ∀ C : Finset α, C.card ≤ m → (∀ x ∈ C, f x ∈ C) →
      (∀ x ∈ C, f (f x) = x) → (∀ x ∈ C, f x ≠ x) → Even C.card from
    h B.card B le_rfl hmaps hinv hne
  intro m
  induction m with
  | zero =>
    intro C hC _ _ _
    rw [Nat.le_zero.1 hC]
    exact ⟨0, rfl⟩
  | succ m ih =>
    intro C hC hmapsC hinvC hneC
    rcases C.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hfx : f x ∈ C := hmapsC x hx
      have hxfx : x ≠ f x := fun h => hneC x hx h.symm
      have hfxe : f x ∈ C.erase x := Finset.mem_erase.2 ⟨fun h => hxfx h.symm, hfx⟩
      have hpair : ({x, f x} : Finset α) ⊆ C := by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy'
        · exact hx
        · rw [Finset.mem_singleton] at hy'
          subst hy'
          exact hfx
      have h2 : 2 ≤ C.card := by
        have h := Finset.card_le_card hpair
        rwa [Finset.card_insert_of_notMem (by simpa using hxfx), Finset.card_singleton] at h
      have hcard : C.card = ((C.erase x).erase (f x)).card + 2 := by
        rw [Finset.card_erase_of_mem hfxe, Finset.card_erase_of_mem hx]
        omega
      have hmapsD : ∀ y ∈ (C.erase x).erase (f x), f y ∈ (C.erase x).erase (f x) := by
        intro y hy
        rw [Finset.mem_erase, Finset.mem_erase] at hy ⊢
        obtain ⟨hy1, hy2, hy3⟩ := hy
        refine ⟨fun h => hy2 ?_, fun h => hy1 ?_, hmapsC y hy3⟩
        · rw [← hinvC y hy3, h, hinvC x hx]
        · rw [← hinvC y hy3, h]
      have hsubD : (C.erase x).erase (f x) ⊆ C :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have := ih ((C.erase x).erase (f x)) (by omega) hmapsD
        (fun y hy => hinvC y (hsubD hy)) (fun y hy => hneC y (hsubD hy))
      rw [hcard]
      exact this.add even_two

end Finset


open Finset
open scoped Pointwise

namespace GridSimplex

variable {n N : ℕ} {lam : (Fin n → ℤ) → Label n} {s : Finset (Fin n → ℤ)}

/- ### Labels on a simplex -/

/-- The labels occurring on a set of grid points. -/
def labels (lam : (Fin n → ℤ) → Label n) (s : Finset (Fin n → ℤ)) : Finset (Label n) :=
  s.image lam

/-- A label occurs on a set exactly when some point carries it. -/
@[simp]
theorem mem_labels {p : Label n} : p ∈ labels lam s ↔ ∃ x ∈ s, lam x = p :=
  Finset.mem_image

/-- A set carries at most as many labels as it has points. -/
theorem card_labels_le : (labels lam s).card ≤ s.card := Finset.card_image_le

/-- Labels of a subset are labels. -/
theorem labels_subset {t : Finset (Fin n → ℤ)} (hts : t ⊆ s) :
    labels lam t ⊆ labels lam s :=
  Finset.image_subset_image hts

/-- Reflecting a set of points reverses its labels, provided the labelling is antipodal
there. -/
theorem labels_neg_of_antipodal
    (h : ∀ x ∈ s, lam (-x) = negLabel (lam x)) :
    labels lam (-s) = (labels lam s).image negLabel := by
  ext p
  simp only [mem_labels, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.1 hx
    exact ⟨lam y, ⟨y, hy, rfl⟩, (h y hy).symm ▸ rfl⟩
  · rintro ⟨q, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨-y, Finset.mem_neg.2 ⟨y, hy, rfl⟩, h y hy⟩

/- ### Happy simplices -/

/-- A simplex is **happy** for a labelling when every sign it carries occurs as a label on
it.  The parity argument runs over the happy simplices. -/
structure IsHappy (N : ℕ) (lam : (Fin n → ℤ) → Label n) (s : Finset (Fin n → ℤ)) :
    Prop where
  /-- A happy simplex is a simplex. -/
  isSimplex : IsSimplex N s
  /-- Every sign it carries occurs as a label. -/
  signs_subset : signs s ⊆ labels lam s

/-- A happy simplex has at least as many labels as directions. -/
theorem IsHappy.card_directions_le (h : IsHappy N lam s) :
    (directions s).card ≤ (labels lam s).card := by
  rw [← h.isSimplex.card_signs]
  exact Finset.card_le_card h.signs_subset

/-- **The three shapes of a happy simplex.**

Writing `k` for the number of directions, a happy simplex has either `k + 1` vertices and
`k + 1` labels, or `k + 1` vertices and `k` labels, or `k` vertices and `k` labels. -/
theorem IsHappy.shape (h : IsHappy N lam s) :
    (s.card = (directions s).card + 1 ∧ (labels lam s).card = (directions s).card + 1) ∨
      (s.card = (directions s).card + 1 ∧ (labels lam s).card = (directions s).card) ∨
      (s.card = (directions s).card ∧ (labels lam s).card = (directions s).card) := by
  have h1 : (directions s).card ≤ (labels lam s).card := h.card_directions_le
  have h2 : (labels lam s).card ≤ s.card := card_labels_le
  have h3 : s.card ≤ (directions s).card + 1 := h.isSimplex.card_le_card_directions_succ
  omega

/- ### Doors

Two happy simplices are joined when one is obtained from the other by deleting a vertex
and already carries all of its signs.  The parity argument counts these incidences twice,
once from each end. -/

/-- `σ` is a **door** of `τ`: it is `τ` with one vertex deleted, still nonempty, and it
already carries every sign of `τ`. -/
structure IsDoor (N : ℕ) (lam : (Fin n → ℤ) → Label n) (σ τ : Finset (Fin n → ℤ)) :
    Prop where
  /-- The larger set is a simplex. -/
  isSimplex : IsSimplex N τ
  /-- The smaller one is contained in it. -/
  subset : σ ⊆ τ
  /-- with one vertex fewer. -/
  card_succ : σ.card + 1 = τ.card
  /-- The smaller one is not empty. -/
  nonempty : σ.Nonempty
  /-- Every sign of the larger one already occurs as a label on the smaller one. -/
  signs_subset : signs τ ⊆ labels lam σ

/-- The smaller end of a door is happy. -/
theorem IsDoor.happy_left {σ τ : Finset (Fin n → ℤ)} (h : IsDoor N lam σ τ) :
    IsHappy N lam σ where
  isSimplex := h.isSimplex.subset h.subset h.nonempty
  signs_subset := (_root_.GridSimplex.signs_subset h.subset).trans h.signs_subset

/-- The larger end of a door is happy. -/
theorem IsDoor.happy_right {σ τ : Finset (Fin n → ℤ)} (h : IsDoor N lam σ τ) :
    IsHappy N lam τ where
  isSimplex := h.isSimplex
  signs_subset := h.signs_subset.trans (_root_.GridSimplex.labels_subset h.subset)

/- ### Counting incidences -/

open scoped Classical in
/-- The happy simplices of the grid, as a finite set. -/
noncomputable def happySet (N : ℕ) (lam : (Fin n → ℤ) → Label n) :
    Finset (Finset (Fin n → ℤ)) :=
  (grid n N).powerset.filter (IsHappy N lam)

/-- A happy simplex belongs to `happySet`. -/
theorem mem_happySet {N : ℕ} : s ∈ happySet N lam ↔ IsHappy N lam s := by
  classical
  rw [happySet, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.isSimplex.subset_grid, h⟩⟩

open scoped Classical in
/-- The number of doors above a happy simplex. -/
noncomputable def upDeg (N : ℕ) (lam : (Fin n → ℤ) → Label n)
    (σ : Finset (Fin n → ℤ)) : ℕ :=
  ((happySet N lam).filter (IsDoor N lam σ)).card

open scoped Classical in
/-- The number of doors below a happy simplex. -/
noncomputable def downDeg (N : ℕ) (lam : (Fin n → ℤ) → Label n)
    (τ : Finset (Fin n → ℤ)) : ℕ :=
  ((happySet N lam).filter fun σ => IsDoor N lam σ τ).card

/-- The degree of a happy simplex in the incidence graph. -/
noncomputable def deg (N : ℕ) (lam : (Fin n → ℤ) → Label n)
    (σ : Finset (Fin n → ℤ)) : ℕ :=
  upDeg N lam σ + downDeg N lam σ

/-- **Every door is counted once from each end**, so the two degree sums agree.  Both are
the number of doors, summed in the two possible orders. -/
theorem sum_upDeg_eq_sum_downDeg (N : ℕ) (lam : (Fin n → ℤ) → Label n) :
    ∑ σ ∈ happySet N lam, upDeg N lam σ = ∑ τ ∈ happySet N lam, downDeg N lam τ := by
  classical
  simp only [upDeg, downDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- The total degree is even, because it counts every door twice. -/
theorem even_sum_deg (N : ℕ) (lam : (Fin n → ℤ) → Label n) :
    Even (∑ σ ∈ happySet N lam, deg N lam σ) := by
  have hsplit : ∑ σ ∈ happySet N lam, deg N lam σ =
      (∑ σ ∈ happySet N lam, upDeg N lam σ) +
        ∑ σ ∈ happySet N lam, downDeg N lam σ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => rfl
  rw [hsplit, ← sum_upDeg_eq_sum_downDeg]
  exact ⟨_, rfl⟩

/-- **The number of happy simplices of odd degree is even.** -/
theorem even_card_odd_deg (N : ℕ) (lam : (Fin n → ℤ) → Label n) :
    Even ((happySet N lam).filter fun σ => Odd (deg N lam σ)).card := by
  classical
  exact (Finset.even_sum_iff_even_card_odd _).1 (even_sum_deg N lam)

/-- In the two shapes with as many labels as vertices, the labelling is injective on the
simplex. -/
theorem injOn_lam_of_card (hcard : (labels lam s).card = s.card) : Set.InjOn lam s := by
  refine Finset.injOn_of_card_image_eq ?_
  rw [← labels]
  exact hcard

/-- Deleting a vertex from a simplex on which the labelling is injective removes exactly
its label. -/
theorem labels_erase_of_injOn (hinj : Set.InjOn lam s) {w : Fin n → ℤ} (hw : w ∈ s) :
    labels lam (s.erase w) = (labels lam s).erase (lam w) := by
  ext p
  constructor
  · intro hp
    obtain ⟨x, hx, rfl⟩ := mem_labels.1 hp
    obtain ⟨hxw, hxs⟩ := Finset.mem_erase.1 hx
    exact Finset.mem_erase.2
      ⟨fun hcon => hxw (hinj hxs hw hcon), mem_labels.2 ⟨x, hxs, rfl⟩⟩
  · intro hp
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hp
    obtain ⟨x, hx, rfl⟩ := mem_labels.1 hmem
    exact mem_labels.2 ⟨x, Finset.mem_erase.2 ⟨fun hcon => hne (by rw [hcon]), hx⟩, rfl⟩

/- ### Doors as insertions and deletions

The doors above a happy simplex are its extensions by one vertex, and the doors below it
are its deletions of one vertex.  This turns both degrees into counts of vertices. -/

open scoped Classical in
/-- The doors above a happy simplex are the vertices extending it without adding a label
it does not already carry. -/
theorem upDeg_eq_card_extensions (h : IsHappy N lam s) :
    upDeg N lam s = (extensions N s (labels lam s)).card := by
  classical
  have hdoor : ∀ w ∈ extensions N s (labels lam s), IsDoor N lam s (insert w s) := by
    intro w hw
    obtain ⟨hws, ht, hsub⟩ := mem_extensions.1 hw
    exact { isSimplex := ht
            subset := Finset.subset_insert _ _
            card_succ := (Finset.card_insert_of_notMem hws).symm
            nonempty := h.isSimplex.nonempty
            signs_subset := hsub }
  refine (Finset.card_nbij (fun w => insert w s) (fun w hw => ?_) (fun w₁ h₁ w₂ h₂ heq => ?_)
    (fun τ hτ => ?_)).symm
  · rw [Finset.mem_coe] at hw
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨mem_happySet.2 (hdoor w hw).happy_right, hdoor w hw⟩
  · rw [Finset.mem_coe, mem_extensions] at h₁
    have heq' : insert w₁ s = insert w₂ s := heq
    have hmem : w₁ ∈ insert w₂ s := by
      rw [← heq']
      exact Finset.mem_insert_self w₁ s
    rcases Finset.mem_insert.1 hmem with hcase | hcase
    · exact hcase
    · exact absurd hcase h₁.1
  · rw [Finset.mem_coe, Finset.mem_filter] at hτ
    obtain ⟨w, hws, hins⟩ := Finset.exists_eq_insert_iff.2 ⟨hτ.2.subset, hτ.2.card_succ⟩
    refine ⟨w, ?_, hins⟩
    rw [Finset.mem_coe, mem_extensions]
    refine ⟨hws, by rw [hins]; exact hτ.2.isSimplex, by rw [hins]; exact hτ.2.signs_subset⟩

open scoped Classical in
/-- The doors below a happy simplex are the vertices whose deletion leaves a nonempty set
still carrying all of its signs. -/
theorem downDeg_eq_card_filter (hs : IsSimplex N s) :
    downDeg N lam s =
      (s.filter fun w => (s.erase w).Nonempty ∧ signs s ⊆ labels lam (s.erase w)).card := by
  classical
  refine (Finset.card_nbij (fun w => s.erase w) (fun w hw => ?_) (fun w₁ h₁ w₂ h₂ heq => ?_)
    (fun σ hσ => ?_)).symm
  · rw [Finset.mem_coe, Finset.mem_filter] at hw
    obtain ⟨hws, hne, hsub⟩ := hw
    have hpos : 0 < s.card := Finset.card_pos.2 ⟨w, hws⟩
    have hd : IsDoor N lam (s.erase w) s :=
      { isSimplex := hs
        subset := Finset.erase_subset _ _
        card_succ := by rw [Finset.card_erase_of_mem hws]; omega
        nonempty := hne
        signs_subset := hsub }
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨mem_happySet.2 hd.happy_left, hd⟩
  · rw [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    exact Finset.erase_injOn s h₁.1 h₂.1 heq
  · rw [Finset.mem_coe, Finset.mem_filter] at hσ
    obtain ⟨w, hws, hins⟩ := Finset.exists_eq_insert_iff.2 ⟨hσ.2.subset, hσ.2.card_succ⟩
    have hwmem : w ∈ s := by
      rw [← hins]
      exact Finset.mem_insert_self w σ
    have herase : s.erase w = σ := by rw [← hins, Finset.erase_insert hws]
    refine ⟨w, ?_, herase⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨hwmem, by rw [herase]; exact hσ.2.nonempty, by rw [herase]; exact hσ.2.signs_subset⟩

/- ### Labellings without a complementary edge

Tucker's lemma is proved by contradiction, so the whole degree computation runs under the
assumption that no simplex carries a pair of opposite labels. -/

/-- A labelling **separates** when no simplex of the grid carries a pair of opposite
labels.  Tucker's lemma says that a labelling antipodal on the boundary never does. -/
def Separates (N : ℕ) (lam : (Fin n → ℤ) → Label n) : Prop :=
  ∀ t : Finset (Fin n → ℤ), IsSimplex N t → ∀ x ∈ t, ∀ y ∈ t, lam x ≠ negLabel (lam y)

/-- Under a separating labelling a simplex carries no pair of opposite labels. -/
theorem Separates.negLabel_not_mem_labels (hsep : Separates N lam) (hs : IsSimplex N s)
    {l : Label n} (hl : l ∈ labels lam s) : negLabel l ∉ labels lam s := by
  intro hcon
  obtain ⟨x, hx, rfl⟩ := mem_labels.1 hl
  obtain ⟨y, hy, hy'⟩ := mem_labels.1 hcon
  exact hsep s hs y hy x hx hy'

/- ### The shape of a happy simplex, in detail -/

/-- A happy simplex with as many labels as directions carries exactly its signs. -/
theorem IsHappy.labels_eq_signs (h : IsHappy N lam s)
    (hl : (labels lam s).card = (directions s).card) : labels lam s = signs s :=
  (Finset.eq_of_subset_of_card_le h.signs_subset
    (by rw [hl, h.isSimplex.card_signs])).symm

/-- A happy simplex with one more label than directions carries exactly one label beyond
its signs. -/
theorem IsHappy.exists_extra_label (h : IsHappy N lam s)
    (hl : (labels lam s).card = (directions s).card + 1) :
    ∃ l, l ∉ signs s ∧ labels lam s = insert l (signs s) := by
  classical
  have hsigns : (signs s).card = (directions s).card := h.isSimplex.card_signs
  have hcs : (labels lam s \ signs s).card = 1 := by
    rw [Finset.card_sdiff_of_subset h.signs_subset]
    omega
  obtain ⟨l, hlset⟩ := Finset.card_eq_one.1 hcs
  obtain ⟨hlmem, hlnot⟩ : l ∈ labels lam s ∧ l ∉ signs s :=
    Finset.mem_sdiff.1 (by rw [hlset]; exact Finset.mem_singleton_self l)
  refine ⟨l, hlnot, (Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hlmem h.signs_subset) ?_).symm⟩
  rw [Finset.card_insert_of_notMem hlnot]
  omega

/-- Deleting a vertex keeps all the signs exactly when its label is not a sign. -/
theorem subset_labels_erase_iff (hinj : Set.InjOn lam s) (hsub : signs s ⊆ labels lam s)
    {w : Fin n → ℤ} (hw : w ∈ s) :
    signs s ⊆ labels lam (s.erase w) ↔ lam w ∉ signs s := by
  classical
  rw [labels_erase_of_injOn hinj hw]
  constructor
  · intro h hcon
    exact (Finset.mem_erase.1 (h hcon)).1 rfl
  · intro h q hq
    exact Finset.mem_erase.2 ⟨fun hcon => h (hcon ▸ hq), hsub hq⟩

/-- Exactly one vertex carries a given label when the labelling is injective. -/
theorem card_filter_lam_eq {l : Label n} [DecidablePred fun w : Fin n → ℤ => lam w = l]
    (hinj : Set.InjOn lam s) (hl : l ∈ labels lam s) :
    (s.filter fun w => lam w = l).card = 1 := by
  obtain ⟨x, hx, hxl⟩ := mem_labels.1 hl
  refine Finset.card_eq_one.2 ⟨x, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun hy => hinj hy.1 hx (by rw [hy.2, hxl]), fun hy => ⟨hy ▸ hx, hy ▸ hxl⟩⟩

/- ### The degree of a happy simplex

A happy simplex has degree two, except for the origin alone and for those with one
coordinate at the boundary of the cube, which have degree one. -/

/-- A happy simplex with one more vertex and one more label than it has directions has
exactly one door above it. -/
theorem upDeg_eq_one_of_card_eq_succ (hsep : Separates N lam) (hN : 0 < N)
    (h : IsHappy N lam s) (hv : s.card = (directions s).card + 1)
    (hl : (labels lam s).card = (directions s).card + 1) : upDeg N lam s = 1 := by
  obtain ⟨l, hlnot, hlabels⟩ := h.exists_extra_label hl
  rw [upDeg_eq_card_extensions h, hlabels]
  refine card_extensions_eq_one h.isSimplex hN hv hlnot fun hcon => ?_
  have h1 : l ∈ labels lam s := by
    rw [hlabels]
    exact Finset.mem_insert_self _ _
  exact hsep.negLabel_not_mem_labels h.isSimplex h1 (h.signs_subset hcon)

open scoped Classical in
/-- A happy simplex with one more vertex and one more label than it has directions, and
with more than one vertex, has exactly one door below it. -/
theorem downDeg_eq_one_of_card_eq_succ (h : IsHappy N lam s)
    (hv : s.card = (directions s).card + 1)
    (hl : (labels lam s).card = (directions s).card + 1) (h2 : 2 ≤ s.card) :
    downDeg N lam s = 1 := by
  classical
  obtain ⟨l, hlnot, hlabels⟩ := h.exists_extra_label hl
  have hinj : Set.InjOn lam s := injOn_lam_of_card (by omega)
  rw [downDeg_eq_card_filter h.isSimplex]
  have hfilter : (s.filter fun w => (s.erase w).Nonempty ∧ signs s ⊆ labels lam (s.erase w))
      = s.filter fun w => lam w = l := by
    refine Finset.filter_congr fun w hw => ?_
    have hne : (s.erase w).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hw]
      omega
    rw [subset_labels_erase_iff hinj h.signs_subset hw]
    constructor
    · rintro ⟨-, hns⟩
      have hmem : lam w ∈ labels lam s := mem_labels.2 ⟨w, hw, rfl⟩
      rw [hlabels, Finset.mem_insert] at hmem
      rcases hmem with hcase | hcase
      · exact hcase
      · exact absurd hcase hns
    · intro heq
      exact ⟨hne, by rw [heq]; exact hlnot⟩
  rw [hfilter]
  exact card_filter_lam_eq hinj (by rw [hlabels]; exact Finset.mem_insert_self _ _)

open scoped Classical in
/-- A single vertex has no door below it. -/
theorem downDeg_eq_zero_of_card_eq_one (hs : IsSimplex N s) (h1 : s.card = 1) :
    downDeg N lam s = 0 := by
  classical
  rw [downDeg_eq_card_filter hs, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw hcon
  have hpos := Finset.card_pos.2 hcon.1
  rw [Finset.card_erase_of_mem hw, h1] at hpos
  omega

/-- A happy simplex with one more vertex than labels has no door above it. -/
theorem upDeg_eq_zero_of_card_labels_eq (h : IsHappy N lam s)
    (hv : s.card = (directions s).card + 1)
    (hl : (labels lam s).card = (directions s).card) : upDeg N lam s = 0 := by
  rw [upDeg_eq_card_extensions h, h.labels_eq_signs hl, extensions_eq_empty h.isSimplex hv,
    Finset.card_empty]

open scoped Classical in
/-- A happy simplex with one more vertex than labels has exactly two doors below it: the
two vertices sharing a label. -/
theorem downDeg_eq_two_of_card_labels_eq (h : IsHappy N lam s)
    (hv : s.card = (directions s).card + 1)
    (hl : (labels lam s).card = (directions s).card) : downDeg N lam s = 2 := by
  classical
  have hls : labels lam s = signs s := h.labels_eq_signs hl
  have hlt : (labels lam s).card < s.card := by omega
  obtain ⟨u, hu, v, hv', huv, huvl⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (fun x hx => mem_labels.2 ⟨x, hx, rfl⟩)
  have hvu : v ∈ s.erase u := Finset.mem_erase.2 ⟨fun hc => huv hc.symm, hv'⟩
  have huv' : u ∈ s.erase v := Finset.mem_erase.2 ⟨huv, hu⟩
  -- deleting either of the two leaves all the labels
  have hlabels : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → lam x = lam y →
      labels lam (s.erase x) = labels lam s := by
    intro x hx y hy hxy hxyl
    refine Finset.Subset.antisymm (labels_subset (Finset.erase_subset _ _)) fun q hq => ?_
    obtain ⟨z, hz, rfl⟩ := mem_labels.1 hq
    rcases eq_or_ne z x with rfl | hzx
    · exact mem_labels.2 ⟨y, Finset.mem_erase.2 ⟨fun hc => hxy hc.symm, hy⟩, hxyl.symm⟩
    · exact mem_labels.2 ⟨z, Finset.mem_erase.2 ⟨hzx, hz⟩, rfl⟩
  have hlu : labels lam (s.erase u) = labels lam s := hlabels u hu v hv' huv huvl
  have hlv : labels lam (s.erase v) = labels lam s :=
    hlabels v hv' u hu (fun hc => huv hc.symm) huvl.symm
  -- outside the two, the labelling is injective
  have hinj : Set.InjOn lam (s.erase u) := by
    refine injOn_lam_of_card ?_
    rw [hlu, Finset.card_erase_of_mem hu]
    omega
  rw [downDeg_eq_card_filter h.isSimplex]
  have hfilter : (s.filter fun w => (s.erase w).Nonempty ∧ signs s ⊆ labels lam (s.erase w))
      = {u, v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, -, hsub⟩
      -- the label of `w` survives the deletion, so some other vertex carries it
      have hmem : lam w ∈ labels lam (s.erase w) := by
        rw [← hls] at hsub
        exact hsub (mem_labels.2 ⟨w, hw, rfl⟩)
      obtain ⟨z, hz, hzl⟩ := mem_labels.1 hmem
      obtain ⟨hzw, hzs⟩ := Finset.mem_erase.1 hz
      by_contra hcon
      have hwu : w ≠ u := fun hc => hcon (Or.inl hc)
      have hwv : w ≠ v := fun hc => hcon (Or.inr hc)
      rcases eq_or_ne z u with rfl | hzu
      · exact hwv (hinj (Finset.mem_erase.2 ⟨hwu, hw⟩) hvu (by rw [← hzl, huvl]))
      · exact hzw (hinj (Finset.mem_erase.2 ⟨hzu, hzs⟩) (Finset.mem_erase.2 ⟨hwu, hw⟩) hzl)
    · rintro (rfl | rfl)
      · exact ⟨hu, ⟨v, hvu⟩, by rw [hlu, hls]⟩
      · exact ⟨hv', ⟨u, huv'⟩, by rw [hlv, hls]⟩
  rw [hfilter, Finset.card_insert_of_notMem (by simpa using huv), Finset.card_singleton]

open scoped Classical in
/-- A happy simplex with as many vertices as directions has no door below it. -/
theorem downDeg_eq_zero_of_card_eq (h : IsHappy N lam s)
    (hv : s.card = (directions s).card)
    (hl : (labels lam s).card = (directions s).card) : downDeg N lam s = 0 := by
  classical
  have hls : labels lam s = signs s := h.labels_eq_signs hl
  have hinj : Set.InjOn lam s := injOn_lam_of_card (by omega)
  rw [downDeg_eq_card_filter h.isSimplex, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw hcon
  refine (subset_labels_erase_iff hinj h.signs_subset hw).1 hcon.2 ?_
  rw [← hls]
  exact mem_labels.2 ⟨w, hw, rfl⟩

/-- A happy simplex with as many vertices as directions and no extremal coordinate has
exactly two doors above it. -/
theorem upDeg_eq_two_of_card_eq (h : IsHappy N lam s) (hv : s.card = (directions s).card)
    (hl : (labels lam s).card = (directions s).card) (hext : ¬ IsExtremal N s) :
    upDeg N lam s = 2 := by
  rw [upDeg_eq_card_extensions h, h.labels_eq_signs hl]
  exact card_extensions_eq_two h.isSimplex hv hext

/-- A happy simplex with as many vertices as directions and one extremal coordinate has
exactly one door above it: the cube blocks the other. -/
theorem upDeg_eq_one_of_card_eq (hN : 0 < N) (h : IsHappy N lam s)
    (hv : s.card = (directions s).card)
    (hl : (labels lam s).card = (directions s).card) (hext : IsExtremal N s) :
    upDeg N lam s = 1 := by
  rw [upDeg_eq_card_extensions h, h.labels_eq_signs hl]
  exact card_extensions_eq_one_of_isExtremal h.isSimplex hN hv hext

/-- **A happy simplex has odd degree exactly when it is the origin alone or has one
coordinate at the boundary of the cube.**

Every other happy simplex has degree two: it is joined to exactly two others. -/
theorem odd_deg_iff (hsep : Separates N lam) (hN : 0 < N) (h : IsHappy N lam s) :
    Odd (deg N lam s) ↔
      s = {0} ∨ (s.card = (directions s).card ∧ IsExtremal N s) := by
  by_cases hb : s.card = (directions s).card
  · -- as many vertices as directions
    have hl : (labels lam s).card = (directions s).card := by
      rcases h.shape with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
      · omega
      · omega
      · exact h2
    have hzero : s ≠ {0} := by
      intro hc
      rw [hc, Finset.card_singleton, directions_singleton_zero, Finset.card_empty] at hb
      omega
    by_cases hext : IsExtremal N s
    · simp only [deg, upDeg_eq_one_of_card_eq hN h hb hl hext,
        downDeg_eq_zero_of_card_eq h hb hl]
      exact ⟨fun _ => Or.inr ⟨hb, hext⟩, fun _ => by decide⟩
    · simp only [deg, upDeg_eq_two_of_card_eq h hb hl hext, downDeg_eq_zero_of_card_eq h hb hl]
      constructor
      · intro hodd
        exact absurd hodd (by decide)
      · rintro (hc | ⟨-, hc⟩)
        · exact absurd hc hzero
        · exact absurd hc hext
  · -- one more vertex than directions
    have hv : s.card = (directions s).card + 1 := by
      rcases h.shape with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    have hnotb : ¬(s.card = (directions s).card ∧ IsExtremal N s) := fun hc => hb hc.1
    rcases h.shape with ⟨-, hl⟩ | ⟨-, hl⟩ | ⟨h1, -⟩
    · -- distinct labels
      by_cases h2 : 2 ≤ s.card
      · have hzero : s ≠ {0} := by
          intro hc
          rw [hc, Finset.card_singleton] at h2
          omega
        simp only [deg, upDeg_eq_one_of_card_eq_succ hsep hN h hv hl,
          downDeg_eq_one_of_card_eq_succ h hv hl h2]
        constructor
        · intro hodd
          exact absurd hodd (by decide)
        · rintro (hc | hc)
          · exact absurd hc hzero
          · exact absurd hc hnotb
      · have h1 : s.card = 1 := by omega
        have hzero : s = {0} := eq_singleton_zero h.isSimplex h1 (by omega)
        simp only [deg, upDeg_eq_one_of_card_eq_succ hsep hN h hv hl,
          downDeg_eq_zero_of_card_eq_one h.isSimplex h1]
        exact ⟨fun _ => Or.inl hzero, fun _ => by decide⟩
    · -- one repeated label
      have hzero : s ≠ {0} := by
        intro hc
        have hpos : 0 < (labels lam s).card :=
          Finset.card_pos.2 (Finset.Nonempty.image h.isSimplex.nonempty lam)
        have hd : (directions s).card = 0 := by
          rw [hc, directions_singleton_zero, Finset.card_empty]
        omega
      simp only [deg, upDeg_eq_zero_of_card_labels_eq h hv hl,
        downDeg_eq_two_of_card_labels_eq h hv hl]
      constructor
      · intro hodd
        exact absurd hodd (by decide)
      · rintro (hc | hc)
        · exact absurd hc hzero
        · exact absurd hc hnotb
    · omega

/- ### Tucker's lemma -/

/-- **Tucker's lemma.**

Label every point of the integer cube `[-N, N]ⁿ` by a coordinate together with a sign, so
that antipodal boundary points get opposite labels.  Then two points of one simplex of the
Kuhn triangulation carry opposite labels.

The proof counts the doors between happy simplices in two ways.  All but two kinds of
happy simplex have exactly two doors; the exceptions are the origin alone and the
simplices with one coordinate at the boundary of the cube, and reflection in the origin
pairs the latter up.  So the number of happy simplices of odd degree is odd, while
counting the doors from both ends makes it even. -/
theorem tucker (hN : 0 < N) (lam : (Fin n → ℤ) → Label n)
    (hlam : ∀ v ∈ grid n N, IsBoundary N v → lam (-v) = negLabel (lam v)) :
    ∃ u ∈ grid n N, ∃ w ∈ grid n N, u ≤ w ∧ (∀ i, w i - u i ≤ 1) ∧
      lam u = negLabel (lam w) := by
  classical
  by_contra hcon
  -- without such a pair, no simplex carries opposite labels
  have hsep : Separates N lam := by
    intro t ht x hx y hy heq
    refine hcon ?_
    rcases eq_or_ne x y with rfl | hne
    · exact ⟨x, ht.subset_grid hx, x, ht.subset_grid hx, le_rfl, fun i => by omega, heq⟩
    rcases ht.chain hx hy hne with hxy | hxy
    · exact ⟨x, ht.subset_grid hx, y, ht.subset_grid hy, hxy,
        fun i => ht.sub_le_one x hx y hy i, heq⟩
    · refine ⟨y, ht.subset_grid hy, x, ht.subset_grid hx, hxy,
        fun i => ht.sub_le_one y hy x hx i, ?_⟩
      rw [heq, negLabel_negLabel]
  -- the origin alone is happy
  have hzerohappy : IsHappy N lam ({0} : Finset (Fin n → ℤ)) :=
    { isSimplex := isSimplex_singleton zero_mem_grid
      signs_subset := by
        rw [signs_singleton_zero]
        exact Finset.empty_subset _ }
  have hzeromem : ({0} : Finset (Fin n → ℤ)) ∈ happySet N lam := mem_happySet.2 hzerohappy
  -- the happy simplices of odd degree are the origin and the extremal faces
  have hoddset : ((happySet N lam).filter fun t => Odd (deg N lam t)) =
      insert ({0} : Finset (Fin n → ℤ))
        ((happySet N lam).filter fun t => t.card = (directions t).card ∧ IsExtremal N t) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨ht, hodd⟩
      rcases (odd_deg_iff hsep hN (mem_happySet.1 ht)).1 hodd with hc | hc
      · exact Or.inl hc
      · exact Or.inr ⟨ht, hc⟩
    · rintro (rfl | ⟨ht, hc⟩)
      · exact ⟨hzeromem, (odd_deg_iff hsep hN hzerohappy).2 (Or.inl rfl)⟩
      · exact ⟨ht, (odd_deg_iff hsep hN (mem_happySet.1 ht)).2 (Or.inr hc)⟩
  have hzeronot : ({0} : Finset (Fin n → ℤ)) ∉
      (happySet N lam).filter fun t => t.card = (directions t).card ∧ IsExtremal N t := by
    intro hmem
    have h := (Finset.mem_filter.1 hmem).2.1
    rw [Finset.card_singleton, directions_singleton_zero, Finset.card_empty] at h
    omega
  -- reflection pairs the extremal faces up
  have hBeven : Even ((happySet N lam).filter
      fun t => t.card = (directions t).card ∧ IsExtremal N t).card := by
    refine Finset.even_card_of_involutive (f := fun t => -t) (fun t ht => ?_)
      (fun t _ => neg_neg t) (fun t ht => ?_)
    · rw [Finset.mem_filter] at ht ⊢
      obtain ⟨ht1, ht2, ht3⟩ := ht
      have hh : IsHappy N lam t := mem_happySet.1 ht1
      have hbd : ∀ z ∈ t, lam (-z) = negLabel (lam z) := by
        intro z hz
        obtain ⟨c, hc⟩ := ht3
        refine hlam z (hh.isSimplex.subset_grid hz) ⟨c, ?_⟩
        rcases hc with hc | hc
        · exact Or.inl (hc z hz)
        · exact Or.inr (hc z hz)
      refine ⟨mem_happySet.2 ⟨hh.isSimplex.neg, ?_⟩, ?_, ht3.neg⟩
      · rw [labels_neg_of_antipodal hbd, signs_neg]
        exact Finset.image_subset_image hh.signs_subset
      · rw [Finset.card_neg, directions_neg]
        exact ht2
    · rw [Finset.mem_filter] at ht
      exact ht.2.2.neg_ne (mem_happySet.1 ht.1).isSimplex.nonempty hN
  have heven := even_card_odd_deg N lam
  rw [hoddset, Finset.card_insert_of_notMem hzeronot] at heven
  obtain ⟨m, hm⟩ := heven
  obtain ⟨m', hm'⟩ := hBeven
  omega


end GridSimplex
end

section
/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/

/-
# The Borsuk–Ulam theorem

The odd-map form of the Borsuk–Ulam theorem states that a continuous odd map from the
sphere `S^{m-1}` into `ℝᵏ` with `k < m` must vanish somewhere.  Equivalently, a
continuous map `S^{m-1} → ℝᵏ` with `k < m` takes the same value at some antipodal
pair.

Mathlib has neither this theorem nor Brouwer's fixed point theorem nor Sperner's lemma,
so it is proved here, combinatorially.  Tucker's lemma (`GridSimplex.tucker`) gives the
cube form `borsukUlam_cube`: a map of the cube into `ℝⁿ`, continuous on the cube and odd
on its boundary, vanishes somewhere.  Lifting the cube onto the unit sphere of the sup
norm and projecting that radially onto the Euclidean sphere gives the statement above.

## Main statements

* `borsukUlam_cube` — Borsuk's antipodal theorem for the cube, from Tucker's lemma by
  uniform continuity.
* `borsukUlam_pi` — the odd-map form on the unit sphere of `Fin m → ℝ` with the sup
  norm, which is the boundary of a cube one dimension lower.
* `borsukUlam` — the theorem itself, on the unit sphere of `EuclideanSpace ℝ (Fin m)`.
* `Function.Odd.exists_norm_eq_and_eq_zero_of_lt_finrank` — the form actually used: on
  *any* finite-dimensional real normed space `E` of dimension `m`, and on the sphere
  of *any* radius `R > 0`, a continuous odd map `E → ℝᵏ` with `k < m` has a zero.
  This is proved from the Euclidean case by transporting along a linear
  homeomorphism and rescaling radially, and it is what makes the lower bound valid
  for an arbitrary norm.
-/

open Metric

/- ### Labelling a point by its largest coordinate

Tucker's lemma is applied to the labelling that sends a point of the cube to the
coordinate in which its image is largest, together with the sign there.  Taking the
**least** such coordinate is what makes the labelling antipodal: reflecting a point
reverses every coordinate of its image without moving the set of largest ones. -/

namespace CubeLabel

variable {n : ℕ}

open scoped Classical in
/-- The coordinates in which `y` attains its sup norm. -/
noncomputable def maxCoords (y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ‖y‖ ≤ |y i|

/-- Membership in `maxCoords`, unfolded. -/
theorem mem_maxCoords {y : Fin n → ℝ} {i : Fin n} : i ∈ maxCoords y ↔ ‖y‖ ≤ |y i| := by
  classical
  simp [maxCoords]

/-- At a largest coordinate the absolute value is the sup norm. -/
theorem abs_eq_norm_of_mem {y : Fin n → ℝ} {i : Fin n} (hi : i ∈ maxCoords y) :
    |y i| = ‖y‖ :=
  le_antisymm (by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i) (mem_maxCoords.1 hi)

/-- Some coordinate attains the sup norm. -/
theorem maxCoords_nonempty (hn : 0 < n) (y : Fin n → ℝ) : (maxCoords y).Nonempty := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun i => |y i|)
      Finset.univ_nonempty
  refine ⟨j, mem_maxCoords.2 ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_)⟩
  simpa [Real.norm_eq_abs] using hj i (Finset.mem_univ i)

/-- Reflection does not move the largest coordinates. -/
theorem maxCoords_neg (y : Fin n → ℝ) : maxCoords (-y) = maxCoords y := by
  classical
  ext i
  simp [mem_maxCoords]

open scoped Classical in
/-- The least coordinate in which `y` attains its sup norm. -/
noncomputable def maxIdx (hn : 0 < n) (y : Fin n → ℝ) : Fin n :=
  (maxCoords y).min' (maxCoords_nonempty hn y)

/-- The chosen coordinate is a largest one. -/
theorem maxIdx_mem (hn : 0 < n) (y : Fin n → ℝ) : maxIdx hn y ∈ maxCoords y :=
  Finset.min'_mem _ _

/-- At the chosen coordinate the absolute value is the sup norm. -/
theorem abs_maxIdx (hn : 0 < n) (y : Fin n → ℝ) : |y (maxIdx hn y)| = ‖y‖ :=
  abs_eq_norm_of_mem (maxIdx_mem hn y)

/-- Reflection does not move the chosen coordinate. -/
theorem maxIdx_neg (hn : 0 < n) (y : Fin n → ℝ) : maxIdx hn (-y) = maxIdx hn y :=
  le_antisymm
    (Finset.min'_le _ _ (by rw [maxCoords_neg]; exact maxIdx_mem hn y))
    (Finset.min'_le _ _ (by rw [← maxCoords_neg]; exact maxIdx_mem hn (-y)))

/-- The label of a point: the least coordinate of largest absolute value, together with
its sign. -/
noncomputable def label (hn : 0 < n) (y : Fin n → ℝ) : GridSimplex.Label n :=
  (maxIdx hn y, if 0 < y (maxIdx hn y) then true else false)

/-- A positively labelled point attains its sup norm there with a positive sign. -/
theorem norm_le_of_label_true (hn : 0 < n) {y : Fin n → ℝ} {i : Fin n}
    (h : label hn y = (i, true)) : ‖y‖ ≤ y i := by
  have hi : maxIdx hn y = i := congrArg Prod.fst h
  have hs : (if 0 < y (maxIdx hn y) then true else false) = true := congrArg Prod.snd h
  have hpos : 0 < y (maxIdx hn y) := by
    by_contra hcon
    rw [if_neg hcon] at hs
    exact Bool.noConfusion hs
  rw [← hi, ← abs_maxIdx hn y, abs_of_pos hpos]

/-- A negatively labelled point attains its sup norm there with a negative sign. -/
theorem le_neg_norm_of_label_false (hn : 0 < n) {y : Fin n → ℝ} {i : Fin n}
    (h : label hn y = (i, false)) : y i ≤ -‖y‖ := by
  have hi : maxIdx hn y = i := congrArg Prod.fst h
  have hs : (if 0 < y (maxIdx hn y) then true else false) = false := congrArg Prod.snd h
  have hnpos : ¬ 0 < y (maxIdx hn y) := by
    intro hcon
    rw [if_pos hcon] at hs
    exact Bool.noConfusion hs
  have habs := abs_maxIdx hn y
  rw [abs_of_nonpos (not_lt.1 hnpos)] at habs
  rw [← hi]
  linarith

/-- **Reflection reverses the label**, away from the origin. -/
theorem label_neg (hn : 0 < n) {y : Fin n → ℝ} (hy : y ≠ 0) :
    label hn (-y) = GridSimplex.negLabel (label hn y) := by
  have hi := maxIdx_neg hn y
  have habs := abs_maxIdx hn y
  have hnorm : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hne : y (maxIdx hn y) ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    linarith
  simp only [label, GridSimplex.negLabel, hi]
  congr 1
  simp only [Pi.neg_apply]
  by_cases hpos : 0 < y (maxIdx hn y)
  · rw [if_pos hpos, if_neg (by linarith), Bool.not_true]
  · have hneg : y (maxIdx hn y) < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne
    rw [if_neg hpos, if_pos (by linarith), Bool.not_false]

end CubeLabel

/- ### Borsuk's antipodal theorem for the cube -/

open GridSimplex in
/-- **Borsuk's antipodal theorem, cube form.**

A map of the cube `[-1, 1]ⁿ` into `ℝⁿ` that is continuous on the cube and odd on its
boundary vanishes somewhere in the cube.  Here `Fin n → ℝ` carries the sup norm, so the
closed unit ball is the cube and the unit sphere is its boundary.

The proof is Tucker's lemma plus uniform continuity.  If the map never vanished, its norm
would have a positive minimum `ε` on the compact cube.  Choose a mesh `1 / N` below the
modulus of continuity for `2 * ε` and label each grid point of `[-N, N]ⁿ` by the
coordinate in which its image is largest, together with the sign there.  Oddness on the
boundary makes this labelling antipodal, so Tucker's lemma gives two neighbouring grid
points whose labels are opposite.  Their images then differ by at least `2 * ε` in one
coordinate, although the points are closer than the mesh. -/
theorem borsukUlam_cube {n : ℕ} (hn : 0 < n) (g : (Fin n → ℝ) → (Fin n → ℝ))
    (hg : ContinuousOn g (closedBall 0 1))
    (hodd : ∀ x : Fin n → ℝ, ‖x‖ = 1 → g (-x) = -g x) :
    ∃ x ∈ closedBall (0 : Fin n → ℝ) 1, g x = 0 := by
  by_contra hcon
  have hzero : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, g x ≠ 0 :=
    fun x hx h0 => hcon ⟨x, hx, h0⟩
  -- the image is bounded away from the origin on the cube
  have hK : IsCompact (closedBall (0 : Fin n → ℝ) 1) := isCompact_closedBall 0 1
  have hKne : (closedBall (0 : Fin n → ℝ) 1).Nonempty :=
    ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne (continuous_norm.comp_continuousOn hg)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = ‖g x₀‖ := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hε]
    exact norm_pos_iff.2 (hzero x₀ hx₀)
  have hlow : ∀ x ∈ closedBall (0 : Fin n → ℝ) 1, ε ≤ ‖g x‖ := by
    intro x hx
    rw [hε]
    exact isMinOn_iff.1 hmin x hx
  -- a mesh finer than the modulus of continuity for `2 * ε`
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hg) (2 * ε)
      (by linarith)
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = max M 1 := ⟨_, rfl⟩
  have hNpos : 0 < N := by
    rw [hNdef]
    exact lt_of_lt_of_le Nat.one_pos (le_max_right M 1)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hmesh : 1 / (N : ℝ) < δ := by
    have hMN : M ≤ N := by
      rw [hNdef]
      exact le_max_left M 1
    have h1 : (1 : ℝ) / δ < N := lt_of_lt_of_le hM (by exact_mod_cast hMN)
    rw [div_lt_iff₀ hδpos] at h1
    rw [div_lt_iff₀ hNreal, mul_comm]
    exact h1
  -- the grid points, rescaled into the cube
  obtain ⟨pt, hpt⟩ : ∃ pt : (Fin n → ℤ) → (Fin n → ℝ), ∀ v i, pt v i = (v i : ℝ) / N :=
    ⟨_, fun _ _ => rfl⟩
  have hptmem : ∀ v ∈ grid n N, pt v ∈ closedBall (0 : Fin n → ℝ) 1 := by
    intro v hv
    rw [mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    rw [Real.norm_eq_abs, hpt, abs_div, abs_of_pos hNreal, div_le_one hNreal, abs_le]
    have h := (mem_grid.1 hv) i
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  -- the boundary of the grid lands on the unit sphere of the sup norm
  have hnorm_one : ∀ v ∈ grid n N, IsBoundary N v → ‖pt v‖ = 1 := by
    intro v hv hb
    obtain ⟨c, hc⟩ := hb
    refine le_antisymm ?_ ?_
    · have h := hptmem v hv
      rwa [mem_closedBall, dist_zero_right] at h
    · have hvc : |((v c : ℤ) : ℝ)| = (N : ℝ) := by
        rcases hc with h | h <;> rw [h] <;> push_cast
        · exact abs_of_pos hNreal
        · rw [abs_neg]
          exact abs_of_pos hNreal
      have h1 : |pt v c| = 1 := by
        rw [hpt, abs_div, hvc, abs_of_pos hNreal, div_self (ne_of_gt hNreal)]
      calc (1 : ℝ) = |pt v c| := h1.symm
        _ ≤ ‖pt v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm (pt v) c
  -- the labelling, antipodal on the boundary
  obtain ⟨lam, hlamdef⟩ :
      ∃ lam : (Fin n → ℤ) → Label n, ∀ v, lam v = CubeLabel.label hn (g (pt v)) :=
    ⟨_, fun _ => rfl⟩
  have hantip : ∀ v ∈ grid n N, IsBoundary N v → lam (-v) = negLabel (lam v) := by
    intro v hv hb
    have hptneg : pt (-v) = -(pt v) := by
      funext i
      simp only [hpt, Pi.neg_apply]
      push_cast
      ring
    have hgneg : g (pt (-v)) = -(g (pt v)) := by
      rw [hptneg]
      exact hodd _ (hnorm_one v hv hb)
    rw [hlamdef, hlamdef, hgneg]
    exact CubeLabel.label_neg hn (hzero _ (hptmem v hv))
  -- Tucker's lemma produces two neighbouring points with opposite labels
  obtain ⟨u, hu, w, hw, huw, hspan, hlab⟩ := tucker hNpos lam hantip
  obtain ⟨i, hidef⟩ : ∃ i, i = (lam w).1 := ⟨_, rfl⟩
  have hlw : lam w = (i, (lam w).2) := by rw [hidef]
  have hlu : lam u = (i, !(lam w).2) := by rw [hlab, negLabel, hidef]
  have hεu : ε ≤ ‖g (pt u)‖ := hlow _ (hptmem u hu)
  have hεw : ε ≤ ‖g (pt w)‖ := hlow _ (hptmem w hw)
  -- at that coordinate the two images differ by at least `2 * ε`
  have hkey : 2 * ε ≤ |g (pt u) i - g (pt w) i| := by
    cases hb : (lam w).2
    · have hw' : CubeLabel.label hn (g (pt w)) = (i, false) := by
        rw [← hlamdef w, hlw, hb]
      have hu' : CubeLabel.label hn (g (pt u)) = (i, true) := by
        rw [← hlamdef u, hlu, hb, Bool.not_false]
      have h1 : g (pt w) i ≤ -‖g (pt w)‖ := CubeLabel.le_neg_norm_of_label_false hn hw'
      have h2 : ‖g (pt u)‖ ≤ g (pt u) i := CubeLabel.norm_le_of_label_true hn hu'
      linarith [le_abs_self (g (pt u) i - g (pt w) i)]
    · have hw' : CubeLabel.label hn (g (pt w)) = (i, true) := by
        rw [← hlamdef w, hlw, hb]
      have hu' : CubeLabel.label hn (g (pt u)) = (i, false) := by
        rw [← hlamdef u, hlu, hb, Bool.not_true]
      have h1 : ‖g (pt w)‖ ≤ g (pt w) i := CubeLabel.norm_le_of_label_true hn hw'
      have h2 : g (pt u) i ≤ -‖g (pt u)‖ := CubeLabel.le_neg_norm_of_label_false hn hu'
      linarith [neg_abs_le (g (pt u) i - g (pt w) i)]
  -- but the two points are closer than the modulus of continuity allows
  have hdistpt : dist (pt u) (pt w) < δ := by
    have hle : dist (pt u) (pt w) ≤ 1 / (N : ℝ) := by
      refine (dist_pi_le_iff (by positivity)).2 fun j => ?_
      have h1 : u j ≤ w j := Pi.le_def.1 huw j
      have h2 : w j - u j ≤ 1 := hspan j
      have hr : |(u j : ℝ) - (w j : ℝ)| ≤ 1 := by
        rw [abs_le]
        constructor
        · have h3 : (w j : ℝ) - (u j : ℝ) ≤ 1 := by exact_mod_cast h2
          linarith
        · have h3 : (u j : ℝ) ≤ (w j : ℝ) := by exact_mod_cast h1
          linarith
      rw [Real.dist_eq, hpt, hpt, div_sub_div_same, abs_div, abs_of_pos hNreal]
      gcongr
    linarith
  have hdistlt : dist (g (pt u)) (g (pt w)) < 2 * ε :=
    hδ (pt u) (hptmem u hu) (pt w) (hptmem w hw) hdistpt
  have hdistge : 2 * ε ≤ dist (g (pt u)) (g (pt w)) := by
    refine le_trans hkey ?_
    rw [← Real.dist_eq]
    exact dist_le_pi_dist _ _ i
  linarith


/- ### From the cube to the sphere

The cube `[-1, 1]ⁿ` maps onto the unit sphere of `ℝ^{n+1}` by lifting a point to the
height left over by its sup norm and then projecting radially.  On the boundary of the
cube the slack vanishes, so there the map is odd. -/

namespace CubeSphere

variable {n : ℕ}

/-- The lift of a point of `ℝⁿ` to `ℝ^{n+1}`: its own coordinates, with the slack of its
sup norm as the last one. -/
noncomputable def lift (x : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc x (1 - ‖x‖)

/-- The lift keeps the original coordinates. -/
@[simp]
theorem lift_castSucc (x : Fin n → ℝ) (j : Fin n) : lift x j.castSucc = x j := by
  simp [lift]

/-- The last coordinate of the lift is the slack of the sup norm. -/
@[simp]
theorem lift_last (x : Fin n → ℝ) : lift x (Fin.last n) = 1 - ‖x‖ := by
  simp [lift]

/-- Lifting does not decrease the sup norm. -/
theorem norm_le_norm_lift (x : Fin n → ℝ) : ‖x‖ ≤ ‖lift x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h := norm_le_pi_norm (lift x) j.castSucc
  rwa [lift_castSucc] at h

/-- The slack is bounded by the norm of the lift. -/
theorem abs_one_sub_norm_le (x : Fin n → ℝ) : |1 - ‖x‖| ≤ ‖lift x‖ := by
  have h := norm_le_pi_norm (lift x) (Fin.last n)
  rwa [lift_last, Real.norm_eq_abs] at h

/-- **The lift never comes near the origin.**  Either the point itself is large, or its
slack is. -/
theorem half_le_norm_lift (x : Fin n → ℝ) : (1 : ℝ) / 2 ≤ ‖lift x‖ := by
  rcases le_total (1 / 2 : ℝ) ‖x‖ with h | h
  · exact le_trans h (norm_le_norm_lift x)
  · refine le_trans ?_ (abs_one_sub_norm_le x)
    rw [abs_of_nonneg (by linarith [norm_nonneg x])]
    linarith

/-- The lift is never the origin. -/
theorem norm_lift_pos (x : Fin n → ℝ) : 0 < ‖lift x‖ :=
  lt_of_lt_of_le (by norm_num) (half_le_norm_lift x)

/-- On the boundary of the cube the slack vanishes, so the lift is odd there. -/
theorem lift_neg_of_norm_eq_one {x : Fin n → ℝ} (hx : ‖x‖ = 1) : lift (-x) = -(lift x) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [hx]
  | cast j => simp

/-- The lift is continuous. -/
theorem continuous_lift : Continuous (lift : (Fin n → ℝ) → Fin (n + 1) → ℝ) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.lastCases with
  | last =>
    simp only [lift_last]
    exact continuous_const.sub continuous_norm
  | cast j =>
    simp only [lift_castSucc]
    exact continuous_apply j

/-- The radial projection of the lift onto the unit sphere of `ℝ^{n+1}`. -/
noncomputable def proj (x : Fin n → ℝ) : Fin (n + 1) → ℝ := ‖lift x‖⁻¹ • lift x

/-- The projection lands on the unit sphere. -/
theorem norm_proj (x : Fin n → ℝ) : ‖proj x‖ = 1 := by
  rw [proj, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt (norm_lift_pos x))]

/-- On the boundary of the cube the projection is odd. -/
theorem proj_neg_of_norm_eq_one {x : Fin n → ℝ} (hx : ‖x‖ = 1) : proj (-x) = -(proj x) := by
  rw [proj, proj, lift_neg_of_norm_eq_one hx, norm_neg, smul_neg]

/-- The projection is continuous, because the lift stays away from the origin. -/
theorem continuous_proj : Continuous (proj : (Fin n → ℝ) → Fin (n + 1) → ℝ) := by
  have h1 : Continuous fun x : Fin n → ℝ => ‖lift x‖ := continuous_norm.comp continuous_lift
  have h2 : Continuous fun x : Fin n → ℝ => (‖lift x‖)⁻¹ :=
    h1.inv₀ fun x => ne_of_gt (norm_lift_pos x)
  exact h2.smul continuous_lift

end CubeSphere

/-- **Borsuk–Ulam theorem for the sup norm.**

A map into `ℝᵏ` with `k < m` that is odd and continuous on the unit sphere of
`Fin m → ℝ`, taken with the sup norm, vanishes at some point of that sphere.

The unit sphere of the sup norm is the boundary of the cube one dimension lower, reached
by `CubeSphere.proj`; padding the values with zeros to `m - 1` coordinates turns the
statement into `borsukUlam_cube`. -/
theorem borsukUlam_pi {m k : ℕ} (hk : k < m) (f : (Fin m → ℝ) → (Fin k → ℝ))
    (hf : ContinuousOn f (sphere 0 1)) (hodd : Function.Odd f) :
    ∃ x ∈ sphere (0 : Fin m → ℝ) 1, f x = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- with no functional, any point of the sphere will do
    have hmpos : 0 < m := hk
    refine ⟨fun _ => 1, ?_, funext fun i => absurd i.2 (by omega)⟩
    rw [mem_sphere_zero_iff_norm]
    refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp) ?_
    simpa using norm_le_pi_norm (fun _ : Fin m => (1 : ℝ)) ⟨0, hmpos⟩
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hn : 0 < n := by omega
    have hkn : k ≤ n := by omega
    -- pad the values with zeros to `n` coordinates
    obtain ⟨pad, hpad⟩ : ∃ pad : (Fin k → ℝ) → (Fin n → ℝ),
        ∀ z j, pad z j = if h : (j : ℕ) < k then z ⟨j, h⟩ else 0 := ⟨_, fun _ _ => rfl⟩
    have hpadcont : Continuous pad := by
      refine continuous_pi fun j => ?_
      by_cases h : (j : ℕ) < k
      · simp only [hpad, dif_pos h]
        exact continuous_apply _
      · simp only [hpad, dif_neg h]
        exact continuous_const
    have hpadodd : ∀ z : Fin k → ℝ, pad (-z) = -(pad z) := by
      intro z
      funext j
      rw [Pi.neg_apply, hpad, hpad]
      by_cases h : (j : ℕ) < k
      · rw [dif_pos h, dif_pos h, Pi.neg_apply]
      · rw [dif_neg h, dif_neg h, neg_zero]
    have hpadzero : ∀ z : Fin k → ℝ, pad z = 0 → z = 0 := by
      intro z hz
      funext i
      have hi : (i : ℕ) < n := lt_of_lt_of_le i.2 hkn
      have h := congrFun hz ⟨i, hi⟩
      rw [hpad, dif_pos i.2] at h
      simpa using h
    -- the map on the cube
    obtain ⟨g, hgdef⟩ : ∃ g : (Fin n → ℝ) → (Fin n → ℝ),
        ∀ x, g x = pad (f (CubeSphere.proj x)) := ⟨_, fun _ => rfl⟩
    have hprojmem : ∀ x : Fin n → ℝ, CubeSphere.proj x ∈ sphere (0 : Fin (n + 1) → ℝ) 1 := by
      intro x
      rw [mem_sphere_zero_iff_norm]
      exact CubeSphere.norm_proj x
    have hgcont : Continuous g := by
      have h1 : Continuous fun x : Fin n → ℝ => f (CubeSphere.proj x) :=
        hf.comp_continuous CubeSphere.continuous_proj hprojmem
      have h2 : g = fun x => pad (f (CubeSphere.proj x)) := funext hgdef
      rw [h2]
      exact hpadcont.comp h1
    have hgodd : ∀ x : Fin n → ℝ, ‖x‖ = 1 → g (-x) = -g x := by
      intro x hx
      rw [hgdef, hgdef, CubeSphere.proj_neg_of_norm_eq_one hx, hodd, hpadodd]
    obtain ⟨x, -, hgx⟩ := borsukUlam_cube hn g hgcont.continuousOn hgodd
    refine ⟨CubeSphere.proj x, hprojmem x, hpadzero _ ?_⟩
    rwa [hgdef] at hgx


end

theorem OMA.odd_zero (m : ℕ) : OddZero m := by
  intro F hf ho
  obtain ⟨x,hx,hzero⟩ := borsukUlam_pi (Nat.lt_succ_self m) F hf.continuousOn ho
  refine ⟨x,?_,hzero⟩
  rintro rfl
  simp at hx

theorem OMA.solution : type_of% @Erdos95.erdos_95.variants.guth_katz :=
  solution_of_borsuk_ulam odd_zero
