import OMAReductions.R_Erdos652_erdos_652_variants_order_sqrt_R1_H1_R1

/-! The cut-circle chains, angle ordering, and tag counts below are from @JaviSoto in the merged parent proof. The final argument constructs the oriented drawing and bounds its intersection sum. -/
namespace OMA.Math652ArcOrder

open Finset
open scoped EuclideanGeometry Classical

noncomputable abbrev plane := Complex.orthonormalBasisOneI.repr

noncomputable def angle (p q : ℝ²) : ℝ := (plane.symm (q-p)).arg

noncomputable def point (p : ℝ²) (r t : ℝ) : ℝ² :=
  p + plane ((r : ℂ) * Complex.exp (t*Complex.I))

theorem continuous_point (p : ℝ²) (r : ℝ) : Continuous (point p r) := by
  unfold point
  fun_prop

theorem angle_mem (p q : ℝ²) : angle p q ∈ Set.Ioc (-Real.pi) Real.pi :=
  Complex.arg_mem_Ioc _

theorem angle_point (p : ℝ²) {r t : ℝ} (hr : 0 < r)
    (ht : t ∈ Set.Ioc (-Real.pi) Real.pi) : angle p (point p r t) = t := by
  simp [angle,point,Complex.exp_mul_I,Complex.arg_mul_cos_add_sin_mul_I hr ht]

theorem point_angle (p q : ℝ²) : point p (dist p q) (angle p q) = q := by
  have hn : dist p q = ‖plane.symm (q-p)‖ := by rw [LinearIsometryEquiv.norm_map, dist_comm, dist_eq_norm]
  rw [point,angle,hn,Complex.norm_mul_exp_arg_mul_I,LinearIsometryEquiv.apply_symm_apply]
  abel

theorem dist_point (p : ℝ²) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : dist p (point p r t) = r := by
  rw [dist_comm, dist_eq_norm]
  simp [point, Complex.norm_exp, hr]

noncomputable def arcPath (p : ℝ²) (r s t : ℝ) : Path (point p r s) (point p r t) :=
  (Path.segment s t).map (continuous_point p r)

theorem range_arcPath (p : ℝ²) (r : ℝ) {s t : ℝ} (hst : s ≤ t) :
    Set.range (arcPath p r s t) = point p r '' Set.Icc s t := by
  change Set.range (point p r ∘ (Path.segment s t)) = _
  rw [Set.range_comp,Path.range_segment,segment_eq_Icc hst]

theorem injective_arcPath (p : ℝ²) {r s t : ℝ} (hr : 0 < r) (hst : s < t)
    (hs : -Real.pi < s) (ht : t ≤ Real.pi) : Function.Injective (arcPath p r s t) := by
  have hseg (u : unitInterval) : Path.segment s t u ∈ Set.Icc s t := by
    rw [← segment_eq_Icc hst.le, ← Path.range_segment]
    exact Set.mem_range_self _
  intro u v h
  have eq := congrArg (angle p) h
  change angle p (point p r (Path.segment s t u)) = angle p (point p r (Path.segment s t v)) at eq
  have hangle (u : unitInterval) : Path.segment s t u ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hs.trans_le (hseg u).1,(hseg u).2.trans ht⟩
  rw [angle_point _ hr (hangle u),angle_point _ hr (hangle v)] at eq
  exact Path.segment_injective_of_ne hst.ne eq

def interval {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (i : Fin m) : Set ℝ :=
  Set.Icc (θ i.castSucc) (θ i.succ)

noncomputable def hits {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (z : ℝ) : Finset (Fin m) :=
  univ.filter fun i => z ∈ interval θ i

noncomputable def surviving {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (C : Finset ℝ) : Finset (Fin m) :=
  univ \ C.biUnion (hits θ)

/-- At most two consecutive closed intervals contain a fixed cut; their common
vertex is the only way both can contain it. -/
theorem card_hits {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (z : ℝ) : (hits θ z).card ≤ 2 := by
  let side (i : Fin m) := decide (θ i.castSucc = z)
  have diff {i j : Fin m} (h : i < j) (hi : z ∈ interval θ i) (hj : z ∈ interval θ j) :
      side i ≠ side j := by
    have ord : θ i.succ ≤ θ j.castSucc := θ.monotone (by simpa using h)
    have heq : θ j.castSucc = z := le_antisymm hj.1 (hi.2.trans ord)
    have hne : θ i.castSucc ≠ z := (θ.strictMono Fin.castSucc_lt_succ).trans_le (ord.trans hj.1) |>.ne
    simp [side,heq,hne]
  have hc : (hits θ z).card ≤ (univ : Finset Bool).card := by
    apply card_le_card_of_injOn side (fun _ _ => mem_univ _)
    intro i hi j hj eq
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    rcases lt_trichotomy i j with h|h|h
    · exact (diff h hi' hj' eq).elim
    · exact h
    · exact (diff h hj' hi' eq.symm).elim
  simpa using hc

theorem card_surviving {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (C : Finset ℝ) :
    m+1 ≤ (surviving θ C).card + 2*C.card+1 := by
  have hu : (C.biUnion (hits θ)).card ≤ C.card*2 :=
    card_biUnion_le.trans ((sum_le_sum fun t _ => card_hits θ t).trans_eq (by simp))
  have h : (univ : Finset (Fin m)).card ≤ (surviving θ C).card + (C.biUnion (hits θ)).card :=
    card_le_card_sdiff_add_card
  simp only [card_univ,Fintype.card_fin] at h
  omega

theorem avoids_cuts {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (C : Finset ℝ) {i : Fin m}
    (hi : i ∈ surviving θ C) {z : ℝ} (hz : z ∈ C) : z ∉ interval θ i := by
  intro h
  exact (mem_sdiff.mp hi).2 (mem_biUnion.mpr ⟨z,hz,mem_filter.mpr ⟨mem_univ _,h⟩⟩)

theorem consecutive {m : ℕ} (θ : Fin (m+1) ↪o ℝ) (i : Fin m) (j : Fin (m+1))
    (h : θ j ∈ interval θ i) : j = i.castSucc ∨ j = i.succ := by
  have h1 := θ.le_iff_le.mp h.1
  have h2 := θ.le_iff_le.mp h.2
  change i.val ≤ j.val at h1
  change j.val ≤ i.val + 1 at h2
  by_cases eq : j.val = i.val
  · exact Or.inl (Fin.ext eq)
  · exact Or.inr (Fin.ext (by change j.val = i.val+1; omega))

/-- The points at radius `r` in the direction of a second center and its opposite. -/
noncomputable def cutPoints (p b : ℝ²) (r : ℝ) : Finset ℝ² :=
  {p + (r / dist p b) • (b-p), p + (-(r / dist p b)) • (b-p)}

noncomputable def lineSide (p b z : ℝ²) : ℝ :=
  (b 0 - p 0)*(z 1 - p 1) - (b 1 - p 1)*(z 0 - p 0)

private theorem point_on_line {p b z : ℝ²} (hb : p ≠ b) (hz : lineSide p b z = 0) :
    ∃ t : ℝ, z = p + t • (b-p) := by
  unfold lineSide at hz
  by_cases h : b 0 - p 0 = 0
  · have h' : b 1 - p 1 ≠ 0 := by
      intro hy
      exact hb (by ext i; fin_cases i <;> simp <;> linarith)
    refine ⟨(z 1 - p 1)/(b 1 - p 1),?_⟩
    ext i
    fin_cases i <;> simp [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,h]
    · rcases mul_eq_zero.mp (show (b 1-p 1)*(z 0-p 0) = 0 by rw [h] at hz; linarith) with h₁|h₂
      · exact (h' h₁).elim
      · linarith
    · field_simp
      ring
  · refine ⟨(z 0-p 0)/(b 0-p 0),?_⟩
    ext i
    fin_cases i <;> simp [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply] <;> field_simp
    · ring
    · linarith

theorem mem_cutPoints {p b z : ℝ²} {r : ℝ} (hb : p ≠ b) (hr : dist p z = r)
    (hz : lineSide p b z = 0) : z ∈ cutPoints p b r := by
  obtain ⟨t,rfl⟩ := point_on_line hb hz
  have hp : 0 < dist p b := dist_pos.mpr hb
  have hnorm : |t| * dist p b = r := by
    rw [dist_comm p _,dist_eq_norm] at hr
    simpa [norm_smul,Real.norm_eq_abs,← dist_eq_norm,dist_comm b p] using hr
  have h := (eq_div_iff hp.ne').mpr hnorm
  rcases le_or_gt 0 t with ht|ht
  · rw [abs_of_nonneg ht] at h
    simp [cutPoints,h]
  · rw [abs_of_neg ht] at h
    have he : t = -(r / dist p b) := by linarith
    simp [cutPoints,he]

noncomputable def cuts (P : Finset ℝ²) (p : ℝ²) (r : ℝ) : Finset ℝ :=
  (P.erase p).biUnion fun b => (cutPoints p b r).image (angle p)

theorem card_cuts (P : Finset ℝ²) {p : ℝ²} (hp : p ∈ P) (r : ℝ) :
    (cuts P p r).card ≤ (P.card-1)*2 := by
  calc
    _ ≤ ∑ b ∈ P.erase p, ((cutPoints p b r).image (angle p)).card := card_biUnion_le
    _ ≤ ∑ _b ∈ P.erase p, 2 := sum_le_sum fun b _ => card_image_le.trans card_le_two
    _ = _ := by simp [card_erase_of_mem hp]

/-- On every surviving interval, no point of the circle lies on any of the cut lines. -/
theorem not_on_cut_line (P : Finset ℝ²) {p b : ℝ²} (hb : b ∈ P) (hne : p ≠ b)
    {r : ℝ} (hr : 0 < r) {m : ℕ} (θ : Fin (m+1) ↪o ℝ)
    (hθ : ∀ j, θ j ∈ Set.Ioc (-Real.pi) Real.pi)
    {i : Fin m} (hi : i ∈ surviving θ (cuts P p r))
    {t : ℝ} (ht : t ∈ interval θ i) : lineSide p b (point p r t) ≠ 0 := by
  intro hz
  have hcut := mem_cutPoints hne (dist_point p hr.le t) hz
  have harg := angle_point p hr (show t ∈ Set.Ioc (-Real.pi) Real.pi from
    ⟨(hθ _).1.trans_le ht.1,ht.2.trans (hθ _).2⟩)
  exact avoids_cuts θ _ hi (mem_biUnion.mpr
    ⟨b,mem_erase.mpr ⟨hne.symm,hb⟩,mem_image.mpr ⟨_,hcut,harg⟩⟩) ht

/-- Any two points on a retained interval lie in the same open halfplane of every
cut line. The determinant defining the halfplane is continuous and never vanishes. -/
theorem same_side (P : Finset ℝ²) {p b : ℝ²} (hb : b ∈ P) (hne : p ≠ b)
    {r : ℝ} (hr : 0 < r) {m : ℕ} (θ : Fin (m+1) ↪o ℝ)
    (hθ : ∀ j, θ j ∈ Set.Ioc (-Real.pi) Real.pi)
    {i : Fin m} (hi : i ∈ surviving θ (cuts P p r)) {t u : ℝ}
    (ht : t ∈ interval θ i) (hu : u ∈ interval θ i) :
    0 < lineSide p b (point p r t) * lineSide p b (point p r u) := by
  let f (s : ℝ) := lineSide p b (point p r s)
  have hcont : Continuous f := by
    unfold f lineSide
    have hc := continuous_point p r
    fun_prop
  have hn (s : ℝ) (hs : s ∈ interval θ i) : f s ≠ 0 := not_on_cut_line P hb hne hr θ hθ hi hs
  have same {a b : ℝ} (ha : a ∈ interval θ i) (hb : b ∈ interval θ i) (h : f a < 0) : f b < 0 := by
    by_contra! h'
    obtain ⟨s,hs,he⟩ := isPreconnected_Icc.intermediate_value ha hb hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f a) (f b) from ⟨h.le,h'⟩)
    exact hn s hs he
  change 0 < f t * f u
  rcases lt_or_gt_of_ne (hn t ht) with ht'|ht'
  · exact mul_pos_of_neg_of_neg ht' (same ht hu ht')
  · rcases lt_or_gt_of_ne (hn u hu) with hu'|hu'
    · exact (lt_asymm ht' (same hu ht hu')).elim
    · exact mul_pos ht' hu'

noncomputable def layer (Q : Finset ℝ²) (p : ℝ²) (r : ℝ) : Finset ℝ² :=
  Q.filter fun q => dist p q = r

/-- Polar-angle enumeration of one radius class of a finite set. -/
structure LayerOrder (Q : Finset ℝ²) (p : ℝ²) (r : ℝ) (n : ℕ) where
  θ : Fin n ↪o ℝ
  range_angle : ∀ j, θ j ∈ Set.Ioc (-Real.pi) Real.pi
  members : ∀ q, q ∈ layer Q p r ↔ ∃ j, point p r (θ j) = q

noncomputable def orderLayer (Q : Finset ℝ²) (p : ℝ²) (r : ℝ) {n : ℕ}
    (hN : (layer Q p r).card = n) : LayerOrder Q p r n := by
  let A := layer Q p r
  let T := A.image (angle p)
  have hr {q : ℝ²} (hq : q ∈ A) : dist p q = r := (mem_filter.mp hq).2
  have hpt {q : ℝ²} (hq : q ∈ A) : point p r (angle p q) = q := hr hq ▸ point_angle p q
  have hinj : Set.InjOn (angle p) (A : Set ℝ²) := by
    intro x hx y hy eq
    rw [← hpt hx,eq,hpt hy]
  have hcard : T.card = n := (card_image_of_injOn hinj).trans hN
  let θ := T.orderEmbOfFin hcard
  have hθ (j : Fin n) : θ j ∈ T := T.orderEmbOfFin_mem hcard j
  refine ⟨θ,?_,?_⟩
  · intro j
    obtain ⟨q,_,he⟩ := mem_image.mp (hθ j)
    rw [← he]
    exact angle_mem _ _
  · intro q
    constructor
    · intro hq
      have hmem : angle p q ∈ (T : Set ℝ) := mem_image_of_mem _ hq
      rw [← T.range_orderEmbOfFin hcard] at hmem
      obtain ⟨j,hj⟩ := hmem
      exact ⟨j,(congrArg (point p r) hj).trans (hpt hq)⟩
    · rintro ⟨j,rfl⟩
      obtain ⟨q,hq,he⟩ := mem_image.mp (hθ j)
      rw [← he,hpt hq]
      exact hq

theorem LayerOrder.avoids {Q : Finset ℝ²} {p : ℝ²} {r : ℝ} (hr : 0 < r) {m : ℕ}
    (L : LayerOrder Q p r (m+1)) (i : Fin m) {q : ℝ²} (hq : q ∈ Q)
    (h : q ∈ Set.range (arcPath p r (L.θ i.castSucc) (L.θ i.succ))) :
    q = point p r (L.θ i.castSucc) ∨ q = point p r (L.θ i.succ) := by
  rw [range_arcPath p r (L.θ.strictMono Fin.castSucc_lt_succ).le] at h
  obtain ⟨t,ht,rfl⟩ := h
  have hq' : point p r t ∈ layer Q p r := mem_filter.mpr ⟨hq,dist_point p hr.le t⟩
  obtain ⟨j,hj⟩ := (L.members _).mp hq'
  have h' := congrArg (angle p) hj
  have ht' : t ∈ Set.Ioc (-Real.pi) Real.pi := ⟨(L.range_angle _).1.trans_le ht.1,ht.2.trans (L.range_angle _).2⟩
  rw [angle_point _ hr (L.range_angle j),angle_point _ hr ht'] at h'
  rcases consecutive L.θ i j (h' ▸ ht) with he|he
  · exact Or.inl (he ▸ hj.symm)
  · exact Or.inr (he ▸ hj.symm)

/-- All local data contributed by a single circle, indexed by its surviving edges. -/
structure CircleChain (P Q : Finset ℝ²) (p : ℝ²) (r : ℝ) where
  n : ℕ
  edge : Fin n → Finset Q
  curve : Fin n → Set ℝ²
  drawn : ∀ i, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
    ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = Set.range γ ∧
      ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i
  simple : Function.Injective edge
  onCircle : ∀ i z, z ∈ curve i → dist p z = r
  uniqueOutside : ∀ i j z, z ∉ Q → z ∈ curve i → z ∈ curve j → i = j
  halfplanes : ∀ i b, b ∈ P → p ≠ b → ∀ x y, x ∈ curve i → y ∈ curve i →
    0 < lineSide p b x * lineSide p b y
  count : (layer Q p r).card ≤ n + 4*(P.card-1)+1

private noncomputable def emptyChain (P Q : Finset ℝ²) (p : ℝ²) (r : ℝ)
    (h : (layer Q p r).card ≤ 1) : CircleChain P Q p r where
  n := 0
  edge := Fin.elim0
  curve := Fin.elim0
  drawn := fun i => i.elim0
  simple := fun i => Fin.elim0 i
  onCircle := fun i => i.elim0
  uniqueOutside := fun i => i.elim0
  halfplanes := fun i => i.elim0
  count := by omega

private noncomputable def vertex {Q : Finset ℝ²} {p : ℝ²} {r : ℝ} {n : ℕ}
    (L : LayerOrder Q p r n) (j : Fin n) : Q :=
  ⟨point p r (L.θ j),(mem_filter.mp ((L.members _).mpr ⟨j,rfl⟩)).1⟩

private theorem vertex_injective {Q : Finset ℝ²} {p : ℝ²} {r : ℝ} (hr : 0 < r) {n : ℕ}
    (L : LayerOrder Q p r n) : Function.Injective (vertex L) := by
  intro i j eq
  have h := congrArg (fun q : Q => angle p q) eq
  change angle p (point p r (L.θ i)) = angle p (point p r (L.θ j)) at h
  rwa [angle_point p hr (L.range_angle _),angle_point p hr (L.range_angle _),L.θ.injective.eq_iff] at h

private theorem interval_inside {Q : Finset ℝ²} {p : ℝ²} {r : ℝ} {m : ℕ}
    (L : LayerOrder Q p r (m+1)) {i : Fin m} {s : ℝ} (hs : s ∈ interval L.θ i) :
    s ∈ Set.Ioc (-Real.pi) Real.pi := ⟨(L.range_angle _).1.trans_le hs.1,hs.2.trans (L.range_angle _).2⟩

private theorem unique_interval {Q : Finset ℝ²} {p : ℝ²} {r : ℝ} {m : ℕ}
    (L : LayerOrder Q p r (m+1)) {i j : Fin m} {s : ℝ} (hs : point p r s ∉ Q)
    (hi : s ∈ interval L.θ i) (hj : s ∈ interval L.θ j) : i = j := by
  have forbidden {i j : Fin m} (hlt : i < j) (hi : s ∈ interval L.θ i)
      (hj : s ∈ interval L.θ j) : False := by
    have ord : L.θ i.succ ≤ L.θ j.castSucc := L.θ.monotone (by simpa using hlt)
    exact hs (le_antisymm hj.1 (hi.2.trans ord) ▸ (vertex L j.castSucc).property)
  rcases lt_trichotomy i j with h|h|h
  · exact (forbidden h hi hj).elim
  · exact h
  · exact (forbidden h hj hi).elim

/-- Construct the data on every radius, including empty and radius-zero layers. -/
noncomputable def circleChain (P Q : Finset ℝ²) (p : ℝ²) (hp : p ∈ P) (r : ℝ) :
    CircleChain P Q p r := by
  by_cases hr : 0 < r
  · cases hm : (layer Q p r).card with
    | zero => exact emptyChain P Q p r (by omega)
    | succ m =>
      let L := orderLayer Q p r hm
      let E := surviving L.θ (cuts P p r)
      let idx (i : Fin E.card) : Fin m := E.equivFin.symm i
      have hi (i : Fin E.card) : idx i ∈ E := (E.equivFin.symm i).property
      have hidx : Function.Injective idx := Subtype.val_injective.comp E.equivFin.symm.injective
      let x (i : Fin E.card) := vertex L (idx i).castSucc
      let y (i : Fin E.card) := vertex L (idx i).succ
      let γ (i : Fin E.card) := arcPath p r (L.θ (idx i).castSucc) (L.θ (idx i).succ)
      have hγ (i : Fin E.card) : Set.range (γ i) = point p r '' interval L.θ (idx i) :=
        range_arcPath p r (L.θ.strictMono Fin.castSucc_lt_succ).le
      refine {
        n := E.card, edge := fun i => {x i,y i}, curve := fun i => Set.range (γ i)
        drawn := ?_, simple := ?_, onCircle := ?_, uniqueOutside := ?_, halfplanes := ?_, count := ?_ }
      · intro i
        refine ⟨x i,y i,(vertex_injective hr L).ne Fin.castSucc_lt_succ.ne,rfl,γ i,?_,rfl,?_⟩
        · exact injective_arcPath p hr (L.θ.strictMono Fin.castSucc_lt_succ) (L.range_angle _).1 (L.range_angle _).2
        · intro v hv
          rcases L.avoids hr (idx i) v.property hv with h | h
          · rw [show v = x i from Subtype.ext h]
            simp
          · rw [show v = y i from Subtype.ext h]
            simp
      · intro i j eq
        have he := congrArg (fun s : Finset Q => (s : Set Q)) eq
        change (({x i,y i} : Finset Q) : Set Q) = (({x j,y j} : Finset Q) : Set Q) at he
        simp only [coe_pair,Set.pair_eq_pair_iff] at he
        rcases he with ⟨h,_⟩|⟨h,h'⟩
        · exact hidx (Fin.ext (congrArg (fun v : Fin (m+1) => v.val) (vertex_injective hr L h)))
        · have h₁ := congrArg Fin.val (vertex_injective hr L h)
          have h₂ := congrArg Fin.val (vertex_injective hr L h')
          change (idx i).val = (idx j).val+1 at h₁
          change (idx i).val+1 = (idx j).val at h₂
          omega
      · intro i z hz
        obtain ⟨t,_,rfl⟩ := hγ i ▸ hz
        exact dist_point p hr.le t
      · intro i j z hz hi hj
        obtain ⟨t,ht,rfl⟩ := hγ i ▸ hi
        obtain ⟨u,hu,htu⟩ := hγ j ▸ hj
        have he := congrArg (angle p) htu
        rw [angle_point p hr (interval_inside L hu),angle_point p hr (interval_inside L ht)] at he
        exact hidx (unique_interval L hz ht (he ▸ hu))
      · intro i b hb hne z w hz hw
        obtain ⟨t,ht,rfl⟩ := hγ i ▸ hz
        obtain ⟨u,hu,rfl⟩ := hγ i ▸ hw
        exact same_side P hb hne hr L.θ L.range_angle (hi i) ht hu
      · have h := card_surviving L.θ (cuts P p r)
        have h' := card_cuts P hp r
        change (layer Q p r).card ≤ (surviving L.θ (cuts P p r)).card + 4*(P.card-1)+1
        omega
  · apply emptyChain P Q p r
    apply card_le_one.mpr
    intro x hx y hy
    have he {z} (hz : z ∈ layer Q p r) : p = z :=
      dist_eq_zero.mp (le_antisymm ((mem_filter.mp hz).2.trans_le (le_of_not_gt hr)) dist_nonneg)
    exact (he hx).symm.trans (he hy)

theorem eq_of_dist_eq_in_same_halfplane {a b x y : ℝ²} (hab : a ≠ b)
    (ha : dist x a = dist y a) (hb : dist x b = dist y b)
    (hs : 0 < lineSide a b x * lineSide a b y) : x = y := by
  have hdist (u v : ℝ²) : dist u v ^ 2 = (u 0-v 0)^2 + (u 1-v 1)^2 := by
    simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  have hE := congrArg (fun z : ℝ => z^2) ha
  have hF := congrArg (fun z : ℝ => z^2) hb
  simp only [hdist] at hE hF
  let u := b 0-a 0
  let v := b 1-a 1
  let dot (z : ℝ²) := u*(z 0-a 0) + v*(z 1-a 1)
  have hd : dot x = dot y := by
    dsimp [dot,u,v]; linear_combination (hE - hF)/2
  have hid (z : ℝ²) : dot z ^ 2 + lineSide a b z ^ 2 =
      (u^2+v^2)*((z 0-a 0)^2+(z 1-a 1)^2) := by dsimp [lineSide,dot,u,v]; ring
  have hh := hid x
  rw [hd,hE,← hid y] at hh
  have hside : lineSide a b x = lineSide a b y := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (add_left_cancel hh) with he | he
    · exact he
    · rw [he] at hs
      nlinarith only [hs,sq_nonneg (lineSide a b y)]
  have huv : u^2+v^2 ≠ 0 := by
    intro hz
    obtain ⟨hu2,hv2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg u) (sq_nonneg v)).mp hz
    have hu : u = 0 := by simpa using hu2
    have hv : v = 0 := by simpa using hv2
    apply hab
    ext i
    fin_cases i
    · exact (sub_eq_zero.mp hu).symm
    · exact (sub_eq_zero.mp hv).symm
  change u*(x 1-a 1) - v*(x 0-a 0) = u*(y 1-a 1) - v*(y 0-a 0) at hside
  dsimp only [dot] at hd
  ext i
  fin_cases i
  · apply mul_left_cancel₀ huv
    change (u^2+v^2)*x 0 = (u^2+v^2)*y 0
    linear_combination u*hd-v*hside
  · apply mul_left_cancel₀ huv
    change (u^2+v^2)*x 1 = (u^2+v^2)*y 1
    linear_combination v*hd+u*hside

namespace CircleChain

variable {P Q : Finset ℝ²} {p b : ℝ²} {r s : ℝ}

theorem edge_card (L : CircleChain P Q p r) (i : Fin L.n) : (L.edge i).card = 2 := by
  obtain ⟨x,y,hxy,he,-⟩ := L.drawn i
  rw [he,card_pair hxy]

theorem mem_curve_iff (L : CircleChain P Q p r) (i : Fin L.n) (v : Q) :
    (v : ℝ²) ∈ L.curve i ↔ v ∈ L.edge i := by
  obtain ⟨x,y,hxy,he,γ,_,hg,ha⟩ := L.drawn i
  refine ⟨ha v,?_⟩
  intro h
  rw [hg]
  rw [he,mem_insert,mem_singleton] at h
  rcases h with rfl|rfl
  · exact γ.source_mem_range
  · exact γ.target_mem_range

private theorem equidistant (L : CircleChain P Q p r) {i j : Fin L.n} {x y : ℝ²}
    (hx : x ∈ L.curve i) (hy : y ∈ L.curve j) : dist x p = dist y p := by
  rw [dist_comm x p,dist_comm y p,L.onCircle i _ hx,L.onCircle j _ hy]

/-- One arc, together with a circle at a different center, has at most one
common point: every point of the arc is on the same side of the line of centers. -/
theorem meet_unique (L : CircleChain P Q p r) (M : CircleChain P Q b s)
    (hb : b ∈ P) (hne : p ≠ b) {i : Fin L.n} {j j' : Fin M.n} {x y : ℝ²}
    (hx : x ∈ L.curve i) (hy : y ∈ L.curve i) (hx' : x ∈ M.curve j) (hy' : y ∈ M.curve j') :
    x = y :=
  eq_of_dist_eq_in_same_halfplane hne (L.equidistant hx hy) (M.equidistant hx' hy')
    (L.halfplanes i b hb hne x y hx hy)

theorem edge_ne (L : CircleChain P Q p r) (M : CircleChain P Q b s)
    (hb : b ∈ P) (hne : p ≠ b) (i : Fin L.n) (j : Fin M.n) : L.edge i ≠ M.edge j := by
  intro eq
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (show 1 < (L.edge i).card by rw [L.edge_card]; decide)
  exact hxy (Subtype.ext (L.meet_unique M hb hne ((L.mem_curve_iff _ _).mpr hx)
    ((L.mem_curve_iff _ _).mpr hy) ((M.mem_curve_iff _ _).mpr (eq ▸ hx))
    ((M.mem_curve_iff _ _).mpr (eq ▸ hy))))

/-- A shared point outside the data set forces four distinct endpoints. -/
theorem four_ends (L : CircleChain P Q p r) (M : CircleChain P Q b s)
    (hb : b ∈ P) (hne : p ≠ b) {i : Fin L.n} {j : Fin M.n} {z : ℝ²}
    (hz : z ∉ Q) (hz₁ : z ∈ L.curve i) (hz₂ : z ∈ M.curve j) :
    (L.edge i ∪ M.edge j).card = 4 := by
  have hd : Disjoint (L.edge i) (M.edge j) := disjoint_left.mpr fun v hv hv' =>
    hz ((L.meet_unique M hb hne ((L.mem_curve_iff _ _).mpr hv) hz₁
      ((M.mem_curve_iff _ _).mpr hv') hz₂) ▸ v.property)
  rw [card_union_of_disjoint hd,L.edge_card,M.edge_card]

/-- Given two fixed circles, the side of the line of centers determines both
participating edges at a crossing away from the data points. -/
theorem crossing_pair_eq (L : CircleChain P Q p r) (M : CircleChain P Q b s)
    (hb : b ∈ P) (hne : p ≠ b) {i i' : Fin L.n} {j j' : Fin M.n} {x y : ℝ²}
    (hx : x ∉ Q) (hy : y ∉ Q) (hxi : x ∈ L.curve i) (hxj : x ∈ M.curve j)
    (hyi : y ∈ L.curve i') (hyj : y ∈ M.curve j')
    (hsgn : decide (0 < lineSide p b x) = decide (0 < lineSide p b y)) : i = i' ∧ j = j' := by
  have hx' := L.halfplanes i b hb hne x x hxi hxi
  have hy' := L.halfplanes i' b hb hne y y hyi hyi
  have hs : 0 < lineSide p b x * lineSide p b y := by
    by_cases h : 0 < lineSide p b x
    · exact mul_pos h (by simpa [h] using hsgn)
    · have h' : ¬ 0 < lineSide p b y := by simpa [h] using hsgn
      apply mul_pos_of_neg_of_neg
      · exact lt_of_le_of_ne (le_of_not_gt h) (fun e => by simp [e] at hx')
      · exact lt_of_le_of_ne (le_of_not_gt h') (fun e => by simp [e] at hy')
  obtain rfl := eq_of_dist_eq_in_same_halfplane hne (L.equidistant hxi hyi) (M.equidistant hxj hyj) hs
  exact ⟨L.uniqueOutside _ _ _ hx hxi hyi,M.uniqueOutside _ _ _ hy hxj hyj⟩

end CircleChain

end OMA.Math652ArcOrder

/- Combine the disjoint radius classes into the finite drawing; the side of
the center line identifies an exceptional intersection of two circles. -/

namespace OMA.Math652ArcOrder

open Finset
open scoped EuclideanGeometry Classical

private abbrev RingTag (P Q : Finset ℝ²) := (p : P) × (Q.image (dist (p : ℝ²)))

private noncomputable abbrev chain {P Q : Finset ℝ²} (a : RingTag P Q) :=
  circleChain P Q a.1 a.1.property a.2

private abbrev EdgeTag (P Q : Finset ℝ²) := (a : RingTag P Q) × Fin (chain a).n

private noncomputable abbrev drawEdge {P Q : Finset ℝ²} (e : EdgeTag P Q) := (chain e.1).edge e.2
private noncomputable abbrev drawCurve {P Q : Finset ℝ²} (e : EdgeTag P Q) := (chain e.1).curve e.2

private theorem tagged_simple {P Q : Finset ℝ²} : Function.Injective (@drawEdge P Q) := by
  rintro ⟨⟨⟨p,hp⟩,⟨r,hr⟩⟩,i⟩ ⟨⟨⟨b,hb⟩,⟨s,hs⟩⟩,j⟩ eq
  let L := circleChain P Q p hp r
  let M := circleChain P Q b hb s
  change L.edge i = M.edge j at eq
  have same : p = b := by by_contra h; exact L.edge_ne M hb h i j eq
  subst b
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (L.edge i).card by rw [L.edge_card]; decide)
  have h1 := L.onCircle i x ((L.mem_curve_iff i x).mpr hx)
  have h2 := M.onCircle j x ((M.mem_curve_iff j x).mpr (eq ▸ hx))
  have hrs := h1.symm.trans h2
  cases hrs
  have hij := L.simple eq
  subst j
  rfl

private noncomputable def badPairs (P Q : Finset ℝ²) : Finset (EdgeTag P Q × EdgeTag P Q) :=
  univ.filter fun e => e.1 ≠ e.2 ∧ ∃ z : ℝ², z ∉ Q ∧ z ∈ drawCurve e.1 ∧ z ∈ drawCurve e.2

private theorem centers_ne {P Q : Finset ℝ²} {a b : EdgeTag P Q} (h : (a,b) ∈ badPairs P Q) :
    (a.1.1 : ℝ²) ≠ b.1.1 := by
  rcases a with ⟨⟨⟨p,hp⟩,⟨r,hr⟩⟩,i⟩
  rcases b with ⟨⟨⟨p',hp'⟩,⟨s,hs⟩⟩,j⟩
  obtain ⟨hne,z,hz,hi,hj⟩ := (mem_filter.mp h).2
  change p ≠ p'
  rintro rfl
  let L := circleChain P Q p hp r
  let M := circleChain P Q p hp' s
  have hrs := (L.onCircle i z hi).symm.trans (M.onCircle j z hj)
  subst s
  obtain rfl := L.uniqueOutside i j z hz hi hj
  exact hne rfl

private theorem card_badPairs {P Q : Finset ℝ²} :
    (badPairs P Q).card ≤ (Fintype.card (RingTag P Q))^2*2 := by
  let B := badPairs P Q
  have hv (u : B) : ∃ z : ℝ², z ∉ Q ∧ z ∈ drawCurve u.val.1 ∧ z ∈ drawCurve u.val.2 :=
    (mem_filter.mp u.property).2.2
  let w (u : B) : ℝ² := (hv u).choose
  have hw (u : B) : w u ∉ Q ∧ w u ∈ drawCurve u.val.1 ∧ w u ∈ drawCurve u.val.2 := (hv u).choose_spec
  let sgn (u : B) := decide (0 < lineSide u.val.1.1.1 u.val.2.1.1 (w u))
  let code (u : B) : (RingTag P Q × RingTag P Q) × Bool := ((u.val.1.1,u.val.2.1),sgn u)
  have inj : Function.Injective code := by
    rintro u v he
    have hc₁ : u.val.1.1 = v.val.1.1 := congrArg (fun t => t.1.1) he
    have hc₂ : u.val.2.1 = v.val.2.1 := congrArg (fun t => t.1.2) he
    have hsg : sgn u = sgn v := congrArg Prod.snd he
    obtain ⟨hu,hui,huj⟩ := hw u
    obtain ⟨hv',hvi,hvj⟩ := hw v
    have hne := centers_ne u.property
    rcases u with ⟨⟨⟨a,i⟩,⟨b,j⟩⟩,hu'⟩
    rcases v with ⟨⟨⟨a',i'⟩,⟨b',j'⟩⟩,hv''⟩
    change a = a' at hc₁
    change b = b' at hc₂
    subst a'; subst b'
    obtain ⟨rfl,rfl⟩ := (chain a).crossing_pair_eq (chain b) b.1.property hne hu hv' hui huj hvi hvj hsg
    rfl
  simpa [B,pow_two] using Fintype.card_le_of_injective code inj

private theorem tag_counts (P Q : Finset ℝ²) (D : ℕ) (hk : 2 ≤ P.card)
    (hD : ∀ p ∈ P, (Q.image (dist p)).card ≤ D) :
    Fintype.card (RingTag P Q) ≤ P.card*D ∧
    P.card*Q.card ≤ Fintype.card (EdgeTag P Q) + 4*P.card^2*(D+1) := by
  have hrings : Fintype.card (RingTag P Q) ≤ P.card*D := by
    rw [Fintype.card_sigma]
    calc _ ≤ ∑ _p : P, D := sum_le_sum fun p _ => by simpa using hD (p : ℝ²) p.property
         _ = _ := by simp
  have htotal : (∑ c : RingTag P Q, (layer Q c.1 c.2).card) = P.card*Q.card := by
    rw [Fintype.sum_sigma]
    have hf (p : P) : (∑ r : Q.image (dist (p : ℝ²)), (layer Q p r).card) = Q.card := by
      exact (sum_coe_sort (Q.image (dist (p : ℝ²))) (fun r : ℝ => (layer Q p r).card)).trans
        (card_eq_sum_card_image (dist (p : ℝ²)) Q).symm
    calc _ = ∑ _p : P, Q.card := sum_congr rfl fun p _ => hf p
         _ = _ := by simp
  have htag : (∑ c : RingTag P Q, (chain c).n) = Fintype.card (EdgeTag P Q) := by
    rw [Fintype.card_sigma]; simp
  have hsum := sum_le_sum (s := (univ : Finset (RingTag P Q))) fun c _ => (chain c).count
  simp only [sum_add_distrib,htotal,htag,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at hsum
  refine ⟨hrings,hsum.trans ?_⟩
  calc _ = Fintype.card (EdgeTag P Q) + Fintype.card (RingTag P Q) * (4*(P.card-1)+1) := by ring
       _ ≤ Fintype.card (EdgeTag P Q) + (P.card*D) * (4*P.card) :=
         Nat.add_le_add_left (Nat.mul_le_mul hrings (by omega)) _
       _ ≤ _ := by nlinarith


private theorem enough_edges (k q t e : ℕ) (hk : 16 ≤ k) (hq : 64*k^5 ≤ q)
    (ht : 1 ≤ t) (hs : (t:ℝ) ≤ Real.sqrt ((k:ℝ)*q)) (hc : k*q ≤ e+4*k^2*(t+1)) :
    k*q ≤ 2*e := by
  have sq : t^2 ≤ k*q := by
    exact_mod_cast (show (t:ℝ)^2 ≤ (k:ℝ)*q by
      calc _ ≤ (Real.sqrt ((k:ℝ)*q))^2 := by gcongr
           _ = _ := Real.sq_sqrt (by positivity))
  have kp : 4 ≤ k^2 := by nlinarith
  have lower : 256*k^3 ≤ q := by nlinarith [Nat.mul_le_mul_left (64*k^3) kp]
  have large : 16*k*t ≤ q := by
    by_contra! bad
    have h := Nat.mul_le_mul_left (256*k^2) sq
    have hh := Nat.mul_le_mul_right q lower
    nlinarith only [h,hh,Nat.mul_self_lt_mul_self bad]
  nlinarith [Nat.mul_le_mul_left k large,Nat.mul_le_mul_left (8*k^2) ht]

set_option maxHeartbeats 2000000 in
private theorem orientedDrawing : OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1_H1_R1.H2 := by
  classical
  intro P Q _ hk hq t ht hs hD
  let I := EdgeTag P Q
  have drawn (i : I) := (chain i.1).drawn i.2
  choose x y ne pair paths using drawn
  choose path pinj prange ends using paths
  let tag (i : I) : ℝ² × ℝ² := ((x i).val,(y i).val)
  have inj : Function.Injective tag := by
    intro i j eq
    have hx : x i = x j := Subtype.ext (congrArg Prod.fst eq)
    have hy : y i = y j := Subtype.ext (congrArg Prod.snd eq)
    exact tagged_simple (by rw [show drawEdge i = _ from pair i,show drawEdge j = _ from pair j,hx,hy])
  have swap_ne (i j : I) : tag j ≠ (tag i).swap := by
    intro eq
    have hx : x j = y i := Subtype.ext (congrArg Prod.fst eq)
    have hy : y j = x i := Subtype.ext (congrArg Prod.snd eq)
    have same : j = i := tagged_simple (by
      rw [show drawEdge i = _ from pair i,show drawEdge j = _ from pair j,hx,hy,pair_comm])
    exact ne i (same ▸ hx)
  let E := univ.image tag
  let γ := Function.extend tag (fun i : I => ((path i).extend : ℝ → ℝ²)) (fun _ _ => 0)
  have curve i : γ (tag i) = (path i).extend := inj.extend_apply _ _ i
  let Z (i : I) := γ (tag i) '' Set.Ioo (0:ℝ) 1
  have vert (i : I) {s : ℝ} (h : s ∈ Set.Icc (0:ℝ) 1) :
      γ (tag i) s = path i ⟨s,h⟩ := by rw [curve]; exact (path i).extend_extends' ⟨s,h⟩
  have contained (i : I) {z : ℝ²} (hz : z ∈ Z i) : z ∈ drawCurve i := by
    obtain ⟨s,hs,rfl⟩ := hz
    rw [show drawCurve i = _ from prange i]
    exact ⟨⟨s,hs.1.le,hs.2.le⟩,(vert i ⟨hs.1.le,hs.2.le⟩).symm⟩
  have avoids (i : I) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) : γ (tag i) s ∉ Q := by
    intro hQ
    let z : Q := ⟨_,hQ⟩
    have hz := ends i z (contained i ⟨s,hs,rfl⟩)
    rw [pair i,mem_insert,mem_singleton] at hz
    let u : unitInterval := ⟨s,hs.1.le,hs.2.le⟩
    have val : z.val = path i u := vert i u.property
    rcases hz with h | h
    · have eq : u = 0 := pinj i (val.symm.trans ((congrArg Subtype.val h).trans (path i).source.symm))
      exact hs.1.ne' (congrArg Subtype.val eq)
    · have eq : u = 1 := pinj i (val.symm.trans ((congrArg Subtype.val h).trans (path i).target.symm))
      exact hs.2.ne (congrArg Subtype.val eq)
  have bad {i j : I} (hne : i ≠ j) {z} (hz : z ∈ Z i ∩ Z j) : (i,j) ∈ badPairs P Q := by
    obtain ⟨s,hs,eq⟩ := hz.1
    exact mem_filter.mpr ⟨mem_univ _,hne,z,eq ▸ avoids i hs,contained _ hz.1,contained _ hz.2⟩
  have unique {i j : I} (hne : i ≠ j) : (Z i ∩ Z j).Subsingleton := by
    intro z hz w hw
    exact (chain i.1).meet_unique (chain j.1) j.1.1.property (centers_ne (bad hne hz))
      (contained i hz.1) (contained i hw.1) (contained j hz.2) (contained j hw.2)
  obtain ⟨rings,count⟩ := tag_counts P Q t (by omega) (by simpa only [dist_comm] using hD)
  refine ⟨E,γ,?_,?_,?_,?_⟩
  · have eq : E.card = Fintype.card I := (card_image_of_injective univ inj).trans card_univ
    rw [eq]
    exact enough_edges _ _ _ _ hk hq ht hs count
  · intro e he
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    refine ⟨(x i).property,(y i).property,fun h => ne i (Subtype.ext h),?_,?_,?_,?_,?_,fun s h => avoids i h⟩
    · rintro h; obtain ⟨j,_,eq⟩ := mem_image.mp h; exact swap_ne i j eq
    · rw [curve]; exact (path i).extend_zero
    · rw [curve]; exact (path i).extend_one
    · rw [curve]; exact (path i).continuous_extend.continuousOn
    · intro a ha b hb eq
      exact congrArg Subtype.val (pinj i ((vert i ha).symm.trans (eq.trans (vert i hb))))
  · intro e he f hf hne
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    obtain ⟨j,_,rfl⟩ := mem_image.mp hf
    exact (unique (fun h => hne (congrArg tag h))).finite
  · let W (i j : I) : ℕ := if (i,j) ∈ badPairs P Q then 1 else 0
    have bound (i j : I) (hne : i ≠ j) : (Z i ∩ Z j).ncard ≤ W i j := by
      by_cases h : (i,j) ∈ badPairs P Q
      · simpa [W,h] using (Set.ncard_le_one_iff (unique hne).finite).mpr (fun ha hb => unique hne ha hb)
      · have empty : Z i ∩ Z j = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun z hz => h (bad hne hz)
        simp [empty,W,h]
    have total : (∑ i, ∑ j, W i j) = (badPairs P Q).card := by
      rw [← Fintype.sum_prod_type']
      simp [W]
    change (∑ e ∈ E, ∑ f ∈ E.erase e, ((γ e '' Set.Ioo 0 1) ∩ (γ f '' Set.Ioo 0 1)).ncard) ≤ _
    dsimp only [E]
    rw [sum_image inj.injOn]
    calc
      _ ≤ ∑ i, ∑ j, W i j := by
        apply sum_le_sum
        intro i _
        rw [← image_erase inj,sum_image inj.injOn]
        exact (sum_le_sum (fun j hj => bound i j (ne_of_mem_erase hj).symm)).trans
          (sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _))
      _ = _ := total
      _ ≤ _ := card_badPairs
      _ ≤ 2*(P.card*t)^2 := by rw [mul_comm]; gcongr

end OMA.Math652ArcOrder

theorem OMA.solution : OMA.R_Erdos652_erdos_652_variants_order_sqrt_R1_H1_R1.H2 :=
  OMA.Math652ArcOrder.orientedDrawing

