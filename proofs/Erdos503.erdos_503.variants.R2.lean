import FormalConjectures.ErdosProblems.«503»

/-!
# Kelly's theorem on planar isosceles sets

The lower bound uses oblique coordinates for a regular pentagon and its center.
For the upper bound, color each edge by its squared length. A triangle uses at
most two colors. We prove that either the whole graph uses at most two colors,
or it has a proper subset of at least two vertices such that each exterior
vertex sees just one color on its edges into the subset.

In the first case a quadratic moment argument rules out seven planar points.
In the second case the exterior lies on a perpendicular bisector. Two exterior
points would put the subset on the intersection of two circles. A single
exterior point would put six points on a circle. Neither is possible.
-/

namespace OMA.E503R2

open scoped EuclideanGeometry

private def pentCoords (t : ℝ) : Fin 6 → ℝ × ℝ :=
  ![(0, 0), (1, 0), (0, 1), (-1, t), (-t, -t), (t, -1)]

private noncomputable def skewPoint (t u : ℝ) (p : ℝ × ℝ) : ℝ² :=
  WithLp.toLp 2 ![p.1 + t * p.2 / 2, u * p.2]

private lemma skew_dist (t u : ℝ) (hu : u^2 = 1 - t^2 / 4) (p q : ℝ × ℝ) :
    dist (skewPoint t u p) (skewPoint t u q) ^ 2 =
      (p.1 - q.1)^2 + t * (p.1 - q.1) * (p.2 - q.2) + (p.2 - q.2)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, skewPoint, Real.dist_eq, sq_abs]
  linear_combination (p.2 - q.2)^2 * hu

private def chordClass (i j : Fin 6) : Fin 4 :=
  if i = j then 0 else if i = 0 ∨ j = 0 then 1 else
    if i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
       (i.val = 1 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 1) then 2 else 3

private def chordSq (t : ℝ) (c : Fin 4) : ℝ :=
  if c.val = 0 then 0 else if c.val = 1 then 1 else if c.val = 2 then 2 - t else 3 + t

private lemma pent_dist (t u : ℝ) (ht : t^2 + t = 1) (hu : u^2 = 1 - t^2 / 4)
    (i j : Fin 6) :
    dist (skewPoint t u (pentCoords t i)) (skewPoint t u (pentCoords t j)) ^ 2 =
      chordSq t (chordClass i j) := by
  have ht3 : t^3 = 2*t-1 := by linear_combination (t-1)*ht
  rw [skew_dist t u hu]
  fin_cases i <;> fin_cases j <;> norm_num [pentCoords, chordSq, chordClass, Fin.val_ofNat] <;>
    ring_nf <;> linarith only [ht, ht3]

private lemma classes_isosceles : ∀ i j k : Fin 6,
    chordClass i j = chordClass j k ∨ chordClass j k = chordClass k i ∨
      chordClass k i = chordClass i j := by decide

/-- The origin and the five vertices of a regular pentagon, written in an oblique basis. -/
theorem six_exists : ∃ A : Set ℝ², A.IsIsosceles ∧ A.ncard = 6 := by
  let t : ℝ := (Real.sqrt 5 - 1) / 2
  have h5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h5' := Real.sqrt_nonneg 5
  have ht : t^2 + t = 1 := by dsimp [t]; nlinarith
  have ht0 : 0 ≤ t := by dsimp [t]; nlinarith
  have ht1 : t ≤ 1 := by dsimp [t]; nlinarith
  let u := Real.sqrt (1 - t^2 / 4)
  have hu : u^2 = 1 - t^2 / 4 := Real.sq_sqrt (by linarith)
  let v (i : Fin 6) := skewPoint t u (pentCoords t i)
  have hdist (i j : Fin 6) : dist (v i) (v j)^2 = chordSq t (chordClass i j) :=
    pent_dist t u ht hu i j
  have hinj : Function.Injective v := by
    intro i j he
    by_contra h
    have hc : chordClass i j ≠ 0 := by
      unfold chordClass
      simp only [if_neg h]
      split <;> first | decide | split <;> decide
    have hp (c : Fin 4) (hc' : c ≠ 0) : 0 < chordSq t c := by
      fin_cases c
      · exact (hc' rfl).elim
      · change (0 : ℝ) < 1
        norm_num
      · change 0 < 2 - t
        linarith
      · change 0 < 3 + t
        linarith
    have hpos := hp _ hc
    have hd := hdist i j
    rw [he, dist_self, zero_pow (by decide)] at hd
    linarith
  refine ⟨Set.range v, ⟨⟨⟨v 0, 0, rfl⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _ _ _
    have eqdist (a b c d : Fin 6) (h : chordClass a b = chordClass c d) :
        dist (v a) (v b) = dist (v c) (v d) := by
      apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
      rw [hdist, hdist, h]
    rcases classes_isosceles i j k with h | h | h
    · exact Or.inl (eqdist _ _ _ _ h)
    · exact Or.inr (Or.inl (eqdist _ _ _ _ h))
    · exact Or.inr (Or.inr (eqdist _ _ _ _ h))
  · rw [Set.ncard_range_of_injective hinj]
    simp

noncomputable def coordD {ι : Type*} (x y : ι → ℝ) (i j : ι) : ℝ :=
  (x i - x j)^2 + (y i - y j)^2

variable {ι : Type*} {x y : ι → ℝ}

private def Separated (x y : ι → ℝ) : Prop :=
  ∀ i j, i ≠ j → x i ≠ x j ∨ y i ≠ y j

private def TripleEq (D : ι → ι → ℝ) : Prop :=
  ∀ i j k, D i j = D j k ∨ D j k = D k i ∨ D k i = D i j

private theorem coord_symm (i j : ι) : coordD x y i j = coordD x y j i := by
  unfold coordD
  ring

private theorem coord_pos (sep : Separated x y) {a b : ι} (hab : a ≠ b) :
    0 < coordD x y a b := by
  unfold coordD
  rcases sep a b hab with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr h)) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (sub_ne_zero.mpr h))

/-- On a level set of the difference of two squared distances, the perpendicular
coordinate determines the point. Its squared increments give the original metric
up to a fixed factor. -/
private theorem project_level (sep : Separated x y) (s : Finset ι) {a b : ι} (hab : a ≠ b)
    (level : ∀ i ∈ s, ∀ j ∈ s,
      coordD x y a i - coordD x y b i = coordD x y a j - coordD x y b j) :
    ∃ t : ι → ℝ, Set.InjOn t (↑s) ∧
      (∀ i ∈ s, ∀ j ∈ s, (t i - t j)^2 = coordD x y a b * coordD x y i j) ∧
      (∀ i ∈ s, ∀ j ∈ s, coordD x y a i = coordD x y a j →
        (t i - t a)^2 = (t j - t a)^2) := by
  let u := x a - x b
  let v := y a - y b
  let l (i : ι) := u * x i + v * y i
  let t (i : ι) := v * x i - u * y i
  have same (i) (hi : i ∈ s) (j) (hj : j ∈ s) : l i = l j := by
    dsimp [l, u, v]
    have e := level i hi j hj
    unfold coordD at e
    linear_combination -e/2
  have rot (i j : ι) :
      (l i-l j)^2 + (t i-t j)^2 = coordD x y a b * coordD x y i j := by
    dsimp [l, t, u, v, coordD]
    ring
  have diff (i) (hi : i ∈ s) (j) (hj : j ∈ s) :
      (t i-t j)^2 = coordD x y a b * coordD x y i j := by
    simpa only [same i hi j hj, sub_self, zero_pow (by decide : 2 ≠ 0), zero_add] using rot i j
  refine ⟨t, ?_, diff, ?_⟩
  · intro i hi j hj eqt
    by_contra h
    have hp := mul_pos (coord_pos sep hab) (coord_pos sep h)
    simp [← diff i hi j hj, eqt] at hp
  · intro i hi j hj he
    rw [coord_symm (x := x) (y := y) a i, coord_symm (x := x) (y := y) a j] at he
    have e := rot i a
    rw [same i hi j hj, he] at e
    linarith only [e, rot j a]

private theorem ordered_mid {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (h : (a-b)^2 = (b-c)^2 ∨ (b-c)^2 = (c-a)^2 ∨ (c-a)^2 = (a-b)^2) :
    a + c = 2*b := by
  simp only [sq_eq_sq_iff_abs_eq_abs, abs_of_neg (sub_neg.mpr hab),
    abs_of_neg (sub_neg.mpr hbc), abs_of_pos (sub_pos.mpr (hab.trans hbc))] at h
  rcases h with h | h | h <;> linarith

private theorem real_line_bound (s : Finset ℝ)
    (iso : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s,
      (a-b)^2 = (b-c)^2 ∨ (b-c)^2 = (c-a)^2 ∨ (c-a)^2 = (a-b)^2) :
    s.card ≤ 3 := by
  by_contra! h
  have hf : 4 ≤ s.card := h
  let e := s.orderEmbOfCardLe hf
  have mem (i : Fin 4) : e i ∈ s := s.orderEmbOfCardLe_mem hf i
  have h01 := e.strictMono (show (0 : Fin 4) < 1 by decide)
  have h12 := e.strictMono (show (1 : Fin 4) < 2 by decide)
  have h23 := e.strictMono (show (2 : Fin 4) < 3 by decide)
  have m := ordered_mid h01 h12 (iso _ (mem 0) _ (mem 1) _ (mem 2))
  have n := ordered_mid h01 (h12.trans h23) (iso _ (mem 0) _ (mem 1) _ (mem 3))
  linarith

private theorem level_bound (sep : Separated x y) (tri : TripleEq (coordD x y))
    (s : Finset ι) {a b : ι} (hab : a ≠ b)
    (level : ∀ i ∈ s, ∀ j ∈ s,
      coordD x y a i - coordD x y b i = coordD x y a j - coordD x y b j) :
    s.card ≤ 3 := by
  classical
  obtain ⟨t, hinj, he, _⟩ := project_level sep s hab level
  rw [← Finset.card_image_of_injOn hinj]
  apply real_line_bound
  intro _ ha _ hb _ hc
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
  rw [he i hi j hj, he j hj k hk, he k hk i hi]
  rcases tri i j k with h | h | h <;> simp [h]

/-- Two circles with distinct centers have at most two common points. -/
private theorem circles_bound (sep : Separated x y) (s : Finset ι) {a b : ι} (hab : a ≠ b)
    (ha : ∀ i ∈ s, ∀ j ∈ s, coordD x y a i = coordD x y a j)
    (hb : ∀ i ∈ s, ∀ j ∈ s, coordD x y b i = coordD x y b j) :
    s.card ≤ 2 := by
  classical
  obtain ⟨t, hinj, _, he⟩ := project_level sep s hab (fun i hi j hj => by
    rw [ha i hi j hj, hb i hi j hj])
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  rw [← Finset.card_image_of_injOn hinj]
  apply le_trans (Finset.card_le_card (t := {t p, 2*t a-t p}) ?_) Finset.card_le_two
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  have e := he i hi p hp (ha i hi p hp)
  have fac : (t i - t p) * (t i - (2*t a - t p)) = 0 := by
    linear_combination e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact (mul_eq_zero.mp fac).imp sub_eq_zero.mp sub_eq_zero.mp

/-- Paths whose edges all have color `c`, within the vertex set `s`. -/
private def gPath (d : ι → ι → ℝ) (s : Finset ι) (c : ℝ) (u v : ι) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ s ∧ b ∈ s ∧ d a b = c) u v

private def gSpan (d : ι → ι → ℝ) (s : Finset ι) (c : ℝ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, gPath d s c a b

private theorem gReverse {d : ι → ι → ℝ} (hs : ∀ a b, d a b = d b a)
    {s : Finset ι} {c : ℝ} {u v : ι} (h : gPath d s c u v) : gPath d s c v u := by
  induction h with
  | refl => exact .refl
  | @tail w z _ he ih => exact ih.head ⟨he.2.1, he.1, (hs z w).trans he.2.2⟩

private theorem gEnd {d : ι → ι → ℝ} {s : Finset ι} {c : ℝ} {u v : ι}
    (h : gPath d s c u v) (hu : u ∈ s) : v ∈ s := by
  cases h with
  | refl => exact hu
  | tail _ he => exact he.2.1

private theorem gCross {d : ι → ι → ℝ} {s : Finset ι} {c : ℝ}
    (hc : gSpan d s c) (p : ι → Prop) {u v : ι}
    (hu : u ∈ s) (hv : v ∈ s) (hpu : p u) (hpv : ¬p v) :
    ∃ x ∈ s, ∃ y ∈ s, p x ∧ ¬p y ∧ d x y = c := by
  classical
  by_contra hn
  apply hpv
  have h := hc u hu v hv
  clear hv hpv
  induction h with
  | refl => exact hpu
  | tail _ he ih =>
    by_contra hpy
    exact hn ⟨_, he.1, _, he.2.1, ih, hpy, he.2.2⟩

/-- From outside a monochromatic component, all edges into it have the same color. -/
private theorem gUniform {d : ι → ι → ℝ} (hs : ∀ a b, d a b = d b a)
    (ht : ∀ i j k, d i j = d j k ∨ d j k = d k i ∨ d k i = d i j)
    {s : Finset ι} {c : ℝ} {u v z : ι} (hz : z ∈ s)
    (hout : ¬gPath d s c u z) (h : gPath d s c u v) : d u z = d v z := by
  induction h with
  | refl => rfl
  | @tail a b hpa he ih =>
    have hpb := hpa.tail he
    have ha : d a z ≠ c := fun h => hout (hpa.tail ⟨he.1, hz, h⟩)
    have hb : d b z ≠ c := fun h => hout (hpb.tail ⟨he.2.1, hz, h⟩)
    rcases ht a b z with h | h | h
    · exact (hb (h.symm.trans he.2.2)).elim
    · exact ih.trans (h.trans (hs z a)).symm
    · exact (ha ((hs a z).trans (h.trans he.2.2))).elim

private theorem gNeighbor [DecidableEq ι] {d : ι → ι → ℝ}
    {s : Finset ι} {v : ι} {c : ℝ} (hne : s.Nonempty) (hv : v ∉ s)
    (hc : gSpan d (insert v s) c) : ∃ w ∈ s, d v w = c := by
  obtain ⟨w, hw⟩ := hne
  obtain ⟨_, _, y, hy, rfl, hny, hcol⟩ :=
    gCross hc (· = v) (Finset.mem_insert_self v s) (Finset.mem_insert_of_mem hw) rfl
      (fun e => hv (e ▸ hw))
  exact ⟨y, (Finset.mem_insert.mp hy).resolve_left hny, hcol⟩

private theorem gTouch [DecidableEq ι] {d : ι → ι → ℝ} (hs : ∀ a b, d a b = d b a)
    {s : Finset ι} {v u : ι} {c : ℝ} (hu : u ∈ s) (hv : v ∉ s)
    (hc : gSpan d (insert v s) c) :
    ∃ w ∈ s, gPath d s c u w ∧ d v w = c := by
  obtain ⟨w, _, y, hy, hpath, hnot, hcol⟩ :=
    gCross hc (gPath d s c u) (Finset.mem_insert_of_mem hu)
      (Finset.mem_insert_self v s) .refl (fun h => hv (gEnd h hu))
  have hw := gEnd hpath hu
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact ⟨w, hw, hpath, (hs _ _).trans hcol⟩
  · exact (hnot (hpath.tail ⟨hw, hy, hcol⟩)).elim

private theorem gObstruct [DecidableEq ι] {d : ι → ι → ℝ} (hs : ∀ a b, d a b = d b a)
    (ht : ∀ i j k, d i j = d j k ∨ d j k = d k i ∨ d k i = d i j)
    {s : Finset ι} {v : ι} {c b g : ℝ} (hv : v ∉ s) (hcb : c ≠ b) (hbg : b ≠ g)
    (hgc : g ≠ c) (hc : gSpan d (insert v s) c) (hb : gSpan d (insert v s) b)
    (hg : gSpan d (insert v s) g) (hn : ¬gSpan d s c) : False := by
  classical
  unfold gSpan at hn
  push Not at hn
  obtain ⟨p, hp, q, hq, hpq⟩ := hn
  obtain ⟨u, hu, hvu⟩ := gNeighbor ⟨p, hp⟩ hv hb
  obtain ⟨w, hw, hvw⟩ := gNeighbor ⟨p, hp⟩ hv hg
  have force {i j : ι} {k : ℝ} (hi : i ∈ s) (hj : j ∈ s)
      (hij : ¬gPath d s c i j) (hvi : d v i = k) (hvj : d v j = c) (hk : c ≠ k) :
      d i j = k := by
    have hnij : d i j ≠ c := fun h => hij (.single ⟨hi, hj, h⟩)
    rcases ht v i j with h | h | h
    · exact h.symm.trans hvi
    · exact (hnij (h.trans ((hs j v).trans hvj))).elim
    · exact (hk (hvj.symm.trans ((hs v j).trans (h.trans hvi)))).elim
  by_cases huw : gPath d s c u w
  · obtain ⟨z, hz, huz⟩ : ∃ z ∈ s, ¬gPath d s c u z := by
      by_contra! hall
      exact hpq ((gReverse hs (hall p hp)).trans (hall q hq))
    obtain ⟨t, htmem, hzt, hvt⟩ := gTouch hs hz hv hc
    have hut : ¬gPath d s c u t := fun h => huz (h.trans (gReverse hs hzt))
    have hwt : ¬gPath d s c w t := fun h => hut (huw.trans h)
    exact hbg ((force hu htmem hut hvu hvt hcb).symm.trans
      ((gUniform hs ht htmem hut huw).trans (force hw htmem hwt hvw hvt hgc.symm)))
  · obtain ⟨a, ha, hua, hva⟩ := gTouch hs hu hv hc
    obtain ⟨t, htm, hwt, hvt⟩ := gTouch hs hw hv hc
    have hut : ¬gPath d s c u t := fun h => huw (h.trans (gReverse hs hwt))
    have hwa : ¬gPath d s c w a := fun h => huw (hua.trans (gReverse hs h))
    have hwu : ¬gPath d s c w u := fun h => huw (gReverse hs h)
    have h1 := gUniform hs ht hu hwu hwt
    have h2 := gUniform hs ht hw huw hua
    exact hbg ((force hu htm hut hvu hvt hcb).symm.trans
      ((hs u t).trans (h1.symm.trans ((hs w u).trans (h2.trans ((hs a w).trans
        (force hw ha hwa hvw hva hgc.symm)))))))

/-- Three distinct colors cannot each connect all the vertices. -/
private theorem gNoThree [DecidableEq ι] {d : ι → ι → ℝ} (hs : ∀ a b, d a b = d b a)
    (ht : ∀ i j k, d i j = d j k ∨ d j k = d k i ∨ d k i = d i j)
    {c b g : ℝ} (hcb : c ≠ b) (hbg : b ≠ g) (hgc : g ≠ c) (s : Finset ι) :
    1 < s.card → gSpan d s c → gSpan d s b → gSpan d s g → False := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
    intro hsize hc hb hg
    by_cases hbig : 1 < s.card
    · by_cases sc : gSpan d s c
      · by_cases sb : gSpan d s b
        · exact gObstruct hs ht hv hgc hcb hbg hg hc hb (fun sg => ih hbig sc sb sg)
        · exact gObstruct hs ht hv hbg hgc hcb hb hg hc sb
      · exact gObstruct hs ht hv hcb hbg hgc hc hb hg sc
    · rw [Finset.card_insert_of_notMem hv] at hsize
      obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
      obtain ⟨x, hx, hxcol⟩ := gNeighbor (Finset.singleton_nonempty w) hv hc
      obtain ⟨y, hy, hycol⟩ := gNeighbor (Finset.singleton_nonempty w) hv hb
      simp only [Finset.mem_singleton] at hx hy
      exact hcb (hxcol.symm.trans ((congrArg (d v) (hx.trans hy.symm)).trans hycol))

/-- A rainbow-free complete graph uses at most two colors or has a proper homogeneous subset. -/
theorem gallai {ι : Type*} [Fintype ι] (d : ι → ι → ℝ) (hs : ∀ a b, d a b = d b a)
    (ht : ∀ i j k, d i j = d j k ∨ d j k = d k i ∨ d k i = d i j) :
    (∃ a b : ℝ, ∀ i j, i ≠ j → d i j = a ∨ d i j = b) ∨
    ∃ M : Finset ι, 2 ≤ M.card ∧ M.card < Fintype.card ι ∧
      ∀ z, z ∉ M → ∀ i ∈ M, ∀ j ∈ M, d z i = d z j := by
  classical
  by_contra! hn
  obtain ⟨hcolors, hmodule⟩ := hn
  obtain ⟨i, j, hij, _, _⟩ := hcolors 0 0
  obtain ⟨k, l, hkl, h₁, _⟩ := hcolors (d i j) (d i j)
  obtain ⟨p, q, hpq, h₂, h₃⟩ := hcolors (d i j) (d k l)
  have hsize : 1 < (Finset.univ : Finset ι).card :=
    Finset.one_lt_card.mpr ⟨i, Finset.mem_univ _, j, Finset.mem_univ _, hij⟩
  have hex : ∃ a b, a ≠ b ∧ ¬gSpan d Finset.univ (d a b) := by
    by_contra! hall
    exact gNoThree hs ht h₁.symm h₃.symm h₂ Finset.univ hsize
      (hall i j hij) (hall k l hkl) (hall p q hpq)
  obtain ⟨a, b, hab, hnot⟩ := hex
  let m := Finset.univ.filter (gPath d Finset.univ (d a b) a)
  have hm (x : ι) : x ∈ m ↔ gPath d Finset.univ (d a b) a x := by simp [m]
  have hm₂ : 2 ≤ m.card := Finset.one_lt_card.mpr
    ⟨a, (hm a).mpr .refl, b, (hm b).mpr (.single ⟨Finset.mem_univ _, Finset.mem_univ _, rfl⟩), hab⟩
  have hlt : m.card < Fintype.card ι := by
    rw [← Finset.card_univ]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro e
    apply hnot
    intro i _ j _
    have all (x : ι) := (hm x).mp (e ▸ Finset.mem_univ x)
    exact (gReverse hs (all i)).trans (all j)
  obtain ⟨z, hz, i, hi, j, hj, hne⟩ := hmodule m hm₂ hlt
  have hout : ¬gPath d Finset.univ (d a b) a z := fun h => hz ((hm z).mpr h)
  exact hne ((hs z i).trans ((gUniform hs ht (Finset.mem_univ _) hout ((hm i).mp hi)).symm.trans
    ((gUniform hs ht (Finset.mem_univ _) hout ((hm j).mp hj)).trans (hs j z))))

private theorem gallaiOn (D : ι → ι → ℝ) (hs : ∀ i j, D i j = D j i)
    (ht : TripleEq D) (s : Finset ι) :
    (∃ a b : ℝ, ∀ i ∈ s, ∀ j ∈ s, i ≠ j → D i j = a ∨ D i j = b) ∨
    ∃ M : Finset ι, M ⊆ s ∧ 2 ≤ M.card ∧ M.card < s.card ∧
      ∀ z ∈ s, z ∉ M → ∀ i ∈ M, ∀ j ∈ M, D z i = D z j := by
  classical
  rcases gallai (fun i j : s => D i j) (fun i j => hs i j) (fun i j k => ht i j k) with
    ⟨a, b, h⟩ | ⟨m, h₂, hlt, hu⟩
  · left
    refine ⟨a, b, fun i hi j hj hij => ?_⟩
    exact h ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (congrArg Subtype.val h))
  · right
    let M := m.map (Function.Embedding.subtype (· ∈ s))
    have hc : M.card = m.card := Finset.card_map _
    have hm (i : s) : i.val ∈ M ↔ i ∈ m := Finset.mem_map' (Function.Embedding.subtype (· ∈ s))
    have hsub : M ⊆ s := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact j.2
    refine ⟨M, hsub, by omega, by simpa [hc] using hlt, ?_⟩
    intro z hz hn i hi j hj
    exact hu ⟨z,hz⟩ (fun h => hn ((hm ⟨z,hz⟩).mpr h))
      ⟨i,hsub hi⟩ ((hm ⟨i,hsub hi⟩).mp hi) ⟨j,hsub hj⟩ ((hm ⟨j,hsub hj⟩).mp hj)

/-- An isosceles subset of a circle has at most five points. -/
private theorem circle_bound (sep : Separated x y) (tri : TripleEq (coordD x y))
    (s : Finset ι) {o : ι} (ho : o ∉ s)
    (circ : ∀ i ∈ s, ∀ j ∈ s, coordD x y o i = coordD x y o j) : s.card ≤ 5 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
  · simp
  rcases gallaiOn (coordD x y) coord_symm tri s with ⟨a, b, hc⟩ | ⟨M, hsub, h₂, hlt, hu⟩
  · let T (r : ℝ) := s.filter (fun i => coordD x y z i = r)
    have small (r : ℝ) : (T r).card ≤ 2 := by
      apply circles_bound sep _ (a := o) (b := z) (fun e => ho (e ▸ hz))
      · intro i hi j hj
        exact circ i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
      · intro i hi j hj
        exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    have cover : s.erase z ⊆ T a ∪ T b := by
      intro i hi
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hi
      rcases hc z hz i hmem hne.symm with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem,h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem,h⟩)
    have bound := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
    rw [Finset.card_erase_of_mem hz] at bound
    have := small a
    have := small b
    omega
  · obtain ⟨p, hp, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hM := circles_bound sep M (a := o) (b := p) (fun e => ho (e ▸ hp))
      (fun i hi j hj => circ i (hsub hi) j (hsub hj)) (hu p hp hnot)
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h₂
    have lev (k : ι) (hk : k ∈ s \ M) : coordD x y i k = coordD x y j k :=
      (coord_symm i k).trans ((hu k (Finset.mem_sdiff.mp hk).1 (Finset.mem_sdiff.mp hk).2
        i hi j hj).trans (coord_symm k j))
    have rest := level_bound sep tri (s \ M) hij (fun k hk l hl => by rw [lev k hk, lev l hl]; simp)
    rw [Finset.card_sdiff_of_subset hsub] at rest
    omega

private theorem paired_sum_zero (w : Fin 7 → ℝ) (m g : Fin 7 → Fin 6 → ℝ)
    (hm : ∀ k, ∑ i, w i * m i k = 0) :
    ∑ i, ∑ j, (w i * w j) * (∑ k, g i k * m j k) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  simp_rw [show ∀ j, (w i * w j) * (g i k * m j k) =
      (w i * g i k) * (w j * m j k) by intro j; ring]
  rw [← Finset.mul_sum, hm, mul_zero]

/-- The six monomials of degree at most two have a nonzero annihilating weight vector
on seven points. Pairing the two-distance polynomial with those weights leaves only its
strictly positive diagonal contribution. -/
theorem two_impossible (x y : Fin 7 → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ht : ∀ i j, i ≠ j → coordD x y i j = a ∨ coordD x y i j = b) : False := by
  classical
  let m (i : Fin 7) : Fin 6 → ℝ := ![1, x i, y i, x i ^ 2, x i * y i, y i ^ 2]
  let u (i : Fin 7) := x i ^ 2 + y i ^ 2
  let g (i : Fin 7) : Fin 6 → ℝ :=
    ![u i ^ 2 - (a + b) * u i + a * b / 2,
      (a + b) * x i - 4 * x i * u i, (a + b) * y i - 4 * y i * u i,
      3 * x i ^ 2 + y i ^ 2, 4 * x i * y i, x i ^ 2 + 3 * y i ^ 2]
  have hdep : ¬LinearIndependent ℝ m := by
    intro h
    have hn := h.fintype_card_le_finrank
    norm_num [Module.finrank_pi] at hn
  obtain ⟨w, hw, l, hl⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hm (k : Fin 6) : ∑ i, w i * m i k = 0 := by
    simpa [Finset.sum_apply] using congrFun hw k
  let K i j := (coordD x y i j - a) * (coordD x y i j - b)
  have expand (i j : Fin 7) : K i j = (∑ k, g i k * m j k) + (∑ k, g j k * m i k) := by
    simp [K, m, g, u, coordD, Fin.sum_univ_succ]
    ring
  have hz := paired_sum_zero w m g hm
  have htwin : ∑ i, ∑ j, (w i * w j) * (∑ k, g j k * m i k) = 0 := by
    rw [Finset.sum_comm]
    simpa only [mul_comm (w _) (w _)] using hz
  have hzK : ∑ i, ∑ j, (w i * w j) * K i j = 0 := by
    simp_rw [expand, mul_add, Finset.sum_add_distrib]
    rw [hz, htwin, add_zero]
  have diag (i : Fin 7) : ∑ j, (w i * w j) * K i j = w i ^ 2 * (a * b) := by
    rw [Finset.sum_eq_single i]
    · simp [K, coordD, pow_two]
    · intro j _ hj
      rcases ht i j hj.symm with h | h <;> simp [K, h]
    · simp
  simp_rw [diag] at hzK
  have hpos : 0 < ∑ i, w i ^ 2 * (a * b) :=
    Finset.sum_pos' (fun i _ => mul_nonneg (sq_nonneg _) (mul_pos ha hb).le)
      ⟨l, Finset.mem_univ _, mul_pos (sq_pos_of_ne_zero hl) (mul_pos ha hb)⟩
  linarith

def NoSeven : Prop :=
  ∀ x y : Fin 7 → ℝ, (∀ i j, i ≠ j → x i ≠ x j ∨ y i ≠ y j) →
    (∀ i j k, coordD x y i j = coordD x y j k ∨ coordD x y j k = coordD x y k i ∨
      coordD x y k i = coordD x y i j) → False

private theorem triple_of_members {A : Set ℝ²} (hA : A.IsIsosceles)
    {a b c : ℝ²} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) : IsIsosceles a b c := by
  rcases eq_or_ne a b with rfl | hab
  · exact Or.inr (Or.inl (dist_comm _ _))
  rcases eq_or_ne b c with rfl | hbc
  · exact Or.inr (Or.inr (dist_comm _ _))
  rcases eq_or_ne a c with rfl | hac
  · exact Or.inl (dist_comm _ _)
  exact hA.2 ha hb hc hab hbc hac

private theorem ncard_le_of_noSeven (upper : NoSeven) {A : Set ℝ²} (hA : A.IsIsosceles) :
    A.ncard ≤ 6 := by
  classical
  by_contra! h
  let : Fintype A := (Set.finite_of_ncard_pos (s := A) (by omega)).fintype
  have hcard : Fintype.card (Fin 7) ≤ Fintype.card A := by
    rw [Fintype.card_fin, Set.fintypeCard_eq_ncard]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let p (i : Fin 7) : ℝ² := e i
  let x (i : Fin 7) := p i 0
  let y (i : Fin 7) := p i 1
  apply upper x y
  · intro i j hij
    by_contra! hxy
    apply hij
    apply e.injective
    apply Subtype.ext
    change p i = p j
    ext k
    fin_cases k <;> tauto
  · have hd (i j : Fin 7) : dist (p i) (p j) ^ 2 = coordD x y i j := by
      simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, coordD, x, y]
    intro i j k
    simp only [← hd]
    rcases triple_of_members hA (e i).property (e j).property (e k).property with h | h | h
    · exact Or.inl (congrArg (fun t : ℝ => t ^ 2) h)
    · exact Or.inr (Or.inl (congrArg (fun t : ℝ => t ^ 2) h))
    · exact Or.inr (Or.inr (congrArg (fun t : ℝ => t ^ 2) h))

/-- Every seven-point configuration contains a scalene triple. -/
theorem noSeven : NoSeven := by
  classical
  intro x y sep tri
  rcases gallai (coordD x y) (coord_symm) tri with ⟨a, b, edges⟩ | ⟨m, hm, hproper, uniform⟩
  · let pos (r : ℝ) := if 0 < r then r else 1
    have hp (r : ℝ) : 0 < pos r := by unfold pos; split <;> positivity
    apply two_impossible x y (pos a) (pos b) (hp a) (hp b)
    intro i j hij
    have hd := coord_pos sep hij
    rcases edges i j hij with e | e
    · exact Or.inl (e.trans (if_pos (e ▸ hd)).symm)
    · exact Or.inr (e.trans (if_pos (e ▸ hd)).symm)
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hm
    have line (z) (hz : z ∈ mᶜ) : coordD x y a z = coordD x y b z :=
      (coord_symm a z).trans ((uniform z (Finset.mem_compl.mp hz) a ha b hb).trans (coord_symm z b))
    have hsmall : mᶜ.card ≤ 3 := level_bound sep tri _ hab (fun i hi j hj => by
      rw [line i hi, line j hj, sub_self, sub_self])
    have hsum : mᶜ.card + m.card = 7 := m.card_compl_add_card
    have hone : mᶜ.card ≤ 1 := by
      by_contra! hn
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hn
      have bound := circles_bound sep m hpq
        (uniform p (Finset.mem_compl.mp hp)) (uniform q (Finset.mem_compl.mp hq))
      omega
    have hlt : m.card < 7 := hproper
    obtain ⟨o, ho⟩ := Finset.card_pos.mp (show 0 < mᶜ.card by omega)
    have bound := circle_bound sep tri m (Finset.mem_compl.mp ho)
      (uniform o (Finset.mem_compl.mp ho))
    omega

theorem ncard_le_six {A : Set ℝ²} (hA : A.IsIsosceles) : A.ncard ≤ 6 :=
  ncard_le_of_noSeven noSeven hA

theorem no_seven_finset (s : Finset ℝ²) (hs : s.card = 7) : ¬(s : Set ℝ²).IsIsosceles := by
  intro h
  have bound := ncard_le_six h
  rw [Set.ncard_coe_finset, hs] at bound
  omega

end OMA.E503R2

theorem OMA.solution : type_of% @Erdos503.erdos_503.variants.R2 := by
  obtain ⟨A₀, h₀, hc₀⟩ := OMA.E503R2.six_exists
  refine ⟨⟨A₀, h₀, hc₀⟩, ?_⟩
  rintro _ ⟨A, hA, rfl⟩
  exact OMA.E503R2.ncard_le_six hA
