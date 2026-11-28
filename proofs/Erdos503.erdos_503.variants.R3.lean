import FormalConjectures.ErdosProblems.«503»

/-!
# Croft's theorem on isosceles sets in three dimensions

A regular pentagon, its center, and two unit poles give eight points. For the upper
bound, color each edge by its length. A rainbow-free coloring either has two colors
or contains a proper homogeneous subset. The two direction spaces across a homogeneous
cut are orthogonal. The planar bound and the bounds on a line and a circle imply that
nine points would force eight points on a sphere. A second cut excludes that case.

For the two-color case, normalize the squared lengths to 1 and r. Each five-point
subset gives four difference vectors in three dimensions, hence a vanishing Gram
determinant. Two incompatible determinants exclude 146 six-vertex graphs. The
remaining ten graphs have no admissible one-vertex extension. The finite certificates
below give the vertex permutations, forbidden subgraphs, and polynomial identities.
-/

namespace OMA.E503R3

open scoped EuclideanGeometry

/- The eight-point configuration. -/

section

/-- The center, the cyclically ordered vertices, and the two poles, in oblique coordinates. -/
private def eightCoords (t : ℝ) : Fin 8 → ℝ × ℝ × ℝ :=
  ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (-1, t, 0), (-t, -t, 0), (t, -1, 0),
    (0, 0, 1), (0, 0, -1)]

private noncomputable def eightPoint (t u : ℝ) (p : ℝ × ℝ × ℝ) : ℝ³ :=
  WithLp.toLp 2 ![p.1 + t * p.2.1 / 2, u * p.2.1, p.2.2]

private lemma eightMetric (t u : ℝ) (hu : u ^ 2 = 1 - t ^ 2 / 4) (p q : ℝ × ℝ × ℝ) :
    dist (eightPoint t u p) (eightPoint t u q) ^ 2 =
      (p.1 - q.1)^2 + t * (p.1 - q.1) * (p.2.1 - q.2.1) +
      (p.2.1 - q.2.1)^2 + (p.2.2 - q.2.2)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three, eightPoint, Real.dist_eq, sq_abs]
  linear_combination (p.2.1 - q.2.1)^2 * hu

private def eightClass (i j : Fin 8) : Fin 6 :=
  if i = j then 0 else if i = 0 ∨ j = 0 then 1 else
    if 6 ≤ i.val ∧ 6 ≤ j.val then 5 else if 6 ≤ i.val ∨ 6 ≤ j.val then 4 else
    if i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (i.val = 1 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 1) then 2 else 3

private def eightSq (t : ℝ) (c : Fin 6) : ℝ :=
  if c.val = 0 then 0 else if c.val = 1 then 1 else if c.val = 2 then 2 - t else
    if c.val = 3 then 3 + t else if c.val = 4 then 2 else 4

private lemma eightDistances (t u : ℝ) (ht : t^2 + t = 1) (hu : u^2 = 1 - t^2 / 4)
    (i j : Fin 8) :
    dist (eightPoint t u (eightCoords t i)) (eightPoint t u (eightCoords t j)) ^ 2 =
      eightSq t (eightClass i j) := by
  have ht3 : t^3 = 2*t-1 := by linear_combination (t-1)*ht
  rw [eightMetric t u hu]
  fin_cases i <;> fin_cases j <;> norm_num [eightCoords, eightSq, eightClass, Fin.val_ofNat] <;>
    ring_nf <;> linarith only [ht, ht3]

private lemma eightTriples (i : Fin 8) : ∀ j k : Fin 8,
    eightClass i j = eightClass j k ∨ eightClass j k = eightClass k i ∨
    eightClass k i = eightClass i j := by
  fin_cases i <;> decide

/-- A regular pentagon, its center, and the unit poles give eight isosceles points. -/
theorem eight_exists : ∃ A : Set ℝ³, A.IsIsosceles ∧ A.ncard = 8 := by
  let t : ℝ := (Real.sqrt 5 - 1) / 2
  have h5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h5' := Real.sqrt_nonneg 5
  have ht : t^2 + t = 1 := by dsimp [t]; nlinarith
  have ht0 : 0 ≤ t := by dsimp [t]; nlinarith
  have ht1 : t ≤ 1 := by dsimp [t]; nlinarith
  let u := Real.sqrt (1 - t^2 / 4)
  have hu : u^2 = 1 - t^2 / 4 := Real.sq_sqrt (by linarith)
  let v (i : Fin 8) := eightPoint t u (eightCoords t i)
  have hd (i j : Fin 8) : dist (v i) (v j)^2 = eightSq t (eightClass i j) :=
    eightDistances t u ht hu i j
  have hinj : Function.Injective v := by
    intro i j hij
    by_contra h
    have hclass : ∀ a b : Fin 8, a ≠ b → eightClass a b ≠ 0 := by decide
    have hpos (c : Fin 6) (hc : c ≠ 0) : 0 < eightSq t c := by
      fin_cases c
      · exact (hc rfl).elim
      all_goals norm_num [eightSq] <;> linarith
    have hp := hpos _ (hclass i j h)
    have hval := hd i j
    rw [hij, dist_self, zero_pow (by decide)] at hval
    linarith
  refine ⟨Set.range v, ⟨⟨⟨v 0, 0, rfl⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _ _ _
    have heq (a b c d : Fin 8) (hc : eightClass a b = eightClass c d) :
        dist (v a) (v b) = dist (v c) (v d) := by
      apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
      rw [hd, hd, hc]
    rcases eightTriples i j k with h | h | h
    · exact Or.inl (heq _ _ _ _ h)
    · exact Or.inr (Or.inl (heq _ _ _ _ h))
    · exact Or.inr (Or.inr (heq _ _ _ _ h))
  · rw [Set.ncard_range_of_injective hinj]
    simp

end

/- The planar and Gallai bounds. -/

section

noncomputable def coordD {ι : Type*} (x y : ι → ℝ) (i j : ι) : ℝ :=
  (x i - x j)^2 + (y i - y j)^2

variable {ι : Type*} {x y : ι → ℝ}

def Separated (x y : ι → ℝ) : Prop :=
  ∀ i j, i ≠ j → x i ≠ x j ∨ y i ≠ y j

def TripleEq (D : ι → ι → ℝ) : Prop :=
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

theorem real_line_bound (s : Finset ℝ)
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

theorem gallaiOn (D : ι → ι → ℝ) (hs : ∀ i j, D i j = D j i)
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
theorem circle_bound (sep : Separated x y) (tri : TripleEq (coordD x y))
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

end

/- Affine dimension across a homogeneous cut. -/

section

open scoped EuclideanGeometry RealInnerProductSpace Pointwise

noncomputable def geoRank {ι : Type*} (p : ι → ℝ³) (s : Finset ι) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ (p '' (s : Set ι)))

theorem geo_rank_zero_card {ι : Type*} (p : ι → ℝ³) (hp : Function.Injective p)
    (s : Finset ι) (hr : geoRank p s = 0) : s.card ≤ 1 := by
  have hz := Submodule.finrank_eq_zero.mp hr
  have h := (vectorSpan_eq_bot_iff_subsingleton ℝ).mp hz
  exact Finset.card_le_one.mpr fun i hi j hj =>
    hp (h (Set.mem_image_of_mem p hi) (Set.mem_image_of_mem p hj))

theorem geo_orthogonal_ranks {ι : Type*} (p : ι → ℝ³) (s t : Finset ι)
    (hu : ∀ z ∈ t, ∀ i ∈ s, ∀ j ∈ s, dist (p z) (p i) = dist (p z) (p j)) :
    geoRank p s + geoRank p t ≤ 3 := by
  let S := vectorSpan ℝ (p '' (s : Set ι))
  let T := vectorSpan ℝ (p '' (t : Set ι))
  have h : T ≤ Sᗮ := by
    apply Submodule.span_le.mpr
    rintro v hv
    obtain ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩ := Set.mem_vsub.mp hv
    have hS : S ≤ (ℝ ∙ (p i -ᵥ p j))ᗮ := by
      apply Submodule.span_le.mpr
      rintro w hw
      obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Set.mem_vsub.mp hw
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      apply EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq
      · simpa only [dist_comm] using hu j hj b hb a ha
      · simpa only [dist_comm] using hu i hi b hb a ha
    apply (S.mem_orthogonal _).mpr
    intro w hw
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hS hw)
  have hdim := S.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at hdim
  change Module.finrank ℝ S + Module.finrank ℝ T ≤ 3
  have := Submodule.finrank_mono h
  omega

/-- Coordinates on the affine hull preserve all pairwise distances. The projection of a
sphere center into that hull is still equidistant from the points of the sphere. -/
private theorem geo_coordinates {ι : Type*} (W : Type*) [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (p : ι → ℝ³) (hp : Function.Injective p)
    (s : Finset ι) (hs : s.Nonempty) (hd : geoRank p s = Module.finrank ℝ W) :
    ∃ f : s → W, Function.Injective f ∧
      (∀ i j : s, dist (f i) (f j) = dist (p i) (p j)) ∧
      (∀ o : ℝ³, ∃ c : W, ∀ i j : s, dist (p i) o = dist (p j) o →
        dist (f i) c = dist (f j) c) := by
  let A := affineSpan ℝ (p '' (s : Set ι))
  let u (i : s) : A := ⟨p i, subset_affineSpan ℝ _ ⟨i, i.2, rfl⟩⟩
  obtain ⟨a, ha⟩ := hs
  let : Nonempty A := ⟨u ⟨a, ha⟩⟩
  have hdim : Module.finrank ℝ A.direction = Module.finrank ℝ W := by
    change Module.finrank ℝ (affineSpan ℝ (p '' (s : Set ι))).direction = _
    rw [direction_affineSpan]
    exact hd
  let e := (stdOrthonormalBasis ℝ A.direction).repr.trans
    ((stdOrthonormalBasis ℝ W).reindex (finCongr hdim.symm)).repr.symm
  let g := (AffineIsometryEquiv.vaddConst ℝ (u ⟨a, ha⟩)).symm.trans e.toAffineIsometryEquiv
  refine ⟨fun i => g (u i), ?_, fun i j => g.dist_map _ _, ?_⟩
  · intro i j h
    exact Subtype.ext (hp (congrArg Subtype.val (g.injective h)))
  · intro o
    let q := EuclideanGeometry.orthogonalProjection A o
    refine ⟨g q, fun i j hij => ?_⟩
    rw [g.dist_map, g.dist_map]
    exact (EuclideanGeometry.dist_eq_iff_dist_orthogonalProjection_eq o (u i).2 (u j).2).mp hij

private theorem geo_chart_iso {ι W : Type*} [Dist W] (p : ι → ℝ³)
    (ht : ∀ i j k, IsIsosceles (p i) (p j) (p k)) (s : Finset ι) (f : s → W)
    (hf : ∀ i j : s, dist (f i) (f j) = dist (p i) (p j)) (i j k : s) :
    IsIsosceles (f i) (f j) (f k) := by
  simpa only [IsIsosceles, hf] using ht i j k

theorem geo_line_bound {ι : Type*} (p : ι → ℝ³) (hp : Function.Injective p)
    (ht : ∀ i j k, IsIsosceles (p i) (p j) (p k)) (s : Finset ι)
    (hr : geoRank p s ≤ 1) : s.card ≤ 3 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  by_cases h0 : geoRank p s = 0
  · exact (geo_rank_zero_card p hp s h0).trans (by decide)
  obtain ⟨f, hi, hd, _⟩ := geo_coordinates ℝ p hp s hs (by rw [Module.finrank_self]; omega)
  let e : s ↪ ℝ := ⟨f, hi⟩
  have bound : (Finset.univ.map e).card ≤ 3 := by
    apply real_line_bound
    rintro _ hx _ hy _ hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hz
    rcases geo_chart_iso p ht s f hd i j k with h | h | h
    · left
      rw [sq_eq_sq_iff_abs_eq_abs]
      simpa [e, Real.dist_eq] using h
    · right; left
      rw [sq_eq_sq_iff_abs_eq_abs]
      simpa [e, Real.dist_eq] using h
    · right; right
      rw [sq_eq_sq_iff_abs_eq_abs]
      simpa [e, Real.dist_eq] using h
  simpa using bound

theorem geo_sphere_line {ι : Type*} (p : ι → ℝ³) (hp : Function.Injective p)
    (s : Finset ι) (hr : geoRank p s ≤ 1) (o : ℝ³) (r : ℝ)
    (hsph : ∀ i ∈ s, dist (p i) o = r) : s.card ≤ 2 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  by_cases h0 : geoRank p s = 0
  · exact (geo_rank_zero_card p hp s h0).trans (by decide)
  obtain ⟨f, hi, _, proj⟩ := geo_coordinates ℝ p hp s hs (by rw [Module.finrank_self]; omega)
  obtain ⟨c, hc⟩ := proj o
  obtain ⟨a, ha⟩ := hs
  let b : s := ⟨a, ha⟩
  let e : s ↪ ℝ := ⟨f, hi⟩
  have small : Finset.univ.map e ⊆ {f b, 2*c - f b} := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    have h := hc i b ((hsph i i.2).trans (hsph b b.2).symm)
    rw [Real.dist_eq, Real.dist_eq, abs_eq_abs] at h
    change f i ∈ ({f b, 2*c - f b} : Finset ℝ)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h with h | h
    · left; linarith
    · right; linarith
  simpa using (Finset.card_le_card small).trans Finset.card_le_two

theorem geo_planar_bound {ι : Type*} (p : ι → ℝ³) (hp : Function.Injective p)
    (ht : ∀ i j k, IsIsosceles (p i) (p j) (p k)) (s : Finset ι)
    (hr : geoRank p s ≤ 2) : s.card ≤ 6 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  by_cases h1 : geoRank p s ≤ 1
  · exact (geo_line_bound p hp ht s h1).trans (by decide)
  obtain ⟨f, hi, hd, _⟩ := geo_coordinates ℝ² p hp s hs (by rw [finrank_euclideanSpace_fin]; omega)
  have hA : (Set.range f).IsIsosceles := by
    obtain ⟨a, ha⟩ := hs
    refine ⟨⟨f ⟨a,ha⟩, Set.mem_range_self _⟩, ?_⟩
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ _ _ _
    exact geo_chart_iso p ht s f hd i j k
  simpa [Set.ncard_range_of_injective hi] using ncard_le_six hA

theorem geo_circle_bound {ι : Type*} (p : ι → ℝ³) (hp : Function.Injective p)
    (ht : ∀ i j k, IsIsosceles (p i) (p j) (p k)) (s : Finset ι)
    (hr : geoRank p s ≤ 2) (o : ℝ³) (r : ℝ)
    (hsph : ∀ i ∈ s, dist (p i) o = r) : s.card ≤ 5 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  by_cases h1 : geoRank p s ≤ 1
  · exact (geo_line_bound p hp ht s h1).trans (by decide)
  obtain ⟨f, hi, hd, proj⟩ := geo_coordinates ℝ² p hp s hs (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨c, hc⟩ := proj o
  have he (i j : s) : dist (f i) c = dist (f j) c :=
    hc i j ((hsph i i.2).trans (hsph j j.2).symm)
  by_cases hmem : c ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hmem
    have hsingle : s.card ≤ 1 := Finset.card_le_one.mpr fun i his j hjs => by
      have q (z : s) : f z = f a := dist_eq_zero.mp ((he z a).trans (dist_self _))
      exact congrArg Subtype.val (hi ((q ⟨i,his⟩).trans (q ⟨j,hjs⟩).symm))
    omega
  have hA : (insert c (Set.range f)).IsIsosceles := by
    refine ⟨⟨c, Set.mem_insert c _⟩, ?_⟩
    rintro x (rfl | ⟨i, rfl⟩) y (rfl | ⟨j, rfl⟩) z (rfl | ⟨k, rfl⟩) hxy hyz hxz
    all_goals first | contradiction | skip
    · exact Or.inr (Or.inr ((he k j).trans (dist_comm _ _)))
    · exact Or.inl ((he i k).trans (dist_comm _ _))
    · exact Or.inr (Or.inl ((he j i).trans (dist_comm _ _)))
    · exact geo_chart_iso p ht s f hd i j k
  have bound := ncard_le_six hA
  rw [Set.ncard_insert_of_notMem hmem (Set.finite_range f), Set.ncard_range_of_injective hi] at bound
  simpa using (show Nat.card s ≤ 5 by omega)

end

/- The five-point Gram condition and normalization of the two distances. -/

section

open scoped EuclideanGeometry InnerProductSpace

/-- The determinant of three rows in scalar form. -/
def twoDet3 (a b c d e f g h i : ℝ) : ℝ :=
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g

/-- Twice the Gram inner products are obtained from squared distances by polarization.
The ten arguments are the edges of five points in lexicographic order. -/
def twoGramDet (a b c d e f g h i j : ℝ) : ℝ :=
  let u := a + b - e
  let v := a + c - f
  let w := a + d - g
  let x := b + c - h
  let y := b + d - i
  let z := c + d - j
  (2*a) * twoDet3 (2*b) x y x (2*c) z y z (2*d) -
  u * twoDet3 u x y v (2*c) z w z (2*d) +
  v * twoDet3 u (2*b) y v x z w y (2*d) -
  w * twoDet3 u (2*b) x v x (2*c) w y z

private def twoGramMat (a b c d e f g h i j : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2*a, a+b-e, a+c-f, a+d-g; a+b-e, 2*b, b+c-h, b+d-i;
     a+c-f, b+c-h, 2*c, c+d-j; a+d-g, b+d-i, c+d-j, 2*d]

private lemma twoGramExpand (a b c d e f g h i j : ℝ) :
    (twoGramMat a b c d e f g h i j).det = twoGramDet a b c d e f g h i j := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  have signs (A B C D E F G H : ℝ) :
      (-1)^0*A*B + (-1)^1*C*D + (-1)^2*E*F + (-1)^3*G*H =
        A*B - C*D + E*F - G*H := by ring
  exact signs _ _ _ _ _ _ _ _

/-- The scaled Gram determinant of any five points of Euclidean three-space vanishes. -/
theorem cmFive (p : Fin 5 → ℝ³) :
    twoGramDet (dist (p 0) (p 1)^2) (dist (p 0) (p 2)^2) (dist (p 0) (p 3)^2)
      (dist (p 0) (p 4)^2) (dist (p 1) (p 2)^2) (dist (p 1) (p 3)^2)
      (dist (p 1) (p 4)^2) (dist (p 2) (p 3)^2) (dist (p 2) (p 4)^2)
      (dist (p 3) (p 4)^2) = 0 := by
  let v (i : Fin 4) : ℝ³ := p 0 - p i.succ
  let d (i j : Fin 5) := dist (p i) (p j)^2
  have hinner (i j : Fin 4) :
      (2 : ℝ) * ⟪v i, v j⟫_ℝ = d 0 i.succ + d 0 j.succ - d i.succ j.succ := by
    have h := norm_sub_sq_real (v i) (v j)
    have he : v i - v j = p j.succ - p i.succ := by dsimp [v]; abel
    rw [he] at h
    dsimp [d]
    rw [dist_comm (p i.succ) (p j.succ), dist_eq_norm, dist_eq_norm, dist_eq_norm]
    dsimp [v] at h ⊢
    linarith
  have hmat : twoGramMat (d 0 1) (d 0 2) (d 0 3) (d 0 4) (d 1 2)
      (d 1 3) (d 1 4) (d 2 3) (d 2 4) (d 3 4) = (2 : ℝ) • Matrix.gram ℝ v := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.gram_apply, hinner]
    fin_cases i <;> fin_cases j <;>
      simp [twoGramMat, d, dist_comm, Matrix.cons_val, Fin.succ] <;>
      (try simp only [dist_comm (p 1) (p 0)]) <;> ring
  have hzero : (Matrix.gram ℝ v).det = 0 := by
    by_contra hn
    have h := (Matrix.linearIndependent_of_det_gram_ne_zero hn).fintype_card_le_finrank
    norm_num [finrank_euclideanSpace_fin] at h
  change twoGramDet (d 0 1) (d 0 2) (d 0 3) (d 0 4) (d 1 2)
    (d 1 3) (d 1 4) (d 2 3) (d 2 4) (d 3 4) = 0
  rw [← twoGramExpand, hmat, Matrix.det_smul, hzero, mul_zero]



/-- A realized distance color normalized by the first squared distance. -/
def twoVal (r : ℝ) (c : Bool) : ℝ := if c then r else 1

/-- The normalized five-point obstruction extracted from an edge coloring. -/
def twoFive (r : ℝ) (c : Fin 7 → Fin 7 → Bool) (f : Fin 5 → Fin 7) : ℝ :=
  twoGramDet
    (twoVal r (c (f 0) (f 1))) (twoVal r (c (f 0) (f 2)))
    (twoVal r (c (f 0) (f 3))) (twoVal r (c (f 0) (f 4)))
    (twoVal r (c (f 1) (f 2))) (twoVal r (c (f 1) (f 3)))
    (twoVal r (c (f 1) (f 4))) (twoVal r (c (f 2) (f 3)))
    (twoVal r (c (f 2) (f 4))) (twoVal r (c (f 3) (f 4)))

/-- Rescaling a two-distance configuration gives polynomial constraints on every five vertices. -/
theorem twoModel (p : Fin 7 → ℝ³) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ i j, i ≠ j → dist (p i) (p j)^2 = a ∨ dist (p i) (p j)^2 = b) :
    ∃ (r : ℝ) (c : Fin 7 → Fin 7 → Bool), r ≠ 0 ∧ (∀ i j, c i j = c j i) ∧
      ∀ f : Fin 5 → Fin 7, Function.Injective f → twoFive r c f = 0 := by
  classical
  let c (i j : Fin 7) := decide (dist (p i) (p j)^2 ≠ a)
  let q (i : Fin 7) : ℝ³ := (Real.sqrt a)⁻¹ • p i
  have hd (i j : Fin 7) (hij : i ≠ j) :
      dist (q i) (q j)^2 = twoVal (b/a) (c i j) := by
    dsimp only [q]
    rw [dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, inv_pow, Real.sq_sqrt ha.le]
    by_cases he : dist (p i) (p j)^2 = a
    · simp [c, twoVal, he, ha.ne']
    · have hb' := (h i j hij).resolve_left he
      have hba : b ≠ a := hb' ▸ he
      simp [c, twoVal, hb', hba, div_eq_inv_mul]
  refine ⟨b/a, c, div_ne_zero hb.ne' ha.ne', fun i j ↦ ?_, ?_⟩
  · dsimp [c]
    rw [dist_comm]
  · intro f hf
    have he (i j : Fin 5) (hij : i ≠ j) := hd (f i) (f j) (hf.ne hij)
    have hc := cmFive (q ∘ f)
    simp (disch := decide) only [Function.comp_apply, he] at hc
    exact hc

end

/- Relabeling and extending a binary distance table. -/

section

def twoColor (g : List Nat) (i j : Fin 7) : Bool :=
  (g[max i.val j.val]?.getD 0).testBit (min i.val j.val)

def twoFits (c : Fin 7 → Fin 7 → Bool) (g : List Nat) (f : Fin 7 → Fin 7) : Prop :=
  ∀ i j : Fin 7, i < j → j.val < g.length → c (f i) (f j) = twoColor g i j

def twoBlocks (c : Fin 7 → Fin 7 → Bool) (g : List Nat) : Prop :=
  ∀ f, Function.Injective f → ¬twoFits c g f

/-- The base-eight digits encode the images of the seven indices. -/
def twoOrder (o : Nat) (i : Fin 7) : Fin 7 :=
  Fin.ofNat 7 (o / 8 ^ i.val % 8)

def twoChart (small big : List Nat) (o : Nat) : Prop :=
  Function.Injective (twoOrder o) ∧
  ∀ i j : Fin 7, i < j → j.val < small.length →
    max (twoOrder o i).val (twoOrder o j).val < big.length ∧
      twoColor big (twoOrder o i) (twoOrder o j) = twoColor small i j

instance (small big : List Nat) (o : Nat) : Decidable (twoChart small big o) := by
  unfold twoChart
  infer_instance

theorem twoRelabel {c : Fin 7 → Fin 7 → Bool} {small big : List Nat} {o : Nat}
    (hsym : ∀ i j, c i j = c j i) (h : twoBlocks c small) (cert : twoChart small big o) :
    twoBlocks c big := by
  intro f hf fits
  apply h (f ∘ twoOrder o) (hf.comp cert.1)
  intro i j hij hjs
  obtain ⟨hbound, hmatch⟩ := cert.2 i j hij hjs
  change c (f (twoOrder o i)) (f (twoOrder o j)) = _
  rw [← hmatch]
  rcases lt_or_gt_of_ne (cert.1.ne hij.ne) with hlt | hgt
  · exact fits _ _ hlt ((le_max_right _ _).trans_lt hbound)
  · rw [hsym]
    have e := fits _ _ hgt ((le_max_left _ _).trans_lt hbound)
    simpa only [twoColor, max_comm (twoOrder o j).val, min_comm (twoOrder o j).val] using e

theorem twoEmpty {c : Fin 7 → Fin 7 → Bool} (h : twoBlocks c []) : False := by
  apply h id Function.injective_id
  intro i j hij hj
  simp at hj

private theorem two_row_exists (n : ℕ) (w : ℕ → Bool) :
    ∃ v : Fin (2^n), ∀ i < n, v.val.testBit i = w i := by
  induction n generalizing w with
  | zero => exact ⟨0, fun i hi => by omega⟩
  | succ n ih =>
    obtain ⟨v,hv⟩ := ih (fun i => w (i+1))
    have hlt := Nat.bit_lt_bit (w 0) false v.isLt
    rw [Nat.bit_false, pow_succ, Nat.mul_comm] at *
    refine ⟨⟨Nat.bit (w 0) v.val,hlt⟩, ?_⟩
    intro i hi
    cases i with
    | zero => exact Nat.testBit_bit_zero _ _
    | succ i =>
      exact (Nat.testBit_bit_succ _ _ _).trans (hv i (by omega))

theorem twoBranch {c : Fin 7 → Fin 7 → Bool} {g : List ℕ}
    (h : ∀ v : Fin (2 ^ g.length), twoBlocks c (g ++ [v.val])) : twoBlocks c g := by
  intro f hf hg
  let lift (n : ℕ) : Fin 7 := if h : n < 7 then ⟨n,h⟩ else 0
  have hlift (i : Fin 7) : lift i.val = i := by simp [lift, i.isLt]
  obtain ⟨v,hv⟩ := two_row_exists g.length (fun i => c (f (lift i)) (f (lift g.length)))
  apply h v f hf
  intro i j hij hj
  have hle : i.val ≤ j.val := Nat.le_of_lt hij
  simp only [twoColor, max_eq_right hle, min_eq_left hle]
  by_cases hprev : j.val < g.length
  · rw [List.getElem?_append_left hprev]
    simpa only [twoColor, max_eq_right hle, min_eq_left hle] using hg i j hij hprev
  · have heq : j.val = g.length := by
      simp only [List.length_append, List.length_singleton] at hj
      omega
    rw [heq, List.getElem?_concat_length]
    simpa only [← heq, hlift, Option.getD_some] using (hv i.val (by omega)).symm

end

/- Checking a table of one-vertex extensions. -/

section

def twoCovers (small : Array (List Nat)) (g : List Nat) (rows : Array (Nat × Nat)) : Prop :=
  ∀ v : Fin (2 ^ g.length),
    let q := rows[v.val]?.getD (0, 0)
    q.1 < small.size ∧ twoChart (small[q.1]?.getD []) (g ++ [v.val]) q.2

instance (small : Array (List Nat)) (g : List Nat) (rows : Array (Nat × Nat)) :
    Decidable (twoCovers small g rows) := by
  unfold twoCovers
  infer_instance

theorem twoApplyCover {c : Fin 7 → Fin 7 → Bool} {small : Array (List Nat)}
    {g : List Nat} {rows : Array (Nat × Nat)} (hs : ∀ i j, c i j = c j i)
    (hb : ∀ h ∈ small, twoBlocks c h) (cert : twoCovers small g rows) : twoBlocks c g := by
  apply twoBranch
  intro v
  obtain ⟨hlt, hchart⟩ := cert v
  rw [Array.getElem?_eq_getElem hlt, Option.getD_some] at hchart
  exact twoRelabel hs (hb _ (Array.getElem_mem hlt)) hchart

theorem twoAllMem {c : Fin 7 → Fin 7 → Bool} {a : Array (List Nat)}
    (h : ∀ i : Fin a.size, twoBlocks c a[i]) : ∀ g ∈ a, twoBlocks c g := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hg
  exact h ⟨i, hi⟩

end

/- Reading a five-point Gram condition from a labeled subgraph. -/

section

def twoWordFive (r : ℝ) (w : Nat) : ℝ :=
  twoGramDet (twoVal r (w.testBit 0)) (twoVal r (w.testBit 1))
    (twoVal r (w.testBit 2)) (twoVal r (w.testBit 3)) (twoVal r (w.testBit 4))
    (twoVal r (w.testBit 5)) (twoVal r (w.testBit 6)) (twoVal r (w.testBit 7))
    (twoVal r (w.testBit 8)) (twoVal r (w.testBit 9))

def twoPentOrder (o : Nat) (i : Fin 5) : Fin 7 :=
  twoOrder o (i.castLE (by decide))

def twoPentCert (g : List Nat) (o w : Nat) : Prop :=
  Function.Injective (twoPentOrder o) ∧
    ∀ i j : Fin 5, i < j →
      max (twoPentOrder o i).val (twoPentOrder o j).val < g.length ∧
      twoColor g (twoPentOrder o i) (twoPentOrder o j) =
        w.testBit (i.val*(9-i.val)/2 + (j.val-i.val-1))

instance (g : List Nat) (o w : Nat) : Decidable (twoPentCert g o w) := by
  unfold twoPentCert
  infer_instance

theorem twoFlag {r : ℝ} {c : Fin 7 → Fin 7 → Bool} {g : List Nat}
    {f : Fin 7 → Fin 7} {o w : Nat}
    (hs : ∀ i j, c i j = c j i)
    (cm : ∀ u : Fin 5 → Fin 7, Function.Injective u → twoFive r c u = 0)
    (hf : Function.Injective f) (fits : twoFits c g f) (cert : twoPentCert g o w) :
    twoWordFive r w = 0 := by
  have he (i j : Fin 5) (hij : i < j) :
      c (f (twoPentOrder o i)) (f (twoPentOrder o j)) =
        w.testBit (i.val*(9-i.val)/2 + (j.val-i.val-1)) := by
    obtain ⟨hlt, hbits⟩ := cert.2 i j hij
    rw [← hbits]
    rcases lt_or_gt_of_ne (cert.1.ne hij.ne) with h | h
    · exact fits _ _ h ((le_max_right _ _).trans_lt hlt)
    · rw [hs]
      have h' := fits _ _ h ((le_max_left _ _).trans_lt hlt)
      simpa only [twoColor, max_comm (twoPentOrder o j).val, min_comm (twoPentOrder o j).val] using h'
  have h := cm (f ∘ twoPentOrder o) (hf.comp cert.1)
  simp (disch := decide) only [twoFive, Function.comp_apply, he] at h
  exact h

end

/- Polynomial certificates for the excluded six-vertex graphs. -/

section

/- Each five-vertex word gives a quartic in the ratio of squared distances.
Removing a power of the nonzero ratio gives the polynomials below. -/
private def twoClash (u v : Nat) : Prop :=
  ∀ r : ℝ, r ≠ 0 → twoWordFive r u = 0 → twoWordFive r v = 0 → False

private theorem twoPoly0 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 0 = 0) :
    (5 : ℝ) = 0 := by
  change twoGramDet 1 1 1 1 1 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly1 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 1 = 0) :
    (8 - 3*r : ℝ) = 0 := by
  change twoGramDet r 1 1 1 1 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^1 * (8 - 3*r) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly3 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 3 = 0) :
    (-4*r^2 + 12*r - 3 : ℝ) = 0 := by
  change twoGramDet r r 1 1 1 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly7 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 7 = 0) :
    (-3*r^2 + 12*r - 4 : ℝ) = 0 := by
  change twoGramDet r r r 1 1 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly15 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 15 = 0) :
    (8*r - 3 : ℝ) = 0 := by
  change twoGramDet r r r r 1 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly19 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 19 = 0) :
    (9 - 4*r : ℝ) = 0 := by
  change twoGramDet r r 1 1 r 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^2 * (9 - 4*r) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly20 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 20 = 0) :
    (r^2 - 8*r + 12 : ℝ) = 0 := by
  change twoGramDet 1 1 r 1 r 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^2 * (r^2 - 8*r + 12) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly21 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 21 = 0) :
    (r^4 - 6*r^3 + 7*r^2 + 6*r - 3 : ℝ) = 0 := by
  change twoGramDet r 1 r 1 r 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly23 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 23 = 0) :
    (r^3 - 8*r^2 + 16*r - 4 : ℝ) = 0 := by
  change twoGramDet r r r 1 r 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^1 * (r^3 - 8*r^2 + 16*r - 4) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly28 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 28 = 0) :
    (-8*r^2 + 17*r - 4 : ℝ) = 0 := by
  change twoGramDet 1 1 r r r 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^1 * (-8*r^2 + 17*r - 4) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly29 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 29 = 0) :
    (-4*r^3 + 8*r^2 + 4*r - 3 : ℝ) = 0 := by
  change twoGramDet r 1 r r r 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly31 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 31 = 0) :
    (-4*r^2 + 13*r - 4 : ℝ) = 0 := by
  change twoGramDet r r r r r 1 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^1 * (-4*r^2 + 13*r - 4) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly54 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 54 = 0) :
    (-4*r^2 + 16*r - 7 : ℝ) = 0 := by
  change twoGramDet 1 r r 1 r r 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly55 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 55 = 0) :
    (-4*r^2 + 13*r - 4 : ℝ) = 0 := by
  change twoGramDet r r r 1 r r 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^1 * (-4*r^2 + 13*r - 4) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly58 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 58 = 0) :
    (r^3 - 12*r^2 + 24*r - 8 : ℝ) = 0 := by
  change twoGramDet 1 r 1 r r r 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^1 * (r^3 - 12*r^2 + 24*r - 8) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly59 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 59 = 0) :
    (r^4 - 10*r^3 + 23*r^2 - 10*r + 1 : ℝ) = 0 := by
  change twoGramDet r r 1 r r r 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly62 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 62 = 0) :
    (-4*r^3 + 9*r^2 + 4*r - 4 : ℝ) = 0 := by
  change twoGramDet 1 r r r r r 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly63 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 63 = 0) :
    (-4*r^3 + 16*r^2 - 8*r + 1 : ℝ) = 0 := by
  change twoGramDet r r r r r r 1 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly126 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 126 = 0) :
    (12*r - 7 : ℝ) = 0 := by
  change twoGramDet 1 r r r r r r 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly127 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 127 = 0) :
    (9*r - 4 : ℝ) = 0 := by
  change twoGramDet r r r r r r r 1 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^1 * (9*r - 4) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly183 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 183 = 0) :
    (8 - 3*r : ℝ) = 0 := by
  change twoGramDet r r r 1 r r 1 r 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^3 * (8 - 3*r) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly184 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 184 = 0) :
    (12 - 7*r : ℝ) = 0 := by
  change twoGramDet 1 1 1 r r r 1 r 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^3 * (12 - 7*r) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly185 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 185 = 0) :
    (-4*r^3 + 4*r^2 + 9*r - 4 : ℝ) = 0 := by
  change twoGramDet r 1 1 r r r 1 r 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^1 * (-4*r^3 + 4*r^2 + 9*r - 4) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly187 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 187 = 0) :
    (-3*r^3 + 4*r^2 + 8*r - 4 : ℝ) = 0 := by
  change twoGramDet r r 1 r r r 1 r 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^1 * (-3*r^3 + 4*r^2 + 8*r - 4) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly191 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 191 = 0) :
    (-4*r^2 + 12*r - 3 : ℝ) = 0 := by
  change twoGramDet r r r r r r 1 r 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^2 * (-4*r^2 + 12*r - 3) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly207 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 207 = 0) :
    (-7*r^2 + 16*r - 4 : ℝ) = 0 := by
  change twoGramDet r r r r 1 1 r r 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^2 * (-7*r^2 + 16*r - 4) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly221 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 221 = 0) :
    (-8*r^3 + 24*r^2 - 12*r + 1 : ℝ) = 0 := by
  change twoGramDet r 1 r r r 1 r r 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly223 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 223 = 0) :
    (-3*r^4 + 6*r^3 + 7*r^2 - 6*r + 1 : ℝ) = 0 := by
  change twoGramDet r r r r r 1 r r 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly254 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 254 = 0) :
    (-4*r^2 + 17*r - 8 : ℝ) = 0 := by
  change twoGramDet 1 r r r r r r r 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^1 * (-4*r^2 + 17*r - 8) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly255 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 255 = 0) :
    (-3*r^2 + 12*r - 4 : ℝ) = 0 := by
  change twoGramDet r r r r r r r r 1 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^2 * (-3*r^2 + 12*r - 4) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly495 {r : ℝ} (_hr : r ≠ 0) (h : twoWordFive r 495 = 0) :
    (12*r^2 - 8*r + 1 : ℝ) = 0 := by
  change twoGramDet r r r r 1 r r r r 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  linear_combination h

private theorem twoPoly511 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 511 = 0) :
    (8*r - 3 : ℝ) = 0 := by
  change twoGramDet r r r r r r r r r 1 = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^2 * (8*r - 3) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoPoly1023 {r : ℝ} (hr : r ≠ 0) (h : twoWordFive r 1023 = 0) :
    (5 : ℝ) = 0 := by
  change twoGramDet r r r r r r r r r r = 0 at h
  unfold twoGramDet twoDet3 at h
  have hmul : r^4 * (5) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hr)

private theorem twoClash0_0 : twoClash 0 0 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly0 hr h₁
  have e₂ := twoPoly0 hr h₂
  clear e₁
  apply one_ne_zero (α := ℝ)
  linear_combination ((1/5) : ℝ) * e₂

private theorem twoClash1_3 : twoClash 1 3 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly1 hr h₁
  have e₂ := twoPoly3 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((4/5 - 12*r/5) : ℝ) * e₁ + ((9/5) : ℝ) * e₂

private theorem twoClash1_7 : twoClash 1 7 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly1 hr h₁
  have e₂ := twoPoly7 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((1/5 - 3*r/20) : ℝ) * e₁ + ((3/20) : ℝ) * e₂

private theorem twoClash1_19 : twoClash 1 19 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly1 hr h₁
  have e₂ := twoPoly19 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((4/5) : ℝ) * e₁ + ((-3/5) : ℝ) * e₂

private theorem twoClash1_20 : twoClash 1 20 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly1 hr h₁
  have e₂ := twoPoly20 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((4/5 - 3*r/20) : ℝ) * e₁ + ((-9/20) : ℝ) * e₂

private theorem twoClash3_7 : twoClash 3 7 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly3 hr h₁
  have e₂ := twoPoly7 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((123/95 - 36*r/95) : ℝ) * e₁ + ((48*r/95 - 116/95) : ℝ) * e₂

private theorem twoClash3_19 : twoClash 3 19 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly3 hr h₁
  have e₂ := twoPoly19 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((4/15) : ℝ) * e₁ + ((1/5 - 4*r/15) : ℝ) * e₂

private theorem twoClash3_28 : twoClash 3 28 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly3 hr h₁
  have e₂ := twoPoly28 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((56*r/5 - 103/5) : ℝ) * e₁ + ((76/5 - 28*r/5) : ℝ) * e₂

private theorem twoClash3_29 : twoClash 3 29 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly3 hr h₁
  have e₂ := twoPoly29 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-4*r^2/15 + 8*r/15 + 7/15) : ℝ) * e₁ + ((4*r/15 - 4/5) : ℝ) * e₂

private theorem twoClash3_54 : twoClash 3 54 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly3 hr h₁
  have e₂ := twoPoly54 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((3/5 - r/5) : ℝ) * e₁ + ((r/5 - 2/5) : ℝ) * e₂

private theorem twoClash7_59 : twoClash 7 59 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly7 hr h₁
  have e₂ := twoPoly59 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((306*r^3/145 - 2949*r^2/145 + 5964*r/145 - 871/145) : ℝ) * e₁ + ((918*r/145 - 3339/145) : ℝ) * e₂

private theorem twoClash7_126 : twoClash 7 126 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly7 hr h₁
  have e₂ := twoPoly126 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((48/95) : ℝ) * e₁ + ((12*r/95 - 41/95) : ℝ) * e₂

private theorem twoClash7_127 : twoClash 7 127 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly7 hr h₁
  have e₂ := twoPoly127 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((27/20) : ℝ) * e₁ + ((9*r/20 - 8/5) : ℝ) * e₂

private theorem twoClash15_31 : twoClash 15 31 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly15 hr h₁
  have e₂ := twoPoly31 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((8*r/5 - 23/5) : ℝ) * e₁ + ((16/5) : ℝ) * e₂

private theorem twoClash15_126 : twoClash 15 126 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly15 hr h₁
  have e₂ := twoPoly126 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((3/5) : ℝ) * e₁ + ((-2/5) : ℝ) * e₂

private theorem twoClash15_127 : twoClash 15 127 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly15 hr h₁
  have e₂ := twoPoly127 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((9/5) : ℝ) * e₁ + ((-8/5) : ℝ) * e₂

private theorem twoClash19_20 : twoClash 19 20 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly19 hr h₁
  have e₂ := twoPoly20 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((23/15 - 4*r/15) : ℝ) * e₁ + ((-16/15) : ℝ) * e₂

private theorem twoClash19_183 : twoClash 19 183 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly19 hr h₁
  have e₂ := twoPoly183 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-3/5) : ℝ) * e₁ + ((4/5) : ℝ) * e₂

private theorem twoClash20_23 : twoClash 20 23 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly20 hr h₁
  have e₂ := twoPoly23 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((r^2/20 - 7*r/20 + 1/5) : ℝ) * e₁ + ((7/20 - r/20) : ℝ) * e₂

private theorem twoClash20_28 : twoClash 20 28 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly20 hr h₁
  have e₂ := twoPoly28 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((94*r/95 - 63/380) : ℝ) * e₁ + ((47*r/380 - 71/95) : ℝ) * e₂

private theorem twoClash21_23 : twoClash 21 23 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly21 hr h₁
  have e₂ := twoPoly23 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((r^2/85 + 18*r/85 - 111/85) : ℝ) * e₁ + ((-r^3/85 - 4*r^2/17 + 4*r/5 + 62/85) : ℝ) * e₂

private theorem twoClash21_58 : twoClash 21 58 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly21 hr h₁
  have e₂ := twoPoly58 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((r^2/5 - 82*r/35 + 143/35) : ℝ) * e₁ + ((-r^3/5 + 8*r^2/7 - 36*r/35 - 58/35) : ℝ) * e₂

private theorem twoClash23_191 : twoClash 23 191 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly23 hr h₁
  have e₂ := twoPoly191 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((16*r/5 - 32/5) : ℝ) * e₁ + ((4*r^2/5 - 28*r/5 + 41/5) : ℝ) * e₂

private theorem twoClash28_54 : twoClash 28 54 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly28 hr h₁
  have e₂ := twoPoly54 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((8/17 - 12*r/85) : ℝ) * e₁ + ((24*r/85 - 7/17) : ℝ) * e₂

private theorem twoClash28_184 : twoClash 28 184 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly28 hr h₁
  have e₂ := twoPoly184 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((49/80) : ℝ) * e₁ + ((23/80 - 7*r/10) : ℝ) * e₂

private theorem twoClash28_185 : twoClash 28 185 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly28 hr h₁
  have e₂ := twoPoly185 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-23*r^2/40 - r/8 + 127/160) : ℝ) * e₁ + ((23*r/20 - 167/160) : ℝ) * e₂

private theorem twoClash29_62 : twoClash 29 62 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly29 hr h₁
  have e₂ := twoPoly62 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((9/5 - 4*r/5) : ℝ) * e₁ + ((4*r/5 - 8/5) : ℝ) * e₂

private theorem twoClash29_187 : twoClash 29 187 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly29 hr h₁
  have e₂ := twoPoly187 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((24*r^2/5 - 4*r - 71/5) : ℝ) * e₁ + ((-32*r^2/5 + 48*r/5 + 52/5) : ℝ) * e₂

private theorem twoClash29_221 : twoClash 29 221 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly29 hr h₁
  have e₂ := twoPoly221 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-16*r^2/5 + 8*r - 6/5) : ℝ) * e₁ + ((8*r^2/5 - 12*r/5 - 13/5) : ℝ) * e₂

private theorem twoClash31_191 : twoClash 31 191 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly31 hr h₁
  have e₂ := twoPoly191 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((4*r/5 - 8/5) : ℝ) * e₁ + ((9/5 - 4*r/5) : ℝ) * e₂

private theorem twoClash31_207 : twoClash 31 207 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly31 hr h₁
  have e₂ := twoPoly207 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((21*r/20 - 29/15) : ℝ) * e₁ + ((101/60 - 3*r/5) : ℝ) * e₂

private theorem twoClash31_255 : twoClash 31 255 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly31 hr h₁
  have e₂ := twoPoly255 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((24/5 - 27*r/20) : ℝ) * e₁ + ((9*r/5 - 101/20) : ℝ) * e₂

private theorem twoClash54_55 : twoClash 54 55 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly54 hr h₁
  have e₂ := twoPoly55 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((4*r/15 - 3/5) : ℝ) * e₁ + ((4/5 - 4*r/15) : ℝ) * e₂

private theorem twoClash55_183 : twoClash 55 183 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly55 hr h₁
  have e₂ := twoPoly183 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((9/20) : ℝ) * e₁ + ((7/20 - 3*r/5) : ℝ) * e₂

private theorem twoClash58_59 : twoClash 58 59 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly58 hr h₁
  have e₂ := twoPoly59 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-67*r^3/135 + 644*r^2/135 - 1288*r/135 + 146/135) : ℝ) * e₁ + ((67*r^2/135 - 778*r/135 + 1303/135) : ℝ) * e₂

private theorem twoClash58_62 : twoClash 58 62 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly58 hr h₁
  have e₂ := twoPoly62 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-17*r^2/56 + 549*r/1120 + 293/560) : ℝ) * e₁ + ((-17*r^2/224 + 69*r/80 - 363/280) : ℝ) * e₂

private theorem twoClash58_187 : twoClash 58 187 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly58 hr h₁
  have e₂ := twoPoly187 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-6*r^2/5 + r + 71/20) : ℝ) * e₁ + ((-2*r^2/5 + 23*r/5 - 147/20) : ℝ) * e₂

private theorem twoClash59_221 : twoClash 59 221 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly59 hr h₁
  have e₂ := twoPoly221 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((448*r^2/135 - 1408*r/135 + 832/135) : ℝ) * e₁ + ((56*r^3/135 - 568*r^2/135 + 1364*r/135 - 697/135) : ℝ) * e₂

private theorem twoClash62_126 : twoClash 62 126 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly62 hr h₁
  have e₂ := twoPoly126 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((108/65) : ℝ) * e₁ + ((36*r^2/65 - 12*r/13 - 71/65) : ℝ) * e₂

private theorem twoClash62_254 : twoClash 62 254 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly62 hr h₁
  have e₂ := twoPoly254 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((163/20 - 11*r/5) : ℝ) * e₁ + ((11*r^2/5 - 15*r/4 - 21/5) : ℝ) * e₂

private theorem twoClash63_223 : twoClash 63 223 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly63 hr h₁
  have e₂ := twoPoly223 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-6348*r^3/85 + 624*r^2/5 + 3656*r/17 - 6651/85) : ℝ) * e₁ + ((8464*r^2/85 - 31072*r/85 + 6736/85) : ℝ) * e₂

private theorem twoClash63_495 : twoClash 63 495 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly63 hr h₁
  have e₂ := twoPoly495 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((76/5 - 132*r/5) : ℝ) * e₁ + ((-44*r^2/5 + 172*r/5 - 71/5) : ℝ) * e₂

private theorem twoClash126_254 : twoClash 126 254 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly126 hr h₁
  have e₂ := twoPoly254 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((3*r/5 - 11/5) : ℝ) * e₁ + ((9/5) : ℝ) * e₂

private theorem twoClash126_495 : twoClash 126 495 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly126 hr h₁
  have e₂ := twoPoly495 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((1/5 - 12*r/5) : ℝ) * e₁ + ((12/5) : ℝ) * e₂

private theorem twoClash127_511 : twoClash 127 511 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly127 hr h₁
  have e₂ := twoPoly511 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-8/5) : ℝ) * e₁ + ((9/5) : ℝ) * e₂

private theorem twoClash183_184 : twoClash 183 184 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly183 hr h₁
  have e₂ := twoPoly184 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((7/20) : ℝ) * e₁ + ((-3/20) : ℝ) * e₂

private theorem twoClash183_191 : twoClash 183 191 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly183 hr h₁
  have e₂ := twoPoly191 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((4/5 - 12*r/5) : ℝ) * e₁ + ((9/5) : ℝ) * e₂

private theorem twoClash184_185 : twoClash 184 185 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly184 hr h₁
  have e₂ := twoPoly185 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-49*r^2/260 - 7*r/52 + 201/1040) : ℝ) * e₁ + ((343/1040) : ℝ) * e₂

private theorem twoClash185_187 : twoClash 185 187 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly185 hr h₁
  have e₂ := twoPoly187 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-3*r^2/4 + 2*r/5 + 14/5) : ℝ) * e₁ + ((r^2 - r/5 - 61/20) : ℝ) * e₂

private theorem twoClash185_221 : twoClash 185 221 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly185 hr h₁
  have e₂ := twoPoly221 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-12*r^2/7 + 22*r/5 - 27/35) : ℝ) * e₁ + ((6*r^2/7 - 17*r/35 - 73/35) : ℝ) * e₂

private theorem twoClash187_255 : twoClash 187 255 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly187 hr h₁
  have e₂ := twoPoly255 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((9*r/20 - 33/20) : ℝ) * e₁ + ((-9*r^2/20 + 9*r/20 + 7/5) : ℝ) * e₂

private theorem twoClash191_207 : twoClash 191 207 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly191 hr h₁
  have e₂ := twoPoly207 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((57/5 - 28*r/5) : ℝ) * e₁ + ((16*r/5 - 44/5) : ℝ) * e₂

private theorem twoClash191_255 : twoClash 191 255 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly191 hr h₁
  have e₂ := twoPoly255 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((123/95 - 36*r/95) : ℝ) * e₁ + ((48*r/95 - 116/95) : ℝ) * e₂

private theorem twoClash191_511 : twoClash 191 511 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly191 hr h₁
  have e₂ := twoPoly511 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((16/15) : ℝ) * e₁ + ((8*r/15 - 7/5) : ℝ) * e₂

private theorem twoClash207_254 : twoClash 207 254 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly207 hr h₁
  have e₂ := twoPoly254 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((31/68 - 11*r/85) : ℝ) * e₁ + ((77*r/340 - 6/17) : ℝ) * e₂

private theorem twoClash207_255 : twoClash 207 255 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly207 hr h₁
  have e₂ := twoPoly255 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((6/5 - 27*r/80) : ℝ) * e₁ + ((63*r/80 - 29/20) : ℝ) * e₂

private theorem twoClash221_223 : twoClash 221 223 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly221 hr h₁
  have e₂ := twoPoly223 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((24*r^3/35 - 24*r^2/35 - 92*r/35 - 29/35) : ℝ) * e₁ + ((-64*r^2/35 + 128*r/35 + 64/35) : ℝ) * e₂

private theorem twoClash223_254 : twoClash 223 254 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly223 hr h₁
  have e₂ := twoPoly254 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((8013/3325 - 2164*r/3325) : ℝ) * e₁ + ((1623*r^3/3325 - 2358*r^2/3325 - 53*r/35 + 586/3325) : ℝ) * e₂

private theorem twoClash254_255 : twoClash 254 255 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly254 hr h₁
  have e₂ := twoPoly255 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((9*r/20 - 3/5) : ℝ) * e₁ + ((19/20 - 3*r/5) : ℝ) * e₂

private theorem twoClash255_511 : twoClash 255 511 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly255 hr h₁
  have e₂ := twoPoly511 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((64/5) : ℝ) * e₁ + ((24*r/5 - 87/5) : ℝ) * e₂

private theorem twoClash495_511 : twoClash 495 511 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly495 hr h₁
  have e₂ := twoPoly511 hr h₂
  apply one_ne_zero (α := ℝ)
  linear_combination ((-16/5) : ℝ) * e₁ + ((24*r/5 - 7/5) : ℝ) * e₂

private theorem twoClash1023_1023 : twoClash 1023 1023 := by
  intro r hr h₁ h₂
  have e₁ := twoPoly1023 hr h₁
  have e₂ := twoPoly1023 hr h₂
  clear e₁
  apply one_ne_zero (α := ℝ)
  linear_combination ((1/5) : ℝ) * e₂

private structure TwoWorld (r : ℝ) (c : Fin 7 → Fin 7 → Bool) : Prop where
  nonzero : r ≠ 0
  symm : ∀ i j, c i j = c j i
  determinant : ∀ f : Fin 5 → Fin 7, Function.Injective f → twoFive r c f = 0

private theorem twoJoint {r c g o₁ o₂ w₁ w₂} (world : TwoWorld r c)
    (incompat : twoClash w₁ w₂) (one : twoPentCert g o₁ w₁) (two : twoPentCert g o₂ w₂) :
    twoBlocks c g := by
  intro f hf fit
  exact incompat r world.nonzero (twoFlag world.symm world.determinant hf fit one)
    (twoFlag world.symm world.determinant hf fit two)

private theorem twoExcluded0 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,0,0,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22737) world twoClash0_0 (by decide) (by decide)

private theorem twoExcluded1 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,0,0,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22737) world twoClash0_0 (by decide) (by decide)

private theorem twoExcluded3 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,0,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22737) world twoClash0_0 (by decide) (by decide)

private theorem twoExcluded7 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,1,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22737) world twoClash0_0 (by decide) (by decide)

private theorem twoExcluded15 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,1,1,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22737) world twoClash0_0 (by decide) (by decide)

private theorem twoExcluded31 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,1,1,1] :=
  twoJoint (o₁ := 22737) (o₂ := 22737) world twoClash0_0 (by decide) (by decide)

private theorem twoExcluded35 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,0,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22664) world twoClash1_19 (by decide) (by decide)

private theorem twoExcluded36 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,1,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22152) world twoClash1_20 (by decide) (by decide)

private theorem twoExcluded37 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,1,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash1_3 (by decide) (by decide)

private theorem twoExcluded39 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,1,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash1_3 (by decide) (by decide)

private theorem twoExcluded44 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,1,1,0] :=
  twoJoint (o₁ := 22737) (o₂ := 21784) world twoClash1_3 (by decide) (by decide)

private theorem twoExcluded45 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,1,1,0] :=
  twoJoint (o₁ := 21784) (o₂ := 22728) world twoClash3_7 (by decide) (by decide)

private theorem twoExcluded47 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,1,1,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash1_7 (by decide) (by decide)

private theorem twoExcluded60 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,1,1,1] :=
  twoJoint (o₁ := 22737) (o₂ := 11032) world twoClash1_7 (by decide) (by decide)

private theorem twoExcluded61 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,1,1,1] :=
  twoJoint (o₁ := 22737) (o₂ := 11032) world twoClash1_7 (by decide) (by decide)

private theorem twoExcluded63 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,1,1,1] :=
  twoJoint (o₁ := 22736) (o₂ := 22664) world twoClash15_31 (by decide) (by decide)

private theorem twoExcluded102 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,3,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22152) world twoClash3_54 (by decide) (by decide)

private theorem twoExcluded103 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,3,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash3_19 (by decide) (by decide)

private theorem twoExcluded106 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,2,1,0] :=
  twoJoint (o₁ := 22608) (o₂ := 18056) world twoClash21_58 (by decide) (by decide)

private theorem twoExcluded107 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,2,1,0] :=
  twoJoint (o₁ := 22728) (o₂ := 22664) world twoClash21_23 (by decide) (by decide)

private theorem twoExcluded110 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,3,1,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash3_7 (by decide) (by decide)

private theorem twoExcluded111 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,3,1,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash3_7 (by decide) (by decide)

private theorem twoExcluded120 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,2,1,1] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash3_28 (by decide) (by decide)

private theorem twoExcluded121 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,2,1,1] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash3_29 (by decide) (by decide)

private theorem twoExcluded122 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,2,1,1] :=
  twoJoint (o₁ := 22737) (o₂ := 15120) world twoClash3_7 (by decide) (by decide)

private theorem twoExcluded123 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,2,1,1] :=
  twoJoint (o₁ := 22737) (o₂ := 15120) world twoClash3_7 (by decide) (by decide)

private theorem twoExcluded126 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,3,1,1] :=
  twoJoint (o₁ := 22616) (o₂ := 22152) world twoClash29_62 (by decide) (by decide)

private theorem twoExcluded127 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,3,1,1] :=
  twoJoint (o₁ := 22736) (o₂ := 22728) world twoClash15_31 (by decide) (by decide)

private theorem twoExcluded238 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,3,3,0] :=
  twoJoint (o₁ := 22737) (o₂ := 18056) world twoClash7_126 (by decide) (by decide)

private theorem twoExcluded239 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,3,3,0] :=
  twoJoint (o₁ := 22737) (o₂ := 18056) world twoClash7_127 (by decide) (by decide)

private theorem twoExcluded246 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,3,2,1] :=
  twoJoint (o₁ := 22728) (o₂ := 22152) world twoClash58_62 (by decide) (by decide)

private theorem twoExcluded247 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,3,2,1] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash7_59 (by decide) (by decide)

private theorem twoExcluded254 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,3,3,1] :=
  twoJoint (o₁ := 22737) (o₂ := 18056) world twoClash7_126 (by decide) (by decide)

private theorem twoExcluded255 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,3,3,1] :=
  twoJoint (o₁ := 22737) (o₂ := 18056) world twoClash7_127 (by decide) (by decide)

private theorem twoExcluded510 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,3,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash15_126 (by decide) (by decide)

private theorem twoExcluded511 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,3,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash15_127 (by decide) (by decide)

private theorem twoExcluded615 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,0,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22152) world twoClash19_183 (by decide) (by decide)

private theorem twoExcluded616 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,6,1,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash19_20 (by decide) (by decide)

private theorem twoExcluded617 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,6,1,0] :=
  twoJoint (o₁ := 22728) (o₂ := 20689) world twoClash21_23 (by decide) (by decide)

private theorem twoExcluded619 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,6,1,0] :=
  twoJoint (o₁ := 22736) (o₂ := 22664) world twoClash21_23 (by decide) (by decide)

private theorem twoExcluded623 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,1,0] :=
  twoJoint (o₁ := 22152) (o₂ := 18056) world twoClash183_191 (by decide) (by decide)

private theorem twoExcluded632 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,6,1,1] :=
  twoJoint (o₁ := 22736) (o₂ := 22152) world twoClash28_184 (by decide) (by decide)

private theorem twoExcluded633 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,6,1,1] :=
  twoJoint (o₁ := 22736) (o₂ := 22152) world twoClash28_185 (by decide) (by decide)

private theorem twoExcluded635 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,6,1,1] :=
  twoJoint (o₁ := 22736) (o₂ := 22152) world twoClash29_187 (by decide) (by decide)

private theorem twoExcluded639 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,1,1] :=
  twoJoint (o₁ := 22736) (o₂ := 22152) world twoClash31_191 (by decide) (by decide)

private theorem twoExcluded655 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,5,3,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash20_23 (by decide) (by decide)

private theorem twoExcluded657 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,0,4,2,1] :=
  twoJoint (o₁ := 22737) (o₂ := 21200) world twoClash20_28 (by decide) (by decide)

private theorem twoExcluded659 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,4,2,1] :=
  twoJoint (o₁ := 19152) (o₂ := 17937) world twoClash21_58 (by decide) (by decide)

private theorem twoExcluded662 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,1,5,2,1] :=
  twoJoint (o₁ := 22280) (o₂ := 18049) world twoClash28_184 (by decide) (by decide)

private theorem twoExcluded663 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,5,2,1] :=
  twoJoint (o₁ := 22737) (o₂ := 19152) world twoClash20_23 (by decide) (by decide)

private theorem twoExcluded671 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,5,3,1] :=
  twoJoint (o₁ := 22736) (o₂ := 18056) world twoClash31_207 (by decide) (by decide)

private theorem twoExcluded685 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,5,3,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22280) world twoClash21_23 (by decide) (by decide)

private theorem twoExcluded687 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,5,3,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash21_23 (by decide) (by decide)

private theorem twoExcluded692 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,5,2,1] :=
  twoJoint (o₁ := 22737) (o₂ := 21200) world twoClash21_58 (by decide) (by decide)

private theorem twoExcluded693 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,5,2,1] :=
  twoJoint (o₁ := 22280) (o₂ := 22096) world twoClash29_62 (by decide) (by decide)

private theorem twoExcluded694 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,5,2,1] :=
  twoJoint (o₁ := 22737) (o₂ := 19152) world twoClash21_23 (by decide) (by decide)

private theorem twoExcluded695 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,5,2,1] :=
  twoJoint (o₁ := 22737) (o₂ := 19152) world twoClash21_23 (by decide) (by decide)

private theorem twoExcluded700 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,5,3,1] :=
  twoJoint (o₁ := 22737) (o₂ := 21768) world twoClash21_58 (by decide) (by decide)

private theorem twoExcluded701 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,5,3,1] :=
  twoJoint (o₁ := 22680) (o₂ := 22096) world twoClash29_62 (by decide) (by decide)

private theorem twoExcluded703 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,5,3,1] :=
  twoJoint (o₁ := 22664) (o₂ := 18056) world twoClash63_223 (by decide) (by decide)

private theorem twoExcluded750 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,7,3,0] :=
  twoJoint (o₁ := 22728) (o₂ := 21018) world twoClash54_55 (by decide) (by decide)

private theorem twoExcluded751 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,3,0] :=
  twoJoint (o₁ := 22728) (o₂ := 22152) world twoClash55_183 (by decide) (by decide)

private theorem twoExcluded758 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,7,2,1] :=
  twoJoint (o₁ := 22728) (o₂ := 21200) world twoClash58_187 (by decide) (by decide)

private theorem twoExcluded759 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,2,1] :=
  twoJoint (o₁ := 22737) (o₂ := 22152) world twoClash23_191 (by decide) (by decide)

private theorem twoExcluded760 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,6,3,1] :=
  twoJoint (o₁ := 22736) (o₂ := 1676) world twoClash28_185 (by decide) (by decide)

private theorem twoExcluded761 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,6,3,1] :=
  twoJoint (o₁ := 22736) (o₂ := 22152) world twoClash28_185 (by decide) (by decide)

private theorem twoExcluded762 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,6,3,1] :=
  twoJoint (o₁ := 22736) (o₂ := 22664) world twoClash29_62 (by decide) (by decide)

private theorem twoExcluded763 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,6,3,1] :=
  twoJoint (o₁ := 22664) (o₂ := 18049) world twoClash63_223 (by decide) (by decide)

private theorem twoExcluded766 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,7,3,1] :=
  twoJoint (o₁ := 22728) (o₂ := 18056) world twoClash62_254 (by decide) (by decide)

private theorem twoExcluded767 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,3,1] :=
  twoJoint (o₁ := 22152) (o₂ := 18056) world twoClash191_255 (by decide) (by decide)

private theorem twoExcluded920 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,0,4,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 15112) world twoClash28_54 (by decide) (by decide)

private theorem twoExcluded921 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,0,4,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 14914) world twoClash28_184 (by decide) (by decide)

private theorem twoExcluded922 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,1,4,3,3] :=
  twoJoint (o₁ := 22736) (o₂ := 11016) world twoClash29_62 (by decide) (by decide)

private theorem twoExcluded923 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,4,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 14914) world twoClash28_185 (by decide) (by decide)

private theorem twoExcluded926 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,1,5,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 5765) world twoClash28_185 (by decide) (by decide)

private theorem twoExcluded927 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,5,3,3] :=
  twoJoint (o₁ := 22736) (o₂ := 22152) world twoClash31_207 (by decide) (by decide)

private theorem twoExcluded954 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,4,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 12842) world twoClash29_62 (by decide) (by decide)

private theorem twoExcluded955 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,4,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 14914) world twoClash29_187 (by decide) (by decide)

private theorem twoExcluded956 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,5,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 15112) world twoClash29_62 (by decide) (by decide)

private theorem twoExcluded957 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,5,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22152) world twoClash29_221 (by decide) (by decide)

private theorem twoExcluded958 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,5,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 15112) world twoClash29_62 (by decide) (by decide)

private theorem twoExcluded959 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,5,3,3] :=
  twoJoint (o₁ := 15112) (o₂ := 22152) world twoClash63_223 (by decide) (by decide)

private theorem twoExcluded1022 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,7,3,3] :=
  twoJoint (o₁ := 22728) (o₂ := 22152) world twoClash126_254 (by decide) (by decide)

private theorem twoExcluded1023 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,3,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22152) world twoClash31_255 (by decide) (by decide)

private theorem twoExcluded1743 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,7,7,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash54_55 (by decide) (by decide)

private theorem twoExcluded1749 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,0,7,6,1] :=
  twoJoint (o₁ := 22736) (o₂ := 22728) world twoClash58_59 (by decide) (by decide)

private theorem twoExcluded1751 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,7,6,1] :=
  twoJoint (o₁ := 21600) (o₂ := 17937) world twoClash62_254 (by decide) (by decide)

private theorem twoExcluded1759 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,7,7,1] :=
  twoJoint (o₁ := 22736) (o₂ := 18056) world twoClash63_495 (by decide) (by decide)

private theorem twoExcluded1775 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,7,0] :=
  twoJoint (o₁ := 22737) (o₂ := 22664) world twoClash55_183 (by decide) (by decide)

private theorem twoExcluded1780 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,7,6,1] :=
  twoJoint (o₁ := 21592) (o₂ := 2187) world twoClash185_187 (by decide) (by decide)

private theorem twoExcluded1781 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,7,6,1] :=
  twoJoint (o₁ := 22664) (o₂ := 21704) world twoClash185_187 (by decide) (by decide)

private theorem twoExcluded1783 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,6,1] :=
  twoJoint (o₁ := 22152) (o₂ := 17937) world twoClash191_255 (by decide) (by decide)

private theorem twoExcluded1788 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,7,7,1] :=
  twoJoint (o₁ := 22736) (o₂ := 1123) world twoClash62_254 (by decide) (by decide)

private theorem twoExcluded1789 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,7,7,1] :=
  twoJoint (o₁ := 22728) (o₂ := 18049) world twoClash63_495 (by decide) (by decide)

private theorem twoExcluded1791 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,7,1] :=
  twoJoint (o₁ := 22664) (o₂ := 18056) world twoClash191_511 (by decide) (by decide)

private theorem twoExcluded1881 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,0,6,5,3] :=
  twoJoint (o₁ := 22737) (o₂ := 18248) world twoClash58_59 (by decide) (by decide)

private theorem twoExcluded1883 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,6,5,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22288) world twoClash58_59 (by decide) (by decide)

private theorem twoExcluded1884 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,0,7,5,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash58_62 (by decide) (by decide)

private theorem twoExcluded1885 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,0,7,5,3] :=
  twoJoint (o₁ := 10820) (o₂ := 10819) world twoClash185_187 (by decide) (by decide)

private theorem twoExcluded1887 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,7,5,3] :=
  twoJoint (o₁ := 22736) (o₂ := 21704) world twoClash63_223 (by decide) (by decide)

private theorem twoExcluded1916 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,7,5,3] :=
  twoJoint (o₁ := 22737) (o₂ := 10777) world twoClash59_221 (by decide) (by decide)

private theorem twoExcluded1917 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,7,5,3] :=
  twoJoint (o₁ := 19144) (o₂ := 21697) world twoClash63_223 (by decide) (by decide)

private theorem twoExcluded1919 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,5,3] :=
  twoJoint (o₁ := 22736) (o₂ := 22664) world twoClash63_223 (by decide) (by decide)

private theorem twoExcluded2012 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,0,7,7,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash62_126 (by decide) (by decide)

private theorem twoExcluded2013 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,0,7,7,3] :=
  twoJoint (o₁ := 22737) (o₂ := 8739) world twoClash62_254 (by decide) (by decide)

private theorem twoExcluded2014 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,1,7,7,3] :=
  twoJoint (o₁ := 22737) (o₂ := 5155) world twoClash62_254 (by decide) (by decide)

private theorem twoExcluded2015 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,7,7,3] :=
  twoJoint (o₁ := 22736) (o₂ := 21768) world twoClash63_223 (by decide) (by decide)

private theorem twoExcluded2046 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,7,7,3] :=
  twoJoint (o₁ := 22728) (o₂ := 22664) world twoClash126_254 (by decide) (by decide)

private theorem twoExcluded2047 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,7,3] :=
  twoJoint (o₁ := 22664) (o₂ := 18056) world twoClash255_511 (by decide) (by decide)

private theorem twoExcluded4061 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,0,7,7,7] :=
  twoJoint (o₁ := 22737) (o₂ := 8748) world twoClash126_254 (by decide) (by decide)

private theorem twoExcluded4063 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,7,7,7] :=
  twoJoint (o₁ := 22737) (o₂ := 22664) world twoClash126_495 (by decide) (by decide)

private theorem twoExcluded4095 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,7,7] :=
  twoJoint (o₁ := 22737) (o₂ := 22664) world twoClash127_511 (by decide) (by decide)

private theorem twoExcluded5871 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,15,0] :=
  twoJoint (o₁ := 18056) (o₂ := 18056) world twoClash1023_1023 (by decide) (by decide)

private theorem twoExcluded5872 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,6,14,1] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash183_184 (by decide) (by decide)

private theorem twoExcluded5873 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,6,14,1] :=
  twoJoint (o₁ := 22737) (o₂ := 2257) world twoClash183_191 (by decide) (by decide)

private theorem twoExcluded5875 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,6,14,1] :=
  twoJoint (o₁ := 22736) (o₂ := 22664) world twoClash185_187 (by decide) (by decide)

private theorem twoExcluded5879 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,14,1] :=
  twoJoint (o₁ := 22737) (o₂ := 22152) world twoClash183_191 (by decide) (by decide)

private theorem twoExcluded5887 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,15,1] :=
  twoJoint (o₁ := 18056) (o₂ := 18056) world twoClash1023_1023 (by decide) (by decide)

private theorem twoExcluded5907 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,4,12,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash184_185 (by decide) (by decide)

private theorem twoExcluded5911 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,5,12,3] :=
  twoJoint (o₁ := 19011) (o₂ := 22736) world twoClash185_187 (by decide) (by decide)

private theorem twoExcluded5919 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,5,13,3] :=
  twoJoint (o₁ := 22736) (o₂ := 22728) world twoClash191_207 (by decide) (by decide)

private theorem twoExcluded5941 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,5,12,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22152) world twoClash185_221 (by decide) (by decide)

private theorem twoExcluded5943 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,5,12,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash185_187 (by decide) (by decide)

private theorem twoExcluded5948 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,2,5,13,3] :=
  twoJoint (o₁ := 22737) (o₂ := 21784) world twoClash185_187 (by decide) (by decide)

private theorem twoExcluded5949 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,5,13,3] :=
  twoJoint (o₁ := 22737) (o₂ := 21784) world twoClash185_187 (by decide) (by decide)

private theorem twoExcluded5950 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,5,13,3] :=
  twoJoint (o₁ := 22737) (o₂ := 19024) world twoClash185_221 (by decide) (by decide)

private theorem twoExcluded5951 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,5,13,3] :=
  twoJoint (o₁ := 22736) (o₂ := 6352) world twoClash191_255 (by decide) (by decide)

private theorem twoExcluded6007 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,12,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22152) world twoClash187_255 (by decide) (by decide)

private theorem twoExcluded6010 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,6,13,3] :=
  twoJoint (o₁ := 19024) (o₂ := 4378) world twoClash221_223 (by decide) (by decide)

private theorem twoExcluded6011 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,6,13,3] :=
  twoJoint (o₁ := 22728) (o₂ := 22664) world twoClash221_223 (by decide) (by decide)

private theorem twoExcluded6014 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,7,13,3] :=
  twoJoint (o₁ := 22736) (o₂ := 6170) world twoClash191_255 (by decide) (by decide)

private theorem twoExcluded6015 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,13,3] :=
  twoJoint (o₁ := 22736) (o₂ := 22152) world twoClash191_255 (by decide) (by decide)

private theorem twoExcluded6142 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,7,15,3] :=
  twoJoint (o₁ := 22737) (o₂ := 4378) world twoClash191_511 (by decide) (by decide)

private theorem twoExcluded6143 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,15,3] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash191_255 (by decide) (by decide)

private theorem twoExcluded6654 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,3,11,7] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash207_254 (by decide) (by decide)

private theorem twoExcluded6655 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,3,11,7] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash207_255 (by decide) (by decide)

private theorem twoExcluded7101 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,2,5,11,7] :=
  twoJoint (o₁ := 22737) (o₂ := 22280) world twoClash221_223 (by decide) (by decide)

private theorem twoExcluded7103 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,5,11,7] :=
  twoJoint (o₁ := 22737) (o₂ := 22736) world twoClash221_223 (by decide) (by decide)

private theorem twoExcluded7166 {r c} (world : TwoWorld r c) : twoBlocks c [0,0,3,7,11,7] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash223_254 (by decide) (by decide)

private theorem twoExcluded7167 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,11,7] :=
  twoJoint (o₁ := 22728) (o₂ := 22152) world twoClash255_511 (by decide) (by decide)

private theorem twoExcluded8157 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,0,7,15,7] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash254_255 (by decide) (by decide)

private theorem twoExcluded8159 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,1,7,15,7] :=
  twoJoint (o₁ := 22736) (o₂ := 8984) world twoClash255_511 (by decide) (by decide)

private theorem twoExcluded8191 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,15,7] :=
  twoJoint (o₁ := 18056) (o₂ := 18056) world twoClash1023_1023 (by decide) (by decide)

private theorem twoExcluded15871 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,3,15,15] :=
  twoJoint (o₁ := 22737) (o₂ := 22728) world twoClash495_511 (by decide) (by decide)

private theorem twoExcluded16383 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,15,15] :=
  twoJoint (o₁ := 22152) (o₂ := 22152) world twoClash1023_1023 (by decide) (by decide)

private theorem twoExcluded32767 {r c} (world : TwoWorld r c) : twoBlocks c [0,1,3,7,15,31] :=
  twoJoint (o₁ := 22737) (o₂ := 22737) world twoClash1023_1023 (by decide) (by decide)

/-- Six-vertex tables excluded by a pair of five-point Gram determinants. -/
def twoBadCatalog : Array (List Nat) := #[
  [0,0,0,0,0,0],[0,1,0,0,0,0],[0,1,1,0,0,0],[0,1,1,1,0,0],[0,1,1,1,1,0],[0,1,1,1,1,1],
  [0,1,3,0,0,0],[0,0,2,1,0,0],[0,1,2,1,0,0],[0,1,3,1,0,0],[0,0,2,1,1,0],[0,1,2,1,1,0],
  [0,1,3,1,1,0],[0,0,2,1,1,1],[0,1,2,1,1,1],[0,1,3,1,1,1],[0,0,3,3,0,0],[0,1,3,3,0,0],
  [0,0,3,2,1,0],[0,1,3,2,1,0],[0,0,3,3,1,0],[0,1,3,3,1,0],[0,0,2,2,1,1],[0,1,2,2,1,1],
  [0,0,3,2,1,1],[0,1,3,2,1,1],[0,0,3,3,1,1],[0,1,3,3,1,1],[0,0,3,3,3,0],[0,1,3,3,3,0],
  [0,0,3,3,2,1],[0,1,3,3,2,1],[0,0,3,3,3,1],[0,1,3,3,3,1],[0,0,3,3,3,3],[0,1,3,3,3,3],
  [0,1,3,7,0,0],[0,0,2,6,1,0],[0,1,2,6,1,0],[0,1,3,6,1,0],[0,1,3,7,1,0],[0,0,2,6,1,1],
  [0,1,2,6,1,1],[0,1,3,6,1,1],[0,1,3,7,1,1],[0,1,1,5,3,0],[0,1,0,4,2,1],[0,1,1,4,2,1],
  [0,0,1,5,2,1],[0,1,1,5,2,1],[0,1,1,5,3,1],[0,1,2,5,3,0],[0,1,3,5,3,0],[0,0,2,5,2,1],
  [0,1,2,5,2,1],[0,0,3,5,2,1],[0,1,3,5,2,1],[0,0,2,5,3,1],[0,1,2,5,3,1],[0,1,3,5,3,1],
  [0,0,3,7,3,0],[0,1,3,7,3,0],[0,0,3,7,2,1],[0,1,3,7,2,1],[0,0,2,6,3,1],[0,1,2,6,3,1],
  [0,0,3,6,3,1],[0,1,3,6,3,1],[0,0,3,7,3,1],[0,1,3,7,3,1],[0,0,0,4,3,3],[0,1,0,4,3,3],
  [0,0,1,4,3,3],[0,1,1,4,3,3],[0,0,1,5,3,3],[0,1,1,5,3,3],[0,0,3,4,3,3],[0,1,3,4,3,3],
  [0,0,2,5,3,3],[0,1,2,5,3,3],[0,0,3,5,3,3],[0,1,3,5,3,3],[0,0,3,7,3,3],[0,1,3,7,3,3],
  [0,1,1,7,7,0],[0,1,0,7,6,1],[0,1,1,7,6,1],[0,1,1,7,7,1],[0,1,3,7,7,0],[0,0,2,7,6,1],
  [0,1,2,7,6,1],[0,1,3,7,6,1],[0,0,2,7,7,1],[0,1,2,7,7,1],[0,1,3,7,7,1],[0,1,0,6,5,3],
  [0,1,1,6,5,3],[0,0,0,7,5,3],[0,1,0,7,5,3],[0,1,1,7,5,3],[0,0,2,7,5,3],[0,1,2,7,5,3],
  [0,1,3,7,5,3],[0,0,0,7,7,3],[0,1,0,7,7,3],[0,0,1,7,7,3],[0,1,1,7,7,3],[0,0,3,7,7,3],
  [0,1,3,7,7,3],[0,1,0,7,7,7],[0,1,1,7,7,7],[0,1,3,7,7,7],[0,1,3,7,15,0],[0,0,2,6,14,1],
  [0,1,2,6,14,1],[0,1,3,6,14,1],[0,1,3,7,14,1],[0,1,3,7,15,1],[0,1,1,4,12,3],[0,1,1,5,12,3],
  [0,1,1,5,13,3],[0,1,2,5,12,3],[0,1,3,5,12,3],[0,0,2,5,13,3],[0,1,2,5,13,3],[0,0,3,5,13,3],
  [0,1,3,5,13,3],[0,1,3,7,12,3],[0,0,3,6,13,3],[0,1,3,6,13,3],[0,0,3,7,13,3],[0,1,3,7,13,3],
  [0,0,3,7,15,3],[0,1,3,7,15,3],[0,0,3,3,11,7],[0,1,3,3,11,7],[0,1,2,5,11,7],[0,1,3,5,11,7],
  [0,0,3,7,11,7],[0,1,3,7,11,7],[0,1,0,7,15,7],[0,1,1,7,15,7],[0,1,3,7,15,7],[0,1,3,3,15,15],
  [0,1,3,7,15,15],[0,1,3,7,15,31]]

private def twoAllBlocks (c : Fin 7 → Fin 7 → Bool) : List (List Nat) → Prop
  | [] => True
  | g :: gs => twoBlocks c g ∧ twoAllBlocks c gs

private theorem twoBlockAt {c gs} (h : twoAllBlocks c gs) (i : Nat) (hi : i < gs.length) :
    twoBlocks c gs[i] := by
  induction gs generalizing i with
  | nil => simp at hi
  | cons g gs ih =>
    cases i with
    | zero => exact h.1
    | succ i => exact ih h.2 i (by simpa using hi)

theorem twoCatalogBlocked {r c} (hr : r ≠ 0) (hs : ∀ i j, c i j = c j i)
    (cm : ∀ f : Fin 5 → Fin 7, Function.Injective f → twoFive r c f = 0)
    (i : Fin twoBadCatalog.size) : twoBlocks c twoBadCatalog[i] := by
  let world : TwoWorld r c := ⟨hr, hs, cm⟩
  have proof : twoAllBlocks c twoBadCatalog.toList :=
    ⟨twoExcluded0 world, twoExcluded1 world, twoExcluded3 world,
      twoExcluded7 world, twoExcluded15 world, twoExcluded31 world,
      twoExcluded35 world, twoExcluded36 world, twoExcluded37 world,
      twoExcluded39 world, twoExcluded44 world, twoExcluded45 world,
      twoExcluded47 world, twoExcluded60 world, twoExcluded61 world,
      twoExcluded63 world, twoExcluded102 world, twoExcluded103 world,
      twoExcluded106 world, twoExcluded107 world, twoExcluded110 world,
      twoExcluded111 world, twoExcluded120 world, twoExcluded121 world,
      twoExcluded122 world, twoExcluded123 world, twoExcluded126 world,
      twoExcluded127 world, twoExcluded238 world, twoExcluded239 world,
      twoExcluded246 world, twoExcluded247 world, twoExcluded254 world,
      twoExcluded255 world, twoExcluded510 world, twoExcluded511 world,
      twoExcluded615 world, twoExcluded616 world, twoExcluded617 world,
      twoExcluded619 world, twoExcluded623 world, twoExcluded632 world,
      twoExcluded633 world, twoExcluded635 world, twoExcluded639 world,
      twoExcluded655 world, twoExcluded657 world, twoExcluded659 world,
      twoExcluded662 world, twoExcluded663 world, twoExcluded671 world,
      twoExcluded685 world, twoExcluded687 world, twoExcluded692 world,
      twoExcluded693 world, twoExcluded694 world, twoExcluded695 world,
      twoExcluded700 world, twoExcluded701 world, twoExcluded703 world,
      twoExcluded750 world, twoExcluded751 world, twoExcluded758 world,
      twoExcluded759 world, twoExcluded760 world, twoExcluded761 world,
      twoExcluded762 world, twoExcluded763 world, twoExcluded766 world,
      twoExcluded767 world, twoExcluded920 world, twoExcluded921 world,
      twoExcluded922 world, twoExcluded923 world, twoExcluded926 world,
      twoExcluded927 world, twoExcluded954 world, twoExcluded955 world,
      twoExcluded956 world, twoExcluded957 world, twoExcluded958 world,
      twoExcluded959 world, twoExcluded1022 world, twoExcluded1023 world,
      twoExcluded1743 world, twoExcluded1749 world, twoExcluded1751 world,
      twoExcluded1759 world, twoExcluded1775 world, twoExcluded1780 world,
      twoExcluded1781 world, twoExcluded1783 world, twoExcluded1788 world,
      twoExcluded1789 world, twoExcluded1791 world, twoExcluded1881 world,
      twoExcluded1883 world, twoExcluded1884 world, twoExcluded1885 world,
      twoExcluded1887 world, twoExcluded1916 world, twoExcluded1917 world,
      twoExcluded1919 world, twoExcluded2012 world, twoExcluded2013 world,
      twoExcluded2014 world, twoExcluded2015 world, twoExcluded2046 world,
      twoExcluded2047 world, twoExcluded4061 world, twoExcluded4063 world,
      twoExcluded4095 world, twoExcluded5871 world, twoExcluded5872 world,
      twoExcluded5873 world, twoExcluded5875 world, twoExcluded5879 world,
      twoExcluded5887 world, twoExcluded5907 world, twoExcluded5911 world,
      twoExcluded5919 world, twoExcluded5941 world, twoExcluded5943 world,
      twoExcluded5948 world, twoExcluded5949 world, twoExcluded5950 world,
      twoExcluded5951 world, twoExcluded6007 world, twoExcluded6010 world,
      twoExcluded6011 world, twoExcluded6014 world, twoExcluded6015 world,
      twoExcluded6142 world, twoExcluded6143 world, twoExcluded6654 world,
      twoExcluded6655 world, twoExcluded7101 world, twoExcluded7103 world,
      twoExcluded7166 world, twoExcluded7167 world, twoExcluded8157 world,
      twoExcluded8159 world, twoExcluded8191 world, twoExcluded15871 world,
      twoExcluded16383 world, twoExcluded32767 world, True.intro⟩
  exact twoBlockAt proof i.val (by simp)

end

/- Each row of an extension table gives an index in the preceding catalog and
a base-eight encoding of the relabeling. twoCovers checks every possible new adjacency row. -/

section

private def twoStage6 : Array (List Nat) :=
  #[[0,0,0,4,2,1], [0,0,2,5,3,0], [0,1,3,4,2,1], [0,0,0,6,5,3], [0,1,3,6,5,3], [0,0,0,7,7,7], [0,1,0,4,12,3], [0,1,1,5,11,7], [0,0,2,5,11,7], [0,0,3,3,15,15]]

private def twoStage5 : Array (List Nat) :=
  #[[0,0,0,0,0], [0,1,0,0,0], [0,1,1,0,0], [0,1,1,1,0], [0,1,1,1,1], [0,1,3,0,0], [0,0,2,1,0], [0,1,2,1,0], [0,1,3,1,0], [0,0,2,1,1], [0,1,2,1,1], [0,1,3,1,1], [0,0,3,3,0], [0,1,3,3,0], [0,0,3,2,1], [0,1,3,2,1], [0,0,3,3,1], [0,1,3,3,1], [0,0,3,3,3], [0,1,3,3,3], [0,1,3,7,0], [0,0,2,6,1], [0,1,2,6,1], [0,1,3,6,1], [0,1,3,7,1], [0,1,1,5,3], [0,0,2,5,3], [0,1,2,5,3], [0,1,3,5,3], [0,0,3,7,3], [0,1,3,7,3], [0,1,1,7,7], [0,1,3,7,7], [0,1,3,7,15]]

private def twoStage4 : Array (List Nat) :=
  #[[0,0,0,0], [0,1,0,0], [0,1,1,0], [0,1,1,1], [0,1,3,0], [0,0,2,1], [0,1,2,1], [0,1,3,1], [0,0,3,3], [0,1,3,3], [0,1,3,7]]

private def twoStage3 : Array (List Nat) :=
  #[[0,0,0], [0,1,0], [0,1,1], [0,1,3]]

private def twoStage2 : Array (List Nat) :=
  #[[0,0], [0,1]]

private def twoStage1 : Array (List Nat) :=
  #[[0]]

private def twoCompleteSix : Array (List Nat) := twoBadCatalog ++ twoStage6

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend6_0 :
    twoCovers twoBadCatalog [0,0,0,4,2,1]
    #[(7,1509585), (10,1108688), (10,1337553), (46,1443505), (10,1337098), (46,1411186), (18,1329041), (47,1328782),
      (10,1336587), (46,1378419), (18,1328537), (47,1328334), (37,1330385), (48,1328782), (38,1328817), (49,1328782),
      (10,1336020), (46,1345204), (37,1326346), (48,1325142), (18,1323938), (47,1323798), (38,1325170), (49,1325142),
      (18,1319843), (47,1319710), (38,1321075), (49,1321054), (38,1316532), (49,1316518), (45,1328782), (50,1328782),
      (7,1509585), (37,1097026), (10,1337553), (46,1443505), (10,1337098), (46,1411186), (18,1329041), (47,1328782),
      (10,1336587), (46,1378419), (18,1328537), (47,1328334), (37,1330385), (48,1328782), (38,1328817), (49,1328782),
      (10,1336020), (46,1345204), (37,1326346), (48,1325142), (18,1323938), (47,1323798), (38,1325170), (49,1325142),
      (18,1319843), (47,1319710), (38,1321075), (49,1321054), (38,1316532), (49,1316518), (45,1328782), (50,1328782)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend6_1 :
    twoCovers twoBadCatalog [0,0,2,5,3,0]
    #[(8,1266202), (57,1525384), (57,1524929), (78,1525384), (57,1520386), (78,1521744), (95,1525265), (100,1457288),
      (57,1515787), (95,1524824), (78,1517593), (100,1453249), (95,1511706), (123,1468040), (123,1467585), (128,1455496),
      (57,1511636), (95,1520288), (95,1515745), (123,1435728), (78,1512994), (100,1416450), (123,1434370), (128,1426320),
      (78,1508451), (123,1401099), (100,1379595), (128,1393049), (100,1346772), (128,1356194), (128,1319843), (52,1216726),
      (46,1084762), (57,1525384), (57,1524929), (78,1525384), (57,1520386), (78,1521744), (95,1525265), (100,1457288),
      (57,1515787), (95,1524824), (78,1517593), (100,1453249), (95,1511706), (123,1468040), (123,1467585), (128,1455496),
      (57,1511636), (95,1520288), (95,1515745), (123,1435728), (78,1512994), (100,1416450), (123,1434370), (128,1426320),
      (78,1508451), (123,1401099), (100,1379595), (128,1393049), (100,1346772), (128,1356194), (128,1319843), (59,1216726)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend6_2 :
    twoCovers twoBadCatalog [0,1,3,4,2,1]
    #[(19,1525265), (25,1267280), (25,1525265), (56,1457169), (25,1521674), (56,1428490), (31,1457169), (63,1457169),
      (55,1466521), (85,1467585), (58,1445073), (86,1454481), (65,1445073), (90,1454481), (67,1443729), (91,1454481),
      (55,1433698), (85,1434370), (65,1412362), (90,1425802), (58,1412362), (86,1425802), (67,1411466), (91,1425802),
      (95,1329041), (100,1454222), (96,1443505), (101,1454222), (96,1411186), (101,1425494), (90,1225616), (102,1454222),
      (19,1525265), (65,1154370), (25,1525265), (56,1457169), (25,1521674), (56,1428490), (31,1457169), (63,1457169),
      (55,1466521), (85,1467585), (58,1445073), (86,1454481), (65,1445073), (90,1454481), (67,1443729), (91,1454481),
      (55,1433698), (85,1434370), (65,1412362), (90,1425802), (58,1412362), (86,1425802), (67,1411466), (91,1425802),
      (95,1329041), (100,1454222), (96,1443505), (101,1454222), (96,1411186), (101,1425494), (101,1167894), (102,1454222)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend6_3 :
    twoCovers twoBadCatalog [0,0,0,6,5,3]
    #[(18,1511587), (53,1513624), (53,1509025), (72,1266881), (47,1511706), (72,1524418), (72,1519882), (97,1457218),
      (24,1511587), (57,1369347), (64,1322076), (95,1351987), (55,1346723), (85,1362963), (89,1316252), (98,1344798),
      (24,1507996), (64,1354787), (57,1336524), (95,1319668), (55,1318044), (89,1344931), (85,1326164), (98,1316070),
      (30,1346723), (66,1352099), (66,1319836), (96,1344798), (62,1346723), (90,1344819), (90,1316084), (99,1344798),
      (18,1511587), (53,1513624), (53,1509025), (89,1115051), (47,1511706), (72,1524418), (72,1519882), (97,1457218),
      (24,1511587), (57,1369347), (64,1322076), (95,1351987), (55,1346723), (85,1362963), (89,1316252), (98,1344798),
      (24,1507996), (64,1354787), (57,1336524), (95,1319668), (55,1318044), (89,1344931), (85,1326164), (98,1316070),
      (30,1346723), (66,1352099), (66,1319836), (96,1344798), (62,1346723), (90,1344819), (90,1316084), (99,1344798)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend6_4 :
    twoCovers twoBadCatalog [0,1,3,6,5,3]
    #[(52,1525314), (67,1525328), (67,1521681), (81,1267329), (59,1525314), (81,1525314), (81,1521674), (102,1457218),
      (90,1524243), (101,1467088), (122,1467970), (129,1467984), (99,1467074), (106,1467074), (126,1467970), (131,1457218),
      (90,1519700), (122,1520288), (101,1433873), (129,1435665), (99,1433866), (126,1435658), (106,1433866), (131,1428490),
      (128,1511587), (136,1363152), (136,1411466), (138,1454642), (122,1238657), (137,1447810), (137,1425522), (139,1454642),
      (52,1525314), (67,1525328), (67,1521681), (126,1174033), (59,1525314), (81,1525314), (81,1521674), (102,1457218),
      (90,1524243), (101,1467088), (122,1467970), (129,1467984), (99,1467074), (106,1467074), (126,1467970), (131,1457218),
      (90,1519700), (122,1520288), (101,1433873), (129,1435665), (99,1433866), (126,1435658), (106,1433866), (131,1428490),
      (128,1511587), (136,1363152), (136,1411466), (138,1454642), (136,1149841), (137,1447810), (137,1425522), (139,1454642)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend6_5 :
    twoCovers twoBadCatalog [0,0,0,7,7,7]
    #[(28,1516067), (76,1383459), (76,1379427), (103,1525384), (76,1346723), (103,1525328), (103,1525265), (34,743624),
      (32,1516067), (80,1383459), (80,1379427), (105,1380771), (80,1346723), (105,1352099), (105,1319843), (109,1380659),
      (32,1516060), (80,1383452), (80,1379420), (105,1380764), (80,1346716), (105,1352092), (105,1319836), (109,1380596),
      (34,1516067), (82,1383459), (82,1379427), (107,1380771), (82,1346723), (107,1352099), (107,1319843), (110,1380638),
      (28,1516067), (76,1383459), (76,1379427), (103,1525384), (76,1346723), (103,1525328), (103,1525265), (109,1118453),
      (32,1516067), (80,1383459), (80,1379427), (105,1380771), (80,1346723), (105,1352099), (105,1319843), (109,1380659),
      (32,1516060), (80,1383452), (80,1379420), (105,1380764), (80,1346716), (105,1352092), (105,1319836), (109,1380596),
      (34,1516067), (82,1383459), (82,1379427), (107,1380771), (82,1346723), (107,1352099), (107,1319843), (110,1380638)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend6_6 :
    twoCovers twoBadCatalog [0,1,0,4,12,3]
    #[(37,1513680), (41,1513680), (41,1509585), (71,1267336), (48,1513666), (64,1370320), (64,1337553), (118,1361542),
      (48,1513603), (64,1370264), (64,1337497), (118,1361094), (71,1524250), (89,1363152), (89,1330385), (119,1361542),
      (48,1513092), (64,1369760), (64,1336993), (118,1357062), (71,1520162), (89,1359120), (89,1326353), (119,1357958),
      (71,1516067), (89,1355032), (89,1322265), (119,1353926), (113,1370320), (114,1361584), (114,1328817), (120,1361542),
      (37,1513680), (41,1513680), (41,1509585), (113,1174082), (48,1513666), (64,1370320), (64,1337553), (118,1361542),
      (48,1513603), (64,1370264), (64,1337497), (118,1361094), (71,1524250), (89,1363152), (89,1330385), (119,1361542),
      (48,1513092), (64,1369760), (64,1336993), (118,1357062), (71,1520162), (89,1359120), (89,1326353), (119,1357958),
      (71,1516067), (89,1355032), (89,1322265), (119,1353926), (113,1370320), (114,1361584), (114,1328817), (120,1361542)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend6_7 :
    twoCovers twoBadCatalog [0,1,1,5,11,7]
    #[(52,1516312), (59,1516312), (90,1517761), (99,1517768), (90,1513218), (99,1513232), (128,1525265), (106,1174096),
      (67,1516291), (81,1516312), (101,1402947), (106,1402968), (122,1369312), (126,1369312), (136,1393560), (137,1393560),
      (67,1512644), (81,1512672), (122,1401624), (126,1401624), (101,1369732), (106,1369760), (136,1357216), (137,1357216),
      (90,1250627), (102,1383704), (129,1383704), (131,1383704), (129,1354976), (131,1354976), (138,1382640), (139,1382640),
      (52,1516312), (59,1516312), (90,1517761), (99,1517768), (90,1513218), (99,1513232), (128,1525265), (131,1154384),
      (67,1516291), (81,1516312), (101,1402947), (106,1402968), (122,1369312), (126,1369312), (136,1393560), (137,1393560),
      (67,1512644), (81,1512672), (122,1401624), (126,1401624), (101,1369732), (106,1369760), (136,1357216), (137,1357216),
      (101,1107141), (102,1383704), (129,1383704), (131,1383704), (129,1354976), (131,1354976), (138,1382640), (139,1382640)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend6_8 :
    twoCovers twoBadCatalog [0,0,2,5,11,7]
    #[(51,1508451), (85,1517656), (66,1515801), (100,1517761), (66,1511650), (100,1513218), (121,1509585), (105,1174082),
      (58,1508451), (98,1517635), (80,1515787), (105,1402891), (96,1508115), (128,1368290), (124,1336419), (136,1378419),
      (58,1507996), (98,1513092), (96,1508556), (128,1401113), (80,1511636), (105,1369620), (124,1335964), (136,1345204),
      (79,1508451), (125,1401099), (101,1322083), (130,1379595), (101,1318044), (130,1346772), (129,1319843), (137,1319710),
      (51,1508451), (85,1517656), (66,1515801), (100,1517761), (66,1511650), (100,1513218), (121,1509585), (130,1154370),
      (58,1508451), (98,1517635), (80,1515787), (105,1402891), (96,1508115), (128,1368290), (124,1336419), (136,1378419),
      (58,1507996), (98,1513092), (96,1508556), (128,1401113), (80,1511636), (105,1369620), (124,1335964), (136,1345204),
      (79,1508451), (125,1401099), (101,1322083), (130,1379595), (101,1318044), (130,1346772), (129,1319843), (137,1319710)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend6_9 :
    twoCovers twoBadCatalog [0,0,3,3,15,15]
    #[(84,1520708), (93,1520736), (93,1520673), (107,1520904), (93,1511650), (129,1520400), (129,1519889), (138,1521800),
      (93,1511587), (129,1516312), (129,1515801), (138,1517768), (107,1511706), (138,1513498), (138,1509466), (110,1005634),
      (87,1520708), (106,1520708), (106,1520652), (110,1520708), (106,1511636), (137,1520260), (137,1519756), (141,1434692),
      (106,1511580), (137,1516228), (137,1515724), (141,1402436), (110,1511636), (141,1368276), (141,1336020), (143,1417780),
      (84,1520708), (93,1520736), (93,1520673), (107,1520904), (93,1511650), (129,1520400), (129,1519889), (138,1521800),
      (93,1511587), (129,1516312), (129,1515801), (138,1517768), (107,1511706), (138,1513498), (138,1509466), (143,1155637),
      (87,1520708), (106,1520708), (106,1520652), (110,1520708), (106,1511636), (137,1520260), (137,1519756), (141,1434692),
      (106,1511580), (137,1516228), (137,1515724), (141,1402436), (110,1511636), (141,1368276), (141,1336020), (143,1417780)] := by decide

private theorem twoLift6 {c : Fin 7 → Fin 7 → Bool} (hs : ∀ i j, c i j = c j i)
    (hb : ∀ g ∈ twoBadCatalog, twoBlocks c g) : ∀ g ∈ twoStage6, twoBlocks c g := by
  apply twoAllMem
  intro i
  change Fin 10 at i
  fin_cases i
  · exact twoApplyCover hs hb twoExtend6_0
  · exact twoApplyCover hs hb twoExtend6_1
  · exact twoApplyCover hs hb twoExtend6_2
  · exact twoApplyCover hs hb twoExtend6_3
  · exact twoApplyCover hs hb twoExtend6_4
  · exact twoApplyCover hs hb twoExtend6_5
  · exact twoApplyCover hs hb twoExtend6_6
  · exact twoApplyCover hs hb twoExtend6_7
  · exact twoApplyCover hs hb twoExtend6_8
  · exact twoApplyCover hs hb twoExtend6_9

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_0 :
    twoCovers twoCompleteSix [0,0,0,0,0]
    #[(0,1754760), (1,1717352), (1,1717289), (2,1717317), (1,1716778), (2,1716869), (2,1716365), (3,1717317),
      (1,1712683), (2,1712837), (2,1712333), (3,1713733), (2,1708245), (3,1709701), (3,1705613), (4,1717317),
      (1,1679916), (2,1680133), (2,1679629), (3,1681477), (2,1675541), (3,1677445), (3,1673357), (4,1688645),
      (2,1642781), (3,1644741), (3,1640653), (4,1656389), (3,1607893), (4,1623685), (4,1590925), (5,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_1 :
    twoCovers twoCompleteSix [0,1,0,0,0]
    #[(1,1754760), (2,1717576), (2,1717569), (6,1717576), (7,1717072), (8,1716904), (8,1717261), (9,1717317),
      (7,1712984), (8,1712872), (8,1713677), (9,1713733), (10,1717317), (11,1717317), (11,1717261), (12,1717317),
      (7,1680224), (8,1680168), (8,1681421), (9,1681477), (10,1688645), (11,1688645), (11,1688589), (12,1688645),
      (10,1656389), (11,1656389), (11,1656333), (12,1656389), (13,1717317), (14,1717317), (14,1717261), (15,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_2 :
    twoCovers twoCompleteSix [0,1,1,0,0]
    #[(2,1754760), (3,1718920), (8,1717576), (9,1717576), (8,1717072), (9,1717072), (16,1717352), (17,1717352),
      (10,1712984), (11,1712872), (18,1713768), (19,1713768), (18,1709736), (19,1709736), (20,1717317), (21,1717317),
      (10,1680224), (11,1680168), (18,1681512), (19,1681512), (18,1677480), (19,1677480), (20,1688645), (21,1688645),
      (22,1644776), (23,1644776), (24,1717317), (25,1717317), (24,1716869), (25,1716869), (26,1717317), (27,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_3 :
    twoCovers twoCompleteSix [0,1,1,1,0]
    #[(3,1754760), (4,1726088), (11,1717576), (12,1717576), (11,1717072), (12,1717072), (20,1717352), (21,1717352),
      (11,1712984), (12,1712984), (20,1713768), (21,1713768), (20,1709736), (21,1709736), (28,1717352), (29,1717352),
      (13,1680224), (14,1680168), (24,1681512), (25,1681512), (24,1677480), (25,1677480), (30,1688680), (31,1688680),
      (24,1644776), (25,1644776), (30,1656424), (31,1656424), (30,1623720), (31,1623720), (32,1717317), (33,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_4 :
    twoCovers twoCompleteSix [0,1,1,1,1]
    #[(4,1754760), (5,1754760), (14,1717576), (15,1717576), (14,1717072), (15,1717072), (26,1717352), (27,1717352),
      (14,1712984), (15,1712984), (26,1713768), (27,1713768), (26,1709736), (27,1709736), (32,1717352), (33,1717352),
      (14,1680224), (15,1680224), (26,1681512), (27,1681512), (26,1677480), (27,1677480), (32,1688680), (33,1688680),
      (26,1644776), (27,1644776), (32,1656424), (33,1656424), (32,1623720), (33,1623720), (34,1717352), (35,1717352)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_5 :
    twoCovers twoCompleteSix [0,1,3,0,0]
    #[(6,1754760), (9,1718920), (9,1718913), (17,1718920), (9,1718850), (17,1718864), (17,1718801), (36,1718920),
      (37,1725507), (38,1717317), (38,1717261), (39,1717317), (38,1716757), (39,1716869), (39,1716365), (40,1717317),
      (37,1692740), (38,1688645), (38,1688589), (39,1688645), (38,1688085), (39,1688197), (39,1687693), (40,1688645),
      (41,1717317), (42,1717317), (42,1717261), (43,1717317), (42,1716757), (43,1716869), (43,1716365), (44,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_6 :
    twoCovers twoCompleteSix [0,0,2,1,0]
    #[(7,1754760), (10,1726088), (10,1725633), (18,1717576), (10,1725122), (18,1717072), (37,1718920), (38,1717352),
      (10,1724555), (37,1714881), (18,1712473), (38,1713705), (18,1708378), (38,1709610), (38,1705067), (45,1717317),
      (146,1682184), (46,1688680), (46,1656361), (47,1717317), (46,1709589), (47,1716869), (48,1717317), (49,1717317),
      (46,1705053), (48,1713677), (47,1712333), (49,1713677), (47,1708245), (49,1709589), (49,1705053), (50,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_7 :
    twoCovers twoCompleteSix [0,1,2,1,0]
    #[(8,1754760), (11,1726088), (11,1725633), (19,1717576), (18,1718864), (20,1718864), (38,1718920), (39,1717576),
      (18,1714713), (38,1714881), (20,1714713), (39,1713985), (147,1716904), (51,1716904), (51,1713677), (52,1717317),
      (46,1682184), (47,1681736), (47,1653057), (148,1681736), (53,1688232), (54,1688232), (55,1717317), (56,1717317),
      (53,1713677), (55,1713677), (54,1713677), (56,1713677), (57,1717317), (58,1717317), (58,1713677), (59,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_8 :
    twoCovers twoCompleteSix [0,1,3,1,0]
    #[(9,1754760), (12,1726088), (19,1718920), (21,1718920), (19,1718864), (21,1718864), (39,1718920), (40,1718920),
      (38,1725507), (45,1714888), (51,1713992), (52,1713992), (51,1709904), (52,1716904), (60,1717352), (61,1717352),
      (48,1692768), (49,1688680), (55,1688680), (56,1688680), (55,1688232), (56,1688232), (62,1688680), (63,1688680),
      (64,1717317), (65,1717317), (66,1717317), (67,1717317), (66,1716869), (67,1716869), (68,1717317), (69,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_9 :
    twoCovers twoCompleteSix [0,0,2,1,1]
    #[(10,1754760), (13,1754760), (22,1718920), (24,1717576), (22,1718864), (24,1717072), (41,1718920), (42,1717352),
      (46,1725528), (48,1714888), (53,1713992), (55,1713992), (53,1709904), (55,1709904), (64,1717352), (65,1717352),
      (46,1692768), (48,1682184), (53,1681736), (55,1681736), (53,1677648), (55,1677648), (64,1688680), (65,1688680),
      (70,1717352), (71,1717352), (72,1717317), (73,1717317), (72,1716869), (73,1716869), (74,1717317), (75,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_10 :
    twoCovers twoCompleteSix [0,1,2,1,1]
    #[(11,1754760), (14,1754760), (23,1718920), (25,1717576), (24,1718864), (26,1718864), (42,1718920), (43,1717576),
      (47,1714888), (49,1714888), (54,1713992), (56,1713992), (57,1716904), (58,1716904), (66,1717352), (67,1717352),
      (47,1682184), (49,1682184), (54,1681736), (56,1681736), (57,1688232), (58,1688232), (66,1688680), (67,1688680),
      (72,1717352), (73,1717352), (76,1717352), (77,1717352), (78,1716904), (79,1716904), (80,1717317), (81,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_11 :
    twoCovers twoCompleteSix [0,1,3,1,1]
    #[(12,1754760), (15,1754760), (25,1718920), (27,1718920), (25,1718864), (27,1718864), (43,1718920), (44,1718920),
      (49,1725528), (50,1714888), (58,1713992), (59,1713992), (58,1709904), (59,1716904), (68,1717352), (69,1717352),
      (49,1692768), (50,1682184), (58,1681736), (59,1681736), (58,1677648), (59,1688232), (68,1688680), (69,1688680),
      (74,1717352), (75,1717352), (80,1717352), (81,1717352), (80,1716904), (81,1716904), (82,1717352), (83,1717352)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_12 :
    twoCovers twoCompleteSix [0,0,3,3,0]
    #[(16,1754760), (20,1726088), (20,1726081), (28,1726088), (20,1724954), (51,1726032), (51,1725969), (60,1718920),
      (20,1724947), (51,1725528), (51,1725465), (60,1714888), (28,1724954), (60,1710618), (60,1706586), (84,1717317),
      (70,1682184), (72,1681736), (72,1681729), (76,1681736), (72,1608026), (85,1717317), (85,1717261), (86,1717317),
      (72,1608019), (85,1713733), (85,1713677), (86,1713733), (76,1608026), (86,1708245), (86,1704661), (87,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_13 :
    twoCovers twoCompleteSix [0,1,3,3,0]
    #[(17,1754760), (21,1726088), (21,1726081), (29,1726088), (39,1726018), (52,1718920), (52,1718913), (61,1718920),
      (39,1725507), (52,1714888), (52,1714881), (61,1714888), (60,1724954), (84,1717576), (84,1717569), (88,1717576),
      (71,1682184), (73,1681736), (73,1681729), (77,1681736), (89,1717317), (90,1717317), (90,1717261), (91,1717317),
      (89,1713733), (90,1713733), (90,1713677), (91,1713733), (92,1717317), (93,1717317), (93,1717261), (94,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_14 :
    twoCovers twoCompleteSix [0,0,3,2,1]
    #[(18,1754760), (24,1754760), (24,1751169), (30,1718920), (47,1754690), (55,1718920), (55,1690241), (62,1718920),
      (53,1725528), (57,1714888), (64,1714888), (66,1713992), (72,1742874), (85,1717352), (89,1717576), (90,1717352),
      (53,1692705), (64,1682177), (57,1682177), (66,1681729), (72,1738338), (89,1688897), (85,1688617), (90,1688617),
      (149,1656648), (95,1713768), (95,1681449), (96,1717317), (97,1717317), (98,1717317), (98,1688589), (99,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_15 :
    twoCovers twoCompleteSix [0,1,3,2,1]
    #[(19,1754760), (25,1754760), (25,1751169), (31,1718920), (148,1718920), (56,1718920), (56,1690241), (63,1718920),
      (55,1725528), (58,1714888), (65,1714888), (67,1713992), (85,1717576), (86,1717576), (90,1717576), (91,1717576),
      (55,1692705), (65,1682177), (58,1682177), (67,1681729), (85,1688897), (90,1688897), (86,1688897), (91,1688897),
      (95,1656648), (96,1656648), (96,1653057), (150,1656648), (100,1717317), (101,1717317), (101,1688589), (102,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_16 :
    twoCovers twoCompleteSix [0,0,3,3,1]
    #[(20,1754760), (26,1754760), (30,1726088), (32,1726088), (54,1726032), (58,1726032), (66,1718920), (68,1718920),
      (54,1725528), (58,1725528), (66,1714888), (68,1714888), (76,1742874), (86,1710800), (92,1717576), (93,1717352),
      (72,1682184), (74,1682184), (78,1681736), (80,1681736), (97,1688904), (98,1717352), (100,1688904), (101,1717352),
      (97,1656648), (98,1713768), (100,1656648), (101,1713768), (103,1717352), (104,1717352), (105,1717317), (106,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_17 :
    twoCovers twoCompleteSix [0,1,3,3,1]
    #[(21,1754760), (27,1754760), (31,1726088), (33,1726088), (56,1726032), (59,1718920), (67,1718920), (69,1718920),
      (56,1725528), (59,1714888), (67,1714888), (69,1714888), (86,1725136), (87,1717576), (93,1717576), (94,1717576),
      (73,1682184), (75,1682184), (79,1681736), (81,1681736), (98,1688904), (99,1688904), (101,1688904), (102,1688904),
      (98,1656648), (99,1656648), (101,1656648), (102,1656648), (105,1717352), (106,1717352), (107,1717352), (108,1717352)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_18 :
    twoCovers twoCompleteSix [0,0,3,3,3]
    #[(28,1754760), (32,1754760), (32,1754753), (34,1754760), (76,1718920), (80,1718920), (80,1718913), (82,1718920),
      (76,1714888), (80,1714888), (80,1714881), (82,1714888), (103,1717576), (105,1717576), (105,1717569), (107,1717576),
      (76,1682184), (80,1682184), (80,1682177), (82,1682184), (103,1688904), (105,1688904), (105,1688897), (107,1688904),
      (103,1656648), (105,1656648), (105,1656641), (107,1656648), (151,1717576), (109,1717352), (109,1717289), (110,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_19 :
    twoCovers twoCompleteSix [0,1,3,3,3]
    #[(29,1754760), (33,1754760), (33,1754753), (35,1754760), (77,1718920), (81,1718920), (81,1718913), (83,1718920),
      (77,1714888), (81,1714888), (81,1714881), (83,1714888), (104,1717576), (106,1717576), (106,1717569), (108,1717576),
      (77,1682184), (81,1682184), (81,1682177), (83,1682184), (104,1688904), (106,1688904), (106,1688897), (108,1688904),
      (104,1656648), (106,1656648), (106,1656641), (108,1656648), (109,1717576), (110,1717576), (110,1717569), (111,1717576)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_20 :
    twoCovers twoCompleteSix [0,1,3,7,0]
    #[(36,1754760), (40,1726088), (40,1726081), (61,1726088), (40,1726018), (61,1726032), (61,1725969), (88,1726088),
      (40,1725507), (61,1725528), (61,1725465), (88,1725640), (61,1724954), (88,1725136), (88,1724625), (112,1726088),
      (113,1750084), (114,1717317), (114,1717261), (115,1717317), (114,1716757), (115,1716869), (115,1716365), (116,1717317),
      (114,1712669), (115,1712837), (115,1712333), (116,1713733), (115,1708245), (116,1709701), (116,1705613), (117,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_21 :
    twoCovers twoCompleteSix [0,0,2,6,1]
    #[(37,1754760), (41,1754760), (48,1754753), (64,1726088), (48,1754690), (64,1726032), (71,1751057), (89,1718920),
      (48,1754179), (64,1725528), (71,1746969), (89,1714888), (71,1742874), (89,1710800), (113,1726088), (114,1717352),
      (41,1738380), (152,1750112), (64,1595020), (118,1717317), (64,1594964), (118,1716869), (89,1587852), (119,1717317),
      (64,1594460), (118,1712837), (89,1583820), (119,1713733), (89,1579732), (119,1709701), (114,1586284), (120,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_22 :
    twoCovers twoCompleteSix [0,1,2,6,1]
    #[(38,1754760), (42,1754760), (49,1754753), (65,1726088), (55,1754690), (66,1726032), (73,1751057), (90,1718920),
      (55,1754179), (66,1725528), (73,1746969), (90,1714888), (89,1725136), (92,1725136), (114,1726088), (115,1717576),
      (64,1738380), (118,1750112), (74,1738401), (119,1690129), (95,1691914), (121,1716904), (98,1674001), (122,1717317),
      (95,1659147), (121,1712872), (98,1641241), (122,1713733), (123,1717317), (124,1717317), (125,1717317), (126,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_23 :
    twoCovers twoCompleteSix [0,1,3,6,1]
    #[(39,1754760), (43,1754760), (56,1754753), (67,1726088), (56,1754690), (67,1726032), (77,1751057), (91,1718920),
      (62,1725528), (68,1725528), (90,1725640), (93,1725640), (90,1725136), (93,1725136), (115,1726088), (116,1718920),
      (89,1749132), (119,1750112), (98,1691921), (122,1717352), (98,1691914), (122,1716904), (104,1691921), (127,1717352),
      (123,1712872), (124,1712872), (128,1713768), (129,1713768), (128,1709736), (129,1709736), (130,1717317), (131,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_24 :
    twoCovers twoCompleteSix [0,1,3,7,1]
    #[(40,1754760), (44,1754760), (63,1726088), (69,1726088), (63,1726032), (69,1726032), (91,1726088), (94,1726088),
      (63,1725528), (69,1725528), (91,1725640), (94,1725640), (91,1725136), (94,1725136), (116,1726088), (117,1726088),
      (114,1750084), (120,1750112), (125,1717352), (126,1717352), (125,1716904), (126,1716904), (130,1717352), (131,1717352),
      (125,1712872), (126,1712872), (130,1713768), (131,1713768), (130,1709736), (131,1709736), (132,1717352), (133,1717352)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_25 :
    twoCovers twoCompleteSix [0,1,1,5,3]
    #[(45,1754760), (50,1754760), (65,1754753), (75,1754760), (65,1751106), (75,1751120), (96,1718920), (99,1718920),
      (65,1747011), (75,1747032), (96,1714888), (99,1714888), (119,1726088), (120,1726088), (124,1717576), (126,1717576),
      (65,1742468), (75,1742496), (119,1693776), (120,1693776), (96,1678096), (99,1678096), (124,1688400), (126,1688400),
      (96,1645336), (99,1645336), (124,1655640), (126,1655640), (124,1619296), (126,1619296), (134,1717352), (135,1717352)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_26 :
    twoCovers twoCompleteSix [0,0,2,5,3]
    #[(147,1754760), (57,1754760), (57,1754305), (78,1754760), (57,1749762), (78,1751120), (95,1754641), (100,1718920),
      (57,1745163), (95,1754200), (78,1746969), (100,1714881), (95,1741082), (123,1726088), (123,1725633), (128,1717576),
      (57,1741012), (95,1749664), (95,1745121), (123,1693776), (78,1742370), (100,1678082), (123,1692418), (128,1688400),
      (78,1737827), (123,1659147), (100,1641227), (128,1655129), (100,1608404), (128,1618274), (128,1581923), (153,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_27 :
    twoCovers twoCompleteSix [0,1,2,5,3]
    #[(51,1754760), (58,1754760), (58,1754305), (79,1754760), (66,1751106), (80,1751120), (96,1726081), (101,1718920),
      (66,1746955), (96,1725640), (80,1746969), (101,1714881), (121,1726088), (124,1726088), (124,1725633), (129,1717576),
      (85,1749636), (98,1749664), (98,1745121), (125,1693776), (100,1692418), (105,1692432), (128,1690192), (130,1690192),
      (100,1659147), (128,1657369), (105,1659161), (130,1657369), (154,1688232), (136,1688232), (136,1713677), (137,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_28 :
    twoCovers twoCompleteSix [0,1,3,5,3]
    #[(52,1754760), (59,1754760), (67,1754753), (81,1754760), (67,1751106), (81,1751120), (150,1718920), (102,1718920),
      (90,1754179), (99,1725640), (101,1725633), (106,1725640), (122,1726088), (126,1726088), (129,1718920), (131,1718920),
      (90,1749636), (99,1692432), (122,1693776), (126,1693776), (101,1692418), (106,1692432), (129,1690192), (131,1690192),
      (128,1745443), (153,1713992), (136,1713992), (137,1713992), (136,1677648), (137,1688232), (138,1717352), (139,1717352)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_29 :
    twoCovers twoCompleteSix [0,0,3,7,3]
    #[(60,1754760), (68,1754760), (68,1754753), (82,1754760), (86,1754690), (101,1754704), (101,1754641), (107,1726088),
      (86,1754179), (101,1754200), (101,1754137), (107,1725640), (104,1741082), (130,1726088), (130,1726081), (132,1726088),
      (92,1741012), (124,1750112), (124,1750049), (134,1693832), (105,1741026), (136,1693776), (136,1693713), (138,1690248),
      (105,1740963), (136,1661016), (136,1660953), (138,1713992), (109,1741082), (140,1717352), (140,1717289), (141,1717317)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_30 :
    twoCovers twoCompleteSix [0,1,3,7,3]
    #[(61,1754760), (69,1754760), (69,1754753), (83,1754760), (91,1754690), (102,1726088), (102,1726081), (108,1726088),
      (91,1754179), (102,1725640), (102,1725633), (108,1725640), (127,1726088), (131,1726088), (131,1726081), (133,1726088),
      (115,1750084), (126,1750112), (126,1750049), (135,1693832), (130,1749538), (137,1690248), (137,1690241), (139,1690248),
      (130,1745443), (137,1657544), (137,1657537), (139,1713992), (140,1717576), (141,1717576), (141,1717569), (142,1717576)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_31 :
    twoCovers twoCompleteSix [0,1,1,7,7]
    #[(84,1754760), (87,1754760), (93,1754753), (106,1754760), (93,1754690), (106,1754704), (107,1754641), (110,1754760),
      (93,1745667), (106,1745688), (129,1754137), (137,1754312), (129,1753626), (137,1753808), (138,1725969), (141,1726088),
      (93,1745604), (106,1745632), (129,1750049), (137,1750280), (129,1749538), (137,1749776), (138,1693713), (141,1693832),
      (107,1745443), (110,1745688), (138,1659427), (141,1659672), (138,1627171), (141,1627416), (155,1717352), (143,1717352)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_32 :
    twoCovers twoCompleteSix [0,1,3,7,7]
    #[(88,1754760), (94,1754760), (94,1754753), (108,1754760), (94,1754690), (108,1754704), (108,1754641), (111,1754760),
      (116,1754179), (131,1754200), (131,1754137), (139,1726088), (131,1753626), (139,1726032), (139,1725969), (142,1726088),
      (116,1750084), (131,1750112), (131,1750049), (139,1693832), (131,1749538), (139,1693776), (139,1693713), (142,1693832),
      (132,1745443), (141,1745688), (141,1745177), (143,1718920), (141,1741082), (143,1718864), (143,1718801), (144,1718920)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend5_33 :
    twoCovers twoCompleteSix [0,1,3,7,15]
    #[(112,1754760), (117,1754760), (117,1754753), (133,1754760), (117,1754690), (133,1754704), (133,1754641), (142,1754760),
      (117,1754179), (133,1754200), (133,1754137), (142,1754312), (133,1753626), (142,1753808), (142,1753297), (144,1754760),
      (117,1750084), (133,1750112), (133,1750049), (142,1750280), (133,1749538), (142,1749776), (142,1749265), (144,1751176),
      (133,1745443), (142,1745688), (142,1745177), (144,1747144), (142,1741082), (144,1743056), (144,1738961), (145,1754760)] := by decide

private theorem twoLift5 {c : Fin 7 → Fin 7 → Bool} (hs : ∀ i j, c i j = c j i)
    (hb : ∀ g ∈ twoCompleteSix, twoBlocks c g) : ∀ g ∈ twoStage5, twoBlocks c g := by
  apply twoAllMem
  intro i
  change Fin 34 at i
  fin_cases i
  · exact twoApplyCover hs hb twoExtend5_0
  · exact twoApplyCover hs hb twoExtend5_1
  · exact twoApplyCover hs hb twoExtend5_2
  · exact twoApplyCover hs hb twoExtend5_3
  · exact twoApplyCover hs hb twoExtend5_4
  · exact twoApplyCover hs hb twoExtend5_5
  · exact twoApplyCover hs hb twoExtend5_6
  · exact twoApplyCover hs hb twoExtend5_7
  · exact twoApplyCover hs hb twoExtend5_8
  · exact twoApplyCover hs hb twoExtend5_9
  · exact twoApplyCover hs hb twoExtend5_10
  · exact twoApplyCover hs hb twoExtend5_11
  · exact twoApplyCover hs hb twoExtend5_12
  · exact twoApplyCover hs hb twoExtend5_13
  · exact twoApplyCover hs hb twoExtend5_14
  · exact twoApplyCover hs hb twoExtend5_15
  · exact twoApplyCover hs hb twoExtend5_16
  · exact twoApplyCover hs hb twoExtend5_17
  · exact twoApplyCover hs hb twoExtend5_18
  · exact twoApplyCover hs hb twoExtend5_19
  · exact twoApplyCover hs hb twoExtend5_20
  · exact twoApplyCover hs hb twoExtend5_21
  · exact twoApplyCover hs hb twoExtend5_22
  · exact twoApplyCover hs hb twoExtend5_23
  · exact twoApplyCover hs hb twoExtend5_24
  · exact twoApplyCover hs hb twoExtend5_25
  · exact twoApplyCover hs hb twoExtend5_26
  · exact twoApplyCover hs hb twoExtend5_27
  · exact twoApplyCover hs hb twoExtend5_28
  · exact twoApplyCover hs hb twoExtend5_29
  · exact twoApplyCover hs hb twoExtend5_30
  · exact twoApplyCover hs hb twoExtend5_31
  · exact twoApplyCover hs hb twoExtend5_32
  · exact twoApplyCover hs hb twoExtend5_33

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_0 :
    twoCovers twoStage5 [0,0,0,0]
    #[(0,1754760), (1,1750112), (1,1750049), (2,1750084), (1,1749538), (2,1749636), (2,1749132), (3,1750084),
      (1,1745443), (2,1745604), (2,1745100), (3,1746500), (2,1741012), (3,1742468), (3,1738380), (4,1750084)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_1 :
    twoCovers twoStage5 [0,1,0,0]
    #[(1,1754760), (2,1750280), (2,1750273), (5,1750280), (6,1749776), (7,1749664), (7,1750028), (8,1750084),
      (6,1745688), (7,1745632), (7,1746444), (8,1746500), (9,1750084), (10,1750084), (10,1750028), (11,1750084)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_2 :
    twoCovers twoStage5 [0,1,1,0]
    #[(2,1754760), (3,1751176), (7,1750280), (8,1750280), (7,1749776), (8,1749776), (12,1750112), (13,1750112),
      (9,1745688), (10,1745632), (14,1746528), (15,1746528), (14,1742496), (15,1742496), (16,1750084), (17,1750084)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_3 :
    twoCovers twoStage5 [0,1,1,1]
    #[(3,1754760), (4,1754760), (10,1750280), (11,1750280), (10,1749776), (11,1749776), (16,1750112), (17,1750112),
      (10,1745688), (11,1745688), (16,1746528), (17,1746528), (16,1742496), (17,1742496), (18,1750112), (19,1750112)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_4 :
    twoCovers twoStage5 [0,1,3,0]
    #[(5,1754760), (8,1751176), (8,1751169), (13,1751176), (8,1751106), (13,1751120), (13,1751057), (20,1751176),
      (21,1754179), (22,1750084), (22,1750028), (23,1750084), (22,1749524), (23,1749636), (23,1749132), (24,1750084)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_5 :
    twoCovers twoStage5 [0,0,2,1]
    #[(6,1754760), (9,1754760), (9,1754305), (14,1750280), (9,1753794), (14,1749776), (21,1751176), (22,1750112),
      (9,1753227), (21,1747137), (14,1745177), (22,1746465), (14,1741082), (22,1742370), (22,1737827), (25,1750084)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_6 :
    twoCovers twoStage5 [0,1,2,1]
    #[(7,1754760), (10,1754760), (10,1754305), (15,1750280), (14,1751120), (16,1751120), (22,1751176), (23,1750280),
      (14,1746969), (22,1747137), (16,1746969), (23,1746689), (26,1749664), (27,1749664), (27,1746444), (28,1750084)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_7 :
    twoCovers twoStage5 [0,1,3,1]
    #[(8,1754760), (11,1754760), (15,1751176), (17,1751176), (15,1751120), (17,1751120), (23,1751176), (24,1751176),
      (22,1754179), (25,1747144), (27,1746696), (28,1746696), (27,1742608), (28,1749664), (29,1750112), (30,1750112)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_8 :
    twoCovers twoStage5 [0,0,3,3]
    #[(12,1754760), (16,1754760), (16,1754753), (18,1754760), (16,1753626), (27,1754704), (27,1754641), (29,1751176),
      (16,1753619), (27,1754200), (27,1754137), (29,1747144), (18,1753626), (29,1742874), (29,1738842), (31,1750084)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_9 :
    twoCovers twoStage5 [0,1,3,3]
    #[(13,1754760), (17,1754760), (17,1754753), (19,1754760), (23,1754690), (28,1751176), (28,1751169), (30,1751176),
      (23,1754179), (28,1747144), (28,1747137), (30,1747144), (29,1753626), (31,1750280), (31,1750273), (32,1750280)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend4_10 :
    twoCovers twoStage5 [0,1,3,7]
    #[(20,1754760), (24,1754760), (24,1754753), (30,1754760), (24,1754690), (30,1754704), (30,1754641), (32,1754760),
      (24,1754179), (30,1754200), (30,1754137), (32,1754312), (30,1753626), (32,1753808), (32,1753297), (33,1754760)] := by decide

private theorem twoLift4 {c : Fin 7 → Fin 7 → Bool} (hs : ∀ i j, c i j = c j i)
    (hb : ∀ g ∈ twoStage5, twoBlocks c g) : ∀ g ∈ twoStage4, twoBlocks c g := by
  apply twoAllMem
  intro i
  change Fin 11 at i
  fin_cases i
  · exact twoApplyCover hs hb twoExtend4_0
  · exact twoApplyCover hs hb twoExtend4_1
  · exact twoApplyCover hs hb twoExtend4_2
  · exact twoApplyCover hs hb twoExtend4_3
  · exact twoApplyCover hs hb twoExtend4_4
  · exact twoApplyCover hs hb twoExtend4_5
  · exact twoApplyCover hs hb twoExtend4_6
  · exact twoApplyCover hs hb twoExtend4_7
  · exact twoApplyCover hs hb twoExtend4_8
  · exact twoApplyCover hs hb twoExtend4_9
  · exact twoApplyCover hs hb twoExtend4_10

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend3_0 :
    twoCovers twoStage4 [0,0,0]
    #[(0,1754760), (1,1754200), (1,1754137), (2,1754179), (1,1753626), (2,1753731), (2,1753227), (3,1754179)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend3_1 :
    twoCovers twoStage4 [0,1,0]
    #[(1,1754760), (2,1754312), (2,1754305), (4,1754312), (5,1753808), (6,1753752), (6,1754123), (7,1754179)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend3_2 :
    twoCovers twoStage4 [0,1,1]
    #[(2,1754760), (3,1754760), (6,1754312), (7,1754312), (6,1753808), (7,1753808), (8,1754200), (9,1754200)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend3_3 :
    twoCovers twoStage4 [0,1,3]
    #[(4,1754760), (7,1754760), (7,1754753), (9,1754760), (7,1754690), (9,1754704), (9,1754641), (10,1754760)] := by decide

private theorem twoLift3 {c : Fin 7 → Fin 7 → Bool} (hs : ∀ i j, c i j = c j i)
    (hb : ∀ g ∈ twoStage4, twoBlocks c g) : ∀ g ∈ twoStage3, twoBlocks c g := by
  apply twoAllMem
  intro i
  change Fin 4 at i
  fin_cases i
  · exact twoApplyCover hs hb twoExtend3_0
  · exact twoApplyCover hs hb twoExtend3_1
  · exact twoApplyCover hs hb twoExtend3_2
  · exact twoApplyCover hs hb twoExtend3_3

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend2_0 :
    twoCovers twoStage3 [0,0]
    #[(0,1754760), (1,1754704), (1,1754641), (2,1754690)] := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend2_1 :
    twoCovers twoStage3 [0,1]
    #[(1,1754760), (2,1754760), (2,1754753), (3,1754760)] := by decide

private theorem twoLift2 {c : Fin 7 → Fin 7 → Bool} (hs : ∀ i j, c i j = c j i)
    (hb : ∀ g ∈ twoStage3, twoBlocks c g) : ∀ g ∈ twoStage2, twoBlocks c g := by
  apply twoAllMem
  intro i
  change Fin 2 at i
  fin_cases i
  · exact twoApplyCover hs hb twoExtend2_0
  · exact twoApplyCover hs hb twoExtend2_1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem twoExtend1_0 :
    twoCovers twoStage2 [0]
    #[(0,1754760), (1,1754760)] := by decide

private theorem twoLift1 {c : Fin 7 → Fin 7 → Bool} (hs : ∀ i j, c i j = c j i)
    (hb : ∀ g ∈ twoStage2, twoBlocks c g) : ∀ g ∈ twoStage1, twoBlocks c g := by
  apply twoAllMem
  intro i
  change Fin 1 at i
  fin_cases i
  · exact twoApplyCover hs hb twoExtend1_0

theorem twoFromCatalog {c : Fin 7 → Fin 7 → Bool} (hs : ∀ i j, c i j = c j i)
    (hb : ∀ i : Fin twoBadCatalog.size, twoBlocks c twoBadCatalog[i]) : False := by
  have bad := twoAllMem hb
  have more := twoLift6 hs bad
  have allSix : ∀ g ∈ twoCompleteSix, twoBlocks c g := by
    intro g hg
    rcases Array.mem_append.mp hg with h | h
    · exact bad g h
    · exact more g h
  have single := twoLift1 hs (twoLift2 hs (twoLift3 hs (twoLift4 hs (twoLift5 hs allSix))))
  have one := single [0] (by simp [twoStage1])
  apply one id Function.injective_id
  intro i j hij hj
  have h : j.val < 1 := hj
  omega

end

/-- Every realization of a two-distance table on seven vertices would satisfy
all of its five-point Gram equations. The six-vertex exclusions rule this out. -/
theorem twoDist_seven (p : Fin 7 → ℝ³) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ i j, i ≠ j → dist (p i) (p j)^2 = a ∨ dist (p i) (p j)^2 = b) : False := by
  obtain ⟨r, c, hr, hsym, hGram⟩ := twoModel p a b ha hb h
  exact twoFromCatalog hsym (twoCatalogBlocked hr hsym hGram)

private theorem two_color_small {ι : Type*}
    (p : ι → ℝ³) (hp : Function.Injective p) (s : Finset ι)
    (a b : ℝ) (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → dist (p i) (p j) = a ∨ dist (p i) (p j) = b) :
    s.card ≤ 6 := by
  classical
  by_contra! hn
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 7) ≤ Fintype.card s by simp; omega)
  let d (r : ℝ) := if 0 < r then r ^ 2 else 1
  have pos (r : ℝ) : 0 < d r := by unfold d; split <;> positivity
  apply twoDist_seven (fun i => p (e i)) (d a) (d b) (pos _) (pos _)
  intro i j hij
  have hne : (e i).val ≠ (e j).val := fun he => hij (e.injective (Subtype.ext he))
  have hpos := dist_pos.mpr (hp.ne hne)
  rcases h _ (e i).property _ (e j).property hne with he | he
  · exact Or.inl (by simp only [d, if_pos (he ▸ hpos), he])
  · exact Or.inr (by simp only [d, if_pos (he ▸ hpos), he])

/-- Within a sphere, a nontrivial homogeneous subset is on a circle, since
both the original center and an exterior point are equidistant from it. -/
private theorem sphere_card_le_seven {ι : Type*}
    (p : ι → ℝ³) (hp : Function.Injective p)
    (ht : ∀ i j k, IsIsosceles (p i) (p j) (p k))
    (s : Finset ι) (o : ι) (ho : o ∉ s) (r : ℝ) (hs : ∀ i ∈ s, dist (p i) (p o) = r) :
    s.card ≤ 7 := by
  classical
  rcases gallaiOn (fun i j => dist (p i) (p j)) (fun _ _ => dist_comm _ _) ht s with
    ⟨a, b, h⟩ | ⟨m, sub, hm, hlt, hu⟩
  · exact (two_color_small p hp s a b h).trans (by decide)
  let t := s \ m
  have hc : t.card = s.card - m.card := Finset.card_sdiff_of_subset sub
  have hun (z) (hz : z ∈ t) := hu z (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < t.card by omega)
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hm
  have hqo : o ≠ q := fun e => ho (e ▸ (Finset.mem_sdiff.mp hq).1)
  have rankPair : 1 ≤ geoRank p {o, q} := by
    by_contra! h
    have := geo_rank_zero_card p hp {o,q} (by omega)
    simp [hqo] at this
  have pairSum := geo_orthogonal_ranks p m {o,q} (by
    intro z hz a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz <;> subst z
    · rw [dist_comm (p o), hs a (sub ha), dist_comm (p o), hs b (sub hb)]
    · exact hun q hq a ha b hb)
  have rankM : 1 ≤ geoRank p m := by
    by_contra! h
    have := geo_rank_zero_card p hp m (by omega)
    omega
  have rankSum := geo_orthogonal_ranks p m t hun
  have sphereM := fun i (hi : i ∈ m) => hs i (sub hi)
  have sphereT := fun i (hi : i ∈ t) => hs i (Finset.mem_sdiff.mp hi).1
  by_cases hline : geoRank p m ≤ 1
  · have hm2 := geo_sphere_line p hp m hline (p o) r sphereM
    have ht5 := geo_circle_bound p hp ht t (by omega) (p o) r sphereT
    omega
  · have hm5 := geo_circle_bound p hp ht m (by omega) (p o) r sphereM
    have ht2 := geo_sphere_line p hp t (by omega) (p o) r sphereT
    omega

/-- Every injective configuration of nine points contains a scalene triangle. -/
theorem noNine (p : Fin 9 → ℝ³)
    (hp : Function.Injective p) (ht : ∀ i j k, IsIsosceles (p i) (p j) (p k)) : False := by
  classical
  rcases gallai (fun i j => dist (p i) (p j)) (fun _ _ => dist_comm _ _) ht with
    ⟨a, b, h⟩ | ⟨m, hm, hlt, hu⟩
  · have hsmall := two_color_small p hp Finset.univ a b (fun i _ j _ => h i j)
    simp at hsmall
  let t := mᶜ
  have hc : t.card + m.card = 9 := m.card_compl_add_card
  have hm9 : m.card < 9 := hlt
  have hun (z) (hz : z ∈ t) := hu z (Finset.mem_compl.mp hz)
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < t.card by omega)
  obtain ⟨i, hi, _, _, _⟩ := Finset.one_lt_card.mp hm
  let r := dist (p q) (p i)
  have sphereM (k) (hk : k ∈ m) : dist (p k) (p q) = r :=
    (dist_comm _ _).trans (hun q hq k hk i hi)
  have rankM : 1 ≤ geoRank p m := by
    by_contra! h
    have := geo_rank_zero_card p hp m (by omega)
    omega
  have ranks := geo_orthogonal_ranks p m t hun
  by_cases hline : geoRank p m ≤ 1
  · have hm2 := geo_sphere_line p hp m hline (p q) r sphereM
    have ht6 := geo_planar_bound p hp ht t (by omega)
    omega
  by_cases hplane : geoRank p m ≤ 2
  · have hm5 := geo_circle_bound p hp ht m hplane (p q) r sphereM
    have ht3 := geo_line_bound p hp ht t (by omega)
    omega
  have ht1 := geo_rank_zero_card p hp t (by omega)
  have hm7 := sphere_card_le_seven p hp ht m q (Finset.mem_compl.mp hq) r sphereM
  omega

theorem ncard_le_eight {s : Set ℝ³} (hs : s.IsIsosceles) : s.ncard ≤ 8 := by
  classical
  by_contra! hn
  let : Fintype s := (Set.finite_of_ncard_pos (s := s) (by omega)).fintype
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 9) ≤ Fintype.card s by
      rw [Fintype.card_fin, Set.fintypeCard_eq_ncard]
      omega)
  let p (i : Fin 9) : ℝ³ := e i
  apply noNine p (Subtype.val_injective.comp e.injective)
  intro i j k
  rcases eq_or_ne i j with rfl | hij
  · exact Or.inr (Or.inl (dist_comm _ _))
  rcases eq_or_ne j k with rfl | hjk
  · exact Or.inr (Or.inr (dist_comm _ _))
  rcases eq_or_ne i k with rfl | hik
  · exact Or.inl (dist_comm _ _)
  have inj : Function.Injective p := Subtype.val_injective.comp e.injective
  exact hs.2 (e i).property (e j).property (e k).property (inj.ne hij) (inj.ne hjk) (inj.ne hik)

end OMA.E503R3

theorem OMA.solution : type_of% @Erdos503.erdos_503.variants.R3 := by
  obtain ⟨s, hs, hn⟩ := OMA.E503R3.eight_exists
  refine ⟨⟨s, hs, hn⟩, ?_⟩
  rintro _ ⟨A, hA, rfl⟩
  exact OMA.E503R3.ncard_le_eight hA
