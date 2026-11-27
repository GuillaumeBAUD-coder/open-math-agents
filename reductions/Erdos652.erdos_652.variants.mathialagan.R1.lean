import FormalConjectures.ErdosProblems.«652»

/-! # Mathialagan's bound for distances from a small set of centers

The planar simple-graph edge inequality and an explicit geometric drawing give the
bound for arbitrary, not necessarily nested, sets P and Q. The two-center bound,
crossing deletion, vertex sampling and constants are proved here.
Credit: @JaviSoto. -/

/- The random sampling part of the graph crossing lemma, by exact finite counting. -/

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

/- Two centers give an injective encoding by two radii and a side of their common line. -/

namespace OMA.CircleArcs

open scoped EuclideanGeometry

/-- Two circles with distinct centers meet at most once in either open halfplane of the
line through their centers. Thus arcs cut at every center line cannot have parallel edges
or a second crossing with another incident arc. -/
theorem eq_of_dist_eq_in_same_halfplane {a b x y : ℝ²} (hab : a ≠ b)
    (ha : dist x a = dist y a) (hb : dist x b = dist y b)
    (hs : 0 ≤ ((b 0-a 0)*(x 1-a 1) - (b 1-a 1)*(x 0-a 0)) * ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0))) : x = y := by
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
  have hid (z : ℝ²) : dot z ^ 2 + ((b 0-a 0)*(z 1-a 1) - (b 1-a 1)*(z 0-a 0)) ^ 2 =
      (u^2+v^2)*((z 0-a 0)^2+(z 1-a 1)^2) := by dsimp [dot,u,v]; ring
  have hh := hid x
  rw [hd,hE,← hid y] at hh
  have hside : ((b 0-a 0)*(x 1-a 1) - (b 1-a 1)*(x 0-a 0)) = ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0)) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (add_left_cancel hh) with he | he
    · exact he
    · rw [he] at hs
      have hz : ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0)) = 0 := by nlinarith only [hs, sq_nonneg (((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0)))]
      simp [hz, he]
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

open Finset
open scoped Classical

theorem two_centers (Q : Finset ℝ²) {a b : ℝ²} (hab : a ≠ b) :
    Q.card ≤ 2 * (Q.image fun x => dist a x).card * (Q.image fun x => dist b x).card := by
  let F (x : ℝ²) := (decide (0 ≤ ((b 0-a 0)*(x 1-a 1) - (b 1-a 1)*(x 0-a 0))), dist a x, dist b x)
  let T := (univ : Finset Bool) ×ˢ ((Q.image (dist a)) ×ˢ (Q.image (dist b)))
  have hmap : Set.MapsTo F (Q : Set ℝ²) (T : Set (Bool × ℝ × ℝ)) := by
    intro x hx
    exact mem_product.mpr ⟨mem_univ _, mem_product.mpr ⟨mem_image_of_mem _ hx, mem_image_of_mem _ hx⟩⟩
  have hinj : Set.InjOn F (Q : Set ℝ²) := by
    intro x _ y _ he
    have hs : decide (0 ≤ ((b 0-a 0)*(x 1-a 1) - (b 1-a 1)*(x 0-a 0))) = decide (0 ≤ ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0))) := congrArg Prod.fst he
    have hA : dist a x = dist a y := congrArg (fun t : Bool × ℝ × ℝ => t.2.1) he
    have hB : dist b x = dist b y := congrArg (fun t : Bool × ℝ × ℝ => t.2.2) he
    apply eq_of_dist_eq_in_same_halfplane hab (by simpa only [dist_comm x, dist_comm y] using hA)
      (by simpa only [dist_comm x, dist_comm y] using hB)
    by_cases hx : 0 ≤ ((b 0-a 0)*(x 1-a 1) - (b 1-a 1)*(x 0-a 0))
    · have hy : 0 ≤ ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0)) := by simpa [hx] using hs.symm
      exact mul_nonneg hx hy
    · have hy : ¬ 0 ≤ ((b 0-a 0)*(y 1-a 1) - (b 1-a 1)*(y 0-a 0)) := by simpa [hx] using hs.symm
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hx) (le_of_not_ge hy)
  simpa [T,Nat.mul_assoc] using card_le_card_of_injOn F hmap hinj

end OMA.CircleArcs

/- Quantitative estimates for a bipartite distinct-distance drawing. -/

namespace OMA.Math652

/-- The edge count, pair-of-circles intersection count, and cubic crossing bound
give the square-root distinct distance estimate throughout the range `k³ ≤ n`. -/
theorem distance_bound (k n D e X : ℕ) (hk : 2 ≤ k) (hn : k^3 ≤ n)
    (htwo : n ≤ 2*D^2) (hedge : k*n ≤ e + 4*k^2*(D+1))
    (hX : X ≤ 2*(k*D)^2) (hcross : 12*n ≤ e → e^3 ≤ 288*n^2*X) :
    (1/68 : ℝ)*Real.sqrt ((k:ℝ)*n) ≤ D := by
  have hk0 : 0 < k := by omega
  have hn0 : 0 < n := (pow_pos hk0 3).trans_le hn
  have hD : 1 ≤ D := by
    by_contra! h
    have : D = 0 := by omega
    subst D
    simp_all
  have bound : k*n ≤ 4624*D^2 := by
    by_cases hk' : k ≤ 24
    · calc k*n ≤ 24*(2*D^2) := Nat.mul_le_mul hk' htwo
           _ ≤ 4624*D^2 := by omega
    by_cases he : k*n ≤ 2*e
    · have dense : 12*n ≤ e := by
        have := Nat.mul_le_mul_right n (show 24 ≤ k by omega)
        omega
      have cube : (k*n)^3 ≤ (2*e)^3 := by gcongr
      have upper : e^3 ≤ 288*n^2*(2*(k*D)^2) :=
        (hcross dense).trans (Nat.mul_le_mul_left _ hX)
      have h : k*n ≤ 4608*D^2 := by
        apply Nat.le_of_mul_le_mul_left (c := k^2*n^2) _ (by positivity)
        nlinarith only [cube,upper]
      omega
    · have loss : n ≤ 16*k*D := by
        apply Nat.le_of_mul_le_mul_left (c := k) _ hk0
        have := Nat.mul_le_mul_left (4*k^2) (show D+1 ≤ 2*D by omega)
        nlinarith only [hedge,he,this]
      have h : k*n ≤ 256*D^2 := by
        apply Nat.le_of_mul_le_mul_left (c := k^2) _ (by positivity)
        have hsq : n^2 ≤ (16*k*D)^2 := by gcongr
        nlinarith only [hsq,Nat.mul_le_mul_right n hn]
      omega
  have hreal : (k:ℝ)*n ≤ (68*(D:ℝ))^2 := by
    have cast : (k:ℝ)*n ≤ 4624*(D:ℝ)^2 := by exact_mod_cast bound
    nlinarith only [cast]
  have hroot : Real.sqrt ((k:ℝ)*n) ≤ 68*(D:ℝ) :=
    (Real.sqrt_le_iff.mpr ⟨by positivity,hreal⟩)
  linarith

end OMA.Math652

/- Plane drawings, the linear planar edge inequality and the circle-arc input. -/

namespace OMA.R_Erdos652_erdos_652_variants_mathialagan_R1

open Finset
open scoped EuclideanGeometry Classical

/-- Euler's linear edge bound for a simple drawing with disjoint edge interiors. -/
def H1 : Prop :=
  ∀ (Q : Finset ℝ²) (S : Finset Q) (E : Finset ℕ) (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²),
  (∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
    ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = Set.range γ ∧
      ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i) →
  (∀ i ∈ E, edge i ⊆ S) → Set.InjOn edge (E : Set ℕ) →
  (∀ i ∈ E, ∀ j ∈ E, i ≠ j → curve i ∩ curve j ⊆ Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) →
  E.card ≤ 3 * S.card

/-- Use arcs between consecutive data points on the concentric circles about each center.
Cut at all center lines so crossings involve four distinct endpoints. C records the
ordered exceptional pairs; unlisted pairs meet only at common endpoints. -/
def H2 : Prop :=
  ∀ (P Q : Finset ℝ²) (D : ℕ), 2 ≤ P.card → P.card ^ 3 ≤ Q.card →
  (∀ p ∈ P, (Q.image (dist p)).card ≤ D) →
  ∃ (E : Finset ℕ) (edge : ℕ → Finset Q) (curve : ℕ → Set ℝ²) (C : Finset (ℕ × ℕ)),
  (∀ i ∈ E, ∃ x y : Q, x ≠ y ∧ edge i = {x,y} ∧
    ∃ γ : Path (x : ℝ²) (y : ℝ²), Function.Injective γ ∧ curve i = Set.range γ ∧
      ∀ v : Q, (v : ℝ²) ∈ curve i → v ∈ edge i) ∧
  Set.InjOn edge (E : Set ℕ) ∧
  (∀ i ∈ E, ∀ j ∈ E, i ≠ j → (i,j) ∉ C → curve i ∩ curve j ⊆ Subtype.val '' ((edge i ∩ edge j : Finset Q) : Set Q)) ∧
  (∀ ij ∈ C, (edge ij.1 ∪ edge ij.2).card = 4) ∧
  P.card * Q.card ≤ E.card + 4 * P.card^2 * (D+1) ∧ C.card ≤ 2 * (P.card*D)^2

/-- Removing the first edge of each crossing suffices for every induced subdrawing. -/
theorem induced_edges {Q : Finset ℝ²} (planar : H1) (E : Finset ℕ) (edge : ℕ → Finset Q)
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
    apply planar Q S G edge curve (fun i hi => drawn i (hE hi))
      (fun _ hi => (mem_filter.mp (hsub hi)).2) (fun _ hi _ hj eq => inj (hE hi) (hE hj) eq)
    intro i hi j hj hij
    apply meet i (hE hi) j (hE hj) hij
    intro hc
    exact (mem_sdiff.mp hi).2 (mem_image.mpr ⟨(i,j), mem_filter.mpr
      ⟨hc, union_subset (mem_filter.mp (hsub hi)).2 (mem_filter.mp (hsub hj)).2⟩, rfl⟩)
  calc F.card ≤ G.card + (K.image Prod.fst).card := card_le_card_sdiff_add_card
       _ ≤ 3 * S.card + K.card := Nat.add_le_add hgood card_image_le

theorem main : H1 → H2 → type_of% @Erdos652.erdos_652.variants.mathialagan := by
  intro hplanar hdraw
  refine ⟨1/68, by norm_num, ?_⟩
  intro P Q hk hn
  let d (p : ℝ²) := (Q.image (dist p)).card
  obtain ⟨p, hp, hmax⟩ := P.exists_max_image d (card_pos.mp (by omega))
  obtain ⟨u, v, hu, hv, huv⟩ := one_lt_card_iff.mp hk
  have htwo : Q.card ≤ 2 * (d p)^2 := calc
    Q.card ≤ 2 * d u * d v := OMA.CircleArcs.two_centers Q huv
    _ ≤ 2 * d p * d p := by gcongr <;> apply hmax <;> assumption
    _ = _ := by ring
  obtain ⟨E, edge, curve, C, drawn, hinj, meet, four, hedge, hX⟩ := hdraw P Q (d p) hk hn hmax
  refine ⟨p, hp, OMA.Math652.distance_bound P.card Q.card (d p) E.card C.card
    hk hn htwo hedge hX ?_⟩
  intro hdense
  have hV : 4 ≤ Q.card := by
    have h := Nat.pow_le_pow_left hk 3
    omega
  have two (i) (hi : i ∈ E) : (edge i).card = 2 := by
    obtain ⟨x,y,hne,he,_⟩ := drawn i hi
    simp [he,hne]
  have h := OMA.Crossing.cubic_crossing_bound E C edge (fun ij => edge ij.1 ∪ edge ij.2)
    two four (by simpa only [Fintype.card_coe] using hV)
    (by simpa only [Fintype.card_coe] using hdense) (induced_edges hplanar E edge curve C drawn hinj meet)
  simpa only [Fintype.card_coe] using h

end OMA.R_Erdos652_erdos_652_variants_mathialagan_R1
