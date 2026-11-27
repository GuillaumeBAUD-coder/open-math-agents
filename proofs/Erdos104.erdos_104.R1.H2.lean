import OMAReductions.R_Erdos104_erdos_104_R1

/-! # Unit circles containing a chord of prescribed length

There are at most two unit-circle centers for any pair of distinct endpoints.
A pair of vertices has at most two common neighbors in a fixed-distance graph;
double-counting these neighbors bounds its number of ordered edges by
the square root of three times the cube of its number of vertices. -/

/- A fixed distance has subquadratically many ordered pairs: two different centers
have at most two common neighbors, so Cauchy--Schwarz bounds the number of pairs.
The half-plane calculation is from our Mathialagan proof for Erdős 652 (#2684). -/
namespace OMA.PairBound104
open Finset
open scoped EuclideanGeometry Classical

private theorem eq_of_dist_eq_in_same_halfplane {a b x y : ℝ²} (hab : a ≠ b)
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

/-- In a prescribed finite set, at most two points have specified equal distances
to two distinct fixed points. -/
theorem common (P : Finset ℝ²) (d : ℝ) {a b : ℝ²} (hab : a ≠ b) :
    (P.filter (fun z => dist a z=d ∧ dist b z=d)).card ≤ 2 := by
  let S := P.filter (fun z => dist a z=d ∧ dist b z=d)
  let side (z : ℝ²) := (b 0-a 0)*(z 1-a 1)-(b 1-a 1)*(z 0-a 0)
  let code (z : S) := decide (0 ≤ side z)
  have inj : Function.Injective code := by
    intro x y he
    apply Subtype.ext
    obtain ⟨hx,hx'⟩ := (mem_filter.mp x.property).2
    obtain ⟨hy,hy'⟩ := (mem_filter.mp y.property).2
    apply eq_of_dist_eq_in_same_halfplane hab
    · simpa only [dist_comm (x:ℝ²),dist_comm (y:ℝ²)] using hx.trans hy.symm
    · simpa only [dist_comm (x:ℝ²),dist_comm (y:ℝ²)] using hx'.trans hy'.symm
    · change 0 ≤ side x * side y
      by_cases h : 0 ≤ side x
      · have hy : 0 ≤ side y := by simpa [code,h] using he
        exact mul_nonneg h hy
      · have hy : ¬0 ≤ side y := by simpa [code,h] using he
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge h) (le_of_not_ge hy)
  simpa [S] using Fintype.card_le_of_injective code inj

/-- Sum the two-step walks by their endpoints. Off the diagonal there are at most
two midpoints; on the diagonal the trivial bound suffices. -/
theorem square (P : Finset ℝ²) (d : ℝ) :
    (((P ×ˢ P).filter (fun e => e.1 ≠ e.2 ∧ dist e.1 e.2=d)).card)^2 ≤ 3 * P.card^3 := by
  let f (x y : ℝ²) : ℕ := if dist y x=d then 1 else 0
  let deg (x : ℝ²) := ∑ y ∈ P, f x y
  have codeg (y z : ℝ²) : ∑ x ∈ P, f x y * f x z =
      (P.filter (fun x => dist y x=d ∧ dist z x=d)).card := by
    rw [Finset.card_filter]
    apply sum_congr rfl
    intro x _
    by_cases hy : dist y x=d <;> by_cases hz : dist z x=d <;> simp [f,hy,hz]
  have row (y : ℝ²) (hy : y∈P) : ∑ z ∈ P, ∑ x ∈ P, f x y*f x z ≤ 3*P.card := by
    calc
      _ ≤ ∑ z ∈ P, ((if y=z then P.card else 0)+2) := by
        apply sum_le_sum
        intro z _
        rw [codeg]
        by_cases eq : y=z
        · simp only [eq,if_true]
          exact (card_filter_le ..).trans (by omega)
        · simpa [eq] using common P d eq
      _ = 3*P.card := by simp [sum_add_distrib,hy]; omega
  have moment : ∑ x ∈ P, (deg x)^2 ≤ 3*P.card^2 := by
    calc
      _ = ∑ x ∈ P, ∑ y ∈ P, ∑ z ∈ P, f x y*f x z := by
        simp only [deg,pow_two,sum_mul,mul_sum]
        apply sum_congr rfl
        intro x _
        exact sum_comm
      _ = ∑ y ∈ P, ∑ z ∈ P, ∑ x ∈ P, f x y*f x z := by
        rw [sum_comm]
        apply sum_congr rfl
        intro y _
        exact sum_comm
      _ ≤ ∑ _y ∈ P, 3*P.card := sum_le_sum row
      _ = _ := by simp; ring
  have e : ((P ×ˢ P).filter (fun e => e.1 ≠ e.2 ∧ dist e.1 e.2=d)).card ≤ ∑ x ∈ P, deg x := by
    rw [Finset.card_filter, sum_product]
    apply sum_le_sum
    intro x _
    apply sum_le_sum
    intro y _
    by_cases h : dist x y=d <;> by_cases eq : x=y <;> simp_all [f,dist_comm y x]
  calc
    _ ≤ (∑ x ∈ P, deg x)^2 := Nat.pow_le_pow_left e 2
    _ ≤ P.card * ∑ x ∈ P, (deg x)^2 := sq_sum_le_card_mul_sum_sq
    _ ≤ P.card * (3*P.card^2) := Nat.mul_le_mul_left _ moment
    _ = _ := by ring

theorem pair_bound (d ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ P : Finset ℝ², P.card ≤ n →
      (((P ×ˢ P).filter (fun e => e.1 ≠ e.2 ∧ dist e.1 e.2=d)).card:ℝ) ≤ ε*(n:ℝ)^2 := by
  obtain ⟨N,hN⟩ := exists_nat_ge (3/ε^2)
  refine ⟨N,?_⟩
  intro n hn P hP
  have h : 3 ≤ n*ε^2 := (div_le_iff₀ (sq_pos_of_pos hε)).mp (hN.trans (Nat.cast_le.mpr hn))
  have sq := (square P d).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 3))
  have cast : (((P ×ˢ P).filter (fun e => e.1 ≠ e.2 ∧ dist e.1 e.2=d)).card:ℝ)^2 ≤ 3*(n:ℝ)^3 := by
    exact_mod_cast sq
  apply le_of_sq_le_sq _ (by positivity)
  calc
    _ ≤ 3*(n:ℝ)^3 := cast
    _ ≤ (n*ε^2)*(n:ℝ)^3 := mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by ring

end OMA.PairBound104

/- Count unit circles by a distinguished ordered chord. The fixed-chord
decomposition is due to JamesSlash (Erdős 104, reduction R1).
The center maps each fiber injectively into the common unit neighbors of
the two ends of that chord. -/

open EuclideanGeometry Finset
open scoped EuclideanGeometry Classical

namespace OMA.CirclePairs104

theorem circle_count
    (common : ∀ (Q : Finset ℝ²) (d : ℝ) {a b : ℝ²}, a ≠ b →
      (Q.filter (fun z => dist a z = d ∧ dist b z = d)).card ≤ 2)
    (P : Finset ℝ²) (d : ℝ) :
    {s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = d ∧ a ∈ s ∧ b ∈ s}.ncard ≤
        2*((P ×ˢ P).filter (fun e => e.1 ≠ e.2 ∧ dist e.1 e.2 = d)).card := by
  let circles : Set (Sphere ℝ²) := {s | s.radius = 1 ∧
    ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = d ∧ a ∈ s ∧ b ∈ s}
  let pairs := (P ×ˢ P).filter (fun e => e.1 ≠ e.2 ∧ dist e.1 e.2 = d)
  change circles.ncard ≤ 2*pairs.card
  have bound (S : Finset (Sphere ℝ²)) (hS : (S : Set _) ⊆ circles) : S.card ≤ 2*pairs.card := by
    let block (e : ℝ² × ℝ²) := S.filter fun s => e.1 ∈ s ∧ e.2 ∈ s
    have covers : S ⊆ pairs.biUnion block := by
      intro s hs
      obtain ⟨_,a,ha,b,hb,hab,hd,has,hbs⟩ := hS hs
      refine mem_biUnion.2 ⟨(a,b), mem_filter.2 ⟨mem_product.2 ⟨ha,hb⟩,hab,hd⟩, ?_⟩
      exact mem_filter.2 ⟨hs,has,hbs⟩
    have hblock (e : ℝ² × ℝ²) (he : e ∈ pairs) : (block e).card ≤ 2 := by
      let Q := S.image Sphere.center
      let C := Q.filter fun z => dist e.1 z = 1 ∧ dist e.2 z = 1
      have hmap : Set.MapsTo Sphere.center (block e : Set (Sphere ℝ²)) (C : Set ℝ²) := by
        intro s hs
        obtain ⟨hs,ha,hb⟩ := mem_filter.1 hs
        have hr : s.radius = 1 := (hS hs).1
        exact mem_filter.2 ⟨mem_image_of_mem _ hs, (mem_sphere.1 ha).trans hr, (mem_sphere.1 hb).trans hr⟩
      have hinj : Set.InjOn Sphere.center (block e : Set (Sphere ℝ²)) := by
        intro s hs t ht h
        have hrs : s.radius = 1 := (hS (mem_filter.1 hs).1).1
        have hrt : t.radius = 1 := (hS (mem_filter.1 ht).1).1
        rw [← Sphere.mk_center_radius s, ← Sphere.mk_center_radius t, h, hrs, hrt]
      exact (card_le_card_of_injOn _ hmap hinj).trans (common Q 1 (mem_filter.1 he).2.1)
    exact (card_le_card covers).trans ((card_biUnion_le_card_mul _ _ _ hblock).trans_eq (Nat.mul_comm _ 2))
  have hf : circles.Finite := by
    by_contra hn
    obtain ⟨S,hS,hcard⟩ := Set.Infinite.exists_subset_card_eq hn (2*pairs.card+1)
    have := bound S hS
    omega
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact bound hf.toFinset (by simp)

end OMA.CirclePairs104

theorem OMA.solution : OMA.R_Erdos104_erdos_104_R1.H2 := by
  intro d ε hε
  obtain ⟨N,hN⟩ := OMA.PairBound104.pair_bound d (ε/2) (by positivity)
  refine ⟨N,fun n hn P hP => ?_⟩
  have a := OMA.CirclePairs104.circle_count OMA.PairBound104.common P d
  have b := hN n hn P hP
  exact (Nat.cast_le.mpr a : (_:ℝ) ≤ _).trans (by push_cast; linarith)
