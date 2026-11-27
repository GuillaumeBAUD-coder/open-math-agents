import FormalConjectures.ErdosProblems.«653»
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Order.Interval.Finset.Fin

/-!
The midpoint arrays and encoding by masks are adapted from the construction of
Liam Kruer and Jensen Kohlmeyer, submitted as gus on Conjectures.io.
https://conjectures.io/results/257ce6dd-e3e5-4169-9d7e-2811092977ca/solution

The geometric part computes affine adjustments using full periods of integer
division and implements the remaining adjustments with finite dictionaries on
three projections. This reduction also constructs the coarse degrees, proves
disjointness and projection separation using private inert-prime residues, and
converts bin overflow to integer corrections.
-/

open Finset Filter EuclideanGeometry Polynomial
open scoped BigOperators EuclideanGeometry Polynomial Topology

namespace OMA.R_Erdos653_erdos_653_R2

private def planePoint (x y : ℝ) : ℝ² := WithLp.toLp 2 ![x, y]

@[simp] theorem planePoint_zero (x y : ℝ) : planePoint x y 0 = x := rfl
@[simp] theorem planePoint_one (x y : ℝ) : planePoint x y 1 = y := rfl

private theorem point_eq_of_coords {p q : ℝ²} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

private theorem sqDist_coords (p q : ℝ²) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity)]
  simp only [Real.dist_eq, sq_abs]

private noncomputable def move (s T : ℝ) (a : ℝ²) : ℝ² :=
  planePoint (a 0 + s * T) (a 1 + s * T ^ 2)

private noncomputable def distancePoly (s : ℝ) (p a : ℝ²) : ℝ[X] :=
  X ^ 4 + C (1 + 2 * s * (a 1 - p 1)) * X ^ 2 + C (2 * s * (a 0 - p 0)) * X +
    C ((a 0 - p 0) ^ 2 + (a 1 - p 1) ^ 2)

private theorem eval_distancePoly (s T : ℝ) (p a : ℝ²) (hs : s ^ 2 = 1) :
    (distancePoly s p a).eval T = dist (move s T a) p ^ 2 := by
  rw [sqDist_coords]
  simp [distancePoly, move]
  linear_combination -(T ^ 4 + T ^ 2) * hs

private theorem distancePoly_injective (s : ℝ) (hs : s ≠ 0) (p : ℝ²) :
    Function.Injective (distancePoly s p) := by
  intro a b h
  have h0 := congrArg (fun f : ℝ[X] => f.coeff 1) h
  have h1 := congrArg (fun f : ℝ[X] => f.coeff 2) h
  norm_num only [distancePoly, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X,
    coeff_C, ite_true, ite_false] at h0 h1
  apply point_eq_of_coords
  · exact mul_left_cancel₀ hs (by linarith only [h0])
  · exact mul_left_cancel₀ hs (by linarith only [h1])

private theorem opposite_eq_iff (p a b : ℝ²) :
    distancePoly 1 p a = distancePoly (-1) p b ↔ b = p + p - a := by
  constructor
  · intro h
    have h0 := congrArg (fun f : ℝ[X] => f.coeff 1) h
    have h1 := congrArg (fun f : ℝ[X] => f.coeff 2) h
    norm_num only [distancePoly, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X,
    coeff_C, ite_true, ite_false] at h0 h1
    apply point_eq_of_coords
    · change b 0 = p 0 + p 0 - a 0
      linarith
    · change b 1 = p 1 + p 1 - a 1
      linarith
  · rintro rfl
    have h0 : (p + p - a) 0 - p 0 = -(a 0 - p 0) := by
      change p 0 + p 0 - a 0 - p 0 = _
      ring
    have h1 : (p + p - a) 1 - p 1 = -(a 1 - p 1) := by
      change p 1 + p 1 - a 1 - p 1 = _
      ring
    unfold distancePoly
    rw [h0, h1]
    ring_nf

private theorem distancePoly_ne_constant (s : ℝ) (p a : ℝ²) (r : ℝ) :
    distancePoly s p a ≠ C r := by
  intro h
  have hh := congrArg (fun f : ℝ[X] => f.coeff 4) h
  norm_num only [distancePoly, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X,
    coeff_C, ite_true, ite_false] at hh

private theorem eventually_eval_imp_eq (f g : ℝ[X]) :
    ∀ᶠ t : ℝ in atTop, f.eval t = g.eval t → f = g := by
  by_cases h : f = g
  · exact Eventually.of_forall fun _ _ => h
  · obtain ⟨m, hm⟩ := (f - g).exists_max_root (sub_ne_zero.mpr h)
    filter_upwards [eventually_gt_atTop m] with t ht he
    exact (not_le_of_gt ht (hm t (by simp [Polynomial.IsRoot, he]))).elim

private noncomputable def oldPolys (P : Finset ℝ²) (p : ℝ²) : Finset ℝ[X] := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  exact (P.erase p).image fun q => C (dist q p ^ 2)

private noncomputable def matched (A B : Finset ℝ²) (p : ℝ²) : Finset ℝ² := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  exact A.filter fun a => p + p - a ∈ B

private theorem card_oldPolys (P : Finset ℝ²) (p : ℝ²) :
    (oldPolys P p).card = distinctDistancesFrom P p := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  unfold oldPolys distinctDistancesFrom
  change ((P.erase p).image ((fun x : ℝ => C (x ^ 2)) ∘ (fun q => dist q p))).card = _
  rw [← Finset.image_image]
  apply Finset.card_image_of_injOn
  intro x hx y hy he
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  have hh := Polynomial.C_injective he
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hh).elim id (fun he' =>
    by linarith [dist_nonneg (x := u) (y := p), dist_nonneg (x := v) (y := p)])

private theorem extend_by_midpoints (P A B : Finset ℝ²) :
    ∃ Q : Finset ℝ², P ⊆ Q ∧ Q.card ≤ P.card + A.card + B.card ∧
      ∀ p ∈ P, (distinctDistancesFrom Q p : ℤ) =
        distinctDistancesFrom P p + A.card + B.card -
          (matched A B p).card := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  let polynomials : Finset ℝ[X] :=
    P.biUnion fun p => (P.image fun q => C (dist q p ^ 2)) ∪
        (A.image (distancePoly 1 p) ∪ B.image (distancePoly (-1) p))
  have hAvoid : ∀ᶠ t : ℝ in atTop,
      ∀ f ∈ polynomials, ∀ g ∈ polynomials, f.eval t = g.eval t → f = g :=
    (eventually_all_finset _).2 fun f _ =>
      (eventually_all_finset _).2 fun g _ => eventually_eval_imp_eq f g
  obtain ⟨t, ht⟩ := hAvoid.exists
  let A' := A.image (move 1 t)
  let B' := B.image (move (-1) t)
  let Q := (P ∪ A') ∪ B'
  have hPQ' : P ⊆ P ∪ A' := Finset.subset_union_left
  have hPQ : P ⊆ Q := hPQ'.trans Finset.subset_union_left
  refine ⟨Q, hPQ, ?_, ?_⟩
  · dsimp [Q]
    exact (Finset.card_union_le _ _).trans
      (add_le_add ((Finset.card_union_le _ _).trans (add_le_add_right Finset.card_image_le _))
        Finset.card_image_le)
  · intro p hp
    let PA := A.image (distancePoly 1 p)
    let PB := B.image (distancePoly (-1) p)
    let R := oldPolys P p ∪ (PA ∪ PB)
    have hconst (q) (hq : q ∈ P) : C (dist q p ^ 2) ∈ polynomials :=
      Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq)⟩
    have ha (f) (hf : f ∈ PA) : f ∈ polynomials :=
      Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_union_right _ (Finset.mem_union_left _ hf)⟩
    have hb (f) (hf : f ∈ PB) : f ∈ polynomials :=
      Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_union_right _ (Finset.mem_union_right _ hf)⟩
    have hR : R ⊆ polynomials := by
      intro f hf
      rcases Finset.mem_union.mp hf with hf | hf
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
        exact hconst q (Finset.mem_erase.mp hq).2
      · exact (Finset.mem_union.mp hf).elim (ha f) (hb f)
    have hpA : p ∉ A' := by
      intro h
      obtain ⟨a, hA, he⟩ := Finset.mem_image.mp h
      apply distancePoly_ne_constant 1 p a (dist p p ^ 2)
      apply ht _ (ha _ (Finset.mem_image_of_mem _ hA)) _ (hconst _ hp)
      rw [eval_distancePoly _ _ _ _ (by norm_num), he, eval_C]
    have hpB : p ∉ B' := by
      intro h
      obtain ⟨b, hB, he⟩ := Finset.mem_image.mp h
      apply distancePoly_ne_constant (-1) p b (dist p p ^ 2)
      apply ht _ (hb _ (Finset.mem_image_of_mem _ hB)) _ (hconst _ hp)
      rw [eval_distancePoly _ _ _ _ (by norm_num), he, eval_C]
    have hcount : distinctDistancesFrom Q p = R.card := by
      have hsq : Set.InjOn (fun x : ℝ => x ^ 2)
          ↑((Q.erase p).image (fun q => dist q p)) := by
        intro x hx y hy hh
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
        exact (sq_eq_sq_iff_eq_or_eq_neg.mp hh).elim id
          (fun h => by linarith [dist_nonneg (x := u) (y := p), dist_nonneg (x := v) (y := p)])
      rw [← Finset.card_image_of_injOn (fun f hf g hg h => ht f (hR hf) g (hR hg) h :
        Set.InjOn (fun f : ℝ[X] => f.eval t) (R : Set ℝ[X]))]
      change ((Q.erase p).image (fun q => dist q p)).card = _
      rw [← Finset.card_image_of_injOn hsq, Finset.image_image]
      congr 1
      have hA'image : A'.image (fun q => dist q p ^ 2) = PA.image (fun f => f.eval t) := by
        rw [Finset.image_image, Finset.image_image]
        apply Finset.image_congr
        intro a _
        exact (eval_distancePoly _ _ _ _ (by norm_num)).symm
      have hB'image : B'.image (fun q => dist q p ^ 2) = PB.image (fun f => f.eval t) := by
        rw [Finset.image_image, Finset.image_image]
        apply Finset.image_congr
        intro a _
        exact (eval_distancePoly _ _ _ _ (by norm_num)).symm
      have hErase : Q.erase p = (P.erase p ∪ A') ∪ B' := by
        change ((P ∪ A') ∪ B').erase p = _
        rw [Finset.erase_union_distrib, Finset.erase_union_distrib,
          Finset.erase_eq_of_notMem hpA, Finset.erase_eq_of_notMem hpB]
      have hOld : (oldPolys P p).image (fun f => f.eval t) =
          (P.erase p).image (fun q => dist q p ^ 2) := by
        rw [oldPolys, Finset.image_image]
        simp only [Function.comp_def, Polynomial.eval_C]
      change (Q.erase p).image (fun q => dist q p ^ 2) =
        (oldPolys P p ∪ (PA ∪ PB)).image (fun f => f.eval t)
      rw [hErase, Finset.image_union, Finset.image_union, hA'image, hB'image,
        Finset.image_union, Finset.image_union, hOld, Finset.union_assoc]
    have hdisj : Disjoint (oldPolys P p) (PA ∪ PB) := by
      refine Finset.disjoint_left.mpr ?_
      intro f hf hfg
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
      rcases Finset.mem_union.mp hfg with hg | hg
      · obtain ⟨a, hma, he⟩ := Finset.mem_image.mp hg
        exact distancePoly_ne_constant _ _ _ _ he
      · obtain ⟨b, hmb, he⟩ := Finset.mem_image.mp hg
        exact distancePoly_ne_constant _ _ _ _ he
    have hinter : PA ∩ PB = (matched A B p).image (distancePoly 1 p) := by
      unfold matched
      ext f
      constructor
      · intro hf
        obtain ⟨hfa, hfb⟩ := Finset.mem_inter.mp hf
        obtain ⟨a, hma, rfl⟩ := Finset.mem_image.mp hfa
        obtain ⟨b, hmb, he⟩ := Finset.mem_image.mp hfb
        have hb' := (opposite_eq_iff _ _ _).mp he.symm
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hma, hb' ▸ hmb⟩)
      · intro hf
        obtain ⟨a, hma, rfl⟩ := Finset.mem_image.mp hf
        obtain ⟨haA, haB⟩ := Finset.mem_filter.mp hma
        exact Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ haA,
          Finset.mem_image.mpr ⟨_, haB, ((opposite_eq_iff _ _ _).mpr rfl).symm⟩⟩
    have hcard := Finset.card_union_add_card_inter PA PB
    rw [hinter, Finset.card_image_of_injective _ (distancePoly_injective 1 one_ne_zero p)] at hcard
    have hca : PA.card = A.card := Finset.card_image_of_injective _ (distancePoly_injective 1 one_ne_zero p)
    have hcb : PB.card = B.card := Finset.card_image_of_injective _ (distancePoly_injective (-1) (by norm_num) p)
    rw [hca, hcb] at hcard
    rw [hcount, show R.card = (oldPolys P p).card + (PA ∪ PB).card from
      Finset.card_union_of_disjoint hdisj, card_oldPolys]
    omega

private def rowSum (L : ℕ) (k : ℤ) (y : ℕ) : ℤ :=
  ∑ r ∈ range L, (k * ((y : ℤ) - r)) / (L : ℤ)

private theorem rowSum_succ {L : ℕ} (hL : 0 < L) (k : ℤ) (y : ℕ) :
    rowSum L k (y + 1) = rowSum L k y + k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  unfold rowSum
  rw [sum_range_succ', sum_range_succ]
  simp only [Nat.cast_succ, Nat.cast_zero, sub_zero]
  have hmid : (∑ r ∈ range m, k * ((y : ℤ) + 1 - ((r : ℤ) + 1)) / ((m : ℤ) + 1)) =
      ∑ r ∈ range m, k * ((y : ℤ) - r) / ((m : ℤ) + 1) := by
    apply sum_congr rfl
    intro r _
    congr 2
    ring
  have hend : k * ((y : ℤ) + 1) / ((m : ℤ) + 1) =
      k * ((y : ℤ) - m) / ((m : ℤ) + 1) + k := by
    rw [show k * ((y : ℤ) + 1) =
      k * ((y : ℤ) - m) + k * ((m : ℤ) + 1) by ring,
      Int.add_mul_ediv_right _ _ (by positivity)]
  rw [hmid, hend]
  ring

private theorem rowSum_eq {L : ℕ} (hL : 0 < L) (k : ℤ) (y : ℕ) :
    rowSum L k y = rowSum L k 0 + k * y := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [rowSum_succ hL, ih]
    push_cast
    ring

private def skewLeft (L : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(4 * (L : ℤ))) (4 * (L : ℤ))).product (Ico 0 (L : ℤ))

private def skewRight (L : ℕ) (k : ℤ) : Finset (ℤ × ℤ) :=
  (Icc (1 - (L : ℤ)) ((L : ℤ) - 1)).biUnion fun h =>
    (Icc (-(6 * (L : ℤ))) (k * h / (L : ℤ))).image fun j => (j, h)

private def midpointMatches (A B : Finset (ℤ × ℤ)) (x y : ℕ) : Finset (ℤ × ℤ) :=
  A.filter fun a => ((x : ℤ) - a.1, (y : ℤ) - a.2) ∈ B

private theorem midpointMatches_card {L x y : ℕ} (hx : x < L) (hy : y < L) {k : ℤ}
    (hk : |k| ≤ (L : ℤ)) :
    ((midpointMatches (skewLeft L) (skewRight L k) x y).card : ℤ) =
      4 * (L : ℤ) ^ 2 + L + rowSum L k 0 - (L : ℤ) * x + k * y := by
  have hL : 0 < L := Nat.zero_lt_of_lt hx
  have hLz : 0 < (L : ℤ) := by exact_mod_cast hL
  have hxz : (x : ℤ) < (L : ℤ) := by exact_mod_cast hx
  have hyz : (y : ℤ) < (L : ℤ) := by exact_mod_cast hy
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hx0 : (0 : ℤ) ≤ x := by positivity
  let upper (r : ℕ) : ℤ := k * ((y : ℤ) - r) / (L : ℤ)
  have hup (r : ℕ) (hr : r < L) : -(L : ℤ) ≤ upper r ∧ upper r ≤ L := by
    have hrz : (r : ℤ) < (L : ℤ) := by exact_mod_cast hr
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have hmul : |k * ((y : ℤ) - r)| ≤ (L : ℤ) * L := by
      rw [abs_mul]
      apply mul_le_mul hk (abs_le.mpr (by omega)) (abs_nonneg _) (by positivity)
    rcases abs_le.mp hmul with ⟨hlo, hhi⟩
    exact ⟨Int.le_ediv_of_mul_le hLz (by simpa only [neg_mul] using hlo),
      Int.ediv_le_of_le_mul hLz hhi⟩
  let I := (range L).sigma fun r => Icc ((x : ℤ) - upper r) (4 * (L : ℤ))
  let emb : (Σ _ : ℕ, ℤ) ↪ ℤ × ℤ :=
    ⟨fun a => (a.2, a.1), by
      rintro ⟨a, b⟩ ⟨c, d⟩ h
      have hac : a = c := by
        have hh : (a : ℤ) = c := congrArg Prod.snd h
        exact_mod_cast hh
      subst c
      have hbd : b = d := congrArg Prod.fst h
      subst d
      rfl⟩
  have hI : I.map emb = midpointMatches (skewLeft L) (skewRight L k) x y := by
    ext p
    rcases p with ⟨a, b⟩
    change (a, b) ∈ I.map emb ↔ (a, b) ∈ (skewLeft L).filter _
    rw [Finset.mem_filter]
    change (a, b) ∈ I.map emb ↔ (a, b) ∈ skewLeft L ∧
      ((x : ℤ) - a, (y : ℤ) - b) ∈ skewRight L k
    have hleft : (a,b) ∈ skewLeft L ↔
        (-(4 * (L : ℤ)) ≤ a ∧ a ≤ 4 * (L : ℤ)) ∧ (0 ≤ b ∧ b < L) := by
      unfold skewLeft
      exact Finset.mem_product.trans (and_congr Finset.mem_Icc Finset.mem_Ico)
    rw [hleft]
    simp only [I, skewRight, Finset.mem_map, mem_sigma,
      mem_range, mem_Icc, mem_biUnion, mem_image]
    constructor
    · rintro ⟨⟨r, v⟩, ⟨hr, hlo, hhi⟩, he⟩
      change (v, (r : ℤ)) = (a, b) at he
      have ha : a = v := (congrArg Prod.fst he).symm
      have hb : b = (r : ℤ) := (congrArg Prod.snd he).symm
      subst a
      subst b
      have hrz : (r : ℤ) < (L : ℤ) := by exact_mod_cast hr
      have hr0 : (0 : ℤ) ≤ r := by positivity
      have hh := hup r hr
      change v ≤ 4 * (L : ℤ) at hhi
      change (x : ℤ) - k * ((y : ℤ) - r) / (L : ℤ) ≤ v at hlo
      exact ⟨⟨⟨by dsimp [upper] at hh; omega, hhi⟩, hr0, hrz⟩,
        (y : ℤ) - r, ⟨by omega, by omega⟩, (x : ℤ) - v, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨⟨⟨halo, hahi⟩, hb0, hbL⟩, h, hh, j, hj, hpair⟩
      have hrz : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb0
      have hr : b.toNat < L := by exact_mod_cast (hrz ▸ hbL)
      have hfst : j = (x : ℤ) - a := congrArg Prod.fst hpair
      have hsnd : h = (y : ℤ) - b := congrArg Prod.snd hpair
      subst j
      subst h
      refine ⟨⟨b.toNat, a⟩, ⟨hr, ?_, hahi⟩, ?_⟩
      · dsimp [upper]
        rw [hrz]
        omega
      · change (a, ((b.toNat : ℕ) : ℤ)) = (a, b)
        rw [hrz]
  rw [← hI, card_map]
  simp only [I, card_sigma, Nat.cast_sum]
  calc
    ∑ r ∈ range L, ((Icc ((x : ℤ) - upper r) (4 * (L : ℤ))).card : ℤ) =
        ∑ r ∈ range L, (4 * (L : ℤ) + 1 - ((x : ℤ) - upper r)) := by
      apply sum_congr rfl
      intro r hr
      have hh := hup r (mem_range.mp hr)
      exact Int.card_Icc_of_le _ _ (by omega)
    _ = 4 * (L : ℤ) ^ 2 + L + rowSum L k 0 - (L : ℤ) * x + k * y := by
      have hterm (r : ℕ) : 4 * (L : ℤ) + 1 - ((x : ℤ) - upper r) =
          (4 * (L : ℤ) + 1 - x) + upper r := by ring
      simp only [hterm, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
      change (L : ℤ) * (4 * L + 1 - x) + rowSum L k y = _
      rw [rowSum_eq hL]
      ring

private def intPoint (v : ℤ × ℤ) : ℝ² := planePoint v.1 v.2

private theorem intPoint_injective : Function.Injective intPoint := by
  intro u v h
  apply Prod.ext
  · have hh : (u.1 : ℝ) = v.1 := congrArg (fun p : ℝ² => p 0) h
    exact_mod_cast hh
  · have hh : (u.2 : ℝ) = v.2 := congrArg (fun p : ℝ² => p 1) h
    exact_mod_cast hh

private theorem intPoint_add (u v : ℤ × ℤ) :
    intPoint (u + v) = intPoint u + intPoint v := by
  apply point_eq_of_coords <;> simp [intPoint, PiLp.add_apply]

private theorem intPoint_sub (u v : ℤ × ℤ) :
    intPoint (u - v) = intPoint u - intPoint v := by
  apply point_eq_of_coords <;> simp [intPoint, PiLp.sub_apply]

private def gridPoint (swap : Bool) (v : ℤ × ℤ) : ℝ² :=
  intPoint (if swap then v.swap else v)

private theorem gridPoint_injective (swap : Bool) : Function.Injective (gridPoint swap) := by
  cases swap
  · exact intPoint_injective
  · intro u v h
    exact Prod.swap_injective (intPoint_injective h)

private theorem gridPoint_sub (swap : Bool) (u v : ℤ × ℤ) :
    gridPoint swap (u - v) = gridPoint swap u - gridPoint swap v := by
  cases swap
  · exact intPoint_sub u v
  · exact intPoint_sub u.swap v.swap

private def Separated {t : ℕ} (r c : Fin t → ℝ²) : Prop :=
  ∀ i j i' j' (v : ℤ × ℤ), r i + c j - (r i' + c j') = intPoint v →
    i = i' ∧ j = j'

private noncomputable def tagged {t : ℕ} (r : Fin t → ℝ²) (swap : Bool)
    (A : Finset (ℤ × ℤ)) : Finset ℝ² := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  exact (univ.product A).image (fun u => r u.1 + gridPoint swap u.2)

private theorem tagged_card_le {t : ℕ} (r : Fin t → ℝ²) (swap : Bool)
    (A : Finset (ℤ × ℤ)) : (tagged r swap A).card ≤ t * A.card := by
  let : DecidableEq ℝ² := Classical.decEq _
  exact Finset.card_image_le.trans_eq (by
    change (Finset.univ ×ˢ A).card = _
    rw [Finset.card_product]
    simp)

private theorem taggedMatches {t : ℕ} (r c : Fin t → ℝ²) (hsep : Separated r c)
    (swap : Bool) (A B : Finset (ℤ × ℤ)) (p : ℝ²) (i j : Fin t) (x y : ℕ)
    (hp : p + p = r i + c j + gridPoint swap (x, y)) :
    (matched (tagged r swap A) (tagged c swap B) p).card =
      (midpointMatches A B x y).card := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  let f (a : ℤ × ℤ) := r i + gridPoint swap a
  have hf : Function.Injective f := fun _ _ h =>
    gridPoint_injective swap (add_left_cancel h)
  have mem_tag {s : Fin t → ℝ²} {D : Finset (ℤ × ℤ)} {q : ℝ²} :
      q ∈ tagged s swap D ↔ ∃ i : Fin t, ∃ a ∈ D, s i + gridPoint swap a = q := by
    unfold tagged
    constructor
    · intro h
      obtain ⟨⟨i, a⟩, hia, rfl⟩ := Finset.mem_image.mp h
      exact ⟨i, a, (Finset.mem_product.mp hia).2, rfl⟩
    · rintro ⟨i, a, ha, rfl⟩
      exact Finset.mem_image.mpr ⟨(i, a),
        Finset.mem_product.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
  have hpair (a b : ℤ × ℤ) (i' j' : Fin t)
      (h : r i' + gridPoint swap a + (c j' + gridPoint swap b) = p + p) :
      i = i' ∧ j = j' ∧ b = ((x : ℤ) - a.1, (y : ℤ) - a.2) := by
    have htags : r i + c j - (r i' + c j') =
        gridPoint swap (a + b - ((x : ℤ), (y : ℤ))) := by
      rw [gridPoint_sub]
      have hadd : gridPoint swap (a + b) = gridPoint swap a + gridPoint swap b := by
        cases swap
        · exact intPoint_add _ _
        · exact intPoint_add a.swap b.swap
      rw [hadd]
      calc
        r i + c j - (r i' + c j') =
            (r i + c j + gridPoint swap ((x : ℤ), (y : ℤ))) -
            (r i' + gridPoint swap a + (c j' + gridPoint swap b)) +
            (gridPoint swap a + gridPoint swap b - gridPoint swap ((x : ℤ), (y : ℤ))) := by
          abel
        _ = _ := by rw [← hp, h]; abel
    have he : i = i' ∧ j = j' := hsep _ _ _ _ _ htags
    refine ⟨he.1, he.2, gridPoint_injective swap ?_⟩
    rw [show ((x : ℤ) - a.1, (y : ℤ) - a.2) = ((x : ℤ), (y : ℤ)) - a from rfl,
      gridPoint_sub]
    rw [← he.1, ← he.2] at h
    calc
      gridPoint swap b =
          (r i + gridPoint swap a + (c j + gridPoint swap b)) -
          (r i + c j + gridPoint swap ((x : ℤ), (y : ℤ))) +
          (gridPoint swap ((x : ℤ), (y : ℤ)) - gridPoint swap a) := by abel
      _ = _ := by rw [h, ← hp]; abel
  have heq : matched (tagged r swap A) (tagged c swap B) p =
      (midpointMatches A B x y).image f := by
    ext q
    constructor
    · intro h
      have hm : q ∈ tagged r swap A ∧ p + p - q ∈ tagged c swap B :=
        Finset.mem_filter.mp h
      obtain ⟨i', a, ha, rfl⟩ := mem_tag.mp hm.1
      obtain ⟨j', b, hb, he⟩ := mem_tag.mp hm.2
      have ht := hpair a b i' j' (by rw [he]; abel)
      refine Finset.mem_image.mpr ⟨a, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨ha, ht.2.2 ▸ hb⟩
      · exact ht.1 ▸ rfl
    · intro h
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      have hm := Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨mem_tag.mpr ⟨i, a, hm.1, rfl⟩, ?_⟩
      refine mem_tag.mpr ⟨j, ((x : ℤ) - a.1, (y : ℤ) - a.2), hm.2, ?_⟩
      change c j + gridPoint swap (((x : ℤ), (y : ℤ)) - a) = _
      rw [gridPoint_sub, hp]
      dsimp [f]
      abel
  rw [heq, Finset.card_image_of_injective _ hf]

private theorem skewLeft_card_le {L : ℕ} (hL : 0 < L) :
    (skewLeft L).card ≤ 9 * L ^ 2 := by
  change ((Icc (-(4 * (L : ℤ))) (4 * (L : ℤ))) ×ˢ (Ico 0 (L : ℤ))).card ≤ _
  rw [Finset.card_product, Int.card_Icc, Int.card_Ico]
  have hLz : (0 : ℤ) ≤ L := by positivity
  have h1 : (4 * (L : ℤ) + 1 - -(4 * (L : ℤ))).toNat ≤ 9 * L := by omega
  have h2 : ((L : ℤ) - 0).toNat = L := by omega
  rw [h2]
  calc
    _ ≤ (9 * L) * L := Nat.mul_le_mul_right _ h1
    _ = _ := by ring

private theorem skewRight_card_le {L : ℕ} (hL : 0 < L) {k : ℤ}
    (hk : |k| ≤ (L : ℤ)) : (skewRight L k).card ≤ 16 * L ^ 2 := by
  have hLz : 0 < (L : ℤ) := by exact_mod_cast hL
  unfold skewRight
  apply Finset.card_biUnion_le.trans
  have hsum : (∑ h ∈ Icc (1 - (L : ℤ)) ((L : ℤ) - 1),
      ((Icc (-(6 * (L : ℤ))) (k * h / (L : ℤ))).image fun j => (j, h)).card) ≤
      (Icc (1 - (L : ℤ)) ((L : ℤ) - 1)).card * (8 * L) := by
    calc
      _ ≤ ∑ _h ∈ Icc (1 - (L : ℤ)) ((L : ℤ) - 1), 8 * L := by
        apply Finset.sum_le_sum
        intro h hh
        apply Finset.card_image_le.trans
        rw [Int.card_Icc]
        have habs : |h| ≤ (L : ℤ) := abs_le.mpr (by
          have := Finset.mem_Icc.mp hh
          omega)
        have hmul : k * h ≤ (L : ℤ) * L :=
          (le_abs_self _).trans (by
            rw [abs_mul]
            exact mul_le_mul hk habs (abs_nonneg _) hLz.le)
        have hdiv := Int.ediv_le_of_le_mul hLz hmul
        omega
      _ = _ := by simp
  apply hsum.trans
  have hc : (Icc (1 - (L : ℤ)) ((L : ℤ) - 1)).card ≤ 2 * L := by
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ (2 * L) * (8 * L) := Nat.mul_le_mul_right _ hc
    _ = _ := by ring

private theorem extend_skew {t L : ℕ} (hL : 0 < L) (r c : Fin t → ℝ²)
    (hsep : Separated r c) (swap : Bool) (k : ℤ) (hk : |k| ≤ (L : ℤ))
    (P : Finset ℝ²) :
    ∃ Q : Finset ℝ², P ⊆ Q ∧ Q.card ≤ P.card + 25 * t * L ^ 2 ∧
      ∃ C : ℤ, ∀ p ∈ P, ∀ (i j : Fin t) (x y : Fin L),
        p + p = r i + c j + gridPoint swap (x.val, y.val) →
        (distinctDistancesFrom Q p : ℤ) =
          distinctDistancesFrom P p + C + (L : ℤ) * x.val - k * y.val := by
  let A := tagged r swap (skewLeft L)
  let B := tagged c swap (skewRight L k)
  obtain ⟨Q, hPQ, hcard, hd⟩ := extend_by_midpoints P A B
  have hAc : A.card ≤ t * (9 * L ^ 2) :=
    (tagged_card_le _ _ _).trans (Nat.mul_le_mul_left _ (skewLeft_card_le hL))
  have hBc : B.card ≤ t * (16 * L ^ 2) :=
    (tagged_card_le _ _ _).trans (Nat.mul_le_mul_left _ (skewRight_card_le hL hk))
  refine ⟨Q, hPQ, hcard.trans ?_, (A.card : ℤ) + B.card -
    (4 * (L : ℤ) ^ 2 + L + rowSum L k 0), ?_⟩
  · calc
      P.card + A.card + B.card ≤ P.card + t * (9 * L ^ 2) + t * (16 * L ^ 2) := by omega
      _ = _ := by ring
  · intro p hp i j x y he
    rw [hd p hp, taggedMatches r c hsep swap _ _ p i j x.val y.val he,
      midpointMatches_card x.isLt y.isLt hk]
    ring

private theorem extend_affine {t L : ℕ} (hL : 0 < L) (r c : Fin t → ℝ²)
    (hsep : Separated r c) (a b : ℤ) (ha : 0 ≤ a ∧ a ≤ L)
    (hb : (L : ℤ) ≤ b ∧ b ≤ 2 * (L : ℤ)) (P : Finset ℝ²) :
    ∃ Q : Finset ℝ², P ⊆ Q ∧ Q.card ≤ P.card + 50 * t * L ^ 2 ∧
      ∃ C : ℤ, ∀ p ∈ P, ∀ (i j : Fin t) (x y : Fin L),
        p + p = r i + c j + intPoint (x.val, y.val) →
        (distinctDistancesFrom Q p : ℤ) =
          distinctDistancesFrom P p + C + a * x.val + b * y.val := by
  have hk₁ : |(L : ℤ) - b| ≤ (L : ℤ) := abs_le.mpr (by omega)
  have hk₂ : |(L : ℤ) - a| ≤ (L : ℤ) := abs_le.mpr (by omega)
  obtain ⟨P₁, hP₁, hC₁, C₁, h₁⟩ := extend_skew hL r c hsep false _ hk₁ P
  obtain ⟨P₂, hP₂, hC₂, C₂, h₂⟩ := extend_skew hL r c hsep true _ hk₂ P₁
  refine ⟨P₂, hP₁.trans hP₂, ?_, C₁ + C₂, ?_⟩
  · calc
      P₂.card ≤ P₁.card + 25 * t * L ^ 2 := hC₂
      _ ≤ P.card + 25 * t * L ^ 2 + 25 * t * L ^ 2 := Nat.add_le_add_right hC₁ _
      _ = _ := by ring
  · intro p hp i j x y he
    rw [h₂ p (hP₁ hp) i j y x he, h₁ p hp i j x y he]
    ring

private noncomputable def diversity (P : Finset ℝ²) : ℕ :=
  (P.image (distinctDistancesFrom P)).card

private theorem diversity_le (P : Finset ℝ²) : diversity P ≤ P.card :=
  Finset.card_image_le

private theorem diversity_le_max {n : ℕ} (P : Finset ℝ²) (hP : P.card = n) :
    diversity P ≤ maximalDistinctDistancesFrom n := by
  unfold maximalDistinctDistancesFrom
  apply le_csSup
  · refine ⟨n, ?_⟩
    rintro _ ⟨A, hA, rfl⟩
    exact (diversity_le A).trans_eq hA
  · exact ⟨P, hP, rfl⟩

private theorem max_le (n : ℕ) : maximalDistinctDistancesFrom n ≤ n := by
  unfold maximalDistinctDistancesFrom
  apply csSup_le'
  rintro _ ⟨P, hP, rfl⟩
  exact (diversity_le P).trans_eq hP

private theorem of_witnesses
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∃ P : Finset ℝ², P.card = n ∧ (1 - ε) * n ≤ (diversity P : ℝ)) :
    type_of% @Erdos653.erdos_653 := by
  let f (n : ℕ) : ℝ := (maximalDistinctDistancesFrom n : ℝ) / n
  have hf : Tendsto f atTop (𝓝 (1 : ℝ)) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [h ((1 - a) / 2) (by linarith), eventually_gt_atTop (0 : ℕ)] with n hn hn0
      obtain ⟨P, hP, hdiv⟩ := hn
      have hmax : (diversity P : ℝ) ≤ (maximalDistinctDistancesFrom n : ℝ) := by
        exact_mod_cast diversity_le_max P hP
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      exact (show a < 1 - (1 - a) / 2 by linarith).trans_le
        ((le_div_iff₀ hnR).2 (hdiv.trans hmax))
    · intro a ha
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn0
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have hmax : (maximalDistinctDistancesFrom n : ℝ) ≤ n := by exact_mod_cast max_le n
      exact ((div_le_iff₀ hnR).2 (by simpa only [one_mul] using hmax)).trans_lt ha
  refine ⟨fun n => 1 - f n, ?_, ?_⟩
  · apply (Asymptotics.isLittleO_one_iff ℝ).2
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hf
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn0
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
    change (1 - (1 - (maximalDistinctDistancesFrom n : ℝ) / n)) * n ≤ _
    rw [sub_sub_cancel, div_mul_cancel₀ _ hnR]

private def projection (a b : ℝ) (p : ℝ²) : ℝ := a * p 0 + b * p 1

private noncomputable def linePoint (a b T s : ℝ) : ℝ² :=
  planePoint (a * (s / (a ^ 2 + b ^ 2)) - b * T) (b * (s / (a ^ 2 + b ^ 2)) + a * T)

private theorem sqDist_line (a b T s : ℝ) (p : ℝ²) (h : 0 < a ^ 2 + b ^ 2) :
    (a ^ 2 + b ^ 2) * dist (linePoint a b T s) p ^ 2 =
      (s - projection a b p) ^ 2 + ((a ^ 2 + b ^ 2) * T + b * p 0 - a * p 1) ^ 2 := by
  rw [sqDist_coords]
  simp only [linePoint, planePoint_zero, planePoint_one, projection]
  field_simp [ne_of_gt h]
  ring

private theorem dist_line_eq (a b T s u : ℝ) (p : ℝ²) (h : 0 < a ^ 2 + b ^ 2) :
    dist (linePoint a b T s) p = dist (linePoint a b T u) p ↔
      s = u ∨ s + u = 2 * projection a b p := by
  have hsq₁ := sqDist_line a b T s p h
  have hsq₂ := sqDist_line a b T u p h
  let e := projection a b p
  change _ ↔ s = u ∨ s + u = 2 * e
  constructor
  · intro he
    rw [he, hsq₂] at hsq₁
    have hs : (s - e) ^ 2 = (u - e) ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
    · left; linarith
    · right; linarith
  · intro he
    have hs : (s - e) ^ 2 = (u - e) ^ 2 := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mpr
      rcases he with he | he
      · left; linarith
      · right; linarith
    have hd : dist (linePoint a b T s) p ^ 2 = dist (linePoint a b T u) p ^ 2 := by
      apply mul_left_cancel₀ h.ne'
      rw [hsq₁, hsq₂, hs]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hd with hh | hh
    · exact hh
    · linarith [dist_nonneg (x := linePoint a b T s) (y := p),
        dist_nonneg (x := linePoint a b T u) (y := p)]

private theorem dist_line_far (P : Finset ℝ²) (a b : ℝ) (h : 0 < a ^ 2 + b ^ 2) :
    ∃ T : ℝ, ∀ p ∈ P, ∀ q ∈ P, ∀ s : ℝ, dist q p < dist (linePoint a b T s) p := by
  classical
  have hf : ∀ᶠ T : ℝ in atTop, ∀ p ∈ P, ∀ q ∈ P, ∀ s : ℝ,
      dist q p < dist (linePoint a b T s) p := by
    apply (eventually_all_finset _).mpr
    intro p _
    apply (eventually_all_finset _).mpr
    intro q _
    filter_upwards [eventually_gt_atTop
      ((1 + (a ^ 2 + b ^ 2) * dist q p ^ 2 - (b * p 0 - a * p 1)) / (a ^ 2 + b ^ 2))] with T hT
    intro s
    have hbound := (div_lt_iff₀ h).mp hT
    let U := (a ^ 2 + b ^ 2) * T + b * p 0 - a * p 1
    have hU : 1 + (a ^ 2 + b ^ 2) * dist q p ^ 2 < U := by dsimp [U]; linarith
    have hnon : 0 ≤ (a ^ 2 + b ^ 2) * dist q p ^ 2 := by positivity
    have hU₁ : 1 ≤ U := by linarith
    have hU₀ : 0 ≤ U := by linarith
    have hU₂ : U ≤ U ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hU₁) hU₀]
    have he := sqDist_line a b T s p h
    change _ = (s - projection a b p) ^ 2 + U ^ 2 at he
    have hless : (a ^ 2 + b ^ 2) * dist q p ^ 2 <
        (a ^ 2 + b ^ 2) * dist (linePoint a b T s) p ^ 2 := by
      linarith [sq_nonneg (s - projection a b p)]
    have hsq := lt_of_mul_lt_mul_left hless h.le
    by_contra! hn
    exact (not_le_of_gt hsq) (by gcongr)
  exact hf.exists

private theorem extend_by_line (P : Finset ℝ²) (A B : Finset ℝ) (a b : ℝ) (h : 0 < a ^ 2 + b ^ 2)
    (hA : ∀ p ∈ P, ∀ s ∈ A, projection a b p < s) (hB : ∀ p ∈ P, ∀ s ∈ B, s < projection a b p) :
    ∃ Q : Finset ℝ², P ⊆ Q ∧ Q.card ≤ P.card + A.card + B.card ∧
      ∀ p ∈ P, (distinctDistancesFrom Q p : ℤ) =
        distinctDistancesFrom P p + A.card + B.card -
          (A.filter fun s => 2 * projection a b p - s ∈ B).card := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  obtain ⟨T, hT⟩ := dist_line_far P a b h
  let F := linePoint a b T
  let A' := A.image F
  let B' := B.image F
  let Q := (P ∪ A') ∪ B'
  have hPQ' : P ⊆ P ∪ A' := Finset.subset_union_left
  refine ⟨Q, hPQ'.trans Finset.subset_union_left, ?_, ?_⟩
  · calc
      Q.card ≤ (P ∪ A').card + B'.card := card_union_le _ _
      _ ≤ P.card + A'.card + B'.card := Nat.add_le_add_right (card_union_le _ _) _
      _ ≤ _ := by gcongr <;> exact card_image_le
  · intro p hp
    let f (s : ℝ) := dist (F s) p
    let D := (P.erase p).image (fun q => dist q p)
    let DA := A.image f
    let DB := B.image f
    have hpA : p ∉ A' := by
      intro hh
      obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hh
      exact (lt_irrefl _) (by simpa only [← he] using hT p hp p hp s)
    have hpB : p ∉ B' := by
      intro hh
      obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hh
      exact (lt_irrefl _) (by simpa only [← he] using hT p hp p hp s)
    have hErase : Q.erase p = (P.erase p ∪ A') ∪ B' := by
      change ((P ∪ A') ∪ B').erase p = _
      rw [erase_union_distrib, erase_union_distrib, erase_eq_of_notMem hpA, erase_eq_of_notMem hpB]
    have hpalette : (Q.erase p).image (fun q => dist q p) = D ∪ (DA ∪ DB) := by
      rw [hErase, Finset.image_union, Finset.image_union, Finset.union_assoc]
      have hDA : A'.image (fun q => dist q p) = DA := Finset.image_image
      have hDB : B'.image (fun q => dist q p) = DB := Finset.image_image
      rw [hDA, hDB]
    have hdisj : Disjoint D (DA ∪ DB) := by
      apply Finset.disjoint_left.mpr
      intro d hd hnew
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
      rcases Finset.mem_union.mp hnew with hnew | hnew
      · obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hnew
        exact (hT p hp q (Finset.mem_erase.mp hq).2 s).ne he.symm
      · obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hnew
        exact (hT p hp q (Finset.mem_erase.mp hq).2 s).ne he.symm
    have hfA : Set.InjOn f A := by
      intro s hs u hu he
      exact ((dist_line_eq a b T s u p h).mp he).elim id (fun hbad =>
        by linarith only [hbad, hA p hp s hs, hA p hp u hu])
    have hfB : Set.InjOn f B := by
      intro s hs u hu he
      exact ((dist_line_eq a b T s u p h).mp he).elim id (fun hbad =>
        by linarith only [hbad, hB p hp s hs, hB p hp u hu])
    let M := A.filter fun s => 2 * projection a b p - s ∈ B
    have hM : DA ∩ DB = M.image f := by
      ext d
      constructor
      · intro hd
        obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hd
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hb
        have hu' : u = 2 * projection a b p - s := by
          rcases (dist_line_eq a b T s u p h).mp he.symm with he | he
          · linarith only [hA p hp s hs, hB p hp u hu, he]
          · linarith
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hs, hu' ▸ hu⟩)
      · intro hd
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
        obtain ⟨ha, hb⟩ := Finset.mem_filter.mp hs
        exact Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image.mpr
          ⟨_, hb, (dist_line_eq a b T _ _ p h).mpr (Or.inr (by ring))⟩⟩
    have hcard := Finset.card_union_add_card_inter DA DB
    rw [hM, Finset.card_image_of_injOn (hfA.mono (by exact Finset.filter_subset _ _)),
      show DA.card = A.card from Finset.card_image_of_injOn hfA,
      show DB.card = B.card from Finset.card_image_of_injOn hfB] at hcard
    change (((Q.erase p).image (fun q => dist q p)).card : ℤ) =
      D.card + A.card + B.card - M.card
    rw [hpalette, Finset.card_union_of_disjoint hdisj]
    omega

private theorem extend_dictionary {C : Type*} [Fintype C] {d H : ℕ} (P : Finset ℝ²)
    (a b : ℝ) (hab : 0 < a ^ 2 + b ^ 2) (base : C → ℝ)
    (hbase : Function.Injective (fun u : C × Fin d => base u.1 + u.2.val))
    (q : C → Fin d → ℕ) (hq : ∀ c j, q c j ≤ H) :
    ∃ Q : Finset ℝ², P ⊆ Q ∧
      Q.card ≤ P.card + H * (2 ^ d * d + Fintype.card C) ∧
      ∃ shift : ℤ, ∀ p ∈ P, ∀ c j, 2 * projection a b p = base c + j.val →
        (distinctDistancesFrom Q p : ℤ) = distinctDistancesFrom P p + shift - q c j := by
  classical
  let mask (h : Fin H) (c : C) := univ.filter fun j : Fin d => h.val < q c j
  let I := Fin H × Finset (Fin d)
  let key (i : I) : ℕ := (Fintype.equivFin I i).val
  have hkey : Function.Injective key :=
    fun _ _ h => (Fintype.equivFin I).injective (Fin.ext h)
  obtain ⟨K₀, hK₀⟩ := (Set.finite_range (fun c => |base c|)).bddAbove
  let K := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  have hbound (c : C) : |base c| ≤ K :=
    (hK₀ (Set.mem_range_self c)).trans (le_max_left _ _)
  let R : ℝ := 4 * K + 4 * d + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨P₀, hP₀⟩ := ((P.image (fun p => |projection a b p|)).finite_toSet).bddAbove
  let T : ℝ := max P₀ 0 + K + 1
  have hT (p : ℝ²) (hp : p ∈ P) : |projection a b p| + K < T := by
    have hP := hP₀ (Finset.mem_image_of_mem _ hp)
    dsimp [T]
    linarith [le_max_left P₀ 0]
  let left (i : I × Fin d) : ℝ := T + R * key i.1 + i.2.val
  let right (u : C × Fin H) : ℝ := -T - R * key (u.2, mask u.2 u.1) + base u.1
  let Aidx : Finset (I × Fin d) := univ.filter fun i => i.2 ∈ i.1.2
  let A := Aidx.image left
  let B := univ.image right
  have hA p (hp : p ∈ P) s (hs : s ∈ A) : projection a b p < s := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    have h := hT p hp
    have hnon : 0 ≤ R * (key i.1 : ℝ) + i.2.val := by positivity
    dsimp [left]
    linarith [le_abs_self (projection a b p)]
  have hB p (hp : p ∈ P) s (hs : s ∈ B) : s < projection a b p := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    have h := hT p hp
    have hnon : 0 ≤ R * (key (u.2, mask u.2 u.1) : ℝ) := by positivity
    have hbu := (abs_le.mp (hbound u.1)).2
    dsimp [right]
    linarith [neg_abs_le (projection a b p)]
  obtain ⟨Q, hPQ, hcard, hQ⟩ := extend_by_line P A B a b hab hA hB
  refine ⟨Q, hPQ, hcard.trans ?_, (A.card : ℤ) + B.card, ?_⟩
  · have hAc : A.card ≤ H * 2 ^ d * d :=
      Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq
        (by simp [I, Fintype.card_prod, Fintype.card_finset]))
    have hBc : B.card ≤ Fintype.card C * H :=
      Finset.card_image_le.trans_eq (by simp [Fintype.card_prod])
    calc
      _ ≤ P.card + (H * 2 ^ d * d) + (Fintype.card C * H) := by omega
      _ = _ := by ring
  · intro p hp c j hproj
    let chosen (h : Fin H) := left ((h, mask h c), j)
    let active := (univ : Finset (Fin H)).filter fun h => h.val < q c j
    have hsep (i k : I) {v w : ℝ} (hv : |v| ≤ K + d) (hw : |w| ≤ K + d)
        (he : R * key i + v = R * key k + w) : i = k := by
      have hdiff : |R * ((key i : ℝ) - key k)| ≤ 2 * (K + d) := by
        rw [show R * ((key i : ℝ) - key k) = w - v by linarith]
        exact (abs_sub_le w 0 v).trans (by
          rw [sub_zero, zero_sub, abs_neg]
          linarith)
      apply hkey
      by_contra hne
      have hne' : (key i : ℝ) - key k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
      have hlarge : 1 ≤ |(key i : ℝ) - key k| := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hh : (key i : ℝ) + 1 ≤ key k := by exact_mod_cast Nat.succ_le_of_lt hlt
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have hh : (key k : ℝ) + 1 ≤ key i := by exact_mod_cast Nat.succ_le_of_lt hgt
          rw [abs_of_nonneg (by linarith)]
          linarith
      have hmul := mul_le_mul_of_nonneg_left hlarge hR.le
      rw [abs_mul, abs_of_pos hR] at hdiff
      dsimp [R] at hmul hdiff
      linarith
    have hchosen : Function.Injective chosen := by
      intro h k he
      have he' : R * (key (h, mask h c) : ℝ) = R * key (k, mask k c) := by
        dsimp [chosen, left] at he
        linarith
      have hh := hkey (by exact_mod_cast mul_left_cancel₀ hR.ne' he')
      exact congrArg Prod.fst hh
    let M := A.filter fun s => 2 * projection a b p - s ∈ B
    have hM : M = active.image chosen := by
      ext s
      constructor
      · intro hs
        obtain ⟨hsA, hsB⟩ := Finset.mem_filter.mp hs
        obtain ⟨⟨i, v⟩, hi, rfl⟩ := Finset.mem_image.mp hsA
        obtain ⟨⟨c', h⟩, hh, hright⟩ := Finset.mem_image.mp hsB
        have he : R * key i + (base c' + v.val) =
            R * key (h, mask h c') + (base c + j.val) := by
          dsimp [left, right] at hright
          linarith
        have hlarge (e : C) (k : Fin d) : |base e + k.val| ≤ K + d := by
          apply (abs_add_le _ _).trans
          have hk : (k.val : ℝ) ≤ d := by exact_mod_cast k.isLt.le
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ k.val)]
          exact add_le_add (hbound e) hk
        have hik := hsep i (h, mask h c') (hlarge c' v) (hlarge c j) he
        rw [hik] at he hi
        have hcv : (c', v) = (c, j) := hbase (by
          change base c' + (v.val : ℝ) = base c + j.val
          linarith)
        have hc' := congrArg Prod.fst hcv
        have hv' := congrArg Prod.snd hcv
        dsimp at hc' hv'
        subst c'
        subst v
        have hj : j ∈ mask h c := (Finset.mem_filter.mp hi).2
        have hq' : h.val < q c j := (Finset.mem_filter.mp hj).2
        rw [hik]
        exact Finset.mem_image.mpr ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq'⟩, rfl⟩
      · intro hs
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hs
        have hq' : h.val < q c j := (Finset.mem_filter.mp hh).2
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_image.mpr
          exact ⟨((h, mask h c), j), Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq'⟩⟩, rfl⟩
        · refine Finset.mem_image.mpr ⟨(c, h), Finset.mem_univ _, ?_⟩
          dsimp [right, chosen, left]
          rw [hproj]
          ring
    have hactive : active.card = q c j := by
      let E : Fin (q c j) ↪ Fin H :=
        ⟨fun i => ⟨i.val, i.isLt.trans_le (hq c j)⟩, fun _ _ h =>
          Fin.ext (congrArg (fun a : Fin H => a.val) h)⟩
      have hmap : (univ : Finset (Fin (q c j))).map E = active := by
        ext h
        constructor
        · intro hh
          obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hh
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
        · intro hh
          exact Finset.mem_map.mpr ⟨⟨h.val, (Finset.mem_filter.mp hh).2⟩, Finset.mem_univ _, rfl⟩
      rw [← hmap]
      simp
    have hmc : M.card = q c j := by
      rw [hM, Finset.card_image_of_injective _ hchosen, hactive]
    exact (hQ p hp).trans (by change _ - (M.card : ℤ) = _; rw [hmc]; ring)

private theorem radix_injective {d : ℕ} {i i' : ℕ} {j j' : Fin d}
    (h : d * i + j.val = d * i' + j'.val) : i = i' ∧ j = j' := by
  have he : i = i' := by
    rcases lt_trichotomy i i' with hl | he | hg
    · have hlt := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hl)
      rw [Nat.mul_succ] at hlt
      have hj := j.isLt
      omega
    · exact he
    · have hlt := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hg)
      rw [Nat.mul_succ] at hlt
      have hj' := j'.isLt
      omega
  subst i'
  exact ⟨rfl, Fin.ext (Nat.add_left_cancel h)⟩

private theorem extend_labelled {ι : Type*} [Fintype ι] {N d H : ℕ} (hd : 0 < d) (P : Finset ℝ²)
    (a b : ℝ) (hab : 0 < a ^ 2 + b ^ 2) (base : ι → ℝ)
    (hb : ∀ i i' z : _, base i - base i' = (z : ℤ) → i = i')
    (q : ι → Fin N → ℕ) (hq : ∀ i w, q i w ≤ H) :
    ∃ Q : Finset ℝ², P ⊆ Q ∧
      Q.card ≤ P.card + H * (2 ^ d * d + Fintype.card ι * (N / d + 1)) ∧
      ∃ shift : ℤ, ∀ p ∈ P, ∀ i (w : Fin N), 2 * projection a b p = base i + w.val →
        (distinctDistancesFrom Q p : ℤ) = distinctDistancesFrom P p + shift - q i w := by
  let C := ι × Fin (N / d + 1)
  let chunk (u : C) : ℝ := base u.1 + (d * u.2.val : ℕ)
  have hinj : Function.Injective (fun u : C × Fin d => chunk u.1 + u.2.val) := by
    rintro ⟨⟨i, k⟩, j⟩ ⟨⟨i', k'⟩, j'⟩ he
    have hblock : i = i' := by
      apply hb i i' ((d : ℤ) * k'.val + j'.val - (d : ℤ) * k.val - j.val)
      dsimp [chunk] at he
      push_cast at he ⊢
      linarith
    subst i'
    have hr : (d : ℝ) * k.val + j.val = (d : ℝ) * k'.val + j'.val := by
      dsimp [chunk] at he
      push_cast at he
      linarith
    have hn : d * k.val + j.val = d * k'.val + j'.val := by exact_mod_cast hr
    obtain ⟨hk, hj⟩ := radix_injective hn
    exact Prod.ext (Prod.ext rfl (Fin.ext hk)) hj
  let q' (u : C) (j : Fin d) : ℕ :=
    if h : d * u.2.val + j.val < N then q u.1 ⟨_, h⟩ else 0
  have hq' (u : C) (j : Fin d) : q' u j ≤ H := by
    dsimp [q']
    split
    · exact hq _ _
    · exact Nat.zero_le _
  obtain ⟨Q, hPQ, hcard, s, hs⟩ := extend_dictionary P a b hab chunk hinj q' hq'
  refine ⟨Q, hPQ, ?_, s, ?_⟩
  · simpa [C, Fintype.card_prod] using hcard
  · intro p hp i w hw
    let k : Fin (N / d + 1) := ⟨w.val / d,
      Nat.lt_succ_of_le (Nat.div_le_div_right w.isLt.le)⟩
    let j : Fin d := ⟨w.val % d, Nat.mod_lt _ hd⟩
    have hkj : d * k.val + j.val = w.val := Nat.div_add_mod _ _
    have hkjR : (d * k.val : ℕ) + (j.val : ℝ) = w.val := by exact_mod_cast hkj
    have hlabel : 2 * projection a b p = chunk (i, k) + j.val := by
      dsimp [chunk]
      linarith
    have hval : q' (i, k) j = q i w := by
      dsimp [q']
      split
      · congr 1
        exact Fin.ext hkj
      · rename_i hn
        exact (hn (hkj ▸ w.isLt)).elim
    rw [hs p hp (i, k) j hlabel, hval]

private theorem row_budget (K : ℕ) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ L : ℕ in atTop,
      4 * (4 * L * (2 ^ d * d + K * (L / d + 1))) ≤ L ^ 2 := by
  let d := 64 * (K + 1)
  let J := 2 ^ d * d + K
  refine ⟨d, by simp [d], ?_⟩
  filter_upwards [eventually_ge_atTop (32 * J)] with L hL
  have hd : 32 * K ≤ d := by dsimp [d]; omega
  have h₁ : 32 * K * (L / d) ≤ L :=
    (Nat.mul_le_mul_right _ hd).trans (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _)
  have h₂ : 32 * (2 ^ d * d + K * (L / d + 1)) ≤ 2 * L := by
    calc
      _ = 32 * J + 32 * K * (L / d) := by unfold J; ring
      _ ≤ L + L := add_le_add hL h₁
      _ = _ := by ring
  calc
    _ = 16 * (2 ^ d * d + K * (L / d + 1)) * L := by ring
    _ ≤ L * L := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

private theorem individual_budget (K B : ℕ) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ L : ℕ in atTop,
      4 * (B * (2 ^ d * d + K * (L ^ 2 / d + 1))) ≤ L ^ 2 := by
  let d := 8 * (B + 1) * (K + 1)
  let J := 2 ^ d * d + K
  refine ⟨d, by simp [d], ?_⟩
  filter_upwards [eventually_ge_atTop (8 * B * J), eventually_gt_atTop 0] with L hL hL0
  have hd : 8 * B * K ≤ d := by dsimp [d]; nlinarith
  have h₁ : 8 * B * K * (L ^ 2 / d) ≤ L ^ 2 :=
    (Nat.mul_le_mul_right _ hd).trans (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _)
  have h₂ : 8 * B * J ≤ L ^ 2 := hL.trans (by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ hL0)
  have h₃ : 8 * (B * (2 ^ d * d + K * (L ^ 2 / d + 1))) ≤ 2 * L ^ 2 := by
    calc
      _ = 8 * B * J + 8 * B * K * (L ^ 2 / d) := by unfold J; ring
      _ ≤ L ^ 2 + L ^ 2 := add_le_add h₂ h₁
      _ = _ := by ring
  omega

private theorem diversity_le_of_image {ι : Type*} (S : Finset ι) (P : Finset ℝ²)
    (f : ι → ℝ²) (hf : ∀ i ∈ S, f i ∈ P)
    (hi : Set.InjOn (fun i => distinctDistancesFrom P (f i)) S) :
    S.card ≤ diversity P := by
  classical
  rw [← Finset.card_image_of_injOn hi]
  apply Finset.card_le_card
  intro n hn
  obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hn
  exact Finset.mem_image_of_mem _ (hf i hiS)

private theorem extend_one (P : Finset ℝ²) :
    ∃ Q : Finset ℝ², Q.card = P.card + 1 ∧ diversity P ≤ diversity Q := by
  classical
  by_cases hp : P.Nonempty
  · obtain ⟨Q, hPQ, hcard, hd⟩ := extend_by_midpoints P ({0} : Finset ℝ²) ∅
    have hdist p (h : p ∈ P) :
        (distinctDistancesFrom Q p : ℤ) = distinctDistancesFrom P p + 1 := by
      simpa [matched] using hd p h
    have hne : P ≠ Q := by
      intro he
      obtain ⟨p, hp⟩ := hp
      have h := hdist p hp
      rw [← he] at h
      omega
    have hlt := Finset.card_lt_card (ssubset_of_subset_of_ne hPQ hne)
    refine ⟨Q, ?_, ?_⟩
    · simp only [Finset.card_singleton, Finset.card_empty, Nat.add_zero] at hcard
      omega
    · let old := P.image (distinctDistancesFrom P)
      have hmap : (old.image (fun x => x + 1)).card = old.card :=
        Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)
      change old.card ≤ diversity Q
      rw [← hmap]
      apply Finset.card_le_card
      intro n hn
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨p, hPQ hp, by have := hdist p hp; omega⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hp]
    exact ⟨{0}, by simp, by simp [diversity]⟩

private theorem pad (P : Finset ℝ²) (n : ℕ) (h : P.card ≤ n) :
    ∃ Q : Finset ℝ², Q.card = n ∧ diversity P ≤ diversity Q := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction m with
  | zero => exact ⟨P, by simp, le_rfl⟩
  | succ m ih =>
    obtain ⟨Q, hQ, hd⟩ := ih
    obtain ⟨R, hR, hd'⟩ := extend_one Q
    exact ⟨R, by omega, hd.trans hd'⟩

private theorem eventual_of_squares {A : ℕ} (hA : 0 < A) {b c : ℝ}
    (hc : 0 < c) (hgap : c * A < b)
    (h : ∀ᶠ L : ℕ in atTop, ∃ P : Finset ℝ², P.card ≤ A * L ^ 2 ∧
      b * (L : ℝ) ^ 2 ≤ (diversity P : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∃ P : Finset ℝ², P.card = n ∧ c * n ≤ (diversity P : ℝ) := by
  obtain ⟨L₀, h₀⟩ := eventually_atTop.mp h
  let e := b - c * A
  have he : 0 < e := sub_pos.mpr hgap
  obtain ⟨M, hM⟩ := exists_nat_gt (3 * (c * A) / e)
  have hMmul : 3 * (c * A) < (M : ℝ) * e := (div_lt_iff₀ he).1 hM
  let N : ℕ := max 1 (max L₀ M)
  apply eventually_atTop.mpr
  refine ⟨A * N ^ 2, ?_⟩
  intro n hn
  let L := (n / A).sqrt
  have hNL : N ≤ L := by
    apply Nat.le_sqrt.mpr
    apply (Nat.le_div_iff_mul_le hA).mpr
    simpa only [pow_two, Nat.mul_comm A (N * N)] using hn
  have hlo : A * L ^ 2 ≤ n := by
    rw [Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le hA).mp (Nat.sqrt_le' _)
  have hhi : n < A * (L + 1) ^ 2 := by
    rw [Nat.mul_comm]
    exact (Nat.div_lt_iff_lt_mul hA).mp (Nat.lt_succ_sqrt' _)
  have hL₀ : L₀ ≤ L := (le_max_left L₀ M).trans ((le_max_right 1 _).trans hNL)
  have hM₀ : M ≤ L := (le_max_right L₀ M).trans ((le_max_right 1 _).trans hNL)
  have hL₁ : (1 : ℝ) ≤ L := by exact_mod_cast (le_max_left 1 (max L₀ M)).trans hNL
  have hM₀r : (M : ℝ) ≤ L := by exact_mod_cast hM₀
  have hLpos : 0 ≤ (L : ℝ) := by positivity
  have hd : 3 * (c * A) ≤ (L : ℝ) * e :=
    hMmul.le.trans (mul_le_mul_of_nonneg_right hM₀r he.le)
  have hAl : 0 ≤ c * (A : ℝ) := mul_nonneg hc.le (by positivity)
  have hsq : ((L : ℝ) + 1) ^ 2 ≤ (L : ℝ) ^ 2 + 3 * L := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hAl
  have hrem := mul_le_mul_of_nonneg_right hd hLpos
  obtain ⟨P, hP, hy⟩ := h₀ L hL₀
  obtain ⟨Q, hQ, hdQ⟩ := pad P n (hP.trans hlo)
  refine ⟨Q, hQ, ?_⟩
  have hhir : (n : ℝ) ≤ (A : ℝ) * ((L : ℝ) + 1) ^ 2 := by exact_mod_cast hhi.le
  have hy' : (diversity P : ℝ) ≤ (diversity Q : ℝ) := by exact_mod_cast hdQ
  calc
    c * (n : ℝ) ≤ c * ((A : ℝ) * ((L : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hhir hc.le
    _ ≤ b * (L : ℝ) ^ 2 := by dsimp [e] at hrem; nlinarith only [hmul, hrem]
    _ ≤ _ := hy.trans hy'

private abbrev Block (t : ℕ) := Fin t × Fin t
private abbrev PinIndex (t L : ℕ) := Block t × Fin L × Fin L

private noncomputable def pin {t L : ℕ} (r c : Fin t → ℝ²) (u : PinIndex t L) : ℝ² :=
  (1 / 2 : ℝ) • (r u.1.1 + c u.1.2 + intPoint (u.2.1.val, u.2.2.val))

private theorem twice_pin {t L : ℕ} (r c : Fin t → ℝ²) (u : PinIndex t L) :
    pin r c u + pin r c u = r u.1.1 + c u.1.2 + intPoint (u.2.1.val, u.2.2.val) := by
  unfold pin
  rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]

private noncomputable def configuration {t : ℕ} (L : ℕ) (r c : Fin t → ℝ²) : Finset ℝ² :=
  univ.image (pin (L := L) r c)

private theorem mem_configuration {t L : ℕ} (r c : Fin t → ℝ²) (u : PinIndex t L) :
    pin r c u ∈ configuration L r c := Finset.mem_image_of_mem _ (Finset.mem_univ _)

private theorem configuration_card_le {t : ℕ} (L : ℕ) (r c : Fin t → ℝ²) :
    (configuration L r c).card ≤ t ^ 2 * L ^ 2 := by
  unfold configuration
  apply Finset.card_image_le.trans_eq
  simp [PinIndex, Block, Fintype.card_prod, pow_two]

private def tags {t : ℕ} (L : ℕ) (r c : Fin t → ℝ²) : Prop :=
  ∀ u v : Block t, u ≠ v → ∀ z : ℤ,
    let d := r u.1 + c u.2 - (r v.1 + c v.2)
    d 0 ≠ z ∧ d 1 ≠ z ∧ d 0 + (L : ℝ) * d 1 ≠ z

private theorem separated_of_tags {t L : ℕ} {r c : Fin t → ℝ²} (h : tags L r c) :
    Separated r c := by
  intro i j i' j' q hq
  have hh : (i, j) = (i', j') := by
    by_contra hn
    exact (h _ _ hn q.1).1 (congrArg (fun p : ℝ² => p 0) hq)
  exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩

-- Each strict row contributes a full row of blocks. The complementary row
-- contributes only its strict columns, giving the two digits of the degree.
private def strong {t : ℕ} (i : Fin t) : Finset (Fin t) :=
  (Ioi i.rev).erase i

private def high {t : ℕ} (u : Block t) : Finset (Block t) :=
  (strong u.1).product univ ∪ ({u.1.rev} : Finset (Fin t)).product (strong u.2)

private theorem mem_strong {t : ℕ} {i j : Fin t} :
    j ∈ strong i ↔ j ≠ i ∧ t - 1 < i.val + j.val := by
  rw [strong, mem_erase, mem_Ioi]
  simp only [Fin.lt_def, Fin.val_rev]
  omega

private theorem mem_high {t : ℕ} {u v : Block t} :
    v ∈ high u ↔ (v.1 ≠ u.1 ∧ t - 1 < u.1.val + v.1.val) ∨
      (u.1.val + v.1.val = t - 1 ∧ v.2 ≠ u.2 ∧ t - 1 < u.2.val + v.2.val) := by
  rw [high]
  rw [mem_union]
  change v ∈ (strong u.1 ×ˢ univ) ∨ v ∈ ({u.1.rev} ×ˢ strong u.2) ↔ _
  simp only [mem_product, mem_univ, and_true, mem_singleton, mem_strong]
  rw [show v.1 = u.1.rev ↔ u.1.val + v.1.val = t - 1 by
    rw [Fin.ext_iff, Fin.val_rev]
    omega]

private theorem card_strong {t : ℕ} (i : Fin t) :
    (strong i).card = i.val - (if t - 1 < 2 * i.val then 1 else 0) := by
  have h₀ : (Ioi i.rev).card = i.val := by
    simp only [Fin.card_Ioi, Fin.val_rev]
    omega
  have h₁ : i ∈ Ioi i.rev ↔ t - 1 < 2 * i.val := by
    simp only [mem_Ioi, Fin.lt_def, Fin.val_rev]
    omega
  by_cases h : i ∈ Ioi i.rev
  · rw [strong, card_erase_of_mem h, h₀, if_pos (h₁.mp h)]
  · rw [strong, erase_eq_of_notMem h, h₀, if_neg (mt h₁.mpr h), Nat.sub_zero]

private theorem card_high {t : ℕ} (u : Block t) :
    (high u).card = (strong u.1).card * t + (strong u.2).card := by
  have hdis : Disjoint ((strong u.1).product (univ : Finset (Fin t)))
      (({u.1.rev} : Finset (Fin t)).product (strong u.2)) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    have hrel := (mem_product.mp hv).1
    have heq := mem_singleton.mp (mem_product.mp hw).1
    rw [heq, strong, mem_erase, mem_Ioi] at hrel
    exact (lt_irrefl _ hrel.2)
  rw [high, card_union_of_disjoint hdis]
  simp

private def goodRows (m : ℕ) : Finset (Fin (2 * (m + 1))) :=
  univ.erase ⟨m + 1, by omega⟩

private def goodBlocks (m : ℕ) : Finset (Block (2 * (m + 1))) :=
  (goodRows m).product (goodRows m)

private theorem goodBlocks_card (m : ℕ) :
    (goodBlocks m).card = (2 * (m + 1) - 1) ^ 2 := by
  simp [goodBlocks, goodRows, card_erase_of_mem, pow_two]

private theorem strong_injOn (m : ℕ) :
    Set.InjOn (fun i => (strong i).card) (↑(goodRows m) : Set (Fin (2 * (m + 1)))) := by
  intro i hi j hj h
  have hmi : i.val ≠ m + 1 := by
    intro he
    exact (mem_erase.mp hi).1 (Fin.ext he)
  have hmj : j.val ≠ m + 1 := by
    intro he
    exact (mem_erase.mp hj).1 (Fin.ext he)
  apply Fin.ext
  change (strong i).card = (strong j).card at h
  rw [card_strong, card_strong] at h
  split at h <;> split at h <;> omega

private theorem high_injOn (m : ℕ) :
    Set.InjOn (fun u => (high u).card) (↑(goodBlocks m) : Set (Block (2 * (m + 1)))) := by
  intro u hu v hv h
  have hu₀ := mem_product.mp (show u ∈ goodBlocks m from hu)
  have hv₀ := mem_product.mp (show v ∈ goodBlocks m from hv)
  change (high u).card = (high v).card at h
  rw [card_high, card_high] at h
  have hl (i : Fin (2 * (m + 1))) : (strong i).card < 2 * (m + 1) :=
    (card_strong i).le.trans_lt ((Nat.sub_le ..).trans_lt i.isLt)
  have h₂ : (strong u.2).card = (strong v.2).card := by
    have := congrArg (fun n : ℕ => n % (2 * (m + 1))) h
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (hl _)] using this
  have h₁ : (strong u.1).card = (strong v.1).card := by
    rw [h₂] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel h)
  exact Prod.ext (strong_injOn m hu₀.1 hv₀.1 h₁) (strong_injOn m hu₀.2 hv₀.2 h₂)

private abbrev Label (t : ℕ) := Fin t ⊕ Fin t

private def mark {t : ℕ} (b : Block t) (k : Label t) : ℤ :=
  match k with
  | .inl i => if b.1 = i then 1 else 0
  | .inr j => if b.2 = j then 1 else 0

private def commonDen {t : ℕ} (p : Label t → ℕ) : ℕ := ∏ k, p k

private def cofactor {t : ℕ} (p : Label t → ℕ) (k : Label t) : ℕ :=
  ∏ i ∈ univ.erase k, p i

private def centerCoord {t : ℕ} (p : Label t → ℕ) (z : Label t → ℤ) (b : Block t) : ℤ :=
  ∑ k, mark b k * (cofactor p k : ℤ) * z k

private def shiftedCoord {t : ℕ} (p : Label t → ℕ) (z : Label t → ℤ)
    (u v : Block t) (a : ℤ) : ℤ :=
  centerCoord p z u - centerCoord p z v + (commonDen p : ℤ) * a

private def shiftedNorm {t : ℕ} (p : Label t → ℕ) (x y : Label t → ℤ)
    (u v : Block t) (a : ℤ × ℤ) : ℤ :=
  shiftedCoord p x u v a.1 ^ 2 + shiftedCoord p y u v a.2 ^ 2

private theorem commonDen_pos {t : ℕ} {p : Label t → ℕ} (hp : ∀ k, (p k).Prime) :
    0 < commonDen p :=
  prod_pos fun k _ => (hp k).pos

private theorem cofactor_zero {t : ℕ} (p : Label t → ℕ) {k j : Label t} (h : k ≠ j) :
    (cofactor p j : ZMod (p k)) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact dvd_prod_of_mem p (mem_erase.mpr ⟨h, mem_univ _⟩)

private theorem cofactor_ne_zero {t : ℕ} {p : Label t → ℕ} (hp : ∀ k, (p k).Prime)
    (hi : Function.Injective p) (k : Label t) : (cofactor p k : ZMod (p k)) ≠ 0 := by
  have : Fact (p k).Prime := ⟨hp k⟩
  rw [cofactor, Nat.cast_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [Ne, ZMod.natCast_eq_zero_iff, Nat.prime_dvd_prime_iff_eq (hp k) (hp j)]
  exact (mem_erase.mp hj).1 ∘ (fun h => (hi h).symm)

private theorem commonDen_zero {t : ℕ} (p : Label t → ℕ) (k : Label t) :
    (commonDen p : ZMod (p k)) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact dvd_prod_of_mem p (mem_univ k)

private theorem center_mod {t : ℕ} (p : Label t → ℕ) (z : Label t → ℤ)
    (u : Block t) (k : Label t) :
    (centerCoord p z u : ZMod (p k)) =
      (mark u k : ZMod (p k)) * (cofactor p k : ZMod (p k)) * (z k : ZMod (p k)) := by
  simp only [centerCoord, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply sum_eq_single k
  · intro j _ hj
    rw [cofactor_zero p hj.symm, mul_zero, zero_mul]
  · simp

private theorem shifted_mod {t : ℕ} (p : Label t → ℕ) (z : Label t → ℤ)
    (u v : Block t) (k : Label t) (a : ℤ) :
    (shiftedCoord p z u v a : ZMod (p k)) =
      ((mark u k : ZMod (p k)) - (mark v k : ZMod (p k))) *
        (cofactor p k : ZMod (p k)) * (z k : ZMod (p k)) := by
  simp only [shiftedCoord, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    commonDen_zero p k, zero_mul, add_zero, center_mod]
  ring

private theorem mark_sub_ne_zero {t : ℕ} (p : Label t → ℕ) (hp : ∀ k, (p k).Prime)
    {u v : Block t} {k : Label t} (h : mark u k ≠ mark v k) :
    (mark u k : ZMod (p k)) - (mark v k : ZMod (p k)) ≠ 0 := by
  have : Fact (p k).Prime := ⟨hp k⟩
  cases k with
  | inl i =>
    by_cases hu : u.1 = i <;> by_cases hv : v.1 = i <;> simp_all [mark]
  | inr i =>
    by_cases hu : u.2 = i <;> by_cases hv : v.2 = i <;> simp_all [mark]

-- The inert norm vanishes modulo a label prime exactly when the pin and
-- target agree about whether they carry the label.
private theorem norm_mod_iff {t : ℕ} {p : Label t → ℕ} {x y : Label t → ℤ}
    (hp : ∀ k, (p k).Prime ∧ p k % 4 = 3)
    (hi : Function.Injective p) (hy : ∀ k, ¬ (p k : ℤ) ∣ y k)
    (u v : Block t) (a : ℤ × ℤ) (k : Label t) :
    (shiftedNorm p x y u v a : ZMod (p k)) = 0 ↔ mark u k = mark v k := by
  have : Fact (p k).Prime := ⟨(hp k).1⟩
  simp only [shiftedNorm, Int.cast_add, Int.cast_pow, shifted_mod]
  constructor
  · intro h
    by_contra hn
    have hy' : (y k : ZMod (p k)) ≠ 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).not.mpr (hy k)
    have hy'' := mul_ne_zero
      (mul_ne_zero (mark_sub_ne_zero p (fun k => (hp k).1) hn)
        (cofactor_ne_zero (fun k => (hp k).1) hi k)) hy'
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy'' (eq_neg_of_add_eq_zero_left h) (hp k).2
  · intro h
    simp [h]

private theorem recover_label {t : ℕ} {u v w : Block t}
    (h : ∀ k, mark u k = mark v k ↔ mark u k = mark w k) : v = w := by
  apply Prod.ext
  · by_contra hn
    by_cases hv : u.1 = v.1
    · have hw : u.1 ≠ w.1 := fun he => hn (hv.symm.trans he)
      specialize h (.inl w.1)
      simp [mark, hw, hn] at h
    · specialize h (.inl v.1)
      simp [mark, hv, Ne.symm hn] at h
  · by_contra hn
    by_cases hv : u.2 = v.2
    · have hw : u.2 ≠ w.2 := fun he => hn (hv.symm.trans he)
      specialize h (.inr w.2)
      simp [mark, hw, hn] at h
    · specialize h (.inr v.2)
      simp [mark, hv, Ne.symm hn] at h

private theorem shiftedNorm_separates {t : ℕ} {p : Label t → ℕ} {x y : Label t → ℤ}
    (hp : ∀ k, (p k).Prime ∧ p k % 4 = 3)
    (hi : Function.Injective p) (hy : ∀ k, ¬ (p k : ℤ) ∣ y k)
    (u : Block t) {v w : Block t} {a b : ℤ × ℤ}
    (h : shiftedNorm p x y u v a = shiftedNorm p x y u w b) : v = w := by
  apply recover_label (u := u)
  intro k
  rw [← norm_mod_iff hp hi hy u v a k, ← norm_mod_iff hp hi hy u w b k, h]

private theorem exists_label_diff {t : ℕ} {u v : Block t} (h : u ≠ v) :
    ∃ k, mark u k ≠ mark v k := by
  by_contra! hn
  have h' := recover_label (u := u) (v := u) (w := v) (fun k => by rw [hn k])
  exact h h'

private theorem shifted_ne_zero {t : ℕ} {p : Label t → ℕ} {z : Label t → ℤ}
    (hp : ∀ k, (p k).Prime) (hi : Function.Injective p)
    (hz : ∀ k, ¬ (p k : ℤ) ∣ z k) {u v : Block t} (huv : u ≠ v) (a : ℤ) :
    shiftedCoord p z u v a ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_label_diff huv
  have : Fact (p k).Prime := ⟨hp k⟩
  intro he
  have hzmod : (z k : ZMod (p k)) ≠ 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).not.mpr (hz k)
  have hne := mul_ne_zero (mul_ne_zero (mark_sub_ne_zero p hp hk)
    (cofactor_ne_zero hp hi k)) hzmod
  apply hne
  rw [← shifted_mod p z u v k a, he, Int.cast_zero]

private theorem centerCoord_eq {t : ℕ} (p : Label t → ℕ) (z : Label t → ℤ)
    (u : Block t) :
    centerCoord p z u =
      (cofactor p (.inl u.1) : ℤ) * z (.inl u.1) +
        (cofactor p (.inr u.2) : ℤ) * z (.inr u.2) := by
  rw [centerCoord, Fintype.sum_sum_type]
  simp [mark, ite_mul, eq_comm (a := u.1), eq_comm (a := u.2)]

private noncomputable def offset {t : ℕ} (p : Label t → ℕ) (x y : Label t → ℤ)
    (k : Label t) : ℝ² :=
  planePoint ((cofactor p k : ℝ) * x k / commonDen p)
    ((cofactor p k : ℝ) * y k / commonDen p)

private theorem offset_coord {t : ℕ} {p : Label t → ℕ} (hq : commonDen p ≠ 0)
    (x y : Label t → ℤ) (u : Block t) :
    (commonDen p : ℝ) * (offset p x y (.inl u.1) + offset p x y (.inr u.2)) 0 =
      (centerCoord p x u : ℝ) ∧
    (commonDen p : ℝ) * (offset p x y (.inl u.1) + offset p x y (.inr u.2)) 1 =
      (centerCoord p y u : ℝ) := by
  have hqr : (commonDen p : ℝ) ≠ 0 := by exact_mod_cast hq
  constructor <;> simp only [offset, PiLp.add_apply, planePoint_zero, planePoint_one,
    centerCoord_eq, Int.cast_add, Int.cast_mul, Int.cast_natCast, mul_add] <;>
    simp only [← mul_div_assoc, mul_div_cancel_left₀ _ hqr]

private theorem offset_tags {t L : ℕ} {p : Label t → ℕ} {x y : Label t → ℤ}
    (hp : ∀ k, (p k).Prime) (hi : Function.Injective p)
    (hx : ∀ k, ¬ (p k : ℤ) ∣ x k) (hy : ∀ k, ¬ (p k : ℤ) ∣ y k)
    (hxy : ∀ k, ¬ (p k : ℤ) ∣ x k + (L : ℤ) * y k) :
    tags L (offset p x y ∘ Sum.inl) (offset p x y ∘ Sum.inr) := by
  intro u v huv z
  have hu := offset_coord (commonDen_pos hp).ne' x y u
  have hv := offset_coord (commonDen_pos hp).ne' x y v
  dsimp [Function.comp_def]
  let Q : ℝ := commonDen p
  have h₀ : Q * ((offset p x y (.inl u.1) + offset p x y (.inr u.2)) 0 -
        (offset p x y (.inl v.1) + offset p x y (.inr v.2)) 0) =
      (centerCoord p x u : ℝ) - centerCoord p x v := by rw [mul_sub, hu.1, hv.1]
  have h₁ : Q * ((offset p x y (.inl u.1) + offset p x y (.inr u.2)) 1 -
        (offset p x y (.inl v.1) + offset p x y (.inr v.2)) 1) =
      (centerCoord p y u : ℝ) - centerCoord p y v := by rw [mul_sub, hu.2, hv.2]
  simp only [PiLp.add_apply] at h₀ h₁
  refine ⟨?_, ?_, ?_⟩
  · intro he
    rw [he] at h₀
    apply shifted_ne_zero hp hi hx huv (-z)
    have hh : (centerCoord p x u - centerCoord p x v + (commonDen p : ℤ) * -z : ℝ) = 0 := by
      push_cast
      change _ - _ + Q * -_ = _
      linarith only [h₀]
    exact_mod_cast hh
  · intro he
    rw [he] at h₁
    apply shifted_ne_zero hp hi hy huv (-z)
    have hh : (centerCoord p y u - centerCoord p y v + (commonDen p : ℤ) * -z : ℝ) = 0 := by
      push_cast
      change _ - _ + Q * -_ = _
      linarith only [h₁]
    exact_mod_cast hh
  · intro he
    apply shifted_ne_zero hp hi hxy huv (-z)
    have he' := congrArg (Q * ·) he
    rw [mul_add, show ∀ a b : ℝ, Q * (a * b) = a * (Q * b) by intros; ring, h₀, h₁] at he'
    have hh : (shiftedCoord p (fun k => x k + (L : ℤ) * y k) u v (-z) : ℝ) = 0 := by
      simp only [shiftedCoord, centerCoord_eq, Int.cast_add, Int.cast_sub, Int.cast_mul,
        Int.cast_neg, Int.cast_natCast]
      simp only [centerCoord_eq, Int.cast_add, Int.cast_mul, Int.cast_natCast] at he'
      nlinarith only [he']
    exact_mod_cast hh

private def box (L : ℕ) : Finset (ℤ × ℤ) :=
  (Ico (-(L : ℤ)) (L : ℤ)).product (Ico (-(L : ℤ)) (L : ℤ))

private def difference {t L : ℕ} (u : PinIndex t L) (a : Fin L × Fin L) : ℤ × ℤ :=
  ((u.2.1.val : ℤ) - a.1.val, (u.2.2.val : ℤ) - a.2.val)

private theorem difference_mem {t L : ℕ} (u : PinIndex t L) (a : Fin L × Fin L) :
    difference u a ∈ box L := by
  apply mem_product.mpr
  simp only [mem_Ico, difference]
  have := u.2.1.isLt
  have := u.2.2.isLt
  have := a.1.isLt
  have := a.2.isLt
  omega

private theorem difference_injective {t L : ℕ} (u : PinIndex t L) :
    Function.Injective (difference u) := by
  intro a b h
  apply Prod.ext <;> apply Fin.ext
  · have h₀ := congrArg Prod.fst h
    dsimp [difference] at h₀
    omega
  · have h₁ := congrArg Prod.snd h
    dsimp [difference] at h₁
    omega

-- Restricting the square of grid differences cannot create more collisions.
private theorem card_image_defect {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A B : Finset α} (hAB : A ⊆ B) (f : α → β) :
    B.card - (B.image f).card ≥ A.card - (A.image f).card := by
  have hB : (B.image f).card ≤ (A.image f).card + (B \ A).card := by
    have h := card_union_le (A.image f) ((B \ A).image f)
    rw [← image_union, union_sdiff_of_subset hAB] at h
    exact h.trans (Nat.add_le_add_left card_image_le _)
  rw [card_sdiff_of_subset hAB] at hB
  have hA := card_le_card hAB
  omega

private noncomputable def localSpectrum {t L : ℕ} (p : Label t → ℕ) (x y : Label t → ℤ)
    (u : PinIndex t L) (v : Block t) : Finset ℤ :=
  ((univ : Finset (Fin L × Fin L)).image (difference u)).image (shiftedNorm p x y u.1 v)

private theorem card_local_le {t L : ℕ} (p : Label t → ℕ) (x y : Label t → ℤ)
    (u : PinIndex t L) (v : Block t) : (localSpectrum p x y u v).card ≤ L ^ 2 := by
  apply card_image_le.trans
  rw [card_image_of_injective _ (difference_injective u)]
  simp [Fintype.card_prod, pow_two]

private theorem localSpectrum_disjoint {t L : ℕ} {p : Label t → ℕ} {x y : Label t → ℤ}
    (hp : ∀ k, (p k).Prime ∧ p k % 4 = 3)
    (hi : Function.Injective p) (hy : ∀ k, ¬ (p k : ℤ) ∣ y k)
    (u : PinIndex t L) : (↑(univ : Finset (Block t)) : Set (Block t)).PairwiseDisjoint (localSpectrum p x y u) := by
  intro v _ w _ hne
  change Disjoint (localSpectrum p x y u v) (localSpectrum p x y u w)
  rw [Finset.disjoint_left]
  intro n hn hm
  obtain ⟨a, _, ha⟩ := mem_image.mp hn
  obtain ⟨b, _, hb⟩ := mem_image.mp hm
  exact hne (shiftedNorm_separates hp hi hy u.1 (ha.trans hb.symm))

private theorem norm_eq_sqDist {t L : ℕ} {p : Label t → ℕ} (hq : commonDen p ≠ 0)
    (x y : Label t → ℤ) (u : PinIndex t L) (v : Block t) (a : Fin L × Fin L) :
    let r := offset p x y ∘ Sum.inl
    let c := offset p x y ∘ Sum.inr
    (shiftedNorm p x y u.1 v (difference u a) : ℝ) =
      (2 * (commonDen p : ℝ) * dist (pin r c u) (pin r c (v, a))) ^ 2 := by
  dsimp only
  let r := offset p x y ∘ Sum.inl
  let c := offset p x y ∘ Sum.inr
  let Q : ℝ := commonDen p
  have hu := offset_coord hq x y u.1
  have hv := offset_coord hq x y v
  have hcoord (i : Fin 2) :
      2 * Q * (pin r c u i - pin r c (v, a) i) =
        Q * ((r u.1.1 + c u.1.2) i - (r v.1 + c v.2) i +
          (intPoint (u.2.1.val, u.2.2.val) i - intPoint (a.1.val, a.2.val) i)) := by
    have h₀ := congrArg (fun p : ℝ² => p i) (twice_pin r c u)
    have h₁ := congrArg (fun p : ℝ² => p i) (twice_pin r c (v, a))
    simp only [PiLp.add_apply] at h₀ h₁ ⊢
    linear_combination Q * h₀ - Q * h₁
  have h₀ := hcoord 0
  have h₁ := hcoord 1
  change _ = (2 * Q * dist (pin r c u) (pin r c (v, a))) ^ 2
  rw [mul_pow, sqDist_coords, mul_add, ← mul_pow, ← mul_pow, h₀, h₁]
  simp only [shiftedNorm, shiftedCoord, difference, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, intPoint, planePoint_zero, planePoint_one,
    mul_add, mul_sub, r, c, Function.comp_apply, hu.1, hu.2, hv.1, hv.2, Q]

private theorem fullSpectrum_card {t L : ℕ} {p : Label t → ℕ}
    (hp : ∀ k, (p k).Prime ∧ p k % 4 = 3)
    (hi : Function.Injective p) {x y : Label t → ℤ} (hy : ∀ k, ¬ (p k : ℤ) ∣ y k)
    (u : PinIndex t L) :
    let r := offset p x y ∘ Sum.inl
    let c := offset p x y ∘ Sum.inr
    ((configuration L r c).image (dist (pin r c u))).card =
      ∑ v : Block t, (localSpectrum p x y u v).card := by
  dsimp only
  let r := offset p x y ∘ Sum.inl
  let c := offset p x y ∘ Sum.inr
  let Q : ℝ := commonDen p
  let f (d : ℝ) := (2 * Q * d) ^ 2
  let P := configuration L r c
  let E := P.image (dist (pin r c u))
  have hQ : 0 < Q := by
    change (0 : ℝ) < commonDen p
    exact_mod_cast commonDen_pos (fun k => (hp k).1)
  have h₀ : (E.image f).card = E.card := by
    apply card_image_of_injOn
    intro a ha b hb he
    have ha' : 0 ≤ a := by obtain ⟨_, _, rfl⟩ := mem_image.mp ha; exact dist_nonneg
    have hb' : 0 ≤ b := by obtain ⟨_, _, rfl⟩ := mem_image.mp hb; exact dist_nonneg
    have he' : (2 * Q * a) ^ 2 = (2 * Q * b) ^ 2 := he
    have hmul : 2 * Q * a = 2 * Q * b := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp he' with h | h
      · exact h
      · have hnonA := mul_nonneg (show 0 ≤ 2 * Q by positivity) ha'
        have hnonB := mul_nonneg (show 0 ≤ 2 * Q by positivity) hb'
        linarith only [h, hnonA, hnonB]
    exact (mul_left_cancel₀ (by positivity : (2 * Q : ℝ) ≠ 0) hmul)
  have h₁ : E.image f =
      ((univ : Finset (Block t)).biUnion (localSpectrum p x y u)).image (fun n : ℤ => (n : ℝ)) := by
    ext d
    simp only [E, P, configuration, image_image, localSpectrum, mem_image, mem_biUnion, mem_univ,
      true_and, Function.comp_apply]
    constructor
    · rintro ⟨⟨v, a⟩, h⟩
      exact ⟨_, ⟨v, ⟨a, rfl⟩⟩, (norm_eq_sqDist (commonDen_pos (fun k => (hp k).1)).ne' x y u v a).trans h⟩
    · rintro ⟨n, ⟨v, a, ha⟩, hn⟩
      exact ⟨(v, a), (norm_eq_sqDist (commonDen_pos (fun k => (hp k).1)).ne' x y u v a).symm.trans
        ((congrArg (fun n : ℤ => (n : ℝ)) ha).trans hn)⟩
  rw [← h₀, h₁, card_image_of_injective _ Int.cast_injective]
  exact card_biUnion (localSpectrum_disjoint hp hi hy u)

/-- Uniform estimates on the full box of grid differences. In the high regime
we bound the collision deficit, and in the low regime we bound the image. -/
private def boxEstimates {t : ℕ} (L : ℕ) (p : Label t → ℕ) (x y : Label t → ℤ)
    (η : ℝ) : Prop :=
  ∀ u v : Block t,
    let M := ((box L).image (shiftedNorm p x y u v)).card
    if v ∈ high u then
      ((box L).card - M : ℕ) ≤ η * (L : ℝ) ^ 2
    else
      (M : ℝ) ≤ η * (L : ℝ) ^ 2

private theorem localSpectrum_error {t L : ℕ} {p : Label t → ℕ} {x y : Label t → ℤ} {η : ℝ}
    (h : boxEstimates L p x y η) (u : PinIndex t L) (v : Block t) :
    |((localSpectrum p x y u v).card : ℝ) -
      (if v ∈ high u.1 then (L : ℝ) ^ 2 else 0)| ≤ η * (L : ℝ) ^ 2 := by
  let A := (univ : Finset (Fin L × Fin L)).image (difference u)
  let f := shiftedNorm p x y u.1 v
  have hAB : A ⊆ box L := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := mem_image.mp ha
    exact difference_mem u b
  have hA : A.card = L ^ 2 := by
    dsimp [A]
    rw [card_image_of_injective _ (difference_injective u)]
    simp [Fintype.card_prod, pow_two]
  have hlocal : (localSpectrum p x y u v).card = (A.image f).card := rfl
  have hle := card_image_le (s := A) (f := f)
  specialize h u.1 v
  dsimp only at h
  rw [hlocal]
  split_ifs with hv
  · rw [if_pos hv] at h
    have hd := card_image_defect hAB f
    have hd' : ((A.card - (A.image f).card : ℕ) : ℝ) ≤ η * (L : ℝ) ^ 2 :=
      (by exact_mod_cast hd : ((A.card - (A.image f).card : ℕ) : ℝ) ≤
        ((#(box L) - #((box L).image f) : ℕ) : ℝ)).trans h
    have hAc : (A.card : ℝ) = (L : ℝ) ^ 2 := by exact_mod_cast hA
    have hle' : ((A.image f).card : ℝ) ≤ A.card := by exact_mod_cast hle
    rw [Nat.cast_sub hle, hAc] at hd'
    rw [abs_of_nonpos (by linarith only [hle', hAc])]
    linarith only [hd']
  · rw [if_neg hv] at h
    have hmono : ((A.image f).card : ℝ) ≤ ((box L).image f).card := by
      exact_mod_cast card_le_card (image_mono f hAB : A.image f ⊆ (box L).image f)
    rw [sub_zero, abs_of_nonneg (by positivity)]
    exact hmono.trans h

private theorem pinned_error {t L : ℕ} {p : Label t → ℕ} {x y : Label t → ℤ} {η : ℝ}
    (hp : ∀ k, (p k).Prime ∧ p k % 4 = 3)
    (hi : Function.Injective p) (hy : ∀ k, ¬ (p k : ℤ) ∣ y k)
    (hb : boxEstimates L p x y η) (u : PinIndex t L) :
    let r := offset p x y ∘ Sum.inl
    let c := offset p x y ∘ Sum.inr
    |(distinctDistancesFrom (configuration L r c) (pin r c u) : ℝ) -
      ((high u.1).card : ℝ) * (L : ℝ) ^ 2| ≤ (t : ℝ) ^ 2 * (η * (L : ℝ) ^ 2) + 1 := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  dsimp only
  let r := offset p x y ∘ Sum.inl
  let c := offset p x y ∘ Sum.inr
  let P := configuration L r c
  let a := pin r c u
  let E := P.image (dist a)
  let E' := (P.erase a).image (dist a)
  have ha : a ∈ P := mem_configuration r c u
  have hcount : distinctDistancesFrom P a = E'.card := by
    unfold distinctDistancesFrom
    congr 2
    funext q
    exact dist_comm q a
  have hE : insert (dist a a) E' = E := by
    rw [← image_insert, insert_erase ha]
  have hE₁ : (E'.card : ℝ) ≤ E.card := by
    exact_mod_cast card_le_card (image_mono (dist a) (erase_subset a P) : E' ⊆ E)
  have hE₂ : (E.card : ℝ) ≤ E'.card + 1 := by
    exact_mod_cast hE ▸ card_insert_le (dist a a) E'
  have hdrop : |(E'.card : ℝ) - E.card| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hE₁)]
    linarith
  let target (v : Block t) := if v ∈ high u.1 then (L : ℝ) ^ 2 else 0
  have htarget : (∑ v : Block t, target v) = ((high u.1).card : ℝ) * (L : ℝ) ^ 2 := by
    dsimp [target]
    have hf : (univ.filter (fun v : Block t => v ∈ high u.1)) = high u.1 := by
      ext v
      simp
    rw [← sum_filter, hf]
    simp
  have hfull : (E.card : ℝ) = ∑ v : Block t, ((localSpectrum p x y u v).card : ℝ) := by
    rw [show E.card = _ from fullSpectrum_card hp hi hy u]
    push_cast
    rfl
  have hsum : |(E.card : ℝ) - ((high u.1).card : ℝ) * (L : ℝ) ^ 2| ≤
      (t : ℝ) ^ 2 * (η * (L : ℝ) ^ 2) := by
    rw [hfull, ← htarget, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _v : Block t, η * (L : ℝ) ^ 2 :=
        sum_le_sum fun v _ => localSpectrum_error hb u v
      _ = _ := by simp [Block, Fintype.card_prod, pow_two]
  change |(distinctDistancesFrom P a : ℝ) - _| ≤ _
  rw [hcount]
  have hsplit : (E'.card : ℝ) - ((high u.1).card : ℝ) * (L : ℝ) ^ 2 =
      ((E'.card : ℝ) - E.card) +
        ((E.card : ℝ) - ((high u.1).card : ℝ) * (L : ℝ) ^ 2) := by ring
  rw [hsplit]
  linarith only [abs_add_le ((E'.card : ℝ) - E.card)
    ((E.card : ℝ) - ((high u.1).card : ℝ) * (L : ℝ) ^ 2), hdrop, hsum]

/-- The outstanding arithmetic problem involves a box independent of the pin. -/
def H1 : Prop :=
  ∀ m : ℕ, ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
    ∀ᶠ L : ℕ in atTop,
      ∃ (p : Label (2 * (m + 1)) → ℕ) (x y : Label (2 * (m + 1)) → ℤ),
        Function.Injective p ∧ (∀ k, (p k).Prime ∧ p k % 4 = 3) ∧
        (∀ k, ¬ (p k : ℤ) ∣ x k) ∧ (∀ k, ¬ (p k : ℤ) ∣ y k) ∧
        (∀ k, ¬ (p k : ℤ) ∣ x k + (L : ℤ) * y k) ∧ boxEstimates L p x y (η L)

section

/-- Coarse configurations with nearly all block degrees distinct. -/
private def Coarse : Prop :=
  ∀ t : ℕ, 0 < t → Even t →
    ∃ (good : Finset (Block t)) (D : Block t → ℤ) (η : ℕ → ℝ)
      (r c : ℕ → Fin t → ℝ²),
      (t - 1) ^ 2 ≤ good.card ∧ Set.InjOn D good ∧
      (∀ u, 0 ≤ D u ∧ D u ≤ (t : ℤ) ^ 2) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ L : ℕ in atTop, tags L (r L) (c L) ∧
        ∀ u : PinIndex t L,
          |(distinctDistancesFrom (configuration L (r L) (c L)) (pin (r L) (c L) u) : ℝ) -
            (D u.1 : ℝ) * (L : ℝ) ^ 2| ≤ η L * (L : ℝ) ^ 2

private theorem coarse_of_box_estimates (h : H1) : Coarse := by
  classical
  intro t ht htEven
  obtain ⟨k, hk⟩ := htEven
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have he : t = 2 * (m + 1) := by omega
  rw [he]
  let t := 2 * (m + 1)
  obtain ⟨η, hη, hL⟩ := h m
  let Valid (L : ℕ) (data : (Label t → ℕ) × (Label t → ℤ) × (Label t → ℤ)) :=
    Function.Injective data.1 ∧ (∀ k, (data.1 k).Prime ∧ data.1 k % 4 = 3) ∧
    (∀ k, ¬ (data.1 k : ℤ) ∣ data.2.1 k) ∧ (∀ k, ¬ (data.1 k : ℤ) ∣ data.2.2 k) ∧
    (∀ k, ¬ (data.1 k : ℤ) ∣ data.2.1 k + (L : ℤ) * data.2.2 k) ∧
    boxEstimates L data.1 data.2.1 data.2.2 (η L)
  have hex : ∀ᶠ L in atTop, ∃ data, Valid L data := by
    filter_upwards [hL] with L hL
    obtain ⟨p, x, y, hh⟩ := hL
    exact ⟨(p, x, y), hh⟩
  let data (L : ℕ) : (Label t → ℕ) × (Label t → ℤ) × (Label t → ℤ) :=
    if hL : ∃ data, Valid L data then hL.choose else (0, 0, 0)
  let r (L : ℕ) : Fin t → ℝ² := offset (data L).1 (data L).2.1 (data L).2.2 ∘ Sum.inl
  let c (L : ℕ) : Fin t → ℝ² := offset (data L).1 (data L).2.1 (data L).2.2 ∘ Sum.inr
  let η' (L : ℕ) : ℝ := η L * (t : ℝ) ^ 2 + 1 / (L : ℝ)
  refine ⟨goodBlocks m, fun u => (high u).card, η', r, c, (goodBlocks_card m).ge, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv hab
    apply high_injOn m hu hv
    change ((high u).card : ℤ) = ((high v).card : ℤ) at hab
    change (high u).card = (high v).card
    exact_mod_cast hab
  · intro u
    have hh : (high u).card ≤ (2 * (m + 1)) ^ 2 :=
      (card_le_univ _).trans_eq (by simp [Block, pow_two])
    change 0 ≤ ((high u).card : ℤ) ∧ ((high u).card : ℤ) ≤ ((2 * (m + 1) : ℕ) : ℤ) ^ 2
    exact ⟨by positivity, by exact_mod_cast hh⟩
  · simpa only [zero_mul, zero_add] using
      (hη.mul_const ((t : ℝ) ^ 2)).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  · filter_upwards [hex, eventually_gt_atTop 0] with L hL hpos
    have hd : Valid L (data L) := by
      dsimp [data]
      rw [dif_pos hL]
      exact hL.choose_spec
    obtain ⟨hi, hp, hx, hy, hxy, hb⟩ := hd
    refine ⟨offset_tags (fun k => (hp k).1) hi hx hy hxy, fun u => ?_⟩
    have h₀ := pinned_error hp hi hy hb u
    simp only [r, c, η', Int.cast_natCast]
    refine h₀.trans ?_
    have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hpos
    have hLr' : (L : ℝ) ≠ 0 := by positivity
    have heq : (1 / (L : ℝ)) * (L : ℝ) ^ 2 = L := by field_simp
    rw [add_mul, heq]
    linarith only [hLr, show (t : ℝ) ^ 2 * (η L * (L : ℝ) ^ 2) =
      η L * (t : ℝ) ^ 2 * (L : ℝ) ^ 2 by ring]

end

/-- Integer score separation with coarse errors and strip corrections. -/
private def IntegerSelection : Prop :=
  ∀ (t : ℕ) (δ : ℝ), 0 < t → 0 < δ → δ < 1 →
    ∃ B : ℕ, ∀ (good : Finset (Block t)) (D : Block t → ℤ)
      (Z : (L : ℕ) → PinIndex t L → ℤ) (η : ℕ → ℝ),
      Set.InjOn D good → (∀ u, 0 ≤ D u ∧ D u ≤ (t : ℤ) ^ 2) →
      Tendsto η atTop (𝓝 0) →
      (∀ᶠ L : ℕ in atTop, ∀ u : PinIndex t L,
        |(Z L u : ℝ) - (D u.1 : ℝ) * (L : ℝ) ^ 2| ≤ η L * (L : ℝ) ^ 2) →
      ∀ᶠ L : ℕ in atTop, ∃ (a b : ℤ)
          (qx qy : Block t → Fin L → ℕ) (q : PinIndex t L → ℕ)
          (S : Finset (PinIndex t L)),
        (0 ≤ a ∧ a ≤ L) ∧ ((L : ℤ) ≤ b ∧ b ≤ 2 * (L : ℤ)) ∧
        (∀ u j, qx u j ≤ 4 * L ∧ qy u j ≤ 4 * L) ∧ (∀ u, q u ≤ B) ∧
        Set.InjOn (fun u : PinIndex t L => Z L u + a * u.2.1.val + b * u.2.2.val -
          (qx u.1 u.2.1 : ℤ) - (qy u.1 u.2.2 : ℤ) - (q u : ℤ)) S ∧
        (1 - δ) * good.card * (L : ℝ) ^ 2 ≤ (S.card : ℝ)

private noncomputable def bin {ι : Type*} (B : ℕ) (f : ι → ℝ) (u : ι) : ℤ :=
  ⌊f u / B⌋

private noncomputable def overflow {ι : Type*} (S : Finset ι) (f : ι → ℝ) (B : ℕ) : ℕ :=
  ∑ k ∈ S.image (bin B f), ((S.filter (fun u => bin B f u = k)).card - B)

private theorem assign_bins {ι : Type*} (W : Finset ι) (f : ι → ℝ) {B : ℕ} (hB : 0 < B) :
    ∃ (S : Finset ι) (T : ι → ℤ),
      S.card + overflow W f B = W.card ∧ Set.InjOn T S ∧
      ∀ u ∈ S, |(T u : ℝ) - f u| ≤ B := by
  classical
  let idx := bin B f
  let I := W.image idx
  let bucket (k : ℤ) := W.filter fun u => idx u = k
  have hex (k : ℤ) : ∃ S ⊆ bucket k, S.card = min B (bucket k).card :=
    exists_subset_card_eq (min_le_right _ _)
  choose select hsub hsize using hex
  let S := I.biUnion select
  have hidx {u : ι} {k : ℤ} (hu : u ∈ select k) : idx u = k :=
    (mem_filter.mp (hsub k hu)).2
  have hin {u : ι} (hu : u ∈ S) : u ∈ select (idx u) := by
    obtain ⟨k, _, hk⟩ := mem_biUnion.mp hu
    rwa [hidx hk]
  let rank (k : ℤ) := Fintype.equivFin (↑(select k) : Type _)
  let pos (k : ℤ) (u : ι) (hu : u ∈ select k) :=
    (rank k ⟨u, hu⟩).val
  let T (u : ι) : ℤ :=
    if hu : u ∈ select (idx u) then (B : ℤ) * idx u + (pos (idx u) u hu : ℤ) else 0
  have hT {u : ι} (hu : u ∈ S) : T u = (B : ℤ) * idx u + (pos (idx u) u (hin hu) : ℤ) :=
    dif_pos (hin hu)
  have hpos {u : ι} (hu : u ∈ S) : pos (idx u) u (hin hu) < B := by
    have hh := (rank (idx u) ⟨u, hin hu⟩).isLt
    have hc : Fintype.card (↑(select (idx u)) : Type _) ≤ B :=
      ((Fintype.card_coe _).trans (hsize _)).le.trans (min_le_left _ _)
    exact hh.trans_le hc
  have hdiv {u : ι} (hu : u ∈ S) : T u / (B : ℤ) = idx u := by
    have hB' : (B : ℤ) ≠ 0 := by positivity
    have hlt : (pos (idx u) u (hin hu) : ℤ) < B := by exact_mod_cast hpos hu
    rw [hT hu, Int.mul_add_ediv_left _ _ hB',
      Int.ediv_eq_zero_of_lt (by positivity) hlt, add_zero]
  refine ⟨S, T, ?_, ?_, ?_⟩
  · have hdis : (↑I : Set ℤ).PairwiseDisjoint select := by
      intro k _ j _ hkj
      change Disjoint (select k) (select j)
      rw [Finset.disjoint_left]
      intro u hu hv
      exact hkj ((hidx hu).symm.trans (hidx hv))
    rw [show S.card = ∑ k ∈ I, (select k).card from card_biUnion hdis]
    change (∑ k ∈ I, (select k).card) + (∑ k ∈ I, ((bucket k).card - B)) = W.card
    rw [← sum_add_distrib]
    have hs : ∑ k ∈ I, (bucket k).card = W.card := by
      unfold bucket
      rw [sum_card_fiberwise_eq_card_filter]
      congr 1
      exact filter_eq_self.mpr fun u hu => mem_image_of_mem idx hu
    rw [← hs]
    apply sum_congr rfl
    intro k _
    rw [hsize k]
    omega
  · intro u hu v hv he
    have hu' := hin hu
    have hv' := hin hv
    have hidx' : idx u = idx v := by rw [← hdiv hu, ← hdiv hv, he]
    change T u = T v at he
    rw [hT hu, hT hv] at he
    have hmul : (B : ℤ) * idx u = (B : ℤ) * idx v := congrArg ((B : ℤ) * ·) hidx'
    have he' : pos (idx u) u hu' = pos (idx v) v hv' := by omega
    have hvin : v ∈ select (idx u) := by rwa [hidx']
    have hpos_eq {k j : ℤ} (h : k = j) (w : ι)
        (hk : w ∈ select k) (hj : w ∈ select j) : pos k w hk = pos j w hj := by
      subst j
      rfl
    have hpos' : pos (idx u) u hu' = pos (idx u) v hvin :=
      he'.trans (hpos_eq hidx'.symm v hv' hvin)
    exact congrArg Subtype.val ((rank (idx u)).injective (Fin.ext hpos'))
  · intro u hu
    have hB' : (0 : ℝ) < B := by positivity
    have hfloor : (idx u : ℝ) ≤ f u / B := Int.floor_le _
    have hceil : f u / B < (idx u : ℝ) + 1 := Int.lt_floor_add_one _
    have hleft := (le_div_iff₀ hB').mp hfloor
    have hright := (div_lt_iff₀ hB').mp hceil
    have hpos' : (pos (idx u) u (hin hu) : ℝ) < B := by exact_mod_cast hpos hu
    have hnon : 0 ≤ (pos (idx u) u (hin hu) : ℝ) := by positivity
    rw [hT hu]
    push_cast
    exact abs_le.mpr ⟨by nlinarith only [hright, hnon], by nlinarith only [hleft, hpos']⟩

private def goodPins {t L : ℕ} (good : Finset (Block t)) : Finset (PinIndex t L) :=
  good.product univ

private theorem goodPins_card {t L : ℕ} (good : Finset (Block t)) :
    (goodPins (L := L) good).card = good.card * L ^ 2 := by
  simp [goodPins, Fintype.card_prod, pow_two]

private noncomputable def score {t L : ℕ} (Z : PinIndex t L → ℤ) (a b : ℝ)
    (wx wy : Block t → Fin L → ℕ) (u : PinIndex t L) : ℝ :=
  Z u + a * u.2.1.val + b * u.2.2.val - wx u.1 u.2.1 - wy u.1 u.2.2

/-- The remaining numerical problem is to bound the total overflow of fixed-width
bins in one affine projection, with optional bounded strip shifts. -/
def H2 : Prop :=
  ∀ (t : ℕ) (δ : ℝ), 0 < t → 0 < δ → δ < 1 →
    ∃ B : ℕ, 0 < B ∧ ∀ (good : Finset (Block t)) (D : Block t → ℤ)
      (Z : (L : ℕ) → PinIndex t L → ℤ) (η : ℕ → ℝ),
      Set.InjOn D good → (∀ u, 0 ≤ D u ∧ D u ≤ (t : ℤ) ^ 2) →
      Tendsto η atTop (𝓝 0) →
      (∀ᶠ L : ℕ in atTop, ∀ u : PinIndex t L,
        |(Z L u : ℝ) - (D u.1 : ℝ) * (L : ℝ) ^ 2| ≤ η L * (L : ℝ) ^ 2) →
      ∀ᶠ L : ℕ in atTop, ∃ (a b : ℝ) (wx wy : Block t → Fin L → ℕ),
        (0 ≤ a ∧ a ≤ L) ∧ ((L : ℝ) ≤ b ∧ b ≤ 2 * (L : ℝ)) ∧
        (∀ u j, wx u j ≤ 3 * L ∧ wy u j ≤ 3 * L) ∧
        (overflow (goodPins (L := L) good) (score (Z L) a b wx wy) B : ℝ) ≤
          δ * good.card * (L : ℝ) ^ 2

section

private noncomputable def stripRounding {L : ℕ} (a : ℝ) (j : Fin L) : ℕ :=
  (⌈a⌉ * (j.val : ℤ) - ⌊a * (j.val : ℝ)⌋).toNat

private theorem stripRounding_spec {L : ℕ} (a : ℝ) (j : Fin L) :
    (stripRounding a j : ℤ) = ⌈a⌉ * (j.val : ℤ) - ⌊a * (j.val : ℝ)⌋ ∧
    stripRounding a j ≤ L := by
  have hj : (0 : ℝ) ≤ j.val := by positivity
  have hjL : (j.val : ℝ) + 1 ≤ L := by exact_mod_cast j.isLt
  have hlo := mul_le_mul_of_nonneg_right (Int.le_ceil a) hj
  have hhi := mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one a).le hj
  let d : ℤ := ⌈a⌉ * (j.val : ℤ) - ⌊a * (j.val : ℝ)⌋
  have h₀ : (0 : ℝ) ≤ (d : ℝ) := by
    dsimp [d]
    push_cast
    linarith only [hlo, Int.floor_le (a * (j.val : ℝ))]
  have h₁ : (d : ℝ) ≤ L := by
    dsimp [d]
    push_cast
    nlinarith only [hhi, hjL, Int.lt_floor_add_one (a * (j.val : ℝ))]
  have hd : 0 ≤ d := by exact_mod_cast h₀
  constructor
  · exact Int.toNat_of_nonneg hd
  · have hle : d ≤ (L : ℤ) := by exact_mod_cast h₁
    change d.toNat ≤ L
    omega

-- Ceiling the slopes creates separable strip shifts. The two floor errors
-- cost at most two units of extra displacement per selected pin.
private theorem integer_of_bins (h : H2) : IntegerSelection := by
  intro t δ ht hδ hδ₁
  obtain ⟨B, hB, hex⟩ := h t δ ht hδ hδ₁
  refine ⟨2 * B + 4, ?_⟩
  intro good D Z η hi hD hη hZ
  filter_upwards [hex good D Z η hi hD hη hZ] with L hL
  obtain ⟨a, b, wx, wy, ha, hb, hshift, hover⟩ := hL
  let f := score (Z L) a b wx wy
  obtain ⟨S, T, hcard, hinj, hnear⟩ := assign_bins (goodPins (L := L) good) f hB
  let qx (v : Block t) (j : Fin L) := stripRounding a j + wx v j
  let qy (v : Block t) (j : Fin L) := stripRounding b j + wy v j
  let F (u : PinIndex t L) : ℤ := Z L u + ⌊a * (u.2.1.val : ℝ)⌋ +
      ⌊b * (u.2.2.val : ℝ)⌋ - (wx u.1 u.2.1 : ℤ) - (wy u.1 u.2.2 : ℤ)
  let q (u : PinIndex t L) := if u ∈ S then (F u - T u + (B : ℤ) + 2).toNat else 0
  have hround (u : PinIndex t L) :
      Z L u + ⌈a⌉ * u.2.1.val + ⌈b⌉ * u.2.2.val -
        (qx u.1 u.2.1 : ℤ) - (qy u.1 u.2.2 : ℤ) = F u := by
    dsimp only [qx, qy, F]
    rw [Int.natCast_add, Int.natCast_add, (stripRounding_spec a _).1, (stripRounding_spec b _).1]
    ring
  have hcorr {u : PinIndex t L} (hu : u ∈ S) :
      (q u : ℤ) = F u - T u + (B : ℤ) + 2 ∧ q u ≤ 2 * B + 4 := by
    have habs := abs_le.mp (hnear u hu)
    have hax := Int.floor_le (a * (u.2.1.val : ℝ))
    have hay := Int.floor_le (b * (u.2.2.val : ℝ))
    have hbx := Int.lt_floor_add_one (a * (u.2.1.val : ℝ))
    have hby := Int.lt_floor_add_one (b * (u.2.2.val : ℝ))
    let d : ℤ := F u - T u + (B : ℤ) + 2
    have hlo : (0 : ℝ) ≤ (d : ℝ) := by
      dsimp [d, F]
      push_cast
      dsimp [f, score] at habs
      linarith only [habs.2, hbx, hby]
    have hhi : (d : ℝ) ≤ 2 * (B : ℝ) + 4 := by
      dsimp [d, F]
      push_cast
      dsimp [f, score] at habs
      linarith only [habs.1, hax, hay]
    have hnn : 0 ≤ d := by exact_mod_cast hlo
    have hle : d ≤ 2 * (B : ℤ) + 4 := by exact_mod_cast hhi
    simp only [q, if_pos hu]
    change (d.toNat : ℤ) = d ∧ d.toNat ≤ 2 * B + 4
    exact ⟨Int.toNat_of_nonneg hnn, by omega⟩
  refine ⟨⌈a⌉, ⌈b⌉, qx, qy, q, S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨Int.ceil_nonneg ha.1, Int.ceil_le.mpr (by exact_mod_cast ha.2)⟩
  · refine ⟨?_, Int.ceil_le.mpr (by push_cast; exact hb.2)⟩
    have h := hb.1.trans (Int.le_ceil b)
    exact_mod_cast h
  · intro u j
    have hx := (stripRounding_spec a j).2
    have hy := (stripRounding_spec b j).2
    have hw := hshift u j
    dsimp [qx, qy]
    omega
  · intro u
    by_cases hu : u ∈ S
    · exact (hcorr hu).2
    · simp [q, hu]
  · intro u hu v hv he
    change _ - _ = _ - _ at he
    rw [hround u, hround v, (hcorr hu).1, (hcorr hv).1] at he
    exact hinj hu hv (by omega)
  · have hc : (S.card : ℝ) + (overflow (goodPins (L := L) good) f B : ℝ) =
        (good.card : ℝ) * (L : ℝ) ^ 2 := by
      rw [goodPins_card] at hcard
      exact_mod_cast hcard
    change (overflow (goodPins (L := L) good) f B : ℝ) ≤ _ at hover
    nlinarith only [hc, hover]


end

section

private theorem projection_sub (a b : ℝ) (p q : ℝ²) :
    projection a b (p - q) = projection a b p - projection a b q := by
  simp only [projection, PiLp.sub_apply]
  ring

private theorem projection_pin {t L : ℕ} (r c : Fin t → ℝ²) (u : PinIndex t L) (a b : ℝ) :
    2 * projection a b (pin r c u) =
      projection a b (r u.1.1 + c u.1.2) + a * u.2.1.val + b * u.2.2.val := by
  have h := congrArg (projection a b) (twice_pin r c u)
  simp only [projection, PiLp.add_apply, intPoint, planePoint_zero, planePoint_one,
    Int.cast_natCast] at h ⊢
  linear_combination h

/-- Strip corrections of order L and bounded individual corrections fit within L² new points. -/
private theorem correct_labels (t B : ℕ) :
    ∀ᶠ L : ℕ in atTop,
    ∀ (r c : Fin t → ℝ²), tags L r c →
    ∀ P : Finset ℝ², configuration L r c ⊆ P →
    ∀ (qx qy : Block t → Fin L → ℕ) (q : PinIndex t L → ℕ),
      (∀ u j, qx u j ≤ 4 * L ∧ qy u j ≤ 4 * L) → (∀ u, q u ≤ B) →
      ∃ Q : Finset ℝ², P ⊆ Q ∧ Q.card ≤ P.card + L ^ 2 ∧ ∃ C : ℤ,
        ∀ u : PinIndex t L, (distinctDistancesFrom Q (pin r c u) : ℤ) =
          distinctDistancesFrom P (pin r c u) + C -
          (qx u.1 u.2.1 : ℤ) - (qy u.1 u.2.2 : ℤ) - (q u : ℤ) := by
  classical
  let K := Fintype.card (Block t)
  obtain ⟨d, hd, hrow⟩ := row_budget K
  obtain ⟨e, he, hind⟩ := individual_budget K B
  filter_upwards [hrow, hind, eventually_gt_atTop 0] with L hrow hind hL
  intro r c htags P hP qx qy q hq hq'
  let tag (u : Block t) := r u.1 + c u.2
  have hbase (a b : ℝ) (h : ∀ u v : Block t, u ≠ v → ∀ z : ℤ,
        projection a b (tag u - tag v) ≠ z) :
      ∀ u v : Block t, ∀ z : ℤ, projection a b (tag u) - projection a b (tag v) = z →
        u = v := by
    intro u v z heq
    by_contra! hne
    exact h u v hne z ((projection_sub a b _ _).trans heq)
  have hx := hbase 1 0 (fun u v h z => by
    simpa [projection, tag] using (htags u v h z).1)
  have hy := hbase 0 1 (fun u v h z => by
    simpa [projection, tag] using (htags u v h z).2.1)
  have hxy := hbase 1 L (fun u v h z => by
    simpa [projection, tag] using (htags u v h z).2.2)
  let code (w : Fin L × Fin L) : Fin (L ^ 2) :=
    ⟨L * w.2.val + w.1.val, by
      have hm := Nat.mul_le_mul_left L (Nat.succ_le_of_lt w.2.isLt)
      rw [Nat.mul_succ] at hm
      rw [pow_two]
      have h₁ := w.1.isLt
      omega⟩
  have hcode : Function.Injective code := by
    intro w v h
    have hh : L * w.2.val + w.1.val = L * v.2.val + v.1.val :=
      congrArg (fun j : Fin (L ^ 2) => j.val) h
    exact Prod.ext (radix_injective hh).2 (Fin.ext (radix_injective hh).1)
  let values (u : Block t) (j : Fin (L ^ 2)) : ℕ :=
    if h : ∃ w, code w = j then q (u, Classical.choose h) else 0
  have hvalues (u : Block t) (j : Fin (L ^ 2)) : values u j ≤ B := by
    dsimp [values]
    split
    · exact hq' _
    · omega
  have heval (u : PinIndex t L) : values u.1 (code u.2) = q u := by
    dsimp [values]
    split
    · rename_i h
      rw [hcode (Classical.choose_spec h)]
    · rename_i h
      exact (h ⟨u.2, rfl⟩).elim
  obtain ⟨P₁, hP₁, hcard₁, C₁, h₁⟩ := extend_labelled hd P 1 0 (by norm_num)
    (projection 1 0 ∘ tag) hx qx (fun u j => (hq u j).1)
  obtain ⟨P₂, hP₂, hcard₂, C₂, h₂⟩ := extend_labelled hd P₁ 0 1 (by norm_num)
    (projection 0 1 ∘ tag) hy qy (fun u j => (hq u j).2)
  obtain ⟨Q, hQ, hcard₃, C₃, h₃⟩ := extend_labelled he P₂ 1 L (by positivity)
    (projection 1 L ∘ tag) hxy values hvalues
  refine ⟨Q, hP₁.trans (hP₂.trans hQ), ?_, C₁ + C₂ + C₃, ?_⟩
  · change P₁.card ≤ P.card + 4 * L * (2 ^ d * d + K * (L / d + 1)) at hcard₁
    change P₂.card ≤ P₁.card + 4 * L * (2 ^ d * d + K * (L / d + 1)) at hcard₂
    change Q.card ≤ P₂.card + B * (2 ^ e * e + K * (L ^ 2 / e + 1)) at hcard₃
    omega
  · intro u
    have hp := hP (mem_configuration r c u)
    have hx_pin : 2 * projection 1 0 (pin r c u) =
        (projection 1 0 ∘ tag) u.1 + u.2.1.val := by
      simpa [tag] using projection_pin r c u 1 0
    have hy_pin : 2 * projection 0 1 (pin r c u) =
        (projection 0 1 ∘ tag) u.1 + u.2.2.val := by
      simpa [tag] using projection_pin r c u 0 1
    have hxy_pin : 2 * projection 1 L (pin r c u) =
        (projection 1 L ∘ tag) u.1 + (code u.2).val := by
      unfold code
      push_cast
      have h := projection_pin r c u 1 L
      dsimp [tag, Function.comp_def]
      linarith
    rw [h₃ _ (hP₂ (hP₁ hp)) u.1 _ hxy_pin, h₂ _ (hP₁ hp) u.1 _ hy_pin,
      h₁ _ hp u.1 _ hx_pin, heval]
    ring

private theorem square_configurations (h₁ : Coarse) (h₂ : IntegerSelection) {t : ℕ}
    (ht : 0 < t) (htEven : Even t) {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ∀ᶠ L : ℕ in atTop, ∃ Q : Finset ℝ²,
      Q.card ≤ (t ^ 2 + 50 * t + 1) * L ^ 2 ∧
      (1 - δ) * ((t - 1 : ℕ) : ℝ) ^ 2 * (L : ℝ) ^ 2 ≤ (diversity Q : ℝ) := by
  obtain ⟨good, D, η, r, c, hg, hinjD, hD, hη, hcoarse⟩ := h₁ t ht htEven
  obtain ⟨B, hB⟩ := h₂ t δ ht hδ hδ₁
  let Z (L : ℕ) (u : PinIndex t L) : ℤ :=
    distinctDistancesFrom (configuration L (r L) (c L)) (pin (r L) (c L) u)
  have hZ : ∀ᶠ L : ℕ in atTop, ∀ u : PinIndex t L,
      |(Z L u : ℝ) - (D u.1 : ℝ) * (L : ℝ) ^ 2| ≤ η L * (L : ℝ) ^ 2 := by
    filter_upwards [hcoarse] with L hL u
    simpa only [Z, Int.cast_natCast] using hL.2 u
  filter_upwards [hcoarse, hB good D Z η hinjD hD hη hZ, correct_labels t B, eventually_gt_atTop 0]
    with L htags hselection hcorrection hL
  obtain ⟨a, b, qx, qy, q, S, ha, hb, hqx, hq, hS, hy⟩ := hselection
  let P := configuration L (r L) (c L)
  have hsep := separated_of_tags htags.1
  obtain ⟨P₁, hP₁, hcard₁, C₁, hcounts₁⟩ := extend_affine hL (r L) (c L) hsep a b ha hb P
  obtain ⟨Q, hQ, hcard₂, C₂, hcounts₂⟩ := hcorrection (r L) (c L) htags.1 P₁ hP₁ qx qy q hqx hq
  have hcountsᵢ (u : PinIndex t L) :
      (distinctDistancesFrom Q (pin (r L) (c L) u) : ℤ) =
        (Z L u + a * u.2.1.val + b * u.2.2.val - (qx u.1 u.2.1 : ℤ) -
          (qy u.1 u.2.2 : ℤ) - (q u : ℤ)) + (C₁ + C₂) := by
    rw [hcounts₂ u, hcounts₁ _ (mem_configuration (r L) (c L) u)
      u.1.1 u.1.2 u.2.1 u.2.2 (twice_pin (r L) (c L) u)]
    change Z L u + C₁ + a * _ + b * _ + C₂ - _ - _ - _ = _
    ring
  have hdiv : S.card ≤ diversity Q := by
    apply diversity_le_of_image S Q (pin (r L) (c L))
    · intro u _
      exact hQ (hP₁ (mem_configuration (r L) (c L) u))
    · intro u hu v hv he
      apply hS hu hv
      have he' : (distinctDistancesFrom Q (pin (r L) (c L) u) : ℤ) =
          (distinctDistancesFrom Q (pin (r L) (c L) v) : ℤ) := by exact_mod_cast he
      rw [hcountsᵢ, hcountsᵢ] at he'
      exact add_right_cancel he'
  have hgr : ((t - 1 : ℕ) : ℝ) ^ 2 ≤ (good.card : ℝ) := by exact_mod_cast hg
  refine ⟨Q, ?_, ?_⟩
  · have hc := configuration_card_le L (r L) (c L)
    calc
      Q.card ≤ P₁.card + L ^ 2 := hcard₂
      _ ≤ P.card + 50 * t * L ^ 2 + L ^ 2 := Nat.add_le_add_right hcard₁ _
      _ ≤ t ^ 2 * L ^ 2 + 50 * t * L ^ 2 + L ^ 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right hc _) _
      _ = _ := by ring
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgr (by linarith))
      (sq_nonneg _)).trans (hy.trans (by exact_mod_cast hdiv))

private theorem assemble : Coarse → IntegerSelection → type_of% @Erdos653.erdos_653 := by
  intro h₁ h₂
  apply of_witnesses
  intro ε hε
  let δ : ℝ := min (ε / 3) (1 / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ' : δ ≤ 1 / 4 := min_le_right _ _
  have hδ₁ : δ < 1 := by linarith
  have hδε : δ ≤ ε / 3 := min_le_left _ _
  obtain ⟨m, hm⟩ := exists_nat_gt (53 / δ)
  let t : ℕ := 2 * (m + 1)
  have ht : 0 < t := by simp [t]
  have htEven : Even t := ⟨m + 1, by unfold t; ring⟩
  have htm : (m : ℝ) ≤ (t : ℝ) := by
    dsimp [t]
    push_cast
    linarith [show 0 ≤ (m : ℝ) by positivity]
  have hlarge : (53 : ℝ) < δ * t := by
    calc
      (53 : ℝ) < (m : ℝ) * δ := (div_lt_iff₀ hδ).mp hm
      _ ≤ (t : ℝ) * δ := mul_le_mul_of_nonneg_right htm hδ.le
      _ = _ := mul_comm _ _
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hcast : ((t - 1 : ℕ) : ℝ) = t - 1 := by rw [Nat.cast_sub ht, Nat.cast_one]
  have hc : 0 < (1 - 2 * δ : ℝ) := by linarith
  have hgap : (1 - 2 * δ) * ((t ^ 2 + 50 * t + 1 : ℕ) : ℝ) <
      (1 - δ) * ((t - 1 : ℕ) : ℝ) ^ 2 := by
    rw [hcast]
    push_cast
    have hlarge' := mul_lt_mul_of_pos_right hlarge htR
    have hdt := mul_nonneg hδ.le htR.le
    nlinarith only [hlarge', hdt, hδ, htR]
  have hev := eventual_of_squares (A := t ^ 2 + 50 * t + 1) (by positivity) hc hgap
    (square_configurations h₁ h₂ ht htEven hδ hδ₁)
  filter_upwards [hev] with n hn
  obtain ⟨P, hp, hy⟩ := hn
  exact ⟨P, hp, (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)).trans hy⟩

theorem main : H1 → H2 → type_of% @Erdos653.erdos_653 := by
  intro h₁ h₂
  exact assemble (coarse_of_box_estimates h₁) (integer_of_bins h₂)

end

end OMA.R_Erdos653_erdos_653_R2
