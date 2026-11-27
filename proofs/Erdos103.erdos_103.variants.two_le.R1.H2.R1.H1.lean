import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1
import Mathlib

/-! A separated set of `n` points on a circle has at most `16 R + 8` points
(four arcs, on each of which one coordinate separates the points), and its
diameter is at least `R` when the centre is the centroid.  Thirty-two rows of
lattice points have diameter at most `n / 32 + 31`. -/

open EuclideanGeometry Filter Finset
open Erdos103
open scoped Classical ENNReal

namespace OMA.Concyclic

theorem dist_sq (x y : ℝ²) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq,Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Fin.sum_univ_two]
  simp [Real.dist_eq,sq_abs]

theorem le_of_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hh
  push Not at hh
  nlinarith

theorem sep_dist {n : ℕ} {B : Finset ℝ²} (hB : B ∈ separatedSets n) {x y : ℝ²}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y) : 1 ≤ dist x y := by
  have hh := hB.2 hx hy hxy
  change (1:ℝ≥0∞) ≤ edist x y at hh
  rwa [edist_dist,← ENNReal.ofReal_one,ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hh

theorem arc_aux {a b a' b' : ℝ} (h : a ^ 2 + b ^ 2 = a' ^ 2 + b' ^ 2)
    (h1 : |a| ≤ b) (h1' : |a'| ≤ b') : (b - b') ^ 2 ≤ (a - a') ^ 2 := by
  have hs : |a + a'| ≤ b + b' := (abs_add_le _ _).trans (add_le_add h1 h1')
  have hb : 0 ≤ b := (abs_nonneg _).trans h1
  have hb' : 0 ≤ b' := (abs_nonneg _).trans h1'
  rcases eq_or_lt_of_le (add_nonneg hb hb') with h0|h0
  · have e1 : b = 0 := by linarith
    have e2 : b' = 0 := by linarith
    rw [e1,e2]
    nlinarith [sq_nonneg (a - a')]
  · have e : (b - b') * (b + b') = (a' - a) * (a' + a) := by linear_combination h
    have h2 : (b - b') ^ 2 * (b + b') ^ 2 = (a - a') ^ 2 * (a + a') ^ 2 := by
      linear_combination ((b - b') * (b + b') + (a' - a) * (a' + a)) * e
    have h3 : (a + a') ^ 2 ≤ (b + b') ^ 2 := by
      have := abs_le.mp hs
      nlinarith
    by_contra hc
    push Not at hc
    have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg (a - a'))
    have h5 := mul_lt_mul_of_pos_right hc (pow_pos h0 2)
    linarith

theorem arc {a b a' b' : ℝ} (h : a ^ 2 + b ^ 2 = a' ^ 2 + b' ^ 2)
    (h1 : |a| ≤ |b|) (h1' : |a'| ≤ |b'|) (hs : 0 ≤ b ↔ 0 ≤ b') :
    (b - b') ^ 2 ≤ (a - a') ^ 2 := by
  by_cases hb : 0 ≤ b
  · have hb' := hs.mp hb
    rw [abs_of_nonneg hb] at h1
    rw [abs_of_nonneg hb'] at h1'
    exact arc_aux h h1 h1'
  · have hb' : ¬ 0 ≤ b' := fun hh => hb (hs.mpr hh)
    push Not at hb hb'
    rw [abs_of_neg hb] at h1
    rw [abs_of_neg hb'] at h1'
    have := arc_aux (a := a) (b := -b) (a' := a') (b' := -b') (by linarith [h]) h1 h1'
    calc (b - b') ^ 2 = (-b - -b') ^ 2 := by ring
      _ ≤ _ := this

theorem floor_close {s s' : ℝ} (h : ⌊2 * s⌋ = ⌊2 * s'⌋) : 4 * (s - s') ^ 2 < 1 := by
  have := abs_lt.mp (Int.abs_sub_lt_one_of_floor_eq_floor h)
  nlinarith

theorem floor_range {s R : ℝ} (h : s ^ 2 ≤ R ^ 2) (hR : 0 ≤ R) :
    ⌊2 * s⌋ ∈ Finset.Icc ⌊-(2 * R)⌋ ⌊2 * R⌋ := by
  have h1 : s ≤ R := le_of_sq_le hR h
  have h2 : -s ≤ R := le_of_sq_le hR (by simpa using h)
  exact Finset.mem_Icc.mpr ⟨Int.floor_mono (by linarith),Int.floor_mono (by linarith)⟩

set_option maxHeartbeats 1000000 in
theorem card_le {n : ℕ} {B : Finset ℝ²} (hB : B ∈ separatedSets n) {c : ℝ²} {R : ℝ}
    (hR : ∀ x ∈ B, dist x c = R) (hne : B.Nonempty) : (n : ℝ) ≤ 16 * R + 8 := by
  have hR0 : 0 ≤ R := by
    obtain ⟨x,hx⟩ := hne
    rw [← hR x hx]
    exact dist_nonneg
  have hcirc (x : ℝ²) (hx : x ∈ B) : (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 = R ^ 2 := by
    rw [← dist_sq,hR x hx]
  let G (x : ℝ²) : Bool × Bool × ℤ :=
    if |x 0 - c 0| ≤ |x 1 - c 1| then (true,decide (0 ≤ x 1 - c 1),⌊2 * (x 0 - c 0)⌋)
    else (false,decide (0 ≤ x 0 - c 0),⌊2 * (x 1 - c 1)⌋)
  let T : Finset (Bool × Bool × ℤ) :=
    (univ : Finset Bool) ×ˢ (univ : Finset Bool) ×ˢ Finset.Icc ⌊-(2 * R)⌋ ⌊2 * R⌋
  have hmaps : ∀ x ∈ B, G x ∈ T := by
    intro x hx
    have hc := hcirc x hx
    dsimp [G,T]
    split_ifs with h
    · exact mem_product.mpr ⟨mem_univ _,mem_product.mpr ⟨mem_univ _,
        floor_range (by nlinarith [sq_nonneg (x 1 - c 1)]) hR0⟩⟩
    · exact mem_product.mpr ⟨mem_univ _,mem_product.mpr ⟨mem_univ _,
        floor_range (by nlinarith [sq_nonneg (x 0 - c 0)]) hR0⟩⟩
  have hinj : Set.InjOn G (B : Set ℝ²) := by
    intro x hx y hy hG
    by_contra hxy
    have hd := sep_dist hB hx hy hxy
    have hd2 : 1 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
      rw [← dist_sq]
      nlinarith
    have hcx := hcirc x hx
    have hcy := hcirc y hy
    dsimp [G] at hG
    split_ifs at hG with h1 h2 h2
    · simp only [Prod.mk.injEq,true_and,decide_eq_decide] at hG
      have h3 := arc (by linarith) h1 h2 hG.1
      have h4 := floor_close hG.2
      nlinarith
    · simp at hG
    · simp at hG
    · simp only [Prod.mk.injEq,true_and,decide_eq_decide] at hG
      push Not at h1 h2
      have h3 := arc (a := x 1 - c 1) (b := x 0 - c 0) (a' := y 1 - c 1) (b' := y 0 - c 0)
        (by linarith) h1.le h2.le hG.1
      have h4 := floor_close hG.2
      nlinarith
  have hcard : B.card ≤ T.card := card_le_card_of_injOn G hmaps hinj
  have hT : T.card = 4 * (⌊2 * R⌋ + 1 - ⌊-(2 * R)⌋).toNat := by
    dsimp [T]
    rw [card_product,card_product,Int.card_Icc]
    simp
    ring
  have hk : (0:ℤ) ≤ ⌊2 * R⌋ + 1 - ⌊-(2 * R)⌋ := by
    have : ⌊-(2 * R)⌋ ≤ ⌊2 * R⌋ := Int.floor_mono (by linarith)
    linarith
  have hk2 : (((⌊2 * R⌋ + 1 - ⌊-(2 * R)⌋).toNat : ℕ) : ℝ) ≤ 4 * R + 2 := by
    have e : (((⌊2 * R⌋ + 1 - ⌊-(2 * R)⌋).toNat : ℕ) : ℤ) = ⌊2 * R⌋ + 1 - ⌊-(2 * R)⌋ :=
      Int.toNat_of_nonneg hk
    have e' : (((⌊2 * R⌋ + 1 - ⌊-(2 * R)⌋).toNat : ℕ) : ℝ)
        = (⌊2 * R⌋ : ℝ) + 1 - (⌊-(2 * R)⌋ : ℝ) := by exact_mod_cast e
    rw [e']
    have h1 := Int.floor_le (2 * R)
    have h2 := Int.lt_floor_add_one (-(2 * R))
    linarith
  have hn : (n : ℝ) ≤ (T.card : ℝ) := by
    rw [← hB.1]
    exact_mod_cast hcard
  rw [hT] at hn
  push_cast at hn
  linarith

theorem radius_le_diam {B : Finset ℝ²} {c : ℝ²} {R : ℝ} (hne : B.Nonempty)
    (hR : ∀ x ∈ B, dist x c = R) (hsum : ∑ x ∈ B, (x - c) = 0) :
    R ≤ Metric.diam (B : Set ℝ²) := by
  obtain ⟨x,hx⟩ := id hne
  have h0 : ∑ y ∈ B, inner ℝ (y - c) (x - c) ≤ ∑ y ∈ B, (0:ℝ) := by
    rw [← sum_inner,hsum,inner_zero_left]
    simp
  obtain ⟨y,hy,hyx⟩ := Finset.exists_le_of_sum_le hne h0
  have h1 : dist x y ^ 2 = R ^ 2 - 2 * inner ℝ (x - c) (y - c) + R ^ 2 := by
    have h1' : dist x y ^ 2
        = dist x c ^ 2 - 2 * inner ℝ (x - c) (y - c) + dist y c ^ 2 := by
      rw [dist_eq_norm,dist_eq_norm,dist_eq_norm,
        show x - y = (x - c) - (y - c) by abel,norm_sub_sq_real]
    rw [h1',hR x hx,hR y hy]
  rw [real_inner_comm] at hyx
  have h2 : R ^ 2 ≤ dist x y ^ 2 := by nlinarith [sq_nonneg R]
  exact (le_of_sq_le dist_nonneg h2).trans
    (Metric.dist_le_diam_of_mem B.finite_toSet.isBounded hx hy)

theorem nat_gap {m k : ℕ} (h : m ≠ k) : (1:ℝ) ≤ ((m:ℝ) - k) ^ 2 := by
  rcases lt_or_gt_of_ne h with h1|h1
  · have : (m:ℝ) + 1 ≤ k := by exact_mod_cast h1
    nlinarith
  · have : (k:ℝ) + 1 ≤ m := by exact_mod_cast h1
    nlinarith

theorem rows (n : ℕ) : ∃ C ∈ separatedSets n,
    Metric.diam (C : Set ℝ²) ≤ (n:ℝ) / 32 + 31 := by
  let f (i : ℕ) : ℝ² := !₂[((i / 32 : ℕ) : ℝ),((i % 32 : ℕ) : ℝ)]
  have f0 (i : ℕ) : f i 0 = ((i / 32 : ℕ) : ℝ) := rfl
  have f1 (i : ℕ) : f i 1 = ((i % 32 : ℕ) : ℝ) := rfl
  have hgap (i j : ℕ) (hij : i ≠ j) : 1 ≤ dist (f i) (f j) := by
    apply le_of_sq_le dist_nonneg
    rw [dist_sq,f0,f1,f0,f1]
    by_cases h : i / 32 = j / 32
    · have h' : i % 32 ≠ j % 32 := by omega
      nlinarith [nat_gap h',sq_nonneg (((i / 32 : ℕ) : ℝ) - ((j / 32 : ℕ) : ℝ))]
    · nlinarith [nat_gap h,sq_nonneg (((i % 32 : ℕ) : ℝ) - ((j % 32 : ℕ) : ℝ))]
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra h
    have := hgap i j h
    rw [hij,dist_self] at this
    linarith
  refine ⟨(range n).image f,⟨by rw [card_image_of_injective _ hinj,card_range],?_⟩,?_⟩
  · intro x hx y hy hxy
    obtain ⟨i,_,rfl⟩ := mem_image.mp (mem_coe.mp hx)
    obtain ⟨j,_,rfl⟩ := mem_image.mp (mem_coe.mp hy)
    change (1:ℝ≥0∞) ≤ edist (f i) (f j)
    rw [edist_dist,← ENNReal.ofReal_one,ENNReal.ofReal_le_ofReal_iff dist_nonneg]
    exact hgap i j (fun h => hxy (by rw [h]))
  · apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp (mem_coe.mp hx)
    obtain ⟨j,hj,rfl⟩ := mem_image.mp (mem_coe.mp hy)
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    apply le_of_sq_le (by positivity)
    rw [dist_sq,f0,f1,f0,f1]
    have bnd (k : ℕ) (hk : k ∈ range n) :
        (0:ℝ) ≤ ((k / 32 : ℕ) : ℝ) ∧ ((k / 32 : ℕ) : ℝ) ≤ (n:ℝ) / 32 ∧
        (0:ℝ) ≤ ((k % 32 : ℕ) : ℝ) ∧ ((k % 32 : ℕ) : ℝ) ≤ 31 := by
      refine ⟨Nat.cast_nonneg _,?_,Nat.cast_nonneg _,?_⟩
      · have h1 : ((k / 32 : ℕ) : ℝ) ≤ (k:ℝ) / 32 := by
          have := Nat.cast_div_le (α := ℝ) (m := k) (n := 32)
          simpa using this
        have h2 : (k:ℝ) ≤ n := by exact_mod_cast (mem_range.mp hk).le
        linarith
      · have : k % 32 ≤ 31 := by omega
        exact_mod_cast this
    obtain ⟨a1,a2,a3,a4⟩ := bnd i hi
    obtain ⟨b1,b2,b3,b4⟩ := bnd j hj
    have e1 : (((i / 32 : ℕ) : ℝ) - ((j / 32 : ℕ) : ℝ)) ^ 2 ≤ ((n:ℝ) / 32) ^ 2 := by
      apply sq_le_sq'
      · linarith
      · linarith
    have e2 : (((i % 32 : ℕ) : ℝ) - ((j % 32 : ℕ) : ℝ)) ^ 2 ≤ (31:ℝ) ^ 2 := by
      apply sq_le_sq'
      · linarith
      · linarith
    nlinarith

end OMA.Concyclic

theorem OMA.solution : OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1.H1 := by
  filter_upwards [eventually_ge_atTop 2000] with n hn
  obtain ⟨C,hC,hCd⟩ := OMA.Concyclic.rows n
  refine ⟨C,hC,?_⟩
  rintro B hB ⟨c,R,hR,hsum⟩
  have hne : B.Nonempty := card_pos.mp (by rw [hB.1]; omega)
  have h1 := OMA.Concyclic.card_le hB hR hne
  have h2 := OMA.Concyclic.radius_le_diam hne hR hsum
  have h3 : (2000:ℝ) ≤ n := by exact_mod_cast hn
  linarith
