import FormalConjectures.ErdosProblems.«704»
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Davies's exponential upper bound for the unit-distance graph

We discretize the trimmed-ball construction from James Davies, *Measurable
obstructions for unmeasurable colourings*, Section 10 (arXiv:2610.12301).
Rounding maps the unit-distance graph to an annulus graph on a finite torus.
We choose centres by finite averaging and bound the count of interfering
offsets by the volume of a cylinder enlarged to account for rounding.
Covering the grid by translates of the retained set yields the colouring.
-/

namespace TorusLattice

open Finset MeasureTheory Metric
open scoped BigOperators ENNReal

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev ZVec (n : ℕ) := Fin n → ℤ

def embed {n : ℕ} (z : ZVec n) : E n :=
  WithLp.toLp 2 fun i => (z i : ℝ)

noncomputable def round {n : ℕ} (x : E n) : ZVec n := fun i => ⌊x i⌋

lemma embed_add {n : ℕ} (a b : ZVec n) : embed (a + b) = embed a + embed b := by
  ext i
  simp [embed]

lemma embed_sub {n : ℕ} (a b : ZVec n) : embed (a - b) = embed a - embed b := by
  ext i
  simp [embed]

lemma norm_le_mul_card {n : ℕ} (x : E n) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ i, |x i| ≤ t) : ‖x‖ ≤ (n : ℝ) * t := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      ∑ i, ‖x i‖ ^ 2 ≤ ∑ _ : Fin n, t ^ 2 := by
        exact sum_le_sum fun i _ => pow_le_pow_left₀ (abs_nonneg (x i)) (h i) _
      _ = (n : ℝ) * t ^ 2 := by simp
      _ ≤ ((n : ℝ) * t) ^ 2 := by
        cases n with
        | zero => simp
        | succ n =>
          have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
          calc
            (↑(n + 1) : ℝ) * t ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * t ^ 2 := by
              exact mul_le_mul_of_nonneg_right (by nlinarith only [hn]) (sq_nonneg t)
            _ = _ := by ring

lemma round_error {n : ℕ} (x : E n) : ‖x - embed (round x)‖ ≤ n := by
  convert norm_le_mul_card (x - embed (round x)) (t := 1) zero_le_one ?_ using 1
  · ring
  · intro i
    change |x i - (⌊x i⌋ : ℤ)| ≤ (1 : ℝ)
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
    linarith [Int.lt_floor_add_one (x i)]

noncomputable def latticeBall (n : ℕ) (r : ℝ) : Finset (ZVec n) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin n => Finset.Icc (-⌈r⌉ : ℤ) ⌈r⌉)).filter
    (fun z => ‖embed z‖ < r)

lemma mem_latticeBall {n : ℕ} {r : ℝ} {z : ZVec n} :
    z ∈ latticeBall n r ↔ ‖embed z‖ < r := by
  classical
  simp only [latticeBall, mem_filter, Fintype.mem_piFinset, mem_Icc, and_iff_right_iff_imp]
  intro h i
  have hco := PiLp.norm_apply_le (embed z) i
  change ‖(z i : ℝ)‖ ≤ ‖embed z‖ at hco
  have habs : |(z i : ℝ)| ≤ (⌈r⌉ : ℤ) :=
    (Real.norm_eq_abs _ ▸ hco).trans (h.le.trans (Int.le_ceil _))
  obtain ⟨hl, hr⟩ := abs_le.mp habs
  exact ⟨by exact_mod_cast hl, by exact_mod_cast hr⟩

noncomputable def cube {n : ℕ} (z : ZVec n) : Set (E n) := {x | round x = z}

lemma cube_eq_preimage {n : ℕ} (z : ZVec n) :
    cube z = WithLp.ofLp ⁻¹' (Set.univ.pi (fun i => Set.Ico (z i : ℝ) (z i + 1))) := by
  ext x
  simp only [cube, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ico, funext_iff, round, Int.floor_eq_iff]

lemma cube_measurable {n : ℕ} (z : ZVec n) : MeasurableSet (cube z) := by
  rw [cube_eq_preimage]
  apply (MeasurableSet.pi (Set.to_countable _) fun _ _ => measurableSet_Ico).preimage
  exact (PiLp.volume_preserving_ofLp (Fin n)).measurable

lemma cube_volume {n : ℕ} (z : ZVec n) : volume (cube z) = 1 := by
  rw [cube_eq_preimage, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage]
  · rw [volume_pi_pi]
    simp
  · exact (MeasurableSet.pi (Set.to_countable (Set.univ : Set (Fin n)))
      (fun i _ => measurableSet_Ico (a := (z i : ℝ)) (b := (z i : ℝ) + 1))).nullMeasurableSet

noncomputable def ballCubes (n : ℕ) (r : ℝ) : Set (E n) :=
  ⋃ z ∈ latticeBall n r, cube z

lemma volume_ballCubes (n : ℕ) (r : ℝ) :
    volume (ballCubes n r) = (latticeBall n r).card := by
  classical
  rw [ballCubes, measure_biUnion_finset]
  · simp [cube_volume]
  · intro a _ b _ hab
    exact Set.disjoint_left.mpr (fun _ ha hb => hab (ha.symm.trans hb))
  · exact fun z _ => cube_measurable z

lemma ball_subset_ballCubes (n : ℕ) (r : ℝ) :
    ball (0 : E n) (r - n) ⊆ ballCubes n r := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  have herr := round_error x
  refine Set.mem_iUnion₂.mpr ⟨round x, mem_latticeBall.mpr ?_, rfl⟩
  calc
    ‖embed (round x)‖ = ‖x - (x - embed (round x))‖ := by rw [sub_sub_self]
    _ ≤ ‖x‖ + ‖x - embed (round x)‖ := norm_sub_le _ _
    _ < r := by linarith

lemma volume_real_ball {n : ℕ} {s : ℝ} (hs : 0 < s) :
    volume.real (ball (0 : E n) s) = s ^ n * volume.real (ball (0 : E n) 1) := by
  simp [measureReal_def, Measure.addHaar_ball_of_pos (volume : Measure (E n)) _ hs,
    finrank_euclideanSpace, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.le _)]

end TorusLattice

namespace TorusColouring

open Finset
open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def patch (S B : Finset G) (a : G) : Finset G := by
  classical
  exact S.filter (fun x => x - a ∈ B)

omit [Fintype G] in
lemma mem_patch {S B : Finset G} {a x : G} :
    x ∈ patch S B a ↔ x ∈ S ∧ x - a ∈ B := by
  classical
  simp [patch]

lemma sum_patch_card (S B : Finset G) :
    ∑ a : G, (patch S B a).card = S.card * B.card := by
  classical
  simp only [patch, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have h (x : G) : ∑ a : G, (if x - a ∈ B then 1 else 0 : ℕ) = B.card := by
    let e : G ≃ G := {
      toFun := fun a => x - a
      invFun := fun a => x - a
      left_inv := fun a => sub_sub_self _ _
      right_inv := fun a => sub_sub_self _ _ }
    calc
      _ = ∑ a : G, (if a ∈ B then 1 else 0 : ℕ) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = B.card := by rw [← sum_filter]; simp
  simp only [h, sum_const, smul_eq_mul]
  simp

lemma exists_patch_ge (S B C : Finset G) (hBC : B ⊆ C)
    (hS : S.Nonempty) (hC : C.Nonempty) :
    ∃ a : G, (patch S C a).Nonempty ∧
      B.card * (patch S C a).card ≤ C.card * (patch S B a).card := by
  classical
  by_contra! hc
  have hs (a : G) :
      C.card * (patch S B a).card ≤ B.card * (patch S C a).card := by
    by_cases hne : (patch S C a).Nonempty
    · exact (hc a hne).le
    · have hb : (patch S B a).card = 0 := by
        apply card_eq_zero.mpr
        have hsub : patch S B a ⊆ patch S C a := by
          intro x hx
          obtain ⟨hxs, hxb⟩ := mem_patch.mp hx
          exact mem_patch.mpr ⟨hxs, hBC hxb⟩
        exact subset_empty.mp ((not_nonempty_iff_eq_empty.mp hne) ▸ hsub)
      simp [hb]
  obtain ⟨x, hx⟩ := hS
  obtain ⟨c, hcC⟩ := hC
  have hne : (patch S C (x - c)).Nonempty := by
    refine ⟨x, mem_patch.mpr ⟨hx, ?_⟩⟩
    convert hcC using 1
    abel
  have hlt := sum_lt_sum (s := (univ : Finset G)) (fun i _ => hs i)
    ⟨x - c, mem_univ _, hc (x - c) hne⟩
  simp only [← mul_sum, sum_patch_card] at hlt
  simp only [Nat.mul_left_comm, Nat.mul_comm, lt_self_iff_false] at hlt

/-- After choosing at most k translates, the number of uncovered vertices is bounded by
the geometric decay predicted by the density of B. -/
lemma exists_covering_patches [DecidableEq G] (B : Finset G) (k : ℕ) :
    ∃ A : Finset G, A.card ≤ k ∧
      ((univ.filter (fun x : G => ∀ a ∈ A, x - a ∉ B)).card : ℝ) ≤
        (Fintype.card G : ℝ) * (1 - (B.card : ℝ) / Fintype.card G) ^ k := by
  classical
  let Gsize := Fintype.card G
  let density : ℝ := (B.card : ℝ) / Gsize
  have hG : (0 : ℝ) < Gsize := by
    exact_mod_cast Fintype.card_pos (α := G)
  have hden : 0 ≤ 1 - density := by
    dsimp [density]
    rw [sub_nonneg, div_le_iff₀ hG, one_mul]
    exact_mod_cast card_le_univ B
  change ∃ A : Finset G, A.card ≤ k ∧
      ((univ.filter (fun x : G => ∀ a ∈ A, x - a ∉ B)).card : ℝ) ≤
        (Gsize : ℝ) * (1 - density) ^ k
  induction k with
  | zero =>
    exact ⟨∅, by simp, by simp [Gsize]⟩
  | succ k ih =>
    obtain ⟨A, hAk, hdecay⟩ := ih
    let S : Finset G := univ.filter (fun x : G => ∀ a ∈ A, x - a ∉ B)
    change (S.card : ℝ) ≤ _ at hdecay
    by_cases hS : S.Nonempty
    · obtain ⟨a, _, ha⟩ := exists_patch_ge S B (univ : Finset G) (subset_univ _) hS
        ⟨0, mem_univ _⟩
      have hpat : patch S univ a = S := by
        ext x
        simp [mem_patch]
      rw [hpat, card_univ] at ha
      let P := patch S B a
      change B.card * S.card ≤ Gsize * P.card at ha
      have hSP : P ⊆ S := fun _ hx => (mem_patch.mp hx).1
      have hreal : (B.card : ℝ) * S.card ≤ Gsize * P.card := by exact_mod_cast ha
      have hP : density * S.card ≤ (P.card : ℝ) := by
        dsimp [density]
        rwa [div_mul_eq_mul_div, div_le_iff₀ hG, mul_comm (P.card : ℝ)]
      refine ⟨insert a A, (card_insert_le _ _).trans (Nat.succ_le_succ hAk), ?_⟩
      have heq : univ.filter (fun x : G => ∀ b ∈ insert a A, x - b ∉ B) = S \ P := by
        ext x
        simp only [mem_filter, mem_univ, true_and, mem_sdiff, S, P, mem_patch]
        constructor
        · intro hx
          refine ⟨fun a' ha' => hx a' (mem_insert_of_mem ha'), ?_⟩
          exact fun hc => hx a (mem_insert_self _ _) hc.2
        · rintro ⟨hx, hp⟩ a' ha'
          rcases mem_insert.mp ha' with rfl | ha'
          · exact fun hin => hp ⟨hx, hin⟩
          · exact hx a' ha'
      rw [heq, card_sdiff_of_subset hSP, Nat.cast_sub (card_le_card hSP), pow_succ, ← mul_assoc]
      calc
        _ ≤ (S.card : ℝ) * (1 - density) := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hdecay hden
    · refine ⟨A, hAk.trans (Nat.le_succ _), ?_⟩
      have hS0 := not_nonempty_iff_eq_empty.mp hS
      change (S.card : ℝ) ≤ _
      simp only [hS0, card_empty, Nat.cast_zero]
      exact mul_nonneg hG.le (pow_nonneg hden _)

lemma exists_covering_translates (B : Finset G) (k : ℕ)
    (hk : (Fintype.card G : ℝ) * (1 - (B.card : ℝ) / Fintype.card G) ^ k < 1) :
    ∃ A : Finset G, A.card ≤ k ∧ ∀ x : G, ∃ a ∈ A, x - a ∈ B := by
  classical
  obtain ⟨A, hA, hbound⟩ := exists_covering_patches B k
  refine ⟨A, hA, ?_⟩
  intro x
  by_contra! hx
  have hmem : x ∈ univ.filter (fun x : G => ∀ a ∈ A, x - a ∉ B) := by exact mem_filter.mpr ⟨mem_univ _, hx⟩
  have hpos := card_pos.mpr ⟨x, hmem⟩
  exact (not_lt_of_ge (by exact_mod_cast hpos : (1 : ℝ) ≤
    ((univ.filter (fun x : G => ∀ a ∈ A, x - a ∉ B)).card : ℝ))) (hbound.trans_lt hk)

end TorusColouring

namespace TorusLattice

open Finset MeasureTheory Metric
open scoped BigOperators ENNReal

abbrev Grid (n M : ℕ) := Fin n → ZMod M

def wrap (n M : ℕ) : ZVec n →+ Grid n M where
  toFun z i := (z i : ZMod M)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

lemma wrap_unique {n M : ℕ} {x y : ZVec n} (h : wrap n M x = wrap n M y)
    (hsize : ‖embed x - embed y‖ < (M : ℝ)) : x = y := by
  have hzero : wrap n M (x - y) = 0 := by rw [map_sub, h, sub_self]
  ext i
  have hi : (((x - y) i : ℤ) : ZMod M) = 0 := congrFun hzero i
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi
  have hnorm := (PiLp.norm_apply_le (embed x - embed y) i).trans_lt hsize
  rw [← embed_sub] at hnorm
  have habs : |((x - y) i)| < (M : ℤ) := by
    change ‖(((x - y) i : ℤ) : ℝ)‖ < (M : ℝ) at hnorm
    exact_mod_cast (Real.norm_eq_abs _ ▸ hnorm)
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd habs)

noncomputable def gridBall (n M : ℕ) (r : ℝ) : Finset (Grid n M) := by
  classical
  exact (latticeBall n r).image (wrap n M)

lemma mem_gridBall {n M : ℕ} {r : ℝ} {a : Grid n M} :
    a ∈ gridBall n M r ↔ ∃ z : ZVec n, ‖embed z‖ < r ∧ wrap n M z = a := by
  classical
  simp [gridBall, mem_latticeBall]

lemma card_gridBall {n M : ℕ} {r : ℝ} (hr : 2 * r ≤ (M : ℝ)) :
    (gridBall n M r).card = (latticeBall n r).card := by
  classical
  apply card_image_of_injOn
  intro x hx y hy hxy
  apply wrap_unique hxy
  have hx' := mem_latticeBall.mp hx
  have hy' := mem_latticeBall.mp hy
  exact (norm_sub_le _ _).trans_lt (by linarith)

lemma zero_gridBall {n M : ℕ} {r : ℝ} (hr : 0 < r) :
    0 ∈ gridBall n M r := by
  have hzero : embed (0 : ZVec n) = 0 := by ext i; simp [embed]
  exact mem_gridBall.mpr ⟨0, by simpa [hzero], map_zero _⟩

def incompatible {n M : ℕ} (D : ℝ) (x y : Grid n M) : Prop :=
  ∃ z : ZVec n, wrap n M z = y - x ∧ D - 2 * n ≤ ‖embed z‖ ∧ ‖embed z‖ ≤ D + 2 * n

lemma incompatible_symm {n M : ℕ} (D : ℝ) :
    Std.Symm (incompatible (n := n) (M := M) D) := by
  constructor
  rintro x y ⟨z, hz, hlo, hhi⟩
  have hembed : embed (-z) = -embed z := by ext i; simp [embed]
  exact ⟨-z, by rw [map_neg, hz, neg_sub], by simpa only [hembed, norm_neg] using hlo, by simpa only [hembed, norm_neg] using hhi⟩

lemma inner_compatible {n M : ℕ} {D r : ℝ} (hrD : 2 * r ≤ D - 2 * n)
    (hM : D + 2 * n + 2 * r ≤ (M : ℝ)) (a x y : Grid n M)
    (hx : x - a ∈ gridBall n M r) (hy : y - a ∈ gridBall n M r) :
    ¬ incompatible D x y := by
  obtain ⟨u, hu, hux⟩ := mem_gridBall.mp hx
  obtain ⟨v, hv, hvy⟩ := mem_gridBall.mp hy
  rintro ⟨z, hz, hlow, hhigh⟩
  have hwrap : wrap n M z = wrap n M (v - u) := by
    rw [map_sub, hvy, hux, hz]
    abel
  have hsmall : ‖embed (v - u)‖ < 2 * r := by
    rw [embed_sub]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hzu : z = v - u := wrap_unique hwrap
    ((norm_sub_le _ _).trans_lt (by linarith))
  rw [hzu] at hlow
  exact (not_lt_of_ge hlow) (hsmall.trans_le hrD)

lemma incompatible_translate {n M : ℕ} {D : ℝ} (a x y : Grid n M) :
    incompatible D (x - a) (y - a) ↔ incompatible D x y := by
  have heq : y - a - (x - a) = y - x := by abel
  simp only [incompatible, heq]

lemma round_incompatible {n M : ℕ} {D : ℝ} (hD : 0 ≤ D) (x y : E n)
    (hxy : dist x y = 1) :
    incompatible D (wrap n M (round (D • x))) (wrap n M (round (D • y))) := by
  have heq : D • y - D • x =
      (D • y - embed (round (D • y))) +
      embed (round (D • y) - round (D • x)) -
      (D • x - embed (round (D • x))) := by
    rw [embed_sub]
    abel
  have hdist : ‖D • y - D • x‖ = D := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hD, ← dist_eq_norm, dist_comm, hxy,
      mul_one]
  have hX := round_error (D • x)
  have hY := round_error (D • y)
  refine ⟨round (D • y) - round (D • x), by rw [map_sub], ?_, ?_⟩
  · have h₁ := norm_sub_le
        ((D • y - embed (round (D • y))) +
        embed (round (D • y) - round (D • x))) (D • x - embed (round (D • x)))
    rw [← heq, hdist] at h₁
    linarith only [h₁, norm_add_le (D • y - embed (round (D • y)))
      (embed (round (D • y) - round (D • x))), hX, hY]
  · have heq' : embed (round (D • y) - round (D • x)) =
        ((D • y - D • x) + (D • x - embed (round (D • x)))) -
        (D • y - embed (round (D • y))) := by
      rw [embed_sub]
      abel
    rw [heq']
    linarith only [norm_sub_le
      ((D • y - D • x) + (D • x - embed (round (D • x))))
      (D • y - embed (round (D • y))),
      norm_add_le (D • y - D • x) (D • x - embed (round (D • x))), hdist, hX, hY]

end TorusLattice

namespace TorusLattice
open Finset

lemma compatible_colourable {n M k : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (T A : Finset (Grid n M)) (hA : A.card ≤ k)
    (hT : ∀ x ∈ T, ∀ y ∈ T, ¬incompatible D x y)
    (hcover : ∀ x : Grid n M, ∃ a ∈ A, x - a ∈ T) :
    (Erdos704.unitDistanceGraph n).Colorable k := by
  classical
  choose c hcA hcT using hcover
  let colour (x : E n) : A := ⟨c (wrap n M (round (D • x))), hcA _⟩
  have hproper (x y : E n) (hxy : dist x y = 1) : colour x ≠ colour y := by
    intro h
    have heq := congrArg Subtype.val h
    change c (wrap n M (round (D • x))) = c (wrap n M (round (D • y))) at heq
    have hy : wrap n M (round (D • y)) - c (wrap n M (round (D • x))) ∈ T := by
      rw [heq]
      exact hcT _
    exact hT _ (hcT (wrap n M (round (D • x)))) _ hy
      ((incompatible_translate _ _ _).mpr (round_incompatible hD x y hxy))
  exact SimpleGraph.Colorable.mono (by simpa using hA)
    (SimpleGraph.Coloring.mk colour (fun {_ _} h => hproper _ _ h)).colorable

end TorusLattice

namespace TorusTrim

open Finset MeasureTheory Metric TorusLattice
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable def splitAxis (n : ℕ) :
    E (1 + n) ≃ₗᵢ[ℝ] WithLp 2 (E 1 × E n) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ ↦ ℝ))

lemma splitAxis_first {n : ℕ} (x : E (1 + n)) :
    (splitAxis n x).fst 0 = x 0 := by
  rfl

lemma first_norm_sq (x : E 1) : ‖x‖ ^ 2 = x 0 ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

noncomputable def alignAxis {n : ℕ}
    (b : OrthonormalBasis (Fin (1 + n)) ℝ (E (1 + n))) :
    E (1 + n) ≃ₗᵢ[ℝ] WithLp 2 (E 1 × E n) :=
  b.repr.trans (splitAxis n)

lemma alignAxis_first {n : ℕ} (b : OrthonormalBasis (Fin (1 + n)) ℝ (E (1 + n))) (z : E (1+n)) :
    (alignAxis b z).fst 0 = ⟪b 0, z⟫ := by
  change (splitAxis n (b.repr z)).fst 0 = _
  rw [splitAxis_first, b.repr_apply_apply]

lemma exists_axis_basis {n : ℕ} (t : E (1 + n)) :
    ∃ b : OrthonormalBasis (Fin (1 + n)) ℝ (E (1 + n)), t = ‖t‖ • b 0 := by
  by_cases ht : t = 0
  · exact ⟨EuclideanSpace.basisFun _ _, by simp [ht]⟩
  let u : E (1 + n) := ‖t‖⁻¹ • t
  have hn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr ht)),
      inv_mul_cancel₀ hn]
  let S : Set (Fin (1 + n)) := {0}
  let v : Fin (1 + n) → E (1 + n) := fun _ => u
  have hv : Orthonormal ℝ (S.domRestrict v) := by
    classical
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (i.property.trans j.property.symm)
    subst j
    simp [v, Set.domRestrict, hu]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp [finrank_euclideanSpace])
  refine ⟨b, ?_⟩
  rw [hb 0 (by simp [S])]
  change t = ‖t‖ • (‖t‖⁻¹ • t)
  rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

def blocks {n : ℕ} (L : ℝ) (t z : E n) : Prop :=
  ‖z‖ ^ 2 - 2 * ⟪t, z⟫ ≤ L * ‖z‖

lemma blocks_norm {n : ℕ} {L : ℝ} {t z : E n} (hL : 0 ≤ L) (ht : 2 * ‖t‖ ≤ L)
    (hz : blocks L t z) : ‖z‖ ≤ 2 * L := by
  have hinner := real_inner_le_norm t z
  by_contra! hlt
  have hmul := mul_pos (sub_pos.mpr hlt) (show 0 < ‖z‖ by linarith)
  have htm := mul_le_mul_of_nonneg_right ht (norm_nonneg z)
  unfold blocks at hz
  nlinarith only [hinner, hmul, htm, hz]

lemma geom_factor {c : ℝ} (hc : 0 ≤ c) :
    (1 + c) ^ 2 * (1 - c ^ 2) ≤ (27 : ℝ) / 16 := by
  have h : 0 ≤ (c - 1 / 2) ^ 2 * (c ^ 2 + 3 * c + 11 / 4) := by positivity
  nlinarith only [h]

lemma blocks_transverse {n : ℕ} {L : ℝ} {t z : E (1 + n)}
    (hL : 0 ≤ L) (ht : 2 * ‖t‖ ≤ L) (hz : blocks L t z)
    (b : OrthonormalBasis (Fin (1 + n)) ℝ (E (1 + n))) (hb : t = ‖t‖ • b 0) :
    ‖(alignAxis b z).snd‖ ≤ L * (3 * Real.sqrt 3 / 4) := by
  let ρ := ‖z‖
  let α := (alignAxis b z).fst 0
  let β := ‖(alignAxis b z).snd‖
  have hβ : 0 ≤ β := norm_nonneg _
  have hsq : ρ ^ 2 = α ^ 2 + β ^ 2 := by
    change ‖z‖ ^ 2 = _ + _
    nth_rewrite 1 [← (alignAxis b).norm_map z]
    rw [WithLp.prod_norm_sq_eq_of_L2, first_norm_sq]
  have htinner : ⟪t, z⟫ = ‖t‖ * α := by
    rw [show α = ⟪b 0, z⟫ from alignAxis_first b z]
    nth_rewrite 1 [hb]
    rw [real_inner_smul_left]
  have hscale : ρ ^ 2 - 2 * ‖t‖ * α ≤ L * ρ := by
    unfold blocks at hz
    rw [htinner] at hz
    linarith only [hz]
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hK : (1 : ℝ) ≤ 3 * Real.sqrt 3 / 4 := by
    by_contra! hh
    have h := mul_lt_mul_of_pos_right hh (show (0 : ℝ) < 3 * Real.sqrt 3 / 4 + 1 by positivity)
    nlinarith only [hroot, h]
  have hρ : 0 ≤ ρ := norm_nonneg _
  change β ≤ _
  rcases eq_or_lt_of_le hρ with hzero | hpos
  · have hb0 : β = 0 := by nlinarith only [hsq, hzero, sq_nonneg α]
    rw [hb0]
    positivity
  by_cases ha : α ≤ 0
  · have hρL : ρ ≤ L := by
      by_contra! hh
      have hprod := mul_pos hpos (sub_pos.mpr hh)
      have hat := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg t) ha
      nlinarith only [hprod, hat, hscale]
    have hβρ : β ≤ ρ := by
      by_contra! hh
      have hprod := mul_pos (sub_pos.mpr hh) (show 0 < β + ρ by linarith)
      nlinarith only [hprod, hsq, sq_nonneg α]
    exact hβρ.trans (hρL.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hK hL))
  let c := α / ρ
  have hc : 0 ≤ c := div_nonneg (le_of_not_ge ha) hρ
  have hαρ : α = c * ρ := (div_mul_cancel₀ _ hpos.ne').symm
  have halpha_le : α ≤ ρ := by
    by_contra! hh
    have hprod := mul_pos (sub_pos.mpr hh) (show 0 < α + ρ by linarith)
    nlinarith only [hprod, hsq, sq_nonneg β]
  have hc1 : c ≤ 1 := (div_le_iff₀ hpos).mpr (by simpa only [one_mul])
  have hρcap : ρ ≤ L * (1 + c) := by
    have h' : ρ * (ρ - 2 * ‖t‖ * c) ≤ ρ * L := by
      rw [hαρ] at hscale
      nlinarith only [hscale]
    have h'' := (mul_le_mul_iff_right₀ hpos).mp (by
      simpa only [mul_comm ρ] using h')
    have htc := mul_le_mul_of_nonneg_right ht hc
    nlinarith only [h'', htc]
  have hfactor : 0 ≤ 1 - c ^ 2 := sub_nonneg.mpr (by nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1)])
  have hβ2 : β ^ 2 = ρ ^ 2 * (1 - c ^ 2) := by
    rw [hαρ] at hsq
    nlinarith only [hsq]
  have hprod := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ hρcap 2) hfactor
  have hgeom := mul_le_mul_of_nonneg_left (geom_factor hc) (sq_nonneg L)
  have hβbound : β ^ 2 ≤ L ^ 2 * ((27 : ℝ) / 16) := by
    rw [hβ2]
    calc
      _ ≤ (L * (1 + c)) ^ 2 * (1 - c ^ 2) := hprod
      _ = L ^ 2 * ((1 + c) ^ 2 * (1 - c ^ 2)) := by ring
      _ ≤ _ := hgeom
  by_contra! hh
  have hnonneg : 0 ≤ L * (3 * Real.sqrt 3 / 4) := by positivity
  have hlt := mul_lt_mul_of_pos_right hh (show 0 < β + L * (3 * Real.sqrt 3 / 4) by linarith)
  have hconst : (L * (3 * Real.sqrt 3 / 4)) ^ 2 = L ^ 2 * ((27 : ℝ) / 16) := by
    rw [mul_pow, div_pow, mul_pow, hroot]
    norm_num
  nlinarith only [hlt, hβbound, hconst]

end TorusTrim

namespace TorusTrim

open Finset MeasureTheory Metric TorusLattice
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable def cylinder {n : ℕ} (f : E (1 + n) ≃ₗᵢ[ℝ] WithLp 2 (E 1 × E n))
    (A R : ℝ) : Set (E (1 + n)) :=
  (WithLp.ofLp ∘ ⇑f) ⁻¹' (ball 0 A ×ˢ ball 0 R)

lemma volume_cylinder_real {n : ℕ} (f : E (1 + n) ≃ₗᵢ[ℝ] WithLp 2 (E 1 × E n))
    {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    volume.real (cylinder f A R) =
      (A * R ^ n) * (volume.real (ball (0 : E 1) 1) * volume.real (ball (0 : E n) 1)) := by
  unfold cylinder
  have hp := (WithLp.volume_preserving_ofLp (E 1) (E n)).comp f.measurePreserving
  have hpre := hp.measure_preimage (isOpen_ball.prod isOpen_ball).measurableSet.nullMeasurableSet
    (s := ball (0 : E 1) A ×ˢ ball (0 : E n) R)
  rw [measureReal_def, hpre]
  change (Measure.prod volume volume (ball (0 : E 1) A ×ˢ ball (0 : E n) R)).toReal = _
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  change volume.real (ball (0 : E 1) A) * volume.real (ball (0 : E n) R) = _
  rw [volume_real_ball hA, volume_real_ball hR, pow_one]
  ring

lemma volume_ball_product_factor (n : ℕ) :
    volume.real (ball (0 : E 1) 1) * volume.real (ball (0 : E n) 1) ≤
      (4 * (1 + (n : ℝ))) * volume.real (ball (0 : E (1 + n)) 1) := by
  let p : ℝ := 1 / (2 * (1 + (n : ℝ)))
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p < 1 := by
    dsimp [p]
    rw [div_lt_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hmp : (n : ℝ) * p ≤ 1 / 2 := by
    dsimp [p]
    rw [← mul_div_assoc, mul_one, div_le_iff₀ (by positivity)]
    linarith
  have hdecay : 1 / 2 ≤ (1 - p) ^ n := by
    have hbern := one_add_mul_sub_le_pow (a := 1 - p) (by linarith : (-1 : ℝ) ≤ 1 - p) n
    nlinarith only [hmp, hbern]
  have hsubset : cylinder (splitAxis n) p (1 - p) ⊆ ball (0 : E (1 + n)) 1 := by
    intro x hx
    have hxn : ‖x‖ ^ 2 =
        ‖(splitAxis n x).fst‖ ^ 2 + ‖(splitAxis n x).snd‖ ^ 2 := by
      nth_rewrite 1 [← (splitAxis n).norm_map x]
      exact WithLp.prod_norm_sq_eq_of_L2 _
    have hf : ‖(splitAxis n x).fst‖ < p := mem_ball_zero_iff.mp hx.1
    have hs : ‖(splitAxis n x).snd‖ < 1 - p := mem_ball_zero_iff.mp hx.2
    have h₁ := pow_lt_pow_left₀ hf (norm_nonneg _) (by decide : 2 ≠ 0)
    have h₂ := pow_lt_pow_left₀ hs (norm_nonneg _) (by decide : 2 ≠ 0)
    have h₃ := mul_nonneg hp.le (le_of_lt (sub_pos.mpr hp1))
    rw [mem_ball_zero_iff]
    by_contra! h
    have hsq := one_le_pow₀ (n := 2) h
    nlinarith only [h₁, h₂, h₃, hxn, hsq]
  have hmeasure := measureReal_mono (μ := (volume : Measure (E (1 + n)))) hsubset
    measure_ball_lt_top.ne
  rw [volume_cylinder_real (splitAxis n) hp (sub_pos.mpr hp1)] at hmeasure
  let v := volume.real (ball (0 : E 1) 1) * volume.real (ball (0 : E n) 1)
  have hv : 0 ≤ v := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hlower : (p / 2) * v ≤ volume.real (ball (0 : E (1 + n)) 1) := by
    refine le_trans ?_ hmeasure
    exact mul_le_mul_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_left hdecay hp.le]) hv
  have heq : p / 2 = 1 / (4 * (1 + (n : ℝ))) := by
    dsimp [p]
    field_simp [show (1 + (n : ℝ)) ≠ 0 by positivity]
    ring
  rw [heq, one_div_mul_eq_div, div_le_iff₀ (by positivity : 0 < 4 * (1 + (n : ℝ)))] at hlower
  exact hlower.trans_eq (mul_comm _ _)

noncomputable def latticeBlockers (n : ℕ) (L : ℝ) (t : E n) : Finset (ZVec n) := by
  classical
  exact (latticeBall n (2 * L + 1)).filter (fun z => blocks L t (embed z))

lemma mem_latticeBlockers {n : ℕ} {L : ℝ} {t : E n}
    (hL : 0 ≤ L) (ht : 2 * ‖t‖ ≤ L) (z : ZVec n) :
    z ∈ latticeBlockers n L t ↔ blocks L t (embed z) := by
  classical
  simp only [latticeBlockers, mem_filter, mem_latticeBall, and_iff_right_iff_imp]
  intro hz
  linarith only [blocks_norm hL ht hz]

lemma lattice_blockers_count {n : ℕ} {L r : ℝ} {t : E (1 + n)} (hL : 0 ≤ L)
    (ht : 2 * ‖t‖ ≤ L) (hr : (1 + (n : ℝ)) < r) :
    ((latticeBlockers (1 + n) L t).card : ℝ) ≤
      4 * (1 + (n : ℝ)) * ((2 * L + 2 * (1 + (n : ℝ))) / (r - (1 + (n : ℝ)))) *
      (((3 * Real.sqrt 3 / 4) * L + 2 * (1 + (n : ℝ))) / (r - (1 + (n : ℝ)))) ^ n *
      (latticeBall (1 + n) r).card := by
  obtain ⟨b, hb⟩ := exists_axis_basis t
  let d := (1 + (n : ℝ))
  have hd : 0 < d := by dsimp [d]; positivity
  let A := 2 * L + 2 * d
  let R := (3 * Real.sqrt 3 / 4) * L + 2 * d
  let s := r - d
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hs : 0 < s := sub_pos.mpr hr
  let P : Set (E (1 + n)) := ⋃ z ∈ latticeBlockers (1 + n) L t, cube z
  have hP : volume P = (latticeBlockers (1 + n) L t).card := by
    dsimp [P]
    rw [measure_biUnion_finset]
    · simp [cube_volume]
    · intro a _ c _ hac
      exact Set.disjoint_left.mpr (fun _ ha hc => hac (ha.symm.trans hc))
    · exact fun z _ => cube_measurable z
  have hsubset : P ⊆ cylinder (alignAxis b) A R := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Set.mem_iUnion₂.mp hx
    change round x = z at hzx
    have herr := round_error x
    rw [hzx, Nat.cast_add, Nat.cast_one] at herr
    have hzb := (mem_latticeBlockers hL ht z).mp hz
    have hzn := blocks_norm hL ht hzb
    have hzt := blocks_transverse hL ht hzb b hb
    let f := alignAxis b
    have hfst : ‖(f (x - embed z)).fst‖ ≤ d :=
      (WithLp.norm_fst_le (E 1) _).trans (by rwa [f.norm_map])
    have hsnd : ‖(f (x - embed z)).snd‖ ≤ d :=
      (WithLp.norm_snd_le (E 1) _).trans (by rwa [f.norm_map])
    have hfz : ‖(f (embed z)).fst‖ ≤ 2 * L :=
      (WithLp.norm_fst_le (E 1) _).trans (by rwa [f.norm_map])
    simp only [cylinder, Set.mem_preimage, Set.mem_prod, mem_ball_zero_iff]
    change ‖(f x).fst‖ < A ∧ ‖(f x).snd‖ < R
    have hxsplit : f x = f (x - embed z) + f (embed z) := by rw [← map_add, sub_add_cancel]
    rw [hxsplit, WithLp.add_fst, WithLp.add_snd]
    constructor
    · exact (norm_add_le _ _).trans_lt (by dsimp [A]; linarith)
    · exact (norm_add_le _ _).trans_lt (by dsimp [R]; linarith only [hsnd, hzt, hd])
  have hcfin : volume (cylinder (alignAxis b) A R) ≠ ∞ := by
    have hp := (WithLp.volume_preserving_ofLp (E 1) (E n)).comp
      (alignAxis b).measurePreserving
    unfold cylinder
    rw [hp.measure_preimage
      (isOpen_ball.prod isOpen_ball).measurableSet.nullMeasurableSet]
    change Measure.prod volume volume (ball (0 : E 1) A ×ˢ ball (0 : E n) R) ≠ _
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_ball_lt_top.ne measure_ball_lt_top.ne
  have hcount := measureReal_mono (μ := (volume : Measure (E (1 + n)))) hsubset hcfin
  rw [measureReal_def, hP, ENNReal.toReal_natCast,
    volume_cylinder_real (alignAxis b) hA hR] at hcount
  let v := volume.real (ball (0 : E (1 + n)) 1)
  have hball := measureReal_mono (μ := (volume : Measure (E (1 + n))))
    (ball_subset_ballCubes (1 + n) r) (by rw [volume_ballCubes]; exact ENNReal.natCast_ne_top _)
  have hball' : s ^ (1 + n) * v ≤ (latticeBall (1 + n) r).card := by
    have heq : r - ((1 + n : ℕ) : ℝ) = s := by simp [s, d]
    rw [heq, volume_real_ball hs] at hball
    simpa only [v, measureReal_def, volume_ballCubes, ENNReal.toReal_natCast] using hball
  change ((latticeBlockers (1 + n) L t).card : ℝ) ≤
    4 * d * (A / s) * (R / s) ^ n * (latticeBall (1 + n) r).card
  calc
    _ ≤ (A * R ^ n) * (volume.real (ball (0 : E 1) 1) * volume.real (ball (0 : E n) 1)) := hcount
    _ ≤ (A * R ^ n) * (4 * d * v) :=
      mul_le_mul_of_nonneg_left (volume_ball_product_factor n) (by positivity)
    _ = 4 * d * (A / s) * (R / s) ^ n * (s ^ (1 + n) * v) := by
      rw [div_pow, pow_add, pow_one]
      field_simp [hs.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hball' (by positivity)

end TorusTrim

namespace TorusTrim

open Finset
open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def penalty (B : Finset G) (F : G → Finset G) (a b : G) : ℕ :=
  (B.filter (fun t => b - a ∈ F t)).card

lemma sum_penalty (B : Finset G) (F : G → Finset G) (a : G) :
    (∑ b : G, penalty B F a b) = ∑ t ∈ B, (F t).card := by
  simp only [penalty, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun t _ => ?_)
  let e : G ≃ G := {
    toFun := fun b => b - a
    invFun := fun b => b + a
    left_inv := fun b => sub_add_cancel b a
    right_inv := fun b => add_sub_cancel_right b a }
  calc
    _ = ∑ b : G, (if b ∈ F t then 1 else 0 : ℕ) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by rw [← sum_filter]; simp

lemma sum_penalty_rev (B : Finset G) (F : G → Finset G) (a : G) :
    (∑ b : G, penalty B F b a) = ∑ t ∈ B, (F t).card := by
  simp only [penalty, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun t _ => ?_)
  let e : G ≃ G := {
    toFun := fun b => a - b
    invFun := fun b => a - b
    left_inv := fun b => sub_sub_self a b
    right_inv := fun b => sub_sub_self a b }
  calc
    _ = ∑ b : G, (if b ∈ F t then 1 else 0 : ℕ) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by rw [← sum_filter]; simp

def debt {k : ℕ} (B : Finset G) (F : G → Finset G) (f : Fin k → G) : ℕ :=
  ∑ i, ∑ j, if i = j then 0 else penalty B F (f i) (f j)

omit [Fintype G] in
lemma debt_snoc {k : ℕ} (B : Finset G) (F : G → Finset G) (f : Fin k → G) (a : G) :
    debt B F (Fin.snoc f a) =
      debt B F f + ∑ i, (penalty B F (f i) a + penalty B F a (f i)) := by
  have hlast (i : Fin k) : Fin.last k ≠ i.castSucc := (Fin.castSucc_ne_last _).symm
  rw [debt, Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_inj,
    Fin.castSucc_ne_last, hlast, if_false, if_true, sum_add_distrib]
  rw [debt]
  omega

lemma exists_small_increment {k : ℕ} (B : Finset G) (F : G → Finset G) (f : Fin k → G) :
    ∃ a : G, Fintype.card G * (∑ i, (penalty B F (f i) a + penalty B F a (f i))) ≤
      2 * k * ∑ t ∈ B, (F t).card := by
  let N := Fintype.card G
  let Z := ∑ t ∈ B, (F t).card
  by_contra! hc
  have h := sum_lt_sum_of_nonempty (univ_nonempty : (univ : Finset G).Nonempty) (fun a _ => hc a)
  change (∑ _ : G, 2 * k * Z) < ∑ a : G,
    N * ∑ i, (penalty B F (f i) a + penalty B F a (f i)) at h
  rw [sum_const, card_univ, smul_eq_mul, ← mul_sum, sum_comm (s := (univ : Finset G))] at h
  simp only [sum_add_distrib (s := (univ : Finset G)), sum_penalty, sum_penalty_rev] at h
  change N * (2 * k * Z) < N * (∑ _ : Fin k, (Z + Z)) at h
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  have heq : 2 * k * Z = k * (Z + Z) := by ring
  exact (lt_irrefl _) (heq ▸ h)

lemma exists_low_debt (B : Finset G) (F : G → Finset G) (k : ℕ) :
    ∃ f : Fin k → G, Fintype.card G * debt B F f ≤ k * (k - 1) * ∑ t ∈ B, (F t).card := by
  induction k with
  | zero => exact ⟨fun _ => 0, by simp [debt]⟩
  | succ k ih =>
    obtain ⟨f, hf⟩ := ih
    obtain ⟨a, ha⟩ := exists_small_increment B F f
    refine ⟨Fin.snoc f a, ?_⟩
    rw [debt_snoc, Nat.mul_add, Nat.add_sub_cancel]
    refine (Nat.add_le_add hf ha).trans_eq ?_
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]
      ring

def kept {k : ℕ} (B : Finset G) (F : G → Finset G) (f : Fin k → G) : Finset (Fin k × G) :=
  (univ ×ˢ B).filter (fun p => ∀ j : Fin k, j ≠ p.1 → f j - f p.1 ∉ F p.2)

omit [Fintype G] in
lemma mem_kept {k : ℕ} (B : Finset G) (F : G → Finset G) (f : Fin k → G)
    (i : Fin k) (t : G) : (i,t) ∈ kept B F f ↔
      t ∈ B ∧ ∀ j : Fin k, j ≠ i → f j - f i ∉ F t := by
  simp [kept]

omit [Fintype G] in
lemma kept_card_add_debt {k : ℕ} (B : Finset G) (F : G → Finset G) (f : Fin k → G) :
    k * B.card ≤ (kept B F f).card + debt B F f := by
  let bad := (univ ×ˢ B).filter (fun p : Fin k × G =>
    ¬∀ j : Fin k, j ≠ p.1 → f j - f p.1 ∉ F p.2)
  let cut (i j : Fin k) := if i = j then ∅ else
    (B.filter (fun t => f j - f i ∈ F t)).map
      (⟨fun t => (i,t), fun _ _ h => (Prod.mk.inj h).2⟩ : G ↪ Fin k × G)
  have hcover : bad ⊆ univ.biUnion (fun i => univ.biUnion (cut i)) := by
    rintro ⟨i,t⟩ hp
    have ht : t ∈ B := (mem_product.mp (mem_filter.mp hp).1).2
    obtain ⟨j, hj, hf⟩ := not_forall.mp (mem_filter.mp hp).2 |>.imp
      (fun j hj => by
        push Not at hj
        exact hj)
    refine mem_biUnion.mpr ⟨i, mem_univ _, mem_biUnion.mpr ⟨j, mem_univ _, ?_⟩⟩
    simp only [cut, if_neg (Ne.symm hj), mem_map]
    exact ⟨t, mem_filter.mpr ⟨ht, hf⟩, rfl⟩
  have hbound : bad.card ≤ debt B F f := by
    calc
      _ ≤ (univ.biUnion (fun i => univ.biUnion (cut i))).card := card_le_card hcover
      _ ≤ ∑ i, (univ.biUnion (cut i)).card := card_biUnion_le
      _ ≤ ∑ i, ∑ j, (cut i j).card := sum_le_sum fun _ _ => card_biUnion_le
      _ = debt B F f := by
        simp only [debt, cut, penalty]
        congr with i
        congr with j
        split <;> simp
  have hsplit : (kept B F f).card + bad.card = (univ ×ˢ B).card :=
    card_filter_add_card_filter_not _
  rw [card_product, card_univ, Fintype.card_fin] at hsplit
  omega

lemma exists_dense_trim (B : Finset G) (F : G → Finset G) (w : ℕ) (hw : 0 < w)
    (hbound : ∀ t ∈ B, (F t).card ≤ w) (bad : G → G → Prop)
    (hinj : ∀ {k : ℕ} (f : Fin k → G),
      Set.InjOn (fun p : Fin k × G => p.2 + f p.1) (kept B F f : Set (Fin k × G)))
    (hcompat : ∀ {k : ℕ} (f : Fin k → G) (p q : Fin k × G),
      p ∈ kept B F f → q ∈ kept B F f → ¬bad (p.2 + f p.1) (q.2 + f q.1)) :
    ∃ T : Finset G, (∀ x ∈ T, ∀ y ∈ T, ¬bad x y) ∧
      Fintype.card G * B.card ≤ 4 * w * T.card := by
  let N := Fintype.card G
  let k := N / (2 * w) + 1
  have hN : 0 < N := Fintype.card_pos
  have h2w : 0 < 2 * w := by positivity
  have hsum : (∑ t ∈ B, (F t).card) ≤ B.card * w := by
    simpa only [sum_const, smul_eq_mul] using
      (sum_le_sum (s := B) (g := fun _ => w) hbound)
  have hk : (k - 1) * (2 * w) ≤ N := by
    simpa only [k, Nat.add_sub_cancel] using Nat.div_mul_le_self N (2 * w)
  have hk' : N ≤ k * (2 * w) := by
    exact (Nat.div_lt_iff_lt_mul h2w).mp (by simp [k]) |>.le
  obtain ⟨f, hf⟩ := exists_low_debt B F k
  let U := kept B F f
  have hf' : N * (2 * debt B F f) ≤ N * (k * B.card) := by
    calc
      _ = 2 * (N * debt B F f) := by ring
      _ ≤ 2 * (k * (k - 1) * (∑ t ∈ B, (F t).card)) := Nat.mul_le_mul_left _ hf
      _ ≤ 2 * (k * (k - 1) * (B.card * w)) := by gcongr
      _ = ((k - 1) * (2 * w)) * (k * B.card) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hk
  have hdebt : 2 * debt B F f ≤ k * B.card := Nat.le_of_mul_le_mul_left hf' hN
  have hsize : k * B.card ≤ 2 * U.card := by
    have := kept_card_add_debt B F f
    change k * B.card ≤ U.card + debt B F f at this
    omega
  let c (p : Fin k × G) := p.2 + f p.1
  let T := U.image c
  refine ⟨T, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hy
    exact hcompat f p q hp hq
  · have hcard : T.card = U.card := card_image_of_injOn (hinj f)
    rw [hcard]
    calc
      _ ≤ (k * (2 * w)) * B.card := Nat.mul_le_mul_right _ hk'
      _ = (2 * w) * (k * B.card) := by ring
      _ ≤ (2 * w) * (2 * U.card) := Nat.mul_le_mul_left _ hsize
      _ = _ := by ring

end TorusTrim

namespace TorusTrim

open Finset MeasureTheory Metric TorusLattice
open scoped BigOperators ENNReal RealInnerProductSpace

lemma embed_neg {n : ℕ} (z : ZVec n) : embed (-z) = -embed z := by
  ext i
  simp [embed]

lemma embed_zero {n : ℕ} : embed (0 : ZVec n) = 0 := by
  ext i
  simp [embed]

noncomputable def lift {n M : ℕ} (r : ℝ) (a : Grid n M) : ZVec n := by
  classical
  exact if h : a ∈ gridBall n M r then (mem_gridBall.mp h).choose else 0

lemma lift_spec {n M : ℕ} {r : ℝ} {a : Grid n M} (ha : a ∈ gridBall n M r) :
    ‖embed (lift r a)‖ < r ∧ wrap n M (lift r a) = a := by
  classical
  simpa only [lift, dif_pos ha] using (mem_gridBall.mp ha).choose_spec

noncomputable def blockingOffsets {n M : ℕ} (L r : ℝ) (a : Grid n M) : Finset (Grid n M) := by
  classical
  exact (latticeBlockers n L (embed (lift r a))).image (wrap n M)

lemma block_mem {n M : ℕ} {L r : ℝ} (hL : 0 ≤ L) (h2r : 2 * r ≤ L)
    {a : Grid n M} (ha : a ∈ gridBall n M r) {z : ZVec n}
    (hz : blocks L (embed (lift r a)) (embed z)) :
    wrap n M z ∈ blockingOffsets L r a := by
  classical
  have ht := (lift_spec ha).1
  have ht' : 2 * ‖embed (lift r a)‖ ≤ L := by linarith
  exact mem_image.mpr ⟨z, (mem_latticeBlockers hL ht' z).mpr hz, rfl⟩

lemma zero_blocker {n M : ℕ} {L r : ℝ} (hL : 0 ≤ L) (h2r : 2 * r ≤ L)
    {a : Grid n M} (ha : a ∈ gridBall n M r) :
    0 ∈ blockingOffsets L r a := by
  have hz : blocks L (embed (lift r a)) (embed (0 : ZVec n)) := by
    simp [blocks, embed_zero]
  simpa only [map_zero] using block_mem hL h2r ha hz

lemma retained_separation {n M k : ℕ} [NeZero M] {L r : ℝ}
    (hL : 0 ≤ L) (h2r : 2 * r ≤ L) (f : Fin k → Grid n M) (p q : Fin k × Grid n M)
    (hp : p ∈ kept (gridBall n M r) (blockingOffsets L r) f)
    (hq : q ∈ kept (gridBall n M r) (blockingOffsets L r) f)
    (hpq : p.1 ≠ q.1) (w : ZVec n)
    (hw : wrap n M w = (q.2 + f q.1) - (p.2 + f p.1)) :
    L < ‖embed w‖ := by
  classical
  obtain ⟨hpB, hpK⟩ := (mem_kept _ _ _ _ _).mp hp
  obtain ⟨hqB, hqK⟩ := (mem_kept _ _ _ _ _).mp hq
  let u := lift r p.2
  let v := lift r q.2
  have hu : wrap n M u = p.2 := (lift_spec hpB).2
  have hv : wrap n M v = q.2 := (lift_spec hqB).2
  let z := w + u - v
  have hwrap : wrap n M z = f q.1 - f p.1 := by
    dsimp [z]
    rw [map_sub, map_add, hw, hu, hv]
    abel
  have hn₁ : ¬ blocks L (embed u) (embed z) := by
    intro hb
    exact hpK q.1 hpq.symm (hwrap ▸ block_mem hL h2r hpB hb)
  have hn₂ : ¬ blocks L (embed v) (embed (-z)) := by
    intro hb
    have h := block_mem hL h2r hqB hb
    rw [map_neg, hwrap, neg_sub] at h
    exact hqK p.1 hpq h
  have heq : embed w = embed z - embed u + embed v := by
    dsimp [z]
    rw [embed_sub, embed_add]
    abel
  have hinner : ⟪embed w, embed z⟫ =
      ‖embed z‖ ^ 2 - ⟪embed u, embed z⟫ + ⟪embed v, embed z⟫ := by
    nth_rewrite 1 [heq]
    rw [inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
  have hnot₁ := lt_of_not_ge hn₁
  change L * ‖embed z‖ < ‖embed z‖ ^ 2 - 2 * ⟪embed u, embed z⟫ at hnot₁
  unfold blocks at hn₂
  rw [embed_neg, norm_neg, inner_neg_right] at hn₂
  have hnot₂ := lt_of_not_ge hn₂
  have hstrict : L * ‖embed z‖ < ⟪embed w, embed z⟫ := by linarith only [hnot₁, hnot₂, hinner]
  by_contra! hh
  exact (not_le_of_gt hstrict)
    ((real_inner_le_norm (embed w) (embed z)).trans
      (mul_le_mul_of_nonneg_right hh (norm_nonneg _)))

lemma retained_inj {n M k : ℕ} [NeZero M] {L r : ℝ}
    (hL : 0 ≤ L) (h2r : 2 * r ≤ L) (f : Fin k → Grid n M) :
    Set.InjOn (fun p : Fin k × Grid n M => p.2 + f p.1)
      (kept (gridBall n M r) (blockingOffsets L r) f : Set (Fin k × Grid n M)) := by
  classical
  intro p hp q hq heq
  change p.2 + f p.1 = q.2 + f q.1 at heq
  have hidx : p.1 = q.1 := by
    by_contra! h
    have hz : wrap n M (0 : ZVec n) = (q.2 + f q.1) - (p.2 + f p.1) := by
      rw [heq, sub_self, map_zero]
    have contra := retained_separation hL h2r f p q hp hq h 0 hz
    simp only [embed_zero, norm_zero] at contra
    exact hL.not_gt contra
  have hv : p.2 = q.2 := by exact add_right_cancel (hidx ▸ heq)
  exact Prod.ext hidx hv

lemma retained_compatible {n M k : ℕ} [NeZero M] {D r : ℝ}
    (hD : 0 ≤ D) (h2r : 2 * r ≤ D - 2 * n)
    (hM : D + 2 * n + 2 * r ≤ (M : ℝ)) (f : Fin k → Grid n M)
    (p q : Fin k × Grid n M)
    (hp : p ∈ kept (gridBall n M r) (blockingOffsets (D + 2 * n) r) f)
    (hq : q ∈ kept (gridBall n M r) (blockingOffsets (D + 2 * n) r) f) :
    ¬ incompatible D (p.2 + f p.1) (q.2 + f q.1) := by
  classical
  by_cases hi : p.1 = q.1
  · apply inner_compatible h2r hM (f p.1)
    · simpa only [add_sub_cancel_right] using ((mem_kept _ _ _ _ _).mp hp).1
    · rw [hi, add_sub_cancel_right]
      exact ((mem_kept _ _ _ _ _).mp hq).1
  · rintro ⟨w, hw, _, hhi⟩
    exact hhi.not_gt (retained_separation (by positivity) (by linarith) f p q hp hq hi w hw)

end TorusTrim

namespace TorusTrim

open Finset MeasureTheory Metric TorusLattice Filter
open scoped BigOperators ENNReal Topology

noncomputable def transverseConstant : ℝ := 3 * Real.sqrt 3 / 4

noncomputable def sharpRatio (H : ℕ) : ℝ :=
  (transverseConstant * (H + 2) + 2) / ((H : ℝ) / 2 - 3)

noncomputable def sharpBudget (H n : ℕ) : ℕ :=
  ⌈(8 * (H : ℝ) * n ^ 2 + 1) * (384 * (n : ℝ) * sharpRatio H ^ n)⌉₊

lemma transverse_ge_one : (1 : ℝ) ≤ transverseConstant := by
  unfold transverseConstant
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  by_contra! h
  have hprod := mul_lt_mul_of_pos_right h (show (0 : ℝ) < 3 * Real.sqrt 3 / 4 + 1 by positivity)
  nlinarith only [hprod, hsq]

lemma sharpRatio_one_lt (H : ℕ) (hH : (8 : ℝ) ≤ H) : 1 < sharpRatio H := by
  unfold sharpRatio
  have hs : 0 < (H : ℝ) / 2 - 3 := by linarith
  rw [lt_div_iff₀ hs, one_mul]
  nlinarith only [mul_le_mul_of_nonneg_right transverse_ge_one
    (show 0 ≤ (H : ℝ) + 2 by positivity), hH]

lemma colourable_of_density {n M : ℕ} [NeZero M] {D P : ℝ}
    (hD : 0 ≤ D) (T : Finset (Grid n M))
    (hT : ∀ x ∈ T, ∀ y ∈ T, ¬incompatible D x y)
    (hP : 1 ≤ P * ((T.card : ℝ) / Fintype.card (Grid n M))) :
    (Erdos704.unitDistanceGraph n).Colorable ⌈((n : ℝ) * M + 1) * P⌉₊ := by
  let N := Fintype.card (Grid n M)
  let density : ℝ := (T.card : ℝ) / N
  let L : ℝ := (n : ℝ) * M + 1
  let k := ⌈L * P⌉₊
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hNr : (N : ℝ) = (M : ℝ) ^ n := by simp [N, ZMod.card]
  have hN : (0 : ℝ) < N := by rw [hNr]; positivity
  have hdnonneg : 0 ≤ 1 - density := by
    dsimp [density]
    rw [sub_nonneg, div_le_iff₀ hN, one_mul]
    exact_mod_cast card_le_univ T
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hk : L * P ≤ (k : ℝ) := Nat.le_ceil _
  have hkD : L ≤ density * k := by
    have hp : 0 ≤ density := by dsimp [density]; positivity
    calc
      L = L * 1 := by ring
      _ ≤ L * (P * density) := mul_le_mul_of_nonneg_left hP hL
      _ = density * (L * P) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hp
  have hlog : (n : ℝ) * Real.log M < L := by
    dsimp [L]
    nlinarith only [mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hM0)
      (Nat.cast_nonneg (α := ℝ) n), Nat.cast_nonneg (α := ℝ) n]
  have hdecay : (N : ℝ) * (1 - density) ^ k < 1 := by
    have hminor : 1 - density ≤ Real.exp (-density) := by
      have := Real.add_one_le_exp (-density)
      linarith
    calc
      _ ≤ (N : ℝ) * (Real.exp (-density)) ^ k := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdnonneg hminor _) hN.le
      _ = Real.exp ((n : ℝ) * Real.log M - density * k) := by
        rw [hNr]
        nth_rewrite 1 [← Real.exp_log hM0]
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ < 1 := by rw [← Real.exp_zero, Real.exp_lt_exp]; linarith
  obtain ⟨A, hA, hcover⟩ := TorusColouring.exists_covering_translates T k hdecay
  exact compatible_colourable hD T A hA hT hcover

lemma grid_colourable_sharp (H m : ℕ) (hH : (8 : ℝ) ≤ H) :
    (Erdos704.unitDistanceGraph (1 + m)).Colorable (sharpBudget H (1 + m)) := by
  classical
  let n := 1 + m
  let M := 8 * H * n
  let D : ℝ := H * n
  let r : ℝ := ((H : ℝ) / 2 - 2) * n
  let L : ℝ := D + 2 * n
  let q := sharpRatio H
  have hn : (0 : ℝ) < n := by dsimp [n]; positivity
  have hHr : (0 : ℝ) < H := by linarith
  have hMr : (M : ℝ) = 8 * H * n := by dsimp [M]; push_cast; ring
  have hM0 : (0 : ℝ) < M := by rw [hMr]; positivity
  let : NeZero M := ⟨by exact_mod_cast hM0.ne'⟩
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hrn : (n : ℝ) < r := by
    dsimp [r]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hH) hn.le, hn]
  have hr : 0 < r := hn.trans hrn
  have h2r : 2 * r ≤ D - 2 * n := by dsimp [r, D]; linarith
  have hDM : D + 2 * n + 2 * r ≤ (M : ℝ) := by
    rw [hMr]
    dsimp [D, r]
    nlinarith [mul_nonneg hHr.le hn.le]
  have hrM : 2 * r ≤ (M : ℝ) := by linarith
  have hrL : 2 * r ≤ L := by dsimp [L]; linarith
  let B := gridBall n M r
  let F := blockingOffsets (n := n) (M := M) L r
  let w := B.sup (fun t => (F t).card)
  have hB0 : 0 ∈ B := zero_gridBall hr
  have hBound (t : Grid n M) (ht : t ∈ B) : (F t).card ≤ w := le_sup (f := fun a => (F a).card) ht
  have hw : 0 < w := (card_pos.mpr ⟨0, zero_blocker hL hrL hB0⟩).trans_le (hBound 0 hB0)
  let P : ℝ := 384 * (n : ℝ) * q ^ n
  have hq : 1 < q := sharpRatio_one_lt H hH
  have hwB : (w : ℝ) ≤ (P / 4) * B.card := by
    obtain ⟨t, ht, htw⟩ := B.exists_mem_eq_sup ⟨0, hB0⟩ (fun t => (F t).card)
    have htr := (lift_spec ht).1
    have htn : 2 * ‖embed (lift r t)‖ ≤ L := by linarith
    have hc₁ : ((2 * L + 2 * n) / (r - n)) ≤ 24 := by
      rw [div_le_iff₀ (sub_pos.mpr hrn)]
      dsimp [L, D, r]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hH) hn.le, hn]
    have hc₂ : (transverseConstant * L + 2 * n) / (r - n) = q := by
      have hd : 0 < (H : ℝ) / 2 - 3 := by linarith
      apply (div_eq_div_iff (sub_pos.mpr hrn).ne' hd.ne').mpr
      dsimp [q, sharpRatio, L, D, r]
      ring
    have hcount := lattice_blockers_count (n := m) hL htn
      (show 1 + (m : ℝ) < r by simpa only [n, Nat.cast_add, Nat.cast_one] using hrn)
    have hncast : (1 + (m : ℝ)) = (n : ℝ) := by simp [n]
    rw [hncast] at hcount
    change ((latticeBlockers n L (embed (lift r t))).card : ℝ) ≤
      4 * n * ((2 * L + 2 * n) / (r - n)) *
      ((transverseConstant * L + 2 * n) / (r - n)) ^ m * (latticeBall n r).card at hcount
    rw [hc₂] at hcount
    have hcard : (F t).card ≤ (latticeBlockers n L (embed (lift r t))).card :=
      card_image_le
    have hBcard : B.card = (latticeBall n r).card := card_gridBall hrM
    rw [show w = (F t).card from htw, hBcard]
    calc
      _ ≤ ((latticeBlockers n L (embed (lift r t))).card : ℝ) := by exact_mod_cast hcard
      _ ≤ 4 * n * ((2 * L + 2 * n) / (r - n)) * q ^ m * (latticeBall n r).card := hcount
      _ ≤ 4 * n * 24 * q ^ m * (latticeBall n r).card := by gcongr
      _ ≤ 4 * n * 24 * q ^ n * (latticeBall n r).card := by
        have he : q ^ m ≤ q ^ n := pow_le_pow_right₀ hq.le (Nat.le_add_left _ _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity))
          (by positivity)
      _ = _ := by dsimp [P]; ring
  obtain ⟨T, hT, hsize⟩ := exists_dense_trim B F w hw hBound (incompatible D)
    (retained_inj hL hrL) (retained_compatible hD h2r hDM)
  let N := Fintype.card (Grid n M)
  have hN : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos (α := Grid n M)
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast card_pos.mpr ⟨0, hB0⟩
  have hreal : (N : ℝ) * B.card ≤ 4 * (w : ℝ) * T.card := by exact_mod_cast hsize
  have hP : 1 ≤ P * ((T.card : ℝ) / N) := by
    rw [← mul_div_assoc, le_div_iff₀ hN, one_mul]
    have hub : (N : ℝ) * B.card ≤ (P * (T.card : ℝ)) * B.card := by
      calc
        _ ≤ 4 * (w : ℝ) * (T.card : ℝ) := hreal
        _ ≤ 4 * ((P / 4) * B.card) * (T.card : ℝ) := by gcongr
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ hBpos).mp (by nlinarith only [hub])
  have h := colourable_of_density hD T hT hP
  change (Erdos704.unitDistanceGraph n).Colorable (sharpBudget H n)
  have hm : (n : ℝ) * M + 1 = 8 * (H : ℝ) * (n : ℝ) ^ 2 + 1 := by rw [hMr]; ring
  simpa only [hm, sharpBudget, P, q] using h

lemma eventually_sharp_budget (H : ℕ) {C : ℝ} (hH : (8 : ℝ) ≤ H) (hC : sharpRatio H < C) :
    ∀ᶠ n : ℕ in atTop, (sharpBudget H n : ℝ) ≤ C ^ n := by
  let q := sharpRatio H
  let K : ℝ := 384 * (8 * (H : ℝ) + 1) + 1
  have hq : 1 < q := sharpRatio_one_lt H hH
  have hCp : 0 < C := by linarith
  have hqc : q / C < 1 := (div_lt_iff₀ hCp).2 (by simpa [q] using hC)
  have htend := (tendsto_pow_const_mul_const_pow_of_lt_one 3
    (by positivity : 0 ≤ q / C) hqc).const_mul K
  have hsmall : ∀ᶠ n : ℕ in atTop, K * ((n : ℝ) ^ 3 * (q / C) ^ n) < 1 :=
    htend.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hnp
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hnp
  have hq1 : 1 ≤ q ^ n := one_le_pow₀ hq.le
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hnr
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hnr
  have hk := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ (8 * (H : ℝ) * n ^ 2 + 1) * (384 * (n : ℝ) * q ^ n))).le
  have hs : K * (n : ℝ) ^ 3 * q ^ n < C ^ n := by
    rw [div_pow, ← mul_div_assoc, ← mul_div_assoc] at hn
    simpa only [one_mul, ← mul_assoc] using (div_lt_iff₀ (pow_pos hCp n)).mp hn
  calc
    (sharpBudget H n : ℝ) ≤ (8 * (H : ℝ) * n ^ 2 + 1) * (384 * (n : ℝ) * q ^ n) + 1 := hk
    _ ≤ (8 * (H : ℝ) * n ^ 2 + (n : ℝ) ^ 2) * (384 * (n : ℝ) * q ^ n) +
          (n : ℝ) ^ 3 * q ^ n := by
      have h := one_le_mul_of_one_le_of_one_le hn3 hq1
      gcongr
    _ = K * (n : ℝ) ^ 3 * q ^ n := by dsimp [K]; ring
    _ ≤ C ^ n := hs.le

lemma davies_bound (C : ℝ) (hC : 3 * Real.sqrt 3 / 2 < C) :
    ∀ᶠ n : ℕ in atTop,
      ∃ k : ℕ, (Erdos704.unitDistanceGraph n).Colorable k ∧ (k : ℝ) ≤ C ^ n := by
  have hc : 0 < C - 2 * transverseConstant := by dsimp [transverseConstant]; linarith
  obtain ⟨H, hH⟩ := exists_nat_gt
    (8 + 2 * ((8 * transverseConstant + 2) / (C - 2 * transverseConstant)))
  have hne : 0 < (8 * transverseConstant + 2) / (C - 2 * transverseConstant) := by
    apply div_pos _ hc
    linarith only [transverse_ge_one]
  have hH8 : (8 : ℝ) ≤ H := by linarith
  have hq : sharpRatio H < C := by
    have hlarge : (8 * transverseConstant + 2) / (C - 2 * transverseConstant) < (H : ℝ) / 2 - 3 := by
      linarith
    have hb := (div_lt_iff₀ hc).mp hlarge
    unfold sharpRatio
    rw [div_lt_iff₀ (by linarith : 0 < (H : ℝ) / 2 - 3)]
    nlinarith only [hb]
  filter_upwards [eventually_sharp_budget H hH8 hq, eventually_gt_atTop 0] with n hn hnp
  refine ⟨sharpBudget H n, ?_, hn⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnp)
  rw [show m.succ = 1 + m by omega]
  exact grid_colourable_sharp H m hH8

end TorusTrim

namespace TorusLattice

open Filter
open scoped Topology

lemma conjectured_base_gap :
    (3 : ℝ) * Real.sqrt 3 / 2 < (2 : ℝ) ^ ((3 : ℝ) / 2) := by
  rw [show (3 : ℝ) / 2 = 1 + (1 / 2 : ℝ) by norm_num, Real.rpow_add (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h₁ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  by_contra! hh
  have hmul := mul_le_mul hh hh (by positivity) (by positivity)
  nlinarith only [h₁, h₂, hmul]

lemma refute_limit_of_upper
    (hupper : ∀ C > 3 * Real.sqrt 3 / 2, ∀ᶠ n : ℕ in atTop,
      ∃ k : ℕ, (Erdos704.unitDistanceGraph n).Colorable k ∧ (k : ℝ) ≤ C ^ n) :
    ¬ Tendsto
      (fun n : ℕ ↦ ((Erdos704.unitDistanceGraph n).chromaticNumber.toNat : ℝ) ^
        (1 / (n : ℝ))) atTop (𝓝 ((2 : ℝ) ^ ((3 : ℝ) / 2))) := by
  intro hlim
  obtain ⟨C, hC, hCtop⟩ := exists_between conjectured_base_gap
  have hCp : 0 < C := (by positivity : 0 < 3 * Real.sqrt 3 / 2).trans hC
  have hub := hupper C hC
  have hbound : ∀ᶠ n : ℕ in atTop,
      ((Erdos704.unitDistanceGraph n).chromaticNumber.toNat : ℝ) ^ (1 / (n : ℝ)) ≤ C := by
    filter_upwards [hub, eventually_gt_atTop 0] with n hn hnpos
    obtain ⟨k, hk, hc⟩ := hn
    have hcast : ((Erdos704.unitDistanceGraph n).chromaticNumber.toNat : ℝ) ≤ k := by
      exact_mod_cast ENat.toNat_le_toNat hk.chromaticNumber_le (ENat.natCast_ne_top k)
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    calc
      _ ≤ (C ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (by positivity) (hcast.trans hc) (by positivity)
      _ = C := by
        rw [← Real.rpow_natCast_mul hCp.le, mul_one_div_cancel hnr.ne', Real.rpow_one]
  exact hCtop.not_ge (le_of_tendsto hlim hbound)

end TorusLattice

theorem OMA.solution : type_of% @Erdos704.erdos_704.variants.larman_rogers_conjecture :=
  TorusLattice.refute_limit_of_upper TorusTrim.davies_bound