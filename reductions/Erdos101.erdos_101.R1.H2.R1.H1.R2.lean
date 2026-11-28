import OMAReductions.R_Erdos101_erdos_101_R1_H2_R1

/-!
# Quadruple-energy reduction for four-point lines on a higher-degree irreducible curve

Reduction of `Erdos101.erdos_101.R1.H2.R1.H1` (the single-component quadruple-line bound for
irreducible curves `F` of degree `4 <= deg(F) <= d`) following the quadruple-incidence framework
of Raz, Sharir, and de Zeeuw (2016) / Elekes and Szabo (2013).

Given `S subseteq Z(F)` with `S.card <= n` and `NonCollinearFor 5 (S : Set R^2)`:
1. Selecting one ordered triple `(x_L, y_L, z_L)` on each four-point line `L` gives an injective
   family `T` of collinear triples with `T.card = (linesWithPointsFor 4 S).ncard`.
2. Grouping by the third point `z in S` and applying Cauchy-Schwarz yields
   `T.card^2 <= n * (T.card + Q.card)`, where `Q subseteq (S x S) x (S x S)` counts non-degenerate
   collinear quadruples `((x, x'), (y, y'))` whose distinct lines `line[R, x, y] != line[R, x', y']`
   meet at a point `z in S` (which is uniquely determined by the two distinct lines).
3. Using `NonCollinearFor 5 S`, every fixed pair `(y, y') in S x S` has at most `4 * S.card`
   quadruple neighbors `(x, x') in S x S`: for each `z in S`, `line[R, y, z]` holds at most two
   points of `S \ {y, z}` and `line[R, y', z]` holds at most two points of `S \ {y', z}`.
   Hence any exceptional set `Bad subseteq S x S` of size `<= eta * n^2` contributes at most
   `4 * eta * n^3` quadruple incidences.

This cleanly separates the algebraic curve-rigidity half from the real incidence-geometry half:
- `H1` (Algebraic correspondence rigidity for `deg(F) >= 4`): outside an exceptional set `Bad`
  of size `<= eta * n^2`, every good pair `v in (S x S) \ Bad` shares more than `M(d)` common
  quadruple neighbors with at most `M(d)` other good pairs.
- `H2` (Real curve-surface incidence bound): any bounded-overlap family `Good subseteq S x S`
  of correspondence curves on `Z(F) x Z(F)` has at most `eta * n^3` quadruple incidences with
  `S x S` for sufficiently large `n`.
-/

namespace OMA.R_Erdos101_erdos_101_R1_H2_R1_H1_R2

open EuclideanGeometry MvPolynomial
open scoped Classical

/-- Algebraic rigidity for irreducible curves of degree at least four: outside a small
exceptional set `Bad subseteq S x S` of pairs `(y, y')`, each good pair shares more than `M`
common non-degenerate collinear-quadruple neighbors `(x, x')` with at most `M` other good pairs. -/
def H1 : Prop :=
  ∀ d : ℕ, ∀ η : ℝ, 0 < η → ∃ M N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset ℝ², S.card ≤ n → NonCollinearFor 5 (S : Set ℝ²) →
      ∀ F : MvPolynomial (Fin 2) ℝ, Irreducible F → 4 ≤ F.totalDegree → F.totalDegree ≤ d →
        (∀ p ∈ S, eval (fun i => p i) F = 0) →
        ∃ Bad : Finset (ℝ² × ℝ²), Bad ⊆ S ×ˢ S ∧ (Bad.card : ℝ) ≤ η * (n : ℝ) ^ 2 ∧
          ∀ v ∈ (S ×ˢ S) \ Bad,
            (((S ×ˢ S) \ Bad).filter (fun v' =>
              M < ((S ×ˢ S).filter (fun u =>
                (∃ z ∈ S, u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ z ≠ u.1 ∧ z ≠ v.1 ∧ z ≠ u.2 ∧ z ≠ v.2 ∧
                  line[ℝ, u.1, v.1] ≠ line[ℝ, u.2, v.2] ∧
                  z ∈ line[ℝ, u.1, v.1] ∧ z ∈ line[ℝ, u.2, v.2]) ∧
                (∃ z ∈ S, u.1 ≠ v'.1 ∧ u.2 ≠ v'.2 ∧ z ≠ u.1 ∧ z ≠ v'.1 ∧ z ≠ u.2 ∧ z ≠ v'.2 ∧
                  line[ℝ, u.1, v'.1] ≠ line[ℝ, u.2, v'.2] ∧
                  z ∈ line[ℝ, u.1, v'.1] ∧ z ∈ line[ℝ, u.2, v'.2]))).card)).card ≤ M

/-- Real incidence bound for bounded-overlap quadruple correspondence curves on `Z(F) x Z(F)`:
if every `v in Good` shares more than `M` common quadruple neighbors with at most `M` other
elements of `Good`, then the total number of quadruple incidences is at most `eta * n^3`. -/
def H2 : Prop :=
  ∀ d M : ℕ, ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset ℝ², S.card ≤ n → NonCollinearFor 5 (S : Set ℝ²) →
      ∀ F : MvPolynomial (Fin 2) ℝ, Irreducible F → 4 ≤ F.totalDegree → F.totalDegree ≤ d →
        (∀ p ∈ S, eval (fun i => p i) F = 0) →
        ∀ Good : Finset (ℝ² × ℝ²), Good ⊆ S ×ˢ S →
          (∀ v ∈ Good,
            (Good.filter (fun v' =>
              M < ((S ×ˢ S).filter (fun u =>
                (∃ z ∈ S, u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ z ≠ u.1 ∧ z ≠ v.1 ∧ z ≠ u.2 ∧ z ≠ v.2 ∧
                  line[ℝ, u.1, v.1] ≠ line[ℝ, u.2, v.2] ∧
                  z ∈ line[ℝ, u.1, v.1] ∧ z ∈ line[ℝ, u.2, v.2]) ∧
                (∃ z ∈ S, u.1 ≠ v'.1 ∧ u.2 ≠ v'.2 ∧ z ≠ u.1 ∧ z ≠ v'.1 ∧ z ≠ u.2 ∧ z ≠ v'.2 ∧
                  line[ℝ, u.1, v'.1] ≠ line[ℝ, u.2, v'.2] ∧
                  z ∈ line[ℝ, u.1, v'.1] ∧ z ∈ line[ℝ, u.2, v'.2]))).card)).card ≤ M) →
          ((∑ v ∈ Good, ((S ×ˢ S).filter (fun u =>
            ∃ z ∈ S, u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ z ≠ u.1 ∧ z ≠ v.1 ∧ z ≠ u.2 ∧ z ≠ v.2 ∧
              line[ℝ, u.1, v.1] ≠ line[ℝ, u.2, v.2] ∧
              z ∈ line[ℝ, u.1, v.1] ∧ z ∈ line[ℝ, u.2, v.2])).card : ℕ) : ℝ) ≤ η * (n : ℝ) ^ 3

/-- Every finite subset of a line `line[R, a, b]` is collinear. -/
theorem collinear_finset_of_subset_line {T : Finset ℝ²} {a b : ℝ²}
    (hT : ∀ p ∈ T, p ∈ line[ℝ, a, b]) : Collinear ℝ (T : Set ℝ²) := by
  have hgen : ∀ U : Finset ℝ², (∀ p ∈ U, p ∈ line[ℝ, a, b]) →
      Collinear ℝ ((U : Set ℝ²) ∪ ({a, b} : Set ℝ²)) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      simpa using collinear_pair ℝ a b
    | @insert p U hp ih =>
      intro hU
      have hU' := ih (fun q hq => hU q (Finset.mem_insert_of_mem hq))
      have hpL : p ∈ line[ℝ, a, b] := hU p (Finset.mem_insert_self p U)
      have hsub : ({a, b} : Set ℝ²) ⊆ (U : Set ℝ²) ∪ ({a, b} : Set ℝ²) := Set.subset_union_right
      have hmem : p ∈ affineSpan ℝ ((U : Set ℝ²) ∪ ({a, b} : Set ℝ²)) :=
        affineSpan_mono ℝ hsub hpL
      rw [Finset.coe_insert, Set.insert_union]
      exact (collinear_insert_iff_of_mem_affineSpan hmem).mpr hU'
  exact (hgen T hT).subset Set.subset_union_left

/-- Under `NonCollinearFor 5 S`, any line `line[R, a, b]` contains at most four points of `S`. -/
theorem line_card_le_four {S : Finset ℝ²} (hcap : NonCollinearFor 5 (S : Set ℝ²)) (a b : ℝ²) :
    (S.filter (fun p => p ∈ line[ℝ, a, b])).card ≤ 4 := by
  by_contra! hgt
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (show 5 ≤ (S.filter (fun p => p ∈ line[ℝ, a, b])).card by omega)
  apply hcap (T : Set ℝ²) (Finset.coe_subset.mpr (hTsub.trans (Finset.filter_subset ..)))
    T.finite_toSet (by simpa using hTcard)
  exact collinear_finset_of_subset_line fun p hp => (Finset.mem_filter.mp (hTsub hp)).2

/-- Distinct lines meet in at most one point. -/
theorem unique_inter_of_ne_lines {x y x' y' z₁ z₂ : ℝ²}
    (hne : line[ℝ, x, y] ≠ line[ℝ, x', y'])
    (hz₁L : z₁ ∈ line[ℝ, x, y]) (hz₁R : z₁ ∈ line[ℝ, x', y'])
    (hz₂L : z₂ ∈ line[ℝ, x, y]) (hz₂R : z₂ ∈ line[ℝ, x', y']) : z₁ = z₂ := by
  by_contra hz
  have h1 : line[ℝ, z₁, z₂] = line[ℝ, x, y] := affineSpan_pair_eq_of_mem_of_mem_of_ne hz₁L hz₂L hz
  have h2 : line[ℝ, z₁, z₂] = line[ℝ, x', y'] := affineSpan_pair_eq_of_mem_of_mem_of_ne hz₁R hz₂R hz
  exact hne (h1.symm.trans h2)

/-- Under `NonCollinearFor 5 S`, every fixed pair `v = (y, y') in S x S` has at most `4 * S.card`
non-degenerate collinear-quadruple neighbors `u = (x, x') in S x S`. -/
theorem quadruple_degree_le {S : Finset ℝ²} (hcap : NonCollinearFor 5 (S : Set ℝ²))
    {v : ℝ² × ℝ²} (hv : v ∈ S ×ˢ S) :
    ((S ×ˢ S).filter (fun u =>
      ∃ z ∈ S, u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ z ≠ u.1 ∧ z ≠ v.1 ∧ z ≠ u.2 ∧ z ≠ v.2 ∧
        line[ℝ, u.1, v.1] ≠ line[ℝ, u.2, v.2] ∧
        z ∈ line[ℝ, u.1, v.1] ∧ z ∈ line[ℝ, u.2, v.2])).card ≤ 4 * S.card := by
  obtain ⟨hv1, hv2⟩ := Finset.mem_product.mp hv
  let U (z : ℝ²) := (S.filter (fun x => x ∈ line[ℝ, v.1, z])).erase v.1 |>.erase z
  let V (z : ℝ²) := (S.filter (fun x' => x' ∈ line[ℝ, v.2, z])).erase v.2 |>.erase z
  let Z := S.filter (fun z => z ≠ v.1 ∧ z ≠ v.2)
  have hU_card (z : ℝ²) (hz : z ∈ Z) : (U z).card ≤ 2 := by
    obtain ⟨hzS, hzv1, _⟩ := Finset.mem_filter.mp hz
    have h4 := line_card_le_four hcap v.1 z
    have hv1_in : v.1 ∈ S.filter (fun x => x ∈ line[ℝ, v.1, z]) :=
      Finset.mem_filter.mpr ⟨hv1, left_mem_affineSpan_pair ℝ v.1 z⟩
    have hz_in : z ∈ (S.filter (fun x => x ∈ line[ℝ, v.1, z])).erase v.1 :=
      Finset.mem_erase.mpr ⟨hzv1, Finset.mem_filter.mpr ⟨hzS, right_mem_affineSpan_pair ℝ v.1 z⟩⟩
    have hcard1 := Finset.card_erase_of_mem hv1_in
    have hcard2 := Finset.card_erase_of_mem hz_in
    change ((S.filter (fun x => x ∈ line[ℝ, v.1, z])).erase v.1 |>.erase z).card ≤ 2
    omega
  have hV_card (z : ℝ²) (hz : z ∈ Z) : (V z).card ≤ 2 := by
    obtain ⟨hzS, _, hzv2⟩ := Finset.mem_filter.mp hz
    have h4 := line_card_le_four hcap v.2 z
    have hv2_in : v.2 ∈ S.filter (fun x' => x' ∈ line[ℝ, v.2, z]) :=
      Finset.mem_filter.mpr ⟨hv2, left_mem_affineSpan_pair ℝ v.2 z⟩
    have hz_in : z ∈ (S.filter (fun x' => x' ∈ line[ℝ, v.2, z])).erase v.2 :=
      Finset.mem_erase.mpr ⟨hzv2, Finset.mem_filter.mpr ⟨hzS, right_mem_affineSpan_pair ℝ v.2 z⟩⟩
    have hcard1 := Finset.card_erase_of_mem hv2_in
    have hcard2 := Finset.card_erase_of_mem hz_in
    change ((S.filter (fun x' => x' ∈ line[ℝ, v.2, z])).erase v.2 |>.erase z).card ≤ 2
    omega
  have hsub : (S ×ˢ S).filter (fun u =>
      ∃ z ∈ S, u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ z ≠ u.1 ∧ z ≠ v.1 ∧ z ≠ u.2 ∧ z ≠ v.2 ∧
        line[ℝ, u.1, v.1] ≠ line[ℝ, u.2, v.2] ∧
        z ∈ line[ℝ, u.1, v.1] ∧ z ∈ line[ℝ, u.2, v.2]) ⊆ Z.biUnion (fun z => U z ×ˢ V z) := by
    intro u hu
    obtain ⟨huSS, z, hzS, hu1v1, hu2v2, hzu1, hzv1, hzu2, hzv2, _, hzL1, hzL2⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu1S, hu2S⟩ := Finset.mem_product.mp huSS
    have hL1 : line[ℝ, v.1, z] = line[ℝ, u.1, v.1] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne (right_mem_affineSpan_pair ℝ u.1 v.1) hzL1 hzv1.symm
    have hL2 : line[ℝ, v.2, z] = line[ℝ, u.2, v.2] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne (right_mem_affineSpan_pair ℝ u.2 v.2) hzL2 hzv2.symm
    have hu1_in : u.1 ∈ U z := Finset.mem_erase.mpr ⟨hzu1.symm, Finset.mem_erase.mpr ⟨hu1v1,
      Finset.mem_filter.mpr ⟨hu1S, hL1.symm ▸ left_mem_affineSpan_pair ℝ u.1 v.1⟩⟩⟩
    have hu2_in : u.2 ∈ V z := Finset.mem_erase.mpr ⟨hzu2.symm, Finset.mem_erase.mpr ⟨hu2v2,
      Finset.mem_filter.mpr ⟨hu2S, hL2.symm ▸ left_mem_affineSpan_pair ℝ u.2 v.2⟩⟩⟩
    exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_filter.mpr ⟨hzS, hzv1, hzv2⟩,
      Finset.mem_product.mpr ⟨hu1_in, hu2_in⟩⟩
  calc _ ≤ (Z.biUnion (fun z => U z ×ˢ V z)).card := Finset.card_le_card hsub
    _ ≤ ∑ z ∈ Z, (U z ×ˢ V z).card := Finset.card_biUnion_le
    _ = ∑ z ∈ Z, (U z).card * (V z).card := by simp [Finset.card_product]
    _ ≤ ∑ _z ∈ Z, 4 := Finset.sum_le_sum fun z hz => Nat.mul_le_mul (hU_card z hz) (hV_card z hz)
    _ = Z.card * 4 := by simp
    _ ≤ S.card * 4 := Nat.mul_le_mul_right 4 (Finset.card_filter_le ..)
    _ = 4 * S.card := by ring

/-- Cauchy-Schwarz quadruple-energy lower bound: any line-injective family `T` of distinct
collinear triples in `S` generates at least `T.card^2 / S.card - T.card` non-degenerate
quadruple incidences. -/
theorem cauchy_schwarz_quadruples {S : Finset ℝ²} {T : Finset (ℝ² × ℝ² × ℝ²)}
    (hTsub : ∀ t ∈ T, t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S ∧
      t.1 ≠ t.2.1 ∧ t.2.2 ≠ t.1 ∧ t.2.2 ≠ t.2.1 ∧ t.2.2 ∈ line[ℝ, t.1, t.2.1])
    (hTinj : (T : Set (ℝ² × ℝ² × ℝ²)).InjOn (fun t => line[ℝ, t.1, t.2.1])) :
    (T.card : ℝ) ^ 2 ≤ (S.card : ℝ) * ((T.card : ℝ) +
      ((∑ v ∈ S ×ˢ S, ((S ×ˢ S).filter (fun u =>
        ∃ z ∈ S, u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ z ≠ u.1 ∧ z ≠ v.1 ∧ z ≠ u.2 ∧ z ≠ v.2 ∧
          line[ℝ, u.1, v.1] ≠ line[ℝ, u.2, v.2] ∧
          z ∈ line[ℝ, u.1, v.1] ∧ z ∈ line[ℝ, u.2, v.2])).card : ℕ) : ℝ)) := by
  let fiber (z : ℝ²) := T.filter (fun t => t.2.2 = z)
  let Q := ((S ×ˢ S) ×ˢ (S ×ˢ S)).filter (fun p =>
    ∃ z ∈ S, p.1.1 ≠ p.2.1 ∧ p.1.2 ≠ p.2.2 ∧ z ≠ p.1.1 ∧ z ≠ p.2.1 ∧ z ≠ p.1.2 ∧ z ≠ p.2.2 ∧
      line[ℝ, p.1.1, p.2.1] ≠ line[ℝ, p.1.2, p.2.2] ∧
      z ∈ line[ℝ, p.1.1, p.2.1] ∧ z ∈ line[ℝ, p.1.2, p.2.2])
  have hQ_eq : Q.card = ∑ v ∈ S ×ˢ S, ((S ×ˢ S).filter (fun u =>
      ∃ z ∈ S, u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ z ≠ u.1 ∧ z ≠ v.1 ∧ z ≠ u.2 ∧ z ≠ v.2 ∧
        line[ℝ, u.1, v.1] ≠ line[ℝ, u.2, v.2] ∧
        z ∈ line[ℝ, u.1, v.1] ∧ z ∈ line[ℝ, u.2, v.2])).card := by
    have hbi : Q = (S ×ˢ S).biUnion (fun v =>
        ((S ×ˢ S).filter (fun u =>
          ∃ z ∈ S, u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ z ≠ u.1 ∧ z ≠ v.1 ∧ z ≠ u.2 ∧ z ≠ v.2 ∧
            line[ℝ, u.1, v.1] ≠ line[ℝ, u.2, v.2] ∧
            z ∈ line[ℝ, u.1, v.1] ∧ z ∈ line[ℝ, u.2, v.2])).image (fun u => (u, v))) := by
      ext ⟨u, v⟩
      simp only [Q, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨⟨hu, hv⟩, hcond⟩
        exact ⟨v, hv, u, ⟨hu, hcond⟩, rfl⟩
      · rintro ⟨v', hv', u', ⟨hu', hcond⟩, hpair⟩
        cases hpair
        exact ⟨⟨hu', hv'⟩, hcond⟩
    rw [hbi, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro v _
      exact Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h
    · intro v₁ _ v₂ _ hne
      refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => ?_
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp₁
      obtain ⟨_, _, h2⟩ := Finset.mem_image.mp hp₂
      exact hne (congrArg Prod.snd h2).symm
  have hT_sum : ∑ z ∈ S, (fiber z).card = T.card := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun t : ℝ² × ℝ² × ℝ² => t.2.2) (s := T) (t := S)
      (fun t ht => (hTsub t ht).2.2.1)
    exact this.symm
  let Off := (T ×ˢ T).filter (fun p => p.1.2.2 = p.2.2.2 ∧ p.1 ≠ p.2)
  have hsq_sum : ∑ z ∈ S, (fiber z).card ^ 2 = T.card + Off.card := by
    have hpair (z : ℝ²) : (fiber z).card ^ 2 = (fiber z).card +
        ((fiber z ×ˢ fiber z).filter (fun p => p.1 ≠ p.2)).card := by
      rw [sq, ← Finset.card_product]
      have hsplit : ((fiber z ×ˢ fiber z).filter (fun p => p.1 = p.2)).card +
          ((fiber z ×ˢ fiber z).filter (fun p => p.1 ≠ p.2)).card = (fiber z ×ˢ fiber z).card := by
        simpa only [ne_eq] using Finset.card_filter_add_card_filter_not (s := fiber z ×ˢ fiber z)
          (fun p => p.1 = p.2)
      have hdiag : ((fiber z ×ˢ fiber z).filter (fun p => p.1 = p.2)).card = (fiber z).card := by
        have heq : (fiber z ×ˢ fiber z).filter (fun p => p.1 = p.2) =
            (fiber z).image (fun t => (t, t)) := by
          ext ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          constructor
          · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl⟩
          · rintro ⟨t, ht, h⟩; cases h; exact ⟨⟨ht, ht⟩, rfl⟩
        rw [heq, Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h]
      omega
    rw [Finset.sum_congr rfl (fun z _ => hpair z), Finset.sum_add_distrib, hT_sum]
    congr 1
    have hOff_eq : Off = S.biUnion (fun z => (fiber z ×ˢ fiber z).filter (fun p => p.1 ≠ p.2)) := by
      ext ⟨t₁, t₂⟩
      simp only [Off, fiber, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion]
      constructor
      · rintro ⟨⟨ht₁, ht₂⟩, hz, hne⟩
        exact ⟨t₁.2.2, (hTsub t₁ ht₁).2.2.1, ⟨⟨ht₁, rfl⟩, ⟨ht₂, hz.symm⟩⟩, hne⟩
      · rintro ⟨z, _, ⟨⟨ht₁, hz₁⟩, ⟨ht₂, hz₂⟩⟩, hne⟩
        exact ⟨⟨ht₁, ht₂⟩, hz₁.trans hz₂.symm, hne⟩
    rw [hOff_eq, Finset.card_biUnion]
    intro z₁ _ z₂ _ hne
    refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => ?_
    have hz₁ := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp₁).1).1).2
    have hz₂ := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp₂).1).1).2
    exact hne (hz₁.symm.trans hz₂)
  let enc : (ℝ² × ℝ² × ℝ²) × (ℝ² × ℝ² × ℝ²) → (ℝ² × ℝ²) × (ℝ² × ℝ²) :=
    fun p => ((p.1.1, p.2.1), (p.1.2.1, p.2.2.1))
  have hOff_le_Q : Off.card ≤ Q.card := by
    apply Finset.card_le_card_of_injOn enc
    · intro p hp
      obtain ⟨hpTT, hz_eq, hne⟩ := Finset.mem_filter.mp hp
      obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp hpTT
      obtain ⟨hx₁, hy₁, hz₁, hxy₁, hzx₁, hzy₁, hmem₁⟩ := hTsub p.1 ht₁
      obtain ⟨hx₂, hy₂, _, hxy₂, hzx₂, hzy₂, hmem₂⟩ := hTsub p.2 ht₂
      have hLne : line[ℝ, p.1.1, p.1.2.1] ≠ line[ℝ, p.2.1, p.2.2.1] := fun h =>
        hne (hTinj ht₁ ht₂ h)
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hx₁, hx₂⟩, Finset.mem_product.mpr ⟨hy₁, hy₂⟩⟩,
        p.1.2.2, hz₁, hxy₁, hxy₂, hzx₁, hzy₁, hz_eq ▸ hzx₂, hz_eq ▸ hzy₂, hLne,
        hmem₁, hz_eq ▸ hmem₂⟩)
    · intro p₁ hp₁ p₂ hp₂ heq
      obtain ⟨hp₁TT, hz₁_eq, hne₁⟩ := Finset.mem_filter.mp hp₁
      obtain ⟨hp₂TT, hz₂_eq, _⟩ := Finset.mem_filter.mp hp₂
      obtain ⟨ht₁a, ht₁b⟩ := Finset.mem_product.mp hp₁TT
      obtain ⟨ht₂a, ht₂b⟩ := Finset.mem_product.mp hp₂TT
      have hx₁ : p₁.1.1 = p₂.1.1 := congrArg (fun q => q.1.1) heq
      have hx₂ : p₁.2.1 = p₂.2.1 := congrArg (fun q => q.1.2) heq
      have hy₁ : p₁.1.2.1 = p₂.1.2.1 := congrArg (fun q => q.2.1) heq
      have hy₂ : p₁.2.2.1 = p₂.2.2.1 := congrArg (fun q => q.2.2) heq
      have hLne : line[ℝ, p₁.1.1, p₁.1.2.1] ≠ line[ℝ, p₁.2.1, p₁.2.2.1] := fun h =>
        hne₁ (hTinj ht₁a ht₁b h)
      have hz_same : p₁.1.2.2 = p₂.1.2.2 := unique_inter_of_ne_lines hLne
        (hTsub p₁.1 ht₁a).2.2.2.2.2.2
        (hz₁_eq ▸ (hTsub p₁.2 ht₁b).2.2.2.2.2.2)
        (hx₁ ▸ hy₁ ▸ (hTsub p₂.1 ht₂a).2.2.2.2.2.2)
        (hx₂ ▸ hy₂ ▸ hz₂_eq ▸ (hTsub p₂.2 ht₂b).2.2.2.2.2.2)
      apply Prod.ext
      · exact Prod.ext hx₁ (Prod.ext hy₁ hz_same)
      · exact Prod.ext hx₂ (Prod.ext hy₂ (hz₁_eq.symm.trans (hz_same.trans hz₂_eq)))
  have hcs : (∑ z ∈ S, ((fiber z).card : ℝ)) ^ 2 ≤ (S.card : ℝ) * ∑ z ∈ S, ((fiber z).card : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsum_cast : (∑ z ∈ S, ((fiber z).card : ℝ)) = (T.card : ℝ) := by exact_mod_cast hT_sum
  have hsq_cast : (∑ z ∈ S, ((fiber z).card : ℝ) ^ 2) = (T.card : ℝ) + (Off.card : ℝ) := by
    exact_mod_cast hsq_sum
  rw [hsum_cast, hsq_cast] at hcs
  have hle_real : (Off.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hOff_le_Q
  rw [hQ_eq] at hle_real
  nlinarith [show (0 : ℝ) ≤ S.card by positivity]

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R1_H2_R1.H1 := by
  intro hrig hinc d ε hε
  let η : ℝ := ε ^ 2 / 10
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨M, N₁, hN₁⟩ := hrig d η hη
  obtain ⟨N₂, hN₂⟩ := hinc d M η hη
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / ε)
  refine ⟨max (max N₁ N₂) (max K 1), ?_⟩
  intro n hn S hSn hcap F hF hdeg4 hdegd hzero
  let hfin := OMA.R_Erdos101_erdos_101_R1.four_lines_finite S
  let A := hfin.toFinset
  rw [Set.ncard_eq_toFinset_card _ hfin]
  by_contra! hlarge
  have hex : ∀ L : A, ∃ t : ℝ² × ℝ² × ℝ²,
      t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S ∧
      t.1 ≠ t.2.1 ∧ t.2.2 ≠ t.1 ∧ t.2.2 ≠ t.2.1 ∧
      line[ℝ, t.1, t.2.1] = L.val ∧ t.2.2 ∈ L.val := by
    intro L
    have hL := hfin.mem_toFinset.mp L.property
    have h4 := OMA.R_Erdos101_erdos_101_R1.four_points hL
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp
      (show 2 < (S.filter (fun p => p ∈ L.val)).card by omega)
    obtain ⟨hxS, hxL⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyS, hyL⟩ := Finset.mem_filter.mp hy
    obtain ⟨hzS, hzL⟩ := Finset.mem_filter.mp hz
    exact ⟨(x, y, z), hxS, hyS, hzS, hxy, hxz.symm, hyz.symm,
      OMA.R_Erdos101_erdos_101_R1.line_through hL hxL hyL hxy, hzL⟩
  choose wit hwit using hex
  let T := A.attach.image wit
  have hTinj_wit : Function.Injective wit := by
    intro L₁ L₂ heq
    have h1 := (hwit L₁).2.2.2.2.2.2.1
    have h2 := (hwit L₂).2.2.2.2.2.2.1
    exact Subtype.ext (h1.symm.trans ((congrArg (fun t => line[ℝ, t.1, t.2.1]) heq).trans h2))
  have hTcard : T.card = A.card := by
    rw [Finset.card_image_of_injective _ hTinj_wit, Finset.card_attach]
  have hTsub : ∀ t ∈ T, t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S ∧
      t.1 ≠ t.2.1 ∧ t.2.2 ≠ t.1 ∧ t.2.2 ≠ t.2.1 ∧ t.2.2 ∈ line[ℝ, t.1, t.2.1] := by
    intro t ht
    obtain ⟨L, _, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hx, hy, hz, hxy, hzx, hzy, hL, hmem⟩ := hwit L
    exact ⟨hx, hy, hz, hxy, hzx, hzy, hL.symm ▸ hmem⟩
  have hTinj : (T : Set (ℝ² × ℝ² × ℝ²)).InjOn (fun t => line[ℝ, t.1, t.2.1]) := by
    intro t₁ ht₁ t₂ ht₂ heq
    obtain ⟨L₁, _, rfl⟩ := Finset.mem_image.mp ht₁
    obtain ⟨L₂, _, rfl⟩ := Finset.mem_image.mp ht₂
    have hL : L₁ = L₂ := Subtype.ext (((hwit L₁).2.2.2.2.2.2.1).symm.trans
      (heq.trans (hwit L₂).2.2.2.2.2.2.1))
    rw [hL]
  have hcs := cauchy_schwarz_quadruples hTsub hTinj
  rw [hTcard] at hcs
  obtain ⟨Bad, hBadSub, hBadCard, hGood⟩ := hN₁ n (by omega) S hSn hcap F hF hdeg4 hdegd hzero
  let Good := (S ×ˢ S) \ Bad
  have hGood_inc := hN₂ n (by omega) S hSn hcap F hF hdeg4 hdegd hzero Good Finset.sdiff_subset hGood
  let deg (v : ℝ² × ℝ²) := ((S ×ˢ S).filter (fun u =>
    ∃ z ∈ S, u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ z ≠ u.1 ∧ z ≠ v.1 ∧ z ≠ u.2 ∧ z ≠ v.2 ∧
      line[ℝ, u.1, v.1] ≠ line[ℝ, u.2, v.2] ∧
      z ∈ line[ℝ, u.1, v.1] ∧ z ∈ line[ℝ, u.2, v.2])).card
  have hsum_split : (∑ v ∈ S ×ˢ S, deg v) = (∑ v ∈ Good, deg v) + (∑ v ∈ Bad, deg v) :=
    (Finset.sum_sdiff hBadSub (f := deg)).symm
  have hBad_inc_nat : ∑ v ∈ Bad, deg v ≤ Bad.card * (4 * S.card) := by
    calc ∑ v ∈ Bad, deg v ≤ ∑ _v ∈ Bad, (4 * S.card) :=
          Finset.sum_le_sum fun v hv => quadruple_degree_le hcap (hBadSub hv)
      _ = Bad.card * (4 * S.card) := by simp
  have hS_le_n : (S.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hSn
  have hBad_inc : ((∑ v ∈ Bad, deg v : ℕ) : ℝ) ≤ 4 * η * (n : ℝ) ^ 3 := by
    have h1 : ((∑ v ∈ Bad, deg v : ℕ) : ℝ) ≤ (Bad.card : ℝ) * (4 * (S.card : ℝ)) := by
      exact_mod_cast hBad_inc_nat
    have h2 : (Bad.card : ℝ) * (4 * (S.card : ℝ)) ≤ (η * (n : ℝ) ^ 2) * (4 * (n : ℝ)) :=
      mul_le_mul hBadCard (by linarith) (by positivity) (by positivity)
    linarith
  set tot : ℕ := ∑ v ∈ S ×ˢ S, deg v
  have hcs_tot : (A.card : ℝ) ^ 2 ≤ (S.card : ℝ) * ((A.card : ℝ) + (tot : ℝ)) := hcs
  have hTotal_inc : (tot : ℝ) ≤ 5 * η * (n : ℝ) ^ 3 := by
    have hcast : (tot : ℝ) =
        ((∑ v ∈ Good, deg v : ℕ) : ℝ) + ((∑ v ∈ Bad, deg v : ℕ) : ℝ) := by
      exact_mod_cast hsum_split
    linarith [hGood_inc, hBad_inc]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnK : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show K ≤ n by omega)
  have hεn : (2 : ℝ) < ε * (n : ℝ) := by
    have h1 : (2 : ℝ) < ε * (K : ℝ) := by linarith [(div_lt_iff₀ hε).mp hK]
    exact h1.trans_le (mul_le_mul_of_nonneg_left hnK hε.le)
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := lt_trans (mul_pos hε (sq_pos_of_pos hn_pos)) hlarge
  have hcs' : (A.card : ℝ) ^ 2 ≤ (n : ℝ) * ((A.card : ℝ) + 5 * η * (n : ℝ) ^ 3) := by
    have hnonneg : (0 : ℝ) ≤ (A.card : ℝ) + (tot : ℝ) :=
      add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h1 : (S.card : ℝ) * ((A.card : ℝ) + (tot : ℝ)) ≤
        (n : ℝ) * ((A.card : ℝ) + (tot : ℝ)) :=
      mul_le_mul_of_nonneg_right hS_le_n hnonneg
    have h2 : (n : ℝ) * ((A.card : ℝ) + (tot : ℝ)) ≤
        (n : ℝ) * ((A.card : ℝ) + 5 * η * (n : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hn_pos.le
    exact hcs_tot.trans (h1.trans h2)
  have hquad : (A.card : ℝ) * ((A.card : ℝ) - (n : ℝ)) ≤ 5 * η * (n : ℝ) ^ 4 := by
    nlinarith [hcs']
  have hlb : (ε * (n : ℝ) ^ 2) * (ε * (n : ℝ) ^ 2 - (n : ℝ)) <
      (A.card : ℝ) * ((A.card : ℝ) - (n : ℝ)) := by
    have hdiff_pos : (0 : ℝ) < ε * (n : ℝ) ^ 2 - (n : ℝ) := by
      nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega)]
    have h1 : (ε * (n : ℝ) ^ 2) * (ε * (n : ℝ) ^ 2 - (n : ℝ)) <
        (A.card : ℝ) * (ε * (n : ℝ) ^ 2 - (n : ℝ)) :=
      mul_lt_mul_of_pos_right hlarge hdiff_pos
    have h2 : (A.card : ℝ) * (ε * (n : ℝ) ^ 2 - (n : ℝ)) <
        (A.card : ℝ) * ((A.card : ℝ) - (n : ℝ)) :=
      mul_lt_mul_of_pos_left (by linarith) hA_pos
    exact h1.trans h2
  have h5η : 5 * η * (n : ℝ) ^ 4 = (ε ^ 2 / 2) * (n : ℝ) ^ 4 := by dsimp [η]; ring
  have hmid : (ε ^ 2 / 2) * (n : ℝ) ^ 4 < (ε * (n : ℝ) ^ 2) * (ε * (n : ℝ) ^ 2 - (n : ℝ)) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hfactor : (ε * (n : ℝ) ^ 2) * (ε * (n : ℝ) ^ 2 - (n : ℝ)) - (ε ^ 2 / 2) * (n : ℝ) ^ 4 =
        (ε / 2) * (n : ℝ) ^ 3 * (ε * (n : ℝ) - 2) := by ring
    have hpos : 0 < (ε / 2) * (n : ℝ) ^ 3 * (ε * (n : ℝ) - 2) :=
      mul_pos (by positivity) (by linarith)
    linarith
  linarith

end OMA.R_Erdos101_erdos_101_R1_H2_R1_H1_R2
