import FormalConjectures.ErdosProblems.«101»

-- Reduction Erdos101.erdos_101.R1 of Erdős Problem 101
-- Credit: @ubuwaits

/-!
# A bounded-degree inverse problem for four-point lines

The first hypothesis asks whether a positive proportion of points incident to many
four-point lines must have a positive proportion on a curve of bounded degree.
The second is the bounded-degree case of the quadruple-line estimate
(Elekes and Szabó, On Triple Lines and Cubic Curves, Theorem 4.3).

The choice of points matters. On each surviving line we designate one of its
four points and discard points that receive too few designations. A curve through
many of the remaining points captures many designated incidences. Applying this
four times and multiplying the polynomials puts all four points of every
surviving line on one bounded-degree curve.
-/

namespace OMA.R_Erdos101_erdos_101_R1

open EuclideanGeometry MvPolynomial Filter Asymptotics
open scoped Classical Finset

/-- A positive-density set of points, each on linearly many four-point lines,
has a positive-density subset on a curve of degree bounded in terms of the density. -/
def H1 : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ d : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ S T : Finset ℝ², N ≤ S.card → T ⊆ S → NonCollinearFor 5 (S : Set ℝ²) →
      τ * S.card ≤ T.card →
      (∀ p ∈ T, ∃ A : Finset (AffineSubspace ℝ ℝ²), τ * S.card ≤ A.card ∧
        ∀ L ∈ A, p ∈ L ∧ L ∈ linesWithPointsFor 4 (S : Set ℝ²)) →
      ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
        c * S.card ≤ (T.filter (fun p => eval (fun i => p i) F = 0)).card

/-- The quadruple-line bound on one bounded-degree real algebraic curve,
uniform in its coefficients. The size parameter n may bound the number of points. -/
def H2 : Prop :=
  ∀ d : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset ℝ², S.card ≤ n → NonCollinearFor 5 (S : Set ℝ²) →
      ∀ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 → F.totalDegree ≤ d →
        (∀ p ∈ S, eval (fun i => p i) F = 0) →
        ((linesWithPointsFor 4 (S : Set ℝ²)).ncard : ℝ) ≤ ε * (n : ℝ)^2

lemma four_lines_finite (S : Finset ℝ²) :
    (linesWithPointsFor 4 (S : Set ℝ²)).Finite := by
  apply (S.finite_toSet.image2 (fun p q => line[ℝ, p, q]) S.finite_toSet).subset
  rintro L ⟨⟨p, hp, q, hq, _, he⟩, _⟩
  exact ⟨p, hp, q, hq, he⟩

lemma four_points {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    (S.filter (fun p => p ∈ L)).card = 4 := by
  have he : ((S.filter (fun p => p ∈ L) : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ S := by
    ext p
    simp [and_comm]
  rw [← Set.ncard_coe_finset, he]
  exact hL.2

lemma line_through {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) {p q : ℝ²}
    (hp : p ∈ L) (hq : q ∈ L) (hne : p ≠ q) : line[ℝ, p, q] = L := by
  obtain ⟨⟨a, _, b, _, _, rfl⟩, _⟩ := hL
  exact affineSpan_pair_eq_of_mem_of_mem_of_ne hp hq hne

/-- Distinct lines through p use disjoint triples among the other points. -/
lemma pencil_bound {S : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)}
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    {p : ℝ²} (hp : p ∈ S) :
    3 * (A.filter (fun L => p ∈ L)).card ≤ S.card - 1 := by
  let pencil := A.filter (fun L => p ∈ L)
  let others := fun L : AffineSubspace ℝ ℝ² => (S.filter (fun q => q ∈ L)).erase p
  have hdisj : (pencil : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint others := by
    intro L hL M hM hne
    obtain ⟨hLA, hpL⟩ := Finset.mem_filter.mp hL
    obtain ⟨hMA, hpM⟩ := Finset.mem_filter.mp hM
    apply Finset.disjoint_left.mpr
    intro q hqL hqM
    obtain ⟨hqp, hqL'⟩ := Finset.mem_erase.mp hqL
    have hqM' := (Finset.mem_erase.mp hqM).2
    exact hne ((line_through (hA L hLA) hpL (Finset.mem_filter.mp hqL').2 hqp.symm).symm.trans
      (line_through (hA M hMA) hpM (Finset.mem_filter.mp hqM').2 hqp.symm))
  have hcard (L) (hL : L ∈ pencil) : (others L).card = 3 := by
    obtain ⟨hLA, hpL⟩ := Finset.mem_filter.mp hL
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hp, hpL⟩), four_points (hA L hLA)]
  have hsub : pencil.biUnion others ⊆ S.erase p := by
    intro q hq
    obtain ⟨L, _, hq⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hq
    exact Finset.mem_erase.mpr ⟨hne, (Finset.mem_filter.mp hmem).1⟩
  calc
    3 * pencil.card = ∑ L ∈ pencil, (others L).card := by
      simp [Finset.sum_congr rfl hcard, mul_comm]
    _ = (pencil.biUnion others).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (S.erase p).card := Finset.card_le_card hsub
    _ = S.card - 1 := Finset.card_erase_of_mem hp

/-- Pair counting, with the constant for unordered pairs. -/
lemma pair_bound {S : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)}
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    12 * A.card ≤ S.card * (S.card - 1) := by
  have hcount : (∑ L ∈ A, (S.filter (fun p => p ∈ L)).card) =
      ∑ p ∈ S, (A.filter (fun L => p ∈ L)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun L p => p ∈ L)
  have hs : (∑ L ∈ A, (S.filter (fun p => p ∈ L)).card) = A.card * 4 := by
    simp [Finset.sum_congr rfl (fun L hL => four_points (hA L hL))]
  calc
    12 * A.card = 3 * (A.card * 4) := by omega
    _ = 3 * ∑ p ∈ S, (A.filter (fun L => p ∈ L)).card := by rw [← hcount, hs]
    _ = ∑ p ∈ S, 3 * (A.filter (fun L => p ∈ L)).card := Finset.mul_sum ..
    _ ≤ ∑ _p ∈ S, (S.card - 1) := Finset.sum_le_sum fun p hp => pencil_bound hA hp
    _ = S.card * (S.card - 1) := by simp

/-- With one designated point on each line, the inverse hypothesis captures a
positive-density subfamily at its designated points. The constants are uniform
over both the line family and the designations. -/
lemma capture_one (h1 : H1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
      ∀ (S : Finset ℝ²) (A : Finset (AffineSubspace ℝ ℝ²))
        (mark : AffineSubspace ℝ ℝ² → ℝ²),
        N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
        (∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) →
        (∀ L ∈ A, mark L ∈ S ∧ mark L ∈ L) →
        δ * (S.card : ℝ)^2 ≤ A.card →
        ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
          ∃ B ⊆ A, η * (S.card : ℝ)^2 ≤ B.card ∧
            ∀ L ∈ B, eval (fun i => mark L i) F = 0 := by
  let τ := δ / 2
  have hτ : 0 < τ := half_pos hδ
  obtain ⟨d, c, hc, N, hinv⟩ := h1 τ hτ
  refine ⟨d, c * τ, mul_pos hc hτ, max N 1, ?_⟩
  intro S A mark hN hS hA hmark hdense
  let n : ℝ := S.card
  have hn : 0 < n := by
    have := (le_max_right N 1).trans hN
    dsimp [n]
    exact_mod_cast (show 0 < S.card by omega)
  let fiber := fun p : ℝ² => A.filter (fun L => mark L = p)
  let w := fun p : ℝ² => ((fiber p).card : ℝ)
  let T := S.filter (fun p => τ * n ≤ w p)
  have hTS : T ⊆ S := Finset.filter_subset ..
  have hmaps : Set.MapsTo mark (A : Set (AffineSubspace ℝ ℝ²)) (S : Set ℝ²) :=
    fun L hL => (hmark L hL).1
  have hsum : ∑ p ∈ S, w p = (A.card : ℝ) := by
    dsimp [w, fiber]
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hcap (p) (hp : p ∈ S) : w p ≤ n := by
    have hsub : fiber p ⊆ A.filter (fun L => p ∈ L) := by
      intro L hL
      obtain ⟨hLA, hLp⟩ := Finset.mem_filter.mp hL
      exact Finset.mem_filter.mpr ⟨hLA, hLp ▸ (hmark L hLA).2⟩
    have hcard := Finset.card_le_card hsub
    have hpencil := pencil_bound hA hp
    dsimp only [w, n]
    exact_mod_cast (show (fiber p).card ≤ S.card by omega)
  have hhot : τ * n ≤ (T.card : ℝ) := by
    have hTsum : (∑ p ∈ T, w p) ≤ T.card * n := by
      calc
        _ ≤ ∑ _p ∈ T, n := Finset.sum_le_sum fun p hp => hcap p (hTS hp)
        _ = _ := by simp
    have hlight : (∑ p ∈ S \ T, w p) ≤ n * (τ * n) := by
      calc
        _ ≤ ∑ _p ∈ S \ T, τ * n := by
          apply Finset.sum_le_sum
          intro p hp
          have hp' := Finset.mem_sdiff.mp hp
          exact le_of_not_ge fun h => hp'.2 (Finset.mem_filter.mpr ⟨hp'.1, h⟩)
        _ = ((S \ T).card : ℝ) * (τ * n) := by simp
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hτ.le hn.le)
          dsimp only [n]
          exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := S) (t := T))
    have htotal := Finset.sum_sdiff hTS (f := w)
    rw [hsum] at htotal
    change δ * n^2 ≤ (A.card : ℝ) at hdense
    have htwice : δ = τ + τ := by dsimp [τ]; ring
    exact (le_of_mul_le_mul_right (a := n) (by nlinarith only [htotal, hlight, hTsum, hdense, htwice]) hn)
  have hstars (p) (hp : p ∈ T) :
      ∃ C : Finset (AffineSubspace ℝ ℝ²), τ * S.card ≤ C.card ∧
        ∀ L ∈ C, p ∈ L ∧ L ∈ linesWithPointsFor 4 (S : Set ℝ²) := by
    refine ⟨fiber p, (Finset.mem_filter.mp hp).2, ?_⟩
    intro L hL
    obtain ⟨hLA, heq⟩ := Finset.mem_filter.mp hL
    exact ⟨heq ▸ (hmark L hLA).2, hA L hLA⟩
  obtain ⟨F, hF, hdeg, hmany⟩ :=
    hinv S T ((le_max_left N 1).trans hN) hTS hS hhot hstars
  let G := T.filter (fun p => eval (fun i => p i) F = 0)
  let B := A.filter (fun L => mark L ∈ G)
  have hgoodmass : ∑ p ∈ G, w p = (B.card : ℝ) := by
    dsimp only [B, w, fiber]
    exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter A G mark
  refine ⟨F, hF, hdeg, B, Finset.filter_subset .., ?_, ?_⟩
  · change c * n ≤ (G.card : ℝ) at hmany
    calc
      (c * τ) * (S.card : ℝ)^2 = (c * n) * (τ * n) := by dsimp [n]; ring
      _ ≤ (G.card : ℝ) * (τ * n) := mul_le_mul_of_nonneg_right hmany (mul_nonneg hτ.le hn.le)
      _ = ∑ _p ∈ G, τ * n := by simp
      _ ≤ ∑ p ∈ G, w p := Finset.sum_le_sum fun p hp =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      _ = _ := hgoodmass
  · intro L hL
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hL).2).2

/-- Repeatedly capture a designated point, retaining the lines captured earlier. -/
lemma capture_many (h1 : H1) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
      ∀ (S : Finset ℝ²) (A : Finset (AffineSubspace ℝ ℝ²))
        (mark : Fin k → AffineSubspace ℝ ℝ² → ℝ²),
        N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
        (∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) →
        (∀ i, ∀ L ∈ A, mark i L ∈ S ∧ mark i L ∈ L) →
        δ * (S.card : ℝ)^2 ≤ A.card →
        ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
          ∃ B ⊆ A, η * (S.card : ℝ)^2 ≤ B.card ∧
            ∀ L ∈ B, ∀ i, eval (fun j => mark i L j) F = 0 := by
  induction k with
  | zero =>
    refine ⟨0, δ, hδ, 0, ?_⟩
    intro S A mark _ _ _ _ hA
    exact ⟨1, one_ne_zero, (by simp), A, Finset.Subset.rfl, hA, fun _ _ i => i.elim0⟩
  | succ k ih =>
    obtain ⟨d, α, hα, N, hfirst⟩ := ih
    obtain ⟨e, β, hβ, M, hlast⟩ := capture_one h1 α hα
    refine ⟨d + e, β, hβ, max N M, ?_⟩
    intro S A mark hN hS hA hp hdense
    obtain ⟨F, hF, hFd, B, hBA, hB, hroots⟩ :=
      hfirst S A (fun i => mark i.castSucc) ((le_max_left N M).trans hN)
        hS hA (fun i => hp i.castSucc) hdense
    obtain ⟨G, hG, hGe, C, hCB, hC, hlastroot⟩ :=
      hlast S B (mark (Fin.last k)) ((le_max_right N M).trans hN) hS
        (fun L hL => hA L (hBA hL)) (fun L hL => hp _ L (hBA hL)) hB
    refine ⟨F * G, mul_ne_zero hF hG, (totalDegree_mul F G).trans (Nat.add_le_add hFd hGe),
      C, hCB.trans hBA, hC, ?_⟩
    intro L hL i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [hlastroot L hL]
    · simp [hroots L (hCB hL) j]

lemma enumerate_four {S : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)}
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    ∃ mark : Fin 4 → AffineSubspace ℝ ℝ² → ℝ²,
      (∀ i, ∀ L ∈ A, mark i L ∈ S ∧ mark i L ∈ L) ∧
      ∀ L ∈ A, ∀ p ∈ S, p ∈ L → ∃ i, mark i L = p := by
  let U (L : AffineSubspace ℝ ℝ²) := S.filter (fun p => p ∈ L)
  let mark (i : Fin 4) (L : AffineSubspace ℝ ℝ²) : ℝ² :=
    if hL : L ∈ A then
      ((Finset.equivFinOfCardEq (s := U L) (four_points (hA L hL))).symm i).val
    else 0
  refine ⟨mark, ?_, ?_⟩
  · intro i L hL
    simp only [mark, dif_pos hL]
    exact Finset.mem_filter.mp (Subtype.property _)
  · intro L hL p hp hpL
    let e : U L ≃ Fin 4 := Finset.equivFinOfCardEq (four_points (hA L hL))
    let a : U L := ⟨p, Finset.mem_filter.mpr ⟨hp, hpL⟩⟩
    refine ⟨e a, ?_⟩
    simpa only [mark, dif_pos hL] using congrArg Subtype.val (e.symm_apply_apply a)

/-- Retaining every point of a four-point line keeps that line in the count. -/
lemma mem_after_restriction {S T : Finset ℝ²} (hTS : T ⊆ S) {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) (hkeep : ∀ p ∈ S, p ∈ L → p ∈ T) :
    L ∈ linesWithPointsFor 4 (T : Set ℝ²) := by
  obtain ⟨⟨a, ha, b, hb, hab, he⟩, hcard⟩ := hL
  have haL : a ∈ L := he ▸ left_mem_affineSpan_pair ℝ a b
  have hbL : b ∈ L := he ▸ right_mem_affineSpan_pair ℝ a b
  refine ⟨⟨a, hkeep a ha haL, b, hkeep b hb hbL, hab, he⟩, ?_⟩
  have hinter : (L : Set ℝ²) ∩ T = (L : Set ℝ²) ∩ S :=
    Set.ext fun p => ⟨fun h => ⟨h.1, hTS h.2⟩, fun h => ⟨h.1, hkeep p h.2 h.1⟩⟩
  rw [hinter]
  exact hcard

/-- Removing k points destroys at most k times (n−1)/3 four-point lines.
This also controls configurations with a small exceptional set off a curve. -/
lemma delete_points_bound {S T : Finset ℝ²} (hTS : T ⊆ S) :
    3 * (linesWithPointsFor 4 (S : Set ℝ²)).ncard ≤
      3 * (linesWithPointsFor 4 (T : Set ℝ²)).ncard + (S \ T).card * (S.card - 1) := by
  let A := (four_lines_finite S).toFinset
  let B := (four_lines_finite T).toFinset
  let through := fun p : ℝ² => A.filter (fun L => p ∈ L)
  have hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) :=
    fun _ hL => (four_lines_finite S).mem_toFinset.mp hL
  have cover : A ⊆ B ∪ (S \ T).biUnion through := by
    intro L hL
    by_cases hkeep : ∀ p ∈ S, p ∈ L → p ∈ T
    · exact Finset.mem_union_left _ ((four_lines_finite T).mem_toFinset.mpr
        (mem_after_restriction hTS (hA L hL) hkeep))
    · push Not at hkeep
      obtain ⟨p, hp, hpL, hdel⟩ := hkeep
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_sdiff.mpr ⟨hp, hdel⟩, Finset.mem_filter.mpr ⟨hL, hpL⟩⟩)
  have hsum : 3 * (∑ p ∈ S \ T, (through p).card) ≤ (S \ T).card * (S.card - 1) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _p ∈ S \ T, (S.card - 1) :=
        Finset.sum_le_sum fun p hp => pencil_bound hA (Finset.mem_sdiff.mp hp).1
      _ = _ := by simp
  have hcount := (Finset.card_le_card cover).trans
    ((Finset.card_union_le ..).trans (Nat.add_le_add_left (Finset.card_biUnion_le ..) B.card))
  rw [Set.ncard_eq_toFinset_card _ (four_lines_finite S),
    Set.ncard_eq_toFinset_card _ (four_lines_finite T)]
  change 3 * A.card ≤ 3 * B.card + (S \ T).card * (S.card - 1)
  omega

/-- The unconditional pair bound on the precise supremum in the problem. -/
lemma max_pair_bound (n : ℕ) : 12 * Erdos101.numLinesWithFourPointMax n ≤ n * (n - 1) := by
  rw [mul_comm 12, ← Nat.le_div_iff_mul_le (by decide : 0 < 12)]
  apply csSup_le'
  rintro b ⟨S, hcard, hfin, _, rfl⟩
  let T := hfin.toFinset
  have he : (T : Set ℝ²) = S := hfin.coe_toFinset
  have hTcard : T.card = n := by simpa [T, ← Set.ncard_eq_toFinset_card] using hcard
  let lineFin := four_lines_finite T
  have h := pair_bound (S := T) (A := lineFin.toFinset)
    (fun _ hL => lineFin.mem_toFinset.mp hL)
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 12), mul_comm]
  rw [← he, Set.ncard_eq_toFinset_card _ lineFin, ← hTcard]
  exact h

lemma configuration_bound (h1 : H1) (h2 : H2) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ S : Finset ℝ², N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
      ((linesWithPointsFor 4 (S : Set ℝ²)).ncard : ℝ) ≤ ε * (S.card : ℝ)^2 := by
  obtain ⟨d, η, hη, N, hcap⟩ := capture_many h1 4 ε hε
  obtain ⟨M, halg⟩ := h2 d (η / 2) (half_pos hη)
  refine ⟨max (max N M) 1, ?_⟩
  intro S hn hS
  have hN := (le_max_left N M).trans ((le_max_left _ 1).trans hn)
  have hM := (le_max_right N M).trans ((le_max_left _ 1).trans hn)
  have hpos : 0 < (S.card : ℝ) := by
    have hh := (le_max_right (max N M) 1).trans hn
    exact_mod_cast (show 0 < S.card by omega)
  let hfin := four_lines_finite S
  let A := hfin.toFinset
  have hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) := fun _ hL => hfin.mem_toFinset.mp hL
  rw [Set.ncard_eq_toFinset_card _ hfin]
  by_contra! hlarge
  obtain ⟨mark, hpoints, hcover⟩ := enumerate_four hA
  obtain ⟨F, hF, hdeg, B, hBA, hB, hzero⟩ := hcap S A mark hN hS hA hpoints hlarge.le
  let T := S.filter (fun p => eval (fun j => p j) F = 0)
  have hTS : T ⊆ S := Finset.filter_subset ..
  have hsub : B ⊆ (four_lines_finite T).toFinset := by
    intro L hL
    apply (four_lines_finite T).mem_toFinset.mpr
    apply mem_after_restriction hTS (hA L (hBA hL))
    intro p hp hpL
    obtain ⟨i, hi⟩ := hcover L (hBA hL) p hp hpL
    exact Finset.mem_filter.mpr ⟨hp, hi ▸ hzero L hL i⟩
  have hub := halg S.card hM T (Finset.card_le_card hTS) (hS.subset hTS) F hF hdeg
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  rw [Set.ncard_eq_toFinset_card _ (four_lines_finite T)] at hub
  have hcard : (B.card : ℝ) ≤ ((four_lines_finite T).toFinset.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have himpossible := hB.trans (hcard.trans hub)
  exact (not_le_of_gt (mul_lt_mul_of_pos_right (half_lt_self hη) (sq_pos_of_pos hpos))) himpossible

theorem main : H1 → H2 → type_of% @Erdos101.erdos_101 := by
  intro h1 h2
  apply IsLittleO.of_bound
  intro ε hε
  obtain ⟨N, hbound⟩ := configuration_bound h1 h2 ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
  have hmax : Erdos101.numLinesWithFourPointMax n ≤ ⌊ε * (n : ℝ)^2⌋₊ := by
    apply csSup_le'
    rintro b ⟨S, hcard, hfin, hS, rfl⟩
    let T := hfin.toFinset
    have he : (T : Set ℝ²) = S := hfin.coe_toFinset
    have hTcard : T.card = n := (Set.ncard_eq_toFinset_card S hfin).symm.trans hcard
    apply Nat.le_floor
    have h := hbound T (hTcard ▸ hn) (he ▸ hS)
    simpa only [he, hTcard] using h
  exact (Nat.cast_le.mpr hmax).trans (Nat.floor_le (mul_nonneg hε.le (sq_nonneg _)))

end OMA.R_Erdos101_erdos_101_R1
