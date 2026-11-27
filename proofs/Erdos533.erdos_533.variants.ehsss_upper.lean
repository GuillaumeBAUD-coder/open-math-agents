import FormalConjectures.ErdosProblems.«533»
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
Use Lemmas 4.2 and 4.3 of Erdős, Hajnal, Simonovits, Sós and Szemerédi (1994)
for a dense pair and a triangle of regular pairs, respectively. The reduced
graph is triangle-free and each retained pair has density at most
`1/3 + η`. Mantel's bound and the regularity error terms then give the
coefficient `1/12`.
-/

-- Credit: @dk8827

open SimpleGraph Finset Finpartition Filter
open scoped BigOperators Pointwise

namespace OMA.R_Erdos533_erdos_533_variants_ehsss_upper_R1

private theorem ordered_edges {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.interedges univ univ).card = 2 * G.edgeFinset.card := by
  rw [G.two_mul_card_edgeFinset, G.interedges_def, univ_product_univ]

def H1 : Prop :=
  ∀ (η : ℝ), 0 < η → η ≤ 1 / 12 →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.CliqueFree 5 →
      ∀ A B : Finset (Fin n), A.Nonempty → B.Nonempty → Disjoint A B →
        G.IsUniform (η ^ 2 / 8) A B →
        (∀ X ⊆ A, (η ^ 2 / 8) * (A.card : ℝ) < (X.card : ℝ) →
          ¬ G.CliqueFreeOn (X : Set (Fin n)) 3) →
        (∀ X ⊆ B, (η ^ 2 / 8) * (B.card : ℝ) < (X.card : ℝ) →
          ¬ G.CliqueFreeOn (X : Set (Fin n)) 3) →
        (G.edgeDensity A B : ℝ) ≤ 1 / 3 + η

def H2 : Prop :=
  ∀ (η : ℝ), 0 < η → η ≤ 1 / 12 →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.CliqueFree 5 →
      ∀ A B C : Finset (Fin n), A.Nonempty → B.Nonempty → C.Nonempty →
        Disjoint A B → Disjoint A C → Disjoint B C →
        G.IsUniform (η ^ 2 / 8) A B → G.IsUniform (η ^ 2 / 8) A C →
        G.IsUniform (η ^ 2 / 8) B C →
        η ≤ (G.edgeDensity A B : ℝ) → η ≤ (G.edgeDensity A C : ℝ) →
        η ≤ (G.edgeDensity B C : ℝ) →
        (∀ X ⊆ C, (η ^ 2 / 8) * (C.card : ℝ) < (X.card : ℝ) →
          ¬ G.CliqueFreeOn (X : Set (Fin n)) 3) → False

set_option maxHeartbeats 1600000 in
theorem main : H1 → H2 → type_of% @Erdos533.erdos_533.variants.ehsss_upper := by
  classical
  intro hdense htriangle ε hε
  let η := min (ε / 20) (1 / 12)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη₁ : η ≤ 1 / 12 := min_le_right _ _
  have hηε : η ≤ ε / 20 := min_le_left _ _
  let ρ : ℝ := η ^ 2 / 8
  have hρ : 0 < ρ := by positivity
  have hρη : ρ ≤ η := by
    dsimp only [ρ]
    nlinarith only [mul_nonneg hη.le (show 0 ≤ 1 - η by linarith only [hη₁])]
  let l : ℕ := ⌈4 / η⌉₊
  have hl : 4 / η ≤ (l : ℝ) := Nat.le_ceil _
  let K := SzemerediRegularity.bound ρ l
  let δ : ℝ := ρ / (4 * ((K : ℝ) + 1))
  refine ⟨δ, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop l, eventually_ge_atTop (1 : ℕ),
    eventually_ge_atTop ⌈((K : ℝ) + 1) / η⌉₊] with n hnl hn1 hnK
  intro G hG hsmall
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hKle : (K : ℝ) + 1 ≤ η * n := by
    have hnK' : ((K : ℝ) + 1) / η ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hnK)
    simpa [mul_comm] using (div_le_iff₀ hη).1 hnK'
  obtain ⟨P, hequi, hPl, hPK, hunif⟩ := szemeredi_regularity G hρ (by simpa using hnl)
  let k := P.parts.card
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hPK
  have hkη : (k : ℝ) ≤ η * n := by linarith only [hkK, hKle]
  have hηhalf : η ≤ 1 / 2 := by linarith
  have hk2 : 2 * k ≤ n := by
    have h := mul_le_mul_of_nonneg_right hηhalf hn0.le
    exact_mod_cast (show (2 : ℝ) * (k : ℝ) ≤ n by linarith only [h, hkη])
  have hlarge : 4 / η ≤ (P.parts.card : ℝ) := hl.trans (by exact_mod_cast hPl)
  have hk0 : 0 < k := by
    have h := (div_pos (by norm_num : (0 : ℝ) < 4) hη).trans_le hlarge
    exact_mod_cast h
  let t := n / k + 1
  have ht (A : Finset (Fin n)) (hA : A ∈ P.parts) : A.card ≤ t := by
    simpa [t, k] using hequi.card_part_le_average_add_one hA
  have hpart (A : Finset (Fin n)) (hA : A ∈ P.parts) : (n : ℝ) ≤ 2 * k * A.card := by
    have hdiv : n ≤ 2 * k * (n / k) := by
      have hrem := Nat.mod_lt n hk0
      have hf := Nat.mod_add_div n k
      have hnk : k ≤ k * (n / k) := by
        simpa using Nat.mul_le_mul_left k (Nat.one_le_div_iff hk0 |>.2 (by omega : k ≤ n))
      rw [Nat.mul_assoc, two_mul]
      omega
    have ha : n / k ≤ A.card := by simpa [k] using hequi.average_le_card_part hA
    exact_mod_cast hdiv.trans (Nat.mul_le_mul_left _ ha)
  have triangle_rich (A : Finset (Fin n)) (ha : A ∈ P.parts) :
      ∀ X ⊆ A, ρ * (A.card : ℝ) < (X.card : ℝ) → ¬ G.CliqueFreeOn (X : Set (Fin n)) 3 := by
    intro X _ hx hX
    have h := hpart A ha
    have hindeed : δ * n ≤ ρ * (A.card : ℝ) := by
      calc
        _ ≤ δ * (2 * k * A.card) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = (δ * (2 * k)) * A.card := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ?_ (by positivity)
      dsimp only [δ]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((K : ℝ) + 1))).2
      nlinarith only [mul_le_mul_of_nonneg_left hkK hρ.le, hρ]
    exact (not_lt_of_ge (hsmall X hX)) (hindeed.trans_lt hx)
  let R : SimpleGraph ↥P.parts :=
    { Adj := fun A B => A ≠ B ∧ G.IsUniform ρ A.1 B.1 ∧ η ≤ (G.edgeDensity A.1 B.1 : ℝ)
      symm := ⟨fun A B h => ⟨h.1.symm, h.2.1.symm, by
        rw [G.edgeDensity_comm]
        exact h.2.2⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  have hR : R.CliqueFree 3 := by
    intro S hS
    obtain ⟨A, B, C, hAB, hAC, hBC, _⟩ := R.is3Clique_iff.1 hS
    have sep {a b : ↥P.parts} (h : a ≠ b) : Disjoint a.1 b.1 :=
      P.disjoint a.2 b.2 (fun he => h (Subtype.ext he))
    exact htriangle η hη hη₁ n G hG A.1 B.1 C.1
      (P.nonempty_of_mem_parts A.2) (P.nonempty_of_mem_parts B.2) (P.nonempty_of_mem_parts C.2)
      (sep hAB.1) (sep hAC.1) (sep hBC.1)
      hAB.2.1 hAC.2.1 hBC.2.1 hAB.2.2 hAC.2.2 hBC.2.2 (triangle_rich C.1 C.2)
  let D := (R.interedges univ univ).image (fun e => (e.1.1, e.2.1))
  have hmantel : R.edgeFinset.card ≤ k ^ 2 / 4 := by
    have h := hR.card_edgeFinset_le (r := 2)
    dsimp only at h
    rw [Fintype.card_coe] at h
    change R.edgeFinset.card ≤ (k ^ 2 - (k % 2) ^ 2) * (2 - 1) / (2 * 2) + (k % 2).choose 2 at h
    rw [Nat.choose_eq_zero_of_lt (Nat.mod_lt k (by decide : 0 < 2))] at h
    norm_num at h
    exact h.trans (Nat.div_le_div_right (Nat.sub_le _ _))
  have hDc : (D.card : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    have hD0 : D.card ≤ 2 * R.edgeFinset.card := card_image_le.trans (ordered_edges R).le
    have hh : R.edgeFinset.card * 4 ≤ k ^ 2 :=
      (Nat.mul_le_mul_right 4 hmantel).trans (Nat.div_mul_le_self _ _)
    have hD' : (D.card : ℝ) ≤ 2 * (R.edgeFinset.card : ℝ) := by exact_mod_cast hD0
    have hh' : (R.edgeFinset.card : ℝ) * 4 ≤ (k : ℝ) ^ 2 := by exact_mod_cast hh
    linarith only [hD', hh']
  let F := D.biUnion (fun (A,B) => G.interedges A B)
  have hterm (e : Finset (Fin n) × Finset (Fin n)) (he : e ∈ D) :
      ((G.interedges e.1 e.2).card : ℝ) ≤ (1 / 3 + η) * (t : ℝ) ^ 2 := by
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := mem_image.1 he
    obtain ⟨_, _, hadj⟩ := (R.mem_interedges_iff).1 hAB
    have hnA := P.nonempty_of_mem_parts A.2
    have hnB := P.nonempty_of_mem_parts B.2
    have hbound := hdense η hη hη₁ n G hG A.1 B.1 hnA hnB
      (P.disjoint A.2 B.2 (fun e => hadj.1 (Subtype.ext e))) hadj.2.1
      (triangle_rich _ A.2) (triangle_rich _ B.2)
    have hrat : ((G.interedges A.1 B.1).card : ℝ) / ((A.1.card : ℝ) * B.1.card) ≤
        1 / 3 + η := by
      simpa only [G.edgeDensity_def, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast] using hbound
    have hcard := (div_le_iff₀ (by positivity : 0 < (A.1.card : ℝ) * B.1.card)).1 hrat
    refine hcard.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [pow_two]
    exact_mod_cast Nat.mul_le_mul (ht _ A.2) (ht _ B.2)
  have hkt : (k : ℝ) * t ≤ (1 + η) * n := by
    have hnat : k * t ≤ n + k := by
      dsimp only [t]
      rw [mul_add, mul_one, mul_comm k (n / k)]
      exact Nat.add_le_add_right (Nat.div_mul_le_self n k) _
    have hh : (k : ℝ) * t ≤ (n : ℝ) + k := by exact_mod_cast hnat
    nlinarith only [hh, hkη]
  have hF : (F.card : ℝ) ≤ (1 / 6 + 2 * η) * (n : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ e ∈ D, ((G.interedges e.1 e.2).card : ℝ) := by
        exact_mod_cast (card_biUnion_le (s := D) (t := fun e => G.interedges e.1 e.2))
      _ ≤ ∑ _e ∈ D, (1 / 3 + η) * (t : ℝ) ^ 2 := sum_le_sum hterm
      _ = (D.card : ℝ) * ((1 / 3 + η) * (t : ℝ) ^ 2) := by simp
      _ ≤ ((k : ℝ) ^ 2 / 2) * ((1 / 3 + η) * (t : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hDc (by positivity)
      _ = ((1 / 3 + η) / 2) * ((k : ℝ) * t) ^ 2 := by ring
      _ ≤ ((1 / 3 + η) / 2) * ((1 + η) * (n : ℝ)) ^ 2 := by gcongr
      _ = (((1 / 3 + η) / 2) * (1 + η) ^ 2) * (n : ℝ) ^ 2 := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hsq : (1 + η) ^ 2 ≤ 1 + 3 * η := by
          nlinarith only [mul_nonneg hη.le (show 0 ≤ 1 - η by linarith)]
        have hmore := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (1 / 3 + η) / 2 by positivity)
        nlinarith only [hmore, mul_nonneg hη.le (show 0 ≤ 1 / 12 - η by linarith)]
  let I := (P.nonUniforms G ρ).biUnion (fun (A,B) => A ×ˢ B)
  let J := P.parts.biUnion offDiag
  let L := (P.sparsePairs G η).biUnion (fun (A,B) => G.interedges A B)
  have hcov : G.interedges univ univ ⊆ I ∪ J ∪ L ∪ F := by
    intro e he
    have ha := ((G.mem_interedges_iff).1 he).2.2
    have hx : e.1 ∈ P.parts.biUnion id := by rw [P.biUnion_parts]; simp
    have hy : e.2 ∈ P.parts.biUnion id := by rw [P.biUnion_parts]; simp
    obtain ⟨A, hA, hx⟩ := mem_biUnion.1 hx
    obtain ⟨B, hB, hy⟩ := mem_biUnion.1 hy
    by_cases hab : A = B
    · subst B
      exact mem_union_left _ (mem_union_left _ (mem_union_right _
        (mem_biUnion.2 ⟨A, hA, mem_offDiag.2 ⟨hx, hy, ha.ne⟩⟩)))
    by_cases hu : G.IsUniform ρ A B
    · by_cases hd : η ≤ (G.edgeDensity A B : ℝ)
      · refine mem_union_right _ (mem_biUnion.2 ⟨(A, B), ?_, G.mem_interedges_iff.2 ⟨hx, hy, ha⟩⟩)
        exact mem_image.2 ⟨(⟨A, hA⟩, ⟨B, hB⟩),
          R.mem_interedges_iff.2 ⟨mem_univ _, mem_univ _, fun hh => hab (congrArg Subtype.val hh),
            hu, hd⟩, rfl⟩
      · exact mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨(A, B),
          (P.mk_mem_sparsePairs G A B η).2 ⟨hA, hB, hab, lt_of_not_ge hd⟩,
          G.mem_interedges_iff.2 ⟨hx, hy, ha⟩⟩))
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_biUnion.2 ⟨(A, B),
        (P.mk_mem_nonUniforms G).2 ⟨hA, hB, hab, hu⟩, mem_product.2 ⟨hx, hy⟩⟩)))
  have hI : (I.card : ℝ) ≤ 4 * ρ * (n : ℝ) ^ 2 := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    simpa [I] using (hequi.sum_nonUniforms_lt univ_nonempty hρ hunif).le
  have hJ : (J.card : ℝ) ≤ η / 2 * (n : ℝ) ^ 2 := by
    simpa [J] using hequi.card_biUnion_offDiag_le hη hlarge
  have hL : (L.card : ℝ) ≤ 4 * η * (n : ℝ) ^ 2 := by
    simpa [L] using hequi.card_interedges_sparsePairs_le (G := G) hη.le
  have hcount : 2 * (G.edgeFinset.card : ℝ) ≤ (I.card : ℝ) + J.card + L.card + F.card := by
    have hnat := (card_le_card hcov).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right ((card_union_le _ _).trans
        (Nat.add_le_add_right (card_union_le _ _) _)) _))
    rw [ordered_edges G] at hnat
    exact_mod_cast hnat
  have hsmallρ := mul_le_mul_of_nonneg_right hρη (sq_nonneg (n : ℝ))
  have hsmallη := mul_le_mul_of_nonneg_right hηε (sq_nonneg (n : ℝ))
  nlinarith only [hcount, hI, hJ, hL, hF, hsmallρ, hsmallη,
    mul_nonneg hε.le (sq_nonneg (n : ℝ))]

end OMA.R_Erdos533_erdos_533_variants_ehsss_upper_R1

namespace OMA.RamseyTuranLocal

private theorem interedge_degree_sum {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) :
    (G.interedges A B).card = ∑ a ∈ A, (B.filter (G.Adj a)).card := by
  rw [SimpleGraph.interedges, Rel.interedges_eq_biUnion, card_biUnion]
  · simp
  · intro a _ b _ hab
    apply Finset.disjoint_left.2
    intro x ha hb
    obtain ⟨y, _, ey⟩ := mem_map.1 ha
    obtain ⟨z, _, ez⟩ := mem_map.1 hb
    exact hab (congrArg Prod.fst (ey.trans ez.symm))

private theorem interedge_density {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty) :
    ((G.interedges A B).card : ℝ) =
      (G.edgeDensity A B : ℝ) * ((A.card : ℝ) * B.card) := by
  rw [G.edgeDensity_def, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_natCast,
    Rat.cast_natCast, div_mul_cancel₀ _ (by positivity)]

private theorem few_bad_vertices {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) (hB : B.Nonempty) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hU : G.IsUniform ρ A B) :
    let D := A.filter (fun a =>
      ((B.filter (G.Adj a)).card : ℝ) <
        ((G.edgeDensity A B : ℝ) - ρ) * B.card)
    (D.card : ℝ) ≤ ρ * A.card := by
  dsimp only
  let c := ((G.edgeDensity A B : ℝ) - ρ) * B.card
  let D := A.filter (fun a => ((B.filter (G.Adj a)).card : ℝ) < c)
  change (D.card : ℝ) ≤ ρ * A.card
  by_contra! h
  have hnD : D.Nonempty := card_pos.1 (by
    exact_mod_cast ((mul_nonneg hρ.le (Nat.cast_nonneg _)).trans_lt h))
  have hu := hU (filter_subset _ _) (Subset.rfl : B ⊆ B)
    (by simpa [mul_comm] using h.le) (mul_le_of_le_one_right (Nat.cast_nonneg _) hρ₁)
  have hlow : (G.edgeDensity A B : ℝ) - ρ < (G.edgeDensity D B : ℝ) := by
    linarith only [(abs_lt.1 hu).1]
  have hsum : ((G.interedges D B).card : ℝ) ≤ (D.card : ℝ) * c := by
    rw [interedge_degree_sum, Nat.cast_sum]
    calc
      _ ≤ ∑ _a ∈ D, c := sum_le_sum (fun a ha => (mem_filter.1 ha).2.le)
      _ = _ := by simp
  have hd : 0 < (D.card : ℝ) * B.card := by positivity
  rw [interedge_density G hnD hB] at hsum
  have hhigh : (G.edgeDensity D B : ℝ) ≤ (G.edgeDensity A B : ℝ) - ρ := by
    apply le_of_mul_le_mul_right _ hd
    calc
      _ ≤ (D.card : ℝ) * c := hsum
      _ = _ := by dsimp only [c]; ring
  exact hlow.not_ge hhigh

private theorem triangle_in {V : Type} {G : SimpleGraph V} {S : Finset V}
    (h : ¬ G.CliqueFreeOn (S : Set V) 3) :
    ∃ T : Finset V, T ⊆ S ∧ G.IsNClique 3 T := by
  classical
  by_contra hn
  apply h
  intro T hTS hT
  exact hn ⟨T, hTS, hT⟩

private theorem common_neighbours_triangleFree {V : Type} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hf : G.CliqueFree 5)
    {a b : V} (hab : G.Adj a b) (B : Finset V) :
    G.CliqueFreeOn ((B.filter (fun x => G.Adj a x ∧ G.Adj b x)) : Set V) 3 := by
  intro T hT hcl
  have joined (v : V) (hv : v ∈ T) : G.Adj a v ∧ G.Adj b v :=
    (mem_filter.1 (hT hv)).2
  have ht4 := hcl.insert (fun x hx => (joined x hx).2)
  have ht5 := ht4.insert (fun x hx => by
    rcases mem_insert.1 hx with rfl | hx
    · exact hab
    · exact (joined x hx).1)
  exact hf _ ht5

private theorem three_degrees {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b c : V) (B : Finset V) :
    (B.filter (G.Adj a)).card + (B.filter (G.Adj b)).card + (B.filter (G.Adj c)).card ≤
      B.card + (B.filter (fun x => G.Adj a x ∧ G.Adj b x)).card +
      (B.filter (fun x => G.Adj a x ∧ G.Adj c x)).card +
      (B.filter (fun x => G.Adj b x ∧ G.Adj c x)).card := by
  simp only [card_filter]
  rw [card_eq_sum_ones B]
  simp only [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases ha : G.Adj a x <;> by_cases hb : G.Adj b x <;> by_cases hc : G.Adj c x <;>
    simp [ha, hb, hc]

private theorem degree_at_least_average {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ a ∈ A, (G.edgeDensity A B : ℝ) * B.card ≤ (B.filter (G.Adj a)).card := by
  by_contra! h
  have hsum : ((G.interedges A B).card : ℝ) <
      (A.card : ℝ) * ((G.edgeDensity A B : ℝ) * B.card) := by
    rw [interedge_degree_sum, Nat.cast_sum, ← nsmul_eq_mul, ← sum_const]
    obtain ⟨a, ha⟩ := hA
    exact sum_lt_sum (fun b hb => (h b hb).le) ⟨a, ha, h a ha⟩
  rw [interedge_density G (by assumption) (by assumption)] at hsum
  nlinarith only [hsum]


theorem dense_pair (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 12)
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hf : G.CliqueFree 5)
    (A B : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty) (_hAB : Disjoint A B)
    (hu : G.IsUniform (η ^ 2 / 8) A B)
    (rich_A : ∀ X ⊆ A, (η ^ 2 / 8) * (A.card : ℝ) < (X.card : ℝ) →
      ¬ G.CliqueFreeOn (X : Set (Fin n)) 3)
    (rich_B : ∀ X ⊆ B, (η ^ 2 / 8) * (B.card : ℝ) < (X.card : ℝ) →
      ¬ G.CliqueFreeOn (X : Set (Fin n)) 3) :
    (G.edgeDensity A B : ℝ) ≤ 1 / 3 + η := by
  classical
  by_contra! hd
  let ρ : ℝ := η ^ 2 / 8
  have hρ : 0 < ρ := by positivity
  have h2ρ : 2 * ρ < η := by
    dsimp only [ρ]
    nlinarith only [hη, mul_nonneg hη.le (show 0 ≤ 1 - η by linarith only [hη₁])]
  have hρ₁ : ρ ≤ 1 := by linarith only [hρ, h2ρ, hη₁]
  let N (v : Fin n) := B.filter (G.Adj v)
  let D := A.filter (fun v => ((N v).card : ℝ) < ((G.edgeDensity A B : ℝ) - ρ) * B.card)
  let U := A \ D
  have hD : (D.card : ℝ) ≤ ρ * A.card := few_bad_vertices G A B hB hρ hρ₁ hu
  have hA0 : (0 : ℝ) < A.card := by positivity
  have hB0 : (0 : ℝ) < B.card := by positivity
  have hUeq : (U.card : ℝ) + D.card = A.card := by
    exact_mod_cast card_sdiff_add_card_eq_card (filter_subset _ A)
  have hU : ρ * (A.card : ℝ) < U.card := by
    have h := mul_lt_mul_of_pos_right (show 2 * ρ < 1 by linarith only [h2ρ, hη₁]) hA0
    linarith only [h, hD, hUeq]
  obtain ⟨T, hTU, hT⟩ := triangle_in (rich_A U sdiff_subset hU)
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := G.is3Clique_iff.1 hT
  have hdeg (v : Fin n) (hv : v ∈ U) :
      (1 / 3 + η - ρ) * (B.card : ℝ) ≤ (N v).card := by
    have hd' : ¬ ((N v).card : ℝ) < ((G.edgeDensity A B : ℝ) - ρ) * B.card := by
      intro hh
      exact (mem_sdiff.1 hv).2 (mem_filter.2 ⟨(mem_sdiff.1 hv).1, hh⟩)
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hd.le _) hB0.le).trans (le_of_not_gt hd')
  have ha := hdeg a (hTU (by simp))
  have hb := hdeg b (hTU (by simp))
  have hc := hdeg c (hTU (by simp))
  have hpair (v w : Fin n) (hvw : G.Adj v w) :
      ((B.filter (fun z => G.Adj v z ∧ G.Adj w z)).card : ℝ) ≤ ρ * B.card := by
    by_contra! hh
    exact rich_B _ (filter_subset _ _) hh (common_neighbours_triangleFree hf hvw B)
  have hpairs :
      ((N a).card : ℝ) + (N b).card + (N c).card ≤
        (B.card : ℝ) + (B.filter (fun z => G.Adj a z ∧ G.Adj b z)).card +
        (B.filter (fun z => G.Adj a z ∧ G.Adj c z)).card +
        (B.filter (fun z => G.Adj b z ∧ G.Adj c z)).card := by
    exact_mod_cast three_degrees G a b c B
  have hstrict := mul_lt_mul_of_pos_right h2ρ hB0
  nlinarith only [ha, hb, hc, hpair a b hab, hpair a c hac, hpair b c hbc, hpairs, hstrict]

theorem uniform_triangle (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 12)
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hf : G.CliqueFree 5)
    (A B C : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (_hAB : Disjoint A B) (_hAC : Disjoint A C) (_hBC : Disjoint B C)
    (uAB : G.IsUniform (η ^ 2 / 8) A B) (uAC : G.IsUniform (η ^ 2 / 8) A C)
    (uBC : G.IsUniform (η ^ 2 / 8) B C)
    (dAB : η ≤ (G.edgeDensity A B : ℝ)) (dAC : η ≤ (G.edgeDensity A C : ℝ))
    (dBC : η ≤ (G.edgeDensity B C : ℝ))
    (rich_C : ∀ X ⊆ C, (η ^ 2 / 8) * (C.card : ℝ) < (X.card : ℝ) →
      ¬ G.CliqueFreeOn (X : Set (Fin n)) 3) : False := by
  classical
  let ρ : ℝ := η ^ 2 / 8
  have hρ : 0 < ρ := by positivity
  have h2ρ : 2 * ρ < η := by
    dsimp only [ρ]
    nlinarith only [hη, mul_nonneg hη.le (show 0 ≤ 1 - η by linarith only [hη₁])]
  have hρ₁ : ρ ≤ 1 := by linarith only [hρ, h2ρ, hη₁]
  let bad (X : Finset (Fin n)) := A.filter (fun v =>
    ((X.filter (G.Adj v)).card : ℝ) < ((G.edgeDensity A X : ℝ) - ρ) * X.card)
  have hBbad : ((bad B).card : ℝ) ≤ ρ * A.card := few_bad_vertices G A B hB hρ hρ₁ uAB
  have hCbad : ((bad C).card : ℝ) ≤ ρ * A.card := few_bad_vertices G A C hC hρ hρ₁ uAC
  let D := bad B ∪ bad C
  have hD : D ⊆ A := union_subset (filter_subset _ _) (filter_subset _ _)
  have hDA : D.card < A.card := by
    have h : (D.card : ℝ) ≤ ((bad B).card : ℝ) + (bad C).card := by
      exact_mod_cast card_union_le (bad B) (bad C)
    have hs := mul_lt_mul_of_pos_right (show 2 * ρ < 1 by linarith only [h2ρ, hη₁])
      (show (0 : ℝ) < A.card by positivity)
    exact_mod_cast (show (D.card : ℝ) < A.card by linarith only [h, hs, hBbad, hCbad])
  have hU : (A \ D).Nonempty := card_pos.1 (by
    rw [card_sdiff_of_subset hD]
    omega)
  obtain ⟨a, ha⟩ := hU
  have hgood (X : Finset (Fin n)) (haX : a ∉ bad X) (hDX : η ≤ (G.edgeDensity A X : ℝ)) :
      (η - ρ) * (X.card : ℝ) ≤ (X.filter (G.Adj a)).card := by
    have hx : ((G.edgeDensity A X : ℝ) - ρ) * X.card ≤ (X.filter (G.Adj a)).card := by
      by_contra! hh
      exact haX (mem_filter.2 ⟨(mem_sdiff.1 ha).1, hh⟩)
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hDX ρ) (by positivity)).trans hx
  let B' := B.filter (G.Adj a)
  let C' := C.filter (G.Adj a)
  have hB' : (η - ρ) * (B.card : ℝ) ≤ B'.card :=
    hgood B (fun h => (mem_sdiff.1 ha).2 (mem_union_left _ h)) dAB
  have hC' : (η - ρ) * (C.card : ℝ) ≤ C'.card :=
    hgood C (fun h => (mem_sdiff.1 ha).2 (mem_union_right _ h)) dAC
  have hηρ : 0 < η - ρ := by linarith only [h2ρ, hρ]
  have hB'0 : B'.Nonempty := card_pos.1 (by exact_mod_cast
    (mul_pos hηρ (show (0 : ℝ) < B.card by positivity)).trans_le hB')
  have hC'0 : C'.Nonempty := card_pos.1 (by exact_mod_cast
    (mul_pos hηρ (show (0 : ℝ) < C.card by positivity)).trans_le hC')
  have small_part (X Y : Finset (Fin n)) (hX : (η - ρ) * (X.card : ℝ) ≤ Y.card) :
      (X.card : ℝ) * ρ ≤ (Y.card : ℝ) := by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right (by linarith only [h2ρ]) (by positivity)).trans hX
  have hU' := uBC (filter_subset _ _) (filter_subset _ _) (small_part B B' hB') (small_part C C' hC')
  change |(G.edgeDensity B' C' : ℝ) - (G.edgeDensity B C : ℝ)| < ρ at hU'
  have hD' : η - ρ ≤ (G.edgeDensity B' C' : ℝ) := by
    linarith only [(abs_lt.1 hU').1, dBC]
  obtain ⟨b, hb, hdegree⟩ := degree_at_least_average G hB'0 hC'0
  let T := C.filter (fun z => G.Adj a z ∧ G.Adj b z)
  have hT : C'.filter (G.Adj b) = T := filter_filter _ _ _
  have hsize : (η - ρ) ^ 2 * (C.card : ℝ) ≤ T.card := by
    calc
      _ = (η - ρ) * ((η - ρ) * (C.card : ℝ)) := by ring
      _ ≤ (η - ρ) * C'.card := mul_le_mul_of_nonneg_left hC' hηρ.le
      _ ≤ (G.edgeDensity B' C' : ℝ) * C'.card :=
        mul_le_mul_of_nonneg_right hD' (by positivity)
      _ ≤ _ := hT ▸ hdegree
  have hρsq : ρ < (η - ρ) ^ 2 := by
    have hlo : η / 2 ≤ η - ρ := by linarith only [h2ρ]
    have he : (η / 2) ^ 2 ≤ (η - ρ) ^ 2 := by gcongr
    dsimp only [ρ] at he ⊢
    nlinarith only [he, sq_pos_of_pos hη]
  have hTemp := mul_lt_mul_of_pos_right hρsq (show (0 : ℝ) < C.card by positivity)
  exact rich_C T (filter_subset _ _) (hTemp.trans_le hsize)
    (common_neighbours_triangleFree hf (mem_filter.1 hb).2 C)

end OMA.RamseyTuranLocal

theorem OMA.solution : type_of% @Erdos533.erdos_533.variants.ehsss_upper :=
  OMA.R_Erdos533_erdos_533_variants_ehsss_upper_R1.main
    OMA.RamseyTuranLocal.dense_pair OMA.RamseyTuranLocal.uniform_triangle
