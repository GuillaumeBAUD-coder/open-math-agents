import FormalConjectures.ErdosProblems.«104»
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset

-- Reduction Erdos104.erdos_104.R1 of Erdős Problem 104
-- Credit: @JamesSlash
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! Thinning reduces unit circles through at least three points to circles through exactly
three. Circles with a diametral pair of contacts are covered by H2 (a fixed-chord count, provable
by a fixed-distance incidence bound); the remaining exact-three circles are H1, the hard part. -/

open EuclideanGeometry Finset
open scoped EuclideanGeometry

namespace OMA.R_Erdos104_erdos_104_R1

-- Hard part: unit circles with exactly three contacts and no diametral pair of contacts.
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : Finset ℝ², P.card ≤ n →
    (({s : Sphere ℝ² | s.radius = 1 ∧ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard = 3} \
      {s : Sphere ℝ² | s.radius = 1 ∧
        ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = 2 ∧ a ∈ s ∧ b ∈ s}).ncard : ℝ) ≤ ε * (n : ℝ) ^ 2

-- Unit circles through two points of the set at a prescribed distance are uniformly o(n^2).
def H2 : Prop :=
  ∀ d ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : Finset ℝ², P.card ≤ n →
    ({s : Sphere ℝ² | s.radius = 1 ∧
      ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = d ∧ a ∈ s ∧ b ∈ s}.ncard : ℝ) ≤ ε * (n : ℝ) ^ 2


namespace RichIncidences


variable {Point Circle : Type*} [DecidableEq Point]

private theorem samples_with_three {P D : Finset Point} (hDP : D ⊆ P) (hD : 3 ≤ D.card) :
    2 ^ (P.card - D.card) ≤ (P.powerset.filter fun Q => (Q ∩ D).card = 3).card := by
  obtain ⟨T, hTD, hT⟩ := exists_subset_card_eq hD
  have hmap : Set.MapsTo (fun R : Finset Point => R ∪ T) ↑(P \ D).powerset
      ↑(P.powerset.filter fun Q => (Q ∩ D).card = 3) := by
    intro R hR
    have hsub : R ⊆ P \ D := mem_powerset.mp hR
    have hdis : Disjoint R D := disjoint_of_subset_left hsub disjoint_sdiff_self_left
    have hEq : (R ∪ T) ∩ D = T := by
      rw [union_inter_distrib_right, disjoint_iff_inter_eq_empty.mp hdis,
        inter_eq_left.mpr hTD, empty_union]
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, by rwa [hEq]⟩
    exact union_subset (hsub.trans sdiff_subset) (hTD.trans hDP)
  have hinj : Set.InjOn (fun R : Finset Point => R ∪ T) ↑(P \ D).powerset := by
    intro R hR S hS h
    have hdR : Disjoint R T :=
      (disjoint_of_subset_left (mem_powerset.mp hR) disjoint_sdiff_self_left).mono_right hTD
    have hdS : Disjoint S T :=
      (disjoint_of_subset_left (mem_powerset.mp hS) disjoint_sdiff_self_left).mono_right hTD
    simpa only [union_sdiff_cancel_right hdR, union_sdiff_cancel_right hdS] using
      congrArg (fun Q : Finset Point => Q \ T) h
  simpa only [card_powerset, card_sdiff_of_subset hDP] using
    card_le_card_of_injOn _ hmap hinj

private theorem exchange_counts (P : Finset Point) (S : Finset Circle) (D : Circle → Finset Point) :
    (∑ c ∈ S, (P.powerset.filter fun Q => (Q ∩ D c).card = 3).card) =
      ∑ Q ∈ P.powerset, (S.filter fun c => (Q ∩ D c).card = 3).card := by
  have h : (∑ c ∈ S, ∑ Q ∈ P.powerset, if (Q ∩ D c).card = 3 then (1 : ℕ) else 0) =
      ∑ Q ∈ P.powerset, ∑ c ∈ S, if (Q ∩ D c).card = 3 then (1 : ℕ) else 0 := Finset.sum_comm
  simpa only [Finset.sum_boole, Nat.cast_id] using h

/-- A single subset retains exactly three incidences at a fixed fraction of the bounded degrees. -/
theorem thin_to_three (P : Finset Point) (S : Finset Circle) (D : Circle → Finset Point) (k : ℕ)
    (hD : ∀ c ∈ S, D c ⊆ P)
    (hdeg : ∀ c ∈ S, 3 ≤ (D c).card ∧ (D c).card ≤ k) :
    ∃ Q ⊆ P, S.card ≤ 2 ^ k * (S.filter fun c => (Q ∩ D c).card = 3).card := by
  classical
  have hper (c : Circle) (hc : c ∈ S) :
      2 ^ P.card ≤ 2 ^ k * (P.powerset.filter fun Q => (Q ∩ D c).card = 3).card := by
    have hle := card_le_card (hD c hc)
    calc
      _ ≤ 2 ^ (k + (P.card - (D c).card)) :=
        Nat.pow_le_pow_right (by decide) (by have := (hdeg c hc).2; omega)
      _ = 2 ^ k * 2 ^ (P.card - (D c).card) := pow_add 2 _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (samples_with_three (hD c hc) (hdeg c hc).1)
  have hsum : P.powerset.card * S.card ≤
      ∑ Q ∈ P.powerset, 2 ^ k * (S.filter fun c => (Q ∩ D c).card = 3).card := by
    rw [card_powerset, ← mul_comm S.card, ← Nat.nsmul_eq_mul, ← sum_const, ← mul_sum,
      ← exchange_counts, mul_sum]
    exact sum_le_sum hper
  by_contra! h
  have hstrict : (∑ Q ∈ P.powerset, 2 ^ k * (S.filter fun c => (Q ∩ D c).card = 3).card) <
      ∑ _Q ∈ P.powerset, S.card :=
    sum_lt_sum_of_nonempty ⟨∅, mem_powerset.mpr (empty_subset _)⟩
      fun Q hQ => h Q (mem_powerset.mp hQ)
  rw [sum_const, Nat.nsmul_eq_mul] at hstrict
  exact (not_lt_of_ge hsum) hstrict

private theorem pairs_exchange (P : Finset Point) (T : Finset Circle) (D : Circle → Finset Point)
    (hD : ∀ c ∈ T, D c ⊆ P) :
    (∑ c ∈ T, (D c).offDiag.card) =
      ∑ p ∈ P.offDiag, (T.filter fun c => p.1 ∈ D c ∧ p.2 ∈ D c).card := by
  classical
  have hrow (c : Circle) (hc : c ∈ T) :
      (D c).offDiag = P.offDiag.filter (fun p => p.1 ∈ D c ∧ p.2 ∈ D c) := by
    ext p
    simp only [mem_offDiag, mem_filter]
    constructor
    · rintro ⟨h₁, h₂, hn⟩
      exact ⟨⟨hD c hc h₁, hD c hc h₂, hn⟩, h₁, h₂⟩
    · rintro ⟨⟨_, _, hn⟩, h₁, h₂⟩
      exact ⟨h₁, h₂, hn⟩
  rw [sum_congr rfl (fun c hc => congrArg card (hrow c hc))]
  have h : (∑ c ∈ T, ∑ p ∈ P.offDiag, if p.1 ∈ D c ∧ p.2 ∈ D c then (1 : ℕ) else 0) =
      ∑ p ∈ P.offDiag, ∑ c ∈ T, if p.1 ∈ D c ∧ p.2 ∈ D c then (1 : ℕ) else 0 := Finset.sum_comm
  simpa only [Finset.sum_boole, Nat.cast_id] using h

/-- A square incidence system with bounded pair multiplicity has a bounded second moment. -/
theorem incidence_square_bound (P : Finset Point) (D : Point → Finset Point)
    (B : ℕ) (hD : ∀ c ∈ P, D c ⊆ P)
    (hpairs : ∀ p ∈ P.offDiag, (P.filter fun c => p.1 ∈ D c ∧ p.2 ∈ D c).card ≤ B) :
    (∑ c ∈ P, (D c).card) ^ 2 ≤ (B + 1) * P.card ^ 3 := by
  have htail : (∑ c ∈ P, (D c).offDiag.card) ≤ B * P.card ^ 2 := by
    rw [pairs_exchange P P D hD]
    calc
      _ ≤ ∑ _p ∈ P.offDiag, B := sum_le_sum hpairs
      _ = P.offDiag.card * B := by rw [sum_const, Nat.nsmul_eq_mul]
      _ ≤ _ := by
        rw [offDiag_card, mul_comm _ B]
        exact Nat.mul_le_mul_left _ (by rw [pow_two]; exact Nat.sub_le ..)
  have hsum : (∑ c ∈ P, (D c).card) ≤ P.card ^ 2 := by
    calc
      _ ≤ ∑ _c ∈ P, P.card := sum_le_sum fun c hc => card_le_card (hD c hc)
      _ = _ := by rw [sum_const, Nat.nsmul_eq_mul, pow_two]
  have hsplit (c : Point) : (D c).card ^ 2 = (D c).offDiag.card + (D c).card := by
    rw [offDiag_card, pow_two]
    exact (Nat.sub_add_cancel (Nat.le_mul_self _)).symm
  have hsecond : (∑ c ∈ P, (D c).card ^ 2) ≤ (B + 1) * P.card ^ 2 := by
    simp_rw [hsplit]
    rw [sum_add_distrib, Nat.add_mul, one_mul]
    exact Nat.add_le_add htail hsum
  calc
    _ ≤ P.card * ∑ c ∈ P, (D c).card ^ 2 := by
      simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) P 1 (fun c => (D c).card)
    _ ≤ P.card * ((B + 1) * P.card ^ 2) := Nat.mul_le_mul_left _ hsecond
    _ = _ := by rw [mul_left_comm P.card (B + 1), ← pow_succ' P.card 2]

/-- The pair count bounds the tail beyond any prescribed degree. -/
theorem heavy_bound (P : Finset Point) (T : Finset Circle) (D : Circle → Finset Point)
    (k B : ℕ) (hD : ∀ c ∈ T, D c ⊆ P) (hdeg : ∀ c ∈ T, k < (D c).card)
    (hpairs : ∀ p ∈ P.offDiag, (T.filter fun c => p.1 ∈ D c ∧ p.2 ∈ D c).card ≤ B) :
    k * (k + 1) * T.card ≤ B * P.offDiag.card := by
  calc
    _ = ∑ _c ∈ T, k * (k + 1) := by rw [sum_const, Nat.nsmul_eq_mul, mul_comm T.card]
    _ ≤ ∑ c ∈ T, (D c).offDiag.card := by
      apply sum_le_sum
      intro c hc
      have hd := hdeg c hc
      rw [offDiag_card, ← Nat.mul_sub_one, mul_comm k (k + 1)]
      exact Nat.mul_le_mul (by omega) (by omega)
    _ = ∑ p ∈ P.offDiag, (T.filter fun c => p.1 ∈ D c ∧ p.2 ∈ D c).card :=
      pairs_exchange P T D hD
    _ ≤ ∑ _p ∈ P.offDiag, B := sum_le_sum hpairs
    _ = _ := by rw [sum_const, Nat.nsmul_eq_mul, mul_comm]

/-- Bounding circles with exactly three incidences suffices after thinning and removing a pair-counted tail. -/
theorem rich_bound_from_exact_three (P : Finset Point) (C : Finset Circle) (D : Circle → Finset Point)
    (k B : ℕ) (hD : ∀ c ∈ C, D c ⊆ P) (hrich : ∀ c ∈ C, 3 ≤ (D c).card)
    (hpairs : ∀ p ∈ P.offDiag, (C.filter fun c => p.1 ∈ D c ∧ p.2 ∈ D c).card ≤ B) :
    ∃ Q ⊆ P, k * (k + 1) * C.card ≤
      k * (k + 1) * (2 ^ k * (C.filter fun c => (Q ∩ D c).card = 3).card) + B * P.offDiag.card := by
  let S := C.filter fun c => (D c).card ≤ k
  let T := C.filter fun c => k < (D c).card
  have hS : S ⊆ C := filter_subset _ _
  have hT : T ⊆ C := filter_subset _ _
  have hcard : S.card + T.card = C.card := by
    simpa only [S, T, not_le] using card_filter_add_card_filter_not (s := C) (p := fun c => (D c).card ≤ k)
  obtain ⟨Q, hQP, hSbound⟩ := thin_to_three P S D k (fun c hc => hD c (hS hc))
    (fun c hc => ⟨hrich c (hS hc), (mem_filter.mp hc).2⟩)
  have hTbound := heavy_bound P T D k B (fun c hc => hD c (hT hc))
    (fun c hc => (mem_filter.mp hc).2) (fun p hp =>
      (card_le_card (filter_subset_filter _ hT)).trans (hpairs p hp))
  have hScard : (S.filter fun c => (Q ∩ D c).card = 3).card ≤
      (C.filter fun c => (Q ∩ D c).card = 3).card := card_le_card (filter_subset_filter _ hS)
  refine ⟨Q, hQP, ?_⟩
  rw [← hcard, mul_add]
  exact add_le_add (Nat.mul_le_mul_left _ (hSbound.trans (Nat.mul_le_mul_left _ hScard))) hTbound

end RichIncidences

set_option maxHeartbeats 2000000 in
theorem main : H1 → H2 → type_of% @Erdos104.erdos_104 := by
  intro h₁ h₂
  classical
  let contacts (P : Finset ℝ²) (s : Sphere ℝ²) : Finset ℝ² := P.filter fun p => p ∈ s
  let pairCircles (a b : ℝ²) : Set (Sphere ℝ²) :=
    {s : Sphere ℝ² | s.radius = 1 ∧ a ∈ s ∧ b ∈ s}
  let richCircles (P : Finset ℝ²) : Set (Sphere ℝ²) :=
    {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ (contacts P s).card}
  let exactCircles (P : Finset ℝ²) : Set (Sphere ℝ²) :=
    {s : Sphere ℝ² | s.radius = 1 ∧ (contacts P s).card = 3}
  let distanceNeighbors (P : Finset ℝ²) (d : ℝ) (a : ℝ²) : Finset ℝ² :=
    P.filter fun b => dist a b = d
  let chordCircles (P : Finset ℝ²) (d : ℝ) : Set (Sphere ℝ²) :=
    {s : Sphere ℝ² | s.radius = 1 ∧ ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ dist a b = d ∧ a ∈ s ∧ b ∈ s}
  let nonDiameterExact (P : Finset ℝ²) : Set (Sphere ℝ²) := exactCircles P \ chordCircles P 2

  -- Finite counts and thinning reduce the uniform rich-circle problem to exactly three contacts.
  have contacts_card (P : Finset ℝ²) (s : Sphere ℝ²) :
      (contacts P s).card = {p ∈ (P : Set ℝ²) | p ∈ s}.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp [contacts]

  have pair_circles_finite {a b : ℝ²} (hab : a ≠ b) :
      (pairCircles a b).Finite ∧ (pairCircles a b).ncard ≤ 2 := by
    classical
    let A : Sphere ℝ² := ⟨a, 1⟩
    let B : Sphere ℝ² := ⟨b, 1⟩
    have hAB : A ≠ B := fun h => hab (congrArg Sphere.center h)
    have ha (s : Sphere ℝ²) (hs : s ∈ pairCircles a b) : s.center ∈ A := by
      change s.radius = 1 ∧ a ∈ s ∧ b ∈ s at hs
      exact mem_sphere'.mpr ((mem_sphere.mp hs.2.1).trans hs.1)
    have hb (s : Sphere ℝ²) (hs : s ∈ pairCircles a b) : s.center ∈ B := by
      change s.radius = 1 ∧ a ∈ s ∧ b ∈ s at hs
      exact mem_sphere'.mpr ((mem_sphere.mp hs.2.2).trans hs.1)
    have byCentre (s t : Sphere ℝ²) (hs : s ∈ pairCircles a b) (ht : t ∈ pairCircles a b)
        (h : s.center = t.center) : s = t := by
      have hsr : s.radius = 1 := hs.1
      have htr : t.radius = 1 := ht.1
      rw [← Sphere.mk_center_radius s, ← Sphere.mk_center_radius t, h, hsr, htr]
    by_cases hsub : (pairCircles a b).Subsingleton
    · have hone := (Set.ncard_le_one_iff hsub.finite).mpr (fun ha hb => hsub ha hb)
      exact ⟨hsub.finite, hone.trans (by decide)⟩
    obtain ⟨s, hs, t, ht, hst⟩ := Set.not_subsingleton_iff.mp hsub
    have hstc : s.center ≠ t.center := fun h => hst (byCentre s t hs ht h)
    have hsubset : pairCircles a b ⊆ ({s, t} : Set (Sphere ℝ²)) := by
      intro u hu
      rcases eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
        (V := ℝ²) (by simp) hAB hstc (ha s hs) (ha t ht) (ha u hu) (hb s hs) (hb t ht) (hb u hu) with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl (byCentre u s hu hs h))
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (byCentre u t hu ht h)))
    have hf : ({s, t} : Set (Sphere ℝ²)).Finite := Set.toFinite _
    refine ⟨hf.subset hsubset, ?_⟩
    exact (Set.ncard_le_ncard hsubset hf).trans (by rw [Set.ncard_pair hst])

  have rich_circles_finite (P : Finset ℝ²) : (richCircles P).Finite := by
    classical
    let block (p : ℝ² × ℝ²) : Finset (Sphere ℝ²) :=
      if h : p.1 ≠ p.2 then (pair_circles_finite h).1.toFinset else ∅
    refine (P.offDiag.biUnion block).finite_toSet.subset ?_
    intro s hs
    change s.radius = 1 ∧ 3 ≤ (contacts P s).card at hs
    have hd : 2 < (contacts P s).card := by omega
    obtain ⟨a, b, _, ha, hb, _, hab, _, _⟩ := Finset.two_lt_card_iff.mp hd
    have ha' : a ∈ P ∧ a ∈ s := by simpa [contacts] using ha
    have hb' : b ∈ P ∧ b ∈ s := by simpa [contacts] using hb
    refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha'.1, hb'.1, hab⟩, ?_⟩
    have hpair : s ∈ pairCircles a b := ⟨hs.1, ha'.2, hb'.2⟩
    simpa only [block, dif_pos hab, Set.Finite.mem_toFinset] using hpair

  have exact_subset_rich (P : Finset ℝ²) : exactCircles P ⊆ richCircles P := by
    intro s hs
    exact ⟨hs.1, hs.2.ge⟩

  have rich_count (P : Finset ℝ²) :
      (richCircles P).ncard = Erdos104.unitCircleCount P := by
    unfold Erdos104.unitCircleCount
    simp only [richCircles, contacts_card]

  have erdos104_thinning (P : Finset ℝ²) (k : ℕ) :
      ∃ Q ⊆ P, k * (k + 1) * Erdos104.unitCircleCount P ≤
        k * (k + 1) * (2 ^ k * (exactCircles Q).ncard) + 2 * P.offDiag.card := by
    classical
    let C := (rich_circles_finite P).toFinset
    have hD (s : Sphere ℝ²) : contacts P s ⊆ P := filter_subset _ _
    have hr (s : Sphere ℝ²) (hs : s ∈ C) : 3 ≤ (contacts P s).card := by
      have hRich : s ∈ richCircles P := by simpa only [C, Set.Finite.mem_toFinset] using hs
      exact hRich.2
    have hpairs (p : ℝ² × ℝ²) (hp : p ∈ P.offDiag) :
        (C.filter fun c => p.1 ∈ contacts P c ∧ p.2 ∈ contacts P c).card ≤ 2 := by
      have hne := (Finset.mem_offDiag.mp hp).2.2
      have hsub : (↑(C.filter fun c => p.1 ∈ contacts P c ∧ p.2 ∈ contacts P c) : Set (Sphere ℝ²))
          ⊆ pairCircles p.1 p.2 := by
        intro s hs
        have ⟨hC, hm⟩ := Finset.mem_filter.mp hs
        have hRich : s ∈ richCircles P := by simpa only [C, Set.Finite.mem_toFinset] using hC
        exact ⟨hRich.1, (Finset.mem_filter.mp hm.1).2, (Finset.mem_filter.mp hm.2).2⟩
      obtain ⟨hf, hbound⟩ := pair_circles_finite hne
      rw [← Set.ncard_coe_finset]
      exact (Set.ncard_le_ncard hsub hf).trans hbound
    obtain ⟨Q, hQ, hcount⟩ := RichIncidences.rich_bound_from_exact_three P C (contacts P) k 2
      (fun s _ => hD s) hr hpairs
    have hcoe : (C : Set (Sphere ℝ²)) = richCircles P := Set.Finite.coe_toFinset _
    have hcard : C.card = Erdos104.unitCircleCount P := by
      rw [← Set.ncard_coe_finset, hcoe, rich_count]
    have heq (s : Sphere ℝ²) : Q ∩ contacts P s = contacts Q s := by
      ext a
      simp only [Finset.mem_inter, contacts, Finset.mem_filter]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hQ h.1, h.2⟩⟩
    have hsub : (↑(C.filter fun s => (Q ∩ contacts P s).card = 3) : Set (Sphere ℝ²)) ⊆ exactCircles Q := by
      intro s hs
      have ⟨hC, hm⟩ := Finset.mem_filter.mp hs
      have hRich : s ∈ richCircles P := by simpa only [C, Set.Finite.mem_toFinset] using hC
      exact ⟨hRich.1, by simpa only [heq] using hm⟩
    have hupper : (C.filter fun s => (Q ∩ contacts P s).card = 3).card ≤ (exactCircles Q).ncard := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub ((rich_circles_finite Q).subset (exact_subset_rich Q))
    refine ⟨Q, hQ, ?_⟩
    rw [hcard] at hcount
    exact hcount.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hupper)) _)

  have erdos104_of_exact_three
      (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : Finset ℝ², P.card ≤ n →
        ((exactCircles P).ncard : ℝ) ≤ ε * (n : ℝ) ^ 2) : type_of% @Erdos104.erdos_104 := by
    classical
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    obtain ⟨l, hl⟩ := exists_nat_gt (4 / ε)
    let k := l + 3
    let A : ℝ := (k * (k + 1) : ℕ)
    let F : ℝ := (2 ^ k : ℕ)
    have hA : 0 < A := by
      dsimp [A, k]
      positivity
    have hF : 0 < F := by dsimp [F]; positivity
    have hk : 4 / ε < (k : ℝ) := by
      refine hl.trans_le ?_
      exact_mod_cast (show l ≤ k by dsimp [k]; omega)
    have hsmall : 2 ≤ (ε / 2) * A := by
      have hkε := (div_lt_iff₀ hε).mp hk
      have hstep : (k : ℝ) ≤ A := by
        change (k : ℝ) ≤ ((k * (k + 1) : ℕ) : ℝ)
        exact_mod_cast (show k ≤ k * (k + 1) from Nat.le_mul_of_pos_right k (by omega))
      calc
        2 ≤ (ε / 2) * (k : ℝ) := by nlinarith only [hkε]
        _ ≤ (ε / 2) * A := mul_le_mul_of_nonneg_left hstep (by positivity)
    let δ := ε / (2 * F)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hFδ : F * δ = ε / 2 := by
      dsimp [δ]
      field_simp
    obtain ⟨N, hN⟩ := h δ hδ
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (sq_nonneg (n : ℝ))]
    have count_bound (P : Finset ℝ²) (hP : P.card ≤ n) :
        (Erdos104.unitCircleCount P : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
      obtain ⟨Q, hQ, hs⟩ := erdos104_thinning P k
      have hE := hN n hn Q ((Finset.card_le_card hQ).trans hP)
      have hS : A * (Erdos104.unitCircleCount P : ℝ) ≤
          A * (F * ((exactCircles Q).ncard : ℝ)) + 2 * (P.offDiag.card : ℝ) := by
        dsimp only [A, F]
        exact_mod_cast hs
      have hpair : (P.offDiag.card : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [Finset.offDiag_card]
        exact_mod_cast (show P.card * P.card - P.card ≤ n ^ 2 from
          (Nat.sub_le _ _).trans (by rw [pow_two]; exact Nat.mul_le_mul hP hP))
      apply le_of_mul_le_mul_left ?_ hA
      calc
        _ ≤ A * (F * ((exactCircles Q).ncard : ℝ)) + 2 * (P.offDiag.card : ℝ) := hS
        _ ≤ A * (F * (δ * (n : ℝ) ^ 2)) + 2 * (n : ℝ) ^ 2 := by gcongr
        _ = A * ((ε / 2) * (n : ℝ) ^ 2) + 2 * (n : ℝ) ^ 2 := by rw [← mul_assoc F δ, hFδ]
        _ ≤ A * ((ε / 2) * (n : ℝ) ^ 2) + ((ε / 2) * A) * (n : ℝ) ^ 2 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hsmall (sq_nonneg (n : ℝ)))
        _ = _ := by ring
    have hsup : Erdos104.maxUnitCircleCount n ≤ ⌊ε * (n : ℝ) ^ 2⌋₊ := by
      unfold Erdos104.maxUnitCircleCount
      refine csSup_le' ?_
      rintro _ ⟨P, hPn, rfl⟩
      exact Nat.le_floor (count_bound P hPn.le)
    exact (Nat.cast_le.mpr hsup).trans (Nat.floor_le (by positivity))

  have chord_circles_count (P : Finset ℝ²) (d : ℝ) :
      (chordCircles P d).Finite ∧
        (chordCircles P d).ncard ≤ 2 * ∑ a ∈ P, (distanceNeighbors P d a).card := by
    classical
    let pairs := P.biUnion fun a => (distanceNeighbors P d a).image (fun b => (a, b))
    let block (p : ℝ² × ℝ²) : Finset (Sphere ℝ²) :=
      if h : p.1 ≠ p.2 then (pair_circles_finite h).1.toFinset else ∅
    have hsub : chordCircles P d ⊆ ↑(pairs.biUnion block) := by
      rintro s ⟨hs, a, ha, b, hb, hab, hd, has, hbs⟩
      have hp : (a, b) ∈ pairs :=
        Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hd⟩, rfl⟩⟩
      refine Finset.mem_biUnion.mpr ⟨(a, b), hp, ?_⟩
      have hpair : s ∈ pairCircles a b := ⟨hs, has, hbs⟩
      simpa only [block, dif_pos hab, Set.Finite.mem_toFinset] using hpair
    have hf := (pairs.biUnion block).finite_toSet
    refine ⟨hf.subset hsub, ?_⟩
    have hblock (p : ℝ² × ℝ²) : (block p).card ≤ 2 := by
      by_cases hp : p.1 ≠ p.2
      · simpa only [block, dif_pos hp, Set.ncard_eq_toFinset_card _ (pair_circles_finite hp).1] using
          (pair_circles_finite hp).2
      · simp only [block, dif_neg hp, Finset.card_empty, Nat.zero_le]
    have hpairs : pairs.card ≤ ∑ a ∈ P, (distanceNeighbors P d a).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
    calc
      _ ≤ (↑(pairs.biUnion block) : Set (Sphere ℝ²)).ncard := Set.ncard_le_ncard hsub hf
      _ = (pairs.biUnion block).card := Set.ncard_coe_finset _
      _ ≤ pairs.card * 2 := Finset.card_biUnion_le_card_mul _ _ _ fun p _ => hblock p
      _ ≤ _ := by rw [mul_comm _ 2]; exact Nat.mul_le_mul_left _ hpairs

  have erdos104_of_nondiameter_exact_three
      (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : Finset ℝ², P.card ≤ n →
        ((nonDiameterExact P).ncard : ℝ) ≤ ε * (n : ℝ) ^ 2) :
      type_of% @Erdos104.erdos_104 := by
    apply erdos104_of_exact_three
    intro ε hε
    obtain ⟨N₁, bound₁⟩ := h (ε / 2) (by positivity)
    obtain ⟨N₂, bound₂⟩ := h₂ 2 (ε / 2) (by positivity)
    refine ⟨max N₁ N₂, ?_⟩
    intro n hn P hP
    have hf : (nonDiameterExact P ∪ chordCircles P 2).Finite :=
      ((rich_circles_finite P).subset (fun _ hs => ⟨hs.1.1, hs.1.2.ge⟩)).union
        (chord_circles_count P 2).1
    have hsub : exactCircles P ⊆ nonDiameterExact P ∪ chordCircles P 2 := by
      intro s hs
      by_cases hd : s ∈ chordCircles P 2
      · exact Or.inr hd
      · exact Or.inl ⟨hs, hd⟩
    have hc := (Set.ncard_le_ncard hsub hf).trans (Set.ncard_union_le _ _)
    have hc' : ((exactCircles P).ncard : ℝ) ≤
        ((nonDiameterExact P).ncard : ℝ) + ((chordCircles P 2).ncard : ℝ) := by
      exact_mod_cast hc
    calc
      _ ≤ _ := hc'
      _ ≤ (ε / 2) * (n : ℝ) ^ 2 + (ε / 2) * (n : ℝ) ^ 2 :=
        add_le_add (bound₁ n ((le_max_left _ _).trans hn) P hP) (bound₂ n ((le_max_right _ _).trans hn) P hP)
      _ = _ := by ring

  apply erdos104_of_nondiameter_exact_three
  intro ε hε
  obtain ⟨N, hN⟩ := h₁ ε hε
  refine ⟨N, ?_⟩
  intro n hn P hP
  simpa only [nonDiameterExact, exactCircles, chordCircles, contacts_card] using hN n hn P hP

end OMA.R_Erdos104_erdos_104_R1
