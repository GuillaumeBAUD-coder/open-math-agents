import FormalConjectures.ErdosProblems.«500»

/-! An inclusion-exclusion formula for the finite tetrahedron extremal count. -/

namespace K4Count

lemma sum_ite_indicator {α : Type*} [DecidableEq α] (Q : Finset α)
    (p : α → Prop) [DecidablePred p] (z : ℤ) :
    (∑ x ∈ Q, if p x then z else 0) = z * (Q.filter p).card := by
  rw [← Finset.sum_filter]
  simp [mul_comm]

lemma card_sizes_eq_sup {α : Type*} [DecidableEq α]
    (s : Finset (Finset α)) (B : ℕ)
    (hB : ∀ H ∈ s, H.card ≤ B)
    (hdown : ∀ H ∈ s, ∀ D, D ⊆ H → D ∈ s) :
    ((Finset.Icc 1 B).filter (fun q => ∃ H ∈ s, H.card = q)).card =
      s.sup Finset.card := by
  classical
  have hset : (Finset.Icc 1 B).filter (fun q => ∃ H ∈ s, H.card = q) =
      Finset.Icc 1 (s.sup Finset.card) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, hqB⟩, H, hH, rfl⟩
      exact ⟨h1, Finset.le_sup hH⟩
    · rintro ⟨h1, hqsup⟩
      have hge : ∃ H ∈ s, q ≤ H.card := by
        by_contra hn
        have hsle : s.sup Finset.card ≤ q - 1 := Finset.sup_le fun H hH => by
          have hlt : H.card < q := Nat.lt_of_not_ge (fun hh => hn ⟨H, hH, hh⟩)
          omega
        omega
      rcases hge with ⟨H, hH, hqH⟩
      have hnon : (H.powersetCard q).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_powersetCard]
        exact Nat.choose_pos hqH
      rcases hnon with ⟨D, hD⟩
      have hDH : D ⊆ H := (Finset.mem_powersetCard.mp hD).1
      have hDq : D.card = q := (Finset.mem_powersetCard.mp hD).2
      have hqB : q ≤ B := by
        rw [← hDq]
        exact (Finset.card_mono hDH).trans (hB H hH)
      exact ⟨⟨h1, hqB⟩, D, hdown H hH D hDH, hDq⟩
  rw [hset, Nat.card_Icc]
  omega

abbrev Edge (n : ℕ) := Finset (Fin n)

def triples (n : ℕ) : Finset (Edge n) :=
  (Finset.univ : Finset (Fin n)).powersetCard 3

def blocks (n : ℕ) : Finset (Edge n) :=
  (Finset.univ : Finset (Fin n)).powersetCard 4

def forced {n : ℕ} (T : Finset (Edge n)) : Finset (Edge n) :=
  T.biUnion (fun S => S.powersetCard 3)

def ieCount (n q : ℕ) : ℤ :=
  ∑ T ∈ (blocks n).powerset,
    let u := (forced T).card
    if u ≤ q then
      (-1 : ℤ) ^ T.card *
        (Nat.choose ((triples n).card - u) (q - u) : ℤ)
    else 0

def value (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (triples n).card).filter (fun q => 0 < ieCount n q)).card

def safe {n : ℕ} (H : Finset (Edge n)) : Prop :=
  ∀ S ∈ blocks n, ¬ S.powersetCard 3 ⊆ H

noncomputable def safeCount (n q : ℕ) : ℕ := by
  classical
  exact ((triples n).powersetCard q).filter safe |>.card

theorem forced_subset_iff {n : ℕ} (T H : Finset (Edge n)) :
    forced T ⊆ H ↔ ∀ S ∈ T, S.powersetCard 3 ⊆ H := by
  constructor
  · intro h S hS e he
    exact h (Finset.mem_biUnion.mpr ⟨S, hS, he⟩)
  · intro h e he
    obtain ⟨S, hS, heS⟩ := Finset.mem_biUnion.mp he
    exact (h S hS) heS

lemma forced_subset_triples {n : ℕ} (T : Finset (Edge n)) : forced T ⊆ triples n := by
  intro e he
  obtain ⟨S, hS, heS⟩ := Finset.mem_biUnion.mp he
  have heS' := Finset.mem_powersetCard.mp heS
  change e ∈ (Finset.univ : Finset (Fin n)).powersetCard 3
  rw [Finset.mem_powersetCard]
  exact ⟨Finset.subset_univ e, heS'.2⟩

lemma card_supersets {α : Type*} [DecidableEq α] (E U : Finset α) (q : ℕ)
    (hUE : U ⊆ E) :
    ((E.powersetCard q).filter (U ⊆ ·)).card =
      if U.card ≤ q then (E.card - U.card).choose (q - U.card) else 0 := by
  classical
  by_cases hu : U.card ≤ q
  · simp [hu, Finset.card_filter_powersetCard_subset U E q hUE hu]
  · simp only [if_neg hu]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro H hH
    rcases Finset.mem_filter.mp hH with ⟨hHp, hUH⟩
    have h' : U.card ≤ H.card := Finset.card_mono hUH
    have hq : H.card = q := (Finset.mem_powersetCard.mp hHp).2
    omega


theorem ieCount_eq_safeCount (n q : ℕ) :
    ieCount n q = (safeCount n q : ℤ) := by
  classical
  let E := triples n
  let B := blocks n
  let Q := E.powersetCard q
  let bad := fun H : Finset (Edge n) => B.filter (fun S => S.powersetCard 3 ⊆ H)
  have hcoeff (T : Finset (Edge n)) (hT : T ∈ B.powerset) :
      (if (forced T).card ≤ q then
        (-1 : ℤ) ^ T.card * (Nat.choose (E.card - (forced T).card)
          (q - (forced T).card) : ℤ) else 0) =
        ∑ H ∈ Q, if forced T ⊆ H then (-1 : ℤ) ^ T.card else 0 := by
    have hU : forced T ⊆ E := forced_subset_triples T
    have hc := card_supersets E (forced T) q hU
    rw [sum_ite_indicator]
    have hc' : ((Q.filter (forced T ⊆ ·)).card : ℤ) =
        if (forced T).card ≤ q then
          (Nat.choose (E.card - (forced T).card) (q - (forced T).card) : ℤ) else 0 := by
      rw [hc]
      split_ifs <;> simp
    rw [hc']
    split_ifs <;> simp
  have hinner (H : Finset (Edge n)) :
      (∑ T ∈ B.powerset, if forced T ⊆ H then (-1 : ℤ) ^ T.card else 0) =
        if bad H = ∅ then 1 else 0 := by
    rw [← Finset.sum_filter]
    have hset : B.powerset.filter (fun T => forced T ⊆ H) = (bad H).powerset := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset]
      rw [forced_subset_iff]
      simp [bad, Finset.subset_iff, Finset.mem_filter, forall_and]
    rw [hset]
    exact Finset.sum_powerset_neg_one_pow_card
  unfold ieCount
  change (∑ T ∈ B.powerset,
      if (forced T).card ≤ q then
        (-1 : ℤ) ^ T.card * (Nat.choose (E.card - (forced T).card)
          (q - (forced T).card) : ℤ) else 0) = _
  calc
    _ = ∑ T ∈ B.powerset, ∑ H ∈ Q,
          if forced T ⊆ H then (-1 : ℤ) ^ T.card else 0 := by
        apply Finset.sum_congr rfl
        intro T hT
        exact hcoeff T hT
    _ = ∑ H ∈ Q, ∑ T ∈ B.powerset,
          if forced T ⊆ H then (-1 : ℤ) ^ T.card else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ H ∈ Q, if bad H = ∅ then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro H hH
        exact hinner H
    _ = ((Q.filter fun H => bad H = ∅).card : ℤ) := by
        rw [sum_ite_indicator]
        simp
    _ = (safeCount n q : ℤ) := by
        have hsafe : Q.filter (fun H => bad H = ∅) = Q.filter safe := by
          ext H
          simp [safe, bad, B]
        change ((Q.filter fun H => bad H = ∅).card : ℤ) =
          (((triples n).powersetCard q).filter safe).card
        rw [hsafe]

lemma ieCount_pos_iff (n q : ℕ) :
    0 < ieCount n q ↔ ∃ H ∈ (triples n).powersetCard q, safe H := by
  classical
  rw [ieCount_eq_safeCount]
  simp only [Int.natCast_pos]
  change 0 < (((triples n).powersetCard q).filter safe).card ↔ _
  rw [Finset.card_pos]
  constructor
  · rintro ⟨H, hH⟩
    rcases Finset.mem_filter.mp hH with ⟨hQ, hSafe⟩
    exact ⟨H, hQ, hSafe⟩
  · rintro ⟨H, hQ, hSafe⟩
    exact ⟨H, Finset.mem_filter.mpr ⟨hQ, hSafe⟩⟩

lemma safe_iff_forbidden {n : ℕ} (H : Finset (Edge n)) :
    safe H ↔ ¬ H.ContainsCompleteHypergraph 3 4 := by
  simp [safe, blocks, Finset.ContainsCompleteHypergraph]

noncomputable def admissible (n : ℕ) : Finset (Finset (Edge n)) := by
  classical
  exact (triples n).powerset.filter safe

lemma admissible_down (n : ℕ) (H : Finset (Edge n))
    (hH : H ∈ admissible n) (D : Finset (Edge n)) (hDH : D ⊆ H) :
    D ∈ admissible n := by
  classical
  rcases Finset.mem_filter.mp hH with ⟨hHp, hSafe⟩
  apply Finset.mem_filter.mpr
  have hDE : D ⊆ triples n := hDH.trans (Finset.mem_powerset.mp hHp)
  refine ⟨Finset.mem_powerset.mpr hDE, ?_⟩
  intro S hS hSD
  exact hSafe S hS (hSD.trans hDH)

lemma ieCount_pos_iff_admissible (n q : ℕ) :
    0 < ieCount n q ↔ ∃ H ∈ admissible n, H.card = q := by
  classical
  rw [ieCount_pos_iff]
  constructor
  · rintro ⟨H, hHQ, hSafe⟩
    have hHp : H ∈ (triples n).powerset :=
      Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hHQ).1
    exact ⟨H, Finset.mem_filter.mpr ⟨hHp, hSafe⟩,
      (Finset.mem_powersetCard.mp hHQ).2⟩
  · rintro ⟨H, hH, hcard⟩
    rcases Finset.mem_filter.mp hH with ⟨hHp, hSafe⟩
    refine ⟨H, ?_, hSafe⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hHp, hcard⟩

theorem value_eq_extremal (n : ℕ) :
    value n = Hypergraph.cliqueExtremalNumber n 3 4 := by
  classical
  let s := admissible n
  have hB : ∀ H ∈ s, H.card ≤ (triples n).card := by
    intro H hH
    exact Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hH).1)
  have hset : (Finset.Icc 1 (triples n).card).filter (fun q => 0 < ieCount n q) =
      (Finset.Icc 1 (triples n).card).filter (fun q => ∃ H ∈ s, H.card = q) := by
    ext q
    simp only [Finset.mem_filter]
    rw [ieCount_pos_iff_admissible]
  have hvalue : value n = s.sup Finset.card := by
    unfold value
    rw [hset]
    exact card_sizes_eq_sup s (triples n).card hB (by
      intro H hH D hDH
      exact admissible_down n H hH D hDH)
  rw [hvalue]
  have hs : s = ((triples n).powerset.filter
      (fun H => ¬ H.ContainsCompleteHypergraph 3 4)) := by
    ext H
    simp [s, admissible, safe_iff_forbidden]
  rw [hs]
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  congr 1
  ext H
  simp [triples]


end K4Count


def OMA.answer : ℕ → ℕ := K4Count.value

theorem OMA.solution : Erdos500.erdos_500.answer = OMA.answer →
    type_of% @Erdos500.erdos_500 := by
  intro h
  rw [h]
  funext n
  exact (K4Count.value_eq_extremal n).symm
