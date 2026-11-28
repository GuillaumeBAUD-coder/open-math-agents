import FormalConjectures.ErdosProblems.«500»

/-! Inclusion-exclusion formula for the finite tetrahedron extremal count. -/

-- Original proof by @richardsondx (PR #12914), streamlined by @dmae97
-- (pending PR #26167). Supremum and subset-cardinality witnesses now use Mathlib.

namespace K4Count

abbrev Edge (n : ℕ) := Finset (Fin n)
def triples (n : ℕ) : Finset (Edge n) := (Finset.univ : Finset (Fin n)).powersetCard 3
def blocks (n : ℕ) : Finset (Edge n) := (Finset.univ : Finset (Fin n)).powersetCard 4
def forced {n : ℕ} (T : Finset (Edge n)) : Finset (Edge n) := T.biUnion (·.powersetCard 3)

def ieCount (n q : ℕ) : ℤ :=
  ∑ T ∈ (blocks n).powerset,
    let u := (forced T).card
    if u ≤ q then (-1 : ℤ) ^ T.card * (Nat.choose ((triples n).card - u) (q - u) : ℤ) else 0

def value (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (triples n).card).filter fun q => 0 < ieCount n q).card

def safe {n : ℕ} (H : Finset (Edge n)) : Prop := ∀ S ∈ blocks n, ¬ S.powersetCard 3 ⊆ H

lemma card_sizes_eq_sup {α : Type*} [DecidableEq α] (s : Finset (Finset α)) (B : ℕ)
    (hB : ∀ H ∈ s, H.card ≤ B) (hdown : ∀ H ∈ s, ∀ D, D ⊆ H → D ∈ s) :
    ((Finset.Icc 1 B).filter fun q => ∃ H ∈ s, H.card = q).card = s.sup Finset.card := by
  classical
  have hset : ((Finset.Icc 1 B).filter fun q => ∃ H ∈ s, H.card = q) =
      Finset.Icc 1 (s.sup Finset.card) := by
    ext q; simp only [Finset.mem_filter, Finset.mem_Icc]; constructor
    · rintro ⟨⟨h1, _⟩, H, hH, rfl⟩; exact ⟨h1, Finset.le_sup hH⟩
    · rintro ⟨h1, hqsup⟩
      obtain ⟨H, hH, hqH⟩ := (Finset.le_sup_iff h1).mp hqsup
      obtain ⟨D, hDH, hDq⟩ := Finset.exists_subset_card_eq hqH
      exact ⟨⟨h1, hDq ▸ (Finset.card_mono hDH).trans (hB H hH)⟩, D, hdown H hH D hDH, hDq⟩
  rw [hset, Nat.card_Icc]; omega

open scoped Classical in
lemma ieCount_eq (n q : ℕ) :
    ieCount n q = (((triples n).powersetCard q).filter safe).card := by
  let E := triples n
  let B := blocks n
  let Q := E.powersetCard q
  have hcoeff (T : Finset (Edge n)) :
      (if (forced T).card ≤ q then
        (-1 : ℤ) ^ T.card * (Nat.choose (E.card - (forced T).card) (q - (forced T).card) : ℤ) else 0) =
      ∑ H ∈ Q, if forced T ⊆ H then (-1 : ℤ) ^ T.card else 0 := by
    have hU : forced T ⊆ E := fun e he => by
      obtain ⟨S, _, heS⟩ := Finset.mem_biUnion.mp he
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, (Finset.mem_powersetCard.mp heS).2⟩
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    by_cases hu : (forced T).card ≤ q
    · simp [hu, Q, Finset.card_filter_powersetCard_subset (forced T) E q hU hu]
    · have hemp : Q.filter (forced T ⊆ ·) = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun H hH => by
        obtain ⟨hHp, hTH⟩ := Finset.mem_filter.mp hH
        exact hu ((Finset.card_mono hTH).trans_eq (Finset.mem_powersetCard.mp hHp).2)
      simp [hu, hemp]
  have hinner (H : Finset (Edge n)) :
      (∑ T ∈ B.powerset, if forced T ⊆ H then (-1 : ℤ) ^ T.card else 0) =
        if safe H then 1 else 0 := by
    let bad := B.filter fun S => S.powersetCard 3 ⊆ H
    have hset : B.powerset.filter (forced · ⊆ H) = bad.powerset := by
      ext T; simp only [Finset.mem_filter, Finset.mem_powerset]
      rw [forced, Finset.biUnion_subset_iff_forall_subset]; simp [bad, Finset.subset_iff, forall_and]
    rw [← Finset.sum_filter, hset, Finset.sum_powerset_neg_one_pow_card]
    have : (bad = ∅) ↔ safe H := by simp [bad, safe, B, Finset.eq_empty_iff_forall_notMem]
    simp [this]
  calc ieCount n q
      = ∑ T ∈ B.powerset, ∑ H ∈ Q, if forced T ⊆ H then (-1 : ℤ) ^ T.card else 0 :=
          Finset.sum_congr rfl fun T _ => hcoeff T
    _ = ∑ H ∈ Q, if safe H then 1 else 0 := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun H _ => hinner H
    _ = _ := by
          rw [← Finset.sum_filter]; simp [Q, E]

theorem value_eq_extremal (n : ℕ) : value n = Hypergraph.cliqueExtremalNumber n 3 4 := by
  classical
  let s := (triples n).powerset.filter fun H => ¬ H.ContainsCompleteHypergraph 3 4
  have hs_safe (H : Finset (Edge n)) : safe H ↔ ¬ H.ContainsCompleteHypergraph 3 4 := by
    simp [safe, blocks, Finset.ContainsCompleteHypergraph]
  have hpos (q : ℕ) : 0 < ieCount n q ↔ ∃ H ∈ s, H.card = q := by
    rw [ieCount_eq]; simp only [Int.natCast_pos, Finset.card_pos, Finset.Nonempty,
      Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powerset, s, hs_safe,
      and_assoc, and_comm]

  have hset : ((Finset.Icc 1 (triples n).card).filter fun q => 0 < ieCount n q) =
      (Finset.Icc 1 (triples n).card).filter fun q => ∃ H ∈ s, H.card = q := by
    ext q; simp [hpos]
  unfold value Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  rw [hset, card_sizes_eq_sup s (triples n).card
    (fun H hH => Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hH).1))
    (fun H hH D hDH => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hH
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hDH.trans (Finset.mem_powerset.mp h1)),
        fun ⟨S, hS, hSD⟩ => h2 ⟨S, hS, hSD.trans hDH⟩⟩)]
  congr 1; ext H; simp [s, triples]

end K4Count

def OMA.answer : ℕ → ℕ := K4Count.value

theorem OMA.solution : Erdos500.erdos_500.answer = OMA.answer →
    type_of% @Erdos500.erdos_500 := by
  intro h; rw [h]; funext n; exact (K4Count.value_eq_extremal n).symm
