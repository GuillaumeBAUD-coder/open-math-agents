import OMAStatements.S_oeis_a401159
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith

/-!
Elementary finite counting lemmas used in the proof of OEIS A401159.
The underlying objects are actual subsets of the row indices, with cardinality
at most two; no counting formula is used as a definition.
-/

namespace A401159

open Finset
open scoped BigOperators

/-- The support of a binary column with at most two entries equal to one. -/
def Column (n : ℕ) := {s : Finset (Fin n) // s.card ≤ 2}

instance (n : ℕ) : Fintype (Column n) :=
  inferInstanceAs (Fintype {s : Finset (Fin n) // s.card ≤ 2})

instance (n : ℕ) : DecidableEq (Column n) :=
  inferInstanceAs (DecidableEq {s : Finset (Fin n) // s.card ≤ 2})

/-- The standard count of subsets of a specified cardinality. -/
theorem card_finsets_card (n k : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = k} = Nat.choose n k := by
  classical
  calc
    _ = ((Finset.univ : Finset (Fin n)).powersetCard k).card :=
      Fintype.card_of_subtype _ (by intro s; simp)
    _ = Nat.choose n k := by simp

theorem card_two_subsets (n : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = 2} = Nat.choose n 2 :=
  card_finsets_card n 2

/-- A column can have zero, one, or two entries equal to one. -/
theorem card_column (n : ℕ) :
    Fintype.card (Column n) = 1 + n + Nat.choose n 2 := by
  classical
  let U : Finset (Fin n) := Finset.univ
  have h01 : Disjoint (U.powersetCard 0) (U.powersetCard 1) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    have hs' := (Finset.mem_powersetCard.mp hs).2
    have ht' := (Finset.mem_powersetCard.mp ht).2
    omega
  have h012 : Disjoint (U.powersetCard 0 ∪ U.powersetCard 1) (U.powersetCard 2) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    have ht' := (Finset.mem_powersetCard.mp ht).2
    rcases Finset.mem_union.mp hs with hs | hs
    · have hs' := (Finset.mem_powersetCard.mp hs).2
      omega
    · have hs' := (Finset.mem_powersetCard.mp hs).2
      omega
  change Fintype.card {s : Finset (Fin n) // s.card ≤ 2} = _
  calc
    _ = ((U.powersetCard 0 ∪ U.powersetCard 1) ∪ U.powersetCard 2).card :=
      Fintype.card_of_subtype _ (by
        intro s
        simp only [Finset.mem_union, Finset.mem_powersetCard, U,
          Finset.subset_univ, true_and]
        omega)
    _ = (U.powersetCard 0).card + (U.powersetCard 1).card +
        (U.powersetCard 2).card := by
      rw [Finset.card_union_of_disjoint h012, Finset.card_union_of_disjoint h01]
    _ = 1 + n + Nat.choose n 2 := by simp [U]

/-- Once a specified row is occupied, the column is `{i,j}` for a unique row
`j`; the case `j = i` represents the singleton column. -/
theorem card_column_containing (n : ℕ) (i : Fin n) :
    Fintype.card {s : Column n // i ∈ s.val} = n := by
  classical
  let f : Fin n → {s : Column n // i ∈ s.val} := fun j =>
    ⟨⟨{i, j}, Finset.card_le_two⟩, by simp⟩
  have hf_inj : Function.Injective f := by
    intro j k h
    have hset : ({i, j} : Finset (Fin n)) = {i, k} :=
      congrArg (fun s : {s : Column n // i ∈ s.val} => s.val.val) h
    have hj : j = i ∨ j = k := by
      have : j ∈ ({i, k} : Finset (Fin n)) := hset ▸ (by simp)
      simpa using this
    have hk : k = i ∨ k = j := by
      have : k ∈ ({i, j} : Finset (Fin n)) := hset.symm ▸ (by simp)
      simpa using this
    rcases hj with hj | hj
    · rcases hk with hk | hk
      · exact hj.trans hk.symm
      · exact hk.symm
    · exact hj
  have hf_surj : Function.Surjective f := by
    intro s
    have hpos : 0 < s.val.val.card := Finset.card_pos.mpr ⟨i, s.property⟩
    have hle : s.val.val.card ≤ 2 := s.val.property
    have hc : s.val.val.card = 1 ∨ s.val.val.card = 2 := by omega
    rcases hc with hc | hc
    · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
      have hij : i = j := by simpa [hj] using s.property
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simp [f, hj, hij]
    · obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hc
      have hi : i = a ∨ i = b := by simpa [hs] using s.property
      rcases hi with hi | hi
      · refine ⟨b, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        simp [f, hs, hi]
      · refine ⟨a, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        simp [f, hs, hi, Finset.pair_comm]
  have hcard := Fintype.card_of_bijective ⟨hf_inj, hf_surj⟩
  simpa using hcard.symm

/-- The elementary pointwise identity behind the bounded-overlap count. -/
theorem zero_indicator_add_of_le_two (k : ℕ) (hk : k ≤ 2) :
    (if k = 0 then 1 else 0) + k = 1 + (if k = 2 then 1 else 0) := by
  by_cases h0 : k = 0
  · simp [h0]
  by_cases h2 : k = 2
  · simp [h2]
  have h1 : k = 1 := by omega
  simp [h1]

/-- Express a finite subtype cardinality as the sum of its indicator. -/
theorem card_subtype_eq_sum_indicator {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] :
    Fintype.card {a : α // P a} = ∑ a : α, if P a then 1 else 0 := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter]

/-- Summing the preceding identity avoids subtraction in the natural numbers. -/
theorem card_zero_add_sum {α : Type*} (s : Finset α) (f : α → ℕ)
    (hf : ∀ a ∈ s, f a ≤ 2) :
    (s.filter (fun a => f a = 0)).card + ∑ a ∈ s, f a =
      s.card + (s.filter (fun a => f a = 2)).card := by
  classical
  rw [Finset.card_filter, Finset.card_filter, Finset.card_eq_sum_ones,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a ha => zero_indicator_add_of_le_two (f a) (hf a ha))

end A401159

/-!
The finite objects counted below are genuine binary matrices.  Passing to
their column supports gives the elementary subset model used for counting.
-/

namespace A401159

abbrev Triple (n : ℕ) := Column n × Column n × Column n

def common {n : ℕ} (t : Triple n) : Finset (Fin n) :=
  t.1.val ∩ t.2.1.val ∩ t.2.2.val

abbrev GoodTriple (n : ℕ) := {t : Triple n // common t = ∅}

abbrev Matrix (n m : ℕ) := Fin n → Fin m → Bool

def colSupport {n m : ℕ} (A : Matrix n m) (j : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => A i j = true)

def rowSupport {n m : ℕ} (A : Matrix n m) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => A i j = true)

def Valid {n m : ℕ} (A : Matrix n m) : Prop :=
  (∀ j, (colSupport A j).card ≤ 2) ∧
  (∀ i, (rowSupport A i).card ≤ 2)

abbrev ValidMatrix (n m : ℕ) := {A : Matrix n m // Valid A}

noncomputable instance validMatrixFintype (n m : ℕ) : Fintype (ValidMatrix n m) := by
  classical
  infer_instance

noncomputable def matrixCount (n m : ℕ) : ℕ :=
  Fintype.card (ValidMatrix n m)

theorem matrix_ext_of_colSupport {n m : ℕ} (A B : Matrix n m)
    (h : ∀ j, colSupport A j = colSupport B j) : A = B := by
  funext i j
  apply Bool.eq_iff_iff.mpr
  have hi : i ∈ colSupport A j ↔ i ∈ colSupport B j := by rw [h j]
  simpa [colSupport] using hi

def fromColumns {n m : ℕ} (C : Fin m → Column n) : Matrix n m :=
  fun i j => decide (i ∈ (C j).val)

@[simp] theorem colSupport_fromColumns {n m : ℕ} (C : Fin m → Column n)
    (j : Fin m) : colSupport (fromColumns C) j = (C j).val := by
  ext i
  simp [colSupport, fromColumns]

theorem rowSupport_card_le {n m : ℕ} (A : Matrix n m) (i : Fin n) :
    (rowSupport A i).card ≤ m := by
  calc
    _ ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = m := by simp

theorem rowSupport_three_le_two_iff {n : ℕ} (A : Matrix n 3) (i : Fin n) :
    (rowSupport A i).card ≤ 2 ↔
      ¬ (A i 0 = true ∧ A i 1 = true ∧ A i 2 = true) := by
  have hle := rowSupport_card_le A i
  have hall : rowSupport A i = Finset.univ ↔
      A i 0 = true ∧ A i 1 = true ∧ A i 2 = true := by
    constructor
    · intro h
      have h0 : (0 : Fin 3) ∈ rowSupport A i := by rw [h]; simp
      have h1 : (1 : Fin 3) ∈ rowSupport A i := by rw [h]; simp
      have h2 : (2 : Fin 3) ∈ rowSupport A i := by rw [h]; simp
      simpa [rowSupport] using And.intro h0 (And.intro h1 h2)
    · rintro ⟨h0, h1, h2⟩
      ext j
      fin_cases j <;> simp [rowSupport, h0, h1, h2]
  constructor
  · intro h h111
    have hc : (rowSupport A i).card = 3 := by rw [hall.mpr h111]; simp
    omega
  · intro h
    by_contra hn
    have hc : (rowSupport A i).card = 3 := by omega
    have he : rowSupport A i = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using hc)
    exact h (hall.mp he)

def columnOf {n m : ℕ} (A : ValidMatrix n m) (j : Fin m) : Column n :=
  ⟨colSupport A.val j, A.property.1 j⟩

def twoColumns {n : ℕ} (p : Column n × Column n) : Fin 2 → Column n :=
  fun j => if j = 0 then p.1 else p.2

def toTwo {n : ℕ} (A : ValidMatrix n 2) : Column n × Column n :=
  (columnOf A 0, columnOf A 1)

def ofTwo {n : ℕ} (p : Column n × Column n) : ValidMatrix n 2 :=
  ⟨fromColumns (twoColumns p), by
    constructor
    · intro j
      rw [colSupport_fromColumns]
      exact (twoColumns p j).property
    · intro i
      exact rowSupport_card_le _ i⟩

theorem toTwo_injective (n : ℕ) : Function.Injective (@toTwo n) := by
  intro A B h
  apply Subtype.ext
  apply matrix_ext_of_colSupport
  intro j
  fin_cases j
  · exact congrArg (fun p : Column n × Column n => p.1.val) h
  · exact congrArg (fun p : Column n × Column n => p.2.val) h

theorem toTwo_surjective (n : ℕ) : Function.Surjective (@toTwo n) := by
  intro p
  refine ⟨ofTwo p, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    simp [toTwo, columnOf, ofTwo, twoColumns]
  · apply Subtype.ext
    simp [toTwo, columnOf, ofTwo, twoColumns]

theorem matrixCount_two (n : ℕ) :
    matrixCount n 2 = (Fintype.card (Column n)) ^ 2 := by
  classical
  calc
    _ = Fintype.card (Column n × Column n) :=
      Fintype.card_congr
        (Equiv.ofBijective (@toTwo n) ⟨toTwo_injective n, toTwo_surjective n⟩)
    _ = _ := by simp [pow_two]

def threeColumns {n : ℕ} (t : Triple n) : Fin 3 → Column n :=
  fun j => if j = 0 then t.1 else if j = 1 then t.2.1 else t.2.2

def toTripleRaw {n : ℕ} (A : ValidMatrix n 3) : Triple n :=
  (columnOf A 0, columnOf A 1, columnOf A 2)

def toTriple {n : ℕ} (A : ValidMatrix n 3) : GoodTriple n :=
  ⟨toTripleRaw A, by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hi' : A.val i 0 = true ∧ A.val i 1 = true ∧ A.val i 2 = true := by
      simpa [common, toTripleRaw, columnOf, colSupport, and_assoc] using hi
    exact (rowSupport_three_le_two_iff A.val i).mp (A.property.2 i) hi'⟩

def ofTriple {n : ℕ} (t : GoodTriple n) : ValidMatrix n 3 :=
  ⟨fromColumns (threeColumns t.val), by
    constructor
    · intro j
      rw [colSupport_fromColumns]
      exact (threeColumns t.val j).property
    · intro i
      apply (rowSupport_three_le_two_iff _ i).mpr
      intro hi
      have hi' : i ∈ t.val.1.val ∧ i ∈ t.val.2.1.val ∧ i ∈ t.val.2.2.val := by
        simpa [fromColumns, threeColumns] using hi
      have hm : i ∈ common t.val := by simpa [common, and_assoc] using hi'
      rw [t.property] at hm
      exact Finset.notMem_empty i hm⟩

theorem toTriple_injective (n : ℕ) : Function.Injective (@toTriple n) := by
  intro A B h
  apply Subtype.ext
  apply matrix_ext_of_colSupport
  intro j
  have ht : toTripleRaw A = toTripleRaw B := congrArg Subtype.val h
  fin_cases j
  · exact congrArg (fun t : Triple n => t.1.val) ht
  · exact congrArg (fun t : Triple n => t.2.1.val) ht
  · exact congrArg (fun t : Triple n => t.2.2.val) ht

theorem toTriple_surjective (n : ℕ) : Function.Surjective (@toTriple n) := by
  intro t
  refine ⟨ofTriple t, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    simp [toTriple, toTripleRaw, columnOf, ofTriple, threeColumns]
  · apply Prod.ext
    · apply Subtype.ext
      simp [toTriple, toTripleRaw, columnOf, ofTriple, threeColumns]
    · apply Subtype.ext
      simp [toTriple, toTripleRaw, columnOf, ofTriple, threeColumns]

theorem matrixCount_three (n : ℕ) :
    matrixCount n 3 = Fintype.card (GoodTriple n) := by
  classical
  exact Fintype.card_congr
    (Equiv.ofBijective (@toTriple n) ⟨toTriple_injective n, toTriple_surjective n⟩)

end A401159

/-!
# OEIS A401159: two and three columns

The definition `matrixCount` in MatrixBridge counts actual Bool matrices with
at most two true entries in every row and every column.  Here we count triples
of column supports.  Their common intersection has at most two elements.

The identity `1[k = 0] + k = 1 + 1[k = 2]` for `k ≤ 2`, summed over all triples,
gives the desired count without subtraction in the natural numbers.
-/

namespace A401159

open Finset
open scoped BigOperators

lemma common_subset_first {n : ℕ} (t : Triple n) : common t ⊆ t.1.val := by
  intro i hi
  exact (Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1

lemma common_subset_second {n : ℕ} (t : Triple n) : common t ⊆ t.2.1.val := by
  intro i hi
  exact (Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).2

lemma common_subset_third {n : ℕ} (t : Triple n) : common t ⊆ t.2.2.val :=
  Finset.inter_subset_right

lemma common_card_le_two {n : ℕ} (t : Triple n) : (common t).card ≤ 2 :=
  (Finset.card_le_card (common_subset_first t)).trans t.1.property

/-- Count an incidence either by its triple or by its distinguished common row. -/
def incidenceEquiv (n : ℕ) :
    (Σ t : Triple n, {i : Fin n // i ∈ common t}) ≃
      (Σ i : Fin n,
        {s : Column n // i ∈ s.val} ×
        {s : Column n // i ∈ s.val} ×
        {s : Column n // i ∈ s.val}) where
  toFun p := by
    rcases p with ⟨⟨a, b, c⟩, ⟨i, h⟩⟩
    have hi : (i ∈ a.val ∧ i ∈ b.val) ∧ i ∈ c.val := by
      simpa only [common, Finset.mem_inter] using h
    exact ⟨i, (⟨a, hi.1.1⟩, ⟨b, hi.1.2⟩, ⟨c, hi.2⟩)⟩
  invFun p := by
    rcases p with ⟨i, ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩⟩
    exact ⟨(a, b, c), ⟨i, by simp only [common, Finset.mem_inter, ha, hb, hc,
      and_self]⟩⟩
  left_inv p := by
    rcases p with ⟨⟨a, b, c⟩, ⟨i, h⟩⟩
    rfl
  right_inv p := by
    rcases p with ⟨i, ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩⟩
    rfl

/-- Each specified row belongs to exactly `n` possible columns, hence to `n³`
triples.  There are `n` choices of the specified row. -/
theorem sum_common_card (n : ℕ) :
    (∑ t : Triple n, (common t).card) = n ^ 4 := by
  classical
  have h := Fintype.card_congr (incidenceEquiv n)
  simp only [Fintype.card_sigma, Fintype.card_coe, Fintype.card_prod,
    card_column_containing] at h
  simpa [pow_succ, Nat.mul_assoc] using h

/-- A two-element common intersection forces all three columns to equal it. -/
def twoCommonEquiv (n : ℕ) :
    {t : Triple n // (common t).card = 2} ≃
      {s : Finset (Fin n) // s.card = 2} where
  toFun t := ⟨common t.val, t.property⟩
  invFun s :=
    ⟨(⟨s.val, s.property.le⟩, ⟨s.val, s.property.le⟩, ⟨s.val, s.property.le⟩),
      by simpa only [common, Finset.inter_self] using s.property⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Finset.eq_of_subset_of_card_le (common_subset_first t.val)
        (by rw [t.property]; exact t.val.1.property)
    · apply Prod.ext
      · apply Subtype.ext
        exact Finset.eq_of_subset_of_card_le (common_subset_second t.val)
          (by rw [t.property]; exact t.val.2.1.property)
      · apply Subtype.ext
        exact Finset.eq_of_subset_of_card_le (common_subset_third t.val)
          (by rw [t.property]; exact t.val.2.2.property)
  right_inv s := by
    apply Subtype.ext
    simp only [common, Finset.inter_self]

theorem card_two_common (n : ℕ) :
    Fintype.card {t : Triple n // (common t).card = 2} = Nat.choose n 2 := by
  classical
  exact (Fintype.card_congr (twoCommonEquiv n)).trans (card_two_subsets n)

/-- The bounded-overlap count, expressed with no natural-number subtraction. -/
theorem card_good_triple_add (n : ℕ) :
    Fintype.card (GoodTriple n) + n ^ 4 =
      (Fintype.card (Column n)) ^ 3 + Nat.choose n 2 := by
  classical
  have h := card_zero_add_sum (Finset.univ : Finset (Triple n))
    (fun t => (common t).card) (fun t _ => common_card_le_two t)
  have hz : Fintype.card (GoodTriple n) =
      ((Finset.univ : Finset (Triple n)).filter
        (fun t => (common t).card = 0)).card := by
    change Fintype.card {t : Triple n // common t = ∅} = _
    rw [Fintype.card_subtype]
    simp only [Finset.card_eq_zero]
  have htwo := card_two_common n
  rw [Fintype.card_subtype] at htwo
  have hall : (Finset.univ : Finset (Triple n)).card =
      (Fintype.card (Column n)) ^ 3 := by
    simp [Triple, pow_succ, Nat.mul_assoc]
  rw [← hz, sum_common_card, hall, htwo] at h
  exact h

/-- A convenient integral form of the usual formula for `n choose 2`. -/
theorem two_choose_two_add (n : ℕ) : 2 * Nat.choose n 2 + n = n ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

/-- The two-column formula. -/
theorem count_two_columns (n : ℕ) :
    matrixCount n 2 = (1 + n + Nat.choose n 2) ^ 2 := by
  rw [matrixCount_two, card_column]

/-- The three-column combinatorial formula, before clearing denominators. -/
theorem count_three_columns_add (n : ℕ) :
    matrixCount n 3 + n ^ 4 =
      (1 + n + Nat.choose n 2) ^ 3 + Nat.choose n 2 := by
  rw [matrixCount_three]
  simpa only [card_column] using card_good_triple_add n

/-- A denominator-free version of the two-column polynomial. -/
theorem count_two_columns_polynomial (n : ℕ) :
    4 * matrixCount n 2 = (n ^ 2 + n + 2) ^ 2 := by
  have hc := two_choose_two_add n
  have hs : 2 * (1 + n + Nat.choose n 2) = n ^ 2 + n + 2 := by omega
  have hs2 := congrArg (fun k : ℕ => k ^ 2) hs
  rw [count_two_columns]
  nlinarith [hs2]

/-- The polynomial conjectured in OEIS A401159, with its denominator cleared.
It holds also for zero rows, where there is one empty matrix. -/
theorem count_three_columns_polynomial (n : ℕ) :
    8 * matrixCount n 3 =
      8 + 8 * n + 22 * n ^ 2 + 13 * n ^ 3 + n ^ 4 + 3 * n ^ 5 + n ^ 6 := by
  have hc := two_choose_two_add n
  have hs : 2 * (1 + n + Nat.choose n 2) = n ^ 2 + n + 2 := by omega
  have hs3 := congrArg (fun k : ℕ => k ^ 3) hs
  have hcount := count_three_columns_add n
  nlinarith [hs3]

/-- Both formulas together, on their original triangular-table domains. -/
theorem a401159_two_and_three_columns :
    (∀ n : ℕ, 2 ≤ n → matrixCount n 2 = (1 + n + Nat.choose n 2) ^ 2) ∧
    (∀ n : ℕ, 3 ≤ n →
      8 * matrixCount n 3 =
        8 + 8 * n + 22 * n ^ 2 + 13 * n ^ 3 + n ^ 4 + 3 * n ^ 5 + n ^ 6) :=
  ⟨fun n _ => count_two_columns n, fun n _ => count_three_columns_polynomial n⟩

end A401159

theorem OMA.solution : type_of% @OMA.S_oeis_a401159.main := by
  exact A401159.a401159_two_and_three_columns
