import OMAStatements.S_oeis_a183245

/-!
# The displaced permutations of OEIS A183245

For boards of size 2n+2, classify the two middle rows by their seven possible
ordered pairs of images. Once the columns of the top and bottom halves are fixed,
their assignment counts factor. Nested allowed sets make each count a product,
and reflecting the board exchanges the two halves. Summing the cases gives
25·4^(n-2) + 4·3^(n-2) for n ≥ 2. The index-one board has nine derangements.
The generating function and recurrence then follow by coefficient comparison.

Source: https://oeis.org/A183245
Credit: @bmendonca3
-/

namespace OMA.A183245
open PowerSeries

/-- The offset-one term in PR 30750 counts ordinary derangements of four elements. -/
theorem initial_count :
    ((Finset.univ : Finset (Equiv.Perm (Fin 4))).filter
      (fun p => ∀ i, (1 : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)).card = 9 := by
  classical
  rw [← Fintype.card_coe]
  let e := Equiv.subtypeEquivRight (α := Equiv.Perm (Fin 4))
    (p := fun p => p ∈ (Finset.univ.filter (fun p : Equiv.Perm (Fin 4) =>
      ∀ i, (1 : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)))
    (q := fun p => p ∈ derangements (Fin 4)) (fun p => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (∀ i, (1 : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|) ↔ ∀ i, p i ≠ i
      constructor
      · intro h i hi
        specialize h i
        simp [hi] at h
      · intro h i
        have hi := h i
        rw [← Fin.val_ne_iff] at hi
        rw [le_abs']
        omega)
  exact (Fintype.card_congr e).trans (card_derangements_fin_eq_numDerangements.trans (by decide))


theorem barker_of_count (a : ℕ → ℕ) (one : a 1 = 9)
    (count : ∀ k : ℕ, a (k + 2) = 25 * 4 ^ k + 4 * 3 ^ k) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 3 * X) * (1 - 4 * X)) =
      X * (9 - 34 * X + 17 * X ^ 2) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 7 * a (n - 1) - 12 * a (n - 2)) := by
  have recurrence (k : ℕ) : a (k + 4) + 12 * a (k + 2) = 7 * a (k + 3) := by
    rw [count (k + 2), count k, count (k + 1)]
    ring
  constructor
  · generalize hF : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = F
    have hl : F * ((1 - 3 * X) * (1 - 4 * X)) =
        F - 7 • (F * X ^ 1) + 12 • (F * X ^ 2) := by ring
    have hr : (X * (9 - 34 * X + 17 * X ^ 2) : ℚ⟦X⟧) =
        9 • X ^ 1 - 34 • X ^ 2 + 17 • X ^ 3 := by ring
    rw [hl, hr]
    subst hF
    ext n
    simp only [map_sub, map_add, map_nsmul, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
    rcases n with _ | _ | _ | _ | n
    · norm_num
    · norm_num [one]
    · norm_num [one, count 0]
    · norm_num [one, count 0, count 1]
    · have h : (a (n + 4) : ℚ) + 12 * a (n + 2) = 7 * a (n + 3) := by exact_mod_cast recurrence n
      simp
      linear_combination h
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have h : (a (k + 4) : ℤ) + 12 * a (k + 2) = 7 * a (k + 3) := by exact_mod_cast recurrence k
    simp
    linarith
/-- The displacement-restricted permutations from statement PR 30750. -/
def permCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin (2 * n + 2)))).filter
    (fun p => ∀ i, (n : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)).card

/-- The remaining hypothesis is a closed formula for the actual permutation count. -/
theorem reduction
    (count : ∀ k : ℕ, permCount (k + 2) = 25 * 4 ^ k + 4 * 3 ^ k) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (permCount n : ℚ)) *
        ((1 - 3 * X) * (1 - 4 * X)) =
      X * (9 - 34 * X + 17 * X ^ 2) ∧
    (∀ n : ℕ, 3 < n → (permCount n : ℤ) =
      7 * permCount (n - 1) - 12 * permCount (n - 2)) :=
  barker_of_count permCount initial_count count
end OMA.A183245

/-! The nested-choice counting lemma used in the displacement permutation proofs.
Process rows in order of increasing allowed column sets. An assignment is a list of
column choices, in row order, with every column used at most once. -/
namespace OMA.NestedChoices

variable {α : Type*} [DecidableEq α]

def assignments (used : Finset α) : List (Finset α) → Finset (List α)
  | [] => {[]}
  | r :: rs => (r \ used).biUnion fun x =>
      (assignments (insert x used) rs).image (List.cons x)

/-- A specification independent of the enumeration algorithm. -/
theorem mem_assignments {used : Finset α} {rs : List (Finset α)} {xs : List α} :
    xs ∈ assignments used rs ↔
      xs.Nodup ∧ (∀ x ∈ xs, x ∉ used) ∧ List.Forall₂ (fun x r => x ∈ r) xs rs := by
  induction rs generalizing xs used with
  | nil => cases xs <;> simp [assignments]
  | cons r rs ih =>
    cases xs with
    | nil => simp [assignments]
    | cons x xs =>
      simp [assignments, ih, List.nodup_cons, List.forall₂_cons]
      grind

/-- Product of the successive available-column counts. -/
def factors (k : ℕ) : List (Finset α) → ℕ
  | [] => 1
  | r :: rs => (r.card - k) * factors (k + 1) rs

theorem card_assignments (rs : List (Finset α)) (used : Finset α)
    (nested : rs.Pairwise (· ⊆ ·)) (available : ∀ r ∈ rs, used ⊆ r) :
    (assignments used rs).card = factors used.card rs := by
  induction rs generalizing used with
  | nil => simp [assignments, factors]
  | cons r rs ih =>
    obtain ⟨subsets, tail⟩ := List.pairwise_cons.mp nested
    rw [assignments, Finset.card_biUnion]
    · calc
        _ = ∑ _x ∈ r \ used, factors (used.card + 1) rs := by
          apply Finset.sum_congr rfl
          intro x hx
          obtain ⟨xr, xu⟩ := Finset.mem_sdiff.mp hx
          rw [Finset.card_image_of_injective _ (by intro l m h; exact (List.cons.inj h).2)]
          rw [ih (insert x used) tail, Finset.card_insert_of_notMem xu]
          intro s hs
          exact Finset.insert_subset (subsets s hs xr) (available s (by simp [hs]))
        _ = _ := by
          simp [factors, Finset.card_sdiff_of_subset (available r (by simp))]
    · intro x hx y hy hxy
      apply Finset.disjoint_left.mpr
      intro l hlx hly
      obtain ⟨l₁, _, rfl⟩ := Finset.mem_image.mp hlx
      obtain ⟨l₂, _, he⟩ := Finset.mem_image.mp hly
      exact hxy (List.cons.inj he).1.symm

/-- For a top row the displacement condition forces the column to its right. -/
theorem top_displacement {n i j : ℕ} (hi : i < n) :
    (n : ℤ) ≤ |(j : ℤ) - (i : ℤ)| ↔ n + i ≤ j := by
  rw [le_abs']
  omega

/-- Allowed columns of the first n rows, processed from the most restricted row down. -/
def topRows (n : ℕ) (columns : Finset ℕ) : List (Finset ℕ) :=
  (List.range n).reverse.map fun i => columns.filter (fun j => n + i ≤ j)

/-- Exact product count of admissible top-row injections into any selected columns. -/
theorem top_count (n : ℕ) (columns : Finset ℕ) :
    (assignments ∅ (topRows n columns)).card = factors 0 (topRows n columns) := by
  apply card_assignments
  · rw [topRows, List.pairwise_map, List.pairwise_reverse]
    apply List.pairwise_lt_range.imp
    intro i j hij c hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, by omega⟩
  · simp

/-- High columns in the zero-based indexing of the permutation board. -/
def high (n : ℕ) := Finset.Ico (n + 2) (2 * n + 2)

theorem high_filtered (n i : ℕ) :
    ((high n).filter fun j => n + i ≤ j).card = (2*n+2) - max (n+2) (n+i) := by
  have h : (high n).filter (fun j => n+i ≤ j) = Finset.Ico (max (n+2) (n+i)) (2*n+2) := by
    ext x
    simp [high, and_comm]
  rw [h, Nat.card_Ico]

private def highRows (n m : ℕ) :=
  (List.range m).reverse.map fun i => (high n).filter (fun j => n+i ≤ j)

private theorem highRows_succ (n m : ℕ) : highRows n (m+1) =
    ((high n).filter fun j => n + m ≤ j) :: highRows n m := by
  simp [highRows, List.range_succ]

private theorem high_factors (n m : ℕ) (h : m + 2 ≤ n) :
    factors (n - (m + 2)) (highRows n (m + 2)) = 2 * 3 ^ m := by
  induction m with
  | zero =>
    rw [highRows_succ, factors, highRows_succ, factors]
    rw [high_filtered, high_filtered]
    have first : 2*n+2 - max (n+2) (n+1) - (n-(0+2)) = 2 := by omega
    have second : 2*n+2 - max (n+2) (n+0) - (n-(0+2)+1) = 1 := by omega
    rw [first, second]
    rfl
  | succ m ih =>
    rw [highRows_succ, factors, high_filtered]
    have shift : n - (m + 1 + 2) + 1 = n - (m + 2) := by omega
    rw [shift, ih (by omega)]
    rw [Nat.max_eq_right (by omega)]
    have three : 2 * n + 2 - (n + (m + 1 + 1)) - (n - (m + 1 + 2)) = 3 := by omega
    rw [three, pow_succ]
    ring

/-- The empty flexible-column case of the top-row count in A183245. -/
theorem high_only_count (k : ℕ) :
    (assignments ∅ (topRows (k + 2) (high (k + 2)))).card = 2 * 3 ^ k := by
  rw [top_count]
  simpa [highRows, topRows] using high_factors (k + 2) k (by omega)

private def rowsOf (n m : ℕ) (C : Finset ℕ) :=
  (List.range m).reverse.map fun i => C.filter (fun j => n+i ≤ j)

private theorem rowsOf_succ (n m : ℕ) (C : Finset ℕ) : rowsOf n (m+1) C =
    (C.filter fun j => n+m ≤ j) :: rowsOf n m C := by
  simp [rowsOf, List.range_succ]

/-- All four flexible-column choices in the top half of the A183245 board. The
two outermost high columns may be removed in either order. Only their number matters. -/
theorem flexible_count (k : ℕ) (F V : Finset ℕ)
    (hf : F ⊆ Finset.Ico (k+2) (k+4))
    (hv : V ⊆ Finset.Ico (2*(k+2)) (2*(k+2)+2)) (size : F.card = V.card) :
    (assignments ∅ (topRows (k+2) ((high (k+2) \ V) ∪ F))).card =
      (3 - F.card)^k * (2 - if k+2 ∈ F then 1 else 0) := by
  set n := k+2 with hn
  let C := (high n \ V) ∪ F
  have vsub : V ⊆ high n := by
    intro x hx
    have hm := Finset.mem_Ico.mp (hv hx)
    apply Finset.mem_Ico.mpr
    omega
  have diss : Disjoint (high n \ V) F := by
    apply Finset.disjoint_left.mpr
    intro x hx hxf
    have hh := Finset.mem_Ico.mp (Finset.mem_sdiff.mp hx).1
    have hm := Finset.mem_Ico.mp (hf hxf)
    omega
  have highcard : (high n).card = n := by simp [high]; omega
  have vc : V.card ≤ n := highcard ▸ Finset.card_le_card vsub
  have cardC : C.card = n := by
    dsimp [C]
    rw [Finset.card_union_of_disjoint diss, Finset.card_sdiff_of_subset vsub, highcard, size]
    omega
  have cmin {x : ℕ} (hx : x ∈ C) : n ≤ x := by
    obtain h | h := Finset.mem_union.mp hx
    · have := (Finset.mem_Ico.mp (Finset.mem_sdiff.mp h).1).1
      omega
    · exact (Finset.mem_Ico.mp (hf h)).1
  have cn : n ∈ C ↔ n ∈ F := by
    simp [C, high]
  have zeroF : C.filter (fun j => n+0 ≤ j) = C := by
    ext j
    simp only [Finset.mem_filter, Nat.add_zero, and_iff_left_iff_imp]
    exact cmin
  have oneF : C.filter (fun j => n+1 ≤ j) = C.erase n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase]
    by_cases hj : j ∈ C
    · have hmin := cmin hj
      simp only [hj, true_and, and_true]
      omega
    · simp [hj]
  have late (i : ℕ) (hi : 2 ≤ i) (hin : i < n) :
      (C.filter (fun j => n+i ≤ j)).card = (2*n+2-(n+i)) - V.card := by
    have eq : C.filter (fun j => n+i ≤ j) =
        ((high n).filter (fun j => n+i ≤ j)) \ V := by
      ext x
      simp only [C, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      have bad : x ∈ F → x < n+2 := fun h => (Finset.mem_Ico.mp (hf h)).2
      grind
    have sub : V ⊆ (high n).filter (fun j => n+i ≤ j) := by
      intro x hx
      have hm := (Finset.mem_Ico.mp (hv hx)).1
      exact Finset.mem_filter.mpr ⟨vsub hx, by omega⟩
    rw [eq, Finset.card_sdiff_of_subset sub, high_filtered, Nat.max_eq_right (by omega)]
  have solve (m : ℕ) (ht : m+2 ≤ n) :
      factors (n-(m+2)) (rowsOf n (m+2) C) =
        (3-F.card)^m * (2 - if n ∈ F then 1 else 0) := by
    induction m with
    | zero =>
      rw [rowsOf_succ, factors, rowsOf_succ, factors, oneF, zeroF, cardC]
      have factor1 : n - (n-(0+2)+1) = 1 := by omega
      rw [factor1]
      by_cases h : n ∈ F
      · rw [Finset.card_erase_of_mem (cn.mpr h), cardC, if_pos h]
        change (n - 1 - (n - 2)) * (1 * 1) = 1 * (2 - 1)
        omega
      · rw [Finset.erase_eq_of_notMem (fun e => h (cn.mp e)), cardC, if_neg h]
        change (n - (n - 2)) * (1 * 1) = 1 * (2 - 0)
        omega
    | succ m ih =>
      rw [rowsOf_succ, factors, late _ (by omega) (by omega)]
      have shift : n - (m+1+2) + 1 = n - (m+2) := by omega
      rw [shift, ih (by omega)]
      have eq : 2*n+2 - (n+(m+1+1)) - V.card - (n-(m+1+2)) = 3-F.card := by omega
      rw [eq, pow_succ]
      ring
  rw [top_count]
  simpa [topRows, rowsOf, C, hn] using solve k (by omega)

/-- Column reversal on the zero-based board. -/
def mirror (n j : ℕ) := 2*n+1-j

theorem reflected_displacement {n i j : ℕ} (hi : i ≤ 2*n+1) (hj : j ≤ 2*n+1) :
    |((mirror n j : ℕ) : ℤ) - (mirror n i : ℕ)| = |(j : ℤ) - (i : ℤ)| := by
  unfold mirror
  rw [Nat.cast_sub hj, Nat.cast_sub hi, ← abs_neg ((j : ℤ) - (i : ℤ))]
  congr 1
  ring

/-- Allowed column sets for bottom rows, under the same row order after reversal. -/
def bottomRows (n : ℕ) (B : Finset ℕ) : List (Finset ℕ) :=
  (List.range n).reverse.map fun i => B.filter (fun j => j + n + i ≤ 2*n+1)

/-- Reversal preserves the number of legal assignments; the right-hand top count can
therefore be replaced with the explicit formula for the corresponding top columns. -/
theorem reflected_count (n : ℕ) (C : Finset ℕ) (bounded : ∀ j ∈ C, j ≤ 2*n+1) :
    (assignments ∅ (bottomRows n (C.image (mirror n)))).card =
    (assignments ∅ (topRows n C)).card := by
  rw [top_count]
  have nested : (bottomRows n (C.image (mirror n))).Pairwise (· ⊆ ·) := by
    rw [bottomRows, List.pairwise_map, List.pairwise_reverse]
    apply List.pairwise_lt_range.imp
    intro i j hij c hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, by omega⟩
  rw [card_assignments _ _ nested (by simp)]
  have hcard (i : ℕ) : ((C.image (mirror n)).filter (fun j => j+n+i ≤ 2*n+1)).card =
      (C.filter (fun j => n+i ≤ j)).card := by
    have heq : (C.image (mirror n)).filter (fun j => j+n+i ≤ 2*n+1) =
        (C.filter (fun j => n+i ≤ j)).image (mirror n) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨x,hx,rfl⟩,h⟩
        exact ⟨x,⟨hx, by have := bounded x hx; unfold mirror at h; omega⟩,rfl⟩
      · rintro ⟨x,⟨hx,h⟩,rfl⟩
        exact ⟨⟨x,hx,rfl⟩,by have := bounded x hx; unfold mirror; omega⟩
    rw [heq, Finset.card_image_of_injOn]
    intro x hx y hy he
    have bx := bounded x (Finset.mem_filter.mp hx).1
    have by' := bounded y (Finset.mem_filter.mp hy).1
    unfold mirror at he
    omega
  suffices h : ∀ (rows : List ℕ) (t : ℕ),
      factors t (rows.map fun i => (C.image (mirror n)).filter (fun j => j+n+i ≤ 2*n+1)) =
      factors t (rows.map fun i => C.filter (fun j => n+i ≤ j)) by
    exact h _ _
  intro rows
  induction rows with
  | nil => simp [factors]
  | cons i rows ih =>
    intro t
    simp only [List.map_cons, factors, hcard, ih]

end OMA.NestedChoices

namespace OMA.MiddleRows

/-- Exact allowed columns of the first of the two middle rows (zero-based). -/
theorem first {n j : ℕ} (hj : j < 2*n+2) :
    (n : ℤ) ≤ |(j : ℤ) - (n : ℤ)| ↔ j = 0 ∨ j = 2*n ∨ j = 2*n+1 := by
  rw [le_abs']
  omega

/-- Exact allowed columns of the second middle row. -/
theorem second {n j : ℕ} (hj : j < 2*n+2) :
    (n : ℤ) ≤ |(j : ℤ) - ((n+1 : ℕ) : ℤ)| ↔ j = 0 ∨ j = 1 ∨ j = 2*n+1 := by
  rw [le_abs']
  omega

def choices (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (2*n+2)) ×ˢ (Finset.range (2*n+2))).filter (fun p =>
    (n : ℤ) ≤ |(p.1 : ℤ) - (n : ℤ)| ∧
    (n : ℤ) ≤ |(p.2 : ℤ) - ((n+1 : ℕ) : ℤ)| ∧ p.1 ≠ p.2)

/-- The seven possible ordered assignments to the two middle rows. -/
theorem seven (n : ℕ) (hn : 2 ≤ n) :
    choices n = {(0,1), (0,2*n+1), (2*n,0), (2*n,1), (2*n,2*n+1),
      (2*n+1,0), (2*n+1,1)} := by
  ext ⟨i,j⟩
  simp only [choices, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hi,hj⟩,h1,h2,hne⟩
    rw [first hi] at h1
    rw [second hj] at h2
    omega
  · intro h
    have hi : i < 2*n+2 := by omega
    have hj : j < 2*n+2 := by omega
    exact ⟨⟨hi,hj⟩,(first hi).2 (by omega),(second hj).2 (by omega),by omega⟩

end OMA.MiddleRows

/-- Summing the seven middle-row configurations after splitting each legal permutation
into top and bottom assignments gives the tail formula used by Barker's recurrence. -/
theorem OMA.MiddleRows.sum_counts (k : ℕ) :
    2 * (2 * 3 ^ k) + 5 * ((2 ^ k)^2 + (2 * 2^k)^2) =
      25 * 4^k + 4 * 3^k := by
  have power : 4^k = (2^k)^2 := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  rw [power]
  ring


namespace OMA.NestedChoices

private theorem ofFn_valid {n : ℕ} {R : Fin n → Finset (Fin n)} (p : Equiv.Perm (Fin n)) :
    List.ofFn p ∈ assignments ∅ (List.ofFn R) ↔ ∀ i, p i ∈ R i := by
  rw [mem_assignments]
  simp only [List.nodup_ofFn_ofInjective p.injective, Finset.notMem_empty, not_false_eq_true, implies_true,
    true_and, List.forall₂_iff_get, List.length_ofFn, List.get_ofFn]
  constructor
  · intro h i
    exact h i.val i.isLt i.isLt
  · intro h i hi _
    exact h ⟨i,by simpa using hi⟩

/-- Row lists count exactly the permutations respecting the given board. -/
theorem permutation_count {n : ℕ} (R : Fin n → Finset (Fin n)) :
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun p => ∀ i, p i ∈ R i)).card =
    (assignments ∅ (List.ofFn R)).card := by
  classical
  apply Finset.card_bij (fun (p : Equiv.Perm (Fin n)) _ => List.ofFn (p : Fin n → Fin n))
  · intro p hp
    exact (ofFn_valid p).2 (Finset.mem_filter.mp hp).2
  · intro p _ q _ he
    exact Equiv.ext (congrFun (List.ofFn_injective he))
  · intro l hl
    obtain ⟨nodup, _, valid⟩ := mem_assignments.mp hl
    have len : l.length = n := by simpa using valid.length_eq
    let f : Fin n → Fin n := fun i => l.get (Fin.cast len.symm i)
    have ofn : List.ofFn f = l := by
      apply List.ext_getElem
      · simpa using len.symm
      · intro i h₁ h₂
        simp [f]
    have inj : Function.Injective f := List.nodup_ofFn.mp (ofn ▸ nodup)
    let p := Equiv.ofBijective f ⟨inj, Finite.surjective_of_injective inj⟩
    have eq : List.ofFn (p : Fin n → Fin n) = l := ofn
    exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(ofFn_valid p).1 (eq ▸ hl)⟩,eq⟩
end OMA.NestedChoices

namespace OMA.NestedChoices

/-- Cardinality of a full square board, when columns are represented as bounded natural
numbers and the rows are indexed by Fin. -/
theorem natBoard_count {N : ℕ} (R : Fin N → Finset ℕ)
    (bound : ∀ i c, c ∈ R i → c < N) :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun p => ∀ i, (p i).val ∈ R i)).card =
      (assignments ∅ (List.ofFn R)).card := by
  classical
  have valid (p : Equiv.Perm (Fin N)) :
      List.ofFn (fun i => (p i).val) ∈ assignments ∅ (List.ofFn R) ↔
      ∀ i, (p i).val ∈ R i := by
    have inj : Function.Injective (fun i => (p i).val) :=
      Fin.val_injective.comp p.injective
    rw [mem_assignments]
    simp only [List.nodup_ofFn_ofInjective inj, Finset.notMem_empty, not_false_eq_true,
      implies_true, true_and, List.forall₂_iff_get, List.length_ofFn, List.get_ofFn]
    constructor
    · intro h i
      exact h i.val i.isLt i.isLt
    · intro h i hi _
      exact h ⟨i,hi⟩
  apply Finset.card_bij (fun (p : Equiv.Perm (Fin N)) _ => List.ofFn (fun i => (p i).val))
  · intro p hp
    exact (valid p).2 (Finset.mem_filter.mp hp).2
  · intro p _ q _ h
    exact Equiv.ext (fun i => Fin.ext (congrFun (List.ofFn_injective h) i))
  · intro l hl
    obtain ⟨nd,_,ok⟩ := mem_assignments.mp hl
    have len : l.length = N := by simpa using ok.length_eq
    let get : Fin N → ℕ := fun i => l.get (Fin.cast len.symm i)
    have ofn : List.ofFn get = l := by
      apply List.ext_getElem
      · simpa using len.symm
      · intro i h₁ h₂
        simp [get]
    have ig : Function.Injective get := List.nodup_ofFn.mp (ofn ▸ nd)
    have hg (i : Fin N) : get i ∈ R i := by
      have := (List.forall₂_iff_get.mp ok).2 i.val (by omega) (by simp)
      simpa [get, List.get_ofFn] using this
    let f : Fin N → Fin N := fun i => ⟨get i,bound i _ (hg i)⟩
    have inj : Function.Injective f := fun i j h => ig (congrArg Fin.val h)
    let p := Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩
    have eq : List.ofFn (fun i => (p i).val) = l := ofn
    exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(valid p).1 (eq ▸ hl)⟩,eq⟩

/-- Reorder the first n rows so the top row constraints run from tight to loose. -/
private def rowOrder (n : ℕ) : Equiv.Perm (Fin (2*n+2)) where
  toFun i := ⟨if i.val < n then n-1-i.val else i.val,by split <;> omega⟩
  invFun i := ⟨if i.val < n then n-1-i.val else i.val,by split <;> omega⟩
  left_inv i := by
    apply Fin.ext
    dsimp
    (repeat' split) <;> omega
  right_inv i := by
    apply Fin.ext
    dsimp
    (repeat' split) <;> omega

def mid1 (n : ℕ) := (Finset.range (2*n+2)).filter (fun j : ℕ =>
  (n : ℤ) ≤ |(j : ℤ) - (n : ℤ)|)
def mid2 (n : ℕ) := (Finset.range (2*n+2)).filter (fun j : ℕ =>
  (n : ℤ) ≤ |(j : ℤ) - ((n+1 : ℕ) : ℤ)|)

private def reordered (n : ℕ) (i : Fin (2*n+2)) : Finset ℕ :=
  (Finset.range (2*n+2)).filter (fun c : ℕ => (n : ℤ) ≤ |(c : ℤ) - ((rowOrder n i).val : ℤ)|)

private theorem reordered_rows (n : ℕ) :
    List.ofFn (reordered n) =
      topRows n (Finset.range (2*n+2)) ++ [mid1 n,mid2 n] ++
      bottomRows n (Finset.range (2*n+2)) := by
  apply List.ext_getElem
  · simp [topRows,bottomRows]; omega
  · intro j hj hk
    have hj' : j < 2*n+2 := by simpa only [List.length_ofFn] using hj
    rw [List.getElem_ofFn]
    by_cases ht : j < n
    · have hleft : j < (topRows n (Finset.range (2*n+2)) ++ [mid1 n,mid2 n]).length := by
        simp [topRows]; omega
      rw [List.getElem_append_left hleft, List.getElem_append_left (by simpa [topRows])]
      simp [topRows,List.getElem_reverse,reordered,rowOrder,ht]
      ext c
      simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
      intro _
      exact top_displacement (by omega)
    · by_cases hm : j < n+2
      · have hleft : j < (topRows n (Finset.range (2*n+2)) ++ [mid1 n,mid2 n]).length := by
          simpa [topRows] using hm
        rw [List.getElem_append_left hleft, List.getElem_append_right (by simpa [topRows] using ht)]
        rcases (show j = n ∨ j = n+1 by omega) with rfl | rfl
        · simp [reordered,mid1,topRows,rowOrder]
        · simp [reordered,mid2,topRows,rowOrder]
      · rw [List.getElem_append_right (by simpa [topRows] using hm)]
        simp [reordered,topRows,bottomRows,List.getElem_reverse,rowOrder,ht]
        ext c
        simp only [Finset.mem_filter,Finset.mem_range,and_congr_right_iff]
        intro hc
        rw [le_abs']
        omega

/-- Convert the exact restricted-permutation count in A183245 into the block assignment count. -/
theorem original_to_board (n : ℕ) :
    ((Finset.univ : Finset (Equiv.Perm (Fin (2*n+2)))).filter
      (fun p => ∀ i, (n : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)).card =
    (assignments ∅ (topRows n (Finset.range (2*n+2)) ++ [mid1 n,mid2 n] ++
      bottomRows n (Finset.range (2*n+2)))).card := by
  rw [←reordered_rows, ←natBoard_count (reordered n) (fun i c h => Finset.mem_range.mp (Finset.mem_filter.mp h).1)]
  let e := rowOrder n
  apply Finset.card_bij (fun (p : Equiv.Perm (Fin (2*n+2))) _ => e.trans p)
  · intro p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i => ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (p (e i)).isLt,
      (Finset.mem_filter.mp hp).2 (e i)⟩
  · intro p _ q _ eq
    apply Equiv.ext
    intro i
    simpa using DFunLike.congr_fun eq (e.symm i)
  · intro p hp
    refine ⟨e.symm.trans p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro i
      have h := (Finset.mem_filter.mp ((Finset.mem_filter.mp hp).2 (e.symm i))).2
      simpa [e] using h
    · ext i
      simp

end OMA.NestedChoices

namespace OMA.NestedChoices

variable {α : Type*} [DecidableEq α]

def restrictRows (R : List (Finset α)) (T : Finset α) := R.map (· ∩ T)

private theorem restricted_iff {x : List α} {A : List (Finset α)} {T : Finset α} :
    x ∈ assignments ∅ (restrictRows A T) ↔
    x ∈ assignments ∅ A ∧ x.toFinset ⊆ T := by
  simp only [mem_assignments, Finset.notMem_empty, not_false_eq_true, implies_true, true_and]
  rw [restrictRows, List.forall₂_map_right_iff]
  have aux (l : List α) (rs : List (Finset α)) :
      List.Forall₂ (fun a r => a ∈ r ∩ T) l rs ↔
      List.Forall₂ (fun a r => a ∈ r) l rs ∧ l.toFinset ⊆ T := by
    induction l generalizing rs with
    | nil => cases rs <;> simp
    | cons a l ih =>
      cases rs with
      | nil => simp
      | cons r rs =>
        rw [List.forall₂_cons, List.forall₂_cons, ih rs]
        simp only [List.toFinset_cons, Finset.insert_subset_iff, Finset.mem_inter]
        tauto
  rw [aux]
  tauto

private theorem exact_cols {xs : List α} {A : List (Finset α)} {T : Finset α}
    (hx : xs ∈ assignments ∅ (restrictRows A T)) (hT : T.card = A.length) :
    xs.toFinset = T := by
  obtain ⟨h,s⟩ := restricted_iff.mp hx
  have v := mem_assignments.mp h
  exact Finset.eq_of_subset_of_card_le s (by rw [List.toFinset_card_of_nodup v.1,hT,v.2.2.length_eq])

private theorem forall_mem_cols {xs : List α} {R : List (Finset α)} {U : Finset α}
    (h : List.Forall₂ (fun x s => x ∈ s) xs R) (hs : ∀ r ∈ R, r ⊆ U) :
    xs.toFinset ⊆ U := by
  induction h with
  | nil => simp
  | cons h _ ih =>
    simp only [List.toFinset_cons, Finset.insert_subset_iff]
    exact ⟨hs _ (by simp) h, ih (fun r hr => hs r (by simp [hr]))⟩

/-- The row order fixes the unique boundary between the two ordinary blocks. -/
private theorem split_board {A B : List (Finset α)} {M N : Finset α} {l : List α}
    (h : l ∈ assignments ∅ (A ++ M :: N :: B)) :
    ∃ x y u v, l = x ++ u :: v :: y ∧ x ∈ assignments ∅ A ∧
      y ∈ assignments ∅ B ∧ u ∈ M ∧ v ∈ N ∧ (x ++ u :: v :: y).Nodup := by
  obtain ⟨hn,_,hf⟩ := mem_assignments.mp h
  let x := l.take A.length
  have hx := List.forall₂_take_append l A (M::N::B) hf
  have hy := List.forall₂_drop_append l A (M::N::B) hf
  have eql : l = x ++ l.drop A.length := (List.take_append_drop _ _).symm
  generalize hdrop : l.drop A.length = ys at hy eql
  cases ys with
  | nil => cases hy
  | cons u ys =>
    cases ys with
    | nil => cases hy with | cons _ hy => cases hy
    | cons v y =>
      obtain ⟨hu, hv, hy⟩ := List.forall₂_cons.mp hy |>.imp_right List.forall₂_cons.mp
      rw [eql] at hn
      have ha := List.nodup_append'.mp hn
      have hb := (List.nodup_cons.mp (List.nodup_cons.mp ha.2.1).2).2
      exact ⟨x,y,u,v,eql,mem_assignments.mpr ⟨ha.1,by simp,hx⟩,
        mem_assignments.mpr ⟨hb,by simp,hy⟩,hu,hv,hn⟩

private abbrev Packet (α : Type*) := Σ _p : α × α, Σ _T : Finset α, List α × List α

private def family (U M N : Finset α) (A B : List (Finset α)) : Finset (Packet α) :=
  ((M ×ˢ N).filter (fun p => p.1 ≠ p.2)).sigma fun p =>
    ((U \ {p.1,p.2}).powersetCard A.length).sigma fun T =>
      assignments ∅ (restrictRows A T) ×ˢ
        assignments ∅ (restrictRows B (U \ ({p.1,p.2} ∪ T)))

private def joinPacket (z : Packet α) := z.2.2.1 ++ z.1.1 :: z.1.2 :: z.2.2.2

private theorem unpack_valid {U M N : Finset α} {A B : List (Finset α)} {l : List α}
    (au : ∀ r ∈ A, r ⊆ U) (bu : ∀ r ∈ B, r ⊆ U)
    (hl : l ∈ assignments ∅ (A ++ M :: N :: B)) :
    ∃ z ∈ family U M N A B, joinPacket z = l := by
  obtain ⟨x,y,u,v,rfl,hx,hy,hu,hv,hn⟩ := split_board hl
  refine ⟨⟨(u,v),x.toFinset,x,y⟩,?_,rfl⟩
  have Hx := mem_assignments.mp hx
  have Hy := mem_assignments.mp hy
  have xu := forall_mem_cols Hx.2.2 au
  have yu := forall_mem_cols Hy.2.2 bu
  have dis := (List.nodup_append'.mp hn).2.2
  have rest := (List.nodup_append'.mp hn).2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at rest
  simp only [family, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product,
    Finset.mem_powersetCard, restricted_iff]
  refine ⟨⟨⟨hu,hv⟩,rest.1.1⟩, ⟨?_,by rw [List.toFinset_card_of_nodup Hx.1,Hx.2.2.length_eq]⟩,
    ⟨hx,Finset.Subset.rfl⟩,hy,?_⟩
  · intro a ha
    have hp := List.mem_toFinset.mp ha
    apply Finset.mem_sdiff.mpr
    exact ⟨xu ha,by simp only [Finset.mem_insert,Finset.mem_singleton]; rintro (rfl|rfl) <;> exact dis hp (by simp)⟩
  · intro a ha
    have hp := List.mem_toFinset.mp ha
    apply Finset.mem_sdiff.mpr
    refine ⟨yu ha,?_⟩
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset]
    intro h
    rcases h with (rfl|rfl)|h
    · exact rest.1.2 hp
    · exact rest.2.1 hp
    · exact dis h (by simp [hp])


private theorem pack_valid {U M N : Finset α} {A B : List (Finset α)} {z : Packet α}
    (hz : z ∈ family U M N A B) :
    joinPacket z ∈ assignments ∅ (A ++ M :: N :: B) := by
  rcases z with ⟨⟨u,v⟩,T,x,y⟩
  simp only [family, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product,
    Finset.mem_powersetCard, restricted_iff] at hz
  obtain ⟨⟨⟨hu,hv⟩,hne⟩,⟨hsub,hcard⟩,⟨hx,xt⟩,hy,yt⟩ := hz
  have X := mem_assignments.mp hx
  have Y := mem_assignments.mp hy
  apply mem_assignments.mpr
  refine ⟨?_,by simp,List.rel_append X.2.2 (.cons hu (.cons hv Y.2.2))⟩
  apply List.nodup_append'.mpr
  refine ⟨X.1,?_,?_⟩
  · simp only [List.nodup_cons,List.mem_cons,not_or]
    refine ⟨⟨hne,?_⟩,?_,Y.1⟩
    · intro hyu
      have H := (Finset.mem_sdiff.mp (yt (List.mem_toFinset.mpr hyu))).2
      simp at H
    · intro hyv
      have H := (Finset.mem_sdiff.mp (yt (List.mem_toFinset.mpr hyv))).2
      simp at H
  · intro a hx' ht
    have atT := xt (List.mem_toFinset.mpr hx')
    have ha := (Finset.mem_sdiff.mp (hsub atT)).2
    simp only [List.mem_cons] at ht
    rcases ht with rfl|rfl|hy'
    · simp at ha
    · simp at ha
    · exact (Finset.mem_sdiff.mp (yt (List.mem_toFinset.mpr hy'))).2 (Finset.mem_union_right _ atT)

private theorem injective_packet {U M N : Finset α} {A B : List (Finset α)}
    {z w : Packet α} (hz : z ∈ family U M N A B) (hw : w ∈ family U M N A B)
    (eq : joinPacket z = joinPacket w) : z = w := by
  rcases z with ⟨⟨u,v⟩,T,x,y⟩
  rcases w with ⟨⟨u',v'⟩,T',x',y'⟩
  simp only [family,Finset.mem_sigma,Finset.mem_product,Finset.mem_powersetCard] at hz hw
  have hx := hz.2.2.1
  have hx' := hw.2.2.1
  have lenX := (mem_assignments.mp (restricted_iff.mp hx).1).2.2.length_eq
  have lenX' := (mem_assignments.mp (restricted_iff.mp hx').1).2.2.length_eq
  change x ++ u :: v :: y = x' ++ u' :: v' :: y' at eq
  obtain ⟨ex,er⟩ := List.append_inj eq (by omega)
  subst x'
  obtain ⟨eu,etail⟩ := List.cons.inj er
  obtain ⟨ev,ey⟩ := List.cons.inj etail
  subst u'
  subst v'
  subst y'
  obtain rfl : T = T' := (exact_cols hx hz.2.1.2).symm.trans (exact_cols hx' hw.2.1.2)
  rfl

theorem split_count (U M N : Finset α) (A B : List (Finset α))
    (au : ∀ r ∈ A, r ⊆ U) (bu : ∀ r ∈ B, r ⊆ U) :
    (assignments ∅ (A ++ M :: N :: B)).card =
      ∑ p ∈ (M ×ˢ N).filter (fun p => p.1 ≠ p.2),
        ∑ T ∈ (U \ {p.1,p.2}).powersetCard A.length,
          (assignments ∅ (restrictRows A T)).card *
          (assignments ∅ (restrictRows B (U \ ({p.1,p.2} ∪ T)))).card := by
  calc
    _ = (family U M N A B).card := by
      symm
      exact Finset.card_bij (fun z _ => joinPacket z) (fun _ h => pack_valid h)
        (fun _ h _ h' e => injective_packet h h' e) (fun _ h => by obtain ⟨z,hz,e⟩ := unpack_valid au bu h; exact ⟨z,hz,e⟩)
    _ = _ := by simp [family,Finset.card_sigma]

end OMA.NestedChoices

namespace OMA.NestedChoices

private theorem restrict_top (n : ℕ) {T U : Finset ℕ} (h : T ⊆ U) :
    restrictRows (topRows n U) T = topRows n T := by
  unfold restrictRows topRows
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  ext j
  simp only [Function.comp_apply, Finset.mem_inter, Finset.mem_filter]
  grind

private theorem restrict_bottom (n : ℕ) {T U : Finset ℕ} (h : T ⊆ U) :
    restrictRows (bottomRows n U) T = bottomRows n T := by
  unfold restrictRows bottomRows
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  ext j
  simp only [Function.comp_apply, Finset.mem_inter, Finset.mem_filter]
  grind

theorem board_split (n : ℕ) :
    let U := Finset.range (2*n+2)
    (assignments ∅ (topRows n U ++ [mid1 n,mid2 n] ++ bottomRows n U)).card =
      ∑ p ∈ OMA.MiddleRows.choices n,
        ∑ T ∈ (U \ {p.1,p.2}).powersetCard n,
          (assignments ∅ (topRows n T)).card *
          (assignments ∅ (bottomRows n ((U \ {p.1,p.2}) \ T))).card := by
  dsimp only
  set U := Finset.range (2*n+2)
  have au : ∀ r ∈ topRows n U, r ⊆ U := by
    intro r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact Finset.filter_subset _ _
  have bu : ∀ r ∈ bottomRows n U, r ⊆ U := by
    intro r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact Finset.filter_subset _ _
  have mid : ((mid1 n ×ˢ mid2 n).filter fun p => p.1 ≠ p.2) = OMA.MiddleRows.choices n := by
    ext p
    simp only [mid1,mid2,OMA.MiddleRows.choices,Finset.mem_filter,Finset.mem_product]
    tauto
  have eq := split_count U (mid1 n) (mid2 n) (topRows n U) (bottomRows n U) au bu
  rw [mid,show (topRows n U).length = n by simp [topRows]] at eq
  rw [List.append_assoc]
  refine eq.trans ?_
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro T hT
  have ht := (Finset.mem_powersetCard.mp hT).1.trans Finset.sdiff_subset
  have hb : U \ ({p.1,p.2} ∪ T) = (U \ {p.1,p.2}) \ T := by ext; simp; tauto
  rw [restrict_top n ht, restrict_bottom n Finset.sdiff_subset, hb]

end OMA.NestedChoices

namespace OMA.ColumnAllocation

/-- Columns usable by either half of the board. -/
def flex (n : ℕ) : Finset ℕ := {n,n+1}

/-- Middle row columns, restricted to the high side. -/
def removedHigh (n : ℕ) (p : ℕ × ℕ) : Finset ℕ := ({p.1,p.2} : Finset ℕ).filter (fun j => n+2 ≤ j)

def topCols (n : ℕ) (p : ℕ × ℕ) (F : Finset ℕ) : Finset ℕ :=
  (Finset.Ico (n+2) (2*n+2) \ removedHigh n p) ∪ F

/-- Flexible sets with the required number of columns. -/
def flexSets (n : ℕ) (p : ℕ × ℕ) : Finset (Finset ℕ) :=
  (flex n).powersetCard (removedHigh n p).card

/-- The two outside-row factors after reflecting the bottom half. -/
def weight (k : ℕ) (F : Finset ℕ) : ℕ :=
  ((3-F.card)^k * (2 - if k+2 ∈ F then 1 else 0)) *
  ((3-((flex (k+2)) \ F).card)^k * (2 - if k+3 ∉ F then 1 else 0))


private theorem flex_card (n : ℕ) : (flex n).card = 2 := by simp [flex]

private theorem flex_one (n : ℕ) :
    (flex n).powersetCard 1 = {{n},{n+1}} := by
  ext F
  simp only [Finset.mem_powersetCard, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h,hc⟩
    obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hc
    have hx := h (by simp : x ∈ ({x} : Finset ℕ))
    simpa [flex] using hx
  · rintro (rfl|rfl) <;> simp [flex]

private theorem weight_none (k : ℕ) : weight k ∅ = 2 * 3^k := by
  simp [weight,flex_card,mul_comm]

private theorem weight_all (k : ℕ) : weight k (flex (k+2)) = 2 * 3^k := by
  simp [weight,flex,mul_comm]

private theorem weight_left (k : ℕ) : weight k {k+2} = 4^k := by
  have hh : flex (k+2) \ {k+2} = {k+3} := by ext x; simp [flex]; omega
  simp [weight,hh,←mul_pow]

private theorem weight_right (k : ℕ) : weight k {k+3} = 4*4^k := by
  have hh : flex (k+2) \ {k+3} = {k+2} := by ext x; simp [flex]
  simp [weight,hh]
  calc
    _ = 4 * (2^k * 2^k) := by ring
    _ = _ := by rw [←mul_pow]; norm_num

theorem weights_by_size (k h : ℕ) (hh : h ≤ 2) :
    (∑ F ∈ (flex (k+2)).powersetCard h, weight k F) =
      if h=1 then 5*4^k else 2*3^k := by
  interval_cases h
  · simp [Finset.powersetCard_zero,weight_none]
  · rw [flex_one]
    simp [weight_left,weight_right,show k+2+1=k+3 by omega]
    ring
  · have hself : (flex (k+2)).powersetCard 2 = {flex (k+2)} := by
      simpa only [flex_card] using Finset.powersetCard_self (flex (k+2))
    simp [hself, weight_all]

theorem total_weight (k : ℕ) :
    (∑ p ∈ OMA.MiddleRows.choices (k+2), ∑ F ∈ flexSets (k+2) p, weight k F) =
      25*4^k + 4*3^k := by
  have inner (p : ℕ × ℕ) :
      (∑ F ∈ flexSets (k+2) p, weight k F) =
        if (removedHigh (k+2) p).card=1 then 5*4^k else 2*3^k := by
    apply weights_by_size
    exact (Finset.card_filter_le _ _).trans Finset.card_le_two
  simp_rw [inner]
  rw [OMA.MiddleRows.seven _ (by omega)]
  repeat' rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega)]
  rw [Finset.sum_singleton]
  simp only [removedHigh, Finset.filter_insert, Finset.filter_singleton]
  have h0 : ¬ k+2+2 ≤ 0 := by omega
  have h1 : ¬ k+2+2 ≤ 1 := by omega
  have ht : k+2+2 ≤ 2*(k+2) := by omega
  have hu : k+2+2 ≤ 2*(k+2)+1 := by omega
  simp [h0,h1,ht,hu]
  ring

end OMA.ColumnAllocation

namespace OMA.ColumnAllocation

open Finset OMA.NestedChoices

private theorem mir_mem {n : ℕ} {S : Finset ℕ} {x : ℕ}
    (hS : ∀ s ∈ S, s ≤ 2*n+1) :
    x ∈ S.image (mirror n) ↔ x ≤ 2*n+1 ∧ mirror n x ∈ S := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨s,hs,rfl⟩
    have hb := hS s hs
    exact ⟨by unfold mirror; omega, by simpa [mirror, Nat.sub_sub_self hb] using hs⟩
  · rintro ⟨hb,hx⟩
    exact ⟨_,hx, by unfold mirror; omega⟩

private theorem mir_card {n : ℕ} {S : Finset ℕ} (hs : ∀ x ∈ S, x ≤ 2*n+1) :
    (S.image (mirror n)).card = S.card := by
  apply card_image_of_injOn
  intro x hx y hy he
  have := hs x hx
  have := hs y hy
  unfold mirror at he
  omega

private theorem column_logic (n y : ℕ) (hn : 2 ≤ n) (hy : y ≤ 2*n+1)
    (P F : Prop) (ep : P → y ≤ 1 ∨ 2*n ≤ y ∧ y ≤ 2*n+1)
    (ef : F → y=n ∨ y=n+1) :
    (y < 2*n+2 ∧ ¬(P ∨ ((n+2 ≤ y ∧ y < 2*n+2) ∧ ¬(P ∧ n+2 ≤ y)) ∨ F)) ↔
      ((n+2 ≤ 2*n+1-y ∧ 2*n+1-y < 2*n+2) ∧ ¬(P ∧ ¬n+2 ≤ y)) ∨
      ((y=n ∨ y=n+1) ∧ ¬F) := by
  by_cases hp : P <;> by_cases hf : F <;> simp [hp, hf] at ep ef ⊢ <;> omega

/-- For a fixed middle-row assignment and its fixed flexible columns, the
outside rows split into two independent nested-row counts, related by reflection. -/
theorem outside_product (k : ℕ) (p : ℕ × ℕ) (F : Finset ℕ)
    (hp : p ∈ OMA.MiddleRows.choices (k+2)) (hF : F ∈ flexSets (k+2) p) :
    (assignments ∅ (topRows (k+2) (topCols (k+2) p F))).card *
      (assignments ∅ (bottomRows (k+2) (range (2*(k+2)+2) \ ({p.1,p.2} ∪ topCols (k+2) p F)))).card =
      weight k F := by
  let n := k+2
  change p ∈ OMA.MiddleRows.choices n at hp
  obtain ⟨hFs,hFc⟩ := Finset.mem_powersetCard.mp hF
  change F ⊆ flex n at hFs
  change F.card = (removedHigh n p).card at hFc
  have hI : ∀ {j}, j ∈ flex n ↔ j=n ∨ j=n+1 := by simp [flex]
  let P : Finset ℕ := {p.1,p.2}
  have hp' := Finset.mem_filter.mp hp
  have hne : p.1 ≠ p.2 := hp'.2.2.2
  have hp1 := (OMA.MiddleRows.first (Finset.mem_range.mp (Finset.mem_product.mp hp'.1).1)).1 hp'.2.1
  have hp2 := (OMA.MiddleRows.second (Finset.mem_range.mp (Finset.mem_product.mp hp'.1).2)).1 hp'.2.2.1
  have hends {j} (hj : j ∈ P) : j ≤ 1 ∨ (2*n ≤ j ∧ j ≤ 2*n+1) := by
    simp only [P, mem_insert, mem_singleton] at hj
    omega
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hfsub : F ⊆ Ico n (n+2) := by
    intro j hj
    have := hI.mp (hFs hj)
    apply mem_Ico.mpr; omega
  have hvsub : removedHigh n p ⊆ Ico (2*n) (2*n+2) := by
    intro j hj
    obtain ⟨hpj,hj⟩ := mem_filter.mp hj
    have := hends hpj
    apply mem_Ico.mpr; omega
  let L := P.filter (fun j => ¬ n+2 ≤ j)
  let D := flex n \ F
  let W := L.image (mirror n)
  let G := D.image (mirror n)
  let C := (high n \ W) ∪ G
  have hL {x} (hx : x ∈ L) : x ≤ 1 := by
    obtain ⟨hpj,hx⟩ := mem_filter.mp hx
    have := hends hpj; omega
  have hD {x} (hx : x ∈ D) : x=n ∨ x=n+1 := hI.mp (mem_sdiff.mp hx).1
  have lb : ∀ x ∈ L, x ≤ 2*n+1 := fun _ hx => by have := hL hx; omega
  have db : ∀ x ∈ D, x ≤ 2*n+1 := fun _ hx => by have := hD hx; omega
  have wg : W ⊆ Ico (2*n) (2*n+2) := by
    intro j hj
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hj
    have := hL hx
    apply mem_Ico.mpr; unfold mirror; omega
  have gg : G ⊆ Ico n (n+2) := by
    intro j hj
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hj
    have := hD hx
    apply mem_Ico.mpr; unfold mirror; omega
  have cb : ∀ x ∈ C, x ≤ 2*n+1 := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · have := mem_Ico.mp (mem_sdiff.mp h).1; omega
    · have := mem_Ico.mp (gg h); omega
  have hgc : G.card = D.card := mir_card db
  have hwc : W.card = L.card := mir_card lb
  have hlc : (removedHigh n p).card + L.card = 2 := by
    change (P.filter _).card + (P.filter _).card = 2
    rw [card_filter_add_card_filter_not]
    simp [P,hne]
  have hdc : D.card = 2 - F.card := by
    rw [show D = flex n \ F from rfl, card_sdiff_of_subset hFs]
    simp [flex]
  have hgsize : G.card = W.card := by omega
  have hmid : n ∈ G ↔ n+1 ∉ F := by
    change n ∈ D.image _ ↔ _
    rw [mir_mem db]
    have hr : mirror n n = n+1 := by unfold mirror; omega
    simp [hr,D,flex] <;> omega
  have eqC : range (2*n+2) \ (P ∪ topCols n p F) = C.image (mirror n) := by
    ext y
    rw [mir_mem cb]
    by_cases hy : y ≤ 2*n+1
    · have hr : mirror n (mirror n y) = y := by unfold mirror; omega
      have hrb : mirror n y ≤ 2*n+1 := by unfold mirror; omega
      simp only [mem_sdiff, mem_range, mem_union, C, high, mem_Ico,
        G, W, mir_mem db, mir_mem lb, hr, hrb, hy, true_and, D, L, mem_filter,
        topCols, removedHigh, mem_sdiff, mem_Ico, mem_union, hI]
      have hf' : y ∈ F → y=n ∨ y=n+1 := fun hyf => hI.mp (hFs hyf)
      have he' := @hends y
      change (y < 2*n+2 ∧ ¬ (y ∈ P ∨ ((n+2 ≤ y ∧ y < 2*n+2) ∧ ¬ (y ∈ P ∧ n+2 ≤ y)) ∨ y ∈ F)) ↔ _
      change (y < 2*n+2 ∧ ¬(y ∈ P ∨ ((n+2 ≤ y ∧ y < 2*n+2) ∧ ¬(y ∈ P ∧ n+2 ≤ y)) ∨ y ∈ F)) ↔
        (n+2 ≤ mirror n y ∧ mirror n y < 2*n+2) ∧ ¬(y ∈ P ∧ ¬n+2 ≤ y) ∨
        (y=n ∨ y=n+1) ∧ y ∉ F
      exact column_logic n y hn hy (y ∈ P) (y ∈ F) he' hf'
    · have hy2 : ¬ y < 2*n+2 := by omega
      simp only [mem_sdiff, mem_range, hy2, hy, false_and]
  change _ * (assignments ∅ (bottomRows n (range (2*n+2) \ (P ∪ topCols n p F)))).card = _
  rw [eqC, reflected_count n C cb]
  change (assignments ∅ (topRows (k+2) ((high (k+2) \ removedHigh n p) ∪ F))).card * (assignments ∅ (topRows (k+2) ((high (k+2) \ W) ∪ G))).card = _
  rw [flexible_count k F (removedHigh n p) hfsub hvsub hFc,
    flexible_count k G W gg wg hgsize]
  simp only [weight, hgc]
  change _ * (_ * (2 - if n ∈ G then 1 else 0)) = _
  simp only [hmid]
  rfl

end OMA.ColumnAllocation

namespace OMA.ColumnAllocation
open OMA.NestedChoices
private theorem mem_row {xs : List ℕ} {rs : List (Finset ℕ)}
    (h : List.Forall₂ (fun x r => x ∈ r) xs rs) {x : ℕ} (hx : x ∈ xs) :
    ∃ r ∈ rs, x ∈ r := by
  induction h with
  | nil => simp at hx
  | cons hab _ ih =>
    rcases List.mem_cons.mp hx with rfl | ht
    · exact ⟨_,List.mem_cons_self,hab⟩
    · obtain ⟨r,hr,hxr⟩ := ih ht
      exact ⟨r,List.mem_cons_of_mem _ hr,hxr⟩

/-- A nonempty assignment using as many rows as columns visits every column. -/
private theorem saturated {rs : List (Finset ℕ)} {T : Finset ℕ}
    (hc : rs.length = T.card) (hs : ∀ r ∈ rs, r ⊆ T)
    (hn : (assignments ∅ rs).card ≠ 0) : ∀ x ∈ T, ∃ r ∈ rs, x ∈ r := by
  obtain ⟨xs,hxs⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
  obtain ⟨hd,_,h⟩ := mem_assignments.mp hxs
  have eq : xs.toFinset = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨r,hr,hxr⟩ := mem_row h (List.mem_toFinset.mp hx)
      exact hs r hr hxr
    · rw [List.toFinset_card_of_nodup hd,h.length_eq,hc]
  intro x hx
  exact mem_row h (List.mem_toFinset.mp (eq ▸ hx))

private theorem top_support (n : ℕ) (T : Finset ℕ) (hc : T.card = n)
    (h : (assignments ∅ (topRows n T)).card ≠ 0) : ∀ x ∈ T, n ≤ x := by
  intro x hx
  obtain ⟨r,hr,hxr⟩ := saturated (rs := topRows n T) (T := T)
    (by simp [topRows,hc]) (by
      intro t ht; obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht; exact Finset.filter_subset _ _) h x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
  have hh := (Finset.mem_filter.mp hxr).2
  omega

private theorem bottom_support (n : ℕ) (T : Finset ℕ) (hc : T.card = n)
    (h : (assignments ∅ (bottomRows n T)).card ≠ 0) : ∀ x ∈ T, x ≤ n+1 := by
  intro x hx
  obtain ⟨r,hr,hxr⟩ := saturated (rs := bottomRows n T) (T := T)
    (by simp [bottomRows,hc]) (by
      intro t ht; obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht; exact Finset.filter_subset _ _) h x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
  have hh := (Finset.mem_filter.mp hxr).2
  omega

def remaining (n : ℕ) (p : ℕ × ℕ) : Finset ℕ :=
  Finset.range (2*n+2) \ {p.1,p.2}

def ways (n : ℕ) (E T : Finset ℕ) : ℕ :=
  (assignments ∅ (topRows n T)).card * (assignments ∅ (bottomRows n (E \ T))).card

theorem restrict_columns (n : ℕ) (hn : 2 ≤ n) (p : ℕ × ℕ)
    (hp : p ∈ OMA.MiddleRows.choices n) :
    ∑ T ∈ (remaining n p).powersetCard n, ways n (remaining n p) T =
    ∑ F ∈ flexSets n p, ways n (remaining n p) (topCols n p F) := by
  classical
  let E := remaining n p
  let H := Finset.Ico (n+2) (2*n+2) \ removedHigh n p
  change ∑ T ∈ E.powersetCard n, ways n E T = _
  have hpair := hp
  simp only [OMA.MiddleRows.choices,Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hpair
  obtain ⟨⟨h1,h2⟩,_,_,hne⟩ := hpair
  have out : ∀ z ∈ flex n, z ≠ p.1 ∧ z ≠ p.2 := by
    rw [OMA.MiddleRows.seven n hn] at hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      intro z hz <;> simp only [flex,Finset.mem_insert,Finset.mem_singleton] at hz <;> omega
  have pairRange : ({p.1,p.2} : Finset ℕ) ⊆ Finset.range (2*n+2) := by
    simpa [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro h1 h2
  have ce : E.card = 2*n := by
    simp [E,remaining,Finset.card_sdiff_of_subset pairRange,hne]
  have removedSub : removedHigh n p ⊆ Finset.Ico (n+2) (2*n+2) := by
    intro z hz
    simp only [removedHigh,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton] at hz
    simp only [Finset.mem_Ico]; omega
  have cH : H.card + (removedHigh n p).card = n := by
    have hi := Finset.card_le_card removedSub
    rw [Nat.card_Ico] at hi
    simp only [H,Finset.card_sdiff_of_subset removedSub,Nat.card_Ico]; omega
  have disj (F : Finset ℕ) (hf : F ⊆ flex n) : Disjoint H F := by
    apply Finset.disjoint_left.mpr
    intro z hz hzf
    have zz := hf hzf
    simp only [flex,Finset.mem_insert,Finset.mem_singleton] at zz
    have hhi := (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hz).1).1
    omega
  have proj (F : Finset ℕ) (hf : F ⊆ flex n) : topCols n p F ∩ flex n = F := by
    have hh := Finset.disjoint_left.mp (disj (flex n) (by rfl))
    ext z
    change z ∈ (H ∪ F) ∩ flex n ↔ _
    simp only [Finset.mem_inter,Finset.mem_union]
    exact ⟨fun h => h.1.resolve_left (fun hz => hh hz h.2),fun hz => ⟨Or.inr hz,hf hz⟩⟩
  let S := (flexSets n p).image (topCols n p)
  have incl : S ⊆ E.powersetCard n := by
    intro T hT
    obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hf,cf⟩ := Finset.mem_powersetCard.mp hF
    apply Finset.mem_powersetCard.mpr
    change H ∪ F ⊆ E ∧ (H ∪ F).card = n
    constructor
    · intro z hz
      rcases Finset.mem_union.mp hz with h | h
      · simp only [H,removedHigh,Finset.mem_sdiff,Finset.mem_Ico,Finset.mem_filter,
          Finset.mem_insert,Finset.mem_singleton] at h
        simp only [E,remaining,Finset.mem_sdiff,Finset.mem_range,Finset.mem_insert,Finset.mem_singleton]
        exact ⟨h.1.2, fun heq => h.2 ⟨heq,h.1.1⟩⟩
      · obtain ⟨h1',h2'⟩ := out z (hf h)
        have hflex := hf h
        simp only [flex,Finset.mem_insert,Finset.mem_singleton] at hflex
        simp only [E,remaining,Finset.mem_sdiff,Finset.mem_range,Finset.mem_insert,Finset.mem_singleton]
        omega
    · rw [Finset.card_union_of_disjoint (disj F hf),cf]; exact cH
  calc
    _ = ∑ T ∈ S, ways n E T := by
      symm
      apply Finset.sum_subset incl
      intro T hT hbad
      by_contra hne0
      have ht := Finset.mem_powersetCard.mp hT
      have cb : (E \ T).card = n := by rw [Finset.card_sdiff_of_subset ht.1,ce,ht.2]; omega
      have top := top_support n T ht.2 (left_ne_zero_of_mul hne0)
      have bot := bottom_support n (E \ T) cb (right_ne_zero_of_mul hne0)
      let F := T ∩ flex n
      have hf : F ⊆ flex n := Finset.inter_subset_right
      have eq : H ∪ F = T := by
        ext z
        simp only [Finset.mem_union]
        constructor
        · rintro (h|h)
          · by_contra hz
            have he : z ∈ E := by
              simp only [H,removedHigh,Finset.mem_sdiff,Finset.mem_Ico,Finset.mem_filter,
                Finset.mem_insert,Finset.mem_singleton] at h
              simp only [E,remaining,Finset.mem_sdiff,Finset.mem_range,Finset.mem_insert,Finset.mem_singleton]
              exact ⟨h.1.2, fun heq => h.2 ⟨heq,h.1.1⟩⟩
            have hb := bot z (Finset.mem_sdiff.mpr ⟨he,hz⟩)
            have hh := (Finset.mem_Ico.mp (Finset.mem_sdiff.mp h).1).1
            omega
          · exact (Finset.mem_inter.mp h).1
        · intro hz
          have hh := top z hz
          have he := ht.1 hz
          simp only [E,remaining,Finset.mem_sdiff,Finset.mem_range,Finset.mem_insert,Finset.mem_singleton] at he
          by_cases b : n+2 ≤ z
          · left
            simp only [H,removedHigh,Finset.mem_sdiff,Finset.mem_Ico,Finset.mem_filter,
              Finset.mem_insert,Finset.mem_singleton]; exact ⟨⟨b,he.1⟩,fun hh => he.2 hh.1⟩
          · right; apply Finset.mem_inter.mpr; refine ⟨hz,?_⟩
            simp only [flex,Finset.mem_insert,Finset.mem_singleton]; omega
      have cf := congrArg Finset.card eq
      rw [Finset.card_union_of_disjoint (disj F hf), ht.2] at cf
      exact hbad (Finset.mem_image.mpr ⟨F,Finset.mem_powersetCard.mpr ⟨hf,by omega⟩,eq⟩)
    _ = _ := by
      apply Finset.sum_image
      intro F hF G hG eq
      simpa only [proj F (Finset.mem_powersetCard.mp hF).1, proj G (Finset.mem_powersetCard.mp hG).1]
        using congrArg (fun Z => Z ∩ flex n) eq
end OMA.ColumnAllocation

namespace OMA.A183245

open OMA.NestedChoices OMA.ColumnAllocation

/-- Count the two outside halves for every pair of middle columns. -/
theorem closed_count (k : ℕ) :
    permCount (k+2) = 25*4^k + 4*3^k := by
  let n := k+2
  change permCount n = _
  rw [permCount, original_to_board, board_split]
  refine Eq.trans ?_ (total_weight k)
  apply Finset.sum_congr rfl
  intro p hp
  change ∑ T ∈ (remaining n p).powersetCard n, ways n (remaining n p) T = _
  rw [restrict_columns n (by dsimp [n]; omega) p hp]
  apply Finset.sum_congr rfl
  intro F hF
  unfold ways remaining
  have hsets (T : Finset ℕ) :
      (Finset.range (2*n+2) \ {p.1,p.2}) \ T =
        Finset.range (2*n+2) \ ({p.1,p.2} ∪ T) := by
    ext; simp; tauto
  rw [hsets]
  exact outside_product k p F hp hF

end OMA.A183245

theorem OMA.solution : type_of% @OMA.S_oeis_a183245.main :=
  OMA.A183245.reduction OMA.A183245.closed_count
