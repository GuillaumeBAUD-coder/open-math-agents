import OMAStatements.S_oeis_a183247

/-!
# The displaced permutations of OEIS A183247

For boards of size 2n+4 with n at least 4, classify the 4 middle rows by their
images, which lie among the 4 lowest and the 4 highest columns. Once the columns of
the top and bottom halves are fixed, their assignment counts factor. Nested allowed
sets make each count a product, and reflecting the board exchanges the two halves.
Summing the cases gives 85264·9^(n-4) + 28812·8^(n-4) + 48·5^(n-4).
The smaller boards are finite checks. The generating function and the recurrence
then follow by coefficient comparison.

Source: https://oeis.org/A183247
Credit: @bmendonca3
-/

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

/-- High columns in the zero-based indexing of the board with r middle rows. -/
def high (r n : ℕ) := Finset.Ico (n + r) (2 * n + r)

theorem high_filtered (r n i : ℕ) :
    ((high r n).filter fun j => n + i ≤ j).card = (2*n+r) - max (n+r) (n+i) := by
  have h : (high r n).filter (fun j => n+i ≤ j) = Finset.Ico (max (n+r) (n+i)) (2*n+r) := by
    ext x
    simp [high, and_comm]
  rw [h, Nat.card_Ico]

private def rowsOf (n m : ℕ) (C : Finset ℕ) :=
  (List.range m).reverse.map fun i => C.filter (fun j => n+i ≤ j)

private theorem rowsOf_succ (n m : ℕ) (C : Finset ℕ) : rowsOf n (m+1) C =
    (C.filter fun j => n+m ≤ j) :: rowsOf n m C := by
  simp [rowsOf, List.range_succ]

/-- The factors of the first rows, which can still reach flexible columns. -/
def lowFactors (n : ℕ) (F : Finset ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => (i + 1 - (F.filter (fun j => j < n + i)).card) * lowFactors n F i

/-- The top-row count for any choice of flexible columns. Only the number of removed
outer columns matters. -/
theorem flexible_count (r e n : ℕ) (hn : n = r + e) (F V : Finset ℕ)
    (hf : F ⊆ Finset.Ico n (n+r))
    (hv : V ⊆ Finset.Ico (2*n) (2*n+r)) (size : F.card = V.card) :
    (assignments ∅ (topRows n ((high r n \ V) ∪ F))).card =
      (r + 1 - F.card)^e * lowFactors n F r := by
  set C := (high r n \ V) ∪ F with hC
  have vsub : V ⊆ high r n := by
    intro x hx
    have hm := Finset.mem_Ico.mp (hv hx)
    apply Finset.mem_Ico.mpr
    omega
  have diss : Disjoint (high r n \ V) F := by
    apply Finset.disjoint_left.mpr
    intro x hx hxf
    have hh := Finset.mem_Ico.mp (Finset.mem_sdiff.mp hx).1
    have hm := Finset.mem_Ico.mp (hf hxf)
    omega
  have highcard : (high r n).card = n := by simp [high]; omega
  have vc : V.card ≤ n := highcard ▸ Finset.card_le_card vsub
  have cardC : C.card = n := by
    rw [hC, Finset.card_union_of_disjoint diss, Finset.card_sdiff_of_subset vsub, highcard, size]
    omega
  have early (i : ℕ) (hi : i ≤ r) :
      (C.filter (fun j => n+i ≤ j)).card = n - (F.filter (fun j => j < n+i)).card := by
    have eq : C.filter (fun j => n+i ≤ j) = C \ F.filter (fun j => j < n+i) := by
      ext x
      simp only [hC, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      have hb : x ∈ high r n → n + r ≤ x := fun h => (Finset.mem_Ico.mp h).1
      constructor
      · rintro ⟨hx, hle⟩
        exact ⟨hx, fun h => by have := h.2; omega⟩
      · rintro ⟨hx, hnot⟩
        refine ⟨hx, ?_⟩
        rcases hx with hx | hx
        · have := hb hx.1; omega
        · by_contra hlt
          exact hnot ⟨hx, by omega⟩
    have sub : F.filter (fun j => j < n+i) ⊆ C :=
      (Finset.filter_subset _ _).trans Finset.subset_union_right
    rw [eq, Finset.card_sdiff_of_subset sub, cardC]
  have late (i : ℕ) (hi : r ≤ i) (hin : i < n) :
      (C.filter (fun j => n+i ≤ j)).card = (2*n+r-(n+i)) - V.card := by
    have eq : C.filter (fun j => n+i ≤ j) =
        ((high r n).filter (fun j => n+i ≤ j)) \ V := by
      ext x
      simp only [hC, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      have bad : x ∈ F → x < n+r := fun h => (Finset.mem_Ico.mp (hf h)).2
      constructor
      · rintro ⟨hx | hx, hle⟩
        · exact ⟨⟨hx.1, hle⟩, hx.2⟩
        · have := bad hx; omega
      · rintro ⟨⟨hx, hle⟩, hv⟩
        exact ⟨Or.inl ⟨hx, hv⟩, hle⟩
    have sub : V ⊆ (high r n).filter (fun j => n+i ≤ j) := by
      intro x hx
      have hm := (Finset.mem_Ico.mp (hv hx)).1
      exact Finset.mem_filter.mpr ⟨vsub hx, by omega⟩
    rw [eq, Finset.card_sdiff_of_subset sub, high_filtered, Nat.max_eq_right (by omega)]
  have solveLow (m : ℕ) (hm : m ≤ r) :
      factors (n - m) (rowsOf n m C) = lowFactors n F m := by
    induction m with
    | zero => simp [rowsOf, factors, lowFactors]
    | succ m ih =>
      rw [rowsOf_succ, factors, early m (by omega)]
      have shift : n - (m+1) + 1 = n - m := by omega
      rw [shift, ih (by omega), lowFactors]
      congr 1
      omega
  have solveHigh (m : ℕ) (hm : r + m ≤ n) :
      factors (n - (r + m)) (rowsOf n (r + m) C) = (r+1-F.card)^m * lowFactors n F r := by
    induction m with
    | zero => simpa using solveLow r (by omega)
    | succ m ih =>
      change factors (n - (r + m + 1)) (rowsOf n (r + m + 1) C) = _
      rw [rowsOf_succ, factors, late _ (by omega) (by omega)]
      have shift : n - (r+m+1) + 1 = n - (r+m) := by omega
      rw [shift, ih (by omega)]
      have eq : 2*n+r - (n+(r+m)) - V.card - (n-(r+m+1)) = r+1-F.card := by omega
      rw [eq, pow_succ]
      ring
  rw [top_count]
  have h := solveHigh e (by omega)
  rw [show n - (r + e) = 0 by omega, ← hn] at h
  exact h

/-- Column reversal on the zero-based board with last column L. -/
def mirror (L j : ℕ) := L - j

/-- Allowed column sets for bottom rows, under the same row order after reversal. -/
def bottomRows (n L : ℕ) (B : Finset ℕ) : List (Finset ℕ) :=
  (List.range n).reverse.map fun i => B.filter (fun j => j + n + i ≤ L)

/-- Reversal preserves the number of legal assignments. -/
theorem reflected_count (n L : ℕ) (C : Finset ℕ) (bounded : ∀ j ∈ C, j ≤ L) :
    (assignments ∅ (bottomRows n L (C.image (mirror L)))).card =
    (assignments ∅ (topRows n C)).card := by
  rw [top_count]
  have nested : (bottomRows n L (C.image (mirror L))).Pairwise (· ⊆ ·) := by
    rw [bottomRows, List.pairwise_map, List.pairwise_reverse]
    apply List.pairwise_lt_range.imp
    intro i j hij c hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, by omega⟩
  rw [card_assignments _ _ nested (by simp)]
  have hcard (i : ℕ) : ((C.image (mirror L)).filter (fun j => j+n+i ≤ L)).card =
      (C.filter (fun j => n+i ≤ j)).card := by
    have heq : (C.image (mirror L)).filter (fun j => j+n+i ≤ L) =
        (C.filter (fun j => n+i ≤ j)).image (mirror L) := by
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
      factors t (rows.map fun i => (C.image (mirror L)).filter (fun j => j+n+i ≤ L)) =
      factors t (rows.map fun i => C.filter (fun j => n+i ≤ j)) by
    exact h _ _
  intro rows
  induction rows with
  | nil => simp [factors]
  | cons i rows ih =>
    intro t
    simp only [List.map_cons, factors, hcard, ih]

/-- Allowed columns of the r middle rows. -/
def mids (r n : ℕ) : List (Finset ℕ) :=
  (List.range r).map fun t => (Finset.range (2*n+r)).filter (fun j : ℕ =>
    (n : ℤ) ≤ |(j : ℤ) - ((n + t : ℕ) : ℤ)|)

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
private def rowOrder (r n : ℕ) : Equiv.Perm (Fin (2*n+r)) where
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

private def reordered (r n : ℕ) (i : Fin (2*n+r)) : Finset ℕ :=
  (Finset.range (2*n+r)).filter (fun c : ℕ => (n : ℤ) ≤ |(c : ℤ) - ((rowOrder r n i).val : ℤ)|)

private theorem reordered_rows (r n : ℕ) :
    List.ofFn (reordered r n) =
      topRows n (Finset.range (2*n+r)) ++ (mids r n ++
      bottomRows n (2*n+r-1) (Finset.range (2*n+r))) := by
  apply List.ext_getElem
  · simp [topRows,bottomRows,mids]; omega
  · intro j hj hk
    have hj' : j < 2*n+r := by simpa only [List.length_ofFn] using hj
    rw [List.getElem_ofFn]
    by_cases ht : j < n
    · rw [List.getElem_append_left (by simpa [topRows] using ht)]
      simp [topRows,List.getElem_reverse,reordered,rowOrder,ht]
      ext c
      simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
      intro _
      exact top_displacement (by omega)
    · rw [List.getElem_append_right (by simpa [topRows] using ht)]
      have hrow : ((rowOrder r n ⟨j, hj'⟩).val) = j := by simp [rowOrder, ht]
      by_cases hm : j < n + r
      · rw [List.getElem_append_left (by simp [topRows, mids]; omega)]
        simp only [mids, topRows, List.getElem_map, List.getElem_range, List.length_map,
          List.length_reverse, List.length_range, reordered, hrow]
        rw [show n + (j - n) = j by omega]
      · rw [List.getElem_append_right (by simp [topRows, mids]; omega)]
        simp only [mids, topRows, bottomRows, List.getElem_map, List.getElem_range,
          List.length_map, List.getElem_reverse,
          List.length_reverse, List.length_range, reordered, hrow]
        ext c
        simp only [Finset.mem_filter,Finset.mem_range,and_congr_right_iff]
        intro hc
        rw [le_abs']
        omega

/-- Convert the exact restricted-permutation count into the block assignment count. -/
theorem original_to_board (r n : ℕ) :
    ((Finset.univ : Finset (Equiv.Perm (Fin (2*n+r)))).filter
      (fun p => ∀ i, (n : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)).card =
    (assignments ∅ (topRows n (Finset.range (2*n+r)) ++ (mids r n ++
      bottomRows n (2*n+r-1) (Finset.range (2*n+r))))).card := by
  rw [←reordered_rows, ←natBoard_count (reordered r n) (fun i c h => Finset.mem_range.mp (Finset.mem_filter.mp h).1)]
  let e := rowOrder r n
  apply Finset.card_bij (fun (p : Equiv.Perm (Fin (2*n+r))) _ => e.trans p)
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

private theorem split2 {A B : List (Finset α)} {l : List α}
    (h : l ∈ assignments ∅ (A ++ B)) :
    ∃ x y, l = x ++ y ∧ x ∈ assignments ∅ A ∧ y ∈ assignments ∅ B := by
  obtain ⟨hn,_,hf⟩ := mem_assignments.mp h
  have hx := List.forall₂_take_append l A B hf
  have hy := List.forall₂_drop_append l A B hf
  have hn' : (l.take A.length ++ l.drop A.length).Nodup := by
    rw [List.take_append_drop]; exact hn
  have ha := List.nodup_append'.mp hn'
  exact ⟨_, _, (List.take_append_drop _ _).symm, mem_assignments.mpr ⟨ha.1, by simp, hx⟩,
    mem_assignments.mpr ⟨ha.2.1, by simp, hy⟩⟩

private theorem join2 {A B : List (Finset α)} {x y : List α}
    (hx : x ∈ assignments ∅ A) (hy : y ∈ assignments ∅ B) (hn : (x ++ y).Nodup) :
    x ++ y ∈ assignments ∅ (A ++ B) := by
  have X := mem_assignments.mp hx
  have Y := mem_assignments.mp hy
  exact mem_assignments.mpr ⟨hn, by simp, List.rel_append X.2.2 Y.2.2⟩

theorem len_assign {A : List (Finset α)} {x : List α} (hx : x ∈ assignments ∅ A) :
    x.length = A.length := (mem_assignments.mp hx).2.2.length_eq

private abbrev Packet (α : Type*) := Σ _m : List α, Σ _T : Finset α, List α × List α

private def family (U : Finset α) (Mid A B : List (Finset α)) : Finset (Packet α) :=
  (assignments ∅ Mid).sigma fun m =>
    ((U \ m.toFinset).powersetCard A.length).sigma fun T =>
      assignments ∅ (restrictRows A T) ×ˢ
        assignments ∅ (restrictRows B (U \ (m.toFinset ∪ T)))

private def joinPacket (z : Packet α) := z.2.2.1 ++ (z.1 ++ z.2.2.2)

private theorem unpack_valid {U : Finset α} {Mid A B : List (Finset α)} {l : List α}
    (au : ∀ r ∈ A, r ⊆ U) (bu : ∀ r ∈ B, r ⊆ U)
    (hl : l ∈ assignments ∅ (A ++ (Mid ++ B))) :
    ∃ z ∈ family U Mid A B, joinPacket z = l := by
  have hn := (mem_assignments.mp hl).1
  obtain ⟨x, w, rfl, hx, hw⟩ := split2 hl
  obtain ⟨m, y, rfl, hm, hy⟩ := split2 hw
  refine ⟨⟨m, x.toFinset, x, y⟩, ?_, rfl⟩
  have Hx := mem_assignments.mp hx
  have Hy := mem_assignments.mp hy
  have xu := forall_mem_cols Hx.2.2 au
  have yu := forall_mem_cols Hy.2.2 bu
  obtain ⟨_, hmy, dis⟩ := List.nodup_append'.mp hn
  obtain ⟨_, _, dis2⟩ := List.nodup_append'.mp hmy
  simp only [family, Finset.mem_sigma, Finset.mem_product, Finset.mem_powersetCard, restricted_iff]
  refine ⟨hm, ⟨?_, by rw [List.toFinset_card_of_nodup Hx.1, Hx.2.2.length_eq]⟩,
    ⟨hx, Finset.Subset.rfl⟩, hy, ?_⟩
  · intro a ha
    have hp := List.mem_toFinset.mp ha
    exact Finset.mem_sdiff.mpr ⟨xu ha,
      fun h => dis hp (List.mem_append_left _ (List.mem_toFinset.mp h))⟩
  · intro a ha
    have hp := List.mem_toFinset.mp ha
    refine Finset.mem_sdiff.mpr ⟨yu ha, ?_⟩
    simp only [Finset.mem_union, List.mem_toFinset]
    rintro (h | h)
    · exact dis2 h hp
    · exact dis h (List.mem_append_right _ hp)

private theorem pack_valid {U : Finset α} {Mid A B : List (Finset α)} {z : Packet α}
    (hz : z ∈ family U Mid A B) :
    joinPacket z ∈ assignments ∅ (A ++ (Mid ++ B)) := by
  rcases z with ⟨m,T,x,y⟩
  simp only [family, Finset.mem_sigma, Finset.mem_product, Finset.mem_powersetCard,
    restricted_iff] at hz
  obtain ⟨hm,⟨hsub,hcard⟩,⟨hx,xt⟩,hy,yt⟩ := hz
  have X := mem_assignments.mp hx
  have Y := mem_assignments.mp hy
  have Mm := mem_assignments.mp hm
  have nmy : (m ++ y).Nodup := by
    refine List.nodup_append'.mpr ⟨Mm.1, Y.1, ?_⟩
    intro a ha hb
    have H := (Finset.mem_sdiff.mp (yt (List.mem_toFinset.mpr hb))).2
    exact H (Finset.mem_union_left _ (List.mem_toFinset.mpr ha))
  have nall : (x ++ (m ++ y)).Nodup := by
    refine List.nodup_append'.mpr ⟨X.1, nmy, ?_⟩
    intro a ha hb
    have atT := xt (List.mem_toFinset.mpr ha)
    rcases List.mem_append.mp hb with hb | hb
    · exact (Finset.mem_sdiff.mp (hsub atT)).2 (List.mem_toFinset.mpr hb)
    · exact (Finset.mem_sdiff.mp (yt (List.mem_toFinset.mpr hb))).2
        (Finset.mem_union_right _ atT)
  exact join2 hx (join2 hm hy nmy) nall

private theorem injective_packet {U : Finset α} {Mid A B : List (Finset α)}
    {z w : Packet α} (hz : z ∈ family U Mid A B) (hw : w ∈ family U Mid A B)
    (eq : joinPacket z = joinPacket w) : z = w := by
  rcases z with ⟨m,T,x,y⟩
  rcases w with ⟨m',T',x',y'⟩
  simp only [family,Finset.mem_sigma,Finset.mem_product,Finset.mem_powersetCard] at hz hw
  have hx := hz.2.2.1
  have hx' := hw.2.2.1
  have lenX := len_assign (restricted_iff.mp hx).1
  have lenX' := len_assign (restricted_iff.mp hx').1
  have lenM := len_assign hz.1
  have lenM' := len_assign hw.1
  change x ++ (m ++ y) = x' ++ (m' ++ y') at eq
  obtain ⟨ex,er⟩ := List.append_inj eq (by omega)
  subst ex
  obtain ⟨em,ey⟩ := List.append_inj er (by omega)
  subst em
  subst ey
  obtain rfl : T = T' := (exact_cols hx hz.2.1.2).symm.trans (exact_cols hx' hw.2.1.2)
  rfl

theorem split_count (U : Finset α) (Mid A B : List (Finset α))
    (au : ∀ r ∈ A, r ⊆ U) (bu : ∀ r ∈ B, r ⊆ U) :
    (assignments ∅ (A ++ (Mid ++ B))).card =
      ∑ m ∈ assignments ∅ Mid,
        ∑ T ∈ (U \ m.toFinset).powersetCard A.length,
          (assignments ∅ (restrictRows A T)).card *
          (assignments ∅ (restrictRows B (U \ (m.toFinset ∪ T)))).card := by
  calc
    _ = (family U Mid A B).card := by
      symm
      exact Finset.card_bij (fun z _ => joinPacket z) (fun _ h => pack_valid h)
        (fun _ h _ h' e => injective_packet h h' e)
        (fun _ h => by obtain ⟨z,hz,e⟩ := unpack_valid au bu h; exact ⟨z,hz,e⟩)
    _ = _ := by simp [family,Finset.card_sigma]

/-- Injective relabeling of the columns commutes with listing the assignments. -/
theorem assignments_image {β : Type*} [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (used : Finset α) (rs : List (Finset α)) :
    assignments (used.image f) (rs.map (fun s => s.image f)) =
      (assignments used rs).image (List.map f) := by
  induction rs generalizing used with
  | nil => simp [assignments]
  | cons r rs ih =>
    simp only [List.map_cons, assignments]
    rw [← Finset.image_sdiff _ _ hf, Finset.image_biUnion, Finset.biUnion_image]
    congr 1
    funext x
    rw [← Finset.image_insert, ih, Finset.image_image, Finset.image_image]
    rfl

/-- Number of assignments with exactly k marked entries, as a plain sum. -/
def cnt (p : ℕ → Bool) (k : ℕ) (used : Finset ℕ) : List (Finset ℕ) → ℕ → ℕ
  | [], acc => if acc = k then 1 else 0
  | r :: rs, acc => ∑ x ∈ r \ used, cnt p k (insert x used) rs (acc + if p x then 1 else 0)

theorem cnt_eq (p : ℕ → Bool) (k : ℕ) (used : Finset ℕ) (rs : List (Finset ℕ)) (acc : ℕ) :
    ((assignments used rs).filter (fun xs => acc + (xs.filter p).length = k)).card =
      cnt p k used rs acc := by
  induction rs generalizing used acc with
  | nil =>
    by_cases h : acc = k <;> simp [assignments, cnt, Finset.filter_singleton, h]
  | cons r rs ih =>
    rw [assignments, Finset.filter_biUnion, Finset.card_biUnion]
    · rw [cnt]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.filter_image,
        Finset.card_image_of_injective _ (by intro l m h; exact (List.cons.inj h).2), ← ih]
      congr 1
      apply Finset.filter_congr
      intro ys _
      by_cases hp : p x <;> simp [List.filter_cons, hp] <;> omega
    · intro x hx y hy hxy
      apply Finset.disjoint_left.mpr
      intro l hlx hly
      obtain ⟨l₁, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hlx).1
      obtain ⟨l₂, _, he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hly).1
      exact hxy (List.cons.inj he).1.symm

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

private theorem restrict_bottom (n L : ℕ) {T U : Finset ℕ} (h : T ⊆ U) :
    restrictRows (bottomRows n L U) T = bottomRows n L T := by
  unfold restrictRows bottomRows
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  ext j
  simp only [Function.comp_apply, Finset.mem_inter, Finset.mem_filter]
  grind

theorem board_split (r n : ℕ) :
    (assignments ∅ (topRows n (Finset.range (2*n+r)) ++ (mids r n ++
      bottomRows n (2*n+r-1) (Finset.range (2*n+r))))).card =
      ∑ m ∈ assignments ∅ (mids r n),
        ∑ T ∈ (Finset.range (2*n+r) \ m.toFinset).powersetCard n,
          (assignments ∅ (topRows n T)).card *
          (assignments ∅ (bottomRows n (2*n+r-1)
            ((Finset.range (2*n+r) \ m.toFinset) \ T))).card := by
  set U := Finset.range (2*n+r)
  have au : ∀ s ∈ topRows n U, s ⊆ U := by
    intro s hs
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
    exact Finset.filter_subset _ _
  have bu : ∀ s ∈ bottomRows n (2*n+r-1) U, s ⊆ U := by
    intro s hs
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
    exact Finset.filter_subset _ _
  have eq := split_count U (mids r n) (topRows n U) (bottomRows n (2*n+r-1) U) au bu
  rw [show (topRows n U).length = n by simp [topRows]] at eq
  refine eq.trans ?_
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro T hT
  have ht := (Finset.mem_powersetCard.mp hT).1.trans Finset.sdiff_subset
  have hb : U \ (m.toFinset ∪ T) = (U \ m.toFinset) \ T := by ext; simp; tauto
  rw [restrict_top n ht, restrict_bottom n _ Finset.sdiff_subset, hb]

end OMA.NestedChoices

namespace OMA.ColumnAllocation

open Finset OMA.NestedChoices

/-- Columns usable by either half of the board. -/
def flex (r n : ℕ) : Finset ℕ := Finset.Ico n (n+r)

/-- Middle row columns on the high side. -/
def removedHigh (r n : ℕ) (P : Finset ℕ) : Finset ℕ := P.filter (fun j => n+r ≤ j)

def topCols (r n : ℕ) (P F : Finset ℕ) : Finset ℕ :=
  (Finset.Ico (n+r) (2*n+r) \ removedHigh r n P) ∪ F

/-- Flexible sets with the required number of columns. -/
def flexSets (r n : ℕ) (P : Finset ℕ) : Finset (Finset ℕ) :=
  (flex r n).powersetCard (removedHigh r n P).card

/-- The top-row count for the flexible set F. -/
def tw (r e n : ℕ) (F : Finset ℕ) : ℕ := (r + 1 - F.card)^e * lowFactors n F r

/-- The two outside-row factors after reflecting the bottom half. -/
def weight (r e n : ℕ) (F : Finset ℕ) : ℕ :=
  tw r e n F * tw r e n ((flex r n \ F).image (mirror (2*n+r-1)))

private theorem mir_mem {L : ℕ} {S : Finset ℕ} {x : ℕ}
    (hS : ∀ s ∈ S, s ≤ L) :
    x ∈ S.image (mirror L) ↔ x ≤ L ∧ mirror L x ∈ S := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨s,hs,rfl⟩
    have hb := hS s hs
    exact ⟨by unfold mirror; omega, by simpa [mirror, Nat.sub_sub_self hb] using hs⟩
  · rintro ⟨hb,hx⟩
    exact ⟨_,hx, by unfold mirror; omega⟩

private theorem mir_card {L : ℕ} {S : Finset ℕ} (hs : ∀ x ∈ S, x ≤ L) :
    (S.image (mirror L)).card = S.card := by
  apply card_image_of_injOn
  intro x hx y hy he
  have := hs x hx
  have := hs y hy
  unfold mirror at he
  omega

/-- For fixed middle columns and fixed flexible columns, the outside rows split
into two independent nested-row counts, related by reflection. -/
theorem outside_product (r e n : ℕ) (hn : n = r + e) (hr : 1 ≤ r) (P F : Finset ℕ)
    (hends : ∀ j ∈ P, j < r ∨ (2*n ≤ j ∧ j < 2*n+r)) (hPc : P.card = r)
    (hF : F ∈ flexSets r n P) :
    (assignments ∅ (topRows n (topCols r n P F))).card *
      (assignments ∅ (bottomRows n (2*n+r-1)
        (range (2*n+r) \ (P ∪ topCols r n P F)))).card =
      weight r e n F := by
  obtain ⟨hFs,hFc⟩ := Finset.mem_powersetCard.mp hF
  set L := 2*n+r-1 with hL
  have hI : ∀ {j}, j ∈ flex r n ↔ n ≤ j ∧ j < n+r := by simp [flex]
  have hfsub : F ⊆ Ico n (n+r) := hFs
  have hvsub : removedHigh r n P ⊆ Ico (2*n) (2*n+r) := by
    intro j hj
    obtain ⟨hpj,hj⟩ := mem_filter.mp hj
    have := hends j hpj
    apply mem_Ico.mpr; omega
  let Lo := P.filter (fun j => ¬ n+r ≤ j)
  let D := flex r n \ F
  let W := Lo.image (mirror L)
  let G := D.image (mirror L)
  let C := (high r n \ W) ∪ G
  have hLo {x} (hx : x ∈ Lo) : x ∈ P ∧ x < r := by
    obtain ⟨hpj,hx⟩ := mem_filter.mp hx
    have := hends x hpj
    exact ⟨hpj, by omega⟩
  have hD {x} (hx : x ∈ D) : n ≤ x ∧ x < n+r := hI.mp (mem_sdiff.mp hx).1
  have lb : ∀ x ∈ Lo, x ≤ L := fun x hx => by have := (hLo hx).2; omega
  have db : ∀ x ∈ D, x ≤ L := fun x hx => by have := hD hx; omega
  have wg : W ⊆ Ico (2*n) (2*n+r) := by
    intro j hj
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hj
    have := (hLo hx).2
    apply mem_Ico.mpr; unfold mirror; omega
  have gg : G ⊆ Ico n (n+r) := by
    intro j hj
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hj
    have := hD hx
    apply mem_Ico.mpr; unfold mirror; omega
  have cb : ∀ x ∈ C, x ≤ L := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · have := mem_Ico.mp (mem_sdiff.mp h).1; omega
    · have := mem_Ico.mp (gg h); omega
  have hgc : G.card = D.card := mir_card db
  have hwc : W.card = Lo.card := mir_card lb
  have hlc : (removedHigh r n P).card + Lo.card = r := by
    change (P.filter _).card + (P.filter _).card = r
    rw [card_filter_add_card_filter_not, hPc]
  have hFle : F.card ≤ r := by
    have := card_le_card hFs
    simpa [flex] using this
  have hdc : D.card = r - F.card := by
    rw [show D = flex r n \ F from rfl, card_sdiff_of_subset hFs]
    simp [flex]
  have hgsize : G.card = W.card := by omega
  have eqC : range (2*n+r) \ (P ∪ topCols r n P F) = C.image (mirror L) := by
    ext y
    rw [mir_mem cb]
    by_cases hy : y ≤ L
    · have hmm : mirror L (mirror L y) = y := by unfold mirror; omega
      have hrb : mirror L y ≤ L := by unfold mirror; omega
      have e1 : mirror L y ∈ W ↔ y ∈ P ∧ ¬ n+r ≤ y := by
        rw [mir_mem lb, hmm]
        simp [Lo, hrb]
      have e2 : mirror L y ∈ G ↔ (n ≤ y ∧ y < n+r) ∧ y ∉ F := by
        rw [mir_mem db, hmm]
        simp [D, hrb, hI]
      have e3 : mirror L y ∈ high r n ↔ y < n := by
        unfold mirror high
        rw [mem_Ico]
        omega
      have hf' : y ∈ F → n ≤ y ∧ y < n+r := fun hyf => hI.mp (hFs hyf)
      have he' := hends y
      have hC : mirror L y ∈ C ↔ (y < n ∧ ¬ (y ∈ P ∧ ¬ n+r ≤ y)) ∨ ((n ≤ y ∧ y < n+r) ∧ y ∉ F) := by
        simp only [C, mem_union, mem_sdiff, e1, e2, e3]
      rw [hC]
      simp only [mem_sdiff, mem_range, mem_union, topCols, removedHigh, mem_Ico, mem_filter]
      by_cases hp : y ∈ P
      · have a1 := he' hp
        by_cases hf : y ∈ F
        · have a2 := hf' hf
          simp [hp, hf] <;> omega
        · simp [hp, hf] <;> omega
      · by_cases hf : y ∈ F
        · have a2 := hf' hf
          simp [hp, hf] <;> omega
        · simp [hp, hf] <;> omega
    · have hy2 : ¬ y < 2*n+r := by omega
      simp only [mem_sdiff, mem_range, hy2, hy, false_and]
  rw [eqC, reflected_count n L C cb]
  rw [show topCols r n P F = (high r n \ removedHigh r n P) ∪ F from rfl,
    flexible_count r e n hn F (removedHigh r n P) hfsub hvsub hFc,
    flexible_count r e n hn G W gg wg hgsize]
  rfl

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

private theorem bottom_support (n L : ℕ) (T : Finset ℕ) (hc : T.card = n)
    (h : (assignments ∅ (bottomRows n L T)).card ≠ 0) : ∀ x ∈ T, x + n ≤ L := by
  intro x hx
  obtain ⟨r,hr,hxr⟩ := saturated (rs := bottomRows n L T) (T := T)
    (by simp [bottomRows,hc]) (by
      intro t ht; obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht; exact Finset.filter_subset _ _) h x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
  have hh := (Finset.mem_filter.mp hxr).2
  omega

def ways (n L : ℕ) (E T : Finset ℕ) : ℕ :=
  (assignments ∅ (topRows n T)).card * (assignments ∅ (bottomRows n L (E \ T))).card

theorem restrict_columns (r n : ℕ) (hrn : r ≤ n) (hr : 1 ≤ r) (P : Finset ℕ)
    (hends : ∀ j ∈ P, j < r ∨ (2*n ≤ j ∧ j < 2*n+r)) (hPc : P.card = r) :
    ∑ T ∈ (range (2*n+r) \ P).powersetCard n, ways n (2*n+r-1) (range (2*n+r) \ P) T =
    ∑ F ∈ flexSets r n P, ways n (2*n+r-1) (range (2*n+r) \ P) (topCols r n P F) := by
  classical
  set E := range (2*n+r) \ P with hE
  let H := Finset.Ico (n+r) (2*n+r) \ removedHigh r n P
  have memE {z : ℕ} : z ∈ E ↔ z < 2*n+r ∧ z ∉ P := by simp [hE]
  have memH {z : ℕ} : z ∈ H ↔ (n+r ≤ z ∧ z < 2*n+r) ∧ z ∉ P := by
    simp only [H, removedHigh, mem_sdiff, mem_Ico, mem_filter]
    tauto
  have memF {z : ℕ} : z ∈ flex r n ↔ n ≤ z ∧ z < n+r := by simp [flex]
  have out : ∀ z ∈ flex r n, z ∉ P := by
    intro z hz hzp
    have := memF.mp hz
    have := hends z hzp
    omega
  have pairRange : P ⊆ range (2*n+r) := by
    intro z hz
    have := hends z hz
    apply mem_range.mpr; omega
  have ce : E.card = 2*n := by
    rw [hE, card_sdiff_of_subset pairRange, card_range, hPc]; omega
  have removedSub : removedHigh r n P ⊆ Finset.Ico (n+r) (2*n+r) := by
    intro z hz
    obtain ⟨hzp, hz⟩ := mem_filter.mp hz
    have := hends z hzp
    apply mem_Ico.mpr; omega
  have cH : H.card + (removedHigh r n P).card = n := by
    have hi := Finset.card_le_card removedSub
    rw [Nat.card_Ico] at hi
    simp only [H,Finset.card_sdiff_of_subset removedSub,Nat.card_Ico]; omega
  have disj (F : Finset ℕ) (hf : F ⊆ flex r n) : Disjoint H F := by
    apply Finset.disjoint_left.mpr
    intro z hz hzf
    have zz := memF.mp (hf hzf)
    have hhi := (memH.mp hz).1
    omega
  have proj (F : Finset ℕ) (hf : F ⊆ flex r n) : topCols r n P F ∩ flex r n = F := by
    have hh := Finset.disjoint_left.mp (disj (flex r n) (by rfl))
    ext z
    change z ∈ (H ∪ F) ∩ flex r n ↔ _
    simp only [Finset.mem_inter,Finset.mem_union]
    exact ⟨fun h => h.1.resolve_left (fun hz => hh hz h.2),fun hz => ⟨Or.inr hz,hf hz⟩⟩
  let S := (flexSets r n P).image (topCols r n P)
  have incl : S ⊆ E.powersetCard n := by
    intro T hT
    obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hf,cf⟩ := Finset.mem_powersetCard.mp hF
    apply Finset.mem_powersetCard.mpr
    change H ∪ F ⊆ E ∧ (H ∪ F).card = n
    constructor
    · intro z hz
      rcases Finset.mem_union.mp hz with h | h
      · have := memH.mp h
        exact memE.mpr ⟨this.1.2, this.2⟩
      · have := memF.mp (hf h)
        exact memE.mpr ⟨by omega, out z (hf h)⟩
    · rw [Finset.card_union_of_disjoint (disj F hf),cf]; exact cH
  calc
    _ = ∑ T ∈ S, ways n (2*n+r-1) E T := by
      symm
      apply Finset.sum_subset incl
      intro T hT hbad
      by_contra hne0
      have ht := Finset.mem_powersetCard.mp hT
      have cb : (E \ T).card = n := by rw [Finset.card_sdiff_of_subset ht.1,ce,ht.2]; omega
      have top := top_support n T ht.2 (left_ne_zero_of_mul hne0)
      have bot := bottom_support n (2*n+r-1) (E \ T) cb (right_ne_zero_of_mul hne0)
      let F := T ∩ flex r n
      have hf : F ⊆ flex r n := Finset.inter_subset_right
      have eq : H ∪ F = T := by
        ext z
        simp only [Finset.mem_union]
        constructor
        · rintro (h|h)
          · by_contra hz
            have hm := memH.mp h
            have he : z ∈ E := memE.mpr ⟨hm.1.2, hm.2⟩
            have hb := bot z (Finset.mem_sdiff.mpr ⟨he,hz⟩)
            omega
          · exact (Finset.mem_inter.mp h).1
        · intro hz
          have hh := top z hz
          have he := memE.mp (ht.1 hz)
          by_cases b : n+r ≤ z
          · left
            exact memH.mpr ⟨⟨b, he.1⟩, he.2⟩
          · right
            exact Finset.mem_inter.mpr ⟨hz, memF.mpr ⟨hh, by omega⟩⟩
      have cf := congrArg Finset.card eq
      rw [Finset.card_union_of_disjoint (disj F hf), ht.2] at cf
      exact hbad (Finset.mem_image.mpr ⟨F,Finset.mem_powersetCard.mpr ⟨hf,by omega⟩,eq⟩)
    _ = _ := by
      apply Finset.sum_image
      intro F hF G hG eq
      simpa only [proj F (Finset.mem_powersetCard.mp hF).1, proj G (Finset.mem_powersetCard.mp hG).1]
        using congrArg (fun Z => Z ∩ flex r n) eq

/-- Each middle-row column is one of the r lowest or one of the r highest columns. -/
theorem mids_ends (r n : ℕ) {m : List ℕ} (hm : m ∈ assignments ∅ (mids r n)) :
    ∀ j ∈ m.toFinset, j < r ∨ (2*n ≤ j ∧ j < 2*n+r) := by
  intro j hj
  obtain ⟨s, hs, hjs⟩ := mem_row (mem_assignments.mp hm).2.2 (List.mem_toFinset.mp hj)
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  have ht' := List.mem_range.mp ht
  obtain ⟨hj1, hj2⟩ := mem_filter.mp hjs
  have hj1' := mem_range.mp hj1
  rw [le_abs'] at hj2
  push_cast at hj2
  omega

theorem mids_card (r n : ℕ) {m : List ℕ} (hm : m ∈ assignments ∅ (mids r n)) :
    m.toFinset.card = r := by
  rw [List.toFinset_card_of_nodup (mem_assignments.mp hm).1, len_assign hm]
  simp [mids]

end OMA.ColumnAllocation

namespace OMA.Displaced

open Finset OMA.NestedChoices OMA.ColumnAllocation

/-- The displacement-restricted permutations of 2n+r elements. -/
def permCount (r n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin (2 * n + r)))).filter
    (fun p => ∀ i, (n : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)).card

/-- Count the two outside halves for every choice of middle columns. -/
theorem count_as_weights (r e n : ℕ) (hn : n = r + e) (hr : 1 ≤ r) :
    permCount r n = ∑ m ∈ assignments ∅ (mids r n),
      ∑ F ∈ flexSets r n m.toFinset, weight r e n F := by
  rw [permCount, original_to_board, board_split]
  apply Finset.sum_congr rfl
  intro m hm
  have hends := mids_ends r n hm
  have hPc := mids_card r n hm
  change ∑ T ∈ (range (2*n+r) \ m.toFinset).powersetCard n,
    ways n (2*n+r-1) (range (2*n+r) \ m.toFinset) T = _
  rw [restrict_columns r n (by omega) hr m.toFinset hends hPc]
  apply Finset.sum_congr rfl
  intro F hF
  unfold ways
  have hsets (T : Finset ℕ) :
      (Finset.range (2*n+r) \ m.toFinset) \ T =
        Finset.range (2*n+r) \ (m.toFinset ∪ T) := by
    ext; simp; tauto
  rw [hsets]
  exact outside_product r e n hn hr m.toFinset F hends hPc hF

/-- The part of the weight that does not depend on n. -/
def cst (r n : ℕ) (F : Finset ℕ) : ℕ :=
  lowFactors n F r * lowFactors n ((flex r n \ F).image (mirror (2*n+r-1))) r

theorem weight_eval (r e n : ℕ) (F : Finset ℕ) (hF : F ⊆ flex r n) :
    weight r e n F = ((r + 1 - F.card) * (F.card + 1))^e * cst r n F := by
  have hFle : F.card ≤ r := by
    have := card_le_card hF
    simpa [flex] using this
  have hc : ((flex r n \ F).image (mirror (2*n+r-1))).card = r - F.card := by
    rw [card_image_of_injOn, card_sdiff_of_subset hF]
    · simp [flex]
    · intro x hx y hy he
      have hx' := mem_Ico.mp (mem_sdiff.mp (mem_coe.mp hx)).1
      have hy' := mem_Ico.mp (mem_sdiff.mp (mem_coe.mp hy)).1
      simp only [mirror] at he
      omega
  unfold weight tw cst
  rw [hc, show r + 1 - (r - F.card) = F.card + 1 by omega, mul_pow]
  ring

private theorem lowFactors_shift (n : ℕ) (F0 : Finset ℕ) (i : ℕ) :
    lowFactors n (F0.map (addRightEmbedding n)) i = lowFactors 0 F0 i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [lowFactors, lowFactors, ih, Finset.filter_map, card_map]
    congr 3
    apply Finset.filter_congr
    intro x _
    simp only [Function.comp_apply, addRightEmbedding_apply]
    omega

theorem cst_shift (r n : ℕ) (F0 : Finset ℕ) :
    cst r n (F0.map (addRightEmbedding n)) = cst r 0 F0 := by
  have h2 : (flex r n \ F0.map (addRightEmbedding n)).image (mirror (2*n+r-1)) =
      ((flex r 0 \ F0).image (mirror (2*0+r-1))).map (addRightEmbedding n) := by
    ext y
    simp only [mem_image, mem_map, mem_sdiff, flex, mem_Ico, addRightEmbedding_apply, mirror]
    constructor
    · rintro ⟨x, ⟨⟨hx1, hx2⟩, hx3⟩, rfl⟩
      refine ⟨r - 1 - (x - n), ⟨x - n, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩, by omega⟩
      intro hxF
      exact hx3 ⟨x - n, hxF, by omega⟩
    · rintro ⟨z, ⟨x, ⟨⟨hx1, hx2⟩, hx3⟩, rfl⟩, rfl⟩
      refine ⟨x + n, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      rintro ⟨a, haF, ha⟩
      have : a = x := by omega
      exact hx3 (this ▸ haF)
  unfold cst
  rw [h2, lowFactors_shift, lowFactors_shift]

/-- The constant attached to the flexible sets of size k. -/
def S (r k : ℕ) : ℕ := ∑ F0 ∈ (flex r 0).powersetCard k, cst r 0 F0

theorem flexSum (r e n k : ℕ) :
    ∑ F ∈ (flex r n).powersetCard k, weight r e n F =
      ((r + 1 - k) * (k + 1))^e * S r k := by
  have hflex : flex r n = (flex r 0).map (addRightEmbedding n) := by
    ext x
    simp only [flex, mem_map, mem_Ico, addRightEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨x - n, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨a, ⟨_, h2⟩, rfl⟩
      omega
  calc
    _ = ∑ F ∈ (flex r n).powersetCard k, ((r + 1 - k) * (k + 1))^e * cst r n F := by
      apply Finset.sum_congr rfl
      intro F hF
      obtain ⟨hs, hc⟩ := mem_powersetCard.mp hF
      rw [weight_eval r e n F hs, hc]
    _ = ((r + 1 - k) * (k + 1))^e * ∑ F ∈ (flex r n).powersetCard k, cst r n F := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [S, hflex, Finset.powersetCard_map, Finset.sum_map]
      congr 1
      apply Finset.sum_congr rfl
      intro F0 _
      exact cst_shift r n F0

/-- The normalized middle rows: the r lowest and the r highest columns only. -/
def mids0 (r : ℕ) : List (Finset ℕ) :=
  (List.range r).map fun t => (Finset.range (2*r)).filter (fun j => j ≤ t ∨ r + t ≤ j)

def phi (r n j : ℕ) : ℕ := if j < r then j else j + (2*n - r)

theorem phi_injective (r n : ℕ) (hrn : r ≤ n) : Function.Injective (phi r n) := by
  intro a b h
  unfold phi at h
  split_ifs at h <;> omega

theorem mids_eq (r n : ℕ) (hrn : r ≤ n) :
    mids r n = (mids0 r).map (fun s => s.image (phi r n)) := by
  unfold mids mids0
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  have ht' := List.mem_range.mp ht
  ext j
  simp only [mem_filter, mem_range, mem_image, Function.comp_apply]
  constructor
  · rintro ⟨hj, habs⟩
    rw [le_abs'] at habs
    push_cast at habs
    have hcase : j ≤ t ∨ 2*n+t ≤ j := by omega
    rcases hcase with h | h
    · exact ⟨j, ⟨by omega, Or.inl h⟩, by unfold phi; rw [if_pos (by omega)]⟩
    · exact ⟨j - (2*n - r), ⟨by omega, Or.inr (by omega)⟩,
        by unfold phi; rw [if_neg (by omega)]; omega⟩
  · rintro ⟨a, ⟨ha, h⟩, rfl⟩
    unfold phi
    rw [le_abs']
    split_ifs <;> push_cast <;> omega

theorem middle_sum (r n : ℕ) (hrn : r ≤ n) (g : ℕ → ℕ) :
    ∑ m ∈ assignments ∅ (mids r n), g (removedHigh r n m.toFinset).card =
      ∑ k ∈ range (r + 1),
        cnt (fun j => decide (r ≤ j)) k ∅ (mids0 r) 0 * g k := by
  have inj := phi_injective r n hrn
  have step : ∑ m ∈ assignments ∅ (mids r n), g (removedHigh r n m.toFinset).card =
      ∑ m0 ∈ assignments ∅ (mids0 r),
        g ((m0.filter (fun j => decide (r ≤ j))).length) := by
    rw [mids_eq r n hrn, ← Finset.image_empty (phi r n), assignments_image _ inj,
      Finset.sum_image (fun a _ b _ h => List.map_injective_iff.mpr inj h)]
    apply Finset.sum_congr rfl
    intro m0 hm0
    congr 1
    have nd := (mem_assignments.mp hm0).1
    have key : ∀ j, n + r ≤ phi r n j ↔ r ≤ j := by
      intro j
      unfold phi
      split_ifs <;> omega
    unfold removedHigh
    have hmap : (m0.map (phi r n)).toFinset = m0.toFinset.image (phi r n) := by
      ext j
      simp
    rw [hmap, Finset.filter_image, card_image_of_injective _ inj]
    have hset : m0.toFinset.filter (fun j => n + r ≤ phi r n j) =
        (m0.filter (fun j => decide (r ≤ j))).toFinset := by
      ext j
      simp [key]
    rw [hset, List.toFinset_card_of_nodup (nd.filter _)]
  rw [step]
  have maps : ∀ m0 ∈ assignments ∅ (mids0 r),
      (m0.filter (fun j => decide (r ≤ j))).length ∈ range (r + 1) := by
    intro m0 hm0
    have hl := len_assign hm0
    have := List.length_filter_le (fun j => decide (r ≤ j)) m0
    simp only [mids0, List.length_map, List.length_range] at hl
    apply mem_range.mpr
    omega
  rw [← Finset.sum_fiberwise_of_maps_to maps]
  apply Finset.sum_congr rfl
  intro k _
  have hc := cnt_eq (fun j => decide (r ≤ j)) k ∅ (mids0 r) 0
  simp only [zero_add] at hc
  rw [← hc, Finset.sum_congr rfl (fun m hm => by rw [(mem_filter.mp hm).2]),
    Finset.sum_const, smul_eq_mul]

/-- The count for n = r + e as a finite sum with explicit constants. -/
theorem closed (r e : ℕ) (hr : 1 ≤ r) :
    permCount r (r + e) = ∑ k ∈ range (r + 1),
      cnt (fun j => decide (r ≤ j)) k ∅ (mids0 r) 0 *
        (((r + 1 - k) * (k + 1))^e * S r k) := by
  rw [count_as_weights r e (r + e) rfl hr]
  simp only [flexSets, flexSum]
  exact middle_sum r (r + e) (by omega) (fun k => ((r + 1 - k) * (k + 1))^e * S r k)

end OMA.Displaced


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

namespace OMA.FiniteDisplacements
open OMA.NestedChoices

/-- Number of ways to assign the remaining rows injectively to unused columns. -/
def count {α : Type*} [DecidableEq α] (used : Finset α) : List (Finset α) → ℕ
  | [] => 1
  | row :: rows => ∑ j ∈ row \ used, count (insert j used) rows

theorem count_eq {α : Type*} [DecidableEq α] (used : Finset α) (rows : List (Finset α)) :
    (assignments used rows).card = count used rows := by
  induction rows generalizing used with
  | nil => simp [assignments, count]
  | cons r rs ih =>
    rw [assignments, Finset.card_biUnion]
    · unfold count
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.card_image_of_injective _ (by intro l m h; exact (List.cons.inj h).2), ih]
    · intro x hx y hy hxy
      apply Finset.disjoint_left.mpr
      intro l hlx hly
      obtain ⟨l₁, _, rfl⟩ := Finset.mem_image.mp hlx
      obtain ⟨l₂, _, he⟩ := Finset.mem_image.mp hly
      exact hxy (List.cons.inj he).1.symm

def board (m n : ℕ) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun j => (n : ℤ) ≤ |(j.val : ℤ) - (i.val : ℤ)|

theorem displacement_count (m n : ℕ) :
    ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
      (fun p => ∀ i, (n : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)).card =
    count ∅ (List.ofFn (board m n)) := by
  rw [← count_eq, ← permutation_count]
  congr 1
  ext p
  simp [board]

/-- For displacement one the permutations are the derangements. -/
theorem derangement_count (m : ℕ) :
    ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
      (fun p => ∀ i, (1 : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)).card = numDerangements m := by
  classical
  rw [← Fintype.card_coe]
  let e := Equiv.subtypeEquivRight (α := Equiv.Perm (Fin m))
    (p := fun p => p ∈ (Finset.univ.filter (fun p : Equiv.Perm (Fin m) =>
      ∀ i, (1 : ℤ) ≤ |((p i).val : ℤ) - (i.val : ℤ)|)))
    (q := fun p => p ∈ derangements (Fin m)) (fun p => by
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
  exact (Fintype.card_congr e).trans card_derangements_fin_eq_numDerangements

end OMA.FiniteDisplacements

namespace OMA.A183247
open PowerSeries OMA.NestedChoices OMA.Displaced OMA.FiniteDisplacements

theorem one : permCount 4 1 = 265 :=
  (derangement_count 6).trans (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem two : permCount 4 2 = 1708 := by
  apply (displacement_count 8 2).trans
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem three : permCount 4 3 = 13365 := by
  apply (displacement_count 10 3).trans
  decide +kernel

theorem tail (k : ℕ) :
    permCount 4 (k + 4) = 85264 * 9 ^ k + 28812 * 8 ^ k + 48 * 5 ^ k := by
  rw [Nat.add_comm k 4, closed 4 k (by norm_num)]
  have c0 : cnt (fun j => decide (4 ≤ j)) 0 ∅ (mids0 4) 0 = 1 := by decide
  have c1 : cnt (fun j => decide (4 ≤ j)) 1 ∅ (mids0 4) 0 = 49 := by decide
  have c2 : cnt (fun j => decide (4 ≤ j)) 2 ∅ (mids0 4) 0 = 146 := by decide
  have c3 : cnt (fun j => decide (4 ≤ j)) 3 ∅ (mids0 4) 0 = 49 := by decide
  have c4 : cnt (fun j => decide (4 ≤ j)) 4 ∅ (mids0 4) 0 = 1 := by decide
  have s0 : S 4 0 = 24 := by decide
  have s1 : S 4 1 = 294 := by decide
  have s2 : S 4 2 = 584 := by decide
  have s3 : S 4 3 = 294 := by decide
  have s4 : S 4 4 = 24 := by decide
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4,
    s0, s1, s2, s3, s4]
  norm_num
  ring

theorem barker_of_count (a : ℕ → ℕ) (one : a 1 = 265) (two : a 2 = 1708)
    (three : a 3 = 13365)
    (count : ∀ k : ℕ, a (k + 4) = 85264 * 9 ^ k + 28812 * 8 ^ k + 48 * 5 ^ k) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 5 * X) * (1 - 8 * X) * (1 - 9 * X)) =
      X * (265 - 4122 * X + 17394 * X ^ 2 - 7150 * X ^ 3 - 29191 * X ^ 4 - 100844 * X ^ 5) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 22 * a (n - 1) - 157 * a (n - 2) + 360 * a (n - 3)) := by
  have recurrence (k : ℕ) :
      a (k + 7) + 157 * a (k + 5) = 22 * a (k + 6) + 360 * a (k + 4) := by
    rw [count (k + 3), count k, count (k + 1), count (k + 2)]
    ring
  constructor
  · generalize hF : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = F
    have hl : F * ((1 - 5 * X) * (1 - 8 * X) * (1 - 9 * X)) =
        F - 22 • (F * X ^ 1) + 157 • (F * X ^ 2) - 360 • (F * X ^ 3) := by ring
    have hr : (X * (265 - 4122 * X + 17394 * X ^ 2 - 7150 * X ^ 3 - 29191 * X ^ 4
        - 100844 * X ^ 5) : ℚ⟦X⟧) =
        265 • X ^ 1 - 4122 • X ^ 2 + 17394 • X ^ 3 - 7150 • X ^ 4 - 29191 • X ^ 5
          - 100844 • X ^ 6 := by ring
    rw [hl, hr]
    subst hF
    ext n
    simp only [map_sub, map_add, map_nsmul, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | _ | n
    · norm_num
    · norm_num [one]
    · norm_num [one, two]
    · norm_num [one, two, three]
    · norm_num [one, two, three, count 0]
    · norm_num [one, two, three, count 0, count 1]
    · norm_num [one, two, three, count 0, count 1, count 2]
    · have h : (a (n + 7) : ℚ) + 157 * a (n + 5) = 22 * a (n + 6) + 360 * a (n + 4) := by
        exact_mod_cast recurrence n
      simp
      linear_combination h
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    have h : (a (k + 7) : ℤ) + 157 * a (k + 5) = 22 * a (k + 6) + 360 * a (k + 4) := by
      exact_mod_cast recurrence k
    simp
    linarith

end OMA.A183247

theorem OMA.solution : type_of% @OMA.S_oeis_a183247.main :=
  OMA.A183247.barker_of_count (OMA.Displaced.permCount 4) OMA.A183247.one OMA.A183247.two
    OMA.A183247.three OMA.A183247.tail
