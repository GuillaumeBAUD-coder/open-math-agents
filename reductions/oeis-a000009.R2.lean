import OMAStatements.S_oeis_a000009

/-!
# Reduction oeis-a000009.R2 of A000009 (two conjectures of Zhi-Wei Sun)

Credit: @Jwolf52

Refines R1: the representation conjecture is now proved unconditionally for every
`n ≤ 997436`, so `H1` only asks for `n > 997436`. `H2`, `H3`, `H4` are the three
non-divisibility conjectures, unchanged.

Foundations proved here (no `native_decide`; kernel evaluation only):
* `strictPartitionCount_eq_subsetCount`: `q(n)` is the number of subsets of `{1, …, n}` with
  sum `n`; `subsetCount_succ` is the recursion `Q(K+1, n) = Q(K, n) + Q(K, n - (K+1))`.
* `tbl_getD`, `strictPartitionCount_eq_rec`: a list DP (written as a `Nat.rec` term) for the
  coefficients of `∏ (1 + x^k)`; one kernel evaluation gives every `q(n)` with `n ≤ N`
  (`N = 250` takes seconds), and `mem_qList` turns list membership into `∃ m, x = q m`.
* `testBit_foldr`: subset sums of a list as one natural number (bit `s` is set iff some
  subset sums to `s`); `testBit_of_mask` checks a whole interval of bits with one identity.
* `H1_le`: the representation conjecture for `0 < n ≤ 997436`, from the 44-term seed antichain of
  note #43523 (its subset sums cover `[237, 997436]`) and 236 explicit small-case witnesses.
* `rep_of_finset`, `extend_cover` (as in R1).
-/

namespace OMA.R_oeis_a000009_R2

open OMA.S_oeis_a000009

/-- The representation conjecture beyond the proved range. -/
def H1 : Prop :=
  ∀ n : ℕ, 997436 < n → ∃ T : Finset ℕ,
    (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧
    (∑ x ∈ T, x) = n

/-- `q(n)` does not divide `p(n)` for `n > 7`. -/
def H2 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ strictPartitionCount n ∣ partitionCount n

/-- `q(n)` does not divide `p(n) - 1` for `n > 7`. -/
def H3 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ strictPartitionCount n ∣ partitionCount n - 1

/-- `q(n)` does not divide `p(n) + 1` for `n > 7`. -/
def H4 : Prop :=
  ∀ n : ℕ, 7 < n → ¬ strictPartitionCount n ∣ partitionCount n + 1

/-! ## `q(n)` as a subset count -/

/-- Distinct-part partitions of `n` are the subsets of `{1, …, n}` summing to `n`. -/
theorem strictPartitionCount_eq_subsetCount (n : ℕ) :
    strictPartitionCount n =
      ((Finset.Icc 1 n).powerset.filter (fun s => ∑ x ∈ s, x = n)).card := by
  unfold strictPartitionCount
  refine Finset.card_bij' (fun p _ => p.parts.toFinset)
    (fun s hs => ⟨s.val, fun {i} hi => by
        have := (Finset.mem_powerset.1 (Finset.mem_filter.1 hs).1) hi
        exact (Finset.mem_Icc.1 this).1,
      by simpa [Finset.sum_val] using (Finset.mem_filter.1 hs).2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    have hnd : p.parts.Nodup := (Finset.mem_filter.1 hp).2
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [Multiset.mem_toFinset] at hi
      exact Finset.mem_Icc.2 ⟨p.parts_pos hi, by
        have := Multiset.le_sum_of_mem hi; rw [p.parts_sum] at this; exact this⟩
    · rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
      simpa using p.parts_sum
  · intro s hs
    simp only [Nat.Partition.distincts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact s.nodup
  · intro p hp
    have hnd : p.parts.Nodup := (Finset.mem_filter.1 hp).2
    ext1
    simp [Multiset.dedup_eq_self.2 hnd]
  · intro s hs
    ext1
    simp

theorem subsetCount_zero (n : ℕ) :
    ((Finset.Icc 1 0).powerset.filter (fun s => ∑ x ∈ s, x = n)).card =
      if n = 0 then 1 else 0 := by
  by_cases h : n = 0 <;> simp [h, Finset.filter_singleton, eq_comm]

theorem subsetCount_succ (K n : ℕ) :
    ((Finset.Icc 1 (K + 1)).powerset.filter (fun s => ∑ x ∈ s, x = n)).card =
      ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n)).card +
        if K + 1 ≤ n then
          ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n - (K + 1))).card
        else 0 := by
  simp only [Finset.card_filter]
  have hIcc : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : K + 1 ∉ Finset.Icc 1 K := by simp
  rw [hIcc, Finset.sum_powerset_insert hnot]
  congr 1
  have key : ∀ t ∈ (Finset.Icc 1 K).powerset,
      (if ∑ x ∈ insert (K + 1) t, x = n then 1 else 0) =
        if K + 1 ≤ n then (if ∑ x ∈ t, x = n - (K + 1) then 1 else 0) else 0 := by
    intro t ht
    have hKt : K + 1 ∉ t := fun h => hnot (Finset.mem_powerset.1 ht h)
    rw [Finset.sum_insert hKt]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl key]
  split_ifs <;> simp

/-- For `n ≤ K` the bound `K` on the parts is irrelevant. -/
theorem subsetCount_of_le (n : ℕ) : ∀ K, n ≤ K →
    ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = n)).card =
      ((Finset.Icc 1 n).powerset.filter (fun s => ∑ x ∈ s, x = n)).card := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => rfl
  | succ K hK ih =>
    rw [subsetCount_succ, if_neg (by omega), add_zero, ih]

/-! ## The coefficient table of `∏ (1 + x^k)` -/

section Table

variable (N : ℕ) (t : ℕ → List ℕ) (h0 : t 0 = 1 :: List.replicate N 0)
  (hs : ∀ K, t (K + 1) = List.zipWith (· + ·) (t K) (List.replicate (K + 1) 0 ++ t K))
include h0 hs

theorem tbl_length (K : ℕ) : (t K).length = N + 1 := by
  induction K with
  | zero => simp [h0]
  | succ K ih => simp [hs, ih]

theorem tbl_getD (K : ℕ) : ∀ i ≤ N, (t K).getD i 0 =
    ((Finset.Icc 1 K).powerset.filter (fun s => ∑ x ∈ s, x = i)).card := by
  induction K with
  | zero =>
    intro i hi
    rw [subsetCount_zero]
    rcases i with _ | i
    · simp [h0]
    · simp [h0, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  | succ K ih =>
    intro i hi
    have hlen := tbl_length N t h0 hs K
    rw [subsetCount_succ, ← ih i hi]
    simp only [hs, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
    have h1 : i < (t K).length := by omega
    rw [List.getElem?_eq_getElem h1]
    by_cases hk : K + 1 ≤ i
    · rw [if_pos hk, ← ih (i - (K + 1)) (by omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by omega)]
      simp
    · rw [if_neg hk, List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
      simp [show i < K + 1 by omega]

end Table

/-- One table gives every value `q(n)` with `n ≤ N`. -/
theorem strictPartitionCount_eq_rec (N n : ℕ) (hn : n ≤ N) :
    strictPartitionCount n = (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) N).getD n 0 := by
  rw [strictPartitionCount_eq_subsetCount,
    tbl_getD N (fun K => Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) rfl (fun _ => rfl)
      N n hn,
    subsetCount_of_le n N hn]

/-- Entries `1, …, N` of the table are values of `q`. -/
theorem mem_qList {N x : ℕ} (hx : x ∈ (Nat.rec (motive := fun _ => List ℕ)
    (1 :: List.replicate N 0)
    (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) N).drop 1) :
    ∃ m, 0 < m ∧ x = strictPartitionCount m := by
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hlen := tbl_length N (fun K => Nat.rec (motive := fun _ => List ℕ)
    (1 :: List.replicate N 0)
    (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) rfl (fun _ => rfl) N
  simp only [List.length_drop] at hi
  refine ⟨i + 1, by omega, ?_⟩
  rw [strictPartitionCount_eq_rec N (i + 1) (by omega), List.getElem_drop,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp [Nat.add_comm]

/-! ## Subset sums as a bitset -/

/-- Bit `s` of `l.foldr (fun a b => b ||| b <<< a) 1` is set iff some subset of `l` sums to `s`. -/
theorem testBit_foldr (l : List ℕ) (hl : l.Nodup) (s : ℕ) :
    (l.foldr (fun a b => b ||| b <<< a) 1).testBit s = true ↔
      ∃ T ⊆ l.toFinset, ∑ x ∈ T, x = s := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldr_nil, List.toFinset_nil, Finset.subset_empty, exists_eq_left,
      Finset.sum_empty]
    rcases s with _ | s <;> simp [Nat.testBit_succ]
  | cons a l ih =>
    have ha : a ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    simp only [List.foldr_cons, Nat.testBit_lor, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, ih hl', List.toFinset_cons]
    constructor
    · rintro (⟨T, hT, hs⟩ | ⟨hsa, T, hT, hs⟩)
      · exact ⟨T, hT.trans (Finset.subset_insert _ _), hs⟩
      · have haT : a ∉ T := fun h => ha (List.mem_toFinset.1 (hT h))
        refine ⟨insert a T, Finset.insert_subset_insert _ hT, ?_⟩
        rw [Finset.sum_insert haT, hs]; omega
    · rintro ⟨T, hT, hs⟩
      by_cases haT : a ∈ T
      · right
        have hle : a ≤ ∑ x ∈ T, x :=
          Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) haT
        refine ⟨by omega, T.erase a, ?_, ?_⟩
        · intro x hx
          have hx' := Finset.mem_erase.1 hx
          rcases Finset.mem_insert.1 (hT hx'.2) with h | h
          · exact absurd h hx'.1
          · exact h
        · have := Finset.sum_erase_add T (fun x => x) haT
          omega
      · left
        refine ⟨T, fun x hx => ?_, hs⟩
        rcases Finset.mem_insert.1 (hT hx) with h | h
        · exact absurd (h ▸ hx) haT
        · exact h

/-- One big-number identity certifies that bits `L, …, L + k - 1` are all set. -/
theorem testBit_of_mask (B L k : ℕ) (h : (B >>> L) % 2 ^ k = 2 ^ k - 1) :
    ∀ s, L ≤ s → s < L + k → B.testBit s = true := by
  intro s h1 h2
  have := congrArg (fun x => x.testBit (s - L)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at this
  rw [show L + (s - L) = s by omega] at this
  simpa [show s - L < k by omega] using this

/-! ## The seed antichain of note #43523, checked by the kernel -/

theorem seed_exists : ∃ seed : List ℕ, seed.Nodup ∧
    (∀ x ∈ seed, x ∈ (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 90 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) 90).drop 1) ∧
    (∀ x ∈ seed, ∀ y ∈ seed, x ≠ y → y % x ≠ 0) ∧
    ((seed.foldr (fun a b => b ||| b <<< a) 1) >>> 237) % 2 ^ 997200 = 2 ^ 997200 - 1 :=
  ⟨[18, 22, 27, 32, 38, 46, 89, 104, 122, 142, 165, 222, 296, 340, 390, 585, 668,
    982, 1113, 1816, 2590, 2910, 3658, 4097, 4582, 5718, 6378, 7108, 7917, 8808, 12076, 13394,
    16444, 20132, 27130, 29927, 48446, 58499, 64234, 84756, 101698, 111322, 159046, 189586],
    by decide +kernel⟩

/-! ## Small cases, checked by the kernel -/

theorem small_exists : ∃ W : List (List ℕ), ∀ i < 236, ((W.getD i []).sum = i + 1 ∧
    (W.getD i []).Nodup ∧
    (∀ x ∈ W.getD i [], x ∈ (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 28 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) 28).drop 1) ∧
    ∀ x ∈ W.getD i [], ∀ y ∈ W.getD i [], x ≠ y → y % x ≠ 0) :=
  ⟨[[1], [2], [3], [4], [5], [6], [5, 2], [8], [5, 4], [10], [8, 3], [12], [10, 3], [10, 4], [15],
    [10, 6], [15, 2], [18], [15, 4], [12, 8], [15, 6], [22], [18, 5], [10, 8, 6], [22, 3], [22, 4],
    [27], [22, 6], [27, 2], [22, 8], [27, 4], [32], [27, 6], [27, 5, 2], [32, 3], [27, 5, 4],
    [32, 5], [38], [27, 12], [32, 5, 3], [38, 3], [38, 4], [38, 5], [38, 6], [38, 4, 3], [46],
    [38, 5, 4], [38, 10], [46, 3], [46, 4], [46, 5], [46, 6], [46, 4, 3], [54], [46, 5, 4],
    [46, 10], [46, 8, 3], [54, 4], [54, 5], [46, 10, 4], [46, 15], [54, 8], [54, 5, 4], [64],
    [46, 15, 4], [54, 12], [64, 3], [54, 10, 4], [64, 5], [64, 6], [54, 12, 5], [64, 5, 3],
    [54, 15, 4], [64, 10], [64, 6, 5], [76], [64, 10, 3], [46, 32], [76, 3], [64, 10, 6], [76, 5],
    [76, 6], [54, 15, 10, 4], [76, 8], [64, 15, 6], [76, 10], [76, 8, 3], [76, 12], [89],
    [76, 8, 6], [89, 2], [89, 3], [89, 4], [89, 5], [89, 6], [89, 5, 2], [89, 8], [89, 5, 4],
    [89, 10], [89, 8, 3], [89, 12], [89, 10, 3], [89, 10, 4], [104], [89, 10, 6], [89, 15, 2],
    [104, 3], [89, 15, 4], [104, 5], [104, 6], [89, 22], [104, 5, 3], [89, 10, 8, 6], [104, 10],
    [104, 6, 5], [104, 12], [104, 10, 3], [89, 27, 2], [104, 15], [104, 10, 6], [104, 12, 5],
    [122], [89, 27, 5, 2], [89, 32, 3], [122, 3], [122, 4], [122, 5], [122, 6], [122, 4, 3],
    [122, 8], [122, 5, 4], [122, 10], [122, 8, 3], [122, 12], [122, 10, 3], [122, 10, 4],
    [122, 15], [122, 10, 6], [122, 12, 5], [122, 18], [122, 15, 4], [142], [122, 15, 6],
    [122, 22], [142, 3], [142, 4], [142, 5], [142, 6], [142, 4, 3], [142, 8], [142, 5, 4],
    [142, 10], [142, 8, 3], [142, 12], [142, 10, 3], [142, 10, 4], [142, 15], [142, 10, 6],
    [142, 12, 5], [142, 18], [142, 15, 4], [142, 12, 8], [142, 15, 6], [142, 22], [165],
    [142, 10, 8, 6], [165, 2], [142, 22, 4], [165, 4], [142, 22, 6], [165, 6], [142, 22, 8],
    [165, 8], [142, 32], [165, 10], [142, 22, 12], [165, 12], [142, 27, 5, 4], [165, 10, 4],
    [142, 38], [165, 10, 6], [142, 32, 5, 3], [165, 18], [142, 38, 4], [165, 12, 8], [142, 38, 6],
    [165, 22], [142, 46], [165, 10, 8, 6], [142, 38, 10], [165, 22, 4], [192], [165, 22, 6],
    [165, 27, 2], [165, 22, 8], [165, 27, 4], [192, 5], [165, 27, 6], [165, 22, 12], [165, 27, 8],
    [165, 22, 10, 4], [192, 10], [165, 38], [165, 27, 12], [165, 22, 18], [165, 27, 10, 4],
    [192, 15], [165, 27, 10, 6], [165, 38, 6], [192, 18], [165, 46], [165, 27, 12, 8],
    [165, 38, 10], [192, 22], [192, 18, 5], [165, 27, 10, 8, 6], [192, 15, 10], [165, 27, 22, 4],
    [192, 27], [192, 18, 10], [165, 46, 10], [222], [165, 54, 4], [192, 27, 5], [192, 18, 15],
    [222, 4], [222, 5], [165, 27, 22, 10, 4], [192, 27, 10], [222, 8], [222, 5, 4], [222, 10],
    [165, 54, 10, 4], [222, 12], [222, 8, 5], [222, 10, 4]],
    by decide +kernel⟩

/-! ## The representation conjecture below one million -/

theorem H1_le (n : ℕ) (hn : 0 < n) (hle : n ≤ 997436) : ∃ T : Finset ℕ,
    (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧
    (∑ x ∈ T, x) = n := by
  by_cases hs : n < 237
  · obtain ⟨W, hW⟩ := small_exists
    obtain ⟨hsum, hnd, hq, han⟩ := hW (n - 1) (by omega)
    refine ⟨(W.getD (n - 1) []).toFinset, ?_, ?_, ?_⟩
    · intro x hx; exact mem_qList (N := 28) (hq x (List.mem_toFinset.1 hx))
    · intro x hx y hy hxy hd
      exact han x (List.mem_toFinset.1 hx) y (List.mem_toFinset.1 hy) hxy
        (Nat.mod_eq_zero_of_dvd hd)
    · rw [List.sum_toFinset _ hnd, List.map_id', hsum]; omega
  · obtain ⟨seed, hnd, hq, han, hmask⟩ := seed_exists
    have hb := testBit_of_mask _ _ _ hmask n (by omega) (by omega)
    obtain ⟨T, hT, hsum⟩ := (testBit_foldr seed hnd n).1 hb
    refine ⟨T, ?_, ?_, hsum⟩
    · intro x hx; exact mem_qList (N := 90) (hq x (List.mem_toFinset.1 (hT hx)))
    · intro x hx y hy hxy hd
      exact han x (List.mem_toFinset.1 (hT hx)) y (List.mem_toFinset.1 (hT hy)) hxy
        (Nat.mod_eq_zero_of_dvd hd)

/-! ## From sets to the target's form, and the greedy step -/

theorem rep_of_finset (T : Finset ℕ)
    (hq : ∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m)
    (hanti : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) :
    ∃ k : ℕ, ∃ terms : Fin k → ℕ,
      (∀ i, ∃ m : ℕ, 0 < m ∧ terms i = strictPartitionCount m) ∧
      (∑ i, terms i) = ∑ x ∈ T, x ∧
      (∀ i j, i ≠ j → ¬ terms i ∣ terms j) := by
  let e : T ≃ Fin T.card := T.equivFin
  refine ⟨T.card, fun i => (e.symm i : ℕ), ?_, ?_, ?_⟩
  · intro i
    exact hq _ (e.symm i).2
  · rw [Equiv.sum_comp e.symm (fun x : T => (x : ℕ))]
    exact Finset.sum_coe_sort T (fun x => x)
  · intro i j hij
    apply hanti _ (e.symm i).2 _ (e.symm j).2
    intro h
    exact hij (e.symm.injective (Subtype.ext h))

/-- The greedy extension step: adding a new element `a ≤ U + 1 - L` to a set whose subset
sums cover `[L, U]` yields a set whose subset sums cover `[L, U + a]`. -/
theorem extend_cover (S : Finset ℕ) (a L U : ℕ) (ha : a ∉ S)
    (hcov : ∀ n, L ≤ n → n ≤ U → ∃ T ⊆ S, (∑ x ∈ T, x) = n)
    (hle : a ≤ U + 1 - L) :
    ∀ n, L ≤ n → n ≤ U + a → ∃ T ⊆ insert a S, (∑ x ∈ T, x) = n := by
  intro n hLn hnU
  by_cases h : n ≤ U
  · obtain ⟨T, hT, hs⟩ := hcov n hLn h
    exact ⟨T, hT.trans (Finset.subset_insert a S), hs⟩
  · rw [not_le] at h
    obtain ⟨T, hT, hs⟩ := hcov (n - a) (by omega) (by omega)
    have haT : a ∉ T := fun h' => ha (hT h')
    refine ⟨insert a T, Finset.insert_subset_insert a hT, ?_⟩
    rw [Finset.sum_insert haT, hs]
    omega

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a000009.main := by
  intro h1 h2 h3 h4
  refine ⟨?_, fun n hn => ⟨h2 n hn, h3 n hn, h4 n hn⟩⟩
  intro n hn
  obtain ⟨T, hq, hanti, hsum⟩ : ∃ T : Finset ℕ,
      (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ x ∈ T, x) = n := by
    by_cases hb : n ≤ 997436
    · exact H1_le n hn hb
    · exact h1 n (by omega)
  obtain ⟨k, terms, hterms, hs, hdiv⟩ := rep_of_finset T hq hanti
  exact ⟨k, terms, hterms, hs.trans hsum, hdiv⟩

end OMA.R_oeis_a000009_R2
