import OMAStatements.S_oeis_a000009

/-!
# Reduction oeis-a000009.R4 of A000009 (two conjectures of Zhi-Wei Sun)

Credit: @Jwolf52

Combines R2 (the representation conjecture, proved for `n ≤ 997436`) with new results on the
three non-divisibility conjectures, and leaves three open steps:

* `H1`: the representation conjecture for `n > 997436` (as in R2).
* `H2`, `H3`: the three non-divisibility conjectures, for `n > 100`, in a reduced form.
  For `n > 7`, `q(n) ≥ 3`, so `q(n)` divides at most one of `p(n) - 1, p(n), p(n) + 1`
  (`at_most_one`). Together they say `2 ≤ p(n) % q(n) ≤ q(n) - 2` (`three_iff_mod`).
  `q(n)` is odd exactly when `n` is a generalized pentagonal number
  (`strictPartitionCount_odd_iff`, from Mathlib's pentagonal number theorem reduced mod 2).
  When `q(n)` is even, the parity of `p(n)` settles two of the three claims (`parity_split`).
  So only pentagonal `n` need the full condition, and every other `n` needs one claim.

Proved unconditionally here (no `native_decide`; kernel evaluation only):
* everything in R2: the `q`-table, the subset-sum bitset, `H1_le`, `rep_of_finset`, `extend_cover`;
* `partitionCount_eq_rec`: `p(n)` equals entry `n` of a list DP, through the recursion
  `c(K+1, n) = c(K, n) + c(K+1, n - (K+1))` for partitions with parts `≤ K`
  (`bounded_succ`, via Mathlib's `partitionWithPartEquiv`);
* `nondiv_le`: `q(n)` divides none of `p(n), p(n) - 1, p(n) + 1` for `8 ≤ n ≤ 100`;
* `three_iff_mod`, `at_most_one`, `parity_split`, `strictPartitionCount_odd_iff`, `H234_of_pentagonal`.
-/

namespace OMA.R_oeis_a000009_R4

open OMA.S_oeis_a000009

/-- The representation conjecture beyond the proved range. -/
def H1 : Prop :=
  ∀ n : ℕ, 997436 < n → ∃ T : Finset ℕ,
    (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧
    (∑ x ∈ T, x) = n

/-- `q(n) ∤ p(n)`, needed only when `n` is pentagonal or `p(n)` is even. -/
def H2 : Prop :=
  ∀ n : ℕ, 100 < n → (n ∈ Set.range pentagonal ∨ partitionCount n % 2 = 0) →
    ¬ strictPartitionCount n ∣ partitionCount n

/-- `2 ≤ p(n) % q(n) ≤ q(n) - 2`, needed only when `n` is pentagonal or `p(n)` is odd. -/
def H3 : Prop :=
  ∀ n : ℕ, 100 < n → (n ∈ Set.range pentagonal ∨ partitionCount n % 2 = 1) →
    2 ≤ partitionCount n % strictPartitionCount n ∧
      partitionCount n % strictPartitionCount n + 2 ≤ strictPartitionCount n

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

/-! ## `p(n)` as a table -/

/-- Partitions of `n` with every part at most `K`. -/
theorem pc_le_card (n : ℕ) : ∀ p : n.Partition, ∀ i ∈ p.parts, i ≤ n := by
  intro p i hi
  have := Multiset.le_sum_of_mem hi
  rw [p.parts_sum] at this
  exact this

theorem partitionCount_eq_bounded (n : ℕ) :
    partitionCount n = (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ n)).card := by
  unfold partitionCount
  rw [Finset.filter_true_of_mem (fun p _ => pc_le_card n p), Finset.card_univ]

theorem bounded_zero (n : ℕ) :
    (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ 0)).card =
      if n = 0 then 1 else 0 := by
  have key : ∀ p : n.Partition, (∀ i ∈ p.parts, i ≤ 0) ↔ p.parts = 0 := by
    intro p
    constructor
    · intro h
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro i hi
      have := p.parts_pos hi
      have := h i hi
      omega
    · intro h i hi
      rw [h] at hi
      simp at hi
  simp only [key]
  split_ifs with hn
  · subst hn
    rw [Finset.card_eq_one]
    refine ⟨Nat.Partition.indiscrete 0, ?_⟩
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _; exact Subsingleton.elim _ _
    · intro _
      have := p.parts_sum
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro i hi
      have h1 := p.parts_pos hi
      have h2 := Multiset.le_sum_of_mem hi
      omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    have := p.parts_sum
    rw [hp] at this
    simp at this
    omega

theorem bounded_succ (K n : ℕ) :
    (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K + 1)).card =
      (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K)).card +
        if K + 1 ≤ n then
          (Finset.univ.filter (fun p : (n - (K + 1)).Partition => ∀ i ∈ p.parts, i ≤ K + 1)).card
        else 0 := by
  rw [← Finset.card_filter_add_card_filter_not (fun p : n.Partition => K + 1 ∈ p.parts),
    Finset.filter_filter, Finset.filter_filter, add_comm]
  congr 1
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hK⟩ i hi
      have := h i hi
      have : i ≠ K + 1 := fun e => hK (e ▸ hi)
      omega
    · intro h
      exact ⟨fun i hi => by have := h i hi; omega, fun hm => by have := h _ hm; omega⟩
  · split_ifs with hn
    · refine Finset.card_bij'
        (fun p hp => Nat.Partition.partitionWithPartEquiv (by omega) hn
          ⟨p, (Finset.mem_filter.1 hp).2.2⟩)
        (fun q _ => ((Nat.Partition.partitionWithPartEquiv (n := n) (a := K + 1)
          (by omega) hn).symm q).1) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        intro i hi
        rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at hi
        exact hp.1 i (Multiset.mem_of_mem_erase hi)
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts]
        refine ⟨fun i hi => ?_, Multiset.mem_cons_self _ _⟩
        rcases Multiset.mem_cons.1 hi with h | h
        · omega
        · exact hq i h
      · intro p hp
        simp
      · intro q hq
        simp
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro p _ ⟨_, hm⟩
      have := pc_le_card n p _ hm
      omega


theorem bounded_of_le (n : ℕ) : ∀ K, n ≤ K →
    (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ K)).card =
      (Finset.univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, i ≤ n)).card := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => rfl
  | succ K hK ih => rw [bounded_succ, if_neg (by omega), add_zero, ih]

/-- The reversed scan computing `new i = old i + new (i - (k+1))`. -/
theorem scan_spec (N k : ℕ) (old : List ℕ) (f : ℕ → ℕ)
    (hf : ∀ i ≤ N, f i = old.getD i 0 + if k + 1 ≤ i then f (i - (k + 1)) else 0) :
    ∀ m ≤ N + 1, (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) m).length = m ∧
      ∀ j < m, (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) m).getD j 0 =
        f (m - 1 - j) := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hlen, hget⟩ := ih (by omega)
    refine ⟨congrArg Nat.succ hlen, ?_⟩
    intro j hj
    rcases j with _ | j
    · show List.getD (_ :: _) 0 0 = _
      rw [List.getD_cons_zero, show m + 1 - 1 - 0 = m by omega, hf m (by omega)]
      congr 1
      split_ifs with h
      · rw [hget k (by omega)]; congr 1; omega
      · rfl
    · show List.getD (_ :: _) (j + 1) 0 = _
      rw [List.getD_cons_succ, hget j (by omega)]
      congr 1; omega

theorem getD_reverse_of_lt (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    l.reverse.getD i 0 = l.getD (l.length - 1 - i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse hi]

theorem scan_rev (N k : ℕ) (old : List ℕ) (f : ℕ → ℕ)
    (hf : ∀ i ≤ N, f i = old.getD i 0 + if k + 1 ≤ i then f (i - (k + 1)) else 0) :
    ∀ i ≤ N, (Nat.rec (motive := fun _ => List ℕ) []
      (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse.getD
        i 0 = f i := by
  intro i hi
  obtain ⟨hlen, hget⟩ := scan_spec N k old f hf (N + 1) le_rfl
  rw [getD_reverse_of_lt _ i (by omega), hlen, hget _ (by omega)]
  congr 1; omega

/-- Row `K` of the table holds the number of partitions of `i` with parts `≤ K`. -/
theorem prow_spec (N : ℕ) (K : ℕ) :
    (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      K).length = N + 1 ∧
    ∀ i ≤ N, (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      K).getD i 0 =
      (Finset.univ.filter (fun p : i.Partition => ∀ j ∈ p.parts, j ≤ K)).card := by
  induction K with
  | zero =>
    refine ⟨by simp, fun i hi => ?_⟩
    rw [bounded_zero]
    rcases i with _ | i
    · simp
    · simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  | succ K ih =>
    obtain ⟨_, hrow⟩ := ih
    have hf : ∀ i ≤ N,
        (Finset.univ.filter (fun p : i.Partition => ∀ j ∈ p.parts, j ≤ K + 1)).card =
          (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
            (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
              (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r)
                (N + 1)).reverse) K).getD i 0 +
          if K + 1 ≤ i then
            (Finset.univ.filter (fun p : (i - (K + 1)).Partition => ∀ j ∈ p.parts, j ≤ K + 1)).card
          else 0 := by
      intro i hi
      rw [hrow i hi, bounded_succ]
    obtain ⟨hlen, _⟩ := scan_spec N K _ _ hf (N + 1) le_rfl
    exact ⟨by simp only [List.length_reverse]; exact hlen, scan_rev N K _ _ hf⟩

/-- One table gives every value `p(n)` with `n ≤ N`. -/
theorem partitionCount_eq_rec (N n : ℕ) (hn : n ≤ N) :
    partitionCount n = (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate N 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (N + 1)).reverse)
      N).getD n 0 := by
  rw [(prow_spec N N).2 n hn, bounded_of_le n N hn, ← partitionCount_eq_bounded]

/-! ## Step 2: the three non-divisibility claims are one statement about `P % Q` -/

theorem succ_mod_of_lt (x Q : ℕ) (hx : x < Q) : (x + 1) % Q = if x + 1 = Q then 0 else x + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- For `Q ≥ 3` and `P ≥ 1`: `Q` divides none of `P - 1, P, P + 1` iff `2 ≤ P % Q ≤ Q - 2`. -/
theorem three_iff_mod (P Q : ℕ) (hP : 1 ≤ P) (hQ : 3 ≤ Q) :
    (¬ Q ∣ P ∧ ¬ Q ∣ P - 1 ∧ ¬ Q ∣ P + 1) ↔ (2 ≤ P % Q ∧ P % Q + 2 ≤ Q) := by
  simp only [Nat.dvd_iff_mod_eq_zero]
  have hr : P % Q < Q := Nat.mod_lt _ (by omega)
  have hs : (P - 1) % Q < Q := Nat.mod_lt _ (by omega)
  have h1 : P % Q = ((P - 1) % Q + 1) % Q := by
    conv_lhs => rw [show P = (P - 1) + 1 by omega]
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < Q by omega)]
  have h2 : (P + 1) % Q = (P % Q + 1) % Q := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < Q by omega)]
  rw [succ_mod_of_lt _ _ hs] at h1
  rw [succ_mod_of_lt _ _ hr] at h2
  split_ifs at h1 h2 <;> omega

/-- At most one of the three divisibilities can hold (for `Q ≥ 3`). -/
theorem at_most_one (P Q : ℕ) (hP : 1 ≤ P) (hQ : 3 ≤ Q) :
    (Q ∣ P → ¬ Q ∣ P - 1 ∧ ¬ Q ∣ P + 1) ∧ (Q ∣ P - 1 → ¬ Q ∣ P + 1) := by
  refine ⟨fun h => ⟨fun h' => ?_, fun h' => ?_⟩, fun h h' => ?_⟩
  · have := Nat.dvd_sub h h'; rw [show P - (P - 1) = 1 by omega] at this
    exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  · have := Nat.dvd_sub h' h; rw [show P + 1 - P = 1 by omega] at this
    exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  · have := Nat.dvd_sub h' h; rw [show P + 1 - (P - 1) = 2 by omega] at this
    exact absurd (Nat.le_of_dvd two_pos this) (by omega)

/-! ## Step 3: the parity split -/

/-- If `Q` is even, the parity of `P` rules out either `Q ∣ P` or both `Q ∣ P ∓ 1`. -/
theorem parity_split (P Q : ℕ) (hP : 1 ≤ P) (hQ : 2 ∣ Q) :
    (P % 2 = 1 → ¬ Q ∣ P) ∧ (P % 2 = 0 → ¬ Q ∣ P - 1 ∧ ¬ Q ∣ P + 1) := by
  refine ⟨fun h hd => ?_, fun h => ⟨fun hd => ?_, fun hd => ?_⟩⟩
  · have := Nat.mod_eq_zero_of_dvd (hQ.trans hd); omega
  · have := Nat.mod_eq_zero_of_dvd (hQ.trans hd); omega
  · have := Nat.mod_eq_zero_of_dvd (hQ.trans hd); omega

/-! ## Side facts: `p(n) ≥ 1`, `q(n) ≥ 3` for `n ≥ 5` -/

theorem partitionCount_pos (n : ℕ) : 1 ≤ partitionCount n :=
  Fintype.card_pos_iff.2 ⟨Nat.Partition.indiscrete n⟩

theorem three_le_strictPartitionCount (n : ℕ) (hn : 5 ≤ n) : 3 ≤ strictPartitionCount n := by
  rw [strictPartitionCount_eq_subsetCount]
  have hsub : ({{n}, {1, n - 1}, {2, n - 2}} : Finset (Finset ℕ)) ⊆
      (Finset.Icc 1 n).powerset.filter (fun s => ∑ x ∈ s, x = n) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    simp only [Finset.mem_filter, Finset.mem_powerset]
    rcases hs with rfl | rfl | rfl
    · exact ⟨by intro x hx; simp at hx; simp [hx]; omega, by simp⟩
    · refine ⟨by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp <;> omega, ?_⟩
      rw [Finset.sum_pair (by omega)]; omega
    · refine ⟨by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp <;> omega, ?_⟩
      rw [Finset.sum_pair (by omega)]; omega
  have hcard : ({{n}, {1, n - 1}, {2, n - 2}} : Finset (Finset ℕ)).card = 3 := by
    have a1 : ({n} : Finset ℕ) ≠ {1, n - 1} := by
      intro h; have := congrArg Finset.card h
      rw [Finset.card_singleton, Finset.card_pair (by omega)] at this; omega
    have a2 : ({n} : Finset ℕ) ≠ {2, n - 2} := by
      intro h; have := congrArg Finset.card h
      rw [Finset.card_singleton, Finset.card_pair (by omega)] at this; omega
    have a3 : ({1, n - 1} : Finset ℕ) ≠ {2, n - 2} := by
      intro h; have : (1 : ℕ) ∈ ({2, n - 2} : Finset ℕ) := h ▸ by simp
      simp at this; omega
    rw [Finset.card_insert_of_notMem (by simp [a1, a2]), Finset.card_pair a3]
  exact hcard ▸ Finset.card_le_card hsub


/-! ## Step 4: `q(n)` is odd iff `n` is a generalized pentagonal number -/

open PowerSeries PowerSeries.WithPiTopology in
/-- 4b: in characteristic 2, `1 + X^k = 1 - X^k`. -/
theorem one_add_X_pow_eq_one_sub (k : ℕ) :
    (1 + X ^ k : (ZMod 2)⟦X⟧) = 1 - X ^ k := by
  ext m
  simp only [map_add, map_sub, coeff_one, coeff_X_pow]
  split_ifs <;> decide

open PowerSeries PowerSeries.WithPiTopology in
/-- 4a–4e: `q(n)` is odd iff `n` is a generalized pentagonal number. -/
theorem strictPartitionCount_odd_iff (n : ℕ) :
    strictPartitionCount n % 2 = 1 ↔ n ∈ Set.range pentagonal := by
  let _ : TopologicalSpace (ZMod 2) := ⊥
  have _ : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  have h1 := Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod 2) (m := 2) two_pos
  have hfac : (fun i : ℕ => ∑ j ∈ Finset.range 2, (X : (ZMod 2)⟦X⟧) ^ ((i + 1) * j)) =
      fun i => 1 - X ^ (i + 1) := by
    funext i
    rw [Finset.sum_range_succ, Finset.sum_range_one, mul_zero, pow_zero, mul_one,
      one_add_X_pow_eq_one_sub]
  rw [hfac] at h1
  have heq := h1.unique (hasProd_one_sub_X_pow (ZMod 2))
  have hc := congrArg (PowerSeries.coeff n) heq
  rw [PowerSeries.coeff_mk, Nat.Partition.countRestricted_two] at hc
  have key : ((strictPartitionCount n : ℕ) : ZMod 2) = 0 ↔ n ∉ Set.range pentagonal := by
    rw [← coeff_pentagonalSeries_eq_zero_iff (R := ZMod 2), ← hc]
    rfl
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at key
  constructor
  · intro h
    by_contra hn
    have := key.2 hn
    omega
  · intro hn
    by_contra h
    exact (key.1 (by omega)) hn

/-! ## The finite range `8 ≤ n ≤ 100`, checked by the kernel -/

theorem nondiv_check :
    ((List.zip (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 100 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) 100)
      (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 100 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (100 + 1)).reverse)
      100)).drop 8).all
      (fun x => x.2 % x.1 != 0 && (x.2 - 1) % x.1 != 0 && (x.2 + 1) % x.1 != 0) = true := by
  decide +kernel

theorem nondiv_le (n : ℕ) (h7 : 7 < n) (hn : n ≤ 100) :
    ¬ strictPartitionCount n ∣ partitionCount n ∧
    ¬ strictPartitionCount n ∣ partitionCount n - 1 ∧
    ¬ strictPartitionCount n ∣ partitionCount n + 1 := by
  rw [strictPartitionCount_eq_rec 100 n hn, partitionCount_eq_rec 100 n hn]
  have hc := nondiv_check
  have hQl := tbl_length 100 (fun K => Nat.rec (motive := fun _ => List ℕ)
    (1 :: List.replicate 100 0)
    (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) K) rfl (fun _ => rfl) 100
  have hPl := (prow_spec 100 100).1
  generalize (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 100 0)
      (fun k l => List.zipWith (· + ·) l (List.replicate (k + 1) 0 ++ l)) 100) = Q at hc hQl ⊢
  generalize (Nat.rec (motive := fun _ => List ℕ) (1 :: List.replicate 100 0)
      (fun k old => (Nat.rec (motive := fun _ => List ℕ) []
        (fun i r => (old.getD i 0 + if k + 1 ≤ i then r.getD k 0 else 0) :: r) (100 + 1)).reverse)
      100) = P at hc hPl ⊢
  rw [List.all_eq_true] at hc
  have hmem : (Q[n]'(by omega), P[n]'(by omega)) ∈ (List.zip Q P).drop 8 := by
    apply List.mem_of_getElem? (i := n - 8)
    rw [List.getElem?_drop, show 8 + (n - 8) = n by omega, List.getElem?_zip_eq_some]
    exact ⟨List.getElem?_eq_getElem _, List.getElem?_eq_getElem _⟩
  have := hc _ hmem
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < Q.length by omega),
    List.getElem?_eq_getElem (show n < P.length by omega), Option.getD_some,
    Nat.dvd_iff_mod_eq_zero]
  exact ⟨this.1.1, this.1.2, this.2⟩

/-! ## The pentagonal form of the three non-divisibility conjectures -/

/-- Beyond any bound `B ≥ 7`: only pentagonal `n` need the full condition; every other `n`
needs one claim, chosen by the parity of `p(n)`. -/
theorem H234_of_pentagonal (B : ℕ) (hB : 7 ≤ B)
    (h2 : ∀ n, B < n → (n ∈ Set.range pentagonal ∨ partitionCount n % 2 = 0) →
      ¬ strictPartitionCount n ∣ partitionCount n)
    (h34 : ∀ n, B < n → (n ∈ Set.range pentagonal ∨ partitionCount n % 2 = 1) →
      2 ≤ partitionCount n % strictPartitionCount n ∧
        partitionCount n % strictPartitionCount n + 2 ≤ strictPartitionCount n) :
    ∀ n, B < n → ¬ strictPartitionCount n ∣ partitionCount n ∧
      ¬ strictPartitionCount n ∣ partitionCount n - 1 ∧
      ¬ strictPartitionCount n ∣ partitionCount n + 1 := by
  intro n hn
  have hP := partitionCount_pos n
  have hQ := three_le_strictPartitionCount n (by omega)
  by_cases hq : strictPartitionCount n % 2 = 1
  · have hpent := (strictPartitionCount_odd_iff n).1 hq
    exact ⟨h2 n hn (Or.inl hpent), ((three_iff_mod _ _ hP hQ).2 (h34 n hn (Or.inl hpent))).2⟩
  · have hq2 : 2 ∣ strictPartitionCount n := Nat.dvd_of_mod_eq_zero (by omega)
    have hpar := parity_split (partitionCount n) _ hP hq2
    by_cases hp : partitionCount n % 2 = 1
    · have h34' := (three_iff_mod _ _ hP hQ).2 (h34 n hn (Or.inr hp))
      exact ⟨hpar.1 hp, h34'.2⟩
    · have hp0 : partitionCount n % 2 = 0 := by omega
      exact ⟨h2 n hn (Or.inr hp0), hpar.2 hp0⟩

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a000009.main := by
  intro h1 h2 h3
  refine ⟨?_, fun n hn => ?_⟩
  · intro n hn
    obtain ⟨T, hq, hanti, hsum⟩ : ∃ T : Finset ℕ,
        (∀ x ∈ T, ∃ m : ℕ, 0 < m ∧ x = strictPartitionCount m) ∧
        (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ x ∣ y) ∧ (∑ x ∈ T, x) = n := by
      by_cases hb : n ≤ 997436
      · exact H1_le n hn hb
      · exact h1 n (by omega)
    obtain ⟨k, terms, hterms, hs, hdiv⟩ := rep_of_finset T hq hanti
    exact ⟨k, terms, hterms, hs.trans hsum, hdiv⟩
  · by_cases hb : n ≤ 100
    · exact nondiv_le n hn hb
    · exact H234_of_pentagonal 100 (by norm_num) h2 h3 n (by omega)

end OMA.R_oeis_a000009_R4
