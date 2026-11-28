import OMAStatements.S_oeis_a340581

/-!
The column-start intervals give the multiplicity of each integer in a row.
Deleting one fixed part gives the partition recurrence. Reindexing the resulting
finite sums identifies both multisets by the multiplicity of every positive part.
-/

open scoped BigOperators

namespace A340581Proof

open OMA.S_oeis_a340581

lemma length_eq_sum (n : ℕ) : L n = ∑ i ∈ Finset.range n, A000070 i := by
  cases n with
  | zero => simp [L]
  | succ n => simp [L, A014153]

lemma length_succ (n : ℕ) : L (n + 1) = L n + A000070 n := by
  simp [length_eq_sum, Finset.sum_range_succ]

lemma cumulative_pos (n : ℕ) : 0 < A000070 n := by
  have hp : 0 < A000041 0 := by
    exact Fintype.card_pos
  have hle : A000041 0 ≤ A000070 n := by
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (A000041 i)) (by simp)
  omega

lemma length_strictMono : StrictMono L := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [length_succ]
  exact Nat.lt_add_of_pos_right (cumulative_pos n)

lemma le_length (n : ℕ) : n ≤ L n := by
  induction n with
  | zero => simp [L]
  | succ n ih =>
    rw [length_succ]
    have := cumulative_pos n
    omega

lemma start_le_iff (k n : ℕ) : start k ≤ n ↔ k ≤ L n := by
  constructor
  · intro h
    have hk : k ≤ L (start k) :=
      Nat.sInf_mem (s := {r : ℕ | k ≤ L r}) ⟨k, le_length k⟩
    exact hk.trans (length_strictMono.monotone h)
  · intro h
    exact Nat.sInf_le h

lemma start_pos {k : ℕ} (hk : 0 < k) : 0 < start k := by
  have h := start_le_iff k 0
  simp [L] at h
  omega

lemma start_eq_succ_iff (k r : ℕ) :
    start k = r + 1 ↔ L r < k ∧ k ≤ L (r + 1) := by
  have hs := Nat.sInf_upward_closed_eq_succ_iff
    (s := {n : ℕ | k ≤ L n})
    (fun a b hab hka => hka.trans (length_strictMono.monotone hab)) r
  simpa only [start, Set.mem_ofPred_eq, not_le, and_comm] using hs

lemma row_value_bounds {n k : ℕ} (hk : k ∈ Finset.Icc 1 (L n)) :
    1 ≤ T n k ∧ T n k ≤ n := by
  obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
  have hs1 := start_pos (by omega : 0 < k)
  have hsn := (start_le_iff k n).mpr hkn
  unfold T
  omega

lemma row_filter_eq {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    (Finset.Icc 1 (L n)).filter (fun k => m = T n k) =
      Finset.Ioc (L (n - m)) (L (n - m + 1)) := by
  classical
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hk1, hkn⟩, hmk⟩
    have hsn := (start_le_iff k n).mpr hkn
    have he : start k = n - m + 1 := by
      unfold T at hmk
      omega
    exact (start_eq_succ_iff k (n - m)).mp he
  · intro hk
    have he := (start_eq_succ_iff k (n - m)).mpr hk
    have hkn : k ≤ L n := hk.2.trans (length_strictMono.monotone (by omega))
    refine ⟨⟨by omega, hkn⟩, ?_⟩
    unfold T
    rw [he]
    omega

lemma row_count {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    (row n).count m = A000070 (n - m) := by
  classical
  unfold row
  rw [Multiset.count_map]
  change ((Finset.Icc 1 (L n)).filter (fun k => m = T n k)).card = _
  rw [row_filter_eq hm1 hmn, Nat.card_Ioc, length_succ]
  omega

lemma row_count_zero {n m : ℕ} (hm : ¬ (1 ≤ m ∧ m ≤ n)) :
    (row n).count m = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro h
  obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.mp h
  exact hm (row_value_bounds hk)

lemma row_support (n : ℕ) : (row n).toFinset = Finset.Icc 1 n := by
  classical
  ext m
  simp only [Multiset.mem_toFinset, Finset.mem_Icc]
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.mp h
    exact row_value_bounds hk
  · rintro ⟨hm1, hmn⟩
    apply Multiset.count_pos.mp
    rw [row_count hm1 hmn]
    exact cumulative_pos (n - m)

lemma row_eq_sum (n : ℕ) :
    row n = ∑ m ∈ Finset.Icc 1 n, A000070 (n - m) • ({m} : Multiset ℕ) := by
  classical
  conv_lhs => rw [← Multiset.toFinset_sum_count_nsmul_eq (row n)]
  rw [row_support]
  apply Finset.sum_congr rfl
  intro m hm
  rw [row_count (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2]

def divisorHom : Multiset ℕ →+ Multiset ℕ where
  toFun := fun s => s.bind (fun t => (Nat.divisors t).val)
  map_zero' := Multiset.zero_bind _
  map_add' := fun _ _ => Multiset.add_bind _ _ _

lemma row_divisors_eq_sum (n : ℕ) :
    (row n).bind (fun t => (Nat.divisors t).val) =
      ∑ m ∈ Finset.Icc 1 n, A000070 (n - m) • (Nat.divisors m).val := by
  change divisorHom (row n) = _
  rw [row_eq_sum, map_sum]
  simp only [map_nsmul, divisorHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Multiset.singleton_bind]

end A340581Proof

open scoped BigOperators
namespace A340581Partition

noncomputable def countParts (n d : ℕ) : ℕ :=
  ∑ p : Nat.Partition n, p.parts.count d

theorem countParts_zero (n : ℕ) : countParts n 0 = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p hp
  exact Multiset.count_eq_zero.mpr (fun h => (p.parts_pos h).false)

theorem countParts_of_lt {n d : ℕ} (h : n < d) : countParts n d = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p hp
  exact Multiset.count_eq_zero.mpr (fun hm => (Nat.Partition.le_of_mem_parts hm).not_gt h)

theorem countParts_rec {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    countParts n d = Fintype.card (Nat.Partition (n-d)) + countParts (n-d) d := by
  classical
  let e := Nat.Partition.partitionWithPartEquiv hd hdn
  have hs : countParts n d =
      ∑ p : {p : Nat.Partition n // d ∈ p.parts}, p.val.parts.count d := by
    unfold countParts
    rw [← Finset.sum_filter_of_ne (p := fun p : Nat.Partition n => d ∈ p.parts)]
    · exact (Finset.sum_subtype _ (by simp) _)
    · intro p hp h
      exact Multiset.count_ne_zero.mp h
  rw [hs]
  calc
    _ = ∑ q : Nat.Partition (n-d), (1 + q.parts.count d) := by
      apply Fintype.sum_equiv e
      intro p
      have h := Multiset.cons_erase p.property
      have hcount := congrArg (Multiset.count d) h
      simpa [e, Nat.Partition.partitionWithPartEquiv, add_comm] using hcount.symm
    _ = Fintype.card (Nat.Partition (n-d)) + countParts (n-d) d := by
      simp [Finset.sum_add_distrib, countParts]

theorem countParts_eq_sum (n d : ℕ) (hd : 0 < d) :
    countParts n d = ∑ i ∈ Finset.range (n / d),
      Fintype.card (Nat.Partition (n - (i + 1) * d)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hdn : d ≤ n
    · rw [countParts_rec hd hdn, ih (n-d) (Nat.sub_lt (by omega) hd),
        Nat.div_eq_sub_div hd hdn, Finset.sum_range_succ']
      simp only [zero_add, one_mul]
      rw [add_comm (Fintype.card _)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have heq : n - d - (i + 1) * d = n - (i + 1 + 1) * d := by
        rw [Nat.sub_sub]
        congr 1
        simp [Nat.add_mul, Nat.add_comm]
      rw [heq]
    · have hn : n < d := Nat.lt_of_not_ge hdn
      rw [countParts_of_lt hn, Nat.div_eq_of_lt hn]
      simp

theorem count_bind_parts (n d : ℕ) :
    ((Finset.univ : Finset (Nat.Partition n)).val.bind (fun p => p.parts)).count d =
      countParts n d := by
  classical
  rw [Multiset.count_bind]
  rfl

theorem count_cumulative_parts (n d : ℕ) :
    (∑ j ∈ Finset.Icc 1 n,
      (Finset.univ : Finset (Nat.Partition j)).val.bind (fun p => p.parts)).count d =
      ∑ j ∈ Finset.Icc 1 n, countParts j d := by
  classical
  simp only [Multiset.count_sum', count_bind_parts]

end A340581Partition

open scoped BigOperators
namespace A340581Sums

variable {M : Type*} [AddCommMonoid M]

/-- Reindex the positive multiples of `d` not exceeding `n`. -/
theorem sum_multiples (f : ℕ → M) (n d : ℕ) (hd : 0 < d) :
    (∑ i ∈ Finset.range (n / d), f (n - (i + 1) * d)) =
      ∑ m ∈ Finset.Icc 1 n, if d ∣ m then f (n - m) else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun i _ => (i + 1) * d) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hi' : i + 1 ≤ n / d := by
      have hi0 := Finset.mem_range.mp hi
      omega
    refine ⟨⟨Nat.mul_pos (by omega) hd, (Nat.le_div_iff_mul_le hd).mp hi'⟩, ?_⟩
    exact dvd_mul_left d (i + 1)
  · intro i hi j hj hij
    exact Nat.add_right_cancel (Nat.mul_right_cancel hd hij)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    refine ⟨m / d - 1, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      have hmd : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm.1.1 hm.2) hd
      have hle : m / d ≤ n / d := Nat.div_le_div_right hm.1.2
      omega
    · have hmd : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm.1.1 hm.2) hd
      rw [Nat.sub_add_cancel hmd, Nat.div_mul_cancel hm.2]
  · intro i hi
    rfl

/-- Exchange the order of summation over a finite triangle. -/
theorem sum_triangle (f : ℕ → ℕ → M) (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 j, f m j) =
      ∑ m ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc m n, f m j := by
  simpa only [Finset.Ico_add_one_right_eq_Icc] using
    (Finset.sum_Ico_Ico_comm 1 (n + 1) f).symm

/-- Translating an interval ending at `n` gives a prefix sum. -/
theorem sum_Icc_sub (f : ℕ → M) {m n : ℕ} (hmn : m ≤ n) :
    (∑ j ∈ Finset.Icc m n, f (j - m)) =
      ∑ i ∈ Finset.range (n - m + 1), f i := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have h : n + 1 - m = n - m + 1 := by omega
  simp only [h, Nat.add_sub_cancel_left]

/-- Cumulative multiples sums are the divisor convolution with prefix sums. -/
theorem sum_cumulative_multiples (f : ℕ → M) (n d : ℕ) (hd : 0 < d) :
    (∑ j ∈ Finset.Icc 1 n, ∑ i ∈ Finset.range (j / d), f (j - (i + 1) * d)) =
      ∑ m ∈ Finset.Icc 1 n,
        if d ∣ m then ∑ i ∈ Finset.range (n - m + 1), f i else 0 := by
  simp_rw [sum_multiples f _ d hd]
  rw [sum_triangle]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hdm : d ∣ m
  · simp only [hdm, if_true]
    exact sum_Icc_sub f (Finset.mem_Icc.mp hm).2
  · simp only [hdm, if_false, Finset.sum_const_zero]

end A340581Sums

namespace A340581Proof

open OMA.S_oeis_a340581 A340581Partition

lemma countParts_cumulative (n d : ℕ) (hd : 0 < d) :
    (∑ j ∈ Finset.Icc 1 n, countParts j d) =
      ∑ m ∈ Finset.Icc 1 n, if d ∣ m then A000070 (n - m) else 0 := by
  simp_rw [countParts_eq_sum _ d hd]
  exact A340581Sums.sum_cumulative_multiples
    (fun k => Fintype.card (Nat.Partition k)) n d hd

lemma count_divisors {t : ℕ} (ht : 0 < t) (d : ℕ) :
    (Nat.divisors t).val.count d = if d ∣ t then 1 else 0 := by
  split_ifs with hdt
  · apply Multiset.count_eq_one_of_mem (Nat.divisors t).nodup
    exact Nat.mem_divisors.mpr ⟨hdt, by omega⟩
  · apply Multiset.count_eq_zero.mpr
    intro hmem
    exact hdt (Nat.dvd_of_mem_divisors hmem)

lemma weighted_divisors_eq_parts (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, A000070 (n - m) • (Nat.divisors m).val) =
      ∑ j ∈ Finset.Icc 1 n,
        (Finset.univ : Finset (Nat.Partition j)).val.bind (fun p => p.parts) := by
  classical
  apply Multiset.ext.mpr
  intro d
  rw [count_cumulative_parts]
  simp only [Multiset.count_sum', Multiset.count_nsmul]
  by_cases hd : d = 0
  · subst d
    rw [show (∑ j ∈ Finset.Icc 1 n, countParts j 0) = 0 by
      simp only [countParts_zero, Finset.sum_const_zero]]
    apply Finset.sum_eq_zero
    intro m hm
    rw [count_divisors (Finset.mem_Icc.mp hm).1]
    have hm0 : m ≠ 0 := by
      have := (Finset.mem_Icc.mp hm).1
      omega
    simp [hm0]
  · rw [countParts_cumulative n d (Nat.pos_of_ne_zero hd)]
    apply Finset.sum_congr rfl
    intro m hm
    rw [count_divisors (Finset.mem_Icc.mp hm).1]
    split_ifs <;> simp

end A340581Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a340581.main := by
  intro n _
  exact (A340581Proof.row_divisors_eq_sum n).trans
    (A340581Proof.weighted_divisors_eq_parts n)
