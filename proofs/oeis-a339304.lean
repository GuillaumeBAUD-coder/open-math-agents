import OMAStatements.S_oeis_a339304

-- Based on the column-counting plan in desk note #119001.
-- The partition counting and column inversion below were constructed independently.


open scoped BigOperators
namespace A339304Partition

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

end A339304Partition

open scoped BigOperators
namespace A339304Proof
open OMA.S_oeis_a339304

def addOne {n : ℕ} (p : Nat.Partition n) : Nat.Partition (n + 1) where
  parts := 1 ::ₘ p.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi
    · decide
    · exact p.parts_pos hi
  parts_sum := by simp [p.parts_sum, Nat.add_comm]

lemma addOne_injective (n : ℕ) : Function.Injective (@addOne n) := by
  intro p q h
  apply Nat.Partition.ext
  apply (Multiset.cons_inj_right 1).mp
  exact congrArg Nat.Partition.parts h

lemma partition_monotone : Monotone A000041 := by
  apply monotone_nat_of_le_succ
  intro n
  exact Fintype.card_le_of_injective (@addOne n) (addOne_injective n)

lemma c_le_iff {k b : ℕ} (hb : k ≤ A000041 b) (j : ℕ) :
    c k ≤ j ↔ k ≤ A000041 j := by
  constructor
  · intro h
    have hk : k ≤ A000041 (c k) := Nat.sInf_mem (s := {j : ℕ | k ≤ A000041 j}) ⟨b, hb⟩
    exact hk.trans (partition_monotone h)
  · exact Nat.sInf_le (s := {j : ℕ | k ≤ A000041 j})

lemma c_eq_zero_iff {k b : ℕ} (hb : k ≤ A000041 b) :
    c k = 0 ↔ k ≤ A000041 0 := by
  have h := c_le_iff hb 0
  omega

lemma c_eq_succ_iff (k j : ℕ) :
    c k = j + 1 ↔ A000041 j < k ∧ k ≤ A000041 (j + 1) := by
  have h := Nat.sInf_upward_closed_eq_succ_iff
    (s := {j : ℕ | k ≤ A000041 j})
    (fun a b hab hka => hka.trans (partition_monotone hab)) j
  simpa only [c, Set.mem_ofPred_eq, not_le, and_comm] using h

def deltaP (j : ℕ) : ℕ :=
  if j = 0 then A000041 0 else A000041 j - A000041 (j - 1)

lemma startFiber_card (n j : ℕ) (hj : j < n) :
    ((Finset.range (A000041 (n - 1))).filter (fun i => c (i + 1) = j)).card =
      deltaP j := by
  classical
  cases j with
  | zero =>
    have hf : (Finset.range (A000041 (n - 1))).filter (fun i => c (i + 1) = 0) =
        Finset.range (A000041 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hi, hc⟩
        have := (c_eq_zero_iff (by omega : i + 1 ≤ A000041 (n-1))).mp hc
        omega
      · intro hi
        have hip : i + 1 ≤ A000041 0 := by omega
        have hbound : i + 1 ≤ A000041 (n-1) := hip.trans (partition_monotone (Nat.zero_le _))
        exact ⟨by omega, (c_eq_zero_iff hbound).mpr hip⟩
    rw [hf]
    simp [deltaP]
  | succ j =>
    have hf : (Finset.range (A000041 (n - 1))).filter (fun i => c (i + 1) = j + 1) =
        Finset.Ico (A000041 j) (A000041 (j + 1)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, c_eq_succ_iff]
      have hp : A000041 (j + 1) ≤ A000041 (n - 1) := partition_monotone (by omega)
      omega
    rw [hf, Nat.card_Ico]
    simp [deltaP]

lemma row_sum_eq (n : ℕ) (hn : 1 ≤ n) :
    (row n).sum = ∑ j ∈ Finset.range n,
      deltaP j * (Nat.divisors (n - j)).card := by
  classical
  have hc : ∀ i ∈ Finset.range (A000041 (n-1)), c (i+1) ∈ Finset.range n := by
    intro i hi
    have hip : i + 1 ≤ A000041 (n-1) := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hcle : c (i+1) ≤ n - 1 := (c_le_iff hip (n-1)).mpr hip
    exact Finset.mem_range.mpr (by omega)
  unfold row rowA336811
  rw [List.map_map]
  change (∑ i ∈ Finset.range (A000041 (n-1)), (Nat.divisors (n-c (i+1))).card) = _
  rw [← Finset.sum_fiberwise_of_maps_to' hc (fun j => (Nat.divisors (n-j)).card)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.sum_const, smul_eq_mul, startFiber_card n j (Finset.mem_range.mp hj)]

end A339304Proof

open scoped BigOperators

namespace A339304Parts

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

end A339304Parts

namespace A339304Proof

open OMA.S_oeis_a339304 A339304Partition

lemma count_divisors {t : ℕ} (ht : 0 < t) (d : ℕ) :
    (Nat.divisors t).val.count d = if d ∣ t then 1 else 0 := by
  split_ifs with hdt
  · apply Multiset.count_eq_one_of_mem (Nat.divisors t).nodup
    exact Nat.mem_divisors.mpr ⟨hdt, by omega⟩
  · apply Multiset.count_eq_zero.mpr
    intro hmem
    exact hdt (Nat.dvd_of_mem_divisors hmem)

lemma weighted_divisors_eq_parts (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, A000041 (n - m) • (Nat.divisors m).val) =
      (Finset.univ : Finset (Nat.Partition n)).val.bind (fun p => p.parts) := by
  classical
  apply Multiset.ext.mpr
  intro d
  rw [count_bind_parts]
  simp only [Multiset.count_sum', Multiset.count_nsmul]
  by_cases hd : d = 0
  · subst d
    rw [countParts_zero]
    apply Finset.sum_eq_zero
    intro m hm
    rw [count_divisors (Finset.mem_Icc.mp hm).1]
    have hm0 : m ≠ 0 := by
      have := (Finset.mem_Icc.mp hm).1
      omega
    simp [hm0]
  · rw [countParts_eq_sum n d (Nat.pos_of_ne_zero hd),
      A339304Parts.sum_multiples (fun k => Fintype.card (Nat.Partition k)) n d
        (Nat.pos_of_ne_zero hd)]
    apply Finset.sum_congr rfl
    intro m hm
    rw [count_divisors (Finset.mem_Icc.mp hm).1]
    split_ifs <;> simp [A000041]

lemma card_all_parts (n : ℕ) :
    ((Finset.univ : Finset (Nat.Partition n)).val.bind (fun p => p.parts)).card =
      A006128 n := by
  rw [Multiset.card_bind]
  rfl

lemma sum_reflect (f g : ℕ → ℕ) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, f (n-m) * g m) =
      ∑ j ∈ Finset.range n, f j * g (n-j) := by
  refine Finset.sum_bij (fun m _ => n-m) ?_ ?_ ?_ ?_
  · intro m hm
    have := Finset.mem_Icc.mp hm
    apply Finset.mem_range.mpr
    omega
  · intro m hm k hk hmk
    have := Finset.mem_Icc.mp hm
    have := Finset.mem_Icc.mp hk
    omega
  · intro j hj
    have hjn := Finset.mem_range.mp hj
    refine ⟨n-j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro m hm
    have := Finset.mem_Icc.mp hm
    have heq : n-(n-m) = m := by omega
    rw [heq]

lemma total_parts_convolution (n : ℕ) :
    A006128 n =
      ∑ j ∈ Finset.range n, A000041 j * (Nat.divisors (n-j)).card := by
  have hc := congrArg Multiset.card (weighted_divisors_eq_parts n)
  rw [card_all_parts] at hc
  calc
    A006128 n =
        (∑ m ∈ Finset.Icc 1 n, A000041 (n-m) • (Nat.divisors m).val).card := hc.symm
    _ = ∑ m ∈ Finset.Icc 1 n, A000041 (n-m) * (Nat.divisors m).card := by
      simp only [Multiset.card_sum, Multiset.card_nsmul, Finset.card_val]
    _ = _ := sum_reflect A000041 (fun m => (Nat.divisors m).card) n

/-- Taking a first difference of the coefficients takes a first difference of the convolution. -/
lemma delta_convolution (p g : ℕ → ℕ) (hp : Monotone p) (n : ℕ) (hn : 1 ≤ n) :
    (∑ j ∈ Finset.range n,
      (if j = 0 then p 0 else p j - p (j-1)) * g (n-j)) +
      (∑ j ∈ Finset.range (n-1), p j * g (n-1-j)) =
        ∑ j ∈ Finset.range n, p j * g (n-j) := by
  cases n with
  | zero => omega
  | succ n =>
    change (∑ j ∈ Finset.range (n+1),
      (if j = 0 then p 0 else p j - p (j-1)) * g (n+1-j)) +
      (∑ j ∈ Finset.range n, p j * g (n-j)) =
        ∑ j ∈ Finset.range (n+1), p j * g (n+1-j)
    have hd : (∑ j ∈ Finset.range (n+1),
        (if j = 0 then p 0 else p j - p (j-1)) * g (n+1-j)) =
        (∑ j ∈ Finset.range n, (p (j+1) - p j) * g (n-j)) + p 0 * g (n+1) := by
      rw [Finset.sum_range_succ']
      simp
    rw [hd, Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [add_right_comm, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Nat.add_mul, Nat.sub_add_cancel (hp (Nat.le_succ j))]

end A339304Proof

namespace A339304Proof
open OMA.S_oeis_a339304

theorem final_result : ∀ n : ℕ, 1 ≤ n → ((row n).sum : ℤ) = A138137 n := by
  intro n hn
  have h : (row n).sum + A006128 (n-1) = A006128 n := by
    rw [row_sum_eq n hn, total_parts_convolution (n-1), total_parts_convolution n]
    simpa only [deltaP] using delta_convolution A000041
      (fun t => (Nat.divisors t).card) partition_monotone n hn
  have hz := congrArg (fun t : ℕ => (t : ℤ)) h
  simp only [Nat.cast_add] at hz
  unfold A138137
  omega

end A339304Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a339304.main :=
  A339304Proof.final_result
