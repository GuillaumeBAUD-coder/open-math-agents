import OMAStatements.S_oeis_a000123
import Mathlib



open scoped BigOperators

namespace OMA.S_oeis_a000123

theorem a_pos (n : ℕ) : 0 < a n := by
  classical
  let p : Nat.Partition (2 * n) :=
    Nat.Partition.ofSums (2 * n) (Multiset.replicate (2 * n) 1) (by simp)
  have hparts : ∀ i ∈ p.parts, ∃ k, i = 2 ^ k := by
    intro i hi
    have hi' : i = 1 := by
      simp [p, Nat.Partition.ofSums, Multiset.mem_replicate] at hi
      exact hi.1.2
    subst i
    exact ⟨0, by norm_num⟩
  have hp : p ∈ Finset.univ.filter
      (fun q : Nat.Partition (2 * n) => ∀ i ∈ q.parts, ∃ k, i = 2 ^ k) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparts⟩
  exact Finset.card_pos.mpr ⟨p, hp⟩

end OMA.S_oeis_a000123


open scoped BigOperators
open Filter Topology

namespace OMA.S_oeis_a000123

noncomputable section
local instance instDecidableProp (p : Prop) : Decidable p := Classical.propDecidable p

private noncomputable def BinaryParts (m : ℕ) : Finset (Nat.Partition m) := by
  classical
  exact Nat.Partition.restricted m (fun i => ∃ k, i = 2 ^ k)

private noncomputable def BinaryCount (m : ℕ) : ℕ :=
  Fintype.card {p : Nat.Partition m // ∀ i ∈ p.parts, ∃ k, i = 2 ^ k}

private theorem BinaryCount_eq_card (m : ℕ) : BinaryCount m = (BinaryParts m).card := by
  classical
  unfold BinaryCount BinaryParts Nat.Partition.restricted
  rw [Fintype.card_subtype]

private theorem a_eq_BinaryCount (n : ℕ) : a n = BinaryCount (2 * n) := by
  classical
  unfold a BinaryCount
  rw [← Finset.card_subtype]
  simp

private theorem allowed_erase_one {m : ℕ} (p : Nat.Partition m)
    (hp : ∀ i ∈ p.parts, ∃ k, i = 2 ^ k) :
    ∀ i ∈ p.parts.erase 1, ∃ k, i = 2 ^ k := by
  intro i him
  exact hp i (Multiset.mem_of_mem_erase him)

private theorem allowed_cons_one {m : ℕ} (p : Nat.Partition m)
    (hp : ∀ i ∈ p.parts, ∃ k, i = 2 ^ k) :
    ∀ i ∈ 1 ::ₘ p.parts, ∃ k, i = 2 ^ k := by
  intro i hi
  rcases Multiset.mem_cons.mp hi with h | h
  · subst i
    exact ⟨0, by norm_num⟩
  · exact hp i h

private theorem pow_two_even_of_ne_one {i : ℕ}
    (hpow : ∃ k, i = 2 ^ k) (hone : i ≠ 1) : Even i := by
  obtain ⟨k, rfl⟩ := hpow
  cases k with
  | zero => exact (hone rfl).elim
  | succ k => exact ⟨2 ^ k, by simp [pow_succ, Nat.mul_two]⟩

private theorem sum_div_two_of_even {s : Multiset ℕ} (hs : ∀ i ∈ s, Even i) :
    2 * (s.map (fun i => i / 2)).sum = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha := hs a (by simp)
      have hs' : ∀ i ∈ s, Even i := fun i hi => hs i (by simp [hi])
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons]
      have hsum := ih hs'
      obtain ⟨b, hb⟩ := ha
      have hdiv : 2 * (a / 2) = a := by omega
      calc
        2 * (a / 2 + (Multiset.map (fun i => i / 2) s).sum) =
            2 * (a / 2) + 2 * (Multiset.map (fun i => i / 2) s).sum := by ring
        _ = a + s.sum := by rw [hdiv, hsum]

private theorem binary_parts_even_of_not_one {m : ℕ} (p : Nat.Partition m)
    (hp : ∀ i ∈ p.parts, ∃ k, i = 2 ^ k) (hnot : 1 ∉ p.parts) :
    ∀ i ∈ p.parts, Even i := by
  intro i hi
  apply pow_two_even_of_ne_one (hp i hi)
  intro heq
  subst i
  exact hnot hi

private theorem binary_partition_total_even {m : ℕ} (p : Nat.Partition m)
    (hp : ∀ i ∈ p.parts, ∃ k, i = 2 ^ k) (hnot : 1 ∉ p.parts) : Even m := by
  have hsum := sum_div_two_of_even (binary_parts_even_of_not_one p hp hnot)
  rw [p.parts_sum] at hsum
  exact ⟨(p.parts.map fun i => i / 2).sum, by simpa [two_mul] using hsum.symm⟩

private theorem map_halve_double {s : Multiset ℕ} (hs : ∀ i ∈ s, Even i) :
    (s.map (fun i => i / 2)).map (fun i => 2 * i) = s := by
  rw [Multiset.map_map]
  calc
    Multiset.map ((fun i => 2 * i) ∘ fun i => i / 2) s = Multiset.map id s := by
      apply Multiset.map_congr rfl
      intro i hi
      obtain ⟨k, hk⟩ := hs i hi
      have hdiv : 2 * (i / 2) = i := by omega
      simpa [Function.comp_def] using hdiv
    _ = s := Multiset.map_id _

private theorem map_double_halve (s : Multiset ℕ) :
    (s.map (fun i => 2 * i)).map (fun i => i / 2) = s := by
  rw [Multiset.map_map]
  calc
    Multiset.map ((fun i => i / 2) ∘ fun i => 2 * i) s = Multiset.map id s := by
      apply Multiset.map_congr rfl
      intro i hi
      simp
    _ = s := Multiset.map_id _

private theorem sum_double (s : Multiset ℕ) :
    (s.map (fun i => 2 * i)).sum = 2 * s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp [ih, Nat.mul_add]

private def halveBinaryNoOneEquiv (n : ℕ) :
    {p : {q : Nat.Partition (2 * n) // ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} //
      1 ∉ p.1.parts} ≃
    {q : Nat.Partition n // ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} := by
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    let r : Nat.Partition n := {
      parts := p.1.1.parts.map (fun i => i / 2)
      parts_pos := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hi
        have heven := binary_parts_even_of_not_one p.1.1 p.1.2 p.2 j hj
        have hjpos := p.1.1.parts_pos hj
        obtain ⟨k, hk⟩ := heven
        omega
      parts_sum := by
        have hsum := sum_div_two_of_even
          (binary_parts_even_of_not_one p.1.1 p.1.2 p.2)
        rw [p.1.1.parts_sum] at hsum
        omega }
    refine ⟨r, ?_⟩
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hi
    rcases p.1.2 j hj with ⟨k, rfl⟩
    cases k with
    | zero => exact (p.2 (by simpa using hj)).elim
    | succ k => exact ⟨k, by simp [pow_succ, Nat.mul_comm]⟩
  · intro q
    let r : Nat.Partition (2 * n) := {
      parts := q.1.parts.map (fun i => 2 * i)
      parts_pos := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hi
        exact Nat.mul_pos (by norm_num) (q.1.parts_pos hj)
      parts_sum := by
        simp [sum_double, q.1.parts_sum] }
    refine ⟨⟨r, ?_⟩, ?_⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hi
      rcases q.2 j hj with ⟨k, rfl⟩
      exact ⟨k + 1, by simp [pow_succ, Nat.mul_comm]⟩
    · simp [r]
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    apply Nat.Partition.ext
    change (p.1.1.parts.map (fun i => i / 2)).map (fun i => 2 * i) = p.1.1.parts
    exact map_halve_double (binary_parts_even_of_not_one p.1.1 p.1.2 p.2)
  · intro q
    apply Subtype.ext
    apply Nat.Partition.ext
    change (q.1.parts.map (fun i => 2 * i)).map (fun i => i / 2) = q.1.parts
    exact map_double_halve q.1.parts

private def binaryPartitionWithOneEquiv {m : ℕ} (hm : 0 < m) :
    {p : {q : Nat.Partition m // ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} //
      1 ∈ p.1.parts} ≃
    {q : Nat.Partition (m - 1) // ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} := by
  let e := Nat.Partition.partitionWithPartEquiv (n := m) (a := 1) (by omega) (by omega)
  refine
    { toFun := fun p => ⟨e ⟨p.1.1, p.2⟩,
        allowed_erase_one p.1.1 p.1.2⟩
      invFun := fun q => ⟨⟨e.symm q,
        allowed_cons_one q.1 q.2⟩, (e.symm q).2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {q : Nat.Partition m // 1 ∈ q.parts} => z.1)
      (e.left_inv ⟨p.1.1, p.2⟩)
  · intro q
    apply Subtype.ext
    exact e.right_inv q

private theorem card_binary_partitions_containing_one {m : ℕ} (hm : 0 < m) :
    Fintype.card {p : {q : Nat.Partition m // ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} //
      1 ∈ p.1.parts} = BinaryCount (m - 1) := by
  classical
  let e := binaryPartitionWithOneEquiv hm
  rw [Fintype.card_congr e]
  rfl

private theorem binaryCount_split_at_one (m : ℕ) :
    BinaryCount m =
      Fintype.card {p : {q : Nat.Partition m // ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} //
        1 ∈ p.1.parts} +
      Fintype.card {p : {q : Nat.Partition m // ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} //
        1 ∉ p.1.parts} := by
  let P : {q : Nat.Partition m // ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} → Prop :=
    fun p => 1 ∈ p.1.parts
  let e : {p : {q : Nat.Partition m // ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} //
      P p ∨ ¬ P p} ≃ {q : Nat.Partition m // ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} := {
    toFun := fun p => p.1
    invFun := fun p => ⟨p, em (P p)⟩
    left_inv := by intro p; apply Subtype.ext; rfl
    right_inv := by intro p; rfl }
  calc
    BinaryCount m = Fintype.card {p : {q : Nat.Partition m //
        ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} // P p ∨ ¬ P p} := by
          exact (Fintype.card_congr e).symm
    _ = Fintype.card {p : {q : Nat.Partition m //
          ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} // P p} +
        Fintype.card {p : {q : Nat.Partition m //
          ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} // ¬ P p} := by
          exact Fintype.card_subtype_or_disjoint P (fun p => ¬ P p)
            (Set.disjoint_left.mpr (by
              intro x hx hn
              exact hn hx))
    _ = _ := by rfl

private theorem binaryCount_even_recurrence (n : ℕ) (hn : 0 < n) :
    BinaryCount (2 * n) = BinaryCount (2 * n - 1) + BinaryCount n := by
  rw [binaryCount_split_at_one (2 * n)]
  rw [card_binary_partitions_containing_one (by omega)]
  have hno : Fintype.card {p : {q : Nat.Partition (2 * n) //
      ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} // 1 ∉ p.1.parts} = BinaryCount n := by
    exact Fintype.card_congr (halveBinaryNoOneEquiv n)
  rw [hno]

private theorem binaryCount_odd_recurrence (n : ℕ) :
    BinaryCount (2 * n + 1) = BinaryCount (2 * n) := by
  rw [binaryCount_split_at_one (2 * n + 1)]
  rw [card_binary_partitions_containing_one (by omega)]
  have hno : Fintype.card {p : {q : Nat.Partition (2 * n + 1) //
      ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} // 1 ∉ p.1.parts} = 0 := by
    letI : IsEmpty {p : {q : Nat.Partition (2 * n + 1) //
        ∀ i ∈ q.parts, ∃ k, i = 2 ^ k} // 1 ∉ p.1.parts} :=
      ⟨fun p => by
        have heven := binary_partition_total_even p.1.1 p.1.2 p.2
        obtain ⟨k, hk⟩ := heven
        omega⟩
    simp
  rw [hno, Nat.add_zero]
  have hindex : 2 * n + 1 - 1 = 2 * n := by omega
  rw [hindex]

theorem a_half_recurrence (n : ℕ) (hn : 0 < n) :
    a n = a (n - 1) + a (n / 2) := by
  rw [a_eq_BinaryCount, binaryCount_even_recurrence n hn]
  have hodd : BinaryCount (2 * n - 1) = BinaryCount (2 * (n - 1)) := by
    have h : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
    rw [h, binaryCount_odd_recurrence]
  rw [hodd, ← a_eq_BinaryCount]
  have hhalf : BinaryCount n = BinaryCount (2 * (n / 2)) := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hnEq : n = 2 * (n / 2) := by omega
      rw [hnEq]
      simp
    · have hnEq : n = 2 * (n / 2) + 1 := by omega
      have hfloor : (2 * (n / 2) + 1) / 2 = n / 2 := by omega
      rw [hnEq, hfloor, binaryCount_odd_recurrence]
  rw [hhalf, ← a_eq_BinaryCount]

theorem a_monotone : Monotone a := by
  apply monotone_nat_of_le_succ
  intro n
  have h := a_half_recurrence (n + 1) (by omega)
  have hi : n + 1 - 1 = n := by omega
  rw [hi] at h
  omega

theorem a_double_sum_identity (n : ℕ) :
    a (2 * n) = a n + 2 * ∑ j ∈ Finset.range n, a j := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hodd := a_half_recurrence (2 * n + 1) (by omega)
      have heven := a_half_recurrence (2 * n + 2) (by omega)
      have hoddidx : (2 * n + 1) - 1 = 2 * n := by omega
      have hoddhalf : (2 * n + 1) / 2 = n := by omega
      have hevenidx : (2 * n + 2) - 1 = 2 * n + 1 := by omega
      have hevenhalf : (2 * n + 2) / 2 = n + 1 := by omega
      rw [hoddidx, hoddhalf] at hodd
      rw [hevenidx, hevenhalf] at heven
      have hodd' : a (2 * n + 1) = a (2 * n) + a n := by
        exact hodd
      have heven' : a (2 * n + 2) = a (2 * n + 1) + a (n + 1) := by
        exact heven
      calc
        a (2 * (n + 1)) = a (2 * n + 2) := by congr 1
        _ = a (2 * n + 1) + a (n + 1) := heven'
        _ = a (2 * n) + a n + a (n + 1) := by rw [hodd']
        _ = a (n + 1) + 2 * ∑ j ∈ Finset.range (n + 1), a j := by
          rw [ih, Finset.sum_range_succ]
          ring

theorem main_of_cumulative_sum_limit
    (hsum : Tendsto
      (fun n : ℕ => Real.log n / (n : ℝ) *
        ((∑ j ∈ Finset.range n, a j : ℕ) : ℝ) / (a n : ℝ))
      atTop (𝓝 (Real.log 2))) :
    type_of% @main := by
  have hlogdivReal : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa [pow_one] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlogdiv : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) :=
    hlogdivReal.comp tendsto_natCast_atTop_atTop
  have hdouble : Tendsto
      (fun n : ℕ => 2 * (Real.log n / (n : ℝ) *
        ((∑ j ∈ Finset.range n, a j : ℕ) : ℝ) / (a n : ℝ)))
      atTop (𝓝 (2 * Real.log 2)) := by
    simpa using hsum.const_mul 2
  have hsumlim := hlogdiv.add hdouble
  have ha : ∀ n, 0 < (a n : ℝ) := fun n => by
    exact_mod_cast a_pos n
  have hEq : ∀ᶠ n : ℕ in atTop,
      Real.log n * a (2 * n) / (n * a n) =
        Real.log n / (n : ℝ) +
          2 * (Real.log n / (n : ℝ) *
            ((∑ j ∈ Finset.range n, a j : ℕ) : ℝ) / (a n : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hcount : (a (2 * n) : ℝ) = (a n : ℝ) +
        2 * ((∑ j ∈ Finset.range n, a j : ℕ) : ℝ) := by
      exact_mod_cast a_double_sum_identity n
    change Real.log n * (a (2 * n) : ℝ) /
        ((n : ℝ) * (a n : ℝ)) = _
    rw [hcount]
    field_simp [hnR.ne', (ha n).ne']
  have hfinal := Filter.Tendsto.congr'
    (Filter.EventuallyEq.symm hEq) hsumlim
  change Tendsto
    (fun n : ℕ => Real.log n * a (2 * n) / (n * a n))
    atTop (𝓝 (2 * Real.log 2))
  simpa [zero_add] using hfinal

end

end OMA.S_oeis_a000123



open PowerSeries

namespace LocalGeneratingFunction

noncomputable section

def series (f : ℕ → ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (f n : ℚ)

theorem recurrence_series_identity (f : ℕ → ℕ) (hzero : f 0 = 1)
    (hrec : ∀ n, 0 < n → f n = f (n - 1) + f (n / 2)) :
    (1 - PowerSeries.X) * series f =
      (1 + PowerSeries.X) * (series f).subst (PowerSeries.X ^ 2) := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, add_mul, one_mul]
  rw [map_sub, map_add]
  have hX (g : PowerSeries ℚ) (m : ℕ) :
      PowerSeries.coeff m (PowerSeries.X * g) =
        if 1 ≤ m then PowerSeries.coeff (m - 1) g else 0 := by
    simpa only [pow_one] using PowerSeries.coeff_X_pow_mul' g 1 m
  simp [series, hX, PowerSeries.coeff_subst_X_pow]
  cases n with
  | zero => simp [hzero]
  | succ n =>
      have hmpos : 0 < n + 1 := by omega
      have hpred : n + 1 - 1 = n := by omega
      have hr : (f (n + 1) : ℚ) = (f n : ℚ) + (f ((n + 1) / 2) : ℚ) := by
        have h := hrec (n + 1) hmpos
        rw [hpred] at h
        exact_mod_cast h
      have hleft : (f (n + 1) : ℚ) - (f n : ℚ) = (f ((n + 1) / 2) : ℚ) := by
        rw [hr]
        ring
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with he | ho
      · have hdiv : 2 ∣ n + 1 := Nat.dvd_of_mod_eq_zero he
        have hnot : ¬ 2 ∣ n := by omega
        simp [hdiv, hnot, hleft]
      · have hnot : ¬ 2 ∣ n + 1 := by omega
        have hdiv : 2 ∣ n := by simpa [hpred] using Nat.dvd_of_mod_eq_zero (by omega : (n + 1 - 1) % 2 = 0)
        have hquot : n / 2 = (n + 1) / 2 := by omega
        simp [hnot, hdiv, hquot, hleft]

end

end LocalGeneratingFunction


open PowerSeries

namespace LocalDyadicWeight

def coefficient (k : ℕ) : ℕ := 2 ^ (k.factorization 2 + 1)

theorem one_add_sum_powers (v : ℕ) :
    1 + ∑ i ∈ Finset.range (v + 1), 2 ^ i = 2 ^ (v + 1) := by
  induction v with
  | zero => simp
  | succ v ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

theorem coefficient_eq_geometric_sum (k : ℕ) :
    coefficient k = 1 + ∑ i ∈ Finset.range (k.factorization 2 + 1), 2 ^ i := by
  rw [one_add_sum_powers]
  rfl

theorem coefficient_eq_dyadic_divisor_sum {k : ℕ} (hk : k ≠ 0) :
    coefficient k = 1 + ∑ i ∈ Finset.range (k.factorization 2 + 1),
      if 2 ^ i ∣ k then 2 ^ i else 0 := by
  rw [coefficient_eq_geometric_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ k.factorization 2 := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hdvd : 2 ^ i ∣ k := Nat.prime_two.pow_dvd_iff_le_factorization hk |>.2 hi'
  simp [hdvd]

theorem coefficient_eq_log_dyadic_sum {k : ℕ} (hk : k ≠ 0) :
    coefficient k = 1 + ∑ i ∈ Finset.range (Nat.log 2 k + 1),
      if 2 ^ i ∣ k then 2 ^ i else 0 := by
  let v := k.factorization 2
  have hvlog : v ≤ Nat.log 2 k := by
    have hdvd : 2 ^ v ∣ k := Nat.prime_two.pow_dvd_iff_le_factorization hk |>.2 le_rfl
    exact Nat.le_log_of_pow_le (by norm_num) (Nat.le_of_dvd (by omega) hdvd)
  rw [coefficient_eq_dyadic_divisor_sum hk]
  have hsplit : Nat.log 2 k + 1 = (v + 1) + (Nat.log 2 k - v) := by omega
  have hdecomp :
      (∑ i ∈ Finset.range (Nat.log 2 k + 1),
        if 2 ^ i ∣ k then 2 ^ i else 0) =
        (∑ i ∈ Finset.range (v + 1), if 2 ^ i ∣ k then 2 ^ i else 0) +
          ∑ i ∈ Finset.range (Nat.log 2 k - v),
            if 2 ^ (v + 1 + i) ∣ k then 2 ^ (v + 1 + i) else 0 := by
    rw [hsplit]
    exact Finset.sum_range_add _ (v + 1) (Nat.log 2 k - v)
  have hfirst :
      (∑ i ∈ Finset.range (v + 1), if 2 ^ i ∣ k then 2 ^ i else 0) =
        ∑ i ∈ Finset.range (v + 1), 2 ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ v := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hdvd : 2 ^ i ∣ k := Nat.prime_two.pow_dvd_iff_le_factorization hk |>.2 hi'
    simp [hdvd]
  have htail :
      (∑ i ∈ Finset.range (Nat.log 2 k - v),
        if 2 ^ (v + 1 + i) ∣ k then 2 ^ (v + 1 + i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hnot : ¬ 2 ^ (v + 1 + i) ∣ k := by
      intro hdvd
      have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hk).1 hdvd
      omega
    simp [hnot]
  rw [hdecomp, hfirst, htail, add_zero]

theorem coefficient_eq_dyadic_sum_of_log_le {k L : ℕ} (hk : k ≠ 0)
    (hlog : Nat.log 2 k ≤ L) :
    coefficient k = 1 + ∑ i ∈ Finset.range (L + 1),
      if 2 ^ i ∣ k then 2 ^ i else 0 := by
  rw [coefficient_eq_log_dyadic_sum hk]
  have htail :
      (∑ i ∈ Finset.range (L - Nat.log 2 k),
        if 2 ^ (Nat.log 2 k + 1 + i) ∣ k then
          2 ^ (Nat.log 2 k + 1 + i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hval : k.factorization 2 ≤ Nat.log 2 k := by
      have hdvd : 2 ^ (k.factorization 2) ∣ k :=
        Nat.prime_two.pow_dvd_iff_le_factorization hk |>.2 le_rfl
      exact Nat.le_log_of_pow_le (by norm_num) (Nat.le_of_dvd (by omega) hdvd)
    have hnot : ¬ 2 ^ (Nat.log 2 k + 1 + i) ∣ k := by
      intro hdvd
      have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hk).1 hdvd
      omega
    simp [hnot]
  have hsum :
      (∑ i ∈ Finset.range (L + 1), if 2 ^ i ∣ k then 2 ^ i else 0) =
        ∑ i ∈ Finset.range (Nat.log 2 k + 1), if 2 ^ i ∣ k then 2 ^ i else 0 := by
    have hsplit : L + 1 = (Nat.log 2 k + 1) + (L - Nat.log 2 k) := by omega
    rw [hsplit, Finset.sum_range_add, htail, add_zero]
  rw [hsum]

theorem coefficient_eq_dyadic_sum_of_le {k n : ℕ} (hk : k ≠ 0) (hkn : k ≤ n) :
    coefficient k = 1 + ∑ i ∈ Finset.range (Nat.log 2 n + 1),
      if 2 ^ i ∣ k then 2 ^ i else 0 := by
  exact coefficient_eq_dyadic_sum_of_log_le hk (Nat.log_mono_right hkn)

theorem coefficient_odd (n : ℕ) : coefficient (2 * n + 1) = 2 := by
  have hnot : ¬ 2 ∣ 2 * n + 1 := by omega
  simp [coefficient, Nat.factorization_eq_zero_of_not_dvd hnot]

theorem coefficient_even (n : ℕ) (hn : 0 < n) :
    coefficient (2 * n) = 2 * coefficient n := by
  unfold coefficient
  rw [show 2 * n = 2 * n by rfl,
    Nat.factorization_mul (by omega : (2 : ℕ) ≠ 0) (by omega : n ≠ 0),
    Finsupp.add_apply, Nat.prime_two.factorization_self]
  calc
    2 ^ (1 + n.factorization 2 + 1) =
        2 ^ ((n.factorization 2 + 1) + 1) := by congr 1 <;> omega
    _ = 2 ^ (n.factorization 2 + 1) * 2 := by rw [pow_succ]
    _ = 2 * 2 ^ (n.factorization 2 + 1) := by omega

def coefficientSequence (n : ℕ) : ℕ := if n = 0 then 0 else coefficient n

def weightSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (coefficientSequence n : ℚ)

def oddSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n % 2 = 1 then 2 else 0

theorem weight_series_identity :
    weightSeries = oddSeries + (2 : ℚ) • (weightSeries.subst (PowerSeries.X ^ 2)) := by
  apply PowerSeries.ext
  intro n
  simp [weightSeries, oddSeries, coefficientSequence,
    PowerSeries.coeff_subst_X_pow (by norm_num : (2 : ℕ) ≠ 0)]
  cases n with
  | zero => simp [coefficientSequence]
  | succ n =>
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with he | ho
      · have hdiv : 2 ∣ n + 1 := Nat.dvd_of_mod_eq_zero he
        have hpos : 0 < (n + 1) / 2 := by omega
        let q := (n + 1) / 2
        have hn : n + 1 = 2 * q := by dsimp [q]; omega
        have hlarge : ¬ n + 1 ≤ 1 := by omega
        have hc := coefficient_even q hpos
        have hc' : (coefficient (2 * q) : ℚ) = 2 * (coefficient q : ℚ) := by
          exact_mod_cast hc
        rw [if_neg (by omega : n + 1 ≠ 0)]
        rw [if_neg (by omega : (n + 1) % 2 ≠ 1)]
        rw [if_pos hdiv, if_neg hlarge]
        rw [hn, Nat.mul_div_cancel_left q (by norm_num)]
        simpa using hc'
      · have hnot : ¬ 2 ∣ n + 1 := by omega
        let q := (n + 1) / 2
        have hn : n + 1 = 2 * q + 1 := by dsimp [q]; omega
        rw [if_neg (by omega : n + 1 ≠ 0)]
        rw [if_pos ho, if_neg hnot]
        rw [hn]
        have hc : (coefficient (2 * q + 1) : ℚ) = 2 := by
          exact_mod_cast coefficient_odd q
        simpa using hc

end LocalDyadicWeight


open PowerSeries

namespace LocalGeneratingFunction

noncomputable section

def invAtOne (p : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.invOfUnit p (1 : ℚˣ)

def logDerivative (p : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.X * PowerSeries.derivative ℚ p * invAtOne p

def U : PowerSeries ℚ := 1 - PowerSeries.X

def V : PowerSeries ℚ := 1 + PowerSeries.X

def oddRational : PowerSeries ℚ :=
  PowerSeries.X * invAtOne U + PowerSeries.X * invAtOne V

def oddSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n % 2 = 1 then 2 else 0

theorem invAtOne_mul (p : PowerSeries ℚ)
    (hp : PowerSeries.constantCoeff p = 1) : p * invAtOne p = 1 := by
  exact PowerSeries.mul_invOfUnit p 1 hp

theorem invAtOne_mul_left (p : PowerSeries ℚ)
    (hp : PowerSeries.constantCoeff p = 1) : invAtOne p * p = 1 := by
  exact PowerSeries.invOfUnit_mul p 1 hp

theorem U_const : PowerSeries.constantCoeff U = 1 := by
  simp [U]

theorem V_const : PowerSeries.constantCoeff V = 1 := by
  simp [V]

theorem invU_coeff (n : ℕ) :
    PowerSeries.coeff n (invAtOne U) = 1 := by
  have hval : U * (PowerSeries.invOneSubPow ℚ 1).val = 1 := by
    have h := (PowerSeries.invOneSubPow ℚ 1).inv_val
    rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at h
    simpa [U] using h
  have heq : invAtOne U = (PowerSeries.invOneSubPow ℚ 1).val := by
    calc
      invAtOne U = invAtOne U * 1 := by simp
      _ = invAtOne U * (U * (PowerSeries.invOneSubPow ℚ 1).val) := by rw [hval]
      _ = (invAtOne U * U) * (PowerSeries.invOneSubPow ℚ 1).val := by ring
      _ = _ := by rw [invAtOne_mul_left U U_const]; simp
  rw [heq]
  have hmk : (PowerSeries.invOneSubPow ℚ 1).val =
      PowerSeries.mk (fun k => (Nat.choose k 0 : ℚ)) := by
    simpa using PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos
      (S := ℚ) (d := 1) (by norm_num)
  rw [hmk]
  simp [PowerSeries.coeff_mk]

theorem invV_coeff (n : ℕ) :
    PowerSeries.coeff n (invAtOne V) = (-1 : ℚ) ^ n := by
  let G : PowerSeries ℚ := PowerSeries.mk fun k => (-1 : ℚ) ^ k
  have hVG : V * G = 1 := by
    apply PowerSeries.ext
    intro k
    change PowerSeries.coeff k ((1 + PowerSeries.X) * G) = PowerSeries.coeff k 1
    rw [add_mul, one_mul, map_add]
    have hX : PowerSeries.coeff k (PowerSeries.X * G) =
        if 1 ≤ k then PowerSeries.coeff (k - 1) G else 0 := by
      simpa only [pow_one] using (PowerSeries.coeff_X_pow_mul' G 1 k)
    rw [hX]
    cases k with
    | zero => simp [G]
    | succ k => simp [G]; ring
  have heq : invAtOne V = G := by
    calc
      invAtOne V = invAtOne V * 1 := by simp
      _ = invAtOne V * (V * G) := by rw [hVG]
      _ = (invAtOne V * V) * G := by ring
      _ = G := by rw [invAtOne_mul_left V V_const]; simp
  rw [heq]
  simp [G, PowerSeries.coeff_mk]

theorem oddRational_eq_oddSeries : oddRational = oddSeries := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [oddRational, oddSeries]
  | succ n =>
      have hX (g : PowerSeries ℚ) :
          PowerSeries.coeff (n + 1) (PowerSeries.X * g) = PowerSeries.coeff n g := by
        simpa using (PowerSeries.coeff_X_pow_mul' g 1 (n + 1))
      rw [oddRational, oddSeries, map_add, hX, hX,
        invU_coeff, invV_coeff, PowerSeries.coeff_mk]
      rcases Nat.mod_two_eq_zero_or_one n with he | ho
      · have hn : n = 2 * (n / 2) := by omega
        rw [hn, pow_mul]
        norm_num
      · have hn : (n + 1) % 2 = 0 := by omega
        have hn' : n = 2 * (n / 2) + 1 := by omega
        have hpow : (-1 : ℚ) ^ n = -1 := by
          rw [hn', pow_add, pow_mul]
          norm_num
        simp [hn, hpow]

theorem derivative_functional_equation (A : PowerSeries ℚ)
    (hA : PowerSeries.constantCoeff A = 1)
    (hfunc : U * A = V * A.subst (PowerSeries.X ^ 2)) :
    U * PowerSeries.derivative ℚ A - A =
      V * PowerSeries.derivative ℚ (A.subst (PowerSeries.X ^ 2)) +
        A.subst (PowerSeries.X ^ 2) := by
  have h := congrArg (PowerSeries.derivative ℚ) hfunc
  rw [Derivation.leibniz, Derivation.leibniz] at h
  simp [U, V, smul_eq_mul] at h
  simpa [U, V, sub_eq_add_neg] using h

theorem logDerivative_functional_equation (A : PowerSeries ℚ)
    (hA : PowerSeries.constantCoeff A = 1)
    (hfunc : U * A = V * A.subst (PowerSeries.X ^ 2)) :
    logDerivative A = oddRational +
      2 * (logDerivative A).subst (PowerSeries.X ^ 2) := by
  let A2 : PowerSeries ℚ := A.subst (PowerSeries.X ^ 2)
  let iA : PowerSeries ℚ := invAtOne A
  let iA2 : PowerSeries ℚ := invAtOne A2
  let iU : PowerSeries ℚ := invAtOne U
  let iV : PowerSeries ℚ := invAtOne V
  have hA2 : PowerSeries.constantCoeff A2 = 1 := by
    simp [A2, PowerSeries.constantCoeff_subst_X_pow, hA]
  have hAi : A * iA = 1 := invAtOne_mul A hA
  have hAiL : iA * A = 1 := invAtOne_mul_left A hA
  have hA2i : A2 * iA2 = 1 := invAtOne_mul A2 hA2
  have hA2iL : iA2 * A2 = 1 := invAtOne_mul_left A2 hA2
  have hUi : U * iU = 1 := invAtOne_mul U U_const
  have hUiL : iU * U = 1 := invAtOne_mul_left U U_const
  have hVi : V * iV = 1 := invAtOne_mul V V_const
  have hViL : iV * V = 1 := invAtOne_mul_left V V_const
  have hRatio : A * iA2 = V * iU := by
    calc
      A * iA2 = (iU * U) * (A * iA2) := by rw [hUiL, one_mul]
      _ = iU * (U * A) * iA2 := by ring
      _ = iU * (V * A2) * iA2 := by rw [hfunc]
      _ = iU * V * (A2 * iA2) := by ring
      _ = iU * V := by rw [hA2i, mul_one]
      _ = V * iU := by ring
  have hRatio' : A2 * iA = iV * U := by
    calc
      A2 * iA = (iV * V) * (A2 * iA) := by rw [hViL, one_mul]
      _ = iV * (V * A2) * iA := by ring
      _ = iV * (U * A) * iA := by rw [← hfunc]
      _ = iV * U * (A * iA) := by ring
      _ = iV * U := by rw [hAi, mul_one]
  have hiA2sub : iA.subst (PowerSeries.X ^ 2) = iA2 := by
    have hsub : A2 * iA.subst (PowerSeries.X ^ 2) = 1 := by
      change A.subst (PowerSeries.X ^ 2) * iA.subst (PowerSeries.X ^ 2) = 1
      rw [← PowerSeries.subst_mul
        (PowerSeries.HasSubst.X_pow (by norm_num : (2 : ℕ) ≠ 0)) A iA, hAi]
      change PowerSeries.subst (PowerSeries.X ^ 2) (1 : PowerSeries ℚ) = 1
      rw [show (1 : PowerSeries ℚ) = PowerSeries.C 1 by simp, PowerSeries.subst_C]
      simp
    calc
      iA.subst (PowerSeries.X ^ 2) =
          (iA2 * A2) * iA.subst (PowerSeries.X ^ 2) := by rw [hA2iL, one_mul]
      _ = iA2 * (A2 * iA.subst (PowerSeries.X ^ 2)) := by ring
      _ = iA2 := by rw [hsub, mul_one]
  have hderiv := derivative_functional_equation A hA hfunc
  have hDsubst : (logDerivative A).subst (PowerSeries.X ^ 2) =
      PowerSeries.X ^ 2 * (PowerSeries.derivative ℚ A).subst (PowerSeries.X ^ 2) * iA2 := by
    change PowerSeries.subst (PowerSeries.X ^ 2)
        (PowerSeries.X * PowerSeries.derivative ℚ A * invAtOne A) = _
    rw [PowerSeries.subst_mul
        (PowerSeries.HasSubst.X_pow (by norm_num : (2 : ℕ) ≠ 0))
        (PowerSeries.X * PowerSeries.derivative ℚ A) (invAtOne A),
      PowerSeries.subst_mul
        (PowerSeries.HasSubst.X_pow (by norm_num : (2 : ℕ) ≠ 0))
        PowerSeries.X (PowerSeries.derivative ℚ A),
      PowerSeries.subst_X (PowerSeries.HasSubst.X_pow (by norm_num : (2 : ℕ) ≠ 0)),
      hiA2sub]
  have hchain : PowerSeries.derivative ℚ A2 =
      (PowerSeries.derivative ℚ A).subst (PowerSeries.X ^ 2) * (2 * PowerSeries.X) := by
    rw [PowerSeries.derivative_subst (f := A) (g := PowerSeries.X ^ 2)
      (PowerSeries.HasSubst.X_pow (by norm_num : (2 : ℕ) ≠ 0)),
      PowerSeries.derivative_pow]
    simp
  have hRatioInv : iU * iA * V = iA2 := by
    calc
      iU * iA * V = V * iU * iA := by ring
      _ = (A * iA2) * iA := by rw [hRatio]
      _ = (A * iA) * iA2 := by ring
      _ = iA2 := by rw [hAi]; simp
  have hRatioInv' : iU * iA * A2 = iV := by
    calc
      iU * iA * A2 = iU * (A2 * iA) := by ring
      _ = iU * (iV * U) := by rw [hRatio']
      _ = iV := by calc
        iU * (iV * U) = iV * (iU * U) := by ring
        _ = iV := by rw [hUiL]; simp
  have hfactorLeft :
      PowerSeries.X * iU * iA * (U * PowerSeries.derivative ℚ A - A) +
        PowerSeries.X * iU =
      PowerSeries.X * PowerSeries.derivative ℚ A * iA := by
    have hterm1 : PowerSeries.X * iU * iA * (U * PowerSeries.derivative ℚ A) =
        PowerSeries.X * PowerSeries.derivative ℚ A * iA := by
      calc
        _ = PowerSeries.X * iA * PowerSeries.derivative ℚ A * (iU * U) := by ring
        _ = _ := by rw [hUiL]; ring
    have hterm2 : PowerSeries.X * iU * iA * A = PowerSeries.X * iU := by
      calc
        _ = PowerSeries.X * iU * (iA * A) := by ring
        _ = _ := by rw [hAiL]; simp
    rw [mul_sub, hterm1, hterm2]
    ring
  have hfactorRight :
      PowerSeries.X * iU * iA * (V * PowerSeries.derivative ℚ A2 + A2) =
        2 * (PowerSeries.X ^ 2 * (PowerSeries.derivative ℚ A).subst
          (PowerSeries.X ^ 2) * iA2) + PowerSeries.X * iV := by
    have hterm1 : PowerSeries.X * iU * iA * V * PowerSeries.derivative ℚ A2 =
        2 * (PowerSeries.X ^ 2 * (PowerSeries.derivative ℚ A).subst
          (PowerSeries.X ^ 2) * iA2) := by
      calc
        _ = PowerSeries.X * (iU * iA * V) * PowerSeries.derivative ℚ A2 := by ring
        _ = PowerSeries.X * iA2 * PowerSeries.derivative ℚ A2 := by rw [hRatioInv]
        _ = _ := by rw [hchain]; ring
    have hterm2 : PowerSeries.X * iU * iA * A2 = PowerSeries.X * iV := by
      rw [show PowerSeries.X * iU * iA * A2 =
        PowerSeries.X * (iU * iA * A2) by ring, hRatioInv']
    calc
      _ = PowerSeries.X * (iU * iA * V) * PowerSeries.derivative ℚ A2 +
            PowerSeries.X * (iU * iA * A2) := by ring
      _ = PowerSeries.X * iA2 * PowerSeries.derivative ℚ A2 + PowerSeries.X * iV := by
            rw [hRatioInv, hRatioInv']
      _ = _ := by rw [hchain]; ring
  calc
    logDerivative A = oddRational +
        2 * (logDerivative A).subst (PowerSeries.X ^ 2) := by
      rw [oddRational, hDsubst]
      change PowerSeries.X * PowerSeries.derivative ℚ A * iA =
        PowerSeries.X * iU + PowerSeries.X * iV +
          2 * (PowerSeries.X ^ 2 * (PowerSeries.derivative ℚ A).subst
            (PowerSeries.X ^ 2) * iA2)
      calc
        _ = PowerSeries.X * iU +
            PowerSeries.X * iU * iA * (U * PowerSeries.derivative ℚ A - A) := by
              calc
                _ = PowerSeries.X * iU * iA *
                    (U * PowerSeries.derivative ℚ A - A) + PowerSeries.X * iU :=
                      hfactorLeft.symm
                _ = _ := by rw [add_comm]
        _ = PowerSeries.X * iU +
            PowerSeries.X * iU * iA * (V * PowerSeries.derivative ℚ A2 + A2) := by
              rw [hderiv]
        _ = PowerSeries.X * iU + 2 * (PowerSeries.X ^ 2 *
            (PowerSeries.derivative ℚ A).subst (PowerSeries.X ^ 2) * iA2) +
            PowerSeries.X * iV := by rw [hfactorRight]; abel
        _ = _ := by abel

end

end LocalGeneratingFunction


open PowerSeries

namespace LocalConvolutionScratch

noncomputable section

theorem logDerivative_eq_weightSeries (A : PowerSeries ℚ)
    (hA : PowerSeries.constantCoeff A = 1)
    (hfunc : LocalGeneratingFunction.U * A = LocalGeneratingFunction.V *
      A.subst (PowerSeries.X ^ 2)) :
    LocalGeneratingFunction.logDerivative A = LocalDyadicWeight.weightSeries := by
  let D := LocalGeneratingFunction.logDerivative A
  let C := LocalDyadicWeight.weightSeries
  have hD : D = LocalGeneratingFunction.oddSeries +
      (2 : PowerSeries ℚ) * D.subst (PowerSeries.X ^ 2) := by
    have h := LocalGeneratingFunction.logDerivative_functional_equation A hA hfunc
    rw [LocalGeneratingFunction.oddRational_eq_oddSeries] at h
    simpa [D] using h
  have hC : C = LocalDyadicWeight.oddSeries +
      (2 : ℚ) • C.subst (PowerSeries.X ^ 2) := by
    simpa [C] using LocalDyadicWeight.weight_series_identity
  have hodd : LocalGeneratingFunction.oddSeries = LocalDyadicWeight.oddSeries := by
    apply PowerSeries.ext
    intro n
    simp [LocalGeneratingFunction.oddSeries, LocalDyadicWeight.oddSeries]
  rw [hodd] at hD
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have hD0 : PowerSeries.coeff 0 D = 0 := by
        simp [D, LocalGeneratingFunction.logDerivative]
      have hC0 : PowerSeries.coeff 0 C = 0 := by
        simp [C, LocalDyadicWeight.weightSeries,
          LocalDyadicWeight.coefficientSequence]
      rw [hD0, hC0]
    · have hDcoeff : PowerSeries.coeff n D =
          (if n % 2 = 1 then 2 else 0) +
            (if 2 ∣ n then 2 * PowerSeries.coeff (n / 2) D else 0) := by
        have h := congrArg (PowerSeries.coeff n) hD
        have htwo : (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) := by
          rw [PowerSeries.C_eq_algebraMap]
          exact (map_ofNat (algebraMap ℚ (PowerSeries ℚ)) 2).symm
        rw [htwo, map_add, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_subst_X_pow (by norm_num : 2 ≠ 0)] at h
        simpa [D, LocalDyadicWeight.oddSeries] using h
      have hCcoeff : PowerSeries.coeff n C =
          (if n % 2 = 1 then 2 else 0) +
            (if 2 ∣ n then 2 * PowerSeries.coeff (n / 2) C else 0) := by
        have h := congrArg (PowerSeries.coeff n) hC
        simpa [C, LocalDyadicWeight.oddSeries, map_add, map_smul,
          PowerSeries.coeff_subst_X_pow] using h
      by_cases he : 2 ∣ n
      · have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
        have ih' := ih (n / 2) hlt
        have hmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd he
        rw [hDcoeff, hCcoeff]
        have ih'' : PowerSeries.coeff (n / 2) D = PowerSeries.coeff (n / 2) C := by
          simpa [D, C] using ih'
        simp [hmod, he, ih'']
      · have hmod : n % 2 = 1 := by omega
        rw [hDcoeff, hCcoeff]
        simp [hmod, he]

/-- The logarithmic derivative identity turns the dyadic weight coefficients
into the convolution coefficients of the binary partition sequence. -/
theorem series_mul_weight_eq_derivative (A : PowerSeries ℚ)
    (hA : PowerSeries.constantCoeff A = 1)
    (hfunc : LocalGeneratingFunction.U * A = LocalGeneratingFunction.V *
      A.subst (PowerSeries.X ^ 2)) :
    A * LocalDyadicWeight.weightSeries =
      PowerSeries.X * PowerSeries.derivative ℚ A := by
  rw [← logDerivative_eq_weightSeries A hA hfunc]
  change A * (PowerSeries.X * PowerSeries.derivative ℚ A *
    LocalGeneratingFunction.invAtOne A) = _
  have hAi : A * LocalGeneratingFunction.invAtOne A = 1 :=
    LocalGeneratingFunction.invAtOne_mul A hA
  calc
    _ = (A * LocalGeneratingFunction.invAtOne A) *
        (PowerSeries.X * PowerSeries.derivative ℚ A) := by ring
    _ = _ := by rw [hAi]; simp

theorem coeff_series_mul_weight (A : PowerSeries ℚ)
    (hA : PowerSeries.constantCoeff A = 1)
    (hfunc : LocalGeneratingFunction.U * A = LocalGeneratingFunction.V *
      A.subst (PowerSeries.X ^ 2)) (n : ℕ) :
    PowerSeries.coeff n (A * LocalDyadicWeight.weightSeries) =
      (n : ℚ) * PowerSeries.coeff n A := by
  rw [series_mul_weight_eq_derivative A hA hfunc]
  cases n with
  | zero => simp
  | succ n =>
      have hX : PowerSeries.coeff (n + 1)
          (PowerSeries.X * PowerSeries.derivative ℚ A) =
          PowerSeries.coeff n (PowerSeries.derivative ℚ A) := by
        simpa [show 1 ≤ n + 1 by omega] using
          (PowerSeries.coeff_X_pow_mul' (PowerSeries.derivative ℚ A) 1 (n + 1))
      calc
        _ = PowerSeries.coeff n (PowerSeries.derivative ℚ A) := hX
        _ = PowerSeries.coeff (n + 1) A * (n + 1 : ℚ) := by
          rw [PowerSeries.coeff_derivative]
        _ = _ := by push_cast; ring

theorem a_series_mul_weight_coeff (n : ℕ) :
    PowerSeries.coeff n
      (LocalGeneratingFunction.series OMA.S_oeis_a000123.a *
        LocalDyadicWeight.weightSeries) =
      (n : ℚ) * (OMA.S_oeis_a000123.a n : ℚ) := by
  let A := LocalGeneratingFunction.series OMA.S_oeis_a000123.a
  have hzero : OMA.S_oeis_a000123.a 0 = 1 := by
    norm_num [OMA.S_oeis_a000123.a]
  have hfunc : LocalGeneratingFunction.U * A = LocalGeneratingFunction.V *
      A.subst (PowerSeries.X ^ 2) := by
    exact LocalGeneratingFunction.recurrence_series_identity
      OMA.S_oeis_a000123.a hzero
      OMA.S_oeis_a000123.a_half_recurrence
  have hconst : PowerSeries.constantCoeff A = 1 := by
    simp [A, LocalGeneratingFunction.series, PowerSeries.constantCoeff_mk, hzero]
  have h := coeff_series_mul_weight A hconst hfunc n
  simpa [A, LocalGeneratingFunction.series] using h

end

end LocalConvolutionScratch


open scoped BigOperators

namespace LocalSampling

def partialSum (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, f j

def samples (f : ℕ → ℕ) (n w : ℕ) : ℕ :=
  w * ∑ j ∈ Finset.range (n / w), f (n % w + w * j)

def directSamples (f : ℕ → ℕ) (n w : ℕ) : ℕ :=
  w * ∑ j ∈ Finset.range (n / w), f (n - w * (j + 1))

theorem directSamples_eq_samples (f : ℕ → ℕ) (n w : ℕ) (hw : 0 < w) :
    directSamples f n w = samples f n w := by
  unfold directSamples samples
  congr 1
  let q := n / w
  let r := n % w
  have hn : r + w * q = n := by
    dsimp [q, r]
    exact Nat.mod_add_div n w
  have hsum :
      (∑ j ∈ Finset.range q, f (n - w * (j + 1))) =
        ∑ j ∈ Finset.range q, f (r + w * (q - 1 - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjq : j + 1 ≤ q := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hmul : w * (q - (j + 1)) = w * q - w * (j + 1) := by
      rw [Nat.mul_sub_left_distrib]
    have hidx : n - w * (j + 1) = r + w * (q - 1 - j) := by
      have hsub : q - 1 - j = q - (j + 1) := by omega
      rw [hsub, hmul]
      rw [← hn]
      have hmulle := Nat.mul_le_mul_left w hjq
      omega
    exact congrArg f hidx
  rw [hsum]
  exact Finset.sum_range_reflect (fun j => f (r + w * j)) q

theorem sampling_bounds (f : ℕ → ℕ) (hf : Monotone f) (w : ℕ) (hw : 0 < w) :
    ∀ n, samples f n w ≤ partialSum f n ∧
      partialSum f n ≤ samples f n w + w * f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hsmall : n < w
      · constructor
        · simp [samples, hsmall, Nat.div_eq_of_lt]
        · simp [samples, partialSum, Nat.div_eq_of_lt hsmall]
          calc
            ∑ j ∈ Finset.range n, f j ≤ n * f n := by
              calc
                (∑ j ∈ Finset.range n, f j) ≤ ∑ _j ∈ Finset.range n, f n :=
                  Finset.sum_le_sum fun j hj => hf (Nat.le_of_lt (Finset.mem_range.mp hj))
                _ = n * f n := by simp [Nat.mul_comm]
            _ ≤ w * f n := Nat.mul_le_mul_right _ (Nat.le_of_lt hsmall)
      · have hwn : w ≤ n := Nat.le_of_not_gt hsmall
        have hdiv : n / w = (n - w) / w + 1 := Nat.div_eq_sub_div hw hwn
        have hmod : n % w = (n - w) % w := by
          calc
            n % w = ((n - w) + w) % w := by congr 1; omega
            _ = (n - w) % w := Nat.add_mod_right _ _
        have hlast : n % w + w * ((n - w) / w) = n - w := by
          rw [hmod]
          exact Nat.mod_add_div (n - w) w
        have hq : ∑ j ∈ Finset.range (n / w), f (n % w + w * j) =
            (∑ j ∈ Finset.range ((n - w) / w),
              f ((n - w) % w + w * j)) + f (n - w) := by
          rw [hdiv, Finset.sum_range_succ, hmod]
          congr 1
          exact congrArg f (Nat.mod_add_div (n - w) w)
        have hprefix : partialSum f n = partialSum f (n - w) +
            ∑ j ∈ Finset.range w, f ((n - w) + j) := by
          rw [partialSum, show n = (n - w) + w by omega, Finset.sum_range_add]
          simp [partialSum]
        have hblock_lower : w * f (n - w) ≤
            ∑ j ∈ Finset.range w, f ((n - w) + j) := by
          calc
            w * f (n - w) = ∑ _j ∈ Finset.range w, f (n - w) := by simp [Nat.mul_comm]
            _ ≤ ∑ j ∈ Finset.range w, f ((n - w) + j) :=
              Finset.sum_le_sum fun j hj => hf (Nat.le_add_right _ _)
        have hblock_upper :
            ∑ j ∈ Finset.range w, f ((n - w) + j) ≤ w * f n := by
          calc
            (∑ j ∈ Finset.range w, f ((n - w) + j)) ≤
                ∑ _j ∈ Finset.range w, f n :=
              Finset.sum_le_sum fun j hj => hf (by
                have := Finset.mem_range.mp hj
                omega)
            _ = w * f n := by simp [Nat.mul_comm]
        have hrec := ih (n - w) (by omega)
        constructor
        · change samples f n w ≤ partialSum f n
          unfold samples
          rw [hq, hprefix]
          have hrec' := hrec.1
          dsimp [samples] at hrec'
          rw [Nat.mul_add]
          exact Nat.add_le_add hrec' hblock_lower
        · change partialSum f n ≤ samples f n w + w * f n
          unfold samples
          rw [hq, hprefix]
          have hrec' := hrec.2
          dsimp [samples] at hrec'
          rw [Nat.mul_add]
          calc
            partialSum f (n - w) + ∑ j ∈ Finset.range w, f (n - w + j) ≤
                (samples f (n - w) w + w * f (n - w)) + w * f n :=
              Nat.add_le_add hrec' hblock_upper
            _ = _ := by congr 1 <;> rfl

theorem direct_sampling_bounds (f : ℕ → ℕ) (hf : Monotone f) (w : ℕ) (hw : 0 < w)
    (n : ℕ) :
    directSamples f n w ≤ partialSum f n ∧
      partialSum f n ≤ directSamples f n w + w * f n := by
  rw [directSamples_eq_samples f n w hw]
  exact sampling_bounds f hf w hw n


end LocalSampling


open PowerSeries
open scoped BigOperators
open Filter Topology

namespace LocalTotalWeightScratch

noncomputable section

def series (f : ℕ → ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (f n : ℚ)

def cumulative (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, OMA.S_oeis_a000123.a k

def dyadicLayer (n i : ℕ) : ℕ :=
  2 ^ i * ∑ j ∈ Finset.range (n / 2 ^ i),
    OMA.S_oeis_a000123.a (n - 2 ^ i * (j + 1))

theorem coeff_product_range (f : ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (series f * LocalDyadicWeight.weightSeries) =
      ∑ k ∈ Finset.range (n + 1),
        (f k : ℚ) * (LocalDyadicWeight.coefficientSequence (n - k) : ℚ) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [series, LocalDyadicWeight.weightSeries,
    LocalDyadicWeight.coefficientSequence]

theorem coefficientSequence_eq_dyadic_divisor_sum {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) :
    LocalDyadicWeight.coefficientSequence m =
      1 + ∑ i ∈ Finset.range (Nat.log 2 n + 1),
        if 2 ^ i ∣ m then 2 ^ i else 0 := by
  unfold LocalDyadicWeight.coefficientSequence
  rw [if_neg (by omega : m ≠ 0)]
  exact LocalDyadicWeight.coefficient_eq_dyadic_sum_of_le (by omega) hmn

theorem pointwise_weight_decomposition (f : ℕ → ℕ) {n k : ℕ} (hkn : k ≤ n) :
    (f k : ℚ) * (LocalDyadicWeight.coefficientSequence (n - k) : ℚ) =
      (if k < n then (f k : ℚ) else 0) +
        ∑ i ∈ Finset.range (Nat.log 2 n + 1),
          (2 ^ i : ℚ) *
            (if k < n ∧ 2 ^ i ∣ n - k then (f k : ℚ) else 0) := by
  by_cases hlt : k < n
  · have hm : 0 < n - k := by omega
    have hmn : n - k ≤ n := by omega
    rw [coefficientSequence_eq_dyadic_divisor_sum hm hmn]
    push_cast
    rw [mul_add, Finset.mul_sum]
    congr 1
    · simp [hlt]
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hdvd : 2 ^ i ∣ n - k
      · simp [hlt, hdvd]
        ring
      · simp [hlt, hdvd]
  · have heq : n - k = 0 := by omega
    simp [heq, LocalDyadicWeight.coefficientSequence, hlt]

theorem weighted_sum_decomposition (f : ℕ → ℕ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (f k : ℚ) * (LocalDyadicWeight.coefficientSequence (n - k) : ℚ)) =
      (∑ k ∈ Finset.range n, (f k : ℚ)) +
        ∑ i ∈ Finset.range (Nat.log 2 n + 1),
          (2 ^ i : ℚ) *
            ∑ k ∈ Finset.range (n + 1),
              if k < n ∧ 2 ^ i ∣ n - k then (f k : ℚ) else 0 := by
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        ((if k < n then (f k : ℚ) else 0) +
          ∑ i ∈ Finset.range (Nat.log 2 n + 1),
            (2 ^ i : ℚ) *
              (if k < n ∧ 2 ^ i ∣ n - k then (f k : ℚ) else 0)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact pointwise_weight_decomposition f (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = (∑ k ∈ Finset.range (n + 1), if k < n then (f k : ℚ) else 0) +
        ∑ k ∈ Finset.range (n + 1),
          ∑ i ∈ Finset.range (Nat.log 2 n + 1),
            (2 ^ i : ℚ) *
              (if k < n ∧ 2 ^ i ∣ n - k then (f k : ℚ) else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ k ∈ Finset.range n, (f k : ℚ)) +
        ∑ i ∈ Finset.range (Nat.log 2 n + 1),
          ∑ k ∈ Finset.range (n + 1),
            (2 ^ i : ℚ) *
              (if k < n ∧ 2 ^ i ∣ n - k then (f k : ℚ) else 0) := by
          congr 1
          · rw [Finset.sum_range_succ]
            have hs : (∑ k ∈ Finset.range n,
                if k < n then (f k : ℚ) else 0) =
                ∑ k ∈ Finset.range n, (f k : ℚ) := by
              apply Finset.sum_congr rfl
              intro k hk
              simp [Finset.mem_range.mp hk]
            rw [hs]
            simp
          · exact Finset.sum_comm
    _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.mul_sum]

theorem divisor_filter_reindex (f : ℕ → ℕ) (n w : ℕ) (hw : 0 < w) :
    (∑ k ∈ Finset.range (n + 1),
      if k < n ∧ w ∣ n - k then f k else 0) =
      ∑ j ∈ Finset.range (n / w), f (n - w * (j + 1)) := by
  classical
  let s := (Finset.range (n + 1)).filter (fun k => k < n ∧ w ∣ n - k)
  rw [← Finset.sum_filter]
  change (∑ k ∈ s, f k) = _
  refine Finset.sum_bij (fun k hk => (n - k) / w - 1) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    have hdiff : 0 < n - k := by omega
    have hlediv : w ≤ n - k := Nat.le_of_dvd hdiff hk'.2
    have hquot : 0 < (n - k) / w := Nat.div_pos hlediv hw
    have hle : (n - k) / w ≤ n / w := Nat.div_le_div_right (by omega)
    exact Finset.mem_range.mpr (by omega)
  · intro k₁ hk₁ k₂ hk₂ heq
    have h₁ := (Finset.mem_filter.mp hk₁).2
    have h₂ := (Finset.mem_filter.mp hk₂).2
    have hq₁ : 0 < (n - k₁) / w :=
      Nat.div_pos (Nat.le_of_dvd (by omega) h₁.2) hw
    have hq₂ : 0 < (n - k₂) / w :=
      Nat.div_pos (Nat.le_of_dvd (by omega) h₂.2) hw
    have hdiv₁ := Nat.mul_div_cancel' h₁.2
    have hdiv₂ := Nat.mul_div_cancel' h₂.2
    have hquot : (n - k₁) / w = (n - k₂) / w := by omega
    have hdiffeq : n - k₁ = n - k₂ := by
      calc
        n - k₁ = w * ((n - k₁) / w) := hdiv₁.symm
        _ = w * ((n - k₂) / w) := by rw [hquot]
        _ = n - k₂ := hdiv₂
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    have hprod : w * (j + 1) ≤ n := by
      calc
        w * (j + 1) ≤ w * (n / w) := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hj')
        _ = (n / w) * w := Nat.mul_comm _ _
        _ ≤ n := Nat.div_mul_le_self n w
    refine ⟨n - w * (j + 1), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        have hpos : 0 < w * (j + 1) := by positivity
        omega
      · constructor
        · have hpos : 0 < w * (j + 1) := by positivity
          omega
        · have hsub : n - (n - w * (j + 1)) = w * (j + 1) := by omega
          rw [hsub]
          exact dvd_mul_right w (j + 1)
    · have hsub : n - (n - w * (j + 1)) = w * (j + 1) := by omega
      rw [hsub, Nat.mul_div_cancel_left _ hw]
      omega
  · intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    have hdiv := Nat.mul_div_cancel' hk'.2
    have hq : 0 < (n - k) / w := Nat.div_pos (Nat.le_of_dvd (by omega) hk'.2) hw
    have hidx : ((n - k) / w - 1) + 1 = (n - k) / w := by omega
    have hprod : w * (((n - k) / w - 1) + 1) = n - k := by
      rw [hidx, Nat.mul_div_cancel' hk'.2]
    have hkval : n - w * (((n - k) / w - 1) + 1) = k := by omega
    rw [hkval]

theorem weighted_sum_samples (f : ℕ → ℕ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (f k : ℚ) * (LocalDyadicWeight.coefficientSequence (n - k) : ℚ)) =
      (∑ k ∈ Finset.range n, (f k : ℚ)) +
        ∑ i ∈ Finset.range (Nat.log 2 n + 1),
          (2 ^ i : ℚ) *
            ∑ j ∈ Finset.range (n / 2 ^ i),
              (f (n - 2 ^ i * (j + 1)) : ℚ) := by
  rw [weighted_sum_decomposition]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have h := divisor_filter_reindex f n (2 ^ i) (by positivity)
  have hcast :
      (∑ k ∈ Finset.range (n + 1),
        (if k < n ∧ 2 ^ i ∣ n - k then f k else 0) : ℚ) =
      ∑ j ∈ Finset.range (n / 2 ^ i), (f (n - 2 ^ i * (j + 1)) : ℚ) := by
    exact_mod_cast h
  simpa using congrArg (fun z : ℚ => (2 ^ i : ℚ) * z) hcast

theorem a_total_weight_identity_rat (n : ℕ) :
    (n : ℚ) * (OMA.S_oeis_a000123.a n : ℚ) =
      (∑ k ∈ Finset.range n, (OMA.S_oeis_a000123.a k : ℚ)) +
        ∑ i ∈ Finset.range (Nat.log 2 n + 1),
          (2 ^ i : ℚ) *
            ∑ j ∈ Finset.range (n / 2 ^ i),
              (OMA.S_oeis_a000123.a (n - 2 ^ i * (j + 1)) : ℚ) := by
  have hprod := coeff_product_range OMA.S_oeis_a000123.a n
  change PowerSeries.coeff n
    (LocalGeneratingFunction.series OMA.S_oeis_a000123.a *
      LocalDyadicWeight.weightSeries) = _ at hprod
  calc
    _ = PowerSeries.coeff n
        (LocalGeneratingFunction.series OMA.S_oeis_a000123.a *
          LocalDyadicWeight.weightSeries) :=
          (LocalConvolutionScratch.a_series_mul_weight_coeff n).symm
    _ = _ := by rw [hprod, weighted_sum_samples]

theorem a_total_weight_identity (n : ℕ) :
    n * OMA.S_oeis_a000123.a n =
      (∑ k ∈ Finset.range n, OMA.S_oeis_a000123.a k) +
        ∑ i ∈ Finset.range (Nat.log 2 n + 1),
          2 ^ i *
            ∑ j ∈ Finset.range (n / 2 ^ i),
              OMA.S_oeis_a000123.a (n - 2 ^ i * (j + 1)) := by
  exact_mod_cast a_total_weight_identity_rat n

theorem a_dyadic_sample_bounds (n i : ℕ) :
    dyadicLayer n i ≤ cumulative n ∧
      cumulative n ≤ dyadicLayer n i + 2 ^ i * OMA.S_oeis_a000123.a n := by
  simpa [dyadicLayer, cumulative, LocalSampling.directSamples,
      LocalSampling.partialSum] using
    LocalSampling.direct_sampling_bounds OMA.S_oeis_a000123.a
      OMA.S_oeis_a000123.a_monotone (2 ^ i) (by positivity) n

theorem total_weight_upper (n : ℕ) :
    n * OMA.S_oeis_a000123.a n ≤
      (Nat.log 2 n + 2) * cumulative n := by
  rw [a_total_weight_identity]
  calc
    cumulative n + ∑ i ∈ Finset.range (Nat.log 2 n + 1), dyadicLayer n i ≤
        cumulative n + ∑ _i ∈ Finset.range (Nat.log 2 n + 1), cumulative n := by
          exact Nat.add_le_add_left
            (Finset.sum_le_sum fun i hi => (a_dyadic_sample_bounds n i).1) _
    _ = _ := by simp [cumulative, Nat.mul_comm]; ring

theorem total_weight_lower_truncated (n t : ℕ)
    (ht : t ≤ Nat.log 2 n) :
    (Nat.log 2 n - t + 2) * cumulative n ≤
      n * OMA.S_oeis_a000123.a n +
        2 ^ (Nat.log 2 n - t + 1) * OMA.S_oeis_a000123.a n := by
  let L := Nat.log 2 n
  let q := L - t + 1
  have hq : 0 < q := by dsimp [q, L]; omega
  have hgeom : 1 + ∑ i ∈ Finset.range q, 2 ^ i = 2 ^ q := by
    have h := LocalDyadicWeight.one_add_sum_powers (q - 1)
    have hq1 : 1 ≤ q := hq
    simpa [Nat.sub_add_cancel hq1] using h
  have hlow :
      q * cumulative n ≤
        (∑ i ∈ Finset.range q, dyadicLayer n i) +
          (2 ^ q - 1) * OMA.S_oeis_a000123.a n := by
    calc
      q * cumulative n =
          ∑ i ∈ Finset.range q, cumulative n := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ Finset.range q,
          (dyadicLayer n i + 2 ^ i * OMA.S_oeis_a000123.a n) :=
            Finset.sum_le_sum fun i hi => (a_dyadic_sample_bounds n i).2
      _ = (∑ i ∈ Finset.range q, dyadicLayer n i) +
          (2 ^ q - 1) * OMA.S_oeis_a000123.a n := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul]
            congr 1
            have hsum : (∑ i ∈ Finset.range q, 2 ^ i) = 2 ^ q - 1 := by omega
            rw [hsum]
  have hqL : q ≤ L + 1 := by dsimp [q, L]; omega
  have hsubset :
      (∑ i ∈ Finset.range q, dyadicLayer n i) ≤
        ∑ i ∈ Finset.range (L + 1), dyadicLayer n i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hqL)
    intro i hi hnot
    exact Nat.zero_le _
  have htotal := a_total_weight_identity n
  dsimp [cumulative, dyadicLayer] at htotal hlow hsubset ⊢
  dsimp [L, q] at hlow hsubset ⊢
  have hmain :
      (Nat.log 2 n - t + 1) *
          (∑ k ∈ Finset.range n, OMA.S_oeis_a000123.a k) ≤
        n * OMA.S_oeis_a000123.a n +
          (2 ^ (Nat.log 2 n - t + 1) - 1) * OMA.S_oeis_a000123.a n := by
    omega
  have herr :
      (2 ^ (Nat.log 2 n - t + 1) - 1) * OMA.S_oeis_a000123.a n ≤
        2 ^ (Nat.log 2 n - t + 1) * OMA.S_oeis_a000123.a n := by
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hcoef : Nat.log 2 n - t + 2 = (Nat.log 2 n - t + 1) + 1 := by omega
  rw [hcoef, Nat.add_mul]
  omega

theorem truncated_error_scale_bound {n t : ℕ} (hn : n ≠ 0)
    (ht : t ≤ Nat.log 2 n) :
    2 ^ t * 2 ^ (Nat.log 2 n - t + 1) ≤ 2 * n := by
  calc
    2 ^ t * 2 ^ (Nat.log 2 n - t + 1) =
        2 ^ (Nat.log 2 n + 1) := by
          rw [← pow_add]
          congr 1
          omega
    _ = 2 ^ Nat.log 2 n * 2 := by rw [pow_succ]
    _ ≤ 2 * n := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hn)

theorem tendsto_nat_log_two :
    Filter.Tendsto (fun n : ℕ => Nat.log 2 n) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro m
  filter_upwards [Filter.eventually_ge_atTop (2 ^ m)] with n hn
  exact Nat.le_log_of_pow_le (by norm_num) hn

theorem tendsto_real_log_div_nat_log_two :
    Filter.Tendsto (fun n : ℕ => Real.log n / (Nat.log 2 n : ℝ))
      Filter.atTop (𝓝 (Real.log 2)) := by
  let L : ℕ → ℝ := fun n => (Nat.log 2 n : ℝ)
  have hL : Filter.Tendsto L Filter.atTop Filter.atTop := by
    change Filter.Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ)) Filter.atTop Filter.atTop
    exact tendsto_natCast_atTop_atTop.comp tendsto_nat_log_two
  have hInv := hL.inv_tendsto_atTop
  have hlower : Filter.Tendsto (fun _ : ℕ => Real.log 2)
      Filter.atTop (𝓝 (Real.log 2)) := tendsto_const_nhds
  have hupper : Filter.Tendsto
      (fun n : ℕ => Real.log 2 + Real.log 2 * (L n)⁻¹)
      Filter.atTop (𝓝 (Real.log 2)) := by
    have hmul := hInv.const_mul (Real.log 2)
    simpa [mul_comm] using hlower.add hmul
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : n ≠ 0 := by omega
    have hpow : 2 ^ 1 ≤ n := by norm_num at hn ⊢; omega
    have hLposNat : 0 < Nat.log 2 n := by
      have hle := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
      omega
    have hLpos : 0 < L n := by dsimp [L]; exact_mod_cast hLposNat
    have hpowloNat := Nat.pow_log_le_self 2 hn0
    have hpowhiNat := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have hpowlo : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast hpowloNat
    have hpowhi : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
      exact_mod_cast hpowhiNat
    have hloglo := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 n) hpowlo
    have hloghi := Real.log_lt_log (by positivity : (0 : ℝ) < (n : ℝ)) hpowhi
    have hlo : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
      simpa [Real.log_pow, mul_comm] using hloglo
    have hhi : Real.log n < ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
      simpa [Real.log_pow, Nat.cast_add, Nat.cast_one] using hloghi
    apply (le_div_iff₀ hLpos).2
    nlinarith [hlo]
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : n ≠ 0 := by omega
    have hpow : 2 ^ 1 ≤ n := by norm_num at hn ⊢; omega
    have hLposNat : 0 < Nat.log 2 n := by
      have hle := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
      omega
    have hLpos : 0 < L n := by dsimp [L]; exact_mod_cast hLposNat
    have hpowhiNat := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have hpowhi : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
      exact_mod_cast hpowhiNat
    have hloghi := Real.log_lt_log (by positivity : (0 : ℝ) < (n : ℝ)) hpowhi
    have hhi : Real.log n < ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
      simpa [Real.log_pow, Nat.cast_add, Nat.cast_one] using hloghi
    apply (div_le_iff₀ hLpos).2
    have heq :
        (Real.log 2 + Real.log 2 * (L n)⁻¹) * L n =
          ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
      dsimp [L]
      field_simp [ne_of_gt hLpos]
    rw [heq]
    exact hhi.le

theorem cumulative_ratio_lower_bound {n : ℕ} (hn : 2 ≤ n) :
    Real.log n / ((Nat.log 2 n : ℝ) + 2) ≤
      Real.log n * (cumulative n : ℝ) /
        ((n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ)) := by
  have hLposNat : 0 < Nat.log 2 n := by
    have hpow : 2 ^ 1 ≤ n := by norm_num at hn ⊢; omega
    have h := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
    omega
  have hLpos : 0 < (Nat.log 2 n : ℝ) := by exact_mod_cast hLposNat
  have hTpos : 0 < (n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ) := by
    have ha := OMA.S_oeis_a000123.a_pos n
    positivity
  have hlognonneg : 0 ≤ Real.log n := by
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hupper := total_weight_upper n
  have hupperR : (n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ) ≤
      ((Nat.log 2 n : ℝ) + 2) * (cumulative n : ℝ) := by
    exact_mod_cast hupper
  rw [div_le_div_iff₀ (by positivity : 0 < (Nat.log 2 n : ℝ) + 2) hTpos]
  nlinarith [hupperR, hlognonneg]

theorem cumulative_ratio_upper_bound {n t : ℕ} (hn : 2 ≤ n)
    (ht : t ≤ Nat.log 2 n) :
    Real.log n * (cumulative n : ℝ) /
        ((n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ)) ≤
      Real.log n * (1 + 2 / (2 ^ t : ℝ)) /
        ((Nat.log 2 n - t + 2 : ℕ) : ℝ) := by
  let e : ℕ := 2 ^ (Nat.log 2 n - t + 1)
  let d : ℕ := Nat.log 2 n - t + 2
  have hn0 : n ≠ 0 := by omega
  have hLposNat : 0 < Nat.log 2 n := by
    have hpow : 2 ^ 1 ≤ n := by norm_num at hn ⊢; omega
    have h := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
    omega
  have hLpos : 0 < (Nat.log 2 n : ℝ) := by exact_mod_cast hLposNat
  have hdposNat : 0 < d := by dsimp [d]; omega
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hdposNat
  have hTpos : 0 < (n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ) := by
    have ha := OMA.S_oeis_a000123.a_pos n
    positivity
  have hApos : 0 < (OMA.S_oeis_a000123.a n : ℝ) := by
    exact_mod_cast OMA.S_oeis_a000123.a_pos n
  have hlognonneg : 0 ≤ Real.log n := by
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlower := total_weight_lower_truncated n t ht
  have hlowerR : (d : ℝ) * (cumulative n : ℝ) ≤
      (n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ) +
        (e : ℝ) * (OMA.S_oeis_a000123.a n : ℝ) := by
    dsimp [d, e]
    exact_mod_cast hlower
  have hscale := truncated_error_scale_bound hn0 ht
  have hscaleR : (2 ^ t : ℝ) * (e : ℝ) ≤ 2 * (n : ℝ) := by
    dsimp [e]
    exact_mod_cast hscale
  have hErrRatio :
      ((e : ℝ) * (OMA.S_oeis_a000123.a n : ℝ)) /
          ((n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ)) ≤
        2 / (2 ^ t : ℝ) := by
    rw [div_le_div_iff₀ hTpos (by positivity : 0 < (2 ^ t : ℝ))]
    nlinarith [mul_le_mul_of_nonneg_right hscaleR hApos.le]
  have hErr :
      (e : ℝ) * (OMA.S_oeis_a000123.a n : ℝ) ≤
        (2 / (2 ^ t : ℝ)) *
          ((n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ)) :=
    (div_le_iff₀ hTpos).1 hErrRatio
  have hSratio :
      (cumulative n : ℝ) /
          ((n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ)) ≤
        (1 + 2 / (2 ^ t : ℝ)) / (d : ℝ) := by
    rw [div_le_div_iff₀ hTpos hdpos]
    nlinarith [hlowerR, hErr]
  calc
    _ = Real.log n *
        ((cumulative n : ℝ) /
          ((n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ))) := by ring
    _ ≤ Real.log n * ((1 + 2 / (2 ^ t : ℝ)) / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hSratio hlognonneg
    _ = _ := by dsimp [d]; ring

theorem tendsto_nat_log_shift_ratio (t : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => (Nat.log 2 n : ℝ) /
        ((Nat.log 2 n - t + 2 : ℕ) : ℝ))
      Filter.atTop (𝓝 1) := by
  let L : ℕ → ℝ := fun n => (Nat.log 2 n : ℝ)
  have hL : Filter.Tendsto L Filter.atTop Filter.atTop := by
    change Filter.Tendsto (fun n : ℕ => (Nat.log 2 n : ℝ)) Filter.atTop Filter.atTop
    exact tendsto_natCast_atTop_atTop.comp tendsto_nat_log_two
  have hInv := hL.inv_tendsto_atTop
  let c : ℝ := 2 - t
  have hc : Filter.Tendsto (fun n : ℕ => 1 + c * (L n)⁻¹)
      Filter.atTop (𝓝 1) := by
    have hsmall : Filter.Tendsto (fun n : ℕ => c * (L n)⁻¹)
        Filter.atTop (𝓝 0) := by
      simpa using hInv.const_mul c
    simpa using tendsto_const_nhds.add hsmall
  have hratio : Filter.Tendsto (fun n : ℕ => (1 + c * (L n)⁻¹)⁻¹)
      Filter.atTop (𝓝 1) := by
    simpa using hc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun n : ℕ =>
      (Nat.log 2 n : ℝ) / ((Nat.log 2 n - t + 2 : ℕ) : ℝ)) =ᶠ[Filter.atTop]
      (fun n : ℕ => (1 + c * (L n)⁻¹)⁻¹) := by
    filter_upwards [Filter.eventually_ge_atTop (max 2 (2 ^ t))] with n hn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hpow : 2 ^ t ≤ n := le_trans (le_max_right _ _) hn
    have htlog : t ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hpow
    have hLposNat : 0 < Nat.log 2 n := by
      have hpow' : 2 ^ 1 ≤ n := by norm_num at hn2 ⊢; omega
      have h := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow'
      omega
    have hLpos : 0 < L n := by dsimp [L]; exact_mod_cast hLposNat
    have hcast : ((Nat.log 2 n - t + 2 : ℕ) : ℝ) = L n - t + 2 := by
      dsimp [L]
      simp [Nat.cast_sub htlog]
    have hdenNat : 0 < Nat.log 2 n - t + 2 := by omega
    have hdenPos : 0 < ((Nat.log 2 n - t + 2 : ℕ) : ℝ) := by
      exact_mod_cast hdenNat
    rw [hcast] at hdenPos
    have hden : L n - t + 2 ≠ 0 := ne_of_gt hdenPos
    dsimp [c]
    rw [hcast]
    dsimp [L]
    field_simp [ne_of_gt hLpos]
    <;> ring_nf
  exact Filter.Tendsto.congr' heq.symm hratio

def lowerEnvelope (n : ℕ) : ℝ :=
  Real.log n / ((Nat.log 2 n : ℝ) + 2)

def upperEnvelope (t n : ℕ) : ℝ :=
  Real.log n * (1 + 2 / (2 ^ t : ℝ)) /
    ((Nat.log 2 n - t + 2 : ℕ) : ℝ)

theorem tendsto_lower_envelope :
    Filter.Tendsto lowerEnvelope Filter.atTop (𝓝 (Real.log 2)) := by
  have hprod := tendsto_real_log_div_nat_log_two.mul (tendsto_nat_log_shift_ratio 0)
  have hlim : Filter.Tendsto
      (fun n : ℕ =>
        (Real.log n / (Nat.log 2 n : ℝ)) *
          ((Nat.log 2 n : ℝ) /
            ((Nat.log 2 n - 0 + 2 : ℕ) : ℝ)))
      Filter.atTop (𝓝 (Real.log 2)) := by
    simpa using hprod
  have heq : lowerEnvelope =ᶠ[Filter.atTop]
      (fun n : ℕ =>
        (Real.log n / (Nat.log 2 n : ℝ)) *
          ((Nat.log 2 n : ℝ) /
            ((Nat.log 2 n - 0 + 2 : ℕ) : ℝ))) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hpow : 2 ^ 1 ≤ n := by norm_num at hn ⊢; omega
    have hLpos : 0 < Nat.log 2 n := by
      have h := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
      omega
    have hden : ((Nat.log 2 n - 0 + 2 : ℕ) : ℝ) =
        (Nat.log 2 n : ℝ) + 2 := by simp
    have hLposR : 0 < (Nat.log 2 n : ℝ) := by exact_mod_cast hLpos
    rw [lowerEnvelope, hden]
    field_simp [ne_of_gt hLposR]
  exact Filter.Tendsto.congr' heq.symm hlim

theorem tendsto_upper_envelope (t : ℕ) :
    Filter.Tendsto (upperEnvelope t) Filter.atTop
      (𝓝 ((1 + 2 / (2 ^ t : ℝ)) * Real.log 2)) := by
  let c : ℝ := 1 + 2 / (2 ^ t : ℝ)
  have hprod := tendsto_real_log_div_nat_log_two.mul (tendsto_nat_log_shift_ratio t)
  have hlim : Filter.Tendsto
      (fun n : ℕ => c * ((Real.log n / (Nat.log 2 n : ℝ)) *
          ((Nat.log 2 n : ℝ) /
            ((Nat.log 2 n - t + 2 : ℕ) : ℝ))))
      Filter.atTop (𝓝 (c * Real.log 2)) := by
    simpa [c, mul_comm, mul_left_comm, mul_assoc] using hprod.const_mul c
  have heq : upperEnvelope t =ᶠ[Filter.atTop]
      (fun n : ℕ => c * ((Real.log n / (Nat.log 2 n : ℝ)) *
          ((Nat.log 2 n : ℝ) /
            ((Nat.log 2 n - t + 2 : ℕ) : ℝ)))) := by
    filter_upwards [Filter.eventually_ge_atTop (max 2 (2 ^ t))] with n hn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hpow : 2 ^ t ≤ n := le_trans (le_max_right _ _) hn
    have htlog : t ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hpow
    have hpow' : 2 ^ 1 ≤ n := by norm_num at hn2 ⊢; omega
    have hLpos : 0 < Nat.log 2 n := by
      have h := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow'
      omega
    have hdenPos : 0 < ((Nat.log 2 n - t + 2 : ℕ) : ℝ) := by
      have h : 0 < Nat.log 2 n - t + 2 := by omega
      exact_mod_cast h
    have hLposR : (Nat.log 2 n : ℝ) ≠ 0 := by
      exact ne_of_gt (by exact_mod_cast hLpos)
    rw [upperEnvelope]
    dsimp [c]
    field_simp [hLposR, ne_of_gt hdenPos]
  have h := Filter.Tendsto.congr' heq.symm hlim
  simpa [c] using h

def upperLimit (t : ℕ) : ℝ :=
  (1 + 2 / (2 ^ t : ℝ)) * Real.log 2

theorem tendsto_upperLimit :
    Filter.Tendsto upperLimit Filter.atTop (𝓝 (Real.log 2)) := by
  have hpow : Filter.Tendsto (fun t : ℕ => (1 / 2 : ℝ) ^ t)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : Filter.Tendsto (fun t : ℕ => 2 / (2 ^ t : ℝ))
      Filter.atTop (𝓝 0) := by
    have heq : (fun t : ℕ => 2 / (2 ^ t : ℝ)) =
        fun t : ℕ => 2 * (1 / 2 : ℝ) ^ t := by
      funext t
      simp [div_eq_mul_inv, one_div_pow]
    rw [heq]
    simpa using hpow.const_mul 2
  have hcoef : Filter.Tendsto (fun t : ℕ => 1 + 2 / (2 ^ t : ℝ))
      Filter.atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hsmall
  have h := hcoef.const_mul (Real.log 2)
  change Filter.Tendsto (fun t : ℕ =>
    (1 + 2 / (2 ^ t : ℝ)) * Real.log 2) Filter.atTop (𝓝 (Real.log 2))
  simpa [mul_comm] using h

def cumulativeRatio (n : ℕ) : ℝ :=
  Real.log n * (cumulative n : ℝ) /
    ((n : ℝ) * (OMA.S_oeis_a000123.a n : ℝ))

theorem tendsto_cumulativeRatio :
    Filter.Tendsto cumulativeRatio Filter.atTop (𝓝 (Real.log 2)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hLower := (tendsto_order.1 tendsto_lower_envelope).1 a ha
    filter_upwards [hLower, Filter.eventually_ge_atTop (2 : ℕ)] with n hlow hn
    have hbound := cumulative_ratio_lower_bound hn
    exact lt_of_lt_of_le hlow (by simpa [lowerEnvelope, cumulativeRatio] using hbound)
  · intro b hb
    have hChoose := (tendsto_order.1 tendsto_upperLimit).2 b hb
    obtain ⟨t, ht⟩ := hChoose.exists
    have hUpper := (tendsto_order.1 (tendsto_upper_envelope t)).2 b ht
    filter_upwards [hUpper, Filter.eventually_ge_atTop (max 2 (2 ^ t))] with n hup hn
    have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
    have hpow : 2 ^ t ≤ n := le_trans (le_max_right _ _) hn
    have htlog : t ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hpow
    have hbound := cumulative_ratio_upper_bound hn2 htlog
    exact lt_of_le_of_lt
      (by simpa [cumulativeRatio, upperEnvelope, Nat.cast_add,
        Nat.cast_sub htlog] using hbound) hup

theorem exact_main_from_total_weight :
    type_of% @OMA.S_oeis_a000123.main := by
  have hsum : Filter.Tendsto
      (fun n : ℕ => Real.log n / (n : ℝ) *
        ((∑ k ∈ Finset.range n, OMA.S_oeis_a000123.a k : ℕ) : ℝ) /
          (OMA.S_oeis_a000123.a n : ℝ))
      Filter.atTop (𝓝 (Real.log 2)) := by
    have hEq : (fun n : ℕ => Real.log n / (n : ℝ) *
        ((∑ k ∈ Finset.range n, OMA.S_oeis_a000123.a k : ℕ) : ℝ) /
          (OMA.S_oeis_a000123.a n : ℝ)) =ᶠ[Filter.atTop] cumulativeRatio := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
      have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
      have haR : (OMA.S_oeis_a000123.a n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (OMA.S_oeis_a000123.a_pos n))
      simp [cumulativeRatio, cumulative]
      field_simp [hnR, haR]
      <;> ring
    exact Filter.Tendsto.congr' hEq.symm tendsto_cumulativeRatio
  exact OMA.S_oeis_a000123.main_of_cumulative_sum_limit hsum

end

end LocalTotalWeightScratch


theorem OMA.solution : type_of% @OMA.S_oeis_a000123.main := by
  exact LocalTotalWeightScratch.exact_main_from_total_weight
