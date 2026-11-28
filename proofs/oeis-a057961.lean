import OMAStatements.S_oeis_a057961

namespace OMA.P_oeis_a057961
open Finset OMA.S_oeis_a057961

theorem inf : (Set.ofPred IsSumTwoSq).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun x : ℕ => x ^ 2)
  · intro x y h; exact Nat.pow_left_injective (by norm_num) h
  · intro x; exact ⟨x, 0, by simp⟩

open Classical in
theorem key (N : ℕ) : Nat.card {p : ℕ × ℕ // p.1 ^ 2 + p.2 ^ 2 ≤ Nat.nth IsSumTwoSq N} = A000592 N := by
  set R := Nat.nth IsSumTwoSq N with hR
  have hle : ∀ x y : ℕ, x ^ 2 + y ^ 2 ≤ R → x < R + 1 ∧ y < R + 1 := by
    intro x y h
    have hx : x ≤ x ^ 2 := Nat.le_self_pow (by norm_num) x
    have hy : y ≤ y ^ 2 := Nat.le_self_pow (by norm_num) y
    omega
  set s := (range (R + 1) ×ˢ range (R + 1)).filter (fun p : ℕ × ℕ => p.1 ^ 2 + p.2 ^ 2 ≤ R) with hs
  have h1 : Nat.card {p : ℕ × ℕ // p.1 ^ 2 + p.2 ^ 2 ≤ R} = s.card := by
    apply Nat.subtype_card
    rintro ⟨x, y⟩
    simp only [hs, mem_filter, mem_product, mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hle x y h, h⟩⟩
  rw [h1, A000592]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => Nat.count IsSumTwoSq (p.1 ^ 2 + p.2 ^ 2))
    (t := range (N + 1))]
  · refine sum_congr rfl fun j hj => ?_
    symm
    apply Nat.subtype_card
    rintro ⟨x, y⟩
    simp only [hs, mem_filter, mem_product, mem_range]
    constructor
    · rintro ⟨⟨_, h⟩, hc⟩
      rw [← hc]; exact (Nat.nth_count ⟨x, y, rfl⟩).symm
    · intro h
      have hj' : j ≤ N := by have := mem_range.mp hj; omega
      have hzR : x ^ 2 + y ^ 2 ≤ R := by rw [h, hR]; exact (Nat.nth_strictMono inf).monotone hj'
      exact ⟨⟨hle x y hzR, hzR⟩, by rw [h]; exact Nat.count_nth_of_infinite inf j⟩
  · rintro ⟨x, y⟩ hp
    have hp2 : x ^ 2 + y ^ 2 ≤ R := (mem_filter.mp hp).2
    have := Nat.count_monotone IsSumTwoSq hp2
    rw [hR, Nat.count_nth_of_infinite inf] at this
    exact mem_range.mpr (by simpa using Nat.lt_succ_of_le this)

theorem quad (R : ℕ) : Nat.card {p : ℤ × ℤ // 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ (R : ℤ)}
    = Nat.card {p : ℕ × ℕ // p.1 ^ 2 + p.2 ^ 2 ≤ R} := by
  symm
  apply Nat.card_congr
  refine ⟨fun p => ⟨((p.1.1 : ℤ), (p.1.2 : ℤ)), by
      refine ⟨by positivity, by positivity, ?_⟩
      show ((p.1.1 : ℤ)) ^ 2 + ((p.1.2 : ℤ)) ^ 2 ≤ (R : ℤ)
      exact_mod_cast p.2⟩,
    fun q => ⟨(q.1.1.toNat, q.1.2.toNat), by
      obtain ⟨⟨u, v⟩, hu, hv, h⟩ := q
      simp only at hu hv h ⊢
      have e1 : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg hu
      have e2 : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg hv
      have : ((u.toNat ^ 2 + v.toNat ^ 2 : ℕ) : ℤ) ≤ R := by push_cast; rw [e1, e2]; exact h
      exact_mod_cast this⟩, ?_, ?_⟩
  · rintro ⟨⟨x, y⟩, h⟩; simp
  · rintro ⟨⟨u, v⟩, hu, hv, h⟩
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    exact ⟨Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hv⟩

end OMA.P_oeis_a057961

open Finset OMA.S_oeis_a057961 OMA.P_oeis_a057961 in
theorem OMA.solution : type_of% @OMA.S_oeis_a057961.main := by
  intro n _
  rw [quadrantCount, radiusSq, quad, key]

