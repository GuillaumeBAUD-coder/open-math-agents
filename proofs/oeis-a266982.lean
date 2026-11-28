import OMAStatements.S_oeis_a266982

-- Credit: @LoopsGod

namespace OMA.HurtProof

open OMA.S_oeis_a266982

/-- `j` is the horizontal offset from the left edge of the displayed row. -/
private def rowBit (b : Bool) (j : ℤ) : Bool :=
  if j = 0 ∨ j = 1 then !b else b

private lemma rule81_bool (l c r : Bool) :
    rule81 l c r = (!r && (l || !c)) := by
  cases l <;> cases c <;> cases r <;> decide

private lemma step_pair (b : Bool) (j : ℤ) :
    rule81 (rowBit b (j - 1)) (rowBit b j) (rowBit b (j + 1)) =
      rowBit (!b) (j + 1) := by
  cases b <;> simp only [rule81_bool, rowBit] <;>
    split_ifs <;> first | rfl | omega

private lemma first_row (i : ℤ) : cell 1 i = rowBit true (i + 1) := by
  simp only [cell, rule81_bool, rowBit]
  by_cases h₁ : i = -1 <;> by_cases h₂ : i = 0 <;> by_cases h₃ : i = 1 <;>
    simp_all

/-- At every positive time just two adjacent sites differ from the background. -/
private lemma cell_pattern (t : ℕ) (ht : 0 < t) (i : ℤ) :
    cell t i = rowBit (decide (t % 2 = 1)) (i + (t : ℤ)) := by
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    by_cases h : t = 0
    · subst t
      simpa using first_row i
    have hpos : 0 < t := by omega
    have hflip : decide ((t + 1) % 2 = 1) = !decide (t % 2 = 1) := by
      by_cases ho : t % 2 = 1
      · have hn : (t + 1) % 2 = 0 := by omega
        simp [hn, ho]
      · have hn : (t + 1) % 2 = 1 := by omega
        simp [hn, ho]
    rw [cell, ih hpos, ih hpos, ih hpos, hflip, Nat.cast_succ]
    rw [show i - 1 + (t : ℤ) = i + t - 1 by ring,
      show i + 1 + (t : ℤ) = i + t + 1 by ring, ← add_assoc]
    exact step_pair (decide (t % 2 = 1)) (i + (t : ℤ))

private lemma term_parity (n : ℕ) (hn : 0 < n) :
    a n = (n - 2).sqrt % 2 := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sqrt_pos.mpr hn).ne'
  let j := n - (t + 1) ^ 2
  have hlow : (t + 1) ^ 2 ≤ n := by simpa only [ht, Nat.succ_eq_add_one] using Nat.sqrt_le' n
  have hhigh : n < (t + 1 + 1) ^ 2 := by
    simpa only [ht, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' n
  have hsum : n = (t + 1) ^ 2 + j := by dsimp [j]; omega
  have ha : a n = (rowBit (decide ((t + 1) % 2 = 1)) (j : ℤ)).toNat := by
    simp only [a, ht, cell_pattern (t + 1) (by omega), sub_add_cancel, j]
  rw [ha]
  by_cases hfront : j < 2
  · have hs : (n - 2).sqrt = t := by
      symm
      apply Nat.eq_sqrt'.2
      constructor
      · by_cases hz : t = 0
        · simp [hz]
        · have htpos : 1 ≤ t := by omega
          have hsq : t ^ 2 + 2 ≤ n := by nlinarith only [hlow, htpos]
          omega
      · have hpos : 0 < (t + 1) ^ 2 := by positivity
        omega
    rw [hs]
    have hj : (j : ℤ) = 0 ∨ (j : ℤ) = 1 := by omega
    unfold rowBit
    rw [if_pos hj]
    by_cases ho : (t + 1) % 2 = 1 <;> simp [ho] <;> omega
  · have hs : (n - 2).sqrt = t + 1 := by
      symm
      apply Nat.eq_sqrt'.2
      omega
    rw [hs]
    have hj : ¬ ((j : ℤ) = 0 ∨ (j : ℤ) = 1) := by omega
    unfold rowBit
    rw [if_neg hj]
    by_cases ho : (t + 1) % 2 = 1
    · simp [ho]
    · simp [ho]
      omega

open Finset

/-- Count the positive lattice points under the hyperbola by exchanging their coordinates.
Only the points on the diagonal contribute to the parity. -/
theorem floor_sum_parity (m : ℕ) :
    (∑ i ∈ Ioc 0 m, m / i) % 2 = m.sqrt % 2 := by
  let pairs := ((Ioc 0 m) ×ˢ (Ioc 0 m)).filter (fun x => x.1 * x.2 ≤ m)
  let upper := pairs.filter (fun x => x.1 < x.2)
  let lower := pairs.filter (fun x => x.2 < x.1)
  let diag := pairs.filter (fun x => x.1 = x.2)
  have hcount : pairs.card = ∑ i ∈ Ioc 0 m, m / i := by
    simp only [pairs, card_eq_sum_ones, sum_filter, sum_product]
    apply sum_congr rfl
    intro i hi
    have hi' := (mem_Ioc.mp hi).1
    have hrow : (Ioc 0 m).filter (fun j => i * j ≤ m) = Ioc 0 (m / i) := by
      ext j
      simp only [mem_filter, mem_Ioc]
      have hdiv : j ≤ m/i ↔ i*j ≤ m := by
        simpa only [Nat.mul_comm j i] using (Nat.le_div_iff_mul_le hi' : j ≤ m/i ↔ j*i ≤ m)
      constructor
      · rintro ⟨⟨hj, _⟩, hprod⟩
        exact ⟨hj, hdiv.mpr hprod⟩
      · rintro ⟨hj, hj'⟩
        exact ⟨⟨hj, hj'.trans (Nat.div_le_self _ _)⟩, hdiv.mp hj'⟩
    change (∑ j ∈ Ioc 0 m, if i * j ≤ m then 1 else 0) = m / i
    rw [← sum_filter, hrow]
    simp
  have hsplit : upper.card + lower.card + diag.card = pairs.card := by
    simp only [upper, lower, diag, card_eq_sum_ones, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    rintro ⟨i, j⟩ _
    dsimp only
    split_ifs <;> omega
  have hswap : upper.card = lower.card := by
    apply card_equiv (Equiv.prodComm ℕ ℕ)
    rintro ⟨i, j⟩
    simp [upper, lower, pairs, Nat.mul_comm, and_comm, and_assoc, and_left_comm]
  have hdiag : diag.card = m.sqrt := by
    calc
      diag.card = (Ioc 0 m.sqrt).card := by
        apply card_bij' (fun x _ => x.1) (fun i _ => (i, i))
        case hi =>
          rintro ⟨i, j⟩ hij
          simp only [diag, pairs, mem_filter, mem_product, mem_Ioc] at hij ⊢
          obtain ⟨⟨⟨⟨hi, _⟩, _⟩, hp⟩, rfl⟩ := hij
          exact ⟨hi, Nat.le_sqrt.mpr hp⟩
        case hj =>
          intro i hi
          obtain ⟨hi, hs⟩ := mem_Ioc.mp hi
          have hm := hs.trans (Nat.sqrt_le_self m)
          simp [diag, pairs, hi, hm, Nat.le_sqrt.mp hs]
        case left_inv =>
          rintro ⟨i, j⟩ hij
          have heq := (mem_filter.mp hij).2
          change i = j at heq
          cases heq
          rfl
        case right_inv =>
          intro i hi
          rfl
      _ = m.sqrt := by simp
  omega

end OMA.HurtProof

theorem OMA.solution : type_of% @OMA.S_oeis_a266982.main := by
  constructor
  · decide
  · intro n hn
    exact (OMA.HurtProof.term_parity n hn).trans (OMA.HurtProof.floor_sum_parity (n - 2)).symm
