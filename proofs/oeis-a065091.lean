import OMAStatements.S_oeis_a065091

open Finset OMA.S_oeis_a065091

namespace OMA.A065091

private lemma reducePower (p u t : ℕ) [Fact p.Prime] (ht : 0 < t)
    (x : ZMod p) : x ^ ((p - 1) * u + t) = x ^ t := by
  by_cases hx : x = 0
  · rw [hx, zero_pow (by omega : (p - 1) * u + t ≠ 0), zero_pow ht.ne']
  · rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]

private lemma sumResidues (p t : ℕ) [Fact p.Prime] (ht : t < p - 1) :
    (∑ j ∈ range p, (j : ZMod p) ^ t) = 0 := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  calc
    _ = ∑ x : ZMod p, x ^ t := by
      refine sum_bij (fun j _ => (j : ZMod p)) (fun _ _ => mem_univ _) ?_ ?_ ?_
      · intro i hi j hj h
        simpa [ZMod.val_natCast_of_lt (mem_range.mp hi),
          ZMod.val_natCast_of_lt (mem_range.mp hj)] using congrArg ZMod.val h
      · intro x _
        exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
      · intro j _
        rfl
    _ = 0 := FiniteField.sum_pow_lt_card_sub_one (ZMod p) t (by simpa using ht)

private lemma sumBlocks (p t : ℕ) [Fact p.Prime] (ht : t < p - 1) (b : ℕ) :
    (∑ j ∈ range (b * p), (j : ZMod p) ^ t) = 0 := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.succ_mul, sum_range_add, ih]
      simpa [Nat.cast_add, Nat.cast_mul] using sumResidues p t ht

private lemma shortSum (p b u t : ℕ) [Fact p.Prime]
    (ht : 0 < t) (ht' : t < p - 1) (hmod : b * p = 198151)
    (hexp : (p - 1) * u + t = 198150)
    (htail : (∑ j ∈ range 12, ((198139 + j : ℕ) : ZMod p) ^ t) = 13) :
    (∑ j ∈ Icc (1 : ℕ) 198138, (j : ZMod p) ^ 198150) = (198138 : ℕ) := by
  have hwhole := sumBlocks p t ht' b
  rw [hmod, show (198151 : ℕ) = 198139 + 12 by decide, sum_range_add, htail] at hwhole
  have hzero : (198151 : ZMod p) = 0 := by
    change ((198151 : ℕ) : ZMod p) = 0
    rw [← hmod, Nat.cast_mul, ZMod.natCast_self, mul_zero]
  have htarget : (198138 : ZMod p) + 13 = 0 := by
    convert hzero using 1
    norm_num
  have hprefix : (∑ j ∈ range 198139, (j : ZMod p) ^ t) = 198138 :=
    add_right_cancel (hwhole.trans htarget.symm)
  rw [← hexp]
  simp_rw [reducePower p u t ht]
  have hcut := sum_range_add_sum_Ico (fun j : ℕ => (j : ZMod p) ^ t)
    (show 1 ≤ 198139 by decide)
  rw [show Ico 1 198139 = (Icc 1 198138 : Finset ℕ) by
        ext j
        simp only [mem_Ico, mem_Icc]
        omega,
      sum_range_one, Nat.cast_zero, zero_pow ht.ne', zero_add] at hcut
  exact hcut.trans hprefix

private lemma witnessCongruence : Cond 198139 198151 := by
  have ht₁ : (∑ j ∈ range 12, ((198139 + j : ℕ) : ZMod 19) ^ 6) = 13 := by
    decide
  have ht₂ : (∑ j ∈ range 12, ((198139 + j : ℕ) : ZMod 10429) ^ 18) = 13 := by
    decide
  have hp₁ : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hp₂ : Fact (Nat.Prime 10429) := ⟨by norm_num⟩
  have h₁ := shortSum 19 10429 11008 6 (by decide) (by decide)
    (by decide) (by decide) ht₁
  have h₂ := shortSum 10429 19 19 18 (by decide) (by decide)
    (by decide) (by decide) ht₂
  have hc : Nat.Coprime 19 10429 := by decide
  change (∑ j ∈ Icc 1 (198139 - 1), j ^ (198151 - 1)) ≡ 198139 - 1 [MOD 198151]
  rw [show (198139 : ℕ) - 1 = 198138 by decide,
    show (198151 : ℕ) - 1 = 198150 by decide, show (198151 : ℕ) = 19 * 10429 by decide]
  apply (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
  constructor
  · apply (ZMod.natCast_eq_natCast_iff _ _ 19).mp
    push_cast
    exact h₁
  · apply (ZMod.natCast_eq_natCast_iff _ _ 10429).mp
    push_cast
    exact h₂

end OMA.A065091

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a065091.main) := by
  intro h
  have hp : Nat.Prime 198139 := by norm_num
  let i := Nat.count Nat.Prime 198139
  have hi : Nat.nth Nat.Prime i = 198139 := Nat.nth_count hp
  have hprev : Nat.nth Nat.Prime (i + 1 - 1) = 198139 := by simpa using hi
  have hlarger : 198139 < Nat.nth Nat.Prime (i + 1) := by
    rw [← hi]
    exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self i)
  have hnext : 198151 < Nat.nth Nat.Prime (i + 1) := by
    by_contra! hle
    have hprime := Nat.prime_nth_prime (i + 1)
    generalize Nat.nth Nat.Prime (i + 1) = q at hle hlarger hprime
    interval_cases q <;> norm_num at hprime
  have hall := h (i + 1) (Nat.succ_pos i)
  dsimp only at hall
  rw [hprev] at hall
  exact hall.2 198151 (by decide) (by decide) hnext OMA.A065091.witnessCongruence
