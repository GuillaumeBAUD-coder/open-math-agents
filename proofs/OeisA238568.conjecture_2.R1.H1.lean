import OMAReductions.R_OeisA238568_conjecture_2_R1
import Mathlib.Tactic

/-!
Step `OeisA238568.conjecture_2.R1.H1`: for every `n` in `{2, 3, 4, 8, 10, 24, 41}` the count
`a n = 1`, where `a n` counts the `1 <= k < n` with `n ^ 2 - pi(k * n)` prime.

The cases `n = 2, 3, 4` are the proved lemmas `OeisA238568.a_2`, `a_3`, `a_4` upstream;
`n = 8, 10, 24` go through by `decide`.  For `n = 41` a monolithic `decide` is out of reach,
so the forty values `pi(k * 41)` are built incrementally: a split lemma expresses
`pi(m + c) - pi(m)` as the cardinality of the primes in the interval `(m, m + c]`,
each 41-wide block is decided separately, and the block evaluations use a
bounded trial-division decidability instance (valid on `42 <= p <= 1640`, where a
composite has a prime factor at most 40).  Finally the filter over `Ico 1 41` is shown
to be the singleton `{10}`, so its cardinality is 1.
-/

open Finset

namespace L7H1

/-- On the range `42 <= p <= 1640`, primality amounts to trial division up to `40`. -/
theorem prime_iff_40 {p : ℕ} (h42 : 42 ≤ p) (h1640 : p ≤ 1640) :
    Nat.Prime p ↔ ∀ m, 2 ≤ m → m ≤ 40 → ¬ m ∣ p := by
  have h1681 : p < 1681 := by omega
  have hsqrt : Nat.sqrt p < 41 := Nat.sqrt_lt'.2 h1681
  constructor
  · intro hp m hm2 hm40 hmp
    exact (Nat.prime_def_lt'.1 hp).2 m hm2 (by omega) hmp
  · intro h
    exact Nat.prime_def_le_sqrt.2 ⟨by omega, fun m hm2 hms hmp => h m hm2 (by omega) hmp⟩

/-- Decidability of `Nat.Prime p` by trial division up to 40 inside `42 <= p <= 1640`,
falling back to the standard instance elsewhere. -/
def l7dec (p : ℕ) : Decidable (Nat.Prime p) :=
  if h : 42 ≤ p ∧ p ≤ 1640 then decidable_of_iff' _ (prime_iff_40 h.1 h.2)
  else Nat.decidablePrime p

/-- `Finset.filter` with `Nat.Prime` does not depend on the decidability instance used. -/
theorem filter_prime_ext (I₁ I₂ : ∀ p, Decidable (Nat.Prime p)) (s : Finset ℕ) :
    @Finset.filter ℕ Nat.Prime I₁ s = @Finset.filter ℕ Nat.Prime I₂ s := by
  ext x
  simp only [Finset.mem_filter]

/-- The prime counting function splits over intervals:
`pi (m + c) = pi m + #{p in (m, m + c] | prime}`. -/
theorem pi_split (m c : ℕ) :
    Nat.primeCounting (m + c)
      = Nat.primeCounting m
        + #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (m + 1) (m + c + 1))) := by
  have hico : Finset.Ico 0 (m + c + 1)
      = Finset.Ico 0 (m + 1) ∪ Finset.Ico (m + 1) (m + c + 1) :=
    (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega)).symm
  have hd : Disjoint (@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico 0 (m + 1)))
      (@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (m + 1) (m + c + 1))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx hx'
    omega
  have e1 : Nat.primeCounting (m + c)
      = #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico 0 (m + c + 1))) := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range,
      Finset.range_eq_Ico]
    exact congrArg Finset.card (filter_prime_ext _ _ _)
  have e2 : #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico 0 (m + 1)))
      = Nat.primeCounting m := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_range,
      Finset.range_eq_Ico]
    exact congrArg Finset.card (filter_prime_ext _ _ _)
  rw [e1, hico, Finset.filter_union, Finset.card_union_eq_card_add_card.mpr hd, e2]

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem pi_1 : Nat.primeCounting (1 * 41) = 13 := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_1 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (1 * 41 + 1) (1 * 41 + 41 + 1)))
      = 9 := by decide

theorem pi_2 : Nat.primeCounting (2 * 41) = 22 := by
  have h := pi_split (1 * 41) 41
  rw [pi_1, block_1] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_2 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (2 * 41 + 1) (2 * 41 + 41 + 1)))
      = 8 := by decide

theorem pi_3 : Nat.primeCounting (3 * 41) = 30 := by
  have h := pi_split (2 * 41) 41
  rw [pi_2, block_2] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_3 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (3 * 41 + 1) (3 * 41 + 41 + 1)))
      = 8 := by decide

theorem pi_4 : Nat.primeCounting (4 * 41) = 38 := by
  have h := pi_split (3 * 41) 41
  rw [pi_3, block_3] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_4 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (4 * 41 + 1) (4 * 41 + 41 + 1)))
      = 8 := by decide

theorem pi_5 : Nat.primeCounting (5 * 41) = 46 := by
  have h := pi_split (4 * 41) 41
  rw [pi_4, block_4] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_5 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (5 * 41 + 1) (5 * 41 + 41 + 1)))
      = 7 := by decide

theorem pi_6 : Nat.primeCounting (6 * 41) = 53 := by
  have h := pi_split (5 * 41) 41
  rw [pi_5, block_5] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_6 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (6 * 41 + 1) (6 * 41 + 41 + 1)))
      = 8 := by decide

theorem pi_7 : Nat.primeCounting (7 * 41) = 61 := by
  have h := pi_split (6 * 41) 41
  rw [pi_6, block_6] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_7 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (7 * 41 + 1) (7 * 41 + 41 + 1)))
      = 5 := by decide

theorem pi_8 : Nat.primeCounting (8 * 41) = 66 := by
  have h := pi_split (7 * 41) 41
  rw [pi_7, block_7] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_8 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (8 * 41 + 1) (8 * 41 + 41 + 1)))
      = 7 := by decide

theorem pi_9 : Nat.primeCounting (9 * 41) = 73 := by
  have h := pi_split (8 * 41) 41
  rw [pi_8, block_8] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_9 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (9 * 41 + 1) (9 * 41 + 41 + 1)))
      = 7 := by decide

theorem pi_10 : Nat.primeCounting (10 * 41) = 80 := by
  have h := pi_split (9 * 41) 41
  rw [pi_9, block_9] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_10 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (10 * 41 + 1) (10 * 41 + 41 + 1)))
      = 7 := by decide

theorem pi_11 : Nat.primeCounting (11 * 41) = 87 := by
  have h := pi_split (10 * 41) 41
  rw [pi_10, block_10] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_11 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (11 * 41 + 1) (11 * 41 + 41 + 1)))
      = 7 := by decide

theorem pi_12 : Nat.primeCounting (12 * 41) = 94 := by
  have h := pi_split (11 * 41) 41
  rw [pi_11, block_11] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_12 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (12 * 41 + 1) (12 * 41 + 41 + 1)))
      = 5 := by decide

theorem pi_13 : Nat.primeCounting (13 * 41) = 99 := by
  have h := pi_split (12 * 41) 41
  rw [pi_12, block_12] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_13 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (13 * 41 + 1) (13 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_14 : Nat.primeCounting (14 * 41) = 105 := by
  have h := pi_split (13 * 41) 41
  rw [pi_13, block_13] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_14 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (14 * 41 + 1) (14 * 41 + 41 + 1)))
      = 7 := by decide

theorem pi_15 : Nat.primeCounting (15 * 41) = 112 := by
  have h := pi_split (14 * 41) 41
  rw [pi_14, block_14] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_15 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (15 * 41 + 1) (15 * 41 + 41 + 1)))
      = 7 := by decide

theorem pi_16 : Nat.primeCounting (16 * 41) = 119 := by
  have h := pi_split (15 * 41) 41
  rw [pi_15, block_15] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_16 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (16 * 41 + 1) (16 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_17 : Nat.primeCounting (17 * 41) = 125 := by
  have h := pi_split (16 * 41) 41
  rw [pi_16, block_16] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_17 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (17 * 41 + 1) (17 * 41 + 41 + 1)))
      = 5 := by decide

theorem pi_18 : Nat.primeCounting (18 * 41) = 130 := by
  have h := pi_split (17 * 41) 41
  rw [pi_17, block_17] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_18 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (18 * 41 + 1) (18 * 41 + 41 + 1)))
      = 7 := by decide

theorem pi_19 : Nat.primeCounting (19 * 41) = 137 := by
  have h := pi_split (18 * 41) 41
  rw [pi_18, block_18] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_19 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (19 * 41 + 1) (19 * 41 + 41 + 1)))
      = 4 := by decide

theorem pi_20 : Nat.primeCounting (20 * 41) = 141 := by
  have h := pi_split (19 * 41) 41
  rw [pi_19, block_19] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_20 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (20 * 41 + 1) (20 * 41 + 41 + 1)))
      = 8 := by decide

theorem pi_21 : Nat.primeCounting (21 * 41) = 149 := by
  have h := pi_split (20 * 41) 41
  rw [pi_20, block_20] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_21 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (21 * 41 + 1) (21 * 41 + 41 + 1)))
      = 5 := by decide

theorem pi_22 : Nat.primeCounting (22 * 41) = 154 := by
  have h := pi_split (21 * 41) 41
  rw [pi_21, block_21] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_22 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (22 * 41 + 1) (22 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_23 : Nat.primeCounting (23 * 41) = 160 := by
  have h := pi_split (22 * 41) 41
  rw [pi_22, block_22] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_23 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (23 * 41 + 1) (23 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_24 : Nat.primeCounting (24 * 41) = 166 := by
  have h := pi_split (23 * 41) 41
  rw [pi_23, block_23] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_24 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (24 * 41 + 1) (24 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_25 : Nat.primeCounting (25 * 41) = 172 := by
  have h := pi_split (24 * 41) 41
  rw [pi_24, block_24] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_25 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (25 * 41 + 1) (25 * 41 + 41 + 1)))
      = 7 := by decide

theorem pi_26 : Nat.primeCounting (26 * 41) = 179 := by
  have h := pi_split (25 * 41) 41
  rw [pi_25, block_25] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_26 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (26 * 41 + 1) (26 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_27 : Nat.primeCounting (27 * 41) = 185 := by
  have h := pi_split (26 * 41) 41
  rw [pi_26, block_26] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_27 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (27 * 41 + 1) (27 * 41 + 41 + 1)))
      = 4 := by decide

theorem pi_28 : Nat.primeCounting (28 * 41) = 189 := by
  have h := pi_split (27 * 41) 41
  rw [pi_27, block_27] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_28 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (28 * 41 + 1) (28 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_29 : Nat.primeCounting (29 * 41) = 195 := by
  have h := pi_split (28 * 41) 41
  rw [pi_28, block_28] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_29 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (29 * 41 + 1) (29 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_30 : Nat.primeCounting (30 * 41) = 201 := by
  have h := pi_split (29 * 41) 41
  rw [pi_29, block_29] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_30 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (30 * 41 + 1) (30 * 41 + 41 + 1)))
      = 4 := by decide

theorem pi_31 : Nat.primeCounting (31 * 41) = 205 := by
  have h := pi_split (30 * 41) 41
  rw [pi_30, block_30] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_31 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (31 * 41 + 1) (31 * 41 + 41 + 1)))
      = 9 := by decide

theorem pi_32 : Nat.primeCounting (32 * 41) = 214 := by
  have h := pi_split (31 * 41) 41
  rw [pi_31, block_31] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_32 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (32 * 41 + 1) (32 * 41 + 41 + 1)))
      = 3 := by decide

theorem pi_33 : Nat.primeCounting (33 * 41) = 217 := by
  have h := pi_split (32 * 41) 41
  rw [pi_32, block_32] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_33 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (33 * 41 + 1) (33 * 41 + 41 + 1)))
      = 4 := by decide

theorem pi_34 : Nat.primeCounting (34 * 41) = 221 := by
  have h := pi_split (33 * 41) 41
  rw [pi_33, block_33] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_34 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (34 * 41 + 1) (34 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_35 : Nat.primeCounting (35 * 41) = 227 := by
  have h := pi_split (34 * 41) 41
  rw [pi_34, block_34] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_35 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (35 * 41 + 1) (35 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_36 : Nat.primeCounting (36 * 41) = 233 := by
  have h := pi_split (35 * 41) 41
  rw [pi_35, block_35] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_36 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (36 * 41 + 1) (36 * 41 + 41 + 1)))
      = 7 := by decide

theorem pi_37 : Nat.primeCounting (37 * 41) = 240 := by
  have h := pi_split (36 * 41) 41
  rw [pi_36, block_36] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_37 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (37 * 41 + 1) (37 * 41 + 41 + 1)))
      = 5 := by decide

theorem pi_38 : Nat.primeCounting (38 * 41) = 245 := by
  have h := pi_split (37 * 41) 41
  rw [pi_37, block_37] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_38 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (38 * 41 + 1) (38 * 41 + 41 + 1)))
      = 6 := by decide

theorem pi_39 : Nat.primeCounting (39 * 41) = 251 := by
  have h := pi_split (38 * 41) 41
  rw [pi_38, block_38] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem block_39 :
    #(@Finset.filter ℕ Nat.Prime l7dec (Finset.Ico (39 * 41 + 1) (39 * 41 + 41 + 1)))
      = 8 := by decide

theorem pi_40 : Nat.primeCounting (40 * 41) = 259 := by
  have h := pi_split (39 * 41) 41
  rw [pi_39, block_39] at h
  norm_num at h ⊢
  exact h

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem a8 : OeisA238568.a 8 = 1 := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem a10 : OeisA238568.a 10 = 1 := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 8000000 in
theorem a24 : OeisA238568.a 24 = 1 := by decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 8000000 in
theorem a41 : OeisA238568.a 41 = 1 := by
  have hfilter :
      (Finset.Ico 1 41).filter (fun k => Nat.Prime (41 ^ 2 - Nat.primeCounting (k * 41)))
        = {10} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      interval_cases k
      all_goals simp only [pi_1, pi_2, pi_3, pi_4, pi_5, pi_6, pi_7, pi_8, pi_9, pi_10, pi_11, pi_12, pi_13, pi_14, pi_15, pi_16, pi_17, pi_18, pi_19, pi_20, pi_21, pi_22, pi_23, pi_24, pi_25, pi_26, pi_27, pi_28, pi_29, pi_30, pi_31, pi_32, pi_33, pi_34, pi_35, pi_36, pi_37, pi_38, pi_39, pi_40] at hp
      all_goals first
        | rfl
        | exact absurd hp (by norm_num)
    · intro hk
      subst hk
      constructor
      · constructor
        · norm_num
        · norm_num
      · rw [pi_10]
        norm_num
  unfold OeisA238568.a
  rw [hfilter, card_singleton]

end L7H1

theorem OMA.solution : OMA.R_OeisA238568_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact OeisA238568.a_2
  · exact OeisA238568.a_3
  · exact OeisA238568.a_4
  · exact L7H1.a8
  · exact L7H1.a10
  · exact L7H1.a24
  · exact L7H1.a41
