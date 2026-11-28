import OMAStatements.S_oeis_a126693

/-!
Proof idea: for `p ≤ 10000`, primality is trial division by `m ≤ 100`. With this fast predicate
`Q` the kernel counts `253` terms below `9941` in chunks of `500` (`decide +kernel`), so
`Nat.nth_count` gives `a(254) = 9941`; the range `9942..10000` contains no term, and for
`p > 10000` we get `10000 - p = 0`, which is not prime.
-/

namespace OMA.P_oeis_a126693

/-- Trial division up to `100`, enough for numbers at most `10000`. -/
def FP (p : ℕ) : Prop := 2 ≤ p ∧ ∀ m < 101, 2 ≤ m → m * m ≤ p → p % m ≠ 0

instance : DecidablePred FP := fun p =>
  inferInstanceAs (Decidable (2 ≤ p ∧ ∀ m < 101, 2 ≤ m → m * m ≤ p → p % m ≠ 0))

open OMA.S_oeis_a126693 in
instance : DecidablePred IsTerm := fun p =>
  inferInstanceAs (Decidable (p.Prime ∧ (10000 - p).Prime))

/-- Fast decidable version of the A126693 predicate. -/
def Q (p : ℕ) : Prop := FP p ∧ FP (10000 - p)

instance : DecidablePred Q := fun p => inferInstanceAs (Decidable (FP p ∧ FP (10000 - p)))

lemma prime_iff_FP {p : ℕ} (hp : p ≤ 10000) : p.Prime ↔ FP p := by
  rw [Nat.prime_def_le_sqrt]
  unfold FP
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m _ hm hmm => ?_⟩
    have := h m hm (Nat.le_sqrt.mpr hmm)
    rwa [Nat.dvd_iff_mod_eq_zero] at this
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hms => ?_⟩
    have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
    have hm101 : m < 101 := by nlinarith
    rw [Nat.dvd_iff_mod_eq_zero]
    exact h m hm101 hm hmm

open OMA.S_oeis_a126693 in
lemma isTerm_iff_Q {p : ℕ} (hp : p ≤ 10000) : IsTerm p ↔ Q p := by
  unfold IsTerm Q
  rw [prime_iff_FP hp, prime_iff_FP (by omega)]

open OMA.S_oeis_a126693 in
lemma count_eq (n : ℕ) (hn : n ≤ 10001) : Nat.count IsTerm n = Nat.count Q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, Nat.count_succ, ih (by omega)]
    by_cases h : Q n
    · rw [if_pos h, if_pos ((isTerm_iff_Q (by omega)).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((isTerm_iff_Q (by omega)).mp h'))]

lemma c500 : Nat.count Q 500 = 15 := by
  decide +kernel

lemma c1000 : Nat.count Q 1000 = 33 := by
  rw [show (1000 : ℕ) = 500 + 500 from rfl, Nat.count_add, c500]
  decide +kernel

lemma c1500 : Nat.count Q 1500 = 48 := by
  rw [show (1500 : ℕ) = 1000 + 500 from rfl, Nat.count_add, c1000]
  decide +kernel

lemma c2000 : Nat.count Q 2000 = 58 := by
  rw [show (2000 : ℕ) = 1500 + 500 from rfl, Nat.count_add, c1500]
  decide +kernel

lemma c2500 : Nat.count Q 2500 = 75 := by
  rw [show (2500 : ℕ) = 2000 + 500 from rfl, Nat.count_add, c2000]
  decide +kernel

lemma c3000 : Nat.count Q 3000 = 84 := by
  rw [show (3000 : ℕ) = 2500 + 500 from rfl, Nat.count_add, c2500]
  decide +kernel

lemma c3500 : Nat.count Q 3500 = 95 := by
  rw [show (3500 : ℕ) = 3000 + 500 from rfl, Nat.count_add, c3000]
  decide +kernel

lemma c4000 : Nat.count Q 4000 = 105 := by
  rw [show (4000 : ℕ) = 3500 + 500 from rfl, Nat.count_add, c3500]
  decide +kernel

lemma c4500 : Nat.count Q 4500 = 119 := by
  rw [show (4500 : ℕ) = 4000 + 500 from rfl, Nat.count_add, c4000]
  decide +kernel

lemma c5000 : Nat.count Q 5000 = 127 := by
  rw [show (5000 : ℕ) = 4500 + 500 from rfl, Nat.count_add, c4500]
  decide +kernel

lemma c5500 : Nat.count Q 5500 = 135 := by
  rw [show (5500 : ℕ) = 5000 + 500 from rfl, Nat.count_add, c5000]
  decide +kernel

lemma c6000 : Nat.count Q 6000 = 149 := by
  rw [show (6000 : ℕ) = 5500 + 500 from rfl, Nat.count_add, c5500]
  decide +kernel

lemma c6500 : Nat.count Q 6500 = 159 := by
  rw [show (6500 : ℕ) = 6000 + 500 from rfl, Nat.count_add, c6000]
  decide +kernel

lemma c7000 : Nat.count Q 7000 = 170 := by
  rw [show (7000 : ℕ) = 6500 + 500 from rfl, Nat.count_add, c6500]
  decide +kernel

lemma c7500 : Nat.count Q 7500 = 179 := by
  rw [show (7500 : ℕ) = 7000 + 500 from rfl, Nat.count_add, c7000]
  decide +kernel

lemma c8000 : Nat.count Q 8000 = 196 := by
  rw [show (8000 : ℕ) = 7500 + 500 from rfl, Nat.count_add, c7500]
  decide +kernel

lemma c8500 : Nat.count Q 8500 = 206 := by
  rw [show (8500 : ℕ) = 8000 + 500 from rfl, Nat.count_add, c8000]
  decide +kernel

lemma c9000 : Nat.count Q 9000 = 221 := by
  rw [show (9000 : ℕ) = 8500 + 500 from rfl, Nat.count_add, c8500]
  decide +kernel

lemma c9500 : Nat.count Q 9500 = 239 := by
  rw [show (9500 : ℕ) = 9000 + 500 from rfl, Nat.count_add, c9000]
  decide +kernel

lemma c9941 : Nat.count Q 9941 = 253 := by
  rw [show (9941 : ℕ) = 9500 + 441 from rfl, Nat.count_add, c9500]
  decide +kernel

end OMA.P_oeis_a126693

open OMA.S_oeis_a126693 OMA.P_oeis_a126693 in
theorem OMA.solution : type_of% @OMA.S_oeis_a126693.main := by
  have h9941 : IsTerm 9941 := ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_⟩
  · have hc : Nat.count IsTerm 9941 = 253 := by rw [count_eq 9941 (by norm_num), c9941]
    rw [← hc]
    exact Nat.nth_count h9941
  · intro p hp
    by_contra hlt
    rcases Nat.lt_or_ge 10000 p with h | h
    · have : 10000 - p = 0 := by omega
      exact Nat.not_prime_zero (this ▸ hp.2)
    · have hq := (isTerm_iff_Q h).mp hp
      have hall : ∀ k < 59, ¬ Q (9942 + k) := by decide +kernel
      have := hall (p - 9942) (by omega)
      rw [show 9942 + (p - 9942) = p by omega] at this
      exact this hq
