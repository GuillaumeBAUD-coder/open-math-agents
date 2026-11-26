import FormalConjectures.ErdosProblems.«711»

/-!
# Reduction of Erdős Problem 711(i) by prime factors of the divisors

The divisors at most `n` split according to whether every prime factor is at most
`Nat.sqrt n`. In the second class each divisor has a unique prime factor above
this threshold. Assign the two classes to adjacent intervals, then absorb the
constant factor in the interval length into a vanishing exponent.
-/

namespace OMA.R_Erdos711_erdos_711_parts_i_R2

open Asymptotics Filter Erdos711

/-- Match the divisors all of whose prime factors are at most the square-root threshold. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, ∃ L : ℕ,
    (L : ℝ) ≤ (n : ℝ) ^ (1 + ε) ∧ ∃ a : Fin n → ℕ,
    Set.InjOn a {i | ∀ p : ℕ, p.Prime → p ∣ (i.val + 1) → p ≤ Nat.sqrt n} ∧
    ∀ i : Fin n, (∀ p : ℕ, p.Prime → p ∣ (i.val + 1) → p ≤ Nat.sqrt n) →
      m < a i ∧ a i < m + L ∧ (i.val + 1) ∣ a i

/-- Match the divisors with a prime factor above the square-root threshold. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, ∃ L : ℕ,
    (L : ℝ) ≤ (n : ℝ) ^ (1 + ε) ∧ ∃ a : Fin n → ℕ,
    Set.InjOn a {i | ∃ p : ℕ, p.Prime ∧ p ∣ (i.val + 1) ∧ Nat.sqrt n < p} ∧
    ∀ i : Fin n, (∃ p : ℕ, p.Prime ∧ p ∣ (i.val + 1) ∧ Nat.sqrt n < p) →
      m < a i ∧ a i < m + L ∧ (i.val + 1) ∣ a i

lemma product_gt_of_sqrt_lt {n p q : ℕ} (hp : Nat.sqrt n < p) (hq : Nat.sqrt n < q) :
    n < p * q := by
  calc
    n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
    _ ≤ p * q := by
      rw [pow_two]
      exact Nat.mul_le_mul (Nat.succ_le_of_lt hp) (Nat.succ_le_of_lt hq)

lemma large_prime_unique {n d p q : ℕ} (hd : d ≤ n) (hd0 : 0 < d)
    (hp : p.Prime) (hq : q.Prime) (hpD : p ∣ d) (hqD : q ∣ d)
    (hpN : Nat.sqrt n < p) (hqN : Nat.sqrt n < q) :
    p = q := by
  by_contra hne
  have hle := Nat.le_of_dvd hd0 (Nat.Prime.dvd_mul_of_dvd_ne hne hp hq hpD hqD)
  exact (not_lt_of_ge (hle.trans hd)) (product_gt_of_sqrt_lt hpN hqN)

lemma cofactor_le_sqrt {n p a : ℕ} (hd : p * a ≤ n) (hp : Nat.sqrt n < p) :
    a ≤ Nat.sqrt n := by
  by_contra! ha
  exact (not_lt_of_ge hd) (product_gt_of_sqrt_lt hp ha)

theorem erdos711_diagonal :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ m, ∃ L,
      HasDivisibleDistinctTuple n m L ∧ (L : ℝ) ≤ (n : ℝ) ^ (1 + ε)) →
    (type_of% @Erdos711.erdos_711.parts.i) := by
  intro h
  let shortest (n m : ℕ) : ℕ := sInf { L | HasDivisibleDistinctTuple n m L }
  let uniform (n : ℕ) : ℕ := max n (sSup (Set.range (shortest n)))
  let error (n : ℕ) : ℝ := Real.log (uniform n : ℝ) / Real.log (n : ℝ) - 1
  have hUniformPos (n : ℕ) (hn : 1 < n) : 0 < (uniform n : ℝ) := by
    have hle : n ≤ uniform n := le_max_left _ _
    exact_mod_cast (show 0 < uniform n by omega)
  have hUniform (n : ℕ) (hn : 1 < n) (ε : ℝ) (hε : 0 < ε)
      (hw : ∀ m, ∃ L, HasDivisibleDistinctTuple n m L ∧
        (L : ℝ) ≤ (n : ℝ) ^ (1 + ε)) :
      (uniform n : ℝ) ≤ (n : ℝ) ^ (1 + ε) ∧
      ∀ m, HasDivisibleDistinctTuple n m (uniform n) := by
    let bound : ℝ := (n : ℝ) ^ (1 + ε)
    have hbound : 0 ≤ bound := by dsimp [bound]; positivity
    have hBounds (m : ℕ) : shortest n m ≤ ⌊bound⌋₊ := by
      obtain ⟨L, hL, hboundL⟩ := hw m
      exact le_trans (Nat.sInf_le hL) (Nat.le_floor hboundL)
    have hUpper : ⌊bound⌋₊ ∈ upperBounds (Set.range (shortest n)) := by
      rintro _ ⟨m, rfl⟩
      exact hBounds m
    have hBdd : BddAbove (Set.range (shortest n)) := ⟨⌊bound⌋₊, hUpper⟩
    have hSup : sSup (Set.range (shortest n)) ≤ ⌊bound⌋₊ := by
      exact csSup_le (Set.range_nonempty _) hUpper
    have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
    constructor
    · rw [Nat.cast_max]
      apply max_le
      · calc
          (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ bound := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      · exact (Nat.le_floor_iff hbound).mp hSup
    · intro m
      obtain ⟨L, hL, _⟩ := hw m
      have hs : HasDivisibleDistinctTuple n m (shortest n m) := by
        change sInf {L | HasDivisibleDistinctTuple n m L} ∈ {L | HasDivisibleDistinctTuple n m L}
        exact Nat.sInf_mem ⟨L, hL⟩
      have hle : shortest n m ≤ uniform n :=
        (le_csSup hBdd ⟨m, rfl⟩).trans (le_max_right _ _)
      rcases hs with ⟨a, ha, hA⟩
      exact ⟨a, ha, fun i ↦ ⟨(hA i).1, lt_of_lt_of_le (hA i).2.1 (Nat.add_le_add_left hle m),
        (hA i).2.2⟩⟩
  refine ⟨error, Asymptotics.isLittleO_iff.2 ?_, ?_⟩
  · intro ε hε
    filter_upwards [eventually_gt_atTop (1 : ℕ), h ε hε] with n hn hw
    have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hLog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
    have hPos : 0 < (uniform n : ℝ) := hUniformPos n hn
    have hge : (n : ℝ) ≤ (uniform n : ℝ) := by exact_mod_cast le_max_left n _
    have hLower : 0 ≤ error n := by
      dsimp [error]
      have := Real.log_le_log (show 0 < (n : ℝ) by positivity) hge
      apply sub_nonneg.mpr
      exact (le_div_iff₀ hLog).2 (by simpa)
    have hUpper : error n ≤ ε := by
      dsimp [error]
      apply sub_le_iff_le_add.mpr
      rw [add_comm]
      apply (div_le_iff₀ hLog).2
      exact (Real.le_rpow_iff_log_le hPos (by positivity)).mp (hUniform n hn ε hε hw).1
    simpa [Real.norm_of_nonneg hLower] using hUpper
  · filter_upwards [eventually_gt_atTop (1 : ℕ), h 1 one_pos] with n hn hw
    intro m
    refine ⟨uniform n, (hUniform n hn 1 one_pos hw).2 m, ?_⟩
    have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hLog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
    apply (Real.le_rpow_iff_log_le (hUniformPos n hn) (by positivity)).2
    dsimp [error]
    have hcancel : 1 + (Real.log (uniform n : ℝ) / Real.log (n : ℝ) - 1) =
        Real.log (uniform n : ℝ) / Real.log (n : ℝ) := by ring
    rw [hcancel, div_mul_cancel₀ _ hLog.ne']


theorem main : H1 → H2 → type_of% @Erdos711.erdos_711.parts.i := by
  intro h1 h2
  apply erdos711_diagonal
  intro δ hδ
  have hhalf : 0 < δ / 2 := by positivity
  have hPow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
  filter_upwards [h1 (δ / 2) hhalf, h2 (δ / 2) hhalf,
    hPow.eventually_ge_atTop 2, eventually_ge_atTop (1 : ℕ)] with n hs hr hLarge hn m
  obtain ⟨L₁, hL₁, a₁, hInj₁, ha₁⟩ := hs m
  obtain ⟨L₂, hL₂, a₂, hInj₂, ha₂⟩ := hr (m + L₁)
  let S : Set (Fin n) := {i | ∀ p : ℕ, p.Prime → p ∣ (i.val + 1) → p ≤ Nat.sqrt n}
  have rough {i : Fin n} (hi : i ∉ S) :
      ∃ p : ℕ, p.Prime ∧ p ∣ (i.val + 1) ∧ Nat.sqrt n < p := by
    by_contra h
    apply hi
    change ∀ p : ℕ, p.Prime → p ∣ (i.val + 1) → p ≤ Nat.sqrt n
    intro p hp hd
    exact le_of_not_gt (fun hlt ↦ h ⟨p, hp, hd, hlt⟩)
  classical
  let a (i : Fin n) := if i ∈ S then a₁ i else a₂ i
  refine ⟨L₁ + L₂, ⟨a, ?_, ?_⟩, ?_⟩
  · intro i j hij
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
    · exact hInj₁ hi hj (by simpa [a, hi, hj] using hij)
    · have hEq : a₁ i = a₂ j := by simpa [a, hi, hj] using hij
      have hLeft := (ha₁ i hi).2.1
      have hRight := (ha₂ j (rough hj)).1
      omega
    · have hEq : a₂ i = a₁ j := by simpa [a, hi, hj] using hij
      have hLeft := (ha₁ j hj).2.1
      have hRight := (ha₂ i (rough hi)).1
      omega
    · exact hInj₂ (rough hi) (rough hj) (by simpa [a, hi, hj] using hij)
  · intro i
    by_cases hi : i ∈ S
    · have h := ha₁ i hi
      simp only [a, if_pos hi]
      exact ⟨h.1, by omega, h.2.2⟩
    · have h := ha₂ i (rough hi)
      simp only [a, if_neg hi]
      exact ⟨by omega, by omega, h.2.2⟩
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    rw [Nat.cast_add]
    calc
      (L₁ : ℝ) + L₂ ≤ (n : ℝ) ^ (1 + δ / 2) + (n : ℝ) ^ (1 + δ / 2) :=
        add_le_add hL₁ hL₂
      _ = 2 * (n : ℝ) ^ (1 + δ / 2) := by ring
      _ ≤ (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (1 + δ / 2) :=
        mul_le_mul_of_nonneg_right hLarge (by positivity)
      _ = (n : ℝ) ^ (1 + δ) := by
        rw [← Real.rpow_add hnR, show δ / 2 + (1 + δ / 2) = 1 + δ by ring]

end OMA.R_Erdos711_erdos_711_parts_i_R2
