import FormalConjectures.Wikipedia.IntegerFactorization

/-!
# Recovering the factor list from factorial coprimality

For odd inputs, a common prime factor of `n` and `b!` detects a prime factor
of `n` at most `b`. The guarded comparison, binary search, and repeated
division below reconstruct the full list using only bounds up to the square
root in the coprimality queries.

Credit: @neiam00
-/

namespace OMA.R_PolyTime_isPolyTime_primeFactorsList_R1

open ComplexityTheory

/-- Detect a shared prime factor of an odd input and a factorial, up to the square
root of the input. Only the coprimality bit is required. -/
def H1 : Prop :=
  ∃ query : ℕ × ℕ → Bool, IsPolyTime query ∧
    ∀ n b : ℕ, 3 ≤ n → ¬ 2 ∣ n → 2 ≤ b → b * b ≤ n →
      (query (n, b) = true ↔ ¬ n.Coprime b.factorial)

/-- Extend a promised comparison to all bounds using parity, comparisons, and integer square root. -/
def H2 : Prop :=
  ∀ query : ℕ × ℕ → Bool, IsPolyTime query →
    ∃ full : ℕ × ℕ → Bool, IsPolyTime full ∧
      ∀ n b : ℕ, full (n, b) =
        if b < 2 then false
        else if n ≤ b then true
        else if 2 ∣ n then true
        else if 2 ≤ min b n.sqrt then query (n, min b n.sqrt)
        else false

/-- Binary search makes one comparison per input bit for each input at least two. -/
def H3 : Prop :=
  ∀ query : ℕ × ℕ → Bool, IsPolyTime query →
    IsPolyTime (fun n : ℕ =>
      if n < 2 then 2 - n
      else (Nat.rec (motive := fun _ => ℕ → ℕ) id
        (fun i search low =>
          if query (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i))
        (n.log2 + 1)) 0)

/-- Emit a list by making at most one division per input bit, for any polynomial-time divisor function. -/
def H4 : Prop :=
  ∀ d : ℕ → ℕ, IsPolyTime d →
    IsPolyTime (fun n : ℕ =>
      (Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
        (fun _ loop x => if x < 2 then [] else d x :: loop (x / d x)) n.log2) n)

/-- After the remaining comparisons, the dyadic interval is a singleton containing the threshold. -/
theorem binary_threshold (query : Nat → Bool) (target : Nat)
    (hq : ∀ b, query b = true ↔ target ≤ b) (k lo : Nat)
    (hlo : lo ≤ target) (hhi : target < lo + 2 ^ k) :
    (Nat.rec (motive := fun _ => Nat → Nat) id
      (fun i search low =>
        if query (low + 2 ^ i - 1) then search low else search (low + 2 ^ i)) k) lo = target := by
  induction k generalizing lo with
  | zero =>
    change lo = target
    simp only [Nat.pow_zero] at hhi
    omega
  | succ k ih =>
    change (if query (lo + 2 ^ k - 1) then _ else _) = target
    rw [Nat.pow_succ] at hhi
    have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
    split
    next h =>
      apply ih lo hlo
      have := (hq _).mp h
      omega
    next h =>
      apply ih (lo + 2 ^ k)
      · have : ¬ target ≤ lo + 2 ^ k - 1 := fun ht => h ((hq _).mpr ht)
        omega
      · omega

theorem find_bounded_threshold (query : Nat → Bool) (target n : Nat)
    (hq : ∀ b, query b = true ↔ target ≤ b) (hn : target ≤ n) :
    (Nat.rec (motive := fun _ => Nat → Nat) id
      (fun i search low =>
        if query (low + 2 ^ i - 1) then search low else search (low + 2 ^ i))
      (n.log2 + 1)) 0 = target := by
  apply binary_threshold query target hq (n.log2 + 1) 0 (Nat.zero_le _)
  simpa only [Nat.zero_add] using Nat.lt_of_le_of_lt hn (Nat.lt_log2_self (n := n))

theorem log2_div_succ_le {n d : Nat} (hd : 2 ≤ d) (hn : d ≤ n) :
    (n / d).log2 + 1 ≤ n.log2 := by
  have hq : 0 < n / d := Nat.div_pos hn (by omega)
  apply (Nat.le_log2 (by omega : n ≠ 0)).2
  rw [Nat.pow_succ]
  calc
    2 ^ (n / d).log2 * 2 ≤ (n / d) * d :=
      Nat.mul_le_mul (Nat.log2_self_le (by omega)) hd
    _ ≤ n := Nat.div_mul_le_self n d

/-- Each division reduces the binary logarithm by at least one, so this much fuel suffices. -/
theorem bounded_descent (d : Nat → Nat) (f : Nat → List Nat)
    (hdiv : ∀ k, 2 ≤ d (k + 2) ∧ d (k + 2) ≤ k + 2)
    (h0 : f 0 = []) (h1 : f 1 = [])
    (hstep : ∀ k, f (k + 2) = d (k + 2) :: f ((k + 2) / d (k + 2)))
    (fuel n : Nat) (hf : n.log2 ≤ fuel) :
    (Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
      (fun _ loop x => if x < 2 then [] else d x :: loop (x / d x)) fuel) n = f n := by
  induction fuel generalizing n with
  | zero =>
    have hn : n < 2 := by
      by_cases h : n < 2
      · exact h
      · have hlog : 1 ≤ n.log2 := (Nat.le_log2 (by omega : n ≠ 0)).mpr (by omega)
        omega
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · exact h0.symm
    · exact h1.symm
  | succ fuel ih =>
    cases n with
    | zero => exact h0.symm
    | succ m =>
      cases m with
      | zero => exact h1.symm
      | succ k =>
        obtain ⟨hd, hn⟩ := hdiv k
        have hsmall := log2_div_succ_le hd hn
        change (if k + 2 < 2 then [] else d (k + 2) :: _) = f (k + 2)
        rw [if_neg (by omega : ¬ k + 2 < 2), hstep k]
        change (k + 2).log2 ≤ fuel + 1 at hf
        exact congrArg (List.cons _) (ih ((k + 2) / d (k + 2)) (by omega))

theorem main : H1 → H2 → H3 → H4 → type_of% @PolyTime.isPolyTime_primeFactorsList := by
  intro h₁ h₂ h₃ h₄
  obtain ⟨query, htime, hquery⟩ := h₁
  obtain ⟨full, hfulltime, hfull⟩ := h₂ query htime
  have hcompare (n b : ℕ) (hn : 2 ≤ n) : full (n, b) = true ↔ n.minFac ≤ b := by
    rw [hfull n b]
    have hlower := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
    by_cases hb : b < 2
    · simp [hb, show ¬ n.minFac ≤ b by omega]
    by_cases hlarge : n ≤ b
    · have hle := (Nat.minFac_le (by omega : 0 < n)).trans hlarge
      simp [hb, hlarge, hle]
    by_cases heven : 2 ∣ n
    · have hle := (Nat.minFac_le_of_dvd (by decide : 2 ≤ 2) heven).trans (by omega : 2 ≤ b)
      simp [hb, hlarge, heven, hle]
    rw [if_neg hb, if_neg hlarge, if_neg heven]
    have hcut (h : n.minFac ≤ b) : n.minFac ≤ min b n.sqrt := by
      have hnp : ¬ n.Prime := (Nat.not_prime_iff_minFac_lt hn).mpr (by omega)
      exact le_min h (Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega) hnp))
    by_cases hc : 2 ≤ min b n.sqrt
    · rw [if_pos hc, hquery n _ (by omega) heven hc (Nat.le_sqrt.mp (min_le_right _ _))]
      rw [Nat.coprime_factorial_iff (by omega : n ≠ 1), not_lt]
      exact ⟨fun h => h.trans (min_le_left _ _), hcut⟩
    · have hnone : ¬ n.minFac ≤ b := fun h => hc (hlower.trans (hcut h))
      simp [hc, hnone]
  have hmin : IsPolyTime Nat.minFac := by
    refine (congrArg (fun f : ℕ → ℕ => IsPolyTime f) ?_).mp (h₃ full hfulltime)
    funext n
    by_cases hn : n < 2
    · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · simp [Nat.minFac_zero]
      · simp [Nat.minFac_one]
    · rw [if_neg hn]
      exact find_bounded_threshold (fun b => full (n, b)) n.minFac n
        (fun b => hcompare n b (by omega)) (Nat.minFac_le (by omega))
  refine (congrArg (fun f : ℕ → List ℕ => IsPolyTime f) ?_).mp (h₄ Nat.minFac hmin)
  funext n
  apply bounded_descent Nat.minFac Nat.primeFactorsList
  · intro k
    exact ⟨(Nat.minFac_prime (by omega : k + 2 ≠ 1)).two_le, Nat.minFac_le (by omega)⟩
  · exact Nat.primeFactorsList_zero
  · exact Nat.primeFactorsList_one
  · exact Nat.primeFactorsList_add_two
  · exact Nat.le_refl _

end OMA.R_PolyTime_isPolyTime_primeFactorsList_R1
