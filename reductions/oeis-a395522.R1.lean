import OMAStatements.S_oeis_a395522
import Mathlib

/-!
# Input periods of the iterated Fibonacci function

The hypotheses concern the ordinary Pisano chain, a divisibility bound on
periods, the fixed endpoint, and a comparison in rows four and five. This
file proves how to transport those two rows to every later row.

The period is taken in the input of the Fibonacci function.
Source: https://oeis.org/A395522
-/

namespace OMA.R_oeis_a395522_R1

open OMA.S_oeis_a395522

/-- Fulton and Morris's iteration theorem. Each step is the least positive
input modulus determining the Fibonacci residue at the preceding modulus. -/
def H1 : Prop :=
  ∀ k : ℕ, 1 < k → ∃ (s a : ℕ) (c : ℕ → ℕ), c 0 = k ∧ c s = 24 * 5 ^ a ∧
    ∀ i : ℕ, i < s →
      0 < c (i + 1) ∧
      (∀ x y : ℕ, x % c (i + 1) = y % c (i + 1) → Nat.fib x % c i = Nat.fib y % c i) ∧
      ∀ t : ℕ, 0 < t →
        (∀ x y : ℕ, x % t = y % t → Nat.fib x % c i = Nat.fib y % c i) → c (i + 1) ≤ t

/-- The rank and sign bound for a chain of ordinary least Pisano periods.
The endpoint exponent is forced by the chain, and every late positive
period must be divisible by half that endpoint. -/
def H2 : Prop :=
  ∀ (s a : ℕ) (c : ℕ → ℕ), 1 < c 0 → c s = 24 * 5 ^ a →
    (∀ i : ℕ, i < s →
      0 < c (i + 1) ∧
      (∀ x y : ℕ, x % c (i + 1) = y % c (i + 1) → Nat.fib x % c i = Nat.fib y % c i) ∧
      ∀ t : ℕ, 0 < t →
        (∀ x y : ℕ, x % t = y % t → Nat.fib x % c i = Nat.fib y % c i) → c (i + 1) ≤ t) →
    ∀ m d : ℕ, s + 4 ≤ m → 0 < d → isPeriod m (c 0) d → 12 * 5 ^ a ∣ d

/-- A fixed Pisano endpoint determines its own Fibonacci residues. -/
def H3 : Prop :=
  ∀ a x y : ℕ, x % (24 * 5 ^ a) = y % (24 * 5 ^ a) →
    Nat.fib x % (24 * 5 ^ a) = Nat.fib y % (24 * 5 ^ a)

/-- At the fixed endpoint, rows four and five give the same half-shift test
for every function of the residue. This is the signed-edge calculation on
the five reachable residues modulo 24 and the fibres modulo a power of 5. -/
def H4 : Prop :=
  ∀ (a : ℕ) (h : ℕ → ℕ),
    (∀ x y : ℕ, x % (24 * 5 ^ a) = y % (24 * 5 ^ a) → h x = h y) →
    ((∀ x : ℕ, h (iterFib 4 (x + 12 * 5 ^ a)) = h (iterFib 4 x)) ↔
     (∀ x : ℕ, h (iterFib 5 (x + 12 * 5 ^ a)) = h (iterFib 5 x)))

theorem iterFib_add (r n x : ℕ) :
    iterFib (r + n) x = iterFib r (iterFib n x) := by
  induction r with
  | zero => simp [iterFib]
  | succ r ih =>
    rw [Nat.succ_add]
    change Nat.fib (iterFib (r + n) x) = Nat.fib (iterFib r (iterFib n x))
    exact congrArg Nat.fib ih

theorem iterFib_inner (n x : ℕ) :
    iterFib (n + 1) x = iterFib n (Nat.fib x) := by
  exact iterFib_add n 1 x

/-- Descend a chain of input moduli from one endpoint residue. -/
theorem descend (c : ℕ → ℕ) (s : ℕ) :
    (∀ i : ℕ, i < s → ∀ x y : ℕ, x % c (i + 1) = y % c (i + 1) →
      Nat.fib x % c i = Nat.fib y % c i) →
    ∀ x y : ℕ, x % c s = y % c s → iterFib s x % c 0 = iterFib s y % c 0 := by
  induction s with
  | zero =>
    intro _ x y h
    exact h
  | succ s ih =>
    intro steps x y h
    rw [iterFib_inner s x, iterFib_inner s y]
    apply ih (fun i hi => steps i (by omega))
    exact steps s (by omega) x y h

theorem fixed_congr (a : ℕ) (fixed : H3) (j : ℕ) :
    ∀ x y : ℕ, x % (24 * 5 ^ a) = y % (24 * 5 ^ a) →
      iterFib j x % (24 * 5 ^ a) = iterFib j y % (24 * 5 ^ a) := by
  induction j with
  | zero => exact fun _ _ h => h
  | succ j ih =>
    intro x y h
    exact fixed a _ _ (ih x y h)

/-- A period must be at least the second positive multiple when the first
positive multiple has been excluded. -/
theorem second_multiple {D t : ℕ} (ht : 0 < t) (hd : D ∣ t) (hne : t ≠ D) :
    2 * D ≤ t := by
  obtain ⟨j, rfl⟩ := hd
  cases j with
  | zero => simp at ht
  | succ j =>
    cases j with
    | zero => simp at hne
    | succ j =>
      rw [Nat.mul_comm 2 D]
      exact Nat.mul_le_mul_left D (by omega)

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a395522.main := by
  intro chains bound fixed tests k hk
  by_cases one : k = 1
  · subst k
    refine ⟨1, 1, by decide, by decide, ?_⟩
    intro m _
    exact ⟨fun x => by simp, fun t ht _ => ht⟩
  have large : 1 < k := by omega
  obtain ⟨s, a, c, first, last, steps⟩ := chains k large
  have down : ∀ x y : ℕ, x % (24 * 5 ^ a) = y % (24 * 5 ^ a) →
      iterFib s x % k = iterFib s y % k := by
    rw [← first, ← last]
    exact descend c s (fun i hi => (steps i hi).2.1)
  have upper (j : ℕ) (x y : ℕ) (hx : x % (24 * 5 ^ a) = y % (24 * 5 ^ a)) :
      iterFib (s + j) x % k = iterFib (s + j) y % k := by
    simp only [iterFib_add]
    exact down _ _ (fixed_congr a fixed j x y hx)
  have lower (m d : ℕ) (hm : s + 4 ≤ m) (hd : 0 < d) (per : isPeriod m k d) :
      12 * 5 ^ a ∣ d := by
    have hc := bound s a c (first.symm ▸ large) last steps m d hm hd
    exact hc (first.symm ▸ per)
  have next (j : ℕ) : isPeriod (s + 4 + j) k (12 * 5 ^ a) ↔
      isPeriod (s + 4 + j + 1) k (12 * 5 ^ a) := by
    have h := tests a (fun x => iterFib (s + j) x % k) (upper j)
    unfold isPeriod
    rw [show s + 4 + j = (s + j) + 4 by omega,
        show s + j + 4 + 1 = (s + j) + 5 by omega]
    simpa only [iterFib_add] using h
  have late (j : ℕ) : isPeriod (s + 4 + j) k (12 * 5 ^ a) ↔
      isPeriod (s + 4) k (12 * 5 ^ a) := by
    induction j with
    | zero => rfl
    | succ j ih => exact (next j).symm.trans ih
  have positive : 0 < 12 * 5 ^ a := by positivity
  by_cases h : isPeriod (s + 4) k (12 * 5 ^ a)
  · refine ⟨s + 4, 12 * 5 ^ a, by omega, positive, ?_⟩
    intro m hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    refine ⟨(late j).mpr h, ?_⟩
    intro t ht per
    exact Nat.le_of_dvd ht (lower _ t (by omega) ht per)
  · refine ⟨s + 4, 24 * 5 ^ a, by omega, by positivity, ?_⟩
    intro m hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    refine ⟨?_, ?_⟩
    · intro x
      rw [Nat.add_assoc s 4 j]
      apply upper (4 + j)
      simp
    · intro t ht per
      rw [show 24 * 5 ^ a = 2 * (12 * 5 ^ a) by omega]
      apply second_multiple ht (lower _ t (by omega) ht per)
      intro eq
      exact h ((late j).mp (eq ▸ per))

end OMA.R_oeis_a395522_R1

