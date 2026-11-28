import Mathlib

/-!
# Buying coupons in batches of distinct types

Source: N. Gast, https://mathoverflow.net/questions/235585 (CC BY-SA 3.0).
Credit: @connoranderson. Gast gave the first-step recursion and the comparison
between sizes one and two. Here the expected purchase cost decreases across
every pair of fixed uniform batch sizes, for arbitrary integer quotas.

A law gives a probability to each possible set of types purchased together.
The iterate of its transition operator on the unfinished-quota indicator is
the probability that another purchase is required after t independent rounds.
The expected total payment is the mean price of a batch times the sum of those
probabilities, since the decision to buy the next batch uses only past draws.

Thinning a large-batch law independently skips some purchases. Its finite-time
survival probabilities compare under a containment inequality on nonempty
sets of outstanding types. Summing the comparison cancels the thinning factor.
The examples give exact costs for two ways the uniform fixed-size assumptions
can fail. In mixedFour the fair coin selects either a uniform s-subset or
all four types; increasing s from one to two increases cost. With biased
singletons the first requested type has probability three quarters.
-/
namespace OMA.S_mo_235585
open Finset
open scoped ENNReal
abbrev Quota (n : ℕ) := Fin n → ℕ
abbrev Law (n : ℕ) := Finset (Fin n) → ℝ

def advance {n : ℕ} (x : Quota n) (A : Finset (Fin n)) : Quota n :=
  fun i => x i - if i ∈ A then 1 else 0

def miss {n : ℕ} (x : Quota n) : ℝ := if x=0 then 0 else 1

noncomputable def trans {n : ℕ} (w : Law n) (f : Quota n → ℝ) (x : Quota n) : ℝ :=
  ∑ A, w A * f (advance x A)

noncomputable def survival {n : ℕ} (w : Law n) (t : ℕ) (x : Quota n) : ℝ :=
  (trans w)^[t] miss x

noncomputable def paid {n : ℕ} (w : Law n) (price : ℝ) (x : Quota n) : ℝ≥0∞ :=
  ENNReal.ofReal price * ∑' t : ℕ, ENNReal.ofReal (survival w t x)

noncomputable def uniform (n k : ℕ) : Law n := fun A =>
  if A.card=k then 1/(n.choose k : ℝ) else 0

noncomputable def coverage {n : ℕ} (w : Law n) (D : Finset (Fin n)) : ℝ :=
  ∑ A ∈ univ.filter (D ⊆ ·), w A

def probability {n : ℕ} (w : Law n) : Prop := (∀ A, 0≤w A) ∧ (∑ A,w A)=1

noncomputable def thin {n : ℕ} (p : ℝ) (w : Law n) : Law n :=
  fun A => (if A=∅ then 1-p else 0) + p*w A

noncomputable def meanSize {n : ℕ} (w : Law n) := ∑ A,w A*A.card

noncomputable def mixedFour (s : ℕ) : Law 4 := fun A => (uniform 4 s A + uniform 4 4 A)/2

def pairRequest : Quota 4 := fun i => if i=0 ∨ i=1 then 1 else 0

noncomputable def biasedSingle : Law 2 := fun A =>
  (if A={0} then 3/4 else 0) + (if A={1} then 1/4 else 0)

def firstRequest : Quota 2 := fun i => if i=0 then 1 else 0

theorem main :
    (∀ {n k l : ℕ}, 0 < k → k ≤ l → l ≤ n → ∀ x : Quota n,
      paid (uniform n l) l x ≤ paid (uniform n k) k x ∧
      paid (uniform n k) k x ≤ ENNReal.ofReal ((n:ℝ)*∑ i,(x i:ℝ))) ∧
    (∀ {n : ℕ} (v w : Law n), probability v → probability w →
      ∀ a b : ℝ, 0 < a → a ≤ b →
      (∀ D : Finset (Fin n), D.Nonempty → coverage w D ≤ (a/b)*coverage v D) →
      ∀ x : Quota n, paid v b x ≤ paid w a x ∧
      ∀ t : ℕ, survival (thin (a/b) v) t x ≤ survival w t x) ∧
    (paid (mixedFour 1) (meanSize (mixedFour 1)) pairRequest = ENNReal.ofReal (14/3) ∧
      paid (mixedFour 2) (meanSize (mixedFour 2)) pairRequest = ENNReal.ofReal (52/11)) ∧
    (paid biasedSingle (meanSize biasedSingle) firstRequest = ENNReal.ofReal (4/3) ∧
      paid (uniform 2 2) 2 firstRequest = ENNReal.ofReal 2) := by
  sorry

end OMA.S_mo_235585
