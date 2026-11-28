import FormalConjectures.ErdosProblems.«470»

/-!
# Odd weird numbers have at least six distinct prime factors (Erdős Problem 470)

We prove `Erdos470.erdos_470.variants.odd_weird_prime_div` end to end: every odd weird number has
at least six distinct prime divisors (originally proved by Liddy and Riedl, 2018).

## Proof overview

1. **Primitive abundant reduction**: Given an odd weird number `n` with at most 5 distinct prime
   factors, its smallest non-deficient divisor `m` is an odd primitive abundant number with at
   most 5 distinct prime factors (a perfect divisor would make `n` pseudoperfect). It therefore
   suffices to show every odd primitive abundant number `m` with at most 5 distinct prime factors
   is pseudoperfect.
2. **Two-layer divisor-sum certificates (`CertifiedBase`)**: Parameterizing the interval-covering
   method by `(L, G)` (we use `(18, 2)` and `(64, 6)`), if a deficient cofactor `b` has proper
   divisor sums covering `[L, ProperSum b - L]` with low-end downward and upward gaps at most `G`,
   and `ProperSum b ≥ (2*G + 1) * (2*L + 8*G + 8)`, then every primitive abundant extension
   `b * q ^ e` (with odd prime `q ∤ b`, `e ≥ 1`) having excess `E ≥ L` (and deficiency `D(b) ≥ 2`
   when `e = 1`) is pseudoperfect.
3. **Hereditary propagation & interval-list verification**:
   - `CertifiedBase` propagates when multiplying by a new coprime prime `p` (via `middle_next`),
     and when raising an existing prime power `p ∣ b` whenever the `p`-free part of `b` has
     divisor sums containing `p` consecutive integers below `ProperSum b + 1 - (p + 1) * L`
     (`RaiseOk`).
   - Small base cofactors and `RaiseOk` witnesses are verified purely with sorted interval lists
     (using only kernel `Nat` addition and comparison, no bitsets).
4. **Verified branch-and-bound + 27 explicit concrete witnesses**:
   - Factoring `m = b * q ^ e` by its largest prime `q`, a verified branch-and-bound checker
     splits primes and exponents incrementally until each branch is either non-primitive (`L ≥ 2`
     or dropping one exponent already yields abundancy `≥ 2`), deficient for all remaining primes,
     certified by `CertifiedBase` with `E ≥ L` for all `q`, or reduced to a concrete small
     cofactor where the 27 remaining small-excess odd primitive abundant numbers are each closed
     by an explicit subset of proper divisors summing to the excess `E`.
-/

namespace Erdos470OddWeird

open Finset ArithmeticFunction

/- ### Section 1: Prime-power divisor sums and compositeness -/

private def sigmaPP (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | a + 1 => sigmaPP p a * p + 1

private lemma sigmaPP_eq_sigma_one_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigmaPP p a = sigma 1 (p ^ a) := by
  rw [sigma_one_apply_prime_pow hp]
  induction a with
  | zero => simp [sigmaPP]
  | succ a ih =>
    rw [sigmaPP, ih, Finset.sum_mul, Finset.sum_range_succ' (f := fun k => p ^ k) (a + 1)]
    simp [pow_succ]

private lemma sigmaPP_pos (p a : ℕ) : 0 < sigmaPP p a := by
  cases a <;> simp [sigmaPP]

private lemma sigmaPP_mul_sub {p : ℕ} (hp : 1 ≤ p) (a : ℕ) :
    (p - 1) * sigmaPP p a + 1 = p ^ (a + 1) := by
  induction a with
  | zero => simp [sigmaPP]; omega
  | succ a ih =>
    rw [sigmaPP]
    zify [hp] at ih ⊢
    rw [pow_succ]
    nlinarith

private lemma sigmaPP_lt_limit {p : ℕ} (hp : 1 < p) (a : ℕ) :
    sigmaPP p a * (p - 1) < p * p ^ a := by
  have h := sigmaPP_mul_sub (Nat.le_of_lt hp) a
  rw [pow_succ, mul_comm (p ^ a) p] at h
  rw [mul_comm]
  omega

private lemma sigmaPP_step_ratio {p : ℕ} (a : ℕ) :
    sigmaPP p a * p ^ (a + 1) ≤ sigmaPP p (a + 1) * p ^ a := by
  rw [sigmaPP, pow_succ]
  nlinarith [Nat.zero_le (p ^ a)]

private lemma sigmaPP_mono_ratio {p : ℕ} (_hp : 0 < p) {a b : ℕ} (hab : a ≤ b) :
    sigmaPP p a * p ^ b ≤ sigmaPP p b * p ^ a := by
  induction hab with
  | refl => exact le_rfl
  | @step m h ih =>
    have h1 : sigmaPP p a * p ^ (m + 1) ≤ sigmaPP p m * p ^ a * p := by
      rw [pow_succ, ← mul_assoc]
      exact Nat.mul_le_mul_right p ih
    have h2 : sigmaPP p m * p ^ a * p ≤ sigmaPP p (m + 1) * p ^ a := by
      rw [sigmaPP, Nat.add_mul, Nat.one_mul]
      have : sigmaPP p m * p ^ a * p = sigmaPP p m * p * p ^ a := by ring
      omega
    exact h1.trans h2

private lemma not_prime_of_mod_zero {n p : ℕ} (hp2 : 2 ≤ p) (hsq : p * p ≤ n)
    (hmod : n % p = 0) : ¬ n.Prime := by
  intro hp
  have hdiv : p ∣ n := Nat.dvd_of_mod_eq_zero hmod
  have hlt : p < n := by nlinarith
  rcases hp.eq_one_or_self_of_dvd p hdiv with h1 | h2 <;> omega

private def hasSmallFactor (n : ℕ) : Bool :=
  if Nat.blt n 4 then false
  else if Nat.beq (n % 2) 0 then true
  else if Nat.blt n 9 then false
  else if Nat.beq (n % 3) 0 then true
  else if Nat.blt n 25 then false
  else if Nat.beq (n % 5) 0 then true
  else if Nat.blt n 49 then false
  else if Nat.beq (n % 7) 0 then true
  else if Nat.blt n 121 then false
  else if Nat.beq (n % 11) 0 then true
  else if Nat.blt n 169 then false
  else if Nat.beq (n % 13) 0 then true
  else if Nat.blt n 289 then false
  else if Nat.beq (n % 17) 0 then true
  else if Nat.blt n 361 then false
  else if Nat.beq (n % 19) 0 then true
  else if Nat.blt n 529 then false
  else if Nat.beq (n % 23) 0 then true
  else if Nat.blt n 841 then false
  else if Nat.beq (n % 29) 0 then true
  else if Nat.blt n 961 then false
  else if Nat.beq (n % 31) 0 then true
  else if Nat.blt n 1369 then false
  else if Nat.beq (n % 37) 0 then true
  else if Nat.blt n 1681 then false
  else if Nat.beq (n % 41) 0 then true
  else if Nat.blt n 1849 then false
  else if Nat.beq (n % 43) 0 then true
  else if Nat.blt n 2209 then false
  else if Nat.beq (n % 47) 0 then true
  else false

private lemma not_prime_of_ite_small {n p : ℕ} {b : Bool} (hp2 : 2 ≤ p)
    (hrest : b = true → ¬ n.Prime)
    (h : (if Nat.blt n (p * p) then false else if Nat.beq (n % p) 0 then true else b) = true) :
    ¬ n.Prime := by
  by_cases h1 : Nat.blt n (p * p) = true
  · rw [if_pos h1] at h; exact absurd h (by decide)
  · rw [if_neg h1] at h
    by_cases h2 : Nat.beq (n % p) 0 = true
    · exact not_prime_of_mod_zero hp2 (by simp [Nat.blt_eq] at h1; omega) (Nat.eq_of_beq_eq_true h2)
    · rw [if_neg h2] at h; exact hrest h

private lemma not_prime_of_hasSmallFactor {n : ℕ} (h : hasSmallFactor n = true) : ¬ n.Prime := by
  unfold hasSmallFactor at h
  apply not_prime_of_ite_small (p := 2) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 3) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 5) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 7) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 11) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 13) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 17) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 19) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 23) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 29) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 31) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 37) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 41) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 43) (by decide) _ h; intro h
  apply not_prime_of_ite_small (p := 47) (by decide) _ h; intro h
  exact absurd h (by decide)

private def prevPrimeAux (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
    if Nat.blt k 2 then 0
    else if hasSmallFactor k then prevPrimeAux (k - 1) fuel
    else k

private def prevPrimeLE (n : ℕ) : ℕ := prevPrimeAux n 120

private def nextPrimeAux (k : ℕ) : ℕ → ℕ
  | 0 => k
  | fuel + 1 =>
    if hasSmallFactor k then nextPrimeAux (k + 2) fuel
    else k

private def nextPrimeAfter (n : ℕ) : ℕ :=
  let start := if Nat.blt n 2 then 3 else if Nat.beq (n % 2) 1 then n + 2 else n + 1
  nextPrimeAux start 60

private lemma allComposite_of_prevPrimeAux {k fuel : ℕ} (h : 2 ≤ prevPrimeAux k fuel) :
    prevPrimeAux k fuel ≤ k ∧
    ∀ q, prevPrimeAux k fuel < q → q ≤ k → ¬ q.Prime := by
  induction fuel generalizing k with
  | zero => simp [prevPrimeAux] at h
  | succ fuel ih =>
    unfold prevPrimeAux at h ⊢
    split_ifs at h ⊢ with hk hcomp
    · simp at h
    · obtain ⟨hle, hnot⟩ := ih h
      refine ⟨by omega, fun q hq1 hq2 => ?_⟩
      by_cases hqk : q = k
      · subst hqk; exact not_prime_of_hasSmallFactor hcomp
      · exact hnot q hq1 (by omega)
    · exact ⟨le_rfl, fun q hq1 hq2 => by omega⟩

private lemma allComposite_of_nextPrimeAux {k fuel : ℕ} (hodd : k % 2 = 1) :
    k ≤ nextPrimeAux k fuel ∧
    ∀ q, k ≤ q → q < nextPrimeAux k fuel → ¬ q.Prime := by
  induction fuel generalizing k with
  | zero =>
    simp only [nextPrimeAux]
    exact ⟨le_rfl, fun q h1 h2 => by omega⟩
  | succ fuel ih =>
    simp only [nextPrimeAux]
    split_ifs with hcomp
    · obtain ⟨hle, hnot⟩ := ih (k := k + 2) (by omega)
      refine ⟨by omega, fun q hq1 hq2 => ?_⟩
      by_cases hqk : q = k
      · subst hqk; exact not_prime_of_hasSmallFactor hcomp
      · by_cases hqk1 : q = k + 1
        · subst hqk1
          intro hp
          have h2 : 2 ∣ k + 1 := by omega
          rcases hp.eq_one_or_self_of_dvd 2 h2 with h1 | h2'
          · omega
          · have hke : k = 1 := by omega
            subst hke; simp [hasSmallFactor] at hcomp
        · exact hnot q (by omega) hq2
    · exact ⟨le_rfl, fun q h1 h2 => by omega⟩

private lemma nextPrimeAfter_spec_odd {n : ℕ} (hn : 2 ≤ n) :
    n < nextPrimeAfter n ∧ ∀ q, n < q → q < nextPrimeAfter n → ¬ q.Prime := by
  unfold nextPrimeAfter
  dsimp only
  have hn2 : ¬ Nat.blt n 2 = true := by simp [Nat.blt_eq]; omega
  rw [if_neg hn2]
  split_ifs with hodd
  · have hodd' : n % 2 = 1 := Nat.eq_of_beq_eq_true hodd
    obtain ⟨hle, hnot⟩ := allComposite_of_nextPrimeAux (k := n + 2) (fuel := 60) (by omega)
    refine ⟨by omega, fun q h1 h2' => ?_⟩
    by_cases hq1 : q = n + 1
    · subst hq1
      intro hp
      have hdiv : 2 ∣ n + 1 := by omega
      rcases hp.eq_one_or_self_of_dvd 2 hdiv with h0 | h0 <;> omega
    · exact hnot q (by omega) h2'
  · have hodd' : n % 2 ≠ 1 := fun h => hodd (by simpa [Nat.beq_eq] using h)
    obtain ⟨hle, hnot⟩ := allComposite_of_nextPrimeAux (k := n + 1) (fuel := 60) (by omega)
    exact ⟨by omega, fun q h1 h2' => hnot q (by omega) h2'⟩

/- ### Section 2: Generalized Two-Layer Interval Covering (`CertifiedBase`) -/

private def Represented (n : ℕ) (x : ℤ) : Prop :=
  ∃ s : Finset ℕ, s ⊆ n.properDivisors ∧ (∑ d ∈ s, (d : ℤ)) = x

private def DivRepresented (n : ℕ) (x : ℤ) : Prop :=
  ∃ s : Finset ℕ, s ⊆ n.divisors ∧ (∑ d ∈ s, (d : ℤ)) = x

private def ProperSum (n : ℕ) : ℤ :=
  ∑ d ∈ n.properDivisors, (d : ℤ)

private def Excess (n : ℕ) : ℤ :=
  (sigma 1 n : ℤ) - 2 * (n : ℤ)

private lemma sigma_split (n : ℕ) : (sigma 1 n : ℤ) = ProperSum n + n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  simp [ProperSum]

private lemma properSum_nonneg (n : ℕ) : 0 ≤ ProperSum n :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

private lemma represented_compl {n : ℕ} {x : ℤ} (h : Represented n x) :
    Represented n (ProperSum n - x) := by
  classical
  obtain ⟨s, hs, rfl⟩ := h
  refine ⟨n.properDivisors \ s, sdiff_subset, ?_⟩
  have hsum := Finset.sum_sdiff hs (f := fun d : ℕ => (d : ℤ))
  change (∑ d ∈ n.properDivisors \ s, (d : ℤ)) + ∑ d ∈ s, (d : ℤ) = ProperSum n at hsum
  linarith

private lemma represented_mono_dvd {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) {x : ℤ}
    (h : Represented a x) : Represented b x := by
  obtain ⟨s, hs, rfl⟩ := h
  refine ⟨s, fun d hd => ?_, rfl⟩
  obtain ⟨hda, hlt⟩ := Nat.mem_properDivisors.mp (hs hd)
  exact Nat.mem_properDivisors.mpr ⟨hda.trans hab, lt_of_lt_of_le hlt (Nat.le_of_dvd hb hab)⟩

private lemma divRepresented_mono_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) {x : ℤ}
    (h : DivRepresented a x) : DivRepresented b x := by
  obtain ⟨s, hs, rfl⟩ := h
  refine ⟨s, fun d hd => ?_, rfl⟩
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors (hs hd)).trans hab, hb⟩

private lemma pseudoperfect_of_excess {m : ℕ} (pos : 0 < m) {s : Finset ℕ}
    (subset : s ⊆ m.properDivisors)
    (sum : (∑ d ∈ s, (d : ℤ)) = (sigma 1 m : ℤ) - 2 * (m : ℤ)) : m.Pseudoperfect := by
  classical
  have total : (sigma 1 m : ℤ) = (∑ d ∈ m.properDivisors, (d : ℤ)) + m := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp
  have rest := sum_sdiff subset (f := fun x : ℕ => (x : ℤ))
  refine ⟨pos, m.properDivisors \ s, sdiff_subset, Int.ofNat_inj.mp ?_⟩
  push_cast
  linarith only [sum, total, rest]

private lemma pseudoperfect_of_represented_excess {m : ℕ} (pos : 0 < m)
    (h : Represented m (Excess m)) : m.Pseudoperfect := by
  obtain ⟨s, hs, hsum⟩ := h
  exact pseudoperfect_of_excess pos hs hsum

private lemma represented_combine {c m p : ℕ} (hm : 0 < m) (cm : c ∣ m) (hn : ¬ p ∣ c)
    (hp : 1 < p) {y i : ℤ} (hy : DivRepresented c y) (hi : Represented m i) :
    Represented (p * m) (y + p * i) := by
  classical
  obtain ⟨s, hs, rfl⟩ := hy
  obtain ⟨t, ht, rfl⟩ := hi
  let f (x : ℕ) := p * x
  have hpos : 0 < p := by omega
  have inj : Function.Injective f := fun x y eq => Nat.eq_of_mul_eq_mul_left hpos eq
  have hsub : s ⊆ (p * m).properDivisors := by
    intro x hx
    have d := Nat.dvd_of_mem_divisors (hs hx)
    have dm := d.trans cm
    refine Nat.mem_properDivisors.mpr ⟨dm.trans (dvd_mul_left _ _), ?_⟩
    exact lt_of_le_of_lt (Nat.le_of_dvd hm dm) (by simpa using Nat.mul_lt_mul_of_pos_right hp hm)
  have hscaled : t.image f ⊆ (p * m).properDivisors := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp (ht hz)
    exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_left p hdiv, Nat.mul_lt_mul_of_pos_left hlt hpos⟩
  have hsep : Disjoint s (t.image f) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨z, _, rfl⟩ := mem_image.mp hx'
    exact hn ((dvd_mul_right p z).trans (Nat.dvd_of_mem_divisors (hs hx)))
  refine ⟨s ∪ t.image f, Finset.union_subset hsub hscaled, ?_⟩
  rw [sum_union hsep, sum_image (fun _ _ _ _ eq => inj eq), Finset.mul_sum]
  simp [f]

private lemma represented_layers {b m q : ℕ} (hm : 0 < m) (bm : b ∣ m) (hn : ¬ q ∣ b)
    (hq : 1 < q) {i y : ℤ} (hi : Represented m i) (hy : Represented b y) :
    Represented (q * m) (y + q * i) ∧ Represented (q * m) (b + y + q * i) := by
  classical
  obtain ⟨s, hs, rfl⟩ := hy
  have hb : b ≠ 0 := by
    intro z; subst b; exact hm.ne' (by simpa using bm)
  have h1 : DivRepresented b (∑ d ∈ s, (d : ℤ)) :=
    ⟨s, hs.trans Nat.properDivisors_subset_divisors, rfl⟩
  have nb : b ∉ s := fun h => Nat.self_notMem_properDivisors (hs h)
  have h2 : DivRepresented b ((b : ℤ) + ∑ d ∈ s, (d : ℤ)) := by
    refine ⟨insert b s, ?_, by rw [sum_insert nb]⟩
    rw [← Nat.insert_self_properDivisors hb]
    exact Finset.insert_subset_insert _ hs
  exact ⟨represented_combine hm bm hn hq h1 hi, represented_combine hm bm hn hq h2 hi⟩

private lemma final_prime_alternatives {P D q L g E : ℤ}
    (hg : 1 ≤ g) (hL : 1 ≤ L) (hD : 2 ≤ D) (hq : 3 ≤ q)
    (big : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ P)
    (excess : E = 2 * P - D * (q - 1)) (low : L ≤ E) :
    (g * q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q * P) ∨
    (q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q ∧ E ≤ 2 * P + D + q - L) ∨
    (L ≤ E ∧ E ≤ P - L) := by
  have gL : 0 ≤ g * L := mul_nonneg (by omega) (by omega)
  have gg : 0 ≤ g * g := mul_self_nonneg g
  have g1L : 0 ≤ (g - 1) * L := mul_nonneg (by omega) (by omega)
  have pbound : 5 * L ≤ P := by nlinarith only [big, hg, hL, gg, g1L]
  have dpos : 0 ≤ D := by omega
  have dlt : D < P := by nlinarith only [excess, low, hL, mul_nonneg (show 0 ≤ q - 3 by omega) dpos]
  by_cases small : g * q ≤ P - 2 * L + 1
  · left
    refine ⟨small, ?_⟩
    have t := mul_le_mul_of_nonneg_right hq (show 0 ≤ P by omega)
    nlinarith only [t, dlt, pbound, hL]
  · have dcap : D < 8 * g := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ q - 1 by omega)
      have w := mul_nonneg (show 0 ≤ g by omega) (show 0 ≤ q - 2 by omega)
      nlinarith only [small, k, w, excess, low, pbound, hL]
    have bigq : 2 * L + 8 * g + 8 < q := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ g by omega)
      nlinarith only [k, small, big, gg, gL, hg]
    by_cases overlap : q ≤ P - 2 * L + 1
    · right; left
      have h := mul_nonneg dpos (show 0 ≤ q - 1 by omega)
      exact ⟨overlap, by omega, by linarith only [excess, h, hD, bigq, hg, hL]⟩
    · right; right
      have k := mul_le_mul_of_nonneg_left hD (show 0 ≤ q - 1 by omega)
      exact ⟨low, by nlinarith only [k, excess, overlap, pbound]⟩

private lemma four_interval_join {P D q L A : ℤ} (w : q ≤ P - 2 * L + 1) (v : D + 2 * L - 1 ≤ q)
    (lo : L ≤ A) (hi : A ≤ 2 * P + D + q - L) :
    (L ≤ A ∧ A ≤ P - L) ∨ (L ≤ A - q ∧ A - q ≤ P - L) ∨
    (L ≤ A - (P + D) ∧ A - (P + D) ≤ P - L) ∨
    (L ≤ A - (P + D + q) ∧ A - (P + D + q) ≤ P - L) := by omega

private lemma nondivisor {P D q : ℤ} (hD : 0 < D)
    (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1)) : ¬ D ∣ 2 * P := by
  rintro ⟨x, h⟩
  rw [h] at low high
  have a := (mul_lt_mul_iff_right₀ hD).mp low
  have b := (mul_lt_mul_iff_right₀ hD).mp high
  omega

private lemma repeated_bounds {P D q L : ℤ} (hD : 0 < D) (hq : 3 ≤ q)
    (large : 6 * L ≤ P) (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1))
    (divone : ¬ D ∣ 2 * P) :
    3 ≤ D ∧ q ≤ P - 2 * L + 1 := by
  have three : 3 ≤ D := by
    by_contra! bad
    interval_cases D <;> simp at divone
  refine ⟨three, ?_⟩
  have a := mul_le_mul_of_nonneg_right three (show 0 ≤ q - 2 by omega)
  omega

private lemma repeated_alternatives {P D q L g E : ℤ} (hg : 1 ≤ g) (hL : 1 ≤ L)
    (hD : 0 < D) (hq : 3 ≤ q) (big : (2 * g + 1) * (2 * L + 8 * g + 8) ≤ P)
    (low : D * (q - 2) < 2 * P) (high : 2 * P < D * (q - 1)) (excess : E ≤ 2 * P + D - q) :
    (g * q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q * P ∧ E ≤ 2 * P + D + q * P - L) ∨
    (q ≤ P - 2 * L + 1 ∧ D + 2 * L - 1 ≤ q ∧ E ≤ 2 * P + D + q - L) := by
  have gL := mul_nonneg (show 0 ≤ g - 1 by omega) (show 0 ≤ L by omega)
  have gg := mul_self_nonneg g
  have pl : 6 * L ≤ P := by nlinarith only [big, hg, gL, gg]
  have pd : D < 2 * P := by nlinarith only [low, mul_nonneg (show 0 ≤ D by omega) (show 0 ≤ q - 3 by omega)]
  obtain ⟨_, qw⟩ := repeated_bounds hD hq pl low high (nondivisor hD low high)
  by_cases small : g * q ≤ P - 2 * L + 1
  · left
    have covers := mul_le_mul_of_nonneg_right hq (show 0 ≤ P by omega)
    exact ⟨small, by omega, by omega⟩
  · right
    have largeQ : 2 * L + 8 * g + 8 < q := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ g by omega)
      nlinarith only [k, small, big, gg, gL, hg, hL]
    have dcap : D < 8 * g := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_right h (show 0 ≤ q - 2 by omega)
      have w := mul_nonneg (show 0 ≤ g by omega) (show 0 ≤ q - 4 by omega)
      nlinarith only [k, low, small, pl, hL, w]
    exact ⟨qw, by omega, by omega⟩

private lemma repeat_from_excess {P D q : ℤ} (hq : 0 < q - 1) (hs : 0 < 2 * P + D)
    (E : ℕ → ℤ) (base : E 0 = -D)
    (next : ∀ j, E (j + 1) = q * E j + (2 * P + D))
    (j : ℕ) (firstDef : E 1 < 0) (previousDef : E j < 0) (abundant : 0 < E (j + 1)) :
    D * (q - 2) < 2 * P ∧ 2 * P < D * (q - 1) ∧ E (j + 1) ≤ 2 * P + D - q := by
  have closed (t : ℕ) : (q - 1) * E t = q ^ t * (2 * P - D * (q - 2)) - (2 * P + D) := by
    induction t with
    | zero => rw [base, pow_zero]; ring
    | succ t ih =>
      rw [next, pow_succ]
      calc _ = q * ((q - 1) * E t) + (q - 1) * (2 * P + D) := by ring
        _ = _ := by rw [ih]; ring
  have c := closed (j + 1)
  have prodPos := mul_pos hq abundant
  have pos : 0 < 2 * P - D * (q - 2) := by
    by_contra! h
    have x := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (show 0 ≤ q by omega) (j + 1)) h
    omega
  have one := next 0
  rw [base] at one
  have qNonneg : 0 ≤ q := by omega
  have neg := mul_le_mul_of_nonneg_left (show E j ≤ -1 by omega) qNonneg
  refine ⟨by omega, ?_, ?_⟩
  · nlinarith only [firstDef, one]
  · rw [next]; linarith only [neg]

private lemma index_for_translate {A : Set ℤ} {T L H g r x : ℤ}
    (hr : 0 < r) (wide : r * g ≤ H - L + 1) (last : T ∈ A)
    (gap : ∀ k : ℤ, 0 ≤ k → k < T → ∃ i ∈ A, k - g < i ∧ i ≤ k)
    (lo : L ≤ x) (hi : x ≤ H + r * T) :
    ∃ i ∈ A, L ≤ x - r * i ∧ x - r * i ≤ H := by
  by_cases finished : L + r * T ≤ x
  · exact ⟨T, last, by omega, by omega⟩
  let k := (x - L) / r
  have kp : k < T := Int.ediv_lt_of_lt_mul hr (by rw [mul_comm T r]; omega)
  obtain ⟨i, mem, lower, upper⟩ := gap k (Int.ediv_nonneg (by omega) (by omega)) kp
  have decomp := Int.emod_add_mul_ediv (x - L) r
  change (x - L) % r + r * k = x - L at decomp
  have remLo := Int.emod_nonneg (x - L) (by omega : r ≠ 0)
  have remHi := Int.emod_lt_of_pos (x - L) hr
  have left := mul_le_mul_of_nonneg_left upper (le_of_lt hr)
  have right := mul_le_mul_of_nonneg_left (show k - g + 1 ≤ i by omega) (le_of_lt hr)
  rw [mul_add, mul_sub, mul_one] at right
  exact ⟨i, mem, by omega, by omega⟩

private lemma middle_next {A B C : Set ℤ} {T P b L g r : ℤ}
    (hr : 0 < r) (wide : r * g ≤ P - 2 * L + 1) (overlap : b + 2 * L ≤ P + r * T + 1)
    (endA : T ∈ A) (gap : ∀ k : ℤ, 0 ≤ k → k < T → ∃ i ∈ A, k - g < i ∧ i ≤ k)
    (central : ∀ y : ℤ, L ≤ y → y ≤ P - L → y ∈ B)
    (layers : ∀ i ∈ A, ∀ y ∈ B, y + r * i ∈ C ∧ b + y + r * i ∈ C) :
    ∀ x : ℤ, L ≤ x → x ≤ b + P + r * T - L → x ∈ C := by
  intro x low high
  by_cases first : x ≤ P - L + r * T
  · obtain ⟨i, hi, h, k⟩ :=
      index_for_translate hr (show r * g ≤ (P - L) - L + 1 by omega) endA gap low first
    have rep := (layers i hi _ (central _ h k)).1
    convert rep using 1; ring
  · obtain ⟨i, hi, h, k⟩ :=
      index_for_translate (x := x - b) hr (show r * g ≤ (P - L) - L + 1 by omega) endA gap
        (show L ≤ x - b by omega) (show x - b ≤ (P - L) + r * T by omega)
    have rep := (layers i hi _ (central _ h k)).2
    convert rep using 1; ring

/-- A cofactor `b` certified with central interval `[L, ProperSum b - L]` and low-end
downward and upward gaps at most `G`. -/
private structure CertifiedBase (b L G : ℕ) : Prop where
  b_gt_one : 1 < b
  L_pos : 1 ≤ L
  G_pos : 1 ≤ G
  large : ((2 * G + 1) * (2 * L + 8 * G + 8) : ℤ) ≤ ProperSum b
  middle : ∀ y : ℤ, (L : ℤ) ≤ y → y ≤ ProperSum b - L → Represented b y
  lowDown : ∀ k : ℤ, 0 ≤ k → k < (L : ℤ) → ∃ i : ℤ, Represented b i ∧ k - G < i ∧ i ≤ k
  lowUp : ∀ t : ℤ, 1 ≤ t → t < (L : ℤ) → ∃ i : ℤ, Represented b i ∧ t ≤ i ∧ i < t + G

private lemma CertifiedBase.full_gap {b L G : ℕ} (hb : CertifiedBase b L G) :
    ∀ k : ℤ, 0 ≤ k → k < ProperSum b → ∃ i : ℤ, Represented b i ∧ k - G < i ∧ i ≤ k := by
  intro k hk0 hkP
  have hG : (1 : ℤ) ≤ G := by exact_mod_cast hb.G_pos
  have hL : (1 : ℤ) ≤ L := by exact_mod_cast hb.L_pos
  by_cases h1 : k < L
  · exact hb.lowDown k hk0 h1
  · by_cases h2 : k ≤ ProperSum b - L
    · exact ⟨k, hb.middle k (by omega) h2, by omega, le_rfl⟩
    · have ht1 : 1 ≤ ProperSum b - k := by omega
      have ht2 : ProperSum b - k < L := by omega
      obtain ⟨j, hj, hj1, hj2⟩ := hb.lowUp (ProperSum b - k) ht1 ht2
      refine ⟨ProperSum b - j, represented_compl hj, by omega, by omega⟩

private lemma excess_step {b q : ℕ} (hq : q.Prime) (cop : b.Coprime q) (j : ℕ) :
    Excess (b * q ^ (j + 1)) = q * Excess (b * q ^ j) + (sigma 1 b : ℤ) := by
  have recurEq : sigma 1 (b * q ^ (j + 1)) = q * sigma 1 (b * q ^ j) + sigma 1 b := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right (j + 1)),
      isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right j),
      sigma_one_apply_prime_pow hq, sigma_one_apply_prime_pow hq, geom_sum_succ]
    ring
  dsimp [Excess]
  rw [recurEq]
  push_cast
  ring

private lemma certified_prime_power_pseudoperfect {b q j L G : ℕ}
    (hcert : CertifiedBase b L G) (hq : q.Prime) (cop : b.Coprime q) (q3 : 3 ≤ q)
    (primitive : ∀ d ∈ (b * q ^ (j + 1)).properDivisors, d.Deficient)
    (high : (L : ℤ) ≤ Excess (b * q ^ (j + 1)))
    (simple : j = 0 → 2 ≤ (b : ℤ) - ProperSum b) :
    (b * q ^ (j + 1)).Pseudoperfect := by
  have bpos : 0 < b := by have := hcert.b_gt_one; omega
  have qpos : 0 < q := hq.pos
  have hqZ : (3 : ℤ) ≤ q := by exact_mod_cast q3
  have hLZ : (1 : ℤ) ≤ L := by exact_mod_cast hcert.L_pos
  have hGZ : (1 : ℤ) ≤ G := by exact_mod_cast hcert.G_pos
  have hlarge : ((2 * (G : ℤ) + 1) * (2 * (L : ℤ) + 8 * (G : ℤ) + 8)) ≤ ProperSum b := by
    simpa [Nat.cast_add, Nat.cast_mul] using hcert.large
  have hgap := hcert.full_gap
  have total : Represented b (ProperSum b) := ⟨b.properDivisors, fun _ h => h, rfl⟩
  have zero : Represented b 0 := ⟨∅, by simp, by simp⟩
  have unit : Represented b 1 :=
    ⟨{1}, by simpa using Nat.one_mem_properDivisors_iff_one_lt.mpr hcert.b_gt_one, by simp⟩
  have translate (t : ℕ) (i y : ℤ) (hi : Represented b i) (hy : Represented b y) :
      Represented (b * q ^ (t + 1)) (y + q * i) ∧
      Represented (b * q ^ (t + 1)) (b + y + q * i) := by
    have hdiv : b ∣ b * q ^ t := dvd_mul_right _ _
    have hpos : 0 < b * q ^ t := by positivity
    have hinc : Represented (b * q ^ t) i := represented_mono_dvd hpos hdiv hi
    have holds := represented_layers hpos hdiv (hq.coprime_iff_not_dvd.mp cop.symm) hq.one_lt hinc hy
    convert holds using 2 <;> ring
  apply pseudoperfect_of_represented_excess (by positivity)
  by_cases hj : j = 0
  · subst hj
    simp only [zero_add, pow_one] at high ⊢
    let P := ProperSum b
    let D : ℤ := b - P
    let E := Excess (b * q)
    have formula : E = 2 * P - D * (q - 1) := by
      have first := excess_step hq cop 0
      simp only [pow_zero, pow_one, mul_one, zero_add] at first
      dsimp only [E, P, D]
      rw [first]
      unfold Excess
      rw [sigma_split b]
      ring
    have cases' := final_prime_alternatives hGZ hLZ (simple rfl) hqZ hlarge formula high
    rcases cases' with ⟨wide, join⟩ | ⟨wide, join, cap⟩ | basic
    · have gb := mul_nonneg (show 0 ≤ (G : ℤ) - 1 by omega) (show 0 ≤ (L : ℤ) by omega)
      have gg := mul_self_nonneg (G : ℤ)
      have pL : (L : ℤ) ≤ P := by nlinarith only [hlarge, hGZ, hLZ, gb, gg]
      have prod := mul_nonneg (show 0 ≤ D by linarith [simple rfl]) (show 0 ≤ (q : ℤ) - 1 by omega)
      have hres := middle_next (A := {i | Represented b i}) (B := {y | Represented b y})
        (C := {z | Represented (b * q) z}) (P := P) (T := P) (b := (b : ℤ))
        (by omega : (0 : ℤ) < q) (by simpa only [mul_comm (q : ℤ) (G : ℤ)] using wide)
        (by change (b : ℤ) - P + 2 * L - 1 ≤ q * P at join; omega)
        total hgap hcert.middle
        (fun i hi y hy => by simpa [Set.mem_ofPred_eq, pow_one] using translate 0 i y hi hy)
        E high (by dsimp only [E, P, D] at formula prod ⊢; nlinarith)
      exact hres
    · have eq : P + D = (b : ℤ) := by dsimp [D]; ring
      rcases four_interval_join wide join high cap with h | h | h | h
      · simpa using (translate 0 0 _ zero (hcert.middle _ h.1 h.2)).1
      · simpa using (translate 0 1 _ unit (hcert.middle _ h.1 h.2)).1
      · rw [eq] at h
        have hr := (translate 0 0 _ zero (hcert.middle _ h.1 h.2)).2
        simp only [zero_add, pow_one] at hr
        convert hr using 1; ring
      · rw [eq] at h
        have hr := (translate 0 1 _ unit (hcert.middle _ h.1 h.2)).2
        simp only [zero_add, pow_one] at hr
        convert hr using 1; ring
    · simpa using (translate 0 0 _ zero (hcert.middle _ basic.1 basic.2)).1
  · have earlier (k : ℕ) (hk : k < j + 1) : ProperSum (b * q ^ k) < (b * q ^ k : ℕ) := by
      have mem : b * q ^ k ∈ (b * q ^ (j + 1)).properDivisors := Nat.mem_properDivisors.mpr
        ⟨Nat.mul_dvd_mul_left b (pow_dvd_pow q hk.le),
         Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hq.one_lt hk) (by omega)⟩
      have defic := primitive _ mem
      change ∑ d ∈ (b * q ^ k).properDivisors, d < b * q ^ k at defic
      dsimp only [ProperSum]
      rw [← Nat.cast_sum]
      exact_mod_cast defic
    have earlierEx (k : ℕ) (hk : k < j + 1) : Excess (b * q ^ k) < 0 := by
      dsimp only [Excess]
      rw [sigma_split]
      linarith only [earlier k hk]
    let P := ProperSum b
    let D : ℤ := b - P
    let E (t : ℕ) := Excess (b * q ^ t)
    have defBase : P < b := by simpa using earlier 0 (by omega)
    have dPos : 0 < D := by dsimp [D]; omega
    have sig : (sigma 1 b : ℤ) = 2 * P + D := by rw [sigma_split]; dsimp [P, D]; ring
    have sPos : 0 < 2 * P + D := by rw [← sig]; exact_mod_cast (sigma_pos_iff.mpr bpos : 0 < sigma 1 b)
    have recurEq (t : ℕ) : E (t + 1) = (q : ℤ) * E t + (2 * P + D) := by
      rw [← sig]; exact excess_step hq cop t
    have e0 : E 0 = -D := by simp only [E, pow_zero, mul_one, Excess, sig]; dsimp [D]; ring
    have one : E 1 < 0 := by simpa [E] using earlierEx 1 (by omega)
    obtain ⟨l, h, e⟩ := repeat_from_excess (q := (q : ℤ)) (by omega) sPos
      E e0 recurEq j one (earlierEx j (by omega)) (lt_of_lt_of_le (by omega) high)
    have alt := repeated_alternatives (P := P) (D := D) (E := E (j + 1))
      hGZ hLZ dPos hqZ hlarge l h e
    rcases alt with ⟨wide, join, cap⟩ | ⟨wide, join, cap⟩
    · exact middle_next (A := {i | Represented b i}) (B := {y | Represented b y})
        (C := {z | Represented (b * q ^ (j + 1)) z}) (P := P) (T := P) (b := (b : ℤ))
        (by omega : (0 : ℤ) < q) (by simpa only [mul_comm (q : ℤ) (G : ℤ)] using wide)
        (by change (b : ℤ) - P + 2 * L - 1 ≤ q * P at join; omega)
        total hgap hcert.middle (fun i hi y hy => translate j i y hi hy)
        _ high (by dsimp only [E, P, D] at cap ⊢; linarith)
    · have bEq : P + D = (b : ℤ) := by dsimp [D]; ring
      rcases four_interval_join wide join high cap with h | h | h | h
      · simpa using (translate j 0 _ zero (hcert.middle _ h.1 h.2)).1
      · simpa using (translate j 1 _ unit (hcert.middle _ h.1 h.2)).1
      · rw [bEq] at h
        convert (translate j 0 _ zero (hcert.middle _ h.1 h.2)).2 using 1; ring
      · rw [bEq] at h
        convert (translate j 1 _ unit (hcert.middle _ h.1 h.2)).2 using 1; ring

/- ### Section 3: Hereditary Propagation of `CertifiedBase` -/

private lemma properSum_mul_prime_coprime {b p : ℕ} (hp : p.Prime) (cop : b.Coprime p) :
    ProperSum (b * p) = (b : ℤ) + ProperSum b + (p : ℤ) * ProperSum b := by
  have hsig : sigma 1 (b * p) = sigma 1 b * (p + 1) := by
    have hsp : sigma 1 p = p + 1 := by
      simpa [sigmaPP, pow_one] using (sigmaPP_eq_sigma_one_prime_pow hp 1).symm
    rw [isMultiplicative_sigma.map_mul_of_coprime cop, hsp]
  have h1 := sigma_split (b * p)
  have h2 := sigma_split b
  have h3 : (sigma 1 (b * p) : ℤ) = (sigma 1 b : ℤ) * ((p : ℤ) + 1) := by exact_mod_cast hsig
  push_cast at h1
  rw [h2] at h3
  nlinarith

private lemma properSum_mul_prime_pow_succ {c p a : ℕ} (hp : p.Prime) (cop : c.Coprime p) :
    ProperSum (c * p ^ (a + 1)) = (sigma 1 c : ℤ) + (p : ℤ) * ProperSum (c * p ^ a) := by
  have hsig : sigma 1 (c * p ^ (a + 1)) = sigma 1 c + p * sigma 1 (c * p ^ a) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right (a + 1)),
      isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right a),
      ← sigmaPP_eq_sigma_one_prime_pow hp (a + 1), ← sigmaPP_eq_sigma_one_prime_pow hp a, sigmaPP]
    ring
  have h1 : (sigma 1 (c * p ^ (a + 1)) : ℤ) = ProperSum (c * p ^ (a + 1)) + (c : ℤ) * (p : ℤ) ^ a * (p : ℤ) := by
    rw [sigma_split]; push_cast [pow_succ]; ring
  have h2 : (sigma 1 (c * p ^ a) : ℤ) = ProperSum (c * p ^ a) + (c : ℤ) * (p : ℤ) ^ a := by
    rw [sigma_split]; push_cast; ring
  have h3 : (sigma 1 (c * p ^ (a + 1)) : ℤ) = (sigma 1 c : ℤ) + (p : ℤ) * (sigma 1 (c * p ^ a) : ℤ) := by
    exact_mod_cast hsig
  rw [h2] at h3
  nlinarith

private lemma properSum_le_of_dvd {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) :
    ProperSum a ≤ ProperSum b := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hda, hlt⟩ := Nat.mem_properDivisors.mp hd
    exact Nat.mem_properDivisors.mpr ⟨hda.trans hab, lt_of_lt_of_le hlt (Nat.le_of_dvd hb hab)⟩
  · intro _ _ _; exact Nat.cast_nonneg _

/-- A cofactor `b` certified with central interval `[L, ProperSum b - L]` and low-end
downward and upward gaps at most `G`, without the size floor `large`. -/
private structure PreCertifiedBase (b L G : ℕ) : Prop where
  b_gt_one : 1 < b
  L_pos : 1 ≤ L
  G_pos : 1 ≤ G
  middle : ∀ y : ℤ, (L : ℤ) ≤ y → y ≤ ProperSum b - L → Represented b y
  lowDown : ∀ k : ℤ, 0 ≤ k → k < (L : ℤ) → ∃ i : ℤ, Represented b i ∧ k - G < i ∧ i ≤ k
  lowUp : ∀ t : ℤ, 1 ≤ t → t < (L : ℤ) → ∃ i : ℤ, Represented b i ∧ t ≤ i ∧ i < t + G

private lemma PreCertifiedBase.full_gap {b L G : ℕ} (hb : PreCertifiedBase b L G) :
    ∀ k : ℤ, 0 ≤ k → k < ProperSum b → ∃ i : ℤ, Represented b i ∧ k - G < i ∧ i ≤ k := by
  intro k hk0 hkP
  have hG : (1 : ℤ) ≤ G := by exact_mod_cast hb.G_pos
  have hL : (1 : ℤ) ≤ L := by exact_mod_cast hb.L_pos
  by_cases h1 : k < L
  · exact hb.lowDown k hk0 h1
  · by_cases h2 : k ≤ ProperSum b - L
    · exact ⟨k, hb.middle k (by omega) h2, by omega, le_rfl⟩
    · have ht1 : 1 ≤ ProperSum b - k := by omega
      have ht2 : ProperSum b - k < L := by omega
      obtain ⟨j, hj, hj1, hj2⟩ := hb.lowUp (ProperSum b - k) ht1 ht2
      refine ⟨ProperSum b - j, represented_compl hj, by omega, by omega⟩

private lemma PreCertifiedBase.toCertifiedBase {b L G : ℕ} (hb : PreCertifiedBase b L G)
    (hlarge : ((2 * G + 1) * (2 * L + 8 * G + 8) : ℤ) ≤ ProperSum b) :
    CertifiedBase b L G :=
  ⟨hb.b_gt_one, hb.L_pos, hb.G_pos, hlarge, hb.middle, hb.lowDown, hb.lowUp⟩

private lemma CertifiedBase.toPre {b L G : ℕ} (hb : CertifiedBase b L G) :
    PreCertifiedBase b L G :=
  ⟨hb.b_gt_one, hb.L_pos, hb.G_pos, hb.middle, hb.lowDown, hb.lowUp⟩

private lemma preCertifiedBase_mul_new_prime {b p L G : ℕ}
    (hb : PreCertifiedBase b L G) (hp : p.Prime) (cop : b.Coprime p)
    (hwide : (p : ℤ) * G ≤ ProperSum b - 2 * L + 1)
    (hover : (b : ℤ) + 2 * L ≤ ProperSum b + (p : ℤ) * ProperSum b + 1) :
    PreCertifiedBase (b * p) L G := by
  have hbpos : 0 < b := by have := hb.b_gt_one; omega
  have hbp : 1 < b * p := by nlinarith [hb.b_gt_one, hp.one_lt]
  have hPeq := properSum_mul_prime_coprime hp cop
  refine ⟨hbp, hb.L_pos, hb.G_pos, ?_, ?_, ?_⟩
  · intro y hy1 hy2
    have htotal : Represented b (ProperSum b) := ⟨b.properDivisors, fun _ h => h, rfl⟩
    have hlayers : ∀ i, Represented b i → ∀ z, Represented b z →
        Represented (b * p) (z + (p : ℤ) * i) ∧ Represented (b * p) ((b : ℤ) + z + (p : ℤ) * i) := by
      intro i hi z hz
      simpa [mul_comm p b] using
        represented_layers hbpos (dvd_refl b) (hp.coprime_iff_not_dvd.mp cop.symm) hp.one_lt hi hz
    exact middle_next (A := fun i => Represented b i) (B := fun z => Represented b z)
      (C := fun x => Represented (b * p) x) (T := ProperSum b) (P := ProperSum b) (b := (b : ℤ))
      (by exact_mod_cast hp.pos) hwide hover htotal hb.full_gap hb.middle hlayers y hy1
      (by linarith [hPeq])
  · intro k hk0 hkL
    obtain ⟨i, hi, hi1, hi2⟩ := hb.lowDown k hk0 hkL
    exact ⟨i, represented_mono_dvd (by positivity) (dvd_mul_right b p) hi, hi1, hi2⟩
  · intro t ht1 htL
    obtain ⟨i, hi, hi1, hi2⟩ := hb.lowUp t ht1 htL
    exact ⟨i, represented_mono_dvd (by positivity) (dvd_mul_right b p) hi, hi1, hi2⟩

private lemma certifiedBase_mul_new_prime {b p L G : ℕ}
    (hb : CertifiedBase b L G) (hp : p.Prime) (cop : b.Coprime p)
    (hwide : (p : ℤ) * G ≤ ProperSum b - 2 * L + 1)
    (hover : (b : ℤ) + 2 * L ≤ ProperSum b + (p : ℤ) * ProperSum b + 1) :
    CertifiedBase (b * p) L G := by
  have hbpos : 0 < b := by have := hb.b_gt_one; omega
  have hPge : ProperSum b ≤ ProperSum (b * p) := properSum_le_of_dvd (Nat.mul_pos hbpos hp.pos) (dvd_mul_right b p)
  exact (preCertifiedBase_mul_new_prime hb.toPre hp cop hwide hover).toCertifiedBase (hb.large.trans hPge)

/-- Complete-residue-system covering condition allowing `PreCertifiedBase b L G` /
`CertifiedBase b L G` to propagate to `b * p ^ k` for all `k`. -/
private def RaiseOk (b p L : ℕ) : Prop :=
  ∃ (c a M : ℕ),
    b = c * p ^ a ∧ 1 ≤ a ∧ c.Coprime p ∧ 0 < c ∧
    ((p + 1) * L : ℤ) ≤ (p : ℤ) * ProperSum c + 1 ∧
    (M : ℤ) ≤ ProperSum b + 1 - ((p + 1) * L : ℤ) ∧
    ∀ r : ℕ, r < p → ∃ y : ℕ, y % p = r ∧ y ≤ M ∧ DivRepresented c (y : ℤ)

private lemma preCertifiedBase_mul_existing_prime {b p L G : ℕ}
    (hb : PreCertifiedBase b L G) (hp : p.Prime) (hr : RaiseOk b p L) :
    PreCertifiedBase (b * p) L G ∧ RaiseOk (b * p) p L := by
  obtain ⟨c, a, M, hreq, hra, hrcop, hrcpos, hrsmallL, hrMbnd, hrres⟩ := hr
  have hbpos : 0 < b := by have := hb.b_gt_one; omega
  have hppos : 0 < p := hp.pos
  have hbp : 1 < b * p := by nlinarith [hb.b_gt_one, hp.one_lt]
  have hPge : ProperSum b ≤ ProperSum (b * p) := properSum_le_of_dvd (by positivity) (dvd_mul_right b p)
  have hbeq : b * p = c * p ^ (a + 1) := by rw [hreq, pow_succ]; ring
  have hPeq : ProperSum (b * p) = (sigma 1 c : ℤ) + (p : ℤ) * ProperSum b := by
    rw [hbeq, properSum_mul_prime_pow_succ hp hrcop, ← hreq]
  have hPb_ge : (sigma 1 c : ℤ) + (p : ℤ) * ProperSum c ≤ ProperSum b := by
    have h1 : c * p ∣ b := by
      rw [hreq]
      exact Nat.mul_dvd_mul_left c (dvd_pow_self p (by omega : a ≠ 0))
    have h2 := properSum_le_of_dvd hbpos h1
    have h3 : ProperSum (c * p) = (sigma 1 c : ℤ) + (p : ℤ) * ProperSum c := by
      simpa [pow_zero, pow_one, mul_one] using properSum_mul_prime_pow_succ (a := 0) hp hrcop
    linarith
  have hcert : PreCertifiedBase (b * p) L G := by
    refine ⟨hbp, hb.L_pos, hb.G_pos, ?_, ?_, ?_⟩
    · intro x hx1 hx2
      by_cases hleft : x ≤ ProperSum b - L
      · exact represented_mono_dvd (by positivity) (dvd_mul_right b p) (hb.middle x hx1 hleft)
      · by_cases hright : ProperSum (b * p) - ProperSum b + L ≤ x
        · have hx' : (L : ℤ) ≤ ProperSum (b * p) - x := by omega
          have hx'' : ProperSum (b * p) - x ≤ ProperSum b - L := by omega
          have hrep := represented_mono_dvd (by positivity) (dvd_mul_right b p) (hb.middle _ hx' hx'')
          simpa using represented_compl hrep
        · have hMZ : (M : ℤ) ≤ ProperSum b + 1 - ((p : ℤ) + 1) * (L : ℤ) := by
            simpa [Nat.cast_add, Nat.cast_mul] using hrMbnd
          have hx_ge : (M : ℤ) + (p : ℤ) * (L : ℤ) ≤ x := by linarith
          have hx_le : x ≤ (p : ℤ) * (ProperSum b - L) := by
            have hsm : ((p : ℤ) + 1) * (L : ℤ) ≤ (p : ℤ) * ProperSum c + 1 := by
              simpa [Nat.cast_add, Nat.cast_mul] using hrsmallL
            linarith
          let xN : ℕ := x.toNat
          have hxN_eq : (xN : ℤ) = x := Int.toNat_of_nonneg (by
            have : (0 : ℤ) ≤ (M : ℤ) + (p : ℤ) * (L : ℤ) := by positivity
            linarith)
          let r : ℕ := xN % p
          have hr_lt : r < p := Nat.mod_lt xN hppos
          obtain ⟨y, hy_mod, hy_le, hy_rep⟩ := hrres r hr_lt
          have hy_le_xN : y ≤ xN := by
            have h1 : (M : ℤ) ≤ (xN : ℤ) := by
              have : (0 : ℤ) ≤ (p : ℤ) * (L : ℤ) := by positivity
              linarith
            omega
          let i : ℕ := (xN - y) / p
          have hdvd_diff : p ∣ xN - y := by
            have hmod : (xN - y) % p = 0 := by
              have h1 : xN = p * (xN / p) + xN % p := (Nat.div_add_mod xN p).symm
              have h2 : y = p * (y / p) + y % p := (Nat.div_add_mod y p).symm
              have h3 : xN % p = y % p := hy_mod.symm
              have h4 : xN - y = p * (xN / p - y / p) := by
                have hdiv_le : y / p ≤ xN / p := Nat.div_le_div_right hy_le_xN
                zify [hy_le_xN, hdiv_le] at h1 h2 h3 ⊢
                nlinarith
              rw [h4, Nat.mul_mod_right]
            exact Nat.dvd_of_mod_eq_zero hmod
          have hxyN : xN = y + p * i := by
            have h1 : p * i = xN - y := Nat.mul_div_cancel' hdvd_diff
            omega
          have hxy : x = (y : ℤ) + (p : ℤ) * (i : ℤ) := by
            rw [← hxN_eq, hxyN]; push_cast; ring
          have hi_lo : (L : ℤ) ≤ (i : ℤ) := by
            have h1 : (p : ℤ) * (L : ℤ) ≤ (p : ℤ) * (i : ℤ) := by
              have : (y : ℤ) ≤ (M : ℤ) := by exact_mod_cast hy_le
              linarith
            nlinarith
          have hi_hi : (i : ℤ) ≤ ProperSum b - L := by
            have h1 : (p : ℤ) * (i : ℤ) ≤ (p : ℤ) * (ProperSum b - L) := by
              have : (0 : ℤ) ≤ (y : ℤ) := Nat.cast_nonneg y
              linarith
            nlinarith
          have hi_rep : Represented b (i : ℤ) := hb.middle (i : ℤ) hi_lo hi_hi
          have hcm : c ∣ b := by rw [hreq]; exact dvd_mul_right _ _
          have hndvd : ¬ p ∣ c := hp.coprime_iff_not_dvd.mp hrcop.symm
          have hcomb := represented_combine hbpos hcm hndvd hp.one_lt hy_rep hi_rep
          rw [mul_comm p b] at hcomb
          rwa [hxy]
    · intro k hk0 hkL
      obtain ⟨i, hi, hi1, hi2⟩ := hb.lowDown k hk0 hkL
      exact ⟨i, represented_mono_dvd (by positivity) (dvd_mul_right b p) hi, hi1, hi2⟩
    · intro t ht1 htL
      obtain ⟨i, hi, hi1, hi2⟩ := hb.lowUp t ht1 htL
      exact ⟨i, represented_mono_dvd (by positivity) (dvd_mul_right b p) hi, hi1, hi2⟩
  refine ⟨hcert, ⟨c, a + 1, M, hbeq, by omega, hrcop, hrcpos, hrsmallL, ?_, hrres⟩⟩
  linarith [hrMbnd, hPge]

private lemma preCertifiedBase_mul_existing_prime_pow {b p L G : ℕ}
    (hb : PreCertifiedBase b L G) (hp : p.Prime) (hr : RaiseOk b p L) :
    ∀ k : ℕ, PreCertifiedBase (b * p ^ k) L G ∧ RaiseOk (b * p ^ k) p L
  | 0 => by simpa using ⟨hb, hr⟩
  | k + 1 => by
    obtain ⟨hbk, hrk⟩ := preCertifiedBase_mul_existing_prime_pow hb hp hr k
    obtain ⟨h1, h2⟩ := preCertifiedBase_mul_existing_prime hbk hp hrk
    rw [pow_succ, ← mul_assoc]
    exact ⟨h1, h2⟩

private lemma preCertifiedBase_mul_new_prime_pow {b p a L G : ℕ}
    (hb : PreCertifiedBase b L G) (hp : p.Prime) (cop : b.Coprime p) (ha : 1 ≤ a)
    (hwide : (p : ℤ) * G ≤ ProperSum b - 2 * L + 1)
    (hover : (b : ℤ) + 2 * L ≤ ProperSum b + (p : ℤ) * ProperSum b + 1)
    (hraise : 1 < a →
      ((p + 1) * L : ℤ) ≤ (p : ℤ) * ProperSum b + 1 ∧
      ((L + p - 1 : ℕ) : ℤ) ≤ ProperSum (b * p) + 1 - ((p + 1) * L : ℤ)) :
    PreCertifiedBase (b * p ^ a) L G := by
  have h1 : PreCertifiedBase (b * p) L G := preCertifiedBase_mul_new_prime hb hp cop hwide hover
  by_cases ha1 : a = 1
  · subst ha1; simpa using h1
  · obtain ⟨hsm, hMbnd⟩ := hraise (by omega)
    have hbpos : 0 < b := by have := hb.b_gt_one; omega
    have hppos : 0 < p := hp.pos
    have hr : RaiseOk (b * p) p L := by
      refine ⟨b, 1, L + p - 1, by simp, le_rfl, cop, hbpos, hsm, hMbnd, fun r hrlt => ?_⟩
      let k := (r + p - L % p) % p
      have hk_lt : k < p := Nat.mod_lt _ hppos
      refine ⟨L + k, ?_, by omega, ?_⟩
      · dsimp [k]
        have hdiv : L = p * (L / p) + L % p := (Nat.div_add_mod L p).symm
        have hlm : L % p < p := Nat.mod_lt L hppos
        rw [Nat.add_mod_mod, show L + (r + p - L % p) = p * (L / p + 1) + r by rw [Nat.mul_add, mul_one]; omega,
          Nat.mul_add_mod, Nat.mod_eq_of_lt hrlt]
      · have hG1 : (1 : ℤ) ≤ G := by exact_mod_cast hb.G_pos
        have hp1 : (p : ℤ) ≤ (p : ℤ) * G := by nlinarith
        have hmid : Represented b ((L + k : ℕ) : ℤ) :=
          hb.middle _ (by push_cast; omega) (by push_cast; linarith)
        obtain ⟨s, hs, hsum⟩ := hmid
        exact ⟨s, hs.trans Nat.properDivisors_subset_divisors, hsum⟩
    have hpow := (preCertifiedBase_mul_existing_prime_pow h1 hp hr (a - 1)).1
    have heq : b * p * p ^ (a - 1) = b * p ^ a := by
      rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel ha]
    rwa [heq] at hpow

private lemma certifiedBase_mul_existing_prime {b p L G : ℕ}
    (hb : CertifiedBase b L G) (hp : p.Prime) (hr : RaiseOk b p L) :
    CertifiedBase (b * p) L G ∧ RaiseOk (b * p) p L := by
  have hbpos : 0 < b := by have := hb.b_gt_one; omega
  have hPge : ProperSum b ≤ ProperSum (b * p) := properSum_le_of_dvd (Nat.mul_pos hbpos hp.pos) (dvd_mul_right b p)
  obtain ⟨hpre, hr'⟩ := preCertifiedBase_mul_existing_prime hb.toPre hp hr
  exact ⟨hpre.toCertifiedBase (hb.large.trans hPge), hr'⟩

private lemma raiseOk_mul_other_prime {b p q L : ℕ} (hb : 0 < b) (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hr : RaiseOk b p L) : RaiseOk (b * q) p L := by
  obtain ⟨c, a, M, hreq, hra, hrcop, hrcpos, hrsmallL, hrMbnd, hrres⟩ := hr
  have hcq_pos : 0 < c * q := by positivity [hrcpos, hq.pos]
  have hcop : (c * q).Coprime p :=
    hrcop.mul_left ((Nat.coprime_primes hq hp).mpr hne.symm)
  have hPge_c : ProperSum c ≤ ProperSum (c * q) :=
    properSum_le_of_dvd hcq_pos (dvd_mul_right c q)
  have hPge_b : ProperSum b ≤ ProperSum (b * q) :=
    properSum_le_of_dvd (by positivity [hb, hq.pos]) (dvd_mul_right b q)
  refine ⟨c * q, a, M, by rw [hreq]; ring, hra, hcop, hcq_pos, ?_, ?_, ?_⟩
  · have : (p : ℤ) * ProperSum c ≤ (p : ℤ) * ProperSum (c * q) :=
      mul_le_mul_of_nonneg_left hPge_c (Nat.cast_nonneg p)
    linarith [hrsmallL]
  · linarith [hrMbnd, hPge_b]
  · intro r hrl
    obtain ⟨y, hymod, hyle, hyrep⟩ := hrres r hrl
    exact ⟨y, hymod, hyle, divRepresented_mono_dvd hcq_pos.ne' (dvd_mul_right c q) hyrep⟩

/- ### Section 4: Interval-List Subset-Sum Engine (Zero Bitsets!) -/

private def insertInterval (a b : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(a, b)]
  | (c, d) :: rest =>
    if b + 1 < c then (a, b) :: (c, d) :: rest
    else if d + 1 < a then (c, d) :: insertInterval a b rest
    else insertInterval (min a c) (max b d) rest

private def mergeIntervals (xs ys : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  xs.foldl (fun acc iv => insertInterval iv.1 iv.2 acc) ys

private def addDivInterval (ivs : List (ℕ × ℕ)) (d : ℕ) : List (ℕ × ℕ) :=
  if ivs.isEmpty || 32 < ivs.length then []
  else mergeIntervals (ivs.map fun iv => (iv.1 + d, iv.2 + d)) ivs

private def intervalSums (ds : List ℕ) : List (ℕ × ℕ) :=
  ds.foldl addDivInterval [(0, 0)]

private def InIntervals (ivs : List (ℕ × ℕ)) (x : ℕ) : Prop :=
  ∃ iv ∈ ivs, iv.1 ≤ x ∧ x ≤ iv.2

private lemma inIntervals_insertInterval {a b x : ℕ} {ivs : List (ℕ × ℕ)}
    (hx : InIntervals (insertInterval a b ivs) x) :
    (a ≤ x ∧ x ≤ b) ∨ InIntervals ivs x := by
  induction ivs generalizing a b with
  | nil =>
    obtain ⟨iv, hiv, h1, h2⟩ := hx
    simp only [insertInterval, List.mem_singleton] at hiv
    subst hiv; exact Or.inl ⟨h1, h2⟩
  | cons cd rest ih =>
    rcases cd with ⟨c, d⟩
    unfold insertInterval at hx
    split_ifs at hx with h1 h2
    · obtain ⟨iv, hiv, hx1, hx2⟩ := hx
      simp only [List.mem_cons] at hiv
      rcases hiv with rfl | hmem
      · exact Or.inl ⟨hx1, hx2⟩
      · exact Or.inr ⟨iv, List.mem_cons.mpr hmem, hx1, hx2⟩
    · obtain ⟨iv, hiv, hx1, hx2⟩ := hx
      simp only [List.mem_cons] at hiv
      rcases hiv with rfl | hmem
      · exact Or.inr ⟨(c, d), List.mem_cons_self, hx1, hx2⟩
      · rcases ih ⟨iv, hmem, hx1, hx2⟩ with hab | hrest
        · exact Or.inl hab
        · obtain ⟨w, hw, hw1, hw2⟩ := hrest
          exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hw1, hw2⟩
    · rcases ih hx with ⟨hm1, hm2⟩ | hrest
      · by_cases hax : a ≤ x ∧ x ≤ b
        · exact Or.inl hax
        · exact Or.inr ⟨(c, d), List.mem_cons_self, by omega, by omega⟩
      · obtain ⟨w, hw, hw1, hw2⟩ := hrest
        exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hw1, hw2⟩

private lemma inIntervals_mergeIntervals {xs ys : List (ℕ × ℕ)} {x : ℕ}
    (hx : InIntervals (mergeIntervals xs ys) x) :
    InIntervals xs x ∨ InIntervals ys x := by
  unfold mergeIntervals at hx
  induction xs generalizing ys with
  | nil => exact Or.inr hx
  | cons iv rest ih =>
    simp only [List.foldl_cons] at hx
    rcases ih hx with hrest | hins
    · obtain ⟨w, hw, hw1, hw2⟩ := hrest
      exact Or.inl ⟨w, List.mem_cons_of_mem _ hw, hw1, hw2⟩
    · rcases inIntervals_insertInterval hins with hcur | hy
      · exact Or.inl ⟨iv, List.mem_cons_self, hcur.1, hcur.2⟩
      · exact Or.inr hy

private def ListSubSum (ds : List ℕ) (x : ℕ) : Prop :=
  ∃ sub : List ℕ, sub.Sublist ds ∧ sub.sum = x

private lemma listSubSum_sound_finset {ds : List ℕ} {S : Finset ℕ} (hnodup : ds.Nodup)
    (hsub : ∀ d ∈ ds, d ∈ S) {x : ℕ} (hx : ListSubSum ds x) :
    ∃ s : Finset ℕ, s ⊆ S ∧ (∑ d ∈ s, (d : ℤ)) = (x : ℤ) := by
  obtain ⟨sub, hsubl, rfl⟩ := hx
  have hnd : sub.Nodup := hnodup.sublist hsubl
  refine ⟨sub.toFinset, ?_, ?_⟩
  · intro d hd
    exact hsub d (hsubl.subset (List.mem_toFinset.mp hd))
  · rw [List.sum_toFinset _ hnd]
    simp

private lemma intervalSums_sound (ds : List ℕ) :
    ∀ x, InIntervals (intervalSums ds) x → ListSubSum ds x := by
  have hfold : ∀ (acc : List (ℕ × ℕ)) (pre : List ℕ),
      (∀ x, InIntervals acc x → ListSubSum pre x) →
      ∀ (rem : List ℕ) (x : ℕ),
        InIntervals (rem.foldl addDivInterval acc) x → ListSubSum (pre ++ rem) x := by
    intro acc pre hpre rem
    induction rem generalizing acc pre with
    | nil =>
      intro x hx
      simpa using hpre x hx
    | cons d rest ih =>
      intro x hx
      simp only [List.foldl_cons] at hx
      have hstep : ∀ y, InIntervals (addDivInterval acc d) y → ListSubSum (pre ++ [d]) y := by
        intro y hy
        unfold addDivInterval at hy
        split_ifs at hy with hcap
        · obtain ⟨iv, hiv, _⟩ := hy; simp at hiv
        · rcases inIntervals_mergeIntervals hy with hshift | hold
          · obtain ⟨iv, hiv, hy1, hy2⟩ := hshift
            rw [List.mem_map] at hiv
            obtain ⟨⟨a, b⟩, hab, rfl⟩ := hiv
            dsimp only at hy1 hy2
            have hy_ge : d ≤ y := by omega
            obtain ⟨sub, hsub, hsum⟩ := hpre (y - d) ⟨(a, b), hab, by omega, by omega⟩
            refine ⟨sub ++ [d], hsub.append (List.Sublist.refl [d]), ?_⟩
            simp [hsum]; omega
          · obtain ⟨sub, hsub, hsum⟩ := hpre y hold
            exact ⟨sub, by simpa using hsub.append (List.nil_sublist [d]), hsum⟩
      have hres := ih (addDivInterval acc d) (pre ++ [d]) hstep x hx
      simpa [List.append_assoc] using hres
  intro x hx
  have h0 : ∀ y, InIntervals [(0, 0)] y → ListSubSum [] y := by
    intro y ⟨iv, hiv, h1, h2⟩
    simp only [List.mem_singleton] at hiv
    subst hiv
    exact ⟨[], List.Sublist.refl [], by simp; omega⟩
  simpa using hfold [(0, 0)] [] h0 ds x hx

/- ### Section 5: Factorized Lists, Divisor Generation, and `CertifiedBase` Checkers -/

private def valF : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, a) :: rest => p ^ a * valF rest

private def sigF : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, a) :: rest => sigmaPP p a * sigF rest

private def ValidFactors : List (ℕ × ℕ) → Prop
  | [] => True
  | (p, a) :: rest =>
    p.Prime ∧ 1 ≤ a ∧ (∀ q ∈ rest, p < q.1) ∧ ValidFactors rest

private lemma coprime_valF_of_lt {p : ℕ} (hp : p.Prime) :
    ∀ {F : List (ℕ × ℕ)}, ValidFactors F → (∀ q ∈ F, p < q.1) → p.Coprime (valF F)
  | [], _, _ => Nat.coprime_one_right p
  | (q, b) :: rest, ⟨hq, _, _, hrest⟩, hlt => by
    have hpq : p ≠ q := ne_of_lt (hlt (q, b) List.mem_cons_self)
    have h1 : p.Coprime (q ^ b) := ((Nat.coprime_primes hp hq).mpr hpq).pow_right b
    have h2 : p.Coprime (valF rest) :=
      coprime_valF_of_lt hp hrest (fun r hr => hlt r (List.mem_cons_of_mem _ hr))
    simpa [valF] using h1.mul_right h2

private lemma valF_pos : ∀ {F : List (ℕ × ℕ)}, ValidFactors F → 0 < valF F
  | [], _ => Nat.zero_lt_one
  | (p, a) :: rest, ⟨hp, _, _, hrest⟩ => by
    rw [valF]; exact Nat.mul_pos (pow_pos hp.pos a) (valF_pos hrest)

private lemma sigF_eq_sigma_one : ∀ {F : List (ℕ × ℕ)}, ValidFactors F → sigF F = sigma 1 (valF F)
  | [], _ => by simp [sigF, valF]
  | (p, a) :: rest, ⟨hp, _, hlt, hrest⟩ => by
    rw [sigF, valF]
    have hcop : (p ^ a).Coprime (valF rest) := (coprime_valF_of_lt hp hrest hlt).pow_left a
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigmaPP_eq_sigma_one_prime_pow hp,
      sigF_eq_sigma_one hrest]

private lemma properSum_valF {F : List (ℕ × ℕ)} (hF : ValidFactors F) :
    ProperSum (valF F) = (sigF F : ℤ) - (valF F : ℤ) := by
  have h1 := sigma_split (valF F)
  rw [← sigF_eq_sigma_one hF] at h1
  linarith

private def mulPows (p : ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | 0, pw, ds => ds.map (· * pw)
  | k + 1, pw, ds => ds.map (· * pw) ++ mulPows p k (pw * p) ds

private def allDivsF : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | (p, a) :: rest => mulPows p a 1 (allDivsF rest)

private def smallDivsF (lim : ℕ) (F : List (ℕ × ℕ)) : List ℕ :=
  (allDivsF F).filter (· ≤ lim)

private lemma mem_mulPows {p k pw : ℕ} {ds : List ℕ} {x : ℕ} :
    x ∈ mulPows p k pw ds ↔ ∃ j ≤ k, ∃ d ∈ ds, d * (pw * p ^ j) = x := by
  induction k generalizing pw with
  | zero =>
    simp only [mulPows, List.mem_map, Nat.le_zero, exists_eq_left, pow_zero, mul_one]
  | succ k ih =>
    simp only [mulPows, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (⟨d, hd, rfl⟩ | ⟨j, hj, d, hd, rfl⟩)
      · exact ⟨0, Nat.zero_le _, d, hd, by simp⟩
      · refine ⟨j + 1, Nat.succ_le_succ hj, d, hd, ?_⟩
        rw [pow_succ']; ring
    · rintro ⟨j, hj, d, hd, rfl⟩
      cases j with
      | zero => exact Or.inl ⟨d, hd, by simp⟩
      | succ j =>
        refine Or.inr ⟨j, Nat.le_of_succ_le_succ hj, d, hd, ?_⟩
        rw [pow_succ']; ring

private lemma allDivsF_dvd {F : List (ℕ × ℕ)} : ∀ d ∈ allDivsF F, d ∣ valF F := by
  induction F with
  | nil => intro d hd; simp [allDivsF, valF] at hd ⊢; exact hd
  | cons pa rest ih =>
    rcases pa with ⟨p, a⟩
    intro x hx
    obtain ⟨j, hj, d, hd, rfl⟩ := mem_mulPows.mp hx
    simp only [valF, one_mul]
    rw [mul_comm]
    exact Nat.mul_dvd_mul (pow_dvd_pow p hj) (ih d hd)

private lemma mulPows_nodup {p k pw : ℕ} {ds : List ℕ} (hp : p.Prime) (hpw : 0 < pw)
    (hnd : ds.Nodup) (hcop : ∀ d ∈ ds, p.Coprime d) :
    (mulPows p k pw ds).Nodup := by
  induction k generalizing pw with
  | zero =>
    simpa [mulPows] using hnd.map (fun a b h => Nat.eq_of_mul_eq_mul_right hpw h)
  | succ k ih =>
    rw [mulPows, List.nodup_append]
    refine ⟨hnd.map (fun a b h => Nat.eq_of_mul_eq_mul_right hpw h),
      ih (Nat.mul_pos hpw hp.pos), ?_⟩
    intro x hx y hy hxy
    subst hxy
    rw [List.mem_map] at hx
    obtain ⟨d1, hd1, rfl⟩ := hx
    obtain ⟨j, _, d2, hd2, heq⟩ := mem_mulPows.mp hy
    have hmul : d2 * (p * p ^ j) * pw = d1 * pw := by linarith [heq]
    have hcancel : d2 * (p * p ^ j) = d1 := Nat.eq_of_mul_eq_mul_right hpw hmul
    have hdvd : p ∣ d1 := ⟨d2 * p ^ j, by linarith [hcancel]⟩
    exact hp.not_dvd_one ((hcop d1 hd1).symm ▸ Nat.dvd_gcd hdvd (dvd_refl p))

private lemma allDivsF_nodup : ∀ {F : List (ℕ × ℕ)}, ValidFactors F → (allDivsF F).Nodup
  | [], _ => by simp [allDivsF]
  | (p, a) :: rest, ⟨hp, _, hlt, hrest⟩ => by
    rw [allDivsF]
    refine mulPows_nodup hp Nat.zero_lt_one (allDivsF_nodup hrest) (fun d hd => ?_)
    have hcop := coprime_valF_of_lt hp hrest hlt
    exact hcop.coprime_dvd_right (allDivsF_dvd d hd)

private lemma allDivsF_mem_divisors {F : List (ℕ × ℕ)} (hF : ValidFactors F) :
    ∀ d ∈ allDivsF F, d ∈ (valF F).divisors := fun d hd =>
  Nat.mem_divisors.mpr ⟨allDivsF_dvd d hd, (valF_pos hF).ne'⟩

private def checkLowDown (ivs : List (ℕ × ℕ)) (G : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 =>
    ivs.any (fun iv => iv.1 ≤ iv.2 && iv.1 ≤ k && k < iv.2 + G) && checkLowDown ivs G k

private lemma checkLowDown_sound {ivs : List (ℕ × ℕ)} {G L : ℕ}
    (h : checkLowDown ivs G L = true) :
    ∀ k : ℕ, k < L → ∃ iv ∈ ivs, iv.1 ≤ iv.2 ∧ iv.1 ≤ k ∧ k < iv.2 + G := by
  induction L with
  | zero => intro k hk; omega
  | succ L ih =>
    simp only [checkLowDown, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    intro k hk
    by_cases hkl : k = L
    · subst hkl
      obtain ⟨iv, hiv, ⟨h1, h2⟩, h3⟩ := h.1
      exact ⟨iv, hiv, h1, h2, h3⟩
    · exact ih h.2 k (by omega)

private def checkLowUp (ivs : List (ℕ × ℕ)) (G : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | t + 1 =>
    ivs.any (fun iv => iv.1 ≤ iv.2 && iv.1 < t + G && t ≤ iv.2) && checkLowUp ivs G t

private lemma checkLowUp_sound {ivs : List (ℕ × ℕ)} {G L : ℕ}
    (h : checkLowUp ivs G L = true) :
    ∀ t : ℕ, 1 ≤ t → t < L → ∃ iv ∈ ivs, iv.1 ≤ iv.2 ∧ iv.1 < t + G ∧ t ≤ iv.2 := by
  induction L with
  | zero => intro t _ ht; omega
  | succ L ih =>
    cases L with
    | zero => intro t ht1 ht2; omega
    | succ L' =>
      simp only [checkLowUp, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
      intro t ht1 ht2
      by_cases htl : t = L' + 1
      · subst htl
        obtain ⟨iv, hiv, ⟨h1, h2⟩, h3⟩ := h.1
        exact ⟨iv, hiv, h1, h2, h3⟩
      · exact ih h.2 t ht1 (by omega)

private def insertNat (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertNat x ys

private def sortNat : List ℕ → List ℕ
  | [] => []
  | x :: xs => insertNat x (sortNat xs)

private lemma insertNat_perm (x : ℕ) : ∀ (l : List ℕ), (insertNat x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertNat
    split_ifs
    · exact List.Perm.refl _
    · exact ((insertNat_perm x ys).cons y).trans (List.Perm.swap x y ys)

private lemma sortNat_perm : ∀ (l : List ℕ), (sortNat l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertNat_perm x (sortNat xs)).trans ((sortNat_perm xs).cons x)

private def checkPreDirect (F : List (ℕ × ℕ)) (L G : ℕ) : Bool :=
  let n := valF F
  let s := sigF F
  if n ≤ 1 || L < 1 || G < 1 || s < n then false
  else
    let P := s - n
    if P < 2 * L then false
    else
      let ds := sortNat ((allDivsF F).filter (· < n))
      let ivs := intervalSums ds
      ivs.any (fun iv => iv.1 ≤ L && P - L ≤ iv.2) &&
      checkLowDown ivs G L &&
      checkLowUp ivs G L

private lemma checkPreDirect_sound {F : List (ℕ × ℕ)} {L G : ℕ}
    (hF : ValidFactors F) (h : checkPreDirect F L G = true) :
    PreCertifiedBase (valF F) L G := by
  unfold checkPreDirect at h
  dsimp only at h
  split_ifs at h with h1 h2
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le, not_lt] at h1 h2
  obtain ⟨⟨⟨hn1, hL1⟩, hG1⟩, hsn⟩ := h1
  simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ivM, hivM, hML, hMR⟩, hDown⟩, hUp⟩ := h
  set n := valF F
  set P : ℕ := sigF F - n
  have hPeq : ProperSum n = (P : ℤ) := by
    rw [properSum_valF hF]; dsimp [P, n]; omega
  let ds := sortNat ((allDivsF F).filter (· < n))
  have hperm : ds.Perm ((allDivsF F).filter (· < n)) := sortNat_perm _
  have hds_nodup : ds.Nodup := hperm.nodup_iff.mpr ((allDivsF_nodup hF).filter _)
  have hds_sub : ∀ d ∈ ds, d ∈ n.properDivisors := by
    intro d hd
    have hd' := hperm.mem_iff.mp hd
    simp only [List.mem_filter, decide_eq_true_eq] at hd'
    exact Nat.mem_properDivisors.mpr ⟨allDivsF_dvd d hd'.1, hd'.2⟩
  have hrep : ∀ x : ℕ, InIntervals (intervalSums ds) x → Represented n (x : ℤ) := by
    intro x hx
    exact listSubSum_sound_finset hds_nodup hds_sub (intervalSums_sound ds x hx)
  refine ⟨hn1, hL1, hG1, ?_, ?_, ?_⟩
  · intro y hy1 hy2
    have hy0 : 0 ≤ y := by omega
    have hynat : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
    rw [← hynat]
    apply hrep y.toNat
    refine ⟨ivM, hivM, ?_, ?_⟩ <;> omega
  · intro k hk0 hkL
    have hknat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    obtain ⟨iv, hiv, hle, h1', h2'⟩ := checkLowDown_sound hDown k.toNat (by omega)
    let j := min k.toNat iv.2
    have hj1 : iv.1 ≤ j := by dsimp [j]; omega
    have hj2 : j ≤ iv.2 := Nat.min_le_right _ _
    have hj3 : j ≤ k.toNat := Nat.min_le_left _ _
    have hj4 : k.toNat < j + G := by dsimp [j]; omega
    refine ⟨(j : ℤ), hrep j ⟨iv, hiv, hj1, hj2⟩, by omega, by omega⟩
  · intro t ht1 htL
    have htnat : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by omega)
    obtain ⟨iv, hiv, hle, h1', h2'⟩ := checkLowUp_sound hUp t.toNat (by omega) (by omega)
    let j := max t.toNat iv.1
    have hj1 : iv.1 ≤ j := Nat.le_max_right _ _
    have hj2 : j ≤ iv.2 := by dsimp [j]; omega
    have hj3 : t.toNat ≤ j := Nat.le_max_left _ _
    have hj4 : j < t.toNat + G := by dsimp [j]; omega
    refine ⟨(j : ℤ), hrep j ⟨iv, hiv, hj1, hj2⟩, by omega, by omega⟩

private def removeIdx : List (ℕ × ℕ) → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | _ :: rest, 0 => rest
  | x :: rest, i + 1 => x :: removeIdx rest i

private def setExp : List (ℕ × ℕ) → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | (p, _) :: rest, 0, a => (p, a) :: rest
  | x :: rest, i + 1, a => x :: setExp rest i a

private lemma validFactors_removeIdx : ∀ {F : List (ℕ × ℕ)} (i : ℕ),
    ValidFactors F → ValidFactors (removeIdx F i)
  | [], _, _ => trivial
  | _ :: _, 0, ⟨_, _, _, hrest⟩ => hrest
  | (p, a) :: rest, i + 1, ⟨hp, ha, hlt, hrest⟩ => by
    refine ⟨hp, ha, fun q hq => ?_, validFactors_removeIdx i hrest⟩
    have hmem : ∀ {L : List (ℕ × ℕ)} {k : ℕ} {x : ℕ × ℕ}, x ∈ removeIdx L k → x ∈ L := by
      intro L k x hx
      induction L generalizing k with
      | nil => simp [removeIdx] at hx
      | cons y ys ih =>
        cases k with
        | zero => exact List.mem_cons_of_mem _ hx
        | succ k =>
          simp only [removeIdx, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih hx)
    exact hlt q (hmem hq)

private lemma validFactors_setExp : ∀ {F : List (ℕ × ℕ)} {i a : ℕ},
    1 ≤ a → ValidFactors F → ValidFactors (setExp F i a)
  | [], _, _, _, _ => trivial
  | (p, _) :: _, 0, a, ha, ⟨hp, _, hlt, hrest⟩ => ⟨hp, ha, hlt, hrest⟩
  | (p, b) :: rest, i + 1, a, ha, ⟨hp, hb, hlt, hrest⟩ => by
    refine ⟨hp, hb, fun q hq => ?_, validFactors_setExp ha hrest⟩
    have hfst : ∀ {L : List (ℕ × ℕ)} {k : ℕ} {x : ℕ × ℕ},
        x ∈ setExp L k a → ∃ y ∈ L, y.1 = x.1 := by
      intro L k x hx
      induction L generalizing k with
      | nil => simp [setExp] at hx
      | cons y ys ih =>
        cases k with
        | zero =>
          rcases y with ⟨p', b'⟩
          simp only [setExp, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨(p', b'), List.mem_cons_self, rfl⟩
          · exact ⟨x, List.mem_cons_of_mem _ hx, rfl⟩
        | succ k =>
          simp only [setExp, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨y, List.mem_cons_self, rfl⟩
          · obtain ⟨z, hz, hze⟩ := ih hx
            exact ⟨z, List.mem_cons_of_mem _ hz, hze⟩
    obtain ⟨y, hy, hye⟩ := hfst hq
    rw [← hye]
    exact hlt y hy

private lemma valF_removeIdx {F : List (ℕ × ℕ)} {i : ℕ} {p a : ℕ}
    (hF : ValidFactors F) (hget : F[i]? = some (p, a)) :
    valF F = valF (removeIdx F i) * p ^ a ∧ (valF (removeIdx F i)).Coprime p ∧ p.Prime ∧ 1 ≤ a := by
  induction F generalizing i with
  | nil => simp at hget
  | cons qb rest ih =>
    rcases qb with ⟨q, b⟩
    rcases hF with ⟨hq, hb, hlt, hrest⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hget
      obtain ⟨rfl, rfl⟩ := hget
      refine ⟨by simp [valF, removeIdx, mul_comm], (coprime_valF_of_lt hq hrest hlt).symm, hq, hb⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      obtain ⟨heq, hcop, hp, ha⟩ := ih hrest hget
      have hqp : q < p := by
        have hmem : (p, a) ∈ rest := List.mem_of_getElem? hget
        exact hlt (p, a) hmem
      have hqcop : (q ^ b).Coprime p := ((Nat.coprime_primes hq hp).mpr (ne_of_lt hqp)).pow_left b
      refine ⟨by simp only [valF, removeIdx]; rw [heq]; ring,
        by simp only [valF, removeIdx]; exact hqcop.mul_left hcop, hp, ha⟩

private lemma valF_setExp_pred {F : List (ℕ × ℕ)} {i p a : ℕ}
    (hget : F[i]? = some (p, a + 1)) :
    valF F = valF (setExp F i a) * p := by
  induction F generalizing i with
  | nil => simp at hget
  | cons qb rest ih =>
    rcases qb with ⟨q, b⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hget
      obtain ⟨rfl, rfl⟩ := hget
      simp only [valF, setExp, pow_succ]; ring
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [valF, setExp]
      rw [ih hget]; ring

private lemma valF_setExp_add {F : List (ℕ × ℕ)} {i p a0 a : ℕ}
    (hget : F[i]? = some (p, a0)) (hle : a0 ≤ a) :
    valF (setExp F i a) = valF F * p ^ (a - a0) := by
  induction F generalizing i with
  | nil => simp at hget
  | cons qb rest ih =>
    rcases qb with ⟨q, b⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hget
      obtain ⟨rfl, rfl⟩ := hget
      simp only [valF, setExp]
      have hpow : q ^ a = q ^ b * q ^ (a - b) := by rw [← pow_add, Nat.add_sub_cancel' hle]
      rw [hpow]; ring
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [valF, setExp]
      rw [ih hget]; ring

private def noDivUpTo (n : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | k + 1 => decide (n % (k + 1) ≠ 0) && noDivUpTo n k

private lemma noDivUpTo_sound {n : ℕ} : ∀ {k : ℕ}, noDivUpTo n k = true →
    ∀ d, 2 ≤ d → d ≤ k → ¬ d ∣ n
  | 0, _, _, h2, hk => by omega
  | 1, _, _, h2, hk => by omega
  | k + 1, h, d, h2, hk => by
    cases k with
    | zero => omega
    | succ k' =>
      simp only [noDivUpTo, Bool.and_eq_true, decide_eq_true_eq] at h
      by_cases hdk : d = k' + 2
      · subst hdk; exact fun hdvd => h.1 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact noDivUpTo_sound h.2 d h2 (by omega)

private def isPrimeFast (p : ℕ) : Bool :=
  decide (2 ≤ p) && noDivUpTo p (p - 1)

private lemma prime_of_isPrimeFast {p : ℕ} (h : isPrimeFast p = true) : p.Prime := by
  simp only [isPrimeFast, Bool.and_eq_true, decide_eq_true_eq] at h
  refine Nat.prime_def_lt'.mpr ⟨h.1, fun m hm2 hmp => noDivUpTo_sound h.2 m hm2 (by omega)⟩

private def validFactorsBool : List (ℕ × ℕ) → Bool
  | [] => true
  | (p, a) :: rest =>
    isPrimeFast p && decide (1 ≤ a) && rest.all (fun q => decide (p < q.1)) && validFactorsBool rest

private lemma validFactors_of_bool : ∀ {F : List (ℕ × ℕ)}, validFactorsBool F = true → ValidFactors F
  | [], _ => trivial
  | (p, a) :: rest, h => by
    simp only [validFactorsBool, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact ⟨prime_of_isPrimeFast h.1.1.1, h.1.1.2, h.1.2, validFactors_of_bool h.2⟩

private def insertDedup (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x == y then y :: ys
    else y :: insertDedup x ys

private lemma mem_insertDedup {x z : ℕ} {l : List ℕ} (h : z ∈ insertDedup x l) :
    z = x ∨ z ∈ l := by
  induction l with
  | nil => simp [insertDedup] at h; exact Or.inl h
  | cons y ys ih =>
    unfold insertDedup at h
    split_ifs at h with h1 h2
    · simp only [List.mem_cons] at h
      rcases h with rfl | h; exact Or.inl rfl; exact Or.inr (List.mem_cons.mpr h)
    · exact Or.inr h
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases ih h with rfl | hy; exact Or.inl rfl; exact Or.inr (List.mem_cons_of_mem _ hy)

private def mergeDedup (xs ys : List ℕ) : List ℕ :=
  xs.foldl (fun acc x => insertDedup x acc) ys

private lemma mem_mergeDedup {xs ys : List ℕ} {z : ℕ} (h : z ∈ mergeDedup xs ys) :
    z ∈ xs ∨ z ∈ ys := by
  unfold mergeDedup at h
  induction xs generalizing ys with
  | nil => exact Or.inr h
  | cons x rest ih =>
    simp only [List.foldl_cons] at h
    rcases ih h with hr | hi
    · exact Or.inl (List.mem_cons_of_mem _ hr)
    · rcases mem_insertDedup hi with rfl | hy
      · exact Or.inl List.mem_cons_self
      · exact Or.inr hy

private def addDivLe (M : ℕ) (acc : List ℕ) (d : ℕ) : List ℕ :=
  mergeDedup ((acc.map (· + d)).filter (· ≤ M)) acc

private def subSumsLe (M : ℕ) (ds : List ℕ) : List ℕ :=
  ds.foldl (addDivLe M) [0]

private lemma subSumsLe_sound (M : ℕ) (ds : List ℕ) :
    ∀ x ∈ subSumsLe M ds, ListSubSum ds x := by
  have hfold : ∀ (acc : List ℕ) (pre : List ℕ),
      (∀ y ∈ acc, ListSubSum pre y) →
      ∀ (rem : List ℕ) (x : ℕ), x ∈ rem.foldl (addDivLe M) acc → ListSubSum (pre ++ rem) x := by
    intro acc pre hpre rem
    induction rem generalizing acc pre with
    | nil => intro x hx; simpa using hpre x hx
    | cons d rest ih =>
      intro x hx
      simp only [List.foldl_cons] at hx
      have hstep : ∀ y ∈ addDivLe M acc d, ListSubSum (pre ++ [d]) y := by
        intro y hy
        rcases mem_mergeDedup hy with hshift | hold
        · simp only [List.mem_filter, List.mem_map] at hshift
          obtain ⟨⟨u, hu, rfl⟩, _⟩ := hshift
          obtain ⟨sub, hsub, hsum⟩ := hpre u hu
          refine ⟨sub ++ [d], hsub.append (List.Sublist.refl [d]), ?_⟩
          simp [hsum]
        · obtain ⟨sub, hsub, hsum⟩ := hpre y hold
          exact ⟨sub, by simpa using hsub.append (List.nil_sublist [d]), hsum⟩
      have hres := ih (addDivLe M acc d) (pre ++ [d]) hstep x hx
      simpa [List.append_assoc] using hres
  intro x hx
  have h0 : ∀ y ∈ ([0] : List ℕ), ListSubSum [] y := by
    intro y hy; simp only [List.mem_singleton] at hy; subst hy
    exact ⟨[], List.Sublist.refl [], by simp⟩
  simpa using hfold [0] [] h0 ds x hx

private def checkResSeed (F : List (ℕ × ℕ)) (p M : ℕ) : Bool :=
  let sums := subSumsLe M (smallDivsF M F)
  (List.range p).all fun r => sums.any fun y => y % p == r && y ≤ M

private lemma checkResSeed_sound {F : List (ℕ × ℕ)} {p M : ℕ}
    (hF : ValidFactors F) (h : checkResSeed F p M = true) :
    ∀ r : ℕ, r < p → ∃ y : ℕ, y % p = r ∧ y ≤ M ∧ DivRepresented (valF F) (y : ℤ) := by
  unfold checkResSeed at h
  dsimp only at h
  simp only [List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at h
  intro r hr
  obtain ⟨y, hy_mem, hy_mod, hy_le⟩ := h r hr
  have hnd : (smallDivsF M F).Nodup := (allDivsF_nodup hF).filter _
  have hsub : ∀ d ∈ smallDivsF M F, d ∈ (valF F).divisors := by
    intro d hd
    simp only [smallDivsF, List.mem_filter] at hd
    exact allDivsF_mem_divisors hF d hd.1
  exact ⟨y, hy_mod, hy_le, listSubSum_sound_finset hnd hsub (subSumsLe_sound M _ y hy_mem)⟩

/-- 37 small pre-verified complete-residue-system seeds `(F0, p, M)`. -/
private def resSeeds : List (List (ℕ × ℕ) × ℕ × ℕ) :=
  [ ([(3, 1), (5, 1)], 7, 9),
    ([(3, 1), (5, 1)], 11, 24),
    ([(3, 2), (5, 1)], 13, 24),
    ([(3, 2), (5, 1)], 17, 28),
    ([(3, 2), (5, 1)], 19, 45),
    ([(3, 2), (5, 1)], 23, 57),
    ([(3, 2), (5, 1)], 29, 69),
    ([(3, 2), (5, 1)], 31, 73),
    ([(3, 1), (5, 2)], 13, 25),
    ([(3, 1), (5, 2)], 17, 44),
    ([(3, 1), (5, 2)], 19, 108),
    ([(3, 2), (5, 2)], 37, 73),
    ([(3, 2), (5, 2)], 41, 77),
    ([(3, 3), (5, 1)], 37, 145),
    ([(3, 1), (7, 1)], 13, 32),
    ([(3, 2), (7, 1)], 11, 17),
    ([(3, 2), (7, 1)], 17, 40),
    ([(3, 2), (7, 1)], 19, 37),
    ([(3, 2), (7, 1)], 23, 41),
    ([(3, 1), (11, 1)], 7, 37),
    ([(3, 1), (11, 1)], 13, 48),
    ([(3, 2), (11, 1)], 17, 56),
    ([(3, 2), (11, 1)], 29, 147),
    ([(3, 2), (11, 1)], 31, 152),
    ([(3, 1), (13, 1)], 7, 40),
    ([(3, 1), (13, 1)], 11, 52),
    ([(3, 2), (13, 1)], 29, 182),
    ([(3, 2), (17, 1)], 7, 13),
    ([(3, 2), (19, 1)], 7, 13),
    ([(3, 2), (19, 1)], 37, 256),
    ([(3, 1), (5, 1), (7, 1)], 17, 31),
    ([(3, 1), (5, 1), (7, 1)], 19, 36),
    ([(3, 1), (5, 1), (7, 1)], 23, 40),
    ([(3, 1), (5, 1), (7, 1)], 29, 46),
    ([(3, 1), (5, 1), (7, 1)], 31, 48),
    ([(3, 1), (5, 1), (7, 1)], 37, 54),
    ([(3, 1), (5, 1), (7, 1)], 41, 58) ]

set_option maxHeartbeats 2000000 in
private lemma resSeeds_valid :
    resSeeds.all (fun s => validFactorsBool s.1 && checkResSeed s.1 s.2.1 s.2.2) = true := rfl

/-- 54 small pre-verified `PreCertifiedBase` seeds `(F0, L0, G0)`. -/
private def preSeeds : List (List (ℕ × ℕ) × ℕ × ℕ) :=
  [ ([(3, 2), (5, 1), (7, 1)], 3, 2),
    ([(3, 2), (5, 1), (7, 1), (157, 1)], 3, 2),
    ([(3, 2), (5, 1), (7, 1), (163, 1)], 3, 2),
    ([(3, 2), (5, 1), (7, 1), (167, 1)], 3, 2),
    ([(3, 2), (5, 1), (7, 1), (173, 1)], 3, 2),
    ([(3, 2), (5, 1), (7, 1), (179, 1)], 3, 2),
    ([(3, 2), (5, 1), (7, 1), (181, 1)], 3, 2),
    ([(3, 2), (5, 1), (7, 1), (191, 1)], 3, 2),
    ([(3, 2), (5, 1), (7, 1), (193, 1)], 3, 2),
    ([(3, 2), (5, 1), (7, 1), (197, 1)], 3, 2),
    ([(3, 2), (5, 1), (7, 1), (199, 1)], 3, 2),
    ([(3, 3), (5, 1), (13, 1)], 12, 2),
    ([(3, 3), (5, 1), (17, 1)], 12, 2),
    ([(3, 2), (5, 2), (13, 1)], 12, 2),
    ([(3, 2), (5, 2), (17, 1)], 12, 2),
    ([(3, 2), (5, 2), (19, 1)], 12, 2),
    ([(3, 1), (5, 2), (7, 1)], 18, 2),
    ([(3, 1), (5, 3), (7, 1)], 18, 2),
    ([(3, 1), (5, 1), (7, 1)], 18, 2),
    ([(3, 1), (5, 1), (7, 1), (29, 1)], 18, 2),
    ([(3, 1), (5, 1), (7, 1), (31, 1)], 18, 2),
    ([(3, 1), (5, 1), (7, 1), (41, 1)], 18, 2),
    ([(3, 1), (5, 1), (7, 1), (43, 1)], 18, 2),
    ([(3, 1), (5, 1), (7, 1), (47, 1)], 18, 2),
    ([(3, 3), (7, 1), (13, 1)], 19, 3),
    ([(3, 3), (5, 2)], 23, 2),
    ([(3, 3), (5, 3)], 23, 2),
    ([(3, 2), (5, 1), (11, 1)], 23, 2),
    ([(3, 3), (5, 1), (11, 1)], 23, 2),
    ([(3, 4), (5, 1), (11, 1)], 23, 2),
    ([(3, 5), (5, 1), (11, 1)], 23, 2),
    ([(3, 6), (5, 1), (11, 1)], 23, 2),
    ([(3, 7), (5, 1), (11, 1)], 23, 2),
    ([(3, 2), (5, 2), (23, 1)], 23, 2),
    ([(3, 1), (5, 2), (11, 1)], 23, 2),
    ([(3, 3), (7, 2), (17, 1)], 24, 3),
    ([(3, 4), (7, 1), (17, 1)], 24, 3),
    ([(3, 2), (7, 2), (11, 1)], 27, 3),
    ([(3, 3), (7, 1), (11, 1)], 27, 3),
    ([(3, 4), (7, 1), (11, 1)], 27, 3),
    ([(3, 3), (5, 1), (23, 1)], 35, 2),
    ([(3, 2), (5, 1), (13, 1)], 36, 2),
    ([(3, 3), (11, 1), (13, 1), (17, 1)], 36, 5),
    ([(3, 2), (5, 2), (29, 1)], 37, 2),
    ([(3, 2), (5, 2), (37, 1)], 37, 2),
    ([(3, 2), (5, 2), (41, 1)], 37, 2),
    ([(3, 3), (7, 2), (19, 1)], 46, 3),
    ([(3, 1), (5, 1), (11, 1)], 47, 2),
    ([(3, 1), (5, 3), (13, 1)], 52, 4),
    ([(3, 1), (5, 2), (13, 2)], 52, 4),
    ([(3, 2), (5, 1), (19, 1)], 57, 2),
    ([(3, 2), (7, 1), (11, 1)], 60, 3),
    ([(3, 2), (5, 2), (31, 1)], 68, 2),
    ([(3, 2), (7, 1), (13, 1)], 79, 3) ]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
private lemma preSeeds_valid :
    preSeeds.all (fun s => validFactorsBool s.1 && checkPreDirect s.1 s.2.1 s.2.2) = true := rfl

private def lookupExp : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (q, a) :: rest, p => if q == p then a else lookupExp rest p

private lemma lookupExp_pow_dvd : ∀ (F : List (ℕ × ℕ)) (p : ℕ), p ^ lookupExp F p ∣ valF F
  | [], _ => by simp [lookupExp, valF]
  | (q, a) :: rest, p => by
    unfold lookupExp valF
    split_ifs with hqp
    · have heq : q = p := by simpa using hqp
      subst heq; exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (lookupExp_pow_dvd rest p) _

private lemma not_mem_of_lookupExp_zero {F : List (ℕ × ℕ)} {p : ℕ}
    (hF : ValidFactors F) (h0 : lookupExp F p = 0) : ∀ pa ∈ F, pa.1 ≠ p := by
  induction F with
  | nil => intro _ hx; simp at hx
  | cons qb rest ih =>
    rcases qb with ⟨q, b⟩
    rcases hF with ⟨_, hb, _, hrest⟩
    unfold lookupExp at h0
    split_ifs at h0 with hqp
    · omega
    · intro pa hpa
      simp only [List.mem_cons] at hpa
      rcases hpa with rfl | hpa
      · simpa using hqp
      · exact ih hrest h0 pa hpa

private def fDvd (F0 F : List (ℕ × ℕ)) : Bool :=
  F0.all fun pa => decide (pa.2 ≤ lookupExp F pa.1)

private lemma valF_dvd_of_fDvd {F0 F : List (ℕ × ℕ)}
    (hF0 : ValidFactors F0) (h : fDvd F0 F = true) : valF F0 ∣ valF F := by
  induction F0 with
  | nil => simp [valF]
  | cons pa rest ih =>
    rcases pa with ⟨p, a⟩
    rcases hF0 with ⟨hp, _, hlt, hrest⟩
    simp only [fDvd, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have h1 : p ^ a ∣ valF F := (pow_dvd_pow p h.1).trans (lookupExp_pow_dvd F p)
    have h2 : valF rest ∣ valF F := ih hrest h.2
    have hcop : (p ^ a).Coprime (valF rest) := (coprime_valF_of_lt hp hrest hlt).pow_left a
    simpa [valF] using hcop.mul_dvd_of_dvd_of_dvd h1 h2

private def insertPair (pa : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [pa]
  | qb :: rest => if pa.1 < qb.1 then pa :: qb :: rest else qb :: insertPair pa rest

private lemma mem_insertPair {pa x : ℕ × ℕ} {F : List (ℕ × ℕ)} :
    x ∈ insertPair pa F ↔ x = pa ∨ x ∈ F := by
  induction F with
  | nil => simp [insertPair]
  | cons qb rest ih =>
    unfold insertPair
    split_ifs
    · simp [List.mem_cons]
    · simp only [List.mem_cons, ih]; tauto

private lemma validFactors_insertPair {F : List (ℕ × ℕ)} {p a : ℕ}
    (hF : ValidFactors F) (hp : p.Prime) (ha : 1 ≤ a) (hne : ∀ qb ∈ F, qb.1 ≠ p) :
    ValidFactors (insertPair (p, a) F) := by
  induction F with
  | nil => exact ⟨hp, ha, fun _ hx => by simp at hx, trivial⟩
  | cons qb rest ih =>
    rcases qb with ⟨q, b⟩
    rcases hF with ⟨hq, hb, hlt, hrest⟩
    unfold insertPair
    split_ifs with hpq
    · refine ⟨hp, ha, fun x hx => ?_, ⟨hq, hb, hlt, hrest⟩⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hpq
      · exact lt_trans hpq (hlt x hx)
    · have hqp : q < p := by
        have h1 : q ≠ p := hne (q, b) List.mem_cons_self
        omega
      refine ⟨hq, hb, fun x hx => ?_, ih hrest (fun y hy => hne y (List.mem_cons_of_mem _ hy))⟩
      rcases mem_insertPair.mp hx with rfl | hx
      · exact hqp
      · exact hlt x hx

private lemma valF_insertPair (p a : ℕ) : ∀ (F : List (ℕ × ℕ)),
    valF (insertPair (p, a) F) = valF F * p ^ a
  | [] => by simp [insertPair, valF]
  | (q, b) :: rest => by
    unfold insertPair
    split_ifs
    · simp only [valF]; ring
    · simp only [valF, valF_insertPair p a rest]; ring

private lemma coprime_valF_of_ne {F : List (ℕ × ℕ)} {p : ℕ}
    (hF : ValidFactors F) (hp : p.Prime) (hne : ∀ qb ∈ F, qb.1 ≠ p) :
    (valF F).Coprime p := by
  induction F with
  | nil => simp [valF]
  | cons qb rest ih =>
    rcases qb with ⟨q, b⟩
    rcases hF with ⟨hq, _, _, hrest⟩
    have hqp : q ≠ p := hne (q, b) List.mem_cons_self
    have h1 : (q ^ b).Coprime p := ((Nat.coprime_primes hq hp).mpr hqp).pow_left b
    have h2 : (valF rest).Coprime p := ih hrest (fun x hx => hne x (List.mem_cons_of_mem _ hx))
    simpa [valF] using h1.mul_left h2

private lemma divRepresented_single {c d : ℕ} (hc : 0 < c) (hd : d ∣ c) :
    DivRepresented c (d : ℤ) :=
  ⟨{d}, by intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; exact Nat.mem_divisors.mpr ⟨hd, hc.ne'⟩,
    by simp⟩

private lemma divRepresented_pair {c d1 d2 : ℕ} (hc : 0 < c) (h1 : d1 ∣ c) (h2 : d2 ∣ c) (hne : d1 ≠ d2) :
    DivRepresented c ((d1 + d2 : ℕ) : ℤ) :=
  ⟨{d1, d2}, by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨h1, hc.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨h2, hc.ne'⟩,
    by rw [Finset.sum_pair hne]; push_cast; ring⟩

private lemma divRepresented_triple {c d1 d2 d3 : ℕ} (hc : 0 < c)
    (h1 : d1 ∣ c) (h2 : d2 ∣ c) (h3 : d3 ∣ c) (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3) :
    DivRepresented c ((d1 + d2 + d3 : ℕ) : ℤ) :=
  ⟨{d1, d2, d3}, by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨h1, hc.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨h2, hc.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨h3, hc.ne'⟩,
    by
      have h1_not : d1 ∉ ({d2, d3} : Finset ℕ) := by simp [h12, h13]
      rw [Finset.sum_insert h1_not, Finset.sum_pair h23]; push_cast; ring⟩

private lemma divRepresented_zero (c : ℕ) : DivRepresented c ((0 : ℕ) : ℤ) :=
  ⟨∅, by simp, by simp⟩

private def o1RaiseOkBase (Fc : List (ℕ × ℕ)) (Pb p L : ℕ) : Bool :=
  let c := valF Fc
  let sc := sigF Fc
  if sc < c then false
  else
    let Pc := sc - c
    if (p + 1) * L > p * Pc + 1 then false
    else if Pb + 1 < (p + 1) * L then false
    else
      let hiLim := Pb + 1 - (p + 1) * L
      let rule3 :=
        match p, Fc with
        | 3, (q, _) :: _ => decide (q + 1 ≤ hiLim)
        | _, _ => false
      if rule3 then true
      else
        let rule5 :=
          match p, Fc with
          | 5, (3, e) :: rest =>
            (decide (2 ≤ e) && decide (12 ≤ hiLim)) ||
            match rest with
            | (q, _) :: _ => decide (q + 4 ≤ hiLim)
            | [] => false
          | _, _ => false
        if rule5 then true
        else resSeeds.any fun s => s.2.1 == p && decide (s.2.2 ≤ hiLim) && fDvd s.1 Fc

private lemma o1RaiseOkBase_sound {Fc : List (ℕ × ℕ)} {b Pb p a L : ℕ}
    (hFc : ValidFactors Fc) (hp : p.Prime) (hcop : (valF Fc).Coprime p)
    (hb : b = valF Fc * p ^ a) (ha : 1 ≤ a) (hPb : ProperSum b = (Pb : ℤ))
    (h : o1RaiseOkBase Fc Pb p L = true) :
    RaiseOk b p L := by
  unfold o1RaiseOkBase at h
  dsimp only at h
  split_ifs at h with hsc hsm hhi hr3 hr5
  · -- Rule 1: p = 3
    cases p with
    | zero => simp at hr3
    | succ p' =>
      cases p' with
      | zero => simp at hr3
      | succ p'' =>
        cases p'' with
        | zero => simp at hr3
        | succ p''' =>
          cases p''' with
          | succ _ => simp at hr3
          | zero =>
            cases Fc with
            | nil => simp at hr3
            | cons qe rest =>
              rcases qe with ⟨q, e⟩
              simp only [decide_eq_true_eq] at hr3
              have hFc_saved := hFc
              rcases hFc with ⟨hq, he, _, hrest⟩
              have hcpos : 0 < valF ((q, e) :: rest) := valF_pos hFc_saved
              have hq_dvd : q ∣ valF ((q, e) :: rest) := by
                simp only [valF]
                exact dvd_mul_of_dvd_left (dvd_pow_self q (by omega : e ≠ 0)) _
              have hq_ne3 : q ≠ 3 := by
                intro heq; subst heq
                have h3 : 3 ∣ Nat.gcd (valF ((3, e) :: rest)) 3 := Nat.dvd_gcd hq_dvd (dvd_refl 3)
                rw [hcop.gcd_eq_one] at h3
                omega
              have hPc : ProperSum (valF ((q, e) :: rest)) =
                  ((sigF ((q, e) :: rest) - valF ((q, e) :: rest) : ℕ) : ℤ) := by
                rw [properSum_valF hFc_saved]; omega
              refine ⟨valF ((q, e) :: rest), a, q + 1, hb, ha, hcop, hcpos, ?_, ?_, ?_⟩
              · rw [hPc]; exact_mod_cast (show (3 + 1) * L ≤ 3 * (sigF ((q, e) :: rest) - valF ((q, e) :: rest)) + 1 by omega)
              · rw [hPb]; omega
              · intro r hr
                have hq_mod : q % 3 = 1 ∨ q % 3 = 2 := by
                  have h0 : q % 3 ≠ 0 := fun hz => by
                    have h3q : 3 ∣ q := Nat.dvd_of_mod_eq_zero hz
                    rcases hq.eq_one_or_self_of_dvd 3 h3q with h1 | h3
                    · omega
                    · exact hq_ne3 h3.symm
                  omega
                interval_cases r
                · exact ⟨0, by simp, by omega, divRepresented_zero _⟩
                · exact ⟨1, by simp, by omega, divRepresented_single hcpos (one_dvd _)⟩
                · rcases hq_mod with hm1 | hm2
                  · exact ⟨1 + q, by omega, by omega,
                      divRepresented_pair hcpos (one_dvd _) hq_dvd (by have := hq.two_le; omega)⟩
                  · exact ⟨q, hm2, by omega, divRepresented_single hcpos hq_dvd⟩
  · -- Rule 2: p = 5
    have hp5 : p = 5 := by
      cases p with
      | zero => simp at hr5
      | succ p1 => cases p1 with
        | zero => simp at hr5
        | succ p2 => cases p2 with
          | zero => simp at hr5
          | succ p3 => cases p3 with
            | zero => simp at hr5
            | succ p4 => cases p4 with
              | zero => simp at hr5
              | succ p5 => cases p5 with
                | zero => rfl
                | succ _ => simp at hr5
    subst hp5
    cases Fc with
    | nil => simp at hr5
    | cons pe rest =>
      rcases pe with ⟨q0, e⟩
      have hq0 : q0 = 3 := by
        cases q0 with
        | zero => simp at hr5
        | succ q1 => cases q1 with
          | zero => simp at hr5
          | succ q2 => cases q2 with
            | zero => simp at hr5
            | succ q3 => cases q3 with
              | zero => rfl
              | succ _ => simp at hr5
      subst hq0
      have hcpos : 0 < valF ((3, e) :: rest) := valF_pos hFc
      have hFc_saved := hFc
      rcases hFc with ⟨_, he, h3lt, hrest⟩
      have hPc : ProperSum (valF ((3, e) :: rest)) =
          ((sigF ((3, e) :: rest) - valF ((3, e) :: rest) : ℕ) : ℤ) := by
        rw [properSum_valF hFc_saved]; omega
      have h3_dvd : 3 ∣ valF ((3, e) :: rest) := by
        simp only [valF]; exact dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega : e ≠ 0)) _
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr5
      rcases hr5 with ⟨he2, h12⟩ | hr5b
      · have h9_dvd : 9 ∣ valF ((3, e) :: rest) := by
          simp only [valF]
          have : 3 ^ 2 ∣ 3 ^ e := pow_dvd_pow 3 he2
          exact dvd_mul_of_dvd_left (by simpa using this) _
        refine ⟨valF ((3, e) :: rest), a, 12, hb, ha, hcop, hcpos, ?_, ?_, ?_⟩
        · rw [hPc]; exact_mod_cast (show (5 + 1) * L ≤ 5 * (sigF ((3, e) :: rest) - valF ((3, e) :: rest)) + 1 by omega)
        · rw [hPb]; omega
        · intro r hr
          interval_cases r
          · exact ⟨0, by simp, by omega, divRepresented_zero _⟩
          · exact ⟨1, by simp, by omega, divRepresented_single hcpos (one_dvd _)⟩
          · exact ⟨3 + 9, by simp, by omega, divRepresented_pair hcpos h3_dvd h9_dvd (by omega)⟩
          · exact ⟨3, by simp, by omega, divRepresented_single hcpos h3_dvd⟩
          · exact ⟨1 + 3, by simp, by omega, divRepresented_pair hcpos (one_dvd _) h3_dvd (by omega)⟩
      · cases rest with
        | nil => simp at hr5b
        | cons qe2 rest2 =>
          rcases qe2 with ⟨q, e2⟩
          simp only [decide_eq_true_eq] at hr5b
          rcases hrest with ⟨hq, he2, _, _⟩
          have h3q : 3 < q := h3lt (q, e2) List.mem_cons_self
          have hq_dvd : q ∣ valF ((3, e) :: (q, e2) :: rest2) := by
            simp only [valF]
            exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_pow_self q (by omega : e2 ≠ 0)) _) _
          have hq_ne5 : q ≠ 5 := by
            intro heq; subst heq
            have h5 : 5 ∣ Nat.gcd (valF ((3, e) :: (5, e2) :: rest2)) 5 := Nat.dvd_gcd hq_dvd (dvd_refl 5)
            rw [hcop.gcd_eq_one] at h5
            omega
          have hq_mod : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by
            have h0 : q % 5 ≠ 0 := fun hz => by
              have h5q : 5 ∣ q := Nat.dvd_of_mod_eq_zero hz
              rcases hq.eq_one_or_self_of_dvd 5 h5q with h1 | h5
              · omega
              · exact hq_ne5 h5.symm
            omega
          refine ⟨valF ((3, e) :: (q, e2) :: rest2), a, q + 4, hb, ha, hcop, hcpos, ?_, ?_, ?_⟩
          · rw [hPc]; exact_mod_cast (show (5 + 1) * L ≤ 5 * (sigF ((3, e) :: (q, e2) :: rest2) - valF ((3, e) :: (q, e2) :: rest2)) + 1 by omega)
          · rw [hPb]; omega
          · intro r hr
            interval_cases r
            · exact ⟨0, by simp, by omega, divRepresented_zero _⟩
            · exact ⟨1, by simp, by omega, divRepresented_single hcpos (one_dvd _)⟩
            · rcases hq_mod with hm1 | hm2 | hm3 | hm4
              · exact ⟨1 + q, by omega, by omega, divRepresented_pair hcpos (one_dvd _) hq_dvd (by omega)⟩
              · exact ⟨q, hm2, by omega, divRepresented_single hcpos hq_dvd⟩
              · exact ⟨1 + 3 + q, by omega, by omega,
                  divRepresented_triple hcpos (one_dvd _) h3_dvd hq_dvd (by omega) (by omega) (by omega)⟩
              · exact ⟨3 + q, by omega, by omega, divRepresented_pair hcpos h3_dvd hq_dvd (by omega)⟩
            · exact ⟨3, by simp, by omega, divRepresented_single hcpos h3_dvd⟩
            · exact ⟨1 + 3, by simp, by omega, divRepresented_pair hcpos (one_dvd _) h3_dvd (by omega)⟩
  · -- Rule 3: resSeeds table
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨F0, p0, M⟩, hmem, ⟨hp0, hM⟩, hdvd⟩ := h
    dsimp only at hp0 hM hdvd
    subst hp0
    have hval := List.all_eq_true.mp resSeeds_valid (F0, p0, M) hmem
    simp only [Bool.and_eq_true] at hval
    have hF0 : ValidFactors F0 := validFactors_of_bool hval.1
    have hres0 := checkResSeed_sound hF0 hval.2
    have hcpos : 0 < valF Fc := valF_pos hFc
    have hPc : ProperSum (valF Fc) = ((sigF Fc - valF Fc : ℕ) : ℤ) := by
      rw [properSum_valF hFc]; omega
    have hdiv : valF F0 ∣ valF Fc := valF_dvd_of_fDvd hF0 hdvd
    refine ⟨valF Fc, a, M, hb, ha, hcop, hcpos, ?_, ?_, ?_⟩
    · rw [hPc]; exact_mod_cast (show (p0 + 1) * L ≤ p0 * (sigF Fc - valF Fc) + 1 by omega)
    · rw [hPb]
      have h1 : (M + (p0 + 1) * L : ℕ) ≤ Pb + 1 := by omega
      have h2 : ((M + (p0 + 1) * L : ℕ) : ℤ) ≤ ((Pb + 1 : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at h2 ⊢; linarith
    · intro r hr
      obtain ⟨y, hymod, hyle, hyrep⟩ := hres0 r hr
      exact ⟨y, hymod, hyle, divRepresented_mono_dvd hcpos.ne' hdiv hyrep⟩

private def raiseReadyLoop (raiseFn : List (ℕ × ℕ) → ℕ → ℕ → ℕ → Bool)
    (F : List (ℕ × ℕ)) (L : ℕ) : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, cur => cur
  | k + 1, cur =>
    let cur' :=
      match cur[k]? with
      | none => cur
      | some (p, a0) =>
        let a := lookupExp F p
        if a0 < a && valF cur ≤ sigF cur &&
           raiseFn (removeIdx cur k) (sigF cur - valF cur) p L then
          setExp cur k a
        else cur
    raiseReadyLoop raiseFn F L k cur'

private def addNewLoop (L G : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ) → Option (List (ℕ × ℕ))
  | cur, [] => some cur
  | cur, (p, a) :: rest =>
    if lookupExp cur p == 0 then
      let b := valF cur
      let sb := sigF cur
      if sb < b then none
      else
        let P := sb - b
        if p * G + 2 * L ≤ P + 1 && b + 2 * L ≤ (p + 1) * P + 1 &&
           (a == 1 || ((p + 1) * L ≤ p * P + 1 && (p + 2) * L + p ≤ b + (p + 1) * P + 2)) then
          addNewLoop L G (insertPair (p, a) cur) rest
        else none
    else addNewLoop L G cur rest

private def raiseAllLoop (raiseFn : List (ℕ × ℕ) → ℕ → ℕ → ℕ → Bool)
    (F : List (ℕ × ℕ)) (L : ℕ) : ℕ → List (ℕ × ℕ) → Option (List (ℕ × ℕ))
  | 0, cur => some cur
  | k + 1, cur =>
    match cur[k]? with
    | none => raiseAllLoop raiseFn F L k cur
    | some (p, a0) =>
      let a := lookupExp F p
      if a0 < a then
        if valF cur ≤ sigF cur && raiseFn (removeIdx cur k) (sigF cur - valF cur) p L then
          raiseAllLoop raiseFn F L k (setExp cur k a)
        else none
      else raiseAllLoop raiseFn F L k cur

private def o1PreFromSeedAux (raiseFn : List (ℕ × ℕ) → ℕ → ℕ → ℕ → Bool)
    (F F0 : List (ℕ × ℕ)) (L G : ℕ) : Bool :=
  if !fDvd F0 F then false
  else
    let cur1 := raiseReadyLoop raiseFn F L F0.length F0
    match addNewLoop L G cur1 F with
    | none => false
    | some cur2 =>
      match raiseAllLoop raiseFn F L cur2.length cur2 with
      | none => false
      | some cur3 => cur3 == F

private lemma raiseReadyLoop_sound {raiseFn : List (ℕ × ℕ) → ℕ → ℕ → ℕ → Bool}
    (hraise : ∀ {Fc : List (ℕ × ℕ)} {b Pb p a L : ℕ},
      ValidFactors Fc → p.Prime → (valF Fc).Coprime p → b = valF Fc * p ^ a → 1 ≤ a →
      ProperSum b = (Pb : ℤ) → raiseFn Fc Pb p L = true → RaiseOk b p L)
    {F : List (ℕ × ℕ)} {L G n : ℕ} {cur : List (ℕ × ℕ)}
    (hcur : ValidFactors cur) (hpre : PreCertifiedBase (valF cur) L G) :
    ValidFactors (raiseReadyLoop raiseFn F L n cur) ∧
    PreCertifiedBase (valF (raiseReadyLoop raiseFn F L n cur)) L G := by
  induction n generalizing cur with
  | zero => exact ⟨hcur, hpre⟩
  | succ k ih =>
    unfold raiseReadyLoop
    dsimp only
    cases hget : cur[k]? with
    | none => exact ih hcur hpre
    | some pa =>
      rcases pa with ⟨p, a0⟩
      dsimp only
      split_ifs with hcond
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨⟨hlt, hle⟩, hr⟩ := hcond
        obtain ⟨heq, hcop, hp, ha0⟩ := valF_removeIdx hcur hget
        have hFc : ValidFactors (removeIdx cur k) := validFactors_removeIdx k hcur
        have hPb : ProperSum (valF cur) = ((sigF cur - valF cur : ℕ) : ℤ) := by
          rw [properSum_valF hcur]; omega
        have hrok : RaiseOk (valF cur) p L := hraise hFc hp hcop heq ha0 hPb hr
        have hvf' : ValidFactors (setExp cur k (lookupExp F p)) :=
          validFactors_setExp (by omega) hcur
        have hpre' : PreCertifiedBase (valF (setExp cur k (lookupExp F p))) L G := by
          rw [valF_setExp_add hget (le_of_lt hlt)]
          exact (preCertifiedBase_mul_existing_prime_pow hpre hp hrok (lookupExp F p - a0)).1
        exact ih hvf' hpre'
      · exact ih hcur hpre

private lemma addNewLoop_sound {L G : ℕ} {cur rem res : List (ℕ × ℕ)}
    (hcur : ValidFactors cur) (hpre : PreCertifiedBase (valF cur) L G)
    (hrem : ∀ pa ∈ rem, pa.1.Prime ∧ 1 ≤ pa.2)
    (h : addNewLoop L G cur rem = some res) :
    ValidFactors res ∧ PreCertifiedBase (valF res) L G := by
  induction rem generalizing cur with
  | nil =>
    simp only [addNewLoop, Option.some.injEq] at h
    subst h; exact ⟨hcur, hpre⟩
  | cons pa rest ih =>
    rcases pa with ⟨p, a⟩
    have hpa := hrem (p, a) List.mem_cons_self
    have hrest : ∀ x ∈ rest, x.1.Prime ∧ 1 ≤ x.2 := fun x hx => hrem x (List.mem_cons_of_mem _ hx)
    unfold addNewLoop at h
    dsimp only at h
    split_ifs at h with hzero hsb hcond
    · simp only [beq_iff_eq] at hzero
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      obtain ⟨⟨hwide, hover⟩, hra⟩ := hcond
      have hne : ∀ qb ∈ cur, qb.1 ≠ p := not_mem_of_lookupExp_zero hcur hzero
      have hvf' : ValidFactors (insertPair (p, a) cur) := validFactors_insertPair hcur hpa.1 hpa.2 hne
      have hcop : (valF cur).Coprime p := coprime_valF_of_ne hcur hpa.1 hne
      have hP : ProperSum (valF cur) = ((sigF cur - valF cur : ℕ) : ℤ) := by
        rw [properSum_valF hcur]; omega
      have hPbp : ProperSum (valF cur * p) =
          (valF cur : ℤ) + ProperSum (valF cur) + (p : ℤ) * ProperSum (valF cur) :=
        properSum_mul_prime_coprime hpa.1 hcop
      have hpre' : PreCertifiedBase (valF (insertPair (p, a) cur)) L G := by
        rw [valF_insertPair]
        refine preCertifiedBase_mul_new_prime_pow hpre hpa.1 hcop hpa.2 ?_ ?_ ?_
        · rw [hP]
          have h1 : ((p * G + 2 * L : ℕ) : ℤ) ≤ ((sigF cur - valF cur + 1 : ℕ) : ℤ) := by exact_mod_cast hwide
          push_cast at h1; linarith
        · rw [hP]
          have h1 : ((valF cur + 2 * L : ℕ) : ℤ) ≤ (((p + 1) * (sigF cur - valF cur) + 1 : ℕ) : ℤ) := by
            exact_mod_cast hover
          push_cast at h1; linarith
        · intro ha_gt
          rcases hra with ha1 | ⟨hsm, hMb⟩
          · omega
          · refine ⟨?_, ?_⟩
            · rw [hP]; exact_mod_cast hsm
            · rw [hPbp, hP]
              have hp_pos : 0 < p := hpa.1.pos
              have h1 : (((p + 2) * L + p : ℕ) : ℤ) ≤ ((valF cur + (p + 1) * (sigF cur - valF cur) + 2 : ℕ) : ℤ) := by
                exact_mod_cast hMb
              have hsub : 1 ≤ L + p := by omega
              push_cast [Nat.cast_sub hsub] at h1 ⊢
              linarith
      exact ih hvf' hpre' hrest h
    · exact ih hcur hpre hrest h

private lemma raiseAllLoop_sound {raiseFn : List (ℕ × ℕ) → ℕ → ℕ → ℕ → Bool}
    (hraise : ∀ {Fc : List (ℕ × ℕ)} {b Pb p a L : ℕ},
      ValidFactors Fc → p.Prime → (valF Fc).Coprime p → b = valF Fc * p ^ a → 1 ≤ a →
      ProperSum b = (Pb : ℤ) → raiseFn Fc Pb p L = true → RaiseOk b p L)
    {F : List (ℕ × ℕ)} {L G n : ℕ} {cur res : List (ℕ × ℕ)}
    (hcur : ValidFactors cur) (hpre : PreCertifiedBase (valF cur) L G)
    (h : raiseAllLoop raiseFn F L n cur = some res) :
    ValidFactors res ∧ PreCertifiedBase (valF res) L G := by
  induction n generalizing cur with
  | zero =>
    simp only [raiseAllLoop, Option.some.injEq] at h
    subst h; exact ⟨hcur, hpre⟩
  | succ k ih =>
    unfold raiseAllLoop at h
    cases hget : cur[k]? with
    | none => rw [hget] at h; exact ih hcur hpre h
    | some pa =>
      rcases pa with ⟨p, a0⟩
      rw [hget] at h
      dsimp only at h
      split_ifs at h with hlt hcond
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨hle, hr⟩ := hcond
        obtain ⟨heq, hcop, hp, ha0⟩ := valF_removeIdx hcur hget
        have hFc : ValidFactors (removeIdx cur k) := validFactors_removeIdx k hcur
        have hPb : ProperSum (valF cur) = ((sigF cur - valF cur : ℕ) : ℤ) := by
          rw [properSum_valF hcur]; omega
        have hrok : RaiseOk (valF cur) p L := hraise hFc hp hcop heq ha0 hPb hr
        have hvf' : ValidFactors (setExp cur k (lookupExp F p)) :=
          validFactors_setExp (by omega) hcur
        have hpre' : PreCertifiedBase (valF (setExp cur k (lookupExp F p))) L G := by
          rw [valF_setExp_add hget (le_of_lt hlt)]
          exact (preCertifiedBase_mul_existing_prime_pow hpre hp hrok (lookupExp F p - a0)).1
        exact ih hvf' hpre' h
      · exact ih hcur hpre h

private lemma validFactors_mem {F : List (ℕ × ℕ)} (hF : ValidFactors F) :
    ∀ pa ∈ F, pa.1.Prime ∧ 1 ≤ pa.2 := by
  induction F with
  | nil => intro _ hx; simp at hx
  | cons qb rest ih =>
    rcases qb with ⟨q, b⟩
    rcases hF with ⟨hq, hb, _, hrest⟩
    intro pa hpa
    simp only [List.mem_cons] at hpa
    rcases hpa with rfl | hpa
    · exact ⟨hq, hb⟩
    · exact ih hrest pa hpa

private lemma o1PreFromSeedAux_sound {raiseFn : List (ℕ × ℕ) → ℕ → ℕ → ℕ → Bool}
    (hraise : ∀ {Fc : List (ℕ × ℕ)} {b Pb p a L : ℕ},
      ValidFactors Fc → p.Prime → (valF Fc).Coprime p → b = valF Fc * p ^ a → 1 ≤ a →
      ProperSum b = (Pb : ℤ) → raiseFn Fc Pb p L = true → RaiseOk b p L)
    {F F0 : List (ℕ × ℕ)} {L G : ℕ}
    (hF : ValidFactors F) (hF0 : ValidFactors F0) (hpre0 : PreCertifiedBase (valF F0) L G)
    (h : o1PreFromSeedAux raiseFn F F0 L G = true) :
    PreCertifiedBase (valF F) L G := by
  unfold o1PreFromSeedAux at h
  dsimp only at h
  split_ifs at h with hdvd
  obtain ⟨hvf1, hpre1⟩ := raiseReadyLoop_sound hraise hF0 hpre0 (F := F) (n := F0.length)
  cases hadd : addNewLoop L G (raiseReadyLoop raiseFn F L F0.length F0) F with
  | none => rw [hadd] at h; simp at h
  | some cur2 =>
    rw [hadd] at h
    dsimp only at h
    obtain ⟨hvf2, hpre2⟩ := addNewLoop_sound hvf1 hpre1 (validFactors_mem hF) hadd
    cases hrall : raiseAllLoop raiseFn F L cur2.length cur2 with
    | none => rw [hrall] at h; simp at h
    | some cur3 =>
      rw [hrall] at h
      dsimp only at h
      obtain ⟨_, hpre3⟩ := raiseAllLoop_sound hraise hvf2 hpre2 hrall
      have heq : cur3 = F := by simpa using h
      subst heq; exact hpre3

private def o1RaiseOkFull (Fc : List (ℕ × ℕ)) (Pb p L : ℕ) : Bool :=
  if o1RaiseOkBase Fc Pb p L then true
  else
    let c := valF Fc
    let sc := sigF Fc
    if sc < c then false
    else
      let Pc := sc - c
      if (p + 1) * L > p * Pc + 1 || Pb + 1 < (p + 1) * L then false
      else
        let hiLim := Pb + 1 - (p + 1) * L
        preSeeds.any fun s =>
          let (F0, L2, G2) := s
          decide (2 * L2 + p - 1 ≤ Pc) && decide (L2 + p - 1 ≤ hiLim) &&
          o1PreFromSeedAux o1RaiseOkBase Fc F0 L2 G2

private lemma o1RaiseOkFull_sound {Fc : List (ℕ × ℕ)} {b Pb p a L : ℕ}
    (hFc : ValidFactors Fc) (hp : p.Prime) (hcop : (valF Fc).Coprime p)
    (hb : b = valF Fc * p ^ a) (ha : 1 ≤ a) (hPb : ProperSum b = (Pb : ℤ))
    (h : o1RaiseOkFull Fc Pb p L = true) :
    RaiseOk b p L := by
  unfold o1RaiseOkFull at h
  dsimp only at h
  split_ifs at h with hbase hsc hlim
  · exact o1RaiseOkBase_sound hFc hp hcop hb ha hPb hbase
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hsc hlim
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨F0, L2, G2⟩, hmem, ⟨hPcBnd, hHiBnd⟩, hseed⟩ := h
    dsimp only at hPcBnd hHiBnd hseed
    have hval := List.all_eq_true.mp preSeeds_valid (F0, L2, G2) hmem
    simp only [Bool.and_eq_true] at hval
    have hF0 : ValidFactors F0 := validFactors_of_bool hval.1
    have hpre0 : PreCertifiedBase (valF F0) L2 G2 := checkPreDirect_sound hF0 hval.2
    have hpreFc : PreCertifiedBase (valF Fc) L2 G2 :=
      o1PreFromSeedAux_sound o1RaiseOkBase_sound hFc hF0 hpre0 hseed
    have hcpos : 0 < valF Fc := valF_pos hFc
    have hPc : ProperSum (valF Fc) = ((sigF Fc - valF Fc : ℕ) : ℤ) := by
      rw [properSum_valF hFc]; omega
    have hppos : 0 < p := hp.pos
    refine ⟨valF Fc, a, L2 + p - 1, hb, ha, hcop, hcpos, ?_, ?_, fun r hrlt => ?_⟩
    · rw [hPc]; exact_mod_cast (show (p + 1) * L ≤ p * (sigF Fc - valF Fc) + 1 by omega)
    · rw [hPb]
      have h1 : (L2 + p - 1) + (p + 1) * L ≤ Pb + 1 := by omega
      have h2 : (((L2 + p - 1) + (p + 1) * L : ℕ) : ℤ) ≤ ((Pb + 1 : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at h2 ⊢; linarith
    · let k := (r + p - L2 % p) % p
      have hk_lt : k < p := Nat.mod_lt _ hppos
      refine ⟨L2 + k, ?_, by omega, ?_⟩
      · dsimp [k]
        have hdiv : L2 = p * (L2 / p) + L2 % p := (Nat.div_add_mod L2 p).symm
        have hlm : L2 % p < p := Nat.mod_lt L2 hppos
        rw [Nat.add_mod_mod, show L2 + (r + p - L2 % p) = p * (L2 / p + 1) + r by rw [Nat.mul_add, mul_one]; omega,
          Nat.mul_add_mod, Nat.mod_eq_of_lt hrlt]
      · have hmid : Represented (valF Fc) ((L2 + k : ℕ) : ℤ) :=
          hpreFc.middle _ (by push_cast; omega) (by rw [hPc]; push_cast; omega)
        obtain ⟨s, hs, hsum⟩ := hmid
        exact ⟨s, hs.trans Nat.properDivisors_subset_divisors, hsum⟩

private def o1CertFromSeed (F F0 : List (ℕ × ℕ)) (L G : ℕ) : Bool :=
  let b := valF F
  let sb := sigF F
  decide (b ≤ sb) && decide ((2 * G + 1) * (2 * L + 8 * G + 8) ≤ sb - b) &&
  o1PreFromSeedAux o1RaiseOkFull F F0 L G

private lemma o1CertFromSeed_sound {F F0 : List (ℕ × ℕ)} {L G : ℕ}
    (hF : ValidFactors F) (hF0 : ValidFactors F0) (hpre0 : PreCertifiedBase (valF F0) L G)
    (h : o1CertFromSeed F F0 L G = true) :
    CertifiedBase (valF F) L G := by
  unfold o1CertFromSeed at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hle, hlarge⟩, haux⟩ := h
  have hpre : PreCertifiedBase (valF F) L G :=
    o1PreFromSeedAux_sound o1RaiseOkFull_sound hF hF0 hpre0 haux
  have hP : ProperSum (valF F) = ((sigF F - valF F : ℕ) : ℤ) := by
    rw [properSum_valF hF]; omega
  exact hpre.toCertifiedBase (by rw [hP]; exact_mod_cast hlarge)

/- ### Section 6: Explicit Concrete Witnesses for the 27 Small-Excess Cases -/

private def concreteWitnesses : List (List (ℕ × ℕ) × List ℕ) :=
  [ ([(3, 1), (5, 1), (7, 1), (11, 1), (383, 1)], [1, 5]),
    ([(3, 1), (5, 1), (7, 1), (11, 2)], [1, 3, 7, 11, 15, 21, 33, 35]),
    ([(3, 1), (5, 1), (7, 2), (11, 1)], [1, 3, 5, 7, 15, 21, 33, 35, 49, 77]),
    ([(3, 1), (5, 1), (7, 2), (13, 1)], [3, 5, 13, 21]),
    ([(3, 1), (5, 2), (7, 1), (17, 1)], [1, 5]),
    ([(3, 2), (5, 1), (7, 1), (103, 1)], [1, 5]),
    ([(3, 2), (5, 1), (7, 2)], [5, 7, 9, 15]),
    ([(3, 2), (5, 1), (11, 1), (13, 1)], [1, 3, 9, 11, 13, 15, 33, 39, 45, 65]),
    ([(3, 2), (5, 1), (11, 1), (17, 1)], [1, 3, 5, 9]),
    ([(3, 2), (5, 2), (7, 1)], [1, 5, 7, 15, 21, 25]),
    ([(3, 2), (5, 2), (11, 1), (19, 1)],
      [3, 9, 11, 15, 19, 25, 33, 45, 55, 57, 75, 95, 99, 165, 209, 225, 275, 285, 475, 495]),
    ([(3, 2), (5, 2), (11, 1), (23, 1)],
      [5, 9, 11, 15, 23, 25, 33, 45, 69, 75, 99, 115, 165, 207, 225, 253, 345, 495]),
    ([(3, 2), (5, 2), (11, 1), (29, 1)],
      [1, 3, 5, 9, 11, 15, 25, 29, 45, 55, 75, 87, 99, 145, 165, 225, 261, 275]),
    ([(3, 2), (5, 2), (11, 1), (31, 1)],
      [1, 5, 9, 11, 25, 31, 33, 45, 55, 75, 93, 99, 155, 165, 225, 275]),
    ([(3, 2), (5, 2), (11, 1), (37, 1)], [3, 5, 9, 11, 25, 33, 37, 45, 75, 99, 111, 165]),
    ([(3, 2), (5, 2), (11, 1), (41, 1)], [3, 5, 9, 11, 15, 33, 41, 45]),
    ([(3, 2), (5, 2), (11, 1), (43, 2)],
      [1, 3, 5, 9, 11, 25, 33, 43, 45, 55, 75, 99, 129, 165, 215, 225, 387, 473]),
    ([(3, 3), (5, 1), (7, 1)], [3, 5, 7, 15]),
    ([(3, 3), (5, 1), (11, 1), (19, 1)],
      [1, 5, 9, 11, 15, 19, 27, 33, 45, 55, 95, 99, 135, 165, 171, 285]),
    ([(3, 3), (5, 1), (11, 1), (23, 1)],
      [1, 3, 5, 9, 11, 15, 23, 27, 33, 45, 55, 69, 99, 115, 135, 165]),
    ([(3, 3), (5, 1), (11, 1), (29, 1)], [1, 3, 9, 11, 15, 27, 29, 33, 55, 87]),
    ([(3, 3), (5, 1), (11, 1), (31, 1)], [3, 5, 9, 15, 27, 31]),
    ([(3, 3), (5, 2), (11, 1)], [1, 5, 9, 15]),
    ([(3, 3), (7, 1), (11, 1), (13, 2)], [7, 11]),
    ([(3, 4), (5, 2), (13, 2)],
      [5, 9, 15, 25, 27, 39, 45, 65, 75, 81, 117, 135, 169, 195, 225, 351, 405]),
    ([(3, 5), (5, 1), (11, 1), (73, 1), (163, 1)], [1, 3, 5, 9]),
    ([(3, 5), (5, 2), (13, 1)], [1, 3, 9, 13]) ]

private def isStrictSorted : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && isStrictSorted (b :: rest)

private lemma nodup_of_isStrictSorted : ∀ {l : List ℕ}, isStrictSorted l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_singleton _
  | a :: b :: rest, h => by
    simp only [isStrictSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    have hgt : ∀ x ∈ b :: rest, a < x := by
      have aux : ∀ (u : ℕ) (xs : List ℕ), isStrictSorted (u :: xs) = true → ∀ x ∈ xs, u < x := by
        intro u xs
        induction xs generalizing u with
        | nil => intro _ x hx; simp at hx
        | cons v vs ih =>
          intro h' x hx
          simp only [isStrictSorted, Bool.and_eq_true, decide_eq_true_eq] at h'
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact h'.1
          · exact lt_trans h'.1 (ih v h'.2 x hx)
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h.1
      · exact lt_trans h.1 (aux b rest h.2 x hx)
    exact List.nodup_cons.mpr ⟨fun ha => (lt_irrefl a) (hgt a ha), nodup_of_isStrictSorted h.2⟩

private def checkWitness (m E : ℕ) (ws : List ℕ) : Bool :=
  isStrictSorted ws && ws.all (fun d => d < m && m % d == 0) && (ws.sum == E)

private lemma pseudoperfect_of_checkWitness {m E : ℕ} {ws : List ℕ}
    (hm : 0 < m) (hE : (E : ℤ) = Excess m) (h : checkWitness m E ws = true) :
    m.Pseudoperfect := by
  simp only [checkWitness, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hsort, hdvd⟩, hsum⟩ := h
  have hnd : ws.Nodup := nodup_of_isStrictSorted hsort
  apply pseudoperfect_of_represented_excess hm
  refine ⟨ws.toFinset, ?_, ?_⟩
  · intro d hd
    have hmem := List.mem_toFinset.mp hd
    obtain ⟨hlt, hmod⟩ := hdvd d hmem
    exact Nat.mem_properDivisors.mpr ⟨Nat.dvd_of_mod_eq_zero hmod, hlt⟩
  · rw [← hE, ← hsum, ← Nat.cast_sum, List.sum_toFinset _ hnd]
    simp

private def lookupWitness (Fm : List (ℕ × ℕ)) : Option (List ℕ) :=
  (concreteWitnesses.find? (fun p => p.1 == Fm)).map Prod.snd

/- ### Section 7: Incremental Branch-and-Bound Checker and Soundness -/

private structure Slot where
  p : ℕ
  lo : ℕ
  pPow : ℕ
  sigPow : ℕ
  fixed : Bool
deriving DecidableEq

private def mkSlot (p : ℕ) : Slot :=
  { p := p, lo := 1, pPow := p, sigPow := p + 1, fixed := false }

private def Slot.fix (s : Slot) : Slot :=
  { s with fixed := true }

private def Slot.bump (s : Slot) : Slot :=
  { s with lo := s.lo + 1, pPow := s.pPow * s.p, sigPow := s.sigPow * s.p + 1, fixed := false }

private def Slot.toPair (s : Slot) : ℕ × ℕ := (s.p, s.lo)

private def slotsUn (st : List Slot) : ℕ :=
  st.foldl (fun acc s => acc * (if s.fixed then s.sigPow else s.p)) 1

private def slotsUd (st : List Slot) : ℕ :=
  st.foldl (fun acc s => acc * (if s.fixed then s.pPow else s.p - 1)) 1

private def slotsLn (st : List Slot) : ℕ :=
  st.foldl (fun acc s => acc * s.sigPow) 1

private def slotsLd (st : List Slot) : ℕ :=
  st.foldl (fun acc s => acc * s.pPow) 1

private def SlotMatches (s : Slot) (a : ℕ) : Prop :=
  s.p.Prime ∧ 3 ≤ s.p ∧ 1 ≤ s.lo ∧
  s.pPow = s.p ^ s.lo ∧ s.sigPow = sigmaPP s.p s.lo ∧
  (if s.fixed then a = s.lo else s.lo ≤ a)

private def SlotsMatch (st : List Slot) (exps : List ℕ) : Prop :=
  List.Forall₂ SlotMatches st exps ∧ List.Pairwise (fun s1 s2 => s1.p < s2.p) st

private def bVal (st : List Slot) (exps : List ℕ) : ℕ :=
  (st.zipWith (fun s a => s.p ^ a) exps).prod

private def bSig (st : List Slot) (exps : List ℕ) : ℕ :=
  (st.zipWith (fun s a => sigmaPP s.p a) exps).prod

private lemma foldl_mul_init (l : List ℕ) (init : ℕ) :
    l.foldl (· * ·) init = init * l.prod := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.prod_cons, ih]
    ring

private lemma foldl_map_mul {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ) :
    l.foldl (fun acc x => acc * f x) init = init * (l.map f).prod := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih]
    ring

private lemma slotsLd_eq_valF {st : List Slot} (h : ∀ s ∈ st, s.pPow = s.p ^ s.lo) :
    slotsLd st = valF (st.map Slot.toPair) := by
  have aux : ∀ (l : List Slot) (init : ℕ),
      (∀ s ∈ l, s.pPow = s.p ^ s.lo) →
      l.foldl (fun acc s => acc * s.pPow) init = init * valF (l.map Slot.toPair) := by
    intro l
    induction l with
    | nil => intro init _; simp [valF]
    | cons s rest ih =>
      intro init hs
      simp only [List.foldl_cons, List.map_cons, valF, Slot.toPair]
      rw [ih (init * s.pPow) (fun t ht => hs t (List.mem_cons_of_mem _ ht)),
        hs s List.mem_cons_self]
      ring
  simpa [slotsLd] using aux st 1 h

private lemma slotsLn_eq_sigF {st : List Slot} (h : ∀ s ∈ st, s.sigPow = sigmaPP s.p s.lo) :
    slotsLn st = sigF (st.map Slot.toPair) := by
  have aux : ∀ (l : List Slot) (init : ℕ),
      (∀ s ∈ l, s.sigPow = sigmaPP s.p s.lo) →
      l.foldl (fun acc s => acc * s.sigPow) init = init * sigF (l.map Slot.toPair) := by
    intro l
    induction l with
    | nil => intro init _; simp [sigF]
    | cons s rest ih =>
      intro init hs
      simp only [List.foldl_cons, List.map_cons, sigF, Slot.toPair]
      rw [ih (init * s.sigPow) (fun t ht => hs t (List.mem_cons_of_mem _ ht)),
        hs s List.mem_cons_self]
      ring
  simpa [slotsLn] using aux st 1 h

private lemma validFactors_of_slotsMatch {st : List Slot} {exps : List ℕ}
    (hm : SlotsMatch st exps) : ValidFactors (st.map Slot.toPair) := by
  obtain ⟨hf, hp⟩ := hm
  induction hf with
  | nil => trivial
  | cons hs hrest ih =>
    rcases hp with _ | ⟨hlt, hprest⟩
    refine ⟨hs.1, hs.2.2.1, ?_, ih hprest⟩
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    exact hlt t ht

private lemma mem_zipWith_fst {α β γ : Type*} {f : α → β → γ} {l₁ : List α} {l₂ : List β} {c : γ}
    (h : c ∈ List.zipWith f l₁ l₂) : ∃ a ∈ l₁, ∃ b ∈ l₂, f a b = c := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨x, List.mem_cons_self, y, List.mem_cons_self, rfl⟩
      · obtain ⟨a, ha, b, hb, rfl⟩ := ih h
        exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, rfl⟩

private lemma validFactors_zipWith_of_slotsMatch {st : List Slot} {exps : List ℕ}
    (hm : SlotsMatch st exps) : ValidFactors (st.zipWith (fun s a => (s.p, a)) exps) := by
  obtain ⟨hf, hp⟩ := hm
  induction hf with
  | nil => trivial
  | @cons s a rest arest hs hrest ih =>
    rcases hp with _ | ⟨hlt, hprest⟩
    have ha1 : 1 ≤ a := by
      have hlo := hs.2.2.1
      have hcmp := hs.2.2.2.2.2
      split_ifs at hcmp <;> omega
    refine ⟨hs.1, ha1, ?_, ih hprest⟩
    intro q hq
    obtain ⟨s', hs', _, _, rfl⟩ := mem_zipWith_fst hq
    exact hlt s' hs'

private lemma bVal_eq_valF_zip {st : List Slot} {exps : List ℕ} :
    bVal st exps = valF (st.zipWith (fun s a => (s.p, a)) exps) := by
  unfold bVal
  induction st generalizing exps with
  | nil => simp [valF]
  | cons s rest ih =>
    cases exps with
    | nil => simp [valF]
    | cons a arest => simp [valF, ih]

private lemma bSig_eq_sigF_zip {st : List Slot} {exps : List ℕ} :
    bSig st exps = sigF (st.zipWith (fun s a => (s.p, a)) exps) := by
  unfold bSig
  induction st generalizing exps with
  | nil => simp [sigF]
  | cons s rest ih =>
    cases exps with
    | nil => simp [sigF]
    | cons a arest => simp [sigF, ih]

private lemma bSig_eq_sigma_one_bVal {st : List Slot} {exps : List ℕ} (hm : SlotsMatch st exps) :
    bSig st exps = sigma 1 (bVal st exps) := by
  rw [bSig_eq_sigF_zip, bVal_eq_valF_zip]
  exact sigF_eq_sigma_one (validFactors_zipWith_of_slotsMatch hm)

private lemma bVal_pos {st : List Slot} {exps : List ℕ} (hm : SlotsMatch st exps) :
    0 < bVal st exps := by
  rw [bVal_eq_valF_zip]
  exact valF_pos (validFactors_zipWith_of_slotsMatch hm)

private lemma slots_bounds {st : List Slot} {exps : List ℕ} (hm : SlotsMatch st exps) :
    0 < slotsLd st ∧ 0 < slotsUd st ∧
    slotsLd st ≤ bVal st exps ∧
    slotsLn st * bVal st exps ≤ bSig st exps * slotsLd st ∧
    bSig st exps * slotsUd st ≤ slotsUn st * bVal st exps := by
  obtain ⟨hf, hpw⟩ := hm
  clear hpw
  have hUn : slotsUn st = (st.map fun s => if s.fixed then s.sigPow else s.p).prod := by
    simpa [slotsUn] using foldl_map_mul (fun s : Slot => if s.fixed then s.sigPow else s.p) st 1
  have hUd : slotsUd st = (st.map fun s => if s.fixed then s.pPow else s.p - 1).prod := by
    simpa [slotsUd] using foldl_map_mul (fun s : Slot => if s.fixed then s.pPow else s.p - 1) st 1
  have hLn : slotsLn st = (st.map Slot.sigPow).prod := by
    simpa [slotsLn] using foldl_map_mul Slot.sigPow st 1
  have hLd : slotsLd st = (st.map Slot.pPow).prod := by
    simpa [slotsLd] using foldl_map_mul Slot.pPow st 1
  rw [hUn, hUd, hLn, hLd]
  clear hUn hUd hLn hLd
  unfold bVal bSig
  induction hf with
  | nil => simp
  | @cons s a rest arest hs hrest ih =>
    obtain ⟨hp, hp3, hlo1, hpPow, hsigPow, hcmp⟩ := hs
    obtain ⟨hLd0, hUd0, hle, hL, hU⟩ := ih
    simp only [List.map_cons, List.prod_cons, List.zipWith_cons_cons]
    have hloa : s.lo ≤ a := by split_ifs at hcmp <;> omega
    have hpp : 0 < s.pPow := by rw [hpPow]; exact pow_pos hp.pos _
    have hpow_le : s.pPow ≤ s.p ^ a := by rw [hpPow]; exact Nat.pow_le_pow_right hp.pos hloa
    have hL1 : s.sigPow * s.p ^ a ≤ sigmaPP s.p a * s.pPow := by
      rw [hpPow, hsigPow]; exact sigmaPP_mono_ratio hp.pos hloa
    have hUd1 : 0 < (if s.fixed then s.pPow else s.p - 1) := by
      split_ifs <;> omega
    have hU1 : sigmaPP s.p a * (if s.fixed then s.pPow else s.p - 1) ≤
        (if s.fixed then s.sigPow else s.p) * s.p ^ a := by
      split_ifs at hcmp ⊢
      · subst hcmp; rw [hpPow, hsigPow]
      · exact le_of_lt (sigmaPP_lt_limit hp.one_lt a)
    refine ⟨Nat.mul_pos hpp hLd0, Nat.mul_pos hUd1 hUd0,
      Nat.mul_le_mul hpow_le hle, ?_, ?_⟩
    · calc (s.sigPow * (rest.map Slot.sigPow).prod) * (s.p ^ a * (rest.zipWith (fun s a => s.p ^ a) arest).prod)
          = (s.sigPow * s.p ^ a) * ((rest.map Slot.sigPow).prod * (rest.zipWith (fun s a => s.p ^ a) arest).prod) := by ring
        _ ≤ (sigmaPP s.p a * s.pPow) * ((rest.zipWith (fun s a => sigmaPP s.p a) arest).prod * (rest.map Slot.pPow).prod) :=
            Nat.mul_le_mul hL1 hL
        _ = (sigmaPP s.p a * (rest.zipWith (fun s a => sigmaPP s.p a) arest).prod) * (s.pPow * (rest.map Slot.pPow).prod) := by ring
    · calc (sigmaPP s.p a * (rest.zipWith (fun s a => sigmaPP s.p a) arest).prod) *
              ((if s.fixed then s.pPow else s.p - 1) * (rest.map fun s => if s.fixed then s.pPow else s.p - 1).prod)
          = (sigmaPP s.p a * (if s.fixed then s.pPow else s.p - 1)) *
              ((rest.zipWith (fun s a => sigmaPP s.p a) arest).prod * (rest.map fun s => if s.fixed then s.pPow else s.p - 1).prod) := by ring
        _ ≤ ((if s.fixed then s.sigPow else s.p) * s.p ^ a) *
              ((rest.map fun s => if s.fixed then s.sigPow else s.p).prod * (rest.zipWith (fun s a => s.p ^ a) arest).prod) :=
            Nat.mul_le_mul hU1 hU
        _ = ((if s.fixed then s.sigPow else s.p) * (rest.map fun s => if s.fixed then s.sigPow else s.p).prod) *
              (s.p ^ a * (rest.zipWith (fun s a => s.p ^ a) arest).prod) := by ring

private lemma bVal_bSig_eq_of_all_fixed {st : List Slot} {exps : List ℕ}
    (hm : SlotsMatch st exps) (hfix : st.all Slot.fixed = true) :
    bVal st exps = slotsLd st ∧ bSig st exps = slotsLn st ∧
    st.zipWith (fun s a => (s.p, a)) exps = st.map Slot.toPair := by
  obtain ⟨hf, hpw⟩ := hm
  clear hpw
  have hLn : slotsLn st = (st.map Slot.sigPow).prod := by
    simpa [slotsLn] using foldl_map_mul Slot.sigPow st 1
  have hLd : slotsLd st = (st.map Slot.pPow).prod := by
    simpa [slotsLd] using foldl_map_mul Slot.pPow st 1
  rw [hLn, hLd]
  clear hLn hLd
  unfold bVal bSig
  induction hf with
  | nil => simp
  | @cons s a rest arest hs hrest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hfix
    have hsf : s.fixed = true := hfix.1
    have hcmp := hs.2.2.2.2.2
    rw [hsf, if_pos rfl] at hcmp
    subst hcmp
    obtain ⟨h1, h2, h3⟩ := ih hfix.2
    simp only [List.zipWith_cons_cons, List.prod_cons, List.map_cons, Slot.toPair]
    refine ⟨by rw [h1, hs.2.2.2.1], by rw [h2, hs.2.2.2.2.1], by rw [h3]⟩

private def fixIdx : List Slot → ℕ → List Slot
  | [], _ => []
  | s :: rest, 0 => s.fix :: rest
  | s :: rest, i + 1 => s :: fixIdx rest i

private def bumpIdx : List Slot → ℕ → List Slot
  | [], _ => []
  | s :: rest, 0 => s.bump :: rest
  | s :: rest, i + 1 => s :: bumpIdx rest i

private lemma slotsLd_fixIdx (st : List Slot) (i : ℕ) :
    slotsLd (fixIdx st i) = slotsLd st := by
  have h1 : ∀ l k, ((fixIdx l k).map Slot.pPow) = l.map Slot.pPow := by
    intro l; induction l with
    | nil => intro k; simp [fixIdx]
    | cons s rest ih =>
      intro k; cases k with
      | zero => simp [fixIdx, Slot.fix]
      | succ k => simp [fixIdx, ih]
  rw [show slotsLd (fixIdx st i) = ((fixIdx st i).map Slot.pPow).prod by
    simpa [slotsLd] using foldl_map_mul Slot.pPow _ 1]
  rw [show slotsLd st = (st.map Slot.pPow).prod by
    simpa [slotsLd] using foldl_map_mul Slot.pPow _ 1]
  rw [h1]

private lemma slotsLd_bumpIdx {st : List Slot} {i : ℕ} {s : Slot} (hget : st[i]? = some s) :
    slotsLd (bumpIdx st i) = slotsLd st * s.p := by
  have h1 : ∀ l k, l[k]? = some s → ((bumpIdx l k).map Slot.pPow).prod = (l.map Slot.pPow).prod * s.p := by
    intro l; induction l with
    | nil => intro k h; simp at h
    | cons t rest ih =>
      intro k h; cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h; simp only [bumpIdx, Slot.bump, List.map_cons, List.prod_cons]; ring
      | succ k =>
        simp only [List.getElem?_cons_succ] at h
        simp only [bumpIdx, List.map_cons, List.prod_cons, ih k h]; ring
  rw [show slotsLd (bumpIdx st i) = ((bumpIdx st i).map Slot.pPow).prod by
    simpa [slotsLd] using foldl_map_mul Slot.pPow _ 1]
  rw [show slotsLd st = (st.map Slot.pPow).prod by
    simpa [slotsLd] using foldl_map_mul Slot.pPow _ 1]
  exact h1 st i hget

private lemma map_p_fixIdx (st : List Slot) (i : ℕ) :
    (fixIdx st i).map Slot.p = st.map Slot.p := by
  induction st generalizing i with
  | nil => simp [fixIdx]
  | cons s rest ih =>
    cases i with
    | zero => simp [fixIdx, Slot.fix]
    | succ i => simp [fixIdx, ih]

private lemma map_p_bumpIdx (st : List Slot) (i : ℕ) :
    (bumpIdx st i).map Slot.p = st.map Slot.p := by
  induction st generalizing i with
  | nil => simp [bumpIdx]
  | cons s rest ih =>
    cases i with
    | zero => simp [bumpIdx, Slot.bump]
    | succ i => simp [bumpIdx, ih]

private lemma pairwise_p_of_map_eq {l1 l2 : List Slot} (heq : l1.map Slot.p = l2.map Slot.p)
    (hp : List.Pairwise (fun s1 s2 => s1.p < s2.p) l2) :
    List.Pairwise (fun s1 s2 => s1.p < s2.p) l1 := by
  have h2 : List.Pairwise (· < ·) (l2.map Slot.p) := List.pairwise_map.mpr hp
  rw [← heq] at h2
  exact List.pairwise_map.mp h2

private lemma bVal_eq_of_map_p_eq {l1 l2 : List Slot} {exps : List ℕ}
    (heq : l1.map Slot.p = l2.map Slot.p) : bVal l1 exps = bVal l2 exps := by
  unfold bVal
  induction l1 generalizing l2 exps with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at heq
  | cons s1 r1 ih =>
    cases l2 with
    | nil => simp at heq
    | cons s2 r2 =>
      simp only [List.map_cons, List.cons.injEq] at heq
      cases exps with
      | nil => simp
      | cons a arest => simp [heq.1, ih heq.2]

private lemma bSig_eq_of_map_p_eq {l1 l2 : List Slot} {exps : List ℕ}
    (heq : l1.map Slot.p = l2.map Slot.p) : bSig l1 exps = bSig l2 exps := by
  unfold bSig
  induction l1 generalizing l2 exps with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at heq
  | cons s1 r1 ih =>
    cases l2 with
    | nil => simp at heq
    | cons s2 r2 =>
      simp only [List.map_cons, List.cons.injEq] at heq
      cases exps with
      | nil => simp
      | cons a arest => simp [heq.1, ih heq.2]

private lemma split_free_slot {st : List Slot} {exps : List ℕ} {i : ℕ} {s : Slot}
    (hm : SlotsMatch st exps) (hget : st[i]? = some s) (hfree : s.fixed = false) :
    SlotsMatch (fixIdx st i) exps ∨ SlotsMatch (bumpIdx st i) exps := by
  obtain ⟨hf, hp⟩ := hm
  have haux : ∀ {l : List Slot} {es : List ℕ} {k : ℕ},
      List.Forall₂ SlotMatches l es → l[k]? = some s → s.fixed = false →
      List.Forall₂ SlotMatches (fixIdx l k) es ∨ List.Forall₂ SlotMatches (bumpIdx l k) es := by
    intro l es k h
    induction h generalizing k with
    | nil => intro hg; simp at hg
    | @cons t a rest arest hs hrest ih =>
      cases k with
      | zero =>
        intro hg hf'
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
        subst hg
        have hcmp := hs.2.2.2.2.2
        rw [hf'] at hcmp
        simp only [Bool.false_eq_true, ↓reduceIte] at hcmp
        by_cases ha : a = t.lo
        · left
          refine List.Forall₂.cons ?_ hrest
          exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, by simp [Slot.fix, ha]⟩
        · right
          refine List.Forall₂.cons ?_ hrest
          refine ⟨hs.1, hs.2.1, by simp only [Slot.bump]; omega, ?_, ?_, ?_⟩
          · simp only [Slot.bump, hs.2.2.2.1, pow_succ]
          · simp only [Slot.bump, hs.2.2.2.2.1, sigmaPP]
          · have hlt : t.lo + 1 ≤ a := by omega
            simpa [Slot.bump] using hlt
      | succ k =>
        intro hg hf'
        simp only [List.getElem?_cons_succ] at hg
        rcases ih hg hf' with h1 | h2
        · exact Or.inl (List.Forall₂.cons hs h1)
        · exact Or.inr (List.Forall₂.cons hs h2)
  rcases haux hf hget hfree with h1 | h2
  · exact Or.inl ⟨h1, pairwise_p_of_map_eq (map_p_fixIdx st i) hp⟩
  · exact Or.inr ⟨h2, pairwise_p_of_map_eq (map_p_bumpIdx st i) hp⟩

private def FamilyCertified (st : List Slot) (L G : ℕ) : Prop :=
  CertifiedBase (slotsLd st) L G ∧
  ∀ s ∈ st, s.fixed = false → RaiseOk (slotsLd st) s.p L

private lemma familyCertified_fixIdx {st : List Slot} {i L G : ℕ}
    (h : FamilyCertified st L G) : FamilyCertified (fixIdx st i) L G := by
  refine ⟨by rw [slotsLd_fixIdx]; exact h.1, fun s hs hfree => ?_⟩
  rw [slotsLd_fixIdx]
  have hmem : ∀ (l : List Slot) (k : ℕ), s ∈ fixIdx l k → s.fixed = false → s ∈ l := by
    intro l; induction l with
    | nil => intro k hm _; simp [fixIdx] at hm
    | cons t rest ih =>
      intro k hm hf
      cases k with
      | zero =>
        simp only [fixIdx, List.mem_cons] at hm
        rcases hm with rfl | hm
        · simp [Slot.fix] at hf
        · exact List.mem_cons_of_mem _ hm
      | succ k =>
        simp only [fixIdx, List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih k hm hf)
  exact h.2 s (hmem st i hs hfree) hfree

private lemma familyCertified_bumpIdx {st : List Slot} {exps : List ℕ} {i L G : ℕ} {s : Slot}
    (hm : SlotsMatch st exps) (hget : st[i]? = some s) (hfree : s.fixed = false)
    (h : FamilyCertified st L G) : FamilyCertified (bumpIdx st i) L G := by
  have hs_mem : s ∈ st := List.mem_of_getElem? hget
  have hs_prime : s.p.Prime := by
    obtain ⟨hf, _⟩ := hm
    have haux : ∀ {l : List Slot} {es : List ℕ}, List.Forall₂ SlotMatches l es → ∀ t ∈ l, t.p.Prime := by
      intro l es h'; induction h' with
      | nil => intro _ hx; simp at hx
      | cons ht _ ih => intro u hu; simp only [List.mem_cons] at hu; rcases hu with rfl | hu; exact ht.1; exact ih u hu
    exact haux hf s hs_mem
  have hr_s : RaiseOk (slotsLd st) s.p L := h.2 s hs_mem hfree
  obtain ⟨hcert', hr_s'⟩ := certifiedBase_mul_existing_prime h.1 hs_prime hr_s
  rw [← slotsLd_bumpIdx hget] at hcert' hr_s'
  refine ⟨hcert', fun t ht htfree => ?_⟩
  rw [slotsLd_bumpIdx hget]
  -- Either t = s.bump (same prime s.p) or t ∈ st with t.p ≠ s.p
  have hcase : ∀ (l : List Slot) (k : ℕ), l[k]? = some s → t ∈ bumpIdx l k →
      List.Pairwise (fun a b => a.p < b.p) l →
      t.p = s.p ∨ (t ∈ l ∧ t.p ≠ s.p) := by
    intro l; induction l with
    | nil => intro k hg _ _; simp at hg
    | cons u rest ih =>
      intro k hg hmem hpw
      rcases hpw with _ | ⟨hlt, hprest⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
        subst hg
        simp only [bumpIdx, List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact Or.inl rfl
        · exact Or.inr ⟨List.mem_cons_of_mem _ hmem, ne_of_gt (hlt t hmem)⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hg
        simp only [bumpIdx, List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact Or.inr ⟨List.mem_cons_self, ne_of_lt (hlt s (List.mem_of_getElem? hg))⟩
        · rcases ih k hg hmem hprest with heq | ⟨hm2, hne⟩
          · exact Or.inl heq
          · exact Or.inr ⟨List.mem_cons_of_mem _ hm2, hne⟩
  rcases hcase st i hget ht hm.2 with heq | ⟨htmem, hne⟩
  · rw [heq, ← slotsLd_bumpIdx hget]; exact hr_s'
  · have ht_prime : t.p.Prime := by
      obtain ⟨hf, _⟩ := hm
      have haux : ∀ {l : List Slot} {es : List ℕ}, List.Forall₂ SlotMatches l es → ∀ u ∈ l, u.p.Prime := by
        intro l es h'; induction h' with
        | nil => intro _ hx; simp at hx
        | cons hu _ ih => intro v hv; simp only [List.mem_cons] at hv; rcases hv with rfl | hv; exact hu.1; exact ih v hv
      exact haux hf t htmem
    exact raiseOk_mul_other_prime (by have := h.1.b_gt_one; omega) ht_prime hs_prime hne (h.2 t htmem htfree)

private def gapSum : List Slot → List ℕ → ℕ
  | [], _ => 0
  | _, [] => 0
  | s :: rest, a :: arest => (a - s.lo) + gapSum rest arest

private lemma certifiedBase_of_familyCertified :
    ∀ (N : ℕ) {st : List Slot} {exps : List ℕ} {L G : ℕ},
      gapSum st exps = N → SlotsMatch st exps → FamilyCertified st L G →
      CertifiedBase (bVal st exps) L G
  | 0, st, exps, L, G, hgap, hm, hfc => by
    have heq : bVal st exps = slotsLd st := by
      rw [show slotsLd st = (st.map Slot.pPow).prod by
        simpa [slotsLd] using foldl_map_mul Slot.pPow _ 1]
      unfold bVal
      obtain ⟨hf, hpw⟩ := hm
      clear hpw hfc
      induction hf with
      | nil => simp
      | @cons s a rest arest hs hrest ih =>
        simp only [gapSum, Nat.add_eq_zero_iff] at hgap
        have hloa : s.lo ≤ a := by
          have hcmp := hs.2.2.2.2.2; split_ifs at hcmp <;> omega
        have ha : a = s.lo := by omega
        simp only [List.zipWith_cons_cons, List.prod_cons, List.map_cons, ha, hs.2.2.2.1, ih hgap.2]
    rw [heq]; exact hfc.1
  | N + 1, st, exps, L, G, hgap, hm, hfc => by
    -- Find an index i with s.lo < a (must be free!)
    have hex : ∃ (i : ℕ) (s : Slot) (a : ℕ),
        st[i]? = some s ∧ exps[i]? = some a ∧ s.lo < a ∧ s.fixed = false ∧
        gapSum (bumpIdx st i) exps = N := by
      have aux : ∀ {l : List Slot} {es : List ℕ},
          List.Forall₂ SlotMatches l es → 0 < gapSum l es →
          ∃ (i : ℕ) (s : Slot) (a : ℕ),
            l[i]? = some s ∧ es[i]? = some a ∧ s.lo < a ∧ s.fixed = false ∧
            gapSum (bumpIdx l i) es + 1 = gapSum l es := by
        intro l es h; induction h with
        | nil => intro hg; simp [gapSum] at hg
        | @cons s a rest arest hs hrest ih =>
          intro hg
          simp only [gapSum] at hg
          by_cases hlt : s.lo < a
          · have hfree : s.fixed = false := by
              have hcmp := hs.2.2.2.2.2
              cases hsf : s.fixed
              · rfl
              · rw [hsf, if_pos rfl] at hcmp; omega
            refine ⟨0, s, a, rfl, rfl, hlt, hfree, ?_⟩
            simp only [bumpIdx, Slot.bump, gapSum]; omega
          · have hg2 : 0 < gapSum rest arest := by omega
            obtain ⟨i, t, b, h1, h2, h3, h4, h5⟩ := ih hg2
            refine ⟨i + 1, t, b, h1, h2, h3, h4, ?_⟩
            simp only [bumpIdx, gapSum]; omega
      obtain ⟨i, s, a, h1, h2, h3, h4, h5⟩ := aux hm.1 (by omega)
      exact ⟨i, s, a, h1, h2, h3, h4, by omega⟩
    obtain ⟨i, s, a, hget, ha_get, hlt, hfree, hgap'⟩ := hex
    have hmatch' : SlotsMatch (bumpIdx st i) exps := by
      rcases split_free_slot hm hget hfree with hfix | hbump
      · exfalso
        -- In fixIdx st i, exps[i] = s.lo, contradicting s.lo < a
        have hcontr : ∀ {l : List Slot} {es : List ℕ} {k : ℕ},
            List.Forall₂ SlotMatches (fixIdx l k) es → l[k]? = some s → es[k]? = some a → a = s.lo := by
          intro l es k hf'
          induction l generalizing es k with
          | nil => intro h; simp at h
          | cons u rest ih =>
            cases es with
            | nil => cases k <;> simp [fixIdx] at hf'
            | cons b brest =>
              cases k with
              | zero =>
                intro h1 h2
                simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
                subst h1; subst h2
                simp only [fixIdx, List.forall₂_cons] at hf'
                have hcmp := hf'.1.2.2.2.2.2
                simpa [Slot.fix] using hcmp
              | succ k =>
                intro h1 h2
                simp only [fixIdx, List.forall₂_cons] at hf'
                exact ih hf'.2 h1 h2
        have := hcontr hfix.1 hget ha_get
        omega
      · exact hbump
    have hfc' := familyCertified_bumpIdx hm hget hfree hfc
    have hbv : bVal (bumpIdx st i) exps = bVal st exps := bVal_eq_of_map_p_eq (map_p_bumpIdx st i)
    rw [← hbv]
    exact certifiedBase_of_familyCertified N hgap' hmatch' hfc'

private def checkAllFreeRaise (F : List (ℕ × ℕ)) (st : List Slot) (Pb L : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 =>
    match st[k]? with
    | none => checkAllFreeRaise F st Pb L k
    | some s =>
      (if s.fixed then true else o1RaiseOkFull (removeIdx F k) Pb s.p L) &&
      checkAllFreeRaise F st Pb L k

private def findGoodFromSeeds (F : List (ℕ × ℕ)) (st : List Slot) (Pb : ℕ) :
    List (List (ℕ × ℕ) × ℕ × ℕ) → Option (ℕ × ℕ)
  | [] => none
  | (F0, L0, G0) :: rest =>
    if fDvd F0 F && Nat.ble ((2 * G0 + 1) * (2 * L0 + 8 * G0 + 8)) Pb &&
       o1PreFromSeedAux o1RaiseOkFull F F0 L0 G0 && checkAllFreeRaise F st Pb L0 st.length then
      some (L0, G0)
    else findGoodFromSeeds F st Pb rest

private def findGoodFamily (st : List Slot) : Option (ℕ × ℕ) :=
  if st.isEmpty then none
  else
    let F := st.map Slot.toPair
    let b := slotsLd st
    let sb := slotsLn st
    if Nat.blt sb b then none
    else findGoodFromSeeds F st (sb - b) preSeeds

private lemma findGoodFamily_sound {st : List Slot} {exps : List ℕ} {L G : ℕ}
    (hm : SlotsMatch st exps) (h : findGoodFamily st = some (L, G)) :
    FamilyCertified st L G := by
  have hF : ValidFactors (st.map Slot.toPair) := validFactors_of_slotsMatch hm
  have hLd : slotsLd st = valF (st.map Slot.toPair) := by
    apply slotsLd_eq_valF
    obtain ⟨hf, _⟩ := hm
    have aux : ∀ {l : List Slot} {es : List ℕ}, List.Forall₂ SlotMatches l es →
        ∀ s ∈ l, s.pPow = s.p ^ s.lo := by
      intro l es h'; induction h' with
      | nil => intro _ hx; simp at hx
      | cons hs _ ih => intro t ht; simp only [List.mem_cons] at ht; rcases ht with rfl | ht; exact hs.2.2.2.1; exact ih t ht
    exact aux hf
  have hLn : slotsLn st = sigF (st.map Slot.toPair) := by
    apply slotsLn_eq_sigF
    obtain ⟨hf, _⟩ := hm
    have aux : ∀ {l : List Slot} {es : List ℕ}, List.Forall₂ SlotMatches l es →
        ∀ s ∈ l, s.sigPow = sigmaPP s.p s.lo := by
      intro l es h'; induction h' with
      | nil => intro _ hx; simp at hx
      | cons hs _ ih => intro t ht; simp only [List.mem_cons] at ht; rcases ht with rfl | ht; exact hs.2.2.2.2.1; exact ih t ht
    exact aux hf
  have hfree_sound : ∀ (L' : ℕ), valF (st.map Slot.toPair) ≤ sigF (st.map Slot.toPair) →
      checkAllFreeRaise (st.map Slot.toPair) st (sigF (st.map Slot.toPair) - valF (st.map Slot.toPair)) L' st.length = true →
      ∀ s ∈ st, s.fixed = false → RaiseOk (slotsLd st) s.p L' := by
    intro L' hle hchk s hs hfree
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    have hPb : ProperSum (valF (st.map Slot.toPair)) =
        ((sigF (st.map Slot.toPair) - valF (st.map Slot.toPair) : ℕ) : ℤ) := by
      rw [properSum_valF hF]; omega
    have haux : ∀ k, k ≤ st.length →
        checkAllFreeRaise (st.map Slot.toPair) st (sigF (st.map Slot.toPair) - valF (st.map Slot.toPair)) L' k = true →
        ∀ j, j < k → ∀ t, st[j]? = some t → t.fixed = false → RaiseOk (slotsLd st) t.p L' := by
      intro k
      induction k with
      | zero => intro _ _ j hj; omega
      | succ k ih =>
        intro hk hck j hj t hget htfree
        unfold checkAllFreeRaise at hck
        by_cases hjk : j = k
        · subst hjk
          rw [hget] at hck
          simp only [htfree, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hck
          rw [hLd]
          have hgetF : (st.map Slot.toPair)[j]? = some (t.p, t.lo) := by
            simp [List.getElem?_map, hget, Slot.toPair]
          obtain ⟨heq, hcop, hp, ha⟩ := valF_removeIdx hF hgetF
          exact o1RaiseOkFull_sound (validFactors_removeIdx j hF) hp hcop heq ha hPb hck.1
        · cases hkget : st[k]? with
          | none => rw [hkget] at hck; exact ih (by omega) hck j (by omega) t hget htfree
          | some u =>
            rw [hkget] at hck
            simp only [Bool.and_eq_true] at hck
            exact ih (by omega) hck.2 j (by omega) t hget htfree
    exact haux st.length le_rfl hchk i hi st[i] (List.getElem?_eq_getElem hi) hfree
  unfold findGoodFamily at h
  dsimp only at h
  rw [hLd, hLn] at h
  split_ifs at h with hemp hsb
  have hle : valF (st.map Slot.toPair) ≤ sigF (st.map Slot.toPair) := by
    simp only [Nat.blt_eq, decide_eq_true_eq] at hsb; omega
  have hscan : ∀ (seeds : List (List (ℕ × ℕ) × ℕ × ℕ)),
      (∀ s ∈ seeds, s ∈ preSeeds) →
      findGoodFromSeeds (st.map Slot.toPair) st (sigF (st.map Slot.toPair) - valF (st.map Slot.toPair)) seeds = some (L, G) →
      FamilyCertified st L G := by
    intro seeds
    induction seeds with
    | nil => intro _ hf; simp [findGoodFromSeeds] at hf
    | cons s rest ih =>
      rcases s with ⟨F0, L0, G0⟩
      intro hsub hf
      unfold findGoodFromSeeds at hf
      split_ifs at hf with hc
      · simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        simp only [Bool.and_eq_true, Nat.ble_eq] at hc
        have hmem : (F0, L0, G0) ∈ preSeeds := hsub (F0, L0, G0) List.mem_cons_self
        have hval := List.all_eq_true.mp preSeeds_valid (F0, L0, G0) hmem
        simp only [Bool.and_eq_true] at hval
        have hF0 : ValidFactors F0 := validFactors_of_bool hval.1
        have hpre0 : PreCertifiedBase (valF F0) L0 G0 := checkPreDirect_sound hF0 hval.2
        have hpreF : PreCertifiedBase (valF (st.map Slot.toPair)) L0 G0 :=
          o1PreFromSeedAux_sound o1RaiseOkFull_sound hF hF0 hpre0 hc.1.2
        have hP : ProperSum (valF (st.map Slot.toPair)) =
            ((sigF (st.map Slot.toPair) - valF (st.map Slot.toPair) : ℕ) : ℤ) := by
          rw [properSum_valF hF]; omega
        have hcertF : CertifiedBase (valF (st.map Slot.toPair)) L0 G0 :=
          hpreF.toCertifiedBase (by rw [hP]; exact_mod_cast hc.1.1.2)
        exact ⟨by rw [hLd]; exact hcertF, hfree_sound L0 hle hc.2⟩
      · exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hf
  exact hscan preSeeds (fun _ hx => hx) h

private def checkRange (f : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if hi < lo then true
    else if lo == hi then f lo
    else
      let mid := (lo + hi) / 2
      checkRange f fuel lo mid && checkRange f fuel (mid + 1) hi

private lemma checkRange_sound {f : ℕ → Bool} {fuel lo hi : ℕ}
    (h : checkRange f fuel lo hi = true) :
    ∀ x, lo ≤ x → x ≤ hi → f x = true := by
  induction fuel generalizing lo hi with
  | zero => simp [checkRange] at h
  | succ fuel ih =>
    unfold checkRange at h
    split_ifs at h with h1 h2
    · intro x hx1 hx2; omega
    · intro x hx1 hx2
      have heq : lo = hi := by simpa using h2
      have hx : x = lo := by omega
      subst hx; exact h
    · simp only [Bool.and_eq_true] at h
      intro x hx1 hx2
      by_cases hxm : x ≤ (lo + hi) / 2
      · exact ih h.1 x hx1 hxm
      · exact ih h.2 x (by omega) hx2

private def checkRangeOdd (f : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if Nat.blt hi lo then true
    else if Nat.beq lo hi then f (2 * lo + 1)
    else
      let mid := (lo + hi) / 2
      checkRangeOdd f fuel lo mid && checkRangeOdd f fuel (mid + 1) hi

private lemma checkRangeOdd_sound {f : ℕ → Bool} {fuel lo hi : ℕ}
    (h : checkRangeOdd f fuel lo hi = true) :
    ∀ k, lo ≤ k → k ≤ hi → f (2 * k + 1) = true := by
  induction fuel generalizing lo hi with
  | zero => simp [checkRangeOdd] at h
  | succ fuel ih =>
    unfold checkRangeOdd at h
    split_ifs at h with h1 h2
    · simp only [Nat.blt_eq, decide_eq_true_eq] at h1
      intro k hk1 hk2; omega
    · have heq : lo = hi := Nat.eq_of_beq_eq_true h2
      intro k hk1 hk2
      have hk : k = lo := by omega
      subst hk; exact h
    · simp only [Bool.and_eq_true] at h
      intro k hk1 hk2
      by_cases hkm : k ≤ (lo + hi) / 2
      · exact ih h.1 k hk1 hkm
      · exact ih h.2 k (by omega) hk2

private def checkOddRange (f : ℕ → Bool) (fuel lo hi : ℕ) : Bool :=
  if Nat.blt hi lo || Nat.blt hi 3 then true
  else checkRangeOdd f fuel (lo / 2) ((hi - 1) / 2)

private lemma checkOddRange_sound {f : ℕ → Bool} {fuel lo hi p : ℕ}
    (h : checkOddRange f fuel lo hi = true)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hlo : lo ≤ p) (hhi : p ≤ hi) :
    f p = true := by
  unfold checkOddRange at h
  have hnot : ¬ (Nat.blt hi lo || Nat.blt hi 3) = true := by
    simp only [Bool.or_eq_true, Nat.blt_eq, decide_eq_true_eq]; omega
  rw [if_neg hnot] at h
  have hp_odd : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hp with h2 | hodd <;> omega
  have h2k : 2 * (p / 2) + 1 = p := by omega
  have hk1 : lo / 2 ≤ p / 2 := Nat.div_le_div_right hlo
  have hk2 : p / 2 ≤ (hi - 1) / 2 := by omega
  have hres := checkRangeOdd_sound h (p / 2) hk1 hk2
  rwa [h2k] at hres

private def findMinExp (sb b q : ℕ) : ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ × ℕ)
  | 0, _, _, _ => none
  | fuel + 1, e, qPow, sigQ =>
    if 2 * b * qPow ≤ sb * sigQ then some (e, qPow, sigQ)
    else findMinExp sb b q fuel (e + 1) (qPow * q) (sigQ * q + 1)

private lemma findMinExp_sound {sb b q fuel e qPow sigQ e0 qPow0 sigQ0 : ℕ}
    (_hq : q.Prime) (hqPow : qPow = q ^ e) (hsigQ : sigQ = sigmaPP q e)
    (hprev : ∀ t, 1 ≤ t → t < e → sb * sigmaPP q t < 2 * b * q ^ t)
    (h : findMinExp sb b q fuel e qPow sigQ = some (e0, qPow0, sigQ0)) :
    e ≤ e0 ∧ qPow0 = q ^ e0 ∧ sigQ0 = sigmaPP q e0 ∧
    2 * b * qPow0 ≤ sb * sigQ0 ∧
    ∀ t, 1 ≤ t → t < e0 → sb * sigmaPP q t < 2 * b * q ^ t := by
  induction fuel generalizing e qPow sigQ with
  | zero => simp [findMinExp] at h
  | succ fuel ih =>
    unfold findMinExp at h
    split_ifs at h with hge
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨le_rfl, hqPow, hsigQ, hge, hprev⟩
    · have hprev' : ∀ t, 1 ≤ t → t < e + 1 → sb * sigmaPP q t < 2 * b * q ^ t := by
        intro t ht1 ht2
        by_cases hte : t = e
        · subst hte; rw [← hqPow, ← hsigQ]; omega
        · exact hprev t ht1 (by omega)
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih (by rw [hqPow, pow_succ]) (by rw [hsigQ, sigmaPP]) hprev' h
      exact ⟨by omega, h2, h3, h4, h5⟩

private def checkNonPrimConcrete (F : List (ℕ × ℕ)) (q e : ℕ) : Bool :=
  let qPow := q ^ e
  let sigQ := sigmaPP q e
  (List.range F.length).any fun i =>
    match F[i]? with
    | none => false
    | some (_p, a) =>
      let F2 := if a == 1 then removeIdx F i else setExp F i (a - 1)
      2 * (valF F2 * qPow) ≤ sigF F2 * sigQ

private lemma valF_drop_one_dvd {F : List (ℕ × ℕ)} {i p a : ℕ}
    (hF : ValidFactors F) (hget : F[i]? = some (p, a)) :
    let F2 := if a == 1 then removeIdx F i else setExp F i (a - 1)
    ValidFactors F2 ∧ valF F = valF F2 * p := by
  dsimp only
  obtain ⟨heq, _, hp, ha⟩ := valF_removeIdx hF hget
  split_ifs with ha1
  · have ha_eq : a = 1 := by simpa using ha1
    subst ha_eq
    exact ⟨validFactors_removeIdx i hF, by simpa using heq⟩
  · have ha2 : 2 ≤ a := by simp at ha1; omega
    have hget' : F[i]? = some (p, (a - 1) + 1) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ a)] using hget
    exact ⟨validFactors_setExp (by omega) hF, valF_setExp_pred hget'⟩

private def checkConcreteQ (st : List Slot) (good : Option (ℕ × ℕ)) (q : ℕ) : Bool :=
  if hasSmallFactor q then true
  else
    let b := slotsLd st
    let sb := slotsLn st
    let F := st.map Slot.toPair
    match findMinExp sb b q 40 1 q (q + 1) with
    | none => false
    | some (e, qPow, sigQ) =>
      if sb * sigQ == 2 * b * qPow then true
      else if checkNonPrimConcrete F q e then true
      else
        let m := b * qPow
        let E := sb * sigQ - 2 * m
        let certOk :=
          match good with
          | none => false
          | some (L, _) => L ≤ E && (1 < e || 2 * b ≥ sb + 2)
        if certOk then true
        else
          match lookupWitness (F ++ [(q, e)]) with
          | none => false
          | some ws => checkWitness m E ws

private lemma coprime_valF_of_last_lt {F : List (ℕ × ℕ)} {q : ℕ}
    (hF : ValidFactors F) (hq : q.Prime) (hlt : ∀ pa ∈ F, pa.1 < q) :
    (valF F).Coprime q := by
  induction F with
  | nil => simp [valF]
  | cons pa rest ih =>
    rcases pa with ⟨p, a⟩
    rcases hF with ⟨hp, _, _, hrest⟩
    have hpq : p ≠ q := ne_of_lt (hlt (p, a) List.mem_cons_self)
    have h1 : (p ^ a).Coprime q := ((Nat.coprime_primes hp hq).mpr hpq).pow_left a
    have h2 : (valF rest).Coprime q := ih hrest (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
    simpa [valF] using h1.mul_left h2

private lemma checkConcreteQ_sound {st : List Slot} {exps : List ℕ} {good : Option (ℕ × ℕ)}
    {q e : ℕ}
    (hm : SlotsMatch st exps) (hfix : st.all Slot.fixed = true)
    (hgood : match good with | none => True | some (L, G) => FamilyCertified st L G)
    (hq : q.Prime) (hq3 : 3 ≤ q) (he : 1 ≤ e)
    (hlt : ∀ s ∈ st, s.p < q)
    (hab : (bVal st exps * q ^ e).Abundant)
    (hprim : ∀ d ∈ (bVal st exps * q ^ e).properDivisors, d.Deficient)
    (hchk : checkConcreteQ st good q = true) :
    (bVal st exps * q ^ e).Pseudoperfect := by
  obtain ⟨hb_eq, hsb_eq, hzip_eq⟩ := bVal_bSig_eq_of_all_fixed hm hfix
  have hF : ValidFactors (st.map Slot.toPair) := validFactors_of_slotsMatch hm
  have hb_valF : slotsLd st = valF (st.map Slot.toPair) := by
    rw [← hb_eq, bVal_eq_valF_zip, hzip_eq]
  have hsb_sigF : slotsLn st = sigF (st.map Slot.toPair) := by
    rw [← hsb_eq, bSig_eq_sigF_zip, hzip_eq]
  have hcop : (slotsLd st).Coprime q := by
    rw [hb_valF]
    refine coprime_valF_of_last_lt hF hq (fun pa hpa => ?_)
    rw [List.mem_map] at hpa
    obtain ⟨s, hs, rfl⟩ := hpa
    exact hlt s hs
  have hsig_b : sigma 1 (slotsLd st) = slotsLn st := by
    rw [hb_valF, hsb_sigF, sigF_eq_sigma_one hF]
  have hsig_pow : ∀ t, sigma 1 (slotsLd st * q ^ t) = slotsLn st * sigmaPP q t := by
    intro t
    rw [isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right t), hsig_b,
      sigmaPP_eq_sigma_one_prime_pow hq]
  have hsig_m : sigma 1 (slotsLd st * q ^ e) = slotsLn st * sigmaPP q e := hsig_pow e
  have hab_m : 2 * (slotsLd st * q ^ e) < slotsLn st * sigmaPP q e := by
    have h1 := hab
    rw [hb_eq] at h1
    change slotsLd st * q ^ e < ∑ d ∈ (slotsLd st * q ^ e).properDivisors, d at h1
    have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := slotsLd st * q ^ e)
    rw [← sigma_one_apply, hsig_m] at h2
    omega
  unfold checkConcreteQ at hchk
  have hns : hasSmallFactor q = false := by
    cases hsf : hasSmallFactor q
    · rfl
    · exact absurd hq (not_prime_of_hasSmallFactor hsf)
  rw [hns] at hchk
  simp only [Bool.false_eq_true, ↓reduceIte] at hchk
  cases hmin : findMinExp (slotsLn st) (slotsLd st) q 40 1 q (q + 1) with
  | none => rw [hmin] at hchk; simp at hchk
  | some res =>
    rcases res with ⟨e0, qPow0, sigQ0⟩
    rw [hmin] at hchk
    dsimp only at hchk
    obtain ⟨he0_1, hqPow0, hsigQ0, hge0, hprev0⟩ :=
      findMinExp_sound hq (by simp) (by simp [sigmaPP]) (fun t h1 h2 => by omega) hmin
    have he0_le : e0 ≤ e := by
      by_contra hlt'
      have := hprev0 e he (by omega)
      nlinarith
    have he_eq : e = e0 := by
      by_contra hne
      have hlt' : e0 < e := by omega
      have hmem : slotsLd st * q ^ e0 ∈ (bVal st exps * q ^ e).properDivisors := by
        rw [hb_eq]
        exact Nat.mem_properDivisors.mpr
          ⟨Nat.mul_dvd_mul_left _ (pow_dvd_pow q hlt'.le),
           Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hq.one_lt hlt') (hb_eq ▸ bVal_pos hm)⟩
      have hdef := hprim _ hmem
      change ∑ d ∈ (slotsLd st * q ^ e0).properDivisors, d < slotsLd st * q ^ e0 at hdef
      have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := slotsLd st * q ^ e0)
      rw [← sigma_one_apply, hsig_pow e0] at h2
      rw [hqPow0, hsigQ0] at hge0
      nlinarith
    subst he_eq
    rw [hqPow0, hsigQ0] at hchk hge0
    split_ifs at hchk with heq2 hnonp hcert
    · -- Perfect case impossible since hab_m is strict
      simp only [beq_iff_eq] at heq2
      nlinarith
    · -- Non-primitive case contradicts hprim!
      exfalso
      unfold checkNonPrimConcrete at hnonp
      simp only [List.any_eq_true, List.mem_range] at hnonp
      obtain ⟨i, hi, hcond⟩ := hnonp
      cases hget : (st.map Slot.toPair)[i]? with
      | none => rw [hget] at hcond; simp at hcond
      | some pa =>
        rcases pa with ⟨p, a⟩
        rw [hget] at hcond
        dsimp only at hcond
        obtain ⟨hF2, hveq⟩ := valF_drop_one_dvd hF hget
        set F2 := if a == 1 then removeIdx (st.map Slot.toPair) i else setExp (st.map Slot.toPair) i (a - 1)
        have hF2_cop : (valF F2).Coprime q := by
          have : valF F2 ∣ slotsLd st := ⟨p, by rw [hb_valF, hveq]⟩
          exact hcop.coprime_dvd_left this
        have hsig_F2 : sigma 1 (valF F2 * q ^ e) = sigF F2 * sigmaPP q e := by
          rw [isMultiplicative_sigma.map_mul_of_coprime (hF2_cop.pow_right e),
            sigF_eq_sigma_one hF2, sigmaPP_eq_sigma_one_prime_pow hq]
        have hp_gt : 1 < p := by
          obtain ⟨_, _, hp', _⟩ := valF_removeIdx hF hget
          exact hp'.one_lt
        have hmem : valF F2 * q ^ e ∈ (bVal st exps * q ^ e).properDivisors := by
          rw [hb_eq, hb_valF, hveq]
          refine Nat.mem_properDivisors.mpr ⟨⟨p, by ring⟩, ?_⟩
          have hpos : 0 < valF F2 * q ^ e := Nat.mul_pos (valF_pos hF2) (pow_pos hq.pos e)
          nlinarith
        have hdef := hprim _ hmem
        change ∑ d ∈ (valF F2 * q ^ e).properDivisors, d < valF F2 * q ^ e at hdef
        have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := valF F2 * q ^ e)
        rw [← sigma_one_apply, hsig_F2] at h2
        have hge : 2 * (valF F2 * q ^ e) ≤ sigF F2 * sigmaPP q e := by simpa using hcond
        omega
    · -- Certified by CertifiedBase!
      cases good with
      | none => simp at hcert
      | some lg =>
        rcases lg with ⟨L, G⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcert
        obtain ⟨hEL, hsimp⟩ := hcert
        rw [hb_eq] at hprim ⊢
        have he_succ : e = (e - 1) + 1 := by omega
        rw [he_succ] at hprim ⊢
        refine certified_prime_power_pseudoperfect hgood.1 hq hcop hq3 hprim ?_ ?_
        · unfold Excess
          rw [← he_succ, hsig_m]
          omega
        · intro hj0
          have he1 : e = 1 := by omega
          rcases hsimp with h1 | h2
          · omega
          · have hsp := sigma_split (slotsLd st)
            rw [hsig_b] at hsp
            omega
    · -- Explicit concrete witness!
      cases hws : lookupWitness (st.map Slot.toPair ++ [(q, e)]) with
      | none => rw [hws] at hchk; simp at hchk
      | some ws =>
        rw [hws] at hchk
        rw [hb_eq]
        have hmpos : 0 < slotsLd st * q ^ e := Nat.mul_pos (hb_eq ▸ bVal_pos hm) (pow_pos hq.pos e)
        refine pseudoperfect_of_checkWitness hmpos ?_ hchk
        unfold Excess
        rw [hsig_m]
        omega

private def lastPrime (st : List Slot) : ℕ :=
  match st.getLast? with
  | none => 2
  | some s => s.p

private lemma lastPrime_ge_two {st : List Slot} {exps : List ℕ} (hm : SlotsMatch st exps) :
    2 ≤ lastPrime st := by
  unfold lastPrime
  cases h : st.getLast? with
  | none => simp
  | some s =>
    simp only
    have hmem : s ∈ st := List.mem_of_getLast? h
    obtain ⟨hf, _⟩ := hm
    have aux : ∀ {l : List Slot} {es : List ℕ}, List.Forall₂ SlotMatches l es →
        ∀ t ∈ l, 3 ≤ t.p := by
      intro l es h'; induction h' with
      | nil => intro _ hx; simp at hx
      | cons ht _ ih => intro u hu; simp only [List.mem_cons] at hu; rcases hu with rfl | hu; exact ht.2.1; exact ih u hu
    have := aux hf s hmem; omega

private lemma all_lt_of_lastPrime_lt {st : List Slot} {exps : List ℕ} {q : ℕ}
    (hm : SlotsMatch st exps) (h : lastPrime st < q) : ∀ s ∈ st, s.p < q := by
  obtain ⟨_, hpw⟩ := hm
  unfold lastPrime at h
  cases hlast : st.getLast? with
  | none =>
    have hempty : st = [] := List.getLast?_eq_none_iff.mp hlast
    subst hempty; intro s hs; simp at hs
  | some sLast =>
    rw [hlast] at h
    dsimp only at h
    intro s hs
    have hle : s.p ≤ sLast.p := by
      have aux : ∀ (l : List Slot), List.Pairwise (fun a b => a.p < b.p) l →
          l.getLast? = some sLast → ∀ t ∈ l, t.p ≤ sLast.p := by
        intro l; induction l with
        | nil => intro _ hl; simp at hl
        | cons u rest ih =>
          intro hp hl t ht
          cases rest with
          | nil =>
            simp only [List.getLast?_singleton, Option.some.injEq] at hl
            subst hl
            simp only [List.mem_singleton] at ht; subst ht; exact le_rfl
          | cons v vs =>
            rcases hp with _ | ⟨hlt, hprest⟩
            have hl' : (v :: vs).getLast? = some sLast := by simpa using hl
            simp only [List.mem_cons] at ht
            rcases ht with rfl | ht
            · exact le_of_lt (hlt sLast (List.mem_of_getLast? hl'))
            · exact ih hprest hl' t (List.mem_cons.mpr ht)
      exact aux st hpw hlast s hs
    omega

private def TailMatch (last rem : ℕ) (tail : List (ℕ × ℕ)) : Prop :=
  tail.length = rem ∧ ValidFactors tail ∧ ∀ pa ∈ tail, last < pa.1

private def tailDeadAux (Un Ud last : ℕ) : ℕ → Bool
  | 0 => Un ≤ 2 * Ud
  | r + 1 =>
    let x := nextPrimeAfter last
    tailDeadAux (Un * x) (Ud * (x - 1)) x r

private lemma sigmaPP_anti_prime {q Q : ℕ} (hq : q ≤ Q) :
    ∀ k, sigmaPP Q k * q ^ k ≤ sigmaPP q k * Q ^ k
  | 0 => by simp [sigmaPP]
  | k + 1 => by
    have ih := sigmaPP_anti_prime hq k
    have hpow : q ^ (k + 1) ≤ Q ^ (k + 1) := Nat.pow_le_pow_left hq (k + 1)
    simp only [sigmaPP, pow_succ]
    calc (sigmaPP Q k * Q + 1) * (q ^ k * q)
        = (sigmaPP Q k * q ^ k) * (Q * q) + q ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ (sigmaPP q k * Q ^ k) * (Q * q) + Q ^ (k + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ ih) hpow
      _ = (sigmaPP q k * q + 1) * (Q ^ k * Q) := by rw [pow_succ]; ring

private lemma sigmaPP_ratio_ge {q Q e0 e : ℕ} (hq : 0 < q) (hqQ : q ≤ Q) (he : e0 ≤ e) :
    sigmaPP Q e0 * q ^ e ≤ sigmaPP q e * Q ^ e0 := by
  have h1 : sigmaPP Q e0 * q ^ e0 ≤ sigmaPP q e0 * Q ^ e0 := sigmaPP_anti_prime hqQ e0
  have h2 : sigmaPP q e0 * q ^ e ≤ sigmaPP q e * q ^ e0 := sigmaPP_mono_ratio hq he
  have hpos : 0 < q ^ e0 := pow_pos hq e0
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc sigmaPP Q e0 * q ^ e * q ^ e0
      = (sigmaPP Q e0 * q ^ e0) * q ^ e := by ring
    _ ≤ (sigmaPP q e0 * Q ^ e0) * q ^ e := Nat.mul_le_mul_right _ h1
    _ = (sigmaPP q e0 * q ^ e) * Q ^ e0 := by ring
    _ ≤ (sigmaPP q e * q ^ e0) * Q ^ e0 := Nat.mul_le_mul_right _ h2
    _ = sigmaPP q e * Q ^ e0 * q ^ e0 := by ring

private lemma bernoulli_nat : ∀ (r p : ℕ), r ≤ p → p ^ r * (p - r) ≤ p * (p - 1) ^ r
  | 0, p, _ => by simp
  | r + 1, p, hr => by
    have ih := bernoulli_nat r p (by omega)
    have h1 : p ^ r * (p - r) * (p - 1) ≤ p * (p - 1) ^ (r + 1) := by
      rw [pow_succ, ← mul_assoc]
      exact Nat.mul_le_mul_right (p - 1) ih
    have h2 : p * (p - (r + 1)) ≤ (p - r) * (p - 1) := by
      zify [show r + 1 ≤ p by omega, show r ≤ p by omega, show 1 ≤ p by omega]
      nlinarith
    calc p ^ (r + 1) * (p - (r + 1))
        = p ^ r * (p * (p - (r + 1))) := by rw [pow_succ]; ring
      _ ≤ p ^ r * ((p - r) * (p - 1)) := Nat.mul_le_mul_left _ h2
      _ = p ^ r * (p - r) * (p - 1) := by ring
      _ ≤ p * (p - 1) ^ (r + 1) := h1

private lemma tailDeadAux_strict :
    ∀ (rem Un Ud last : ℕ) (tail : List (ℕ × ℕ)),
      2 ≤ last → 0 < Ud → TailMatch last rem tail →
      tailDeadAux Un Ud last rem = true →
      ∀ (bS bV : ℕ), bS * Ud < Un * bV →
        bS * sigF tail < 2 * (bV * valF tail)
  | 0, Un, Ud, last, tail, _, hUd, htail, hdead, bS, bV, hlt => by
    obtain ⟨hlen, _, _⟩ := htail
    have hnil : tail = [] := List.eq_nil_of_length_eq_zero hlen
    subst hnil
    simp only [tailDeadAux, decide_eq_true_eq] at hdead
    simp only [sigF, valF, mul_one]
    have h1 : bS * Ud < 2 * bV * Ud := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right h1
  | r + 1, Un, Ud, last, tail, hlast, hUd, htail, hdead, bS, bV, hlt => by
    obtain ⟨hlen, hvf, hgt⟩ := htail
    cases tail with
    | nil => simp at hlen
    | cons pa rest =>
      rcases pa with ⟨q, a⟩
      rcases hvf with ⟨hq, ha, hqrest, hvf_rest⟩
      have hlast_q : last < q := hgt (q, a) List.mem_cons_self
      let x := nextPrimeAfter last
      obtain ⟨hlast_x, hcomp_x⟩ := nextPrimeAfter_spec_odd hlast
      have hxq : x ≤ q := by
        by_contra hlt'
        exact hcomp_x q hlast_q (by omega) hq
      have hx3 : 3 ≤ x := by omega
      have hq3 : 3 ≤ q := by omega
      have hsig_q : sigmaPP q a * (q - 1) < q * q ^ a := sigmaPP_lt_limit hq.one_lt a
      have hqx : q * (x - 1) ≤ x * (q - 1) := by
        zify [show 1 ≤ x by omega, show 1 ≤ q by omega]
        nlinarith
      have hstep : (bS * sigmaPP q a) * (Ud * (x - 1)) < (Un * x) * (bV * q ^ a) := by
        apply Nat.lt_of_mul_lt_mul_right (a := q - 1)
        have hpos1 : 0 < q * q ^ a * (x - 1) :=
          Nat.mul_pos (Nat.mul_pos hq.pos (pow_pos hq.pos a)) (by omega)
        calc (bS * sigmaPP q a) * (Ud * (x - 1)) * (q - 1)
            = (bS * Ud) * (sigmaPP q a * (q - 1)) * (x - 1) := by ring
          _ ≤ (bS * Ud) * (q * q ^ a) * (x - 1) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (le_of_lt hsig_q))
          _ = (bS * Ud) * (q * q ^ a * (x - 1)) := by ring
          _ < (Un * bV) * (q * q ^ a * (x - 1)) := Nat.mul_lt_mul_of_pos_right hlt hpos1
          _ = (Un * bV) * (q * (x - 1)) * q ^ a := by ring
          _ ≤ (Un * bV) * (x * (q - 1)) * q ^ a :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hqx)
          _ = (Un * x) * (bV * q ^ a) * (q - 1) := by ring
      have htail' : TailMatch x r rest := by
        refine ⟨by simpa using hlen, hvf_rest, fun pb hpb => ?_⟩
        exact lt_of_le_of_lt hxq (hqrest pb hpb)
      have hres := tailDeadAux_strict r (Un * x) (Ud * (x - 1)) x rest (by omega)
        (Nat.mul_pos hUd (by omega)) htail' hdead (bS * sigmaPP q a) (bV * q ^ a) hstep
      simpa [sigF, valF, mul_assoc] using hres

private lemma tailDeadAux_sound {Un Ud last rem : ℕ} {tail : List (ℕ × ℕ)}
    (hlast : 2 ≤ last) (hrem : 1 ≤ rem) (hUd : 0 < Ud)
    (htail : TailMatch last rem tail) (hdead : tailDeadAux Un Ud last rem = true)
    {bS bV : ℕ} (hbV : 0 < bV) (hbound : bS * Ud ≤ Un * bV) :
    bS * sigF tail < 2 * (bV * valF tail) := by
  by_cases hbS : bS = 0
  · subst hbS
    have hv := valF_pos htail.2.1
    simp only [zero_mul]
    exact Nat.mul_pos (by omega) (Nat.mul_pos hbV hv)
  · have hbS_pos : 0 < bS := Nat.pos_of_ne_zero hbS
    cases rem with
    | zero => omega
    | succ r =>
      obtain ⟨hlen, hvf, hgt⟩ := htail
      cases tail with
      | nil => simp at hlen
      | cons pa rest =>
        rcases pa with ⟨q, a⟩
        rcases hvf with ⟨hq, ha, hqrest, hvf_rest⟩
        have hlast_q : last < q := hgt (q, a) List.mem_cons_self
        let x := nextPrimeAfter last
        obtain ⟨hlast_x, hcomp_x⟩ := nextPrimeAfter_spec_odd hlast
        have hxq : x ≤ q := by
          by_contra hlt'
          exact hcomp_x q hlast_q (by omega) hq
        have hx3 : 3 ≤ x := by omega
        have hq3 : 3 ≤ q := by omega
        have hsig_q : sigmaPP q a * (q - 1) < q * q ^ a := sigmaPP_lt_limit hq.one_lt a
        have hqx : q * (x - 1) ≤ x * (q - 1) := by
          zify [show 1 ≤ x by omega, show 1 ≤ q by omega]
          nlinarith
        have hstep : (bS * sigmaPP q a) * (Ud * (x - 1)) < (Un * x) * (bV * q ^ a) := by
          apply Nat.lt_of_mul_lt_mul_right (a := q - 1)
          have hpos_bUd : 0 < bS * Ud := Nat.mul_pos hbS_pos hUd
          have hpos_x1 : 0 < x - 1 := by omega
          calc (bS * sigmaPP q a) * (Ud * (x - 1)) * (q - 1)
              = (bS * Ud) * (sigmaPP q a * (q - 1)) * (x - 1) := by ring
            _ < (bS * Ud) * (q * q ^ a) * (x - 1) :=
                Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hsig_q hpos_bUd) hpos_x1
            _ ≤ (Un * bV) * (q * q ^ a) * (x - 1) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hbound)
            _ = (Un * bV) * (q * (x - 1)) * q ^ a := by ring
            _ ≤ (Un * bV) * (x * (q - 1)) * q ^ a :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hqx)
            _ = (Un * x) * (bV * q ^ a) * (q - 1) := by ring
        have htail' : TailMatch x r rest := by
          refine ⟨by simpa using hlen, hvf_rest, fun pb hpb => ?_⟩
          exact lt_of_le_of_lt hxq (hqrest pb hpb)
        have hres := tailDeadAux_strict r (Un * x) (Ud * (x - 1)) x rest (by omega)
          (Nat.mul_pos hUd (by omega)) htail' hdead (bS * sigmaPP q a) (bV * q ^ a) hstep
        simpa [sigF, valF, mul_assoc] using hres

private lemma sigF_tail_upper {p : ℕ} (hp : 2 ≤ p) :
    ∀ (tail : List (ℕ × ℕ)), ValidFactors tail → (∀ pa ∈ tail, p ≤ pa.1) →
      sigF tail * (p - 1) ^ tail.length ≤ p ^ tail.length * valF tail
  | [], _, _ => by simp [sigF, valF]
  | (q, a) :: rest, hvf, hge => by
    rcases hvf with ⟨hq, ha, _, hvf_rest⟩
    have hpq : p ≤ q := hge (q, a) List.mem_cons_self
    have ih := sigF_tail_upper hp rest hvf_rest (fun x hx => hge x (List.mem_cons_of_mem _ hx))
    have hsig : sigmaPP q a * (q - 1) ≤ q * q ^ a := le_of_lt (sigmaPP_lt_limit hq.one_lt a)
    have hqp : q * (p - 1) ≤ p * (q - 1) := by
      zify [show 1 ≤ p by omega, show 1 ≤ q by omega]
      nlinarith
    have h1 : sigmaPP q a * (p - 1) ≤ p * q ^ a := by
      have hmul : sigmaPP q a * (p - 1) * (q - 1) ≤ p * q ^ a * (q - 1) :=
        calc sigmaPP q a * (p - 1) * (q - 1)
            = (sigmaPP q a * (q - 1)) * (p - 1) := by ring
          _ ≤ (q * q ^ a) * (p - 1) := Nat.mul_le_mul_right _ hsig
          _ = (q * (p - 1)) * q ^ a := by ring
          _ ≤ (p * (q - 1)) * q ^ a := Nat.mul_le_mul_right _ hqp
          _ = p * q ^ a * (q - 1) := by ring
      exact Nat.le_of_mul_le_mul_right hmul (by omega)
    simp only [sigF, valF, List.length_cons, pow_succ]
    calc (sigmaPP q a * sigF rest) * ((p - 1) ^ rest.length * (p - 1))
        = (sigmaPP q a * (p - 1)) * (sigF rest * (p - 1) ^ rest.length) := by ring
      _ ≤ (p * q ^ a) * (p ^ rest.length * valF rest) := Nat.mul_le_mul h1 ih
      _ = p ^ rest.length * p * (q ^ a * valF rest) := by ring

private lemma tail_head_le_pMax {Un Ud rem p a : ℕ} {rest : List (ℕ × ℕ)} {bS bV : ℕ}
    (hrem : 1 ≤ rem) (hUn : 1 ≤ Un) (hUd : 0 < Ud) (hU : Un < 2 * Ud)
    (hlen : ((p, a) :: rest).length = rem) (hvf : ValidFactors ((p, a) :: rest))
    (hp3 : 3 ≤ p) (_hbV : 0 < bV) (hbound : bS * Ud ≤ Un * bV)
    (hab : 2 * (bV * valF ((p, a) :: rest)) < bS * sigF ((p, a) :: rest)) :
    p ≤ (2 * Ud * rem - 1) / (2 * Ud - Un) := by
  have hden : 0 < 2 * Ud - Un := by omega
  rw [Nat.le_div_iff_mul_le hden]
  by_cases hpr : p < rem
  · have h1 : (2 * Ud - Un) * p ≤ (2 * Ud - 1) * rem :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (2 * Ud - 1) * rem ≤ 2 * Ud * rem - 1 := by
      zify [show 1 ≤ 2 * Ud by omega, show 1 ≤ 2 * Ud * rem by nlinarith]
      nlinarith
    rw [mul_comm]
    omega
  · have hrp : rem ≤ p := by omega
    have hge : ∀ pa ∈ (p, a) :: rest, p ≤ pa.1 := by
      intro pa hpa
      simp only [List.mem_cons] at hpa
      rcases hpa with rfl | hpa
      · exact le_rfl
      · exact le_of_lt (hvf.2.2.1 pa hpa)
    have hsig := sigF_tail_upper (by omega : 2 ≤ p) ((p, a) :: rest) hvf hge
    rw [hlen] at hsig
    have hvpos : 0 < valF ((p, a) :: rest) := valF_pos hvf
    have hpm1 : 0 < (p - 1) ^ rem := pow_pos (by omega) rem
    have h2 : 2 * Ud * (p - 1) ^ rem < Un * p ^ rem := by
      apply Nat.lt_of_mul_lt_mul_right (a := bV * valF ((p, a) :: rest))
      calc 2 * Ud * (p - 1) ^ rem * (bV * valF ((p, a) :: rest))
          = 2 * (bV * valF ((p, a) :: rest)) * (Ud * (p - 1) ^ rem) := by ring
        _ < (bS * sigF ((p, a) :: rest)) * (Ud * (p - 1) ^ rem) :=
            Nat.mul_lt_mul_of_pos_right hab (Nat.mul_pos hUd hpm1)
        _ = (bS * Ud) * (sigF ((p, a) :: rest) * (p - 1) ^ rem) := by ring
        _ ≤ (Un * bV) * (p ^ rem * valF ((p, a) :: rest)) := Nat.mul_le_mul hbound hsig
        _ = Un * p ^ rem * (bV * valF ((p, a) :: rest)) := by ring
    have hbern := bernoulli_nat rem p hrp
    have h3 : 2 * Ud * (p - rem) < Un * p := by
      apply Nat.lt_of_mul_lt_mul_right (a := p ^ rem)
      calc 2 * Ud * (p - rem) * p ^ rem
          = 2 * Ud * (p ^ rem * (p - rem)) := by ring
        _ ≤ 2 * Ud * (p * (p - 1) ^ rem) := Nat.mul_le_mul_left _ hbern
        _ = (2 * Ud * (p - 1) ^ rem) * p := by ring
        _ < (Un * p ^ rem) * p := Nat.mul_lt_mul_of_pos_right h2 (by omega)
        _ = Un * p * p ^ rem := by ring
    zify [show Un ≤ 2 * Ud by omega, show rem ≤ p by omega, show 1 ≤ 2 * Ud * rem by nlinarith] at h3 ⊢
    nlinarith

private lemma slotsLd_append_mkSlot (st : List Slot) (p : ℕ) :
    slotsLd (st ++ [mkSlot p]) = slotsLd st * p := by
  simp [slotsLd, List.foldl_append, mkSlot]

private lemma familyCertified_append_prime {st : List Slot} {exps : List ℕ} {p L G : ℕ}
    (hm : SlotsMatch st exps) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hlt : ∀ s ∈ st, s.p < p)
    (hfc : FamilyCertified st L G)
    (hwide : p * G + 2 * L ≤ slotsLn st - slotsLd st + 1)
    (hover : slotsLd st + 2 * L ≤ (p + 1) * (slotsLn st - slotsLd st) + 1) :
    FamilyCertified (st ++ [mkSlot p]) L G := by
  have hF : ValidFactors (st.map Slot.toPair) := validFactors_of_slotsMatch hm
  have hLd_val : slotsLd st = valF (st.map Slot.toPair) := by
    apply slotsLd_eq_valF
    obtain ⟨hf, _⟩ := hm
    have aux : ∀ {l : List Slot} {es : List ℕ}, List.Forall₂ SlotMatches l es →
        ∀ s ∈ l, s.pPow = s.p ^ s.lo := by
      intro l es h'; induction h' with
      | nil => intro _ hx; simp at hx
      | cons hs _ ih => intro t ht; simp only [List.mem_cons] at ht; rcases ht with rfl | ht; exact hs.2.2.2.1; exact ih t ht
    exact aux hf
  have hLn_sig : slotsLn st = sigF (st.map Slot.toPair) := by
    apply slotsLn_eq_sigF
    obtain ⟨hf, _⟩ := hm
    have aux : ∀ {l : List Slot} {es : List ℕ}, List.Forall₂ SlotMatches l es →
        ∀ s ∈ l, s.sigPow = sigmaPP s.p s.lo := by
      intro l es h'; induction h' with
      | nil => intro _ hx; simp at hx
      | cons hs _ ih => intro t ht; simp only [List.mem_cons] at ht; rcases ht with rfl | ht; exact hs.2.2.2.2.1; exact ih t ht
    exact aux hf
  have hsig_b : sigma 1 (slotsLd st) = slotsLn st := by
    rw [hLd_val, hLn_sig, sigF_eq_sigma_one hF]
  have hcop : (slotsLd st).Coprime p := by
    rw [hLd_val]
    refine coprime_valF_of_last_lt hF hp (fun pa hpa => ?_)
    rw [List.mem_map] at hpa
    obtain ⟨s, hs, rfl⟩ := hpa
    exact hlt s hs
  have hPeq : ProperSum (slotsLd st) = (slotsLn st : ℤ) - (slotsLd st : ℤ) := by
    have hsp := sigma_split (slotsLd st)
    rw [hsig_b] at hsp
    linarith
  have hP_nonneg : slotsLd st ≤ slotsLn st := by
    have := properSum_nonneg (slotsLd st)
    omega
  have hPnat : ProperSum (slotsLd st) = ((slotsLn st - slotsLd st : ℕ) : ℤ) := by
    rw [hPeq, Nat.cast_sub hP_nonneg]
  have hwideZ : (p : ℤ) * (G : ℤ) ≤ ProperSum (slotsLd st) - 2 * (L : ℤ) + 1 := by
    rw [hPnat]; omega
  have hoverZ : (slotsLd st : ℤ) + 2 * (L : ℤ) ≤
      ProperSum (slotsLd st) + (p : ℤ) * ProperSum (slotsLd st) + 1 := by
    rw [hPnat]
    have h1 : ((slotsLd st + 2 * L : ℕ) : ℤ) ≤ (((p + 1) * (slotsLn st - slotsLd st) + 1 : ℕ) : ℤ) := by
      exact_mod_cast hover
    push_cast at h1
    linarith
  have hcert' : CertifiedBase (slotsLd st * p) L G :=
    certifiedBase_mul_new_prime hfc.1 hp hcop hwideZ hoverZ
  unfold FamilyCertified
  rw [slotsLd_append_mkSlot]
  refine ⟨hcert', fun t ht htfree => ?_⟩
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | rfl
  · have ht_prime : t.p.Prime := by
      obtain ⟨hf, _⟩ := hm
      have aux : ∀ {l : List Slot} {es : List ℕ}, List.Forall₂ SlotMatches l es → ∀ u ∈ l, u.p.Prime := by
        intro l es h'; induction h' with
        | nil => intro _ hx; simp at hx
        | cons hu _ ih => intro v hv; simp only [List.mem_cons] at hv; rcases hv with rfl | hv; exact hu.1; exact ih v hv
      exact aux hf t ht
    exact raiseOk_mul_other_prime (by have := hfc.1.b_gt_one; omega) ht_prime hp (ne_of_lt (hlt t ht)) (hfc.2 t ht htfree)
  · -- New slot mkSlot p: RaiseOk (slotsLd st * p) p L follows directly from CertifiedBase (slotsLd st) L G!
    have hlarge := hfc.1.large
    have hG1 : 1 ≤ G := hfc.1.G_pos
    have hL1 : 1 ≤ L := hfc.1.L_pos
    have hPge6 : 6 * (L : ℤ) + 48 ≤ ProperSum (slotsLd st) := by
      have h1 : (3 : ℤ) ≤ 2 * (G : ℤ) + 1 := by omega
      have h2 : 2 * (L : ℤ) + 16 ≤ 2 * (L : ℤ) + 8 * (G : ℤ) + 8 := by omega
      have h3 : (3 : ℤ) * (2 * (L : ℤ) + 16) ≤ (2 * (G : ℤ) + 1) * (2 * (L : ℤ) + 8 * (G : ℤ) + 8) :=
        mul_le_mul h1 h2 (by omega) (by omega)
      linarith
    have hPbp : ProperSum (slotsLd st * p) =
        (slotsLd st : ℤ) + ProperSum (slotsLd st) + (p : ℤ) * ProperSum (slotsLd st) :=
      properSum_mul_prime_coprime hp hcop
    refine ⟨slotsLd st, 1, L + p - 1, by simp [mkSlot], le_rfl, hcop, by have := hfc.1.b_gt_one; omega, ?_, ?_, ?_⟩
    · simp only [mkSlot]
      have : (p : ℤ) * (6 * (L : ℤ) + 48) ≤ (p : ℤ) * ProperSum (slotsLd st) :=
        mul_le_mul_of_nonneg_left hPge6 (Nat.cast_nonneg p)
      nlinarith
    · simp only [mkSlot]
      have hsub : 1 ≤ L + p := by omega
      push_cast [Nat.cast_sub hsub]
      have : (p : ℤ) * (6 * (L : ℤ) + 48) ≤ (p : ℤ) * ProperSum (slotsLd st) :=
        mul_le_mul_of_nonneg_left hPge6 (Nat.cast_nonneg p)
      have hb0 : (0 : ℤ) ≤ slotsLd st := Nat.cast_nonneg _
      have hP0 : 0 ≤ ProperSum (slotsLd st) := properSum_nonneg _
      nlinarith [hPbp]
    · intro r hr
      simp only [mkSlot] at hr ⊢
      let k := (r + p - L % p) % p
      have hk_lt : k < p := Nat.mod_lt _ hp.pos
      refine ⟨L + k, ?_, by omega, ?_⟩
      · dsimp [k]
        have hdiv : L = p * (L / p) + L % p := (Nat.div_add_mod L p).symm
        have hlm : L % p < p := Nat.mod_lt L hp.pos
        rw [Nat.add_mod_mod, show L + (r + p - L % p) = p * (L / p + 1) + r by rw [Nat.mul_add, mul_one]; omega,
          Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      · have hmid : Represented (slotsLd st) ((L + k : ℕ) : ℤ) := by
          apply hfc.1.middle
          · push_cast; omega
          · have : (p : ℤ) * (1 : ℤ) ≤ (p : ℤ) * (G : ℤ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hG1) (Nat.cast_nonneg p)
            push_cast
            linarith
        obtain ⟨s, hs, hsum⟩ := hmid
        exact ⟨s, hs.trans Nat.properDivisors_subset_divisors, hsum⟩

private def findMinExpStrict (Un Ud x : ℕ) : ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ × ℕ)
  | 0, _, _, _ => none
  | fuel + 1, e, xPow, sigX =>
    if 2 * Ud * xPow < Un * sigX then some (e, xPow, sigX)
    else findMinExpStrict Un Ud x fuel (e + 1) (xPow * x) (sigX * x + 1)

private lemma findMinExpStrict_sound {Un Ud x fuel e xPow sigX e0 xPow0 sigX0 : ℕ}
    (hxPow : xPow = x ^ e) (hsigX : sigX = sigmaPP x e)
    (hprev : ∀ t, 1 ≤ t → t < e → Un * sigmaPP x t ≤ 2 * Ud * x ^ t)
    (h : findMinExpStrict Un Ud x fuel e xPow sigX = some (e0, xPow0, sigX0)) :
    e ≤ e0 ∧ xPow0 = x ^ e0 ∧ sigX0 = sigmaPP x e0 ∧
    ∀ t, 1 ≤ t → t < e0 → Un * sigmaPP x t ≤ 2 * Ud * x ^ t := by
  induction fuel generalizing e xPow sigX with
  | zero => simp [findMinExpStrict] at h
  | succ fuel ih =>
    unfold findMinExpStrict at h
    split_ifs at h with hlt
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨le_rfl, hxPow, hsigX, hprev⟩
    · have hprev' : ∀ t, 1 ≤ t → t < e + 1 → Un * sigmaPP x t ≤ 2 * Ud * x ^ t := by
        intro t ht1 ht2
        by_cases hte : t = e
        · subst hte; rw [← hxPow, ← hsigX]; omega
        · exact hprev t ht1 (by omega)
      obtain ⟨h1, h2, h3, h4⟩ := ih (by rw [hxPow, pow_succ]) (by rw [hsigX, sigmaPP]) hprev' h
      exact ⟨by omega, h2, h3, h4⟩

private lemma exp_ge_of_findMinExpStrict {st : List Slot} {exps : List ℕ}
    {x q e fuel e0 xPow0 sigX0 : ℕ}
    (hm : SlotsMatch st exps) (hx0 : 0 < x) (hxq : x ≤ q) (he : 1 ≤ e)
    (hab : 2 * (bVal st exps * q ^ e) < bSig st exps * sigmaPP q e)
    (hfind : findMinExpStrict (slotsUn st) (slotsUd st) x fuel 1 x (x + 1) = some (e0, xPow0, sigX0)) :
    e0 ≤ e := by
  obtain ⟨_, _, _, hprev⟩ := findMinExpStrict_sound (by simp) (by simp [sigmaPP])
    (fun t h1 h2 => by omega) hfind
  by_contra hlt
  have hle : slotsUn st * sigmaPP x e ≤ 2 * slotsUd st * x ^ e := hprev e he (by omega)
  obtain ⟨_, hUd0, _, _, hU⟩ := slots_bounds hm
  have hanti : sigmaPP q e * x ^ e ≤ sigmaPP x e * q ^ e := sigmaPP_anti_prime hxq e
  have hpos : 0 < slotsUd st * x ^ e := Nat.mul_pos hUd0 (pow_pos hx0 e)
  have h1 : 2 * (bVal st exps * q ^ e) * (slotsUd st * x ^ e) <
      (bSig st exps * sigmaPP q e) * (slotsUd st * x ^ e) :=
    Nat.mul_lt_mul_of_pos_right hab hpos
  have h2 : (bSig st exps * sigmaPP q e) * (slotsUd st * x ^ e) ≤
      (slotsUn st * bVal st exps) * (sigmaPP x e * q ^ e) := by
    calc (bSig st exps * sigmaPP q e) * (slotsUd st * x ^ e)
        = (bSig st exps * slotsUd st) * (sigmaPP q e * x ^ e) := by ring
      _ ≤ (slotsUn st * bVal st exps) * (sigmaPP x e * q ^ e) := Nat.mul_le_mul hU hanti
  have h3 : (slotsUn st * bVal st exps) * (sigmaPP x e * q ^ e) ≤
      2 * (bVal st exps * q ^ e) * (slotsUd st * x ^ e) := by
    calc (slotsUn st * bVal st exps) * (sigmaPP x e * q ^ e)
        = (slotsUn st * sigmaPP x e) * (bVal st exps * q ^ e) := by ring
      _ ≤ (2 * slotsUd st * x ^ e) * (bVal st exps * q ^ e) := Nat.mul_le_mul_right _ hle
      _ = 2 * (bVal st exps * q ^ e) * (slotsUd st * x ^ e) := by ring
  omega

private def dropSlotLnLd : List Slot → ℕ → ℕ × ℕ
  | [], _ => (1, 1)
  | s :: rest, 0 => (sigmaPP s.p (s.lo - 1) * slotsLn rest, s.p ^ (s.lo - 1) * slotsLd rest)
  | s :: rest, i + 1 =>
    let (ln, ld) := dropSlotLnLd rest i
    (s.sigPow * ln, s.pPow * ld)

private def checkNonPrimFamilyAux (st : List Slot) (Qpow sigQ : ℕ) : ℕ → Bool
  | 0 => false
  | k + 1 =>
    let (ln2, ld2) := dropSlotLnLd st k
    if 2 * ld2 * Qpow ≤ ln2 * sigQ then true
    else checkNonPrimFamilyAux st Qpow sigQ k

private def checkNonPrimFamily (st : List Slot) (Qpow sigQ : ℕ) : Bool :=
  checkNonPrimFamilyAux st Qpow sigQ st.length

private lemma dropSlot_witness {st : List Slot} {exps : List ℕ} {k : ℕ}
    (hm : SlotsMatch st exps) (hk : k < st.length) :
    ∃ b' p', 3 ≤ p' ∧ 0 < b' ∧ bVal st exps = b' * p' ∧
      0 < (dropSlotLnLd st k).2 ∧
      (dropSlotLnLd st k).1 * b' ≤ sigma 1 b' * (dropSlotLnLd st k).2 := by
  obtain ⟨hf, hpw⟩ := hm
  induction hf generalizing k with
  | nil => simp at hk
  | @cons s a rest arest hs hrest ih =>
    rcases hpw with _ | ⟨hlt, hprest⟩
    obtain ⟨hp, hp3, hlo1, hpPow, hsigPow, hcmp⟩ := hs
    have hloa : s.lo ≤ a := by split_ifs at hcmp <;> omega
    have hrest_match : SlotsMatch rest arest := ⟨hrest, hprest⟩
    have hcop_s : s.p.Coprime (bVal rest arest) := by
      rw [bVal_eq_valF_zip]
      refine coprime_valF_of_lt hp (validFactors_zipWith_of_slotsMatch hrest_match) (fun pa hpa => ?_)
      obtain ⟨t, ht, _, _, rfl⟩ := mem_zipWith_fst hpa
      exact hlt t ht
    cases k with
    | zero =>
      refine ⟨s.p ^ (a - 1) * bVal rest arest, s.p, hp3,
        Nat.mul_pos (pow_pos hp.pos _) (bVal_pos hrest_match), ?_, ?_, ?_⟩
      · simp only [bVal, List.zipWith_cons_cons, List.prod_cons]
        have ha1 : (a - 1) + 1 = a := by omega
        calc s.p ^ a * bVal rest arest
            = s.p ^ ((a - 1) + 1) * bVal rest arest := by rw [ha1]
          _ = s.p ^ (a - 1) * bVal rest arest * s.p := by rw [pow_succ]; ring
      · simp only [dropSlotLnLd]
        exact Nat.mul_pos (pow_pos hp.pos _) (slots_bounds hrest_match).1
      · simp only [dropSlotLnLd]
        have hsig_drop : sigma 1 (s.p ^ (a - 1) * bVal rest arest) =
            sigmaPP s.p (a - 1) * bSig rest arest := by
          rw [isMultiplicative_sigma.map_mul_of_coprime (hcop_s.pow_left (a - 1)),
            sigmaPP_eq_sigma_one_prime_pow hp, bSig_eq_sigma_one_bVal hrest_match]
        rw [hsig_drop]
        have hL1 : sigmaPP s.p (s.lo - 1) * s.p ^ (a - 1) ≤ sigmaPP s.p (a - 1) * s.p ^ (s.lo - 1) :=
          sigmaPP_mono_ratio hp.pos (by omega)
        have hL2 := (slots_bounds hrest_match).2.2.2.1
        calc sigmaPP s.p (s.lo - 1) * slotsLn rest * (s.p ^ (a - 1) * bVal rest arest)
            = (sigmaPP s.p (s.lo - 1) * s.p ^ (a - 1)) * (slotsLn rest * bVal rest arest) := by ring
          _ ≤ (sigmaPP s.p (a - 1) * s.p ^ (s.lo - 1)) * (bSig rest arest * slotsLd rest) :=
              Nat.mul_le_mul hL1 hL2
          _ = sigmaPP s.p (a - 1) * bSig rest arest * (s.p ^ (s.lo - 1) * slotsLd rest) := by ring
    | succ k =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      obtain ⟨b', p', hp'3, hb'pos, hb'eq, hld2_pos, hL2⟩ := ih hk hprest
      have hcop_b' : (s.p ^ a).Coprime b' := by
        have hdvd : b' ∣ bVal rest arest := ⟨p', hb'eq⟩
        exact (hcop_s.coprime_dvd_right hdvd).pow_left a
      refine ⟨s.p ^ a * b', p', hp'3, Nat.mul_pos (pow_pos hp.pos _) hb'pos, ?_, ?_, ?_⟩
      · simp only [bVal, List.zipWith_cons_cons, List.prod_cons]
        change s.p ^ a * bVal rest arest = s.p ^ a * b' * p'
        rw [hb'eq]; ring
      · simp only [dropSlotLnLd]
        exact Nat.mul_pos (by rw [hpPow]; exact pow_pos hp.pos _) hld2_pos
      · simp only [dropSlotLnLd]
        have hsig_drop : sigma 1 (s.p ^ a * b') = sigmaPP s.p a * sigma 1 b' := by
          rw [isMultiplicative_sigma.map_mul_of_coprime hcop_b', sigmaPP_eq_sigma_one_prime_pow hp]
        rw [hsig_drop]
        have hL1 : s.sigPow * s.p ^ a ≤ sigmaPP s.p a * s.pPow := by
          rw [hpPow, hsigPow]; exact sigmaPP_mono_ratio hp.pos hloa
        calc s.sigPow * (dropSlotLnLd rest k).1 * (s.p ^ a * b')
            = (s.sigPow * s.p ^ a) * ((dropSlotLnLd rest k).1 * b') := by ring
          _ ≤ (sigmaPP s.p a * s.pPow) * (sigma 1 b' * (dropSlotLnLd rest k).2) :=
              Nat.mul_le_mul hL1 hL2
          _ = sigmaPP s.p a * sigma 1 b' * (s.pPow * (dropSlotLnLd rest k).2) := by ring

private lemma dropSlot_nonPrim_false {st : List Slot} {exps : List ℕ} {k q Q e0 e : ℕ}
    (hm : SlotsMatch st exps) (hk : k < st.length) (hq : q.Prime) (hqQ : q ≤ Q) (he : e0 ≤ e)
    (hlt : ∀ s ∈ st, s.p < q)
    (hprim : ∀ d ∈ (bVal st exps * q ^ e).properDivisors, d.Deficient)
    (hle : 2 * (dropSlotLnLd st k).2 * Q ^ e0 ≤ (dropSlotLnLd st k).1 * sigmaPP Q e0) : False := by
  obtain ⟨b', p', hp'3, hb'pos, hb'eq, hld2_pos, hL2⟩ := dropSlot_witness hm hk
  have hcop_b : (bVal st exps).Coprime q := by
    rw [bVal_eq_valF_zip]
    refine coprime_valF_of_last_lt (validFactors_zipWith_of_slotsMatch hm) hq (fun pa hpa => ?_)
    obtain ⟨s, hs, _, _, rfl⟩ := mem_zipWith_fst hpa
    exact hlt s hs
  have hcop_b' : b'.Coprime q := hcop_b.coprime_dvd_left ⟨p', hb'eq⟩
  have hmem : b' * q ^ e ∈ (bVal st exps * q ^ e).properDivisors := by
    rw [hb'eq]
    refine Nat.mem_properDivisors.mpr ⟨⟨p', by ring⟩, ?_⟩
    have hpos : 0 < b' * q ^ e := Nat.mul_pos hb'pos (pow_pos hq.pos e)
    nlinarith
  have hdef := hprim _ hmem
  change ∑ d ∈ (b' * q ^ e).properDivisors, d < b' * q ^ e at hdef
  have hsum := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := b' * q ^ e)
  rw [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime (hcop_b'.pow_right e),
    ← sigmaPP_eq_sigma_one_prime_pow hq] at hsum
  have hlt_sig : sigma 1 b' * sigmaPP q e < 2 * (b' * q ^ e) := by omega
  have hrat : sigmaPP Q e0 * q ^ e ≤ sigmaPP q e * Q ^ e0 := sigmaPP_ratio_ge hq.pos hqQ he
  have hQpos : 0 < Q ^ e0 := pow_pos (by have := hq.pos; omega) e0
  have hmul_pos : 0 < (dropSlotLnLd st k).2 * Q ^ e0 := Nat.mul_pos hld2_pos hQpos
  have h1 : 2 * (b' * q ^ e) * ((dropSlotLnLd st k).2 * Q ^ e0) ≤
      (sigma 1 b' * sigmaPP q e) * ((dropSlotLnLd st k).2 * Q ^ e0) := by
    calc 2 * (b' * q ^ e) * ((dropSlotLnLd st k).2 * Q ^ e0)
        = (2 * (dropSlotLnLd st k).2 * Q ^ e0) * (b' * q ^ e) := by ring
      _ ≤ ((dropSlotLnLd st k).1 * sigmaPP Q e0) * (b' * q ^ e) := Nat.mul_le_mul_right _ hle
      _ = ((dropSlotLnLd st k).1 * b') * (sigmaPP Q e0 * q ^ e) := by ring
      _ ≤ (sigma 1 b' * (dropSlotLnLd st k).2) * (sigmaPP q e * Q ^ e0) := Nat.mul_le_mul hL2 hrat
      _ = (sigma 1 b' * sigmaPP q e) * ((dropSlotLnLd st k).2 * Q ^ e0) := by ring
  have h2 := Nat.mul_lt_mul_of_pos_right hlt_sig hmul_pos
  omega

private def slotsMaxSig : List Slot → ℕ
  | [] => 1
  | s :: rest =>
    let m := slotsMaxSig rest
    if Nat.ble s.sigPow m then m else s.sigPow

private lemma slotsMaxSig_append_mkSlot (st : List Slot) (p : ℕ) :
    slotsMaxSig (st ++ [mkSlot p]) =
      if Nat.ble (slotsMaxSig st) (p + 1) then p + 1 else slotsMaxSig st := by
  induction st with
  | nil =>
    simp only [List.nil_append, slotsMaxSig, mkSlot, Nat.ble_eq]
    split_ifs <;> omega
  | cons s rest ih =>
    simp only [List.cons_append, slotsMaxSig, ih]
    split_ifs <;> simp only [Nat.ble_eq] at * <;> omega

private lemma slotsMaxSig_fixIdx (st : List Slot) (i : ℕ) :
    slotsMaxSig (fixIdx st i) = slotsMaxSig st := by
  induction st generalizing i with
  | nil => simp [fixIdx, slotsMaxSig]
  | cons s rest ih =>
    cases i with
    | zero => simp [fixIdx, slotsMaxSig, Slot.fix]
    | succ i => simp [fixIdx, slotsMaxSig, ih]

private lemma exists_slot_of_slotsMaxSig_gt_one {st : List Slot} (h : 1 < slotsMaxSig st) :
    ∃ k < st.length, ∃ s, st[k]? = some s ∧ s.sigPow = slotsMaxSig st := by
  induction st with
  | nil => simp [slotsMaxSig] at h
  | cons s rest ih =>
    unfold slotsMaxSig at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ with hle
    · obtain ⟨k, hk, t, hget, hsig⟩ := ih h
      exact ⟨k + 1, Nat.succ_lt_succ hk, t, hget, hsig⟩
    · exact ⟨0, Nat.zero_lt_succ _, s, rfl, rfl⟩

private lemma dropSlotLnLd_mul_sigPow {st : List Slot} {exps : List ℕ} {k : ℕ} {s : Slot}
    (hm : SlotsMatch st exps) (hget : st[k]? = some s) :
    0 < s.p * s.sigPow ∧
    (dropSlotLnLd st k).1 * s.sigPow * s.p = slotsLn st * (s.sigPow - 1) ∧
    (dropSlotLnLd st k).2 * s.p = slotsLd st := by
  obtain ⟨hf, hpw⟩ := hm
  clear hpw
  have hLn_cons : ∀ (u : Slot) (r : List Slot), slotsLn (u :: r) = u.sigPow * slotsLn r := by
    intro u r
    rw [show slotsLn (u :: r) = ((u :: r).map Slot.sigPow).prod by
      simpa [slotsLn] using foldl_map_mul Slot.sigPow (u :: r) 1]
    rw [show slotsLn r = (r.map Slot.sigPow).prod by
      simpa [slotsLn] using foldl_map_mul Slot.sigPow r 1]
    simp
  have hLd_cons : ∀ (u : Slot) (r : List Slot), slotsLd (u :: r) = u.pPow * slotsLd r := by
    intro u r
    rw [show slotsLd (u :: r) = ((u :: r).map Slot.pPow).prod by
      simpa [slotsLd] using foldl_map_mul Slot.pPow (u :: r) 1]
    rw [show slotsLd r = (r.map Slot.pPow).prod by
      simpa [slotsLd] using foldl_map_mul Slot.pPow r 1]
    simp
  induction hf generalizing k with
  | nil => simp at hget
  | @cons u a rest arest hu hrest ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      obtain ⟨hp, _, hlo1, hpPow, hsigPow, _⟩ := hu
      have hlo_eq : (u.lo - 1) + 1 = u.lo := by omega
      have hsp_eq : sigmaPP u.p (u.lo - 1) * u.p + 1 = u.sigPow := by
        rw [hsigPow]
        conv_rhs => rw [← hlo_eq]
        rfl
      have hpp_eq : u.p ^ (u.lo - 1) * u.p = u.pPow := by
        rw [hpPow]; conv_rhs => rw [← hlo_eq, pow_succ]
      have hsp_sub : sigmaPP u.p (u.lo - 1) * u.p = u.sigPow - 1 := by omega
      refine ⟨Nat.mul_pos hp.pos (by rw [hsigPow]; exact sigmaPP_pos _ _), ?_, ?_⟩
      · simp only [dropSlotLnLd, hLn_cons]
        calc sigmaPP u.p (u.lo - 1) * slotsLn rest * u.sigPow * u.p
            = (u.sigPow * slotsLn rest) * (sigmaPP u.p (u.lo - 1) * u.p) := by ring
          _ = u.sigPow * slotsLn rest * (u.sigPow - 1) := by rw [hsp_sub]
      · simp only [dropSlotLnLd, hLd_cons]
        calc u.p ^ (u.lo - 1) * slotsLd rest * u.p
            = (u.p ^ (u.lo - 1) * u.p) * slotsLd rest := by ring
          _ = u.pPow * slotsLd rest := by rw [hpp_eq]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hget
      obtain ⟨hpos, h1, h2⟩ := ih hget
      refine ⟨hpos, ?_, ?_⟩
      · simp only [dropSlotLnLd, hLn_cons]
        calc u.sigPow * (dropSlotLnLd rest k).1 * s.sigPow * s.p
            = u.sigPow * ((dropSlotLnLd rest k).1 * s.sigPow * s.p) := by ring
          _ = u.sigPow * (slotsLn rest * (s.sigPow - 1)) := by rw [h1]
          _ = u.sigPow * slotsLn rest * (s.sigPow - 1) := by ring
      · simp only [dropSlotLnLd, hLd_cons]
        calc u.pPow * (dropSlotLnLd rest k).2 * s.p
            = u.pPow * ((dropSlotLnLd rest k).2 * s.p) := by ring
          _ = u.pPow * slotsLd rest := by rw [h2]

private lemma checkNonPrimMaxSig_false_of_prim {st : List Slot} {exps : List ℕ} {q Q e0 e : ℕ}
    (hm : SlotsMatch st exps) (hq : q.Prime) (hqQ : q ≤ Q) (he : e0 ≤ e)
    (hlt : ∀ s ∈ st, s.p < q)
    (hprim : ∀ d ∈ (bVal st exps * q ^ e).properDivisors, d.Deficient)
    (hchk : Nat.ble (2 * slotsLd st * slotsMaxSig st * Q ^ e0)
        (slotsLn st * (slotsMaxSig st - 1) * sigmaPP Q e0) = true) : False := by
  simp only [Nat.ble_eq] at hchk
  have hLd0 : 0 < slotsLd st := (slots_bounds hm).1
  have hQ0 : 0 < Q ^ e0 := pow_pos (by have := hq.pos; omega) e0
  have hgt1 : 1 < slotsMaxSig st := by
    by_contra hle
    have hsub0 : slotsMaxSig st - 1 = 0 := by omega
    rw [hsub0] at hchk
    simp only [mul_zero, zero_mul, Nat.le_zero] at hchk
    have hpos : 0 < 2 * slotsLd st * slotsMaxSig st * Q ^ e0 := by
      have : 0 < slotsMaxSig st := by
        cases st with
        | nil => simp [slotsMaxSig]
        | cons s rest =>
          unfold slotsMaxSig; dsimp only; split_ifs with h1
          · exact Nat.pos_of_ne_zero (by intro hz; rw [hz] at h1; simp [Nat.ble_eq] at h1; have := hm.1; cases this with | cons hs _ => rw [hs.2.2.2.2.1] at h1; exact absurd h1 (Nat.ne_of_gt (sigmaPP_pos _ _)))
          · cases hm.1 with | cons hs _ => rw [hs.2.2.2.2.1]; exact sigmaPP_pos _ _
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hLd0) this) hQ0
    omega
  obtain ⟨k, hk, s, hget, hsig⟩ := exists_slot_of_slotsMaxSig_gt_one hgt1
  obtain ⟨hpos, h1, h2⟩ := dropSlotLnLd_mul_sigPow hm hget
  have hle : 2 * (dropSlotLnLd st k).2 * Q ^ e0 ≤ (dropSlotLnLd st k).1 * sigmaPP Q e0 := by
    apply Nat.le_of_mul_le_mul_right _ hpos
    calc 2 * (dropSlotLnLd st k).2 * Q ^ e0 * (s.p * s.sigPow)
        = 2 * ((dropSlotLnLd st k).2 * s.p) * s.sigPow * Q ^ e0 := by ring
      _ = 2 * slotsLd st * slotsMaxSig st * Q ^ e0 := by rw [h2, hsig]
      _ ≤ slotsLn st * (slotsMaxSig st - 1) * sigmaPP Q e0 := hchk
      _ = slotsLn st * (s.sigPow - 1) * sigmaPP Q e0 := by rw [hsig]
      _ = ((dropSlotLnLd st k).1 * s.sigPow * s.p) * sigmaPP Q e0 := by rw [← h1]
      _ = (dropSlotLnLd st k).1 * sigmaPP Q e0 * (s.p * s.sigPow) := by ring
  exact dropSlot_nonPrim_false hm hk hq hqQ he hlt hprim hle

private def slotsUnF : List Slot → ℕ
  | [] => 1
  | s :: rest => (if s.fixed then s.sigPow else s.p) * slotsUnF rest

private def slotsUdF : List Slot → ℕ
  | [] => 1
  | s :: rest => (if s.fixed then s.pPow else s.p - 1) * slotsUdF rest

private def slotsLnF : List Slot → ℕ
  | [] => 1
  | s :: rest => s.sigPow * slotsLnF rest

private def slotsLdF : List Slot → ℕ
  | [] => 1
  | s :: rest => s.pPow * slotsLdF rest

private lemma slotsUnF_eq (st : List Slot) : slotsUnF st = slotsUn st := by
  rw [show slotsUn st = (st.map fun s => if s.fixed then s.sigPow else s.p).prod by
    simpa [slotsUn] using foldl_map_mul (fun s : Slot => if s.fixed then s.sigPow else s.p) st 1]
  induction st with
  | nil => rfl
  | cons s rest ih => simp [slotsUnF, ih]

private lemma slotsUdF_eq (st : List Slot) : slotsUdF st = slotsUd st := by
  rw [show slotsUd st = (st.map fun s => if s.fixed then s.pPow else s.p - 1).prod by
    simpa [slotsUd] using foldl_map_mul (fun s : Slot => if s.fixed then s.pPow else s.p - 1) st 1]
  induction st with
  | nil => rfl
  | cons s rest ih => simp [slotsUdF, ih]

private lemma slotsLnF_eq (st : List Slot) : slotsLnF st = slotsLn st := by
  rw [show slotsLn st = (st.map Slot.sigPow).prod by
    simpa [slotsLn] using foldl_map_mul Slot.sigPow st 1]
  induction st with
  | nil => rfl
  | cons s rest ih => simp [slotsLnF, ih]

private lemma slotsLdF_eq (st : List Slot) : slotsLdF st = slotsLd st := by
  rw [show slotsLd st = (st.map Slot.pPow).prod by
    simpa [slotsLd] using foldl_map_mul Slot.pPow st 1]
  induction st with
  | nil => rfl
  | cons s rest ih => simp [slotsLdF, ih]

private lemma slotsUn_append_mkSlot (st : List Slot) (p : ℕ) :
    slotsUn (st ++ [mkSlot p]) = slotsUn st * p := by
  simp [slotsUn, List.foldl_append, mkSlot]

private lemma slotsUd_append_mkSlot (st : List Slot) (p : ℕ) :
    slotsUd (st ++ [mkSlot p]) = slotsUd st * (p - 1) := by
  simp [slotsUd, List.foldl_append, mkSlot]

private lemma slotsLn_append_mkSlot (st : List Slot) (p : ℕ) :
    slotsLn (st ++ [mkSlot p]) = slotsLn st * (p + 1) := by
  simp [slotsLn, List.foldl_append, mkSlot]

private lemma slotsUn_bumpIdx_of_free {st : List Slot} {i : ℕ} {s : Slot}
    (hget : st[i]? = some s) (hfree : s.fixed = false) :
    slotsUn (bumpIdx st i) = slotsUn st := by
  rw [← slotsUnF_eq, ← slotsUnF_eq]
  induction st generalizing i with
  | nil => simp at hget
  | cons u rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [bumpIdx, slotsUnF, Slot.bump, hfree]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      simp [bumpIdx, slotsUnF, ih hget]

private lemma slotsUd_bumpIdx_of_free {st : List Slot} {i : ℕ} {s : Slot}
    (hget : st[i]? = some s) (hfree : s.fixed = false) :
    slotsUd (bumpIdx st i) = slotsUd st := by
  rw [← slotsUdF_eq, ← slotsUdF_eq]
  induction st generalizing i with
  | nil => simp at hget
  | cons u rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [bumpIdx, slotsUdF, Slot.bump, hfree]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      simp [bumpIdx, slotsUdF, ih hget]

private lemma slotsLn_fixIdx (st : List Slot) (i : ℕ) :
    slotsLn (fixIdx st i) = slotsLn st := by
  rw [← slotsLnF_eq, ← slotsLnF_eq]
  induction st generalizing i with
  | nil => simp [fixIdx]
  | cons u rest ih =>
    cases i with
    | zero => simp [fixIdx, slotsLnF, Slot.fix]
    | succ i => simp [fixIdx, slotsLnF, ih]

private def deficGeTwo (st : List Slot) (Un Ud Ld : ℕ) : Bool :=
  Nat.ble (2 * Ud + Un * Ld) (2 * Ud * Ld) || st.any (fun s => s.fixed && Nat.beq (s.lo % 2) 1)

private lemma sigmaPP_mod_two {p : ℕ} (hodd : p % 2 = 1) : ∀ a, sigmaPP p a % 2 = (a + 1) % 2
  | 0 => by simp [sigmaPP]
  | a + 1 => by
    have ih := sigmaPP_mod_two hodd a
    rw [sigmaPP, Nat.add_mod, Nat.mul_mod, ih, hodd]
    omega

private lemma deficGeTwo_sound {st : List Slot} {exps : List ℕ}
    (hm : SlotsMatch st exps) (hdef : bSig st exps < 2 * bVal st exps)
    (h : deficGeTwo st (slotsUn st) (slotsUd st) (slotsLd st) = true) :
    2 ≤ (bVal st exps : ℤ) - ProperSum (bVal st exps) := by
  have hsp := sigma_split (bVal st exps)
  rw [← bSig_eq_sigma_one_bVal hm] at hsp
  suffices h2 : bSig st exps + 2 ≤ 2 * bVal st exps by omega
  unfold deficGeTwo at h
  simp only [Bool.or_eq_true, Nat.ble_eq, List.any_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
  rcases h with hbound | ⟨s, hs_mem, hs_fix, hs_odd⟩
  · obtain ⟨_, hUd0, hLd_le, _, hU⟩ := slots_bounds hm
    have h1 : 2 * slotsUd st + slotsUn st * bVal st exps ≤ 2 * slotsUd st * bVal st exps := by
      have hsub : slotsUn st ≤ 2 * slotsUd st :=
        Nat.le_of_mul_le_mul_right (by omega : slotsUn st * slotsLd st ≤ 2 * slotsUd st * slotsLd st)
          (slots_bounds hm).1
      zify [hsub] at hbound ⊢
      nlinarith
    have h2 : (bSig st exps + 2) * slotsUd st ≤ (2 * bVal st exps) * slotsUd st := by nlinarith
    exact Nat.le_of_mul_le_mul_right h2 hUd0
  · have heven : 2 ∣ bSig st exps := by
      obtain ⟨hf, hpw⟩ := hm
      clear hpw hdef hsp
      unfold bSig
      induction hf with
      | nil => simp at hs_mem
      | @cons t a rest arest ht hrest ih =>
        simp only [List.zipWith_cons_cons, List.prod_cons]
        simp only [List.mem_cons] at hs_mem
        rcases hs_mem with rfl | hs_mem
        · have ha : a = s.lo := by
            have hcmp := ht.2.2.2.2.2
            rwa [hs_fix, if_pos rfl] at hcmp
          subst ha
          have ht_odd : s.p % 2 = 1 := by
            rcases Nat.Prime.eq_two_or_odd ht.1 with h2 | hodd
            · have := ht.2.1; omega
            · exact hodd
          have hmod := sigmaPP_mod_two ht_odd s.lo
          have hdvd : 2 ∣ sigmaPP s.p s.lo := Nat.dvd_of_mod_eq_zero (by omega)
          exact dvd_mul_of_dvd_left hdvd _
        · exact dvd_mul_of_dvd_right (ih hs_mem) _
    omega

private def pickBestFreeAux : List Slot → ℕ → Option (ℕ × ℕ) → Option (ℕ × ℕ)
  | [], _, best => best
  | s :: rest, i, best =>
    let best' :=
      if s.fixed then best
      else
        let v := s.pPow * s.p
        match best with
        | none => some (i, v)
        | some (_, bv) => if v < bv then some (i, v) else best
    pickBestFreeAux rest (i + 1) best'

private def pickBestFree (st : List Slot) : Option ℕ :=
  (pickBestFreeAux st 0 none).map Prod.fst

private lemma pickBestFree_sound {st : List Slot} {i : ℕ} (h : pickBestFree st = some i) :
    ∃ s, st[i]? = some s ∧ s.fixed = false := by
  have aux : ∀ (l : List Slot) (off : ℕ) (best : Option (ℕ × ℕ)) (j v : ℕ),
      (∀ bi bv, best = some (bi, bv) → bi < off ∧ ∃ s, st[bi]? = some s ∧ s.fixed = false) →
      (∀ k s, l[k]? = some s → st[off + k]? = some s) →
      pickBestFreeAux l off best = some (j, v) →
      ∃ s, st[j]? = some s ∧ s.fixed = false := by
    intro l
    induction l with
    | nil =>
      intro off best j v hbest _ hres
      simp only [pickBestFreeAux] at hres
      exact (hbest j v hres).2
    | cons u rest ih =>
      intro off best j v hbest hshift hres
      simp only [pickBestFreeAux] at hres
      apply ih (off + 1) _ j v _ (fun k s hk => by
        have := hshift (k + 1) s (by simpa using hk)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this) hres
      intro bi bv hbi
      split_ifs at hbi with huf
      · obtain ⟨h1, h2⟩ := hbest bi bv hbi
        exact ⟨by omega, h2⟩
      · cases hbe : best with
        | none =>
          rw [hbe] at hbi
          simp only [Option.some.injEq, Prod.mk.injEq] at hbi
          obtain ⟨rfl, rfl⟩ := hbi
          refine ⟨by omega, u, ?_, by simpa using huf⟩
          simpa using hshift 0 u rfl
        | some bp =>
          rcases bp with ⟨bi0, bv0⟩
          rw [hbe] at hbi
          dsimp only at hbi
          split_ifs at hbi with hlt
          · simp only [Option.some.injEq, Prod.mk.injEq] at hbi
            obtain ⟨rfl, rfl⟩ := hbi
            refine ⟨by omega, u, ?_, by simpa using huf⟩
            simpa using hshift 0 u rfl
          · obtain ⟨h1, h2⟩ := hbest bi bv (by rw [hbe]; exact hbi)
            exact ⟨by omega, h2⟩
  unfold pickBestFree at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨j, v⟩, hres, rfl⟩ := h
  exact aux st 0 none j v (fun _ _ h' => by simp at h') (fun k s hk => by simpa using hk) hres

private def checkFamilyQ (st : List Slot) (good : Option (ℕ × ℕ)) (Un Ud Ln Ld maxSig q : ℕ) : Bool :=
  if hasSmallFactor q then true
  else if Nat.blt (2 * Ud * q) (Un * (q + 1)) then
    if Nat.ble (2 * Ld * maxSig * q) (Ln * (maxSig - 1) * (q + 1)) then true
    else
      match good with
      | none => false
      | some (L, _) =>
        deficGeTwo st Un Ud Ld && Nat.ble (2 * Ld * q + L) (Ln * (q + 1))
  else
    match findMinExpStrict Un Ud q 60 1 q (q + 1) with
    | none => false
    | some (eMin, qP, sigQ) =>
      if Nat.ble (2 * Ld * maxSig * qP) (Ln * (maxSig - 1) * sigQ) then true
      else
        match good with
        | none => false
        | some (L, _) =>
          (Nat.blt 1 eMin || deficGeTwo st Un Ud Ld) && Nat.ble (2 * Ld * qP + L) (Ln * sigQ)

private lemma checkFamilyQ_sound {st : List Slot} {exps : List ℕ} {good : Option (ℕ × ℕ)}
    {q e : ℕ}
    (hm : SlotsMatch st exps)
    (hgood : match good with | none => True | some (L, G) => FamilyCertified st L G)
    (hq : q.Prime) (hq3 : 3 ≤ q) (he : 1 ≤ e)
    (hlt : ∀ s ∈ st, s.p < q)
    (hab : (bVal st exps * q ^ e).Abundant)
    (hprim : ∀ d ∈ (bVal st exps * q ^ e).properDivisors, d.Deficient)
    (hchk : checkFamilyQ st good (slotsUn st) (slotsUd st) (slotsLn st) (slotsLd st) (slotsMaxSig st) q = true) :
    (bVal st exps * q ^ e).Pseudoperfect := by
  have hcop : (bVal st exps).Coprime q := by
    rw [bVal_eq_valF_zip]
    refine coprime_valF_of_last_lt (validFactors_zipWith_of_slotsMatch hm) hq (fun pa hpa => ?_)
    obtain ⟨s, hs, _, _, rfl⟩ := mem_zipWith_fst hpa
    exact hlt s hs
  have hsig_m : sigma 1 (bVal st exps * q ^ e) = bSig st exps * sigmaPP q e := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right e),
      bSig_eq_sigma_one_bVal hm, sigmaPP_eq_sigma_one_prime_pow hq]
  have hab_m : 2 * (bVal st exps * q ^ e) < bSig st exps * sigmaPP q e := by
    have h1 := hab
    change bVal st exps * q ^ e < ∑ d ∈ (bVal st exps * q ^ e).properDivisors, d at h1
    have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := bVal st exps * q ^ e)
    rw [← sigma_one_apply, hsig_m] at h2
    omega
  have hb_def : bSig st exps < 2 * bVal st exps := by
    have hmem : bVal st exps ∈ (bVal st exps * q ^ e).properDivisors := by
      refine Nat.mem_properDivisors.mpr ⟨dvd_mul_right _ _, ?_⟩
      have hq1 : 1 < q ^ e := one_lt_pow₀ hq.one_lt (by omega)
      nlinarith [bVal_pos hm]
    have hdef := hprim _ hmem
    change ∑ d ∈ (bVal st exps).properDivisors, d < bVal st exps at hdef
    have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := bVal st exps)
    rw [← sigma_one_apply, ← bSig_eq_sigma_one_bVal hm] at h2
    omega
  have hclose : ∀ (g : Option (ℕ × ℕ)) (eMin : ℕ), 1 ≤ eMin → eMin ≤ e →
      (match g with
       | none => false
       | some (L, _) => (Nat.blt 1 eMin || deficGeTwo st (slotsUn st) (slotsUd st) (slotsLd st)) &&
           Nat.ble (2 * slotsLd st * q ^ eMin + L) (slotsLn st * sigmaPP q eMin)) = true →
      (match g with | none => True | some (L, G) => FamilyCertified st L G) →
      (bVal st exps * q ^ e).Pseudoperfect := by
    intro g eMin heMin1 he_ge hcond hg
    cases g with
    | none => simp at hcond
    | some lg =>
      rcases lg with ⟨L, G⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at hcond
      obtain ⟨hdef2, hEL⟩ := hcond
      have hcert : CertifiedBase (bVal st exps) L G :=
        certifiedBase_of_familyCertified (gapSum st exps) rfl hm hg
      obtain ⟨hLd0, _, hLd_le, hL_bnd, _⟩ := slots_bounds hm
      have hrat : sigmaPP q eMin * q ^ e ≤ sigmaPP q e * q ^ eMin := sigmaPP_mono_ratio hq.pos he_ge
      have hpow_le : q ^ eMin ≤ q ^ e := Nat.pow_le_pow_right hq.pos he_ge
      have hEx : 2 * (bVal st exps * q ^ e) + L ≤ bSig st exps * sigmaPP q e := by
        have hmul : (2 * (bVal st exps * q ^ e) + L) * (slotsLd st * q ^ eMin) ≤
            bSig st exps * sigmaPP q e * (slotsLd st * q ^ eMin) :=
          calc (2 * (bVal st exps * q ^ e) + L) * (slotsLd st * q ^ eMin)
              = 2 * (bVal st exps * q ^ e) * (slotsLd st * q ^ eMin) + L * (slotsLd st * q ^ eMin) := by ring
            _ ≤ 2 * (bVal st exps * q ^ e) * (slotsLd st * q ^ eMin) + L * (bVal st exps * q ^ e) :=
                Nat.add_le_add_left (Nat.mul_le_mul_left L (Nat.mul_le_mul hLd_le hpow_le)) _
            _ = (bVal st exps * q ^ e) * (2 * slotsLd st * q ^ eMin + L) := by ring
            _ ≤ (bVal st exps * q ^ e) * (slotsLn st * sigmaPP q eMin) := Nat.mul_le_mul_left _ hEL
            _ = (slotsLn st * bVal st exps) * (sigmaPP q eMin * q ^ e) := by ring
            _ ≤ (bSig st exps * slotsLd st) * (sigmaPP q e * q ^ eMin) := Nat.mul_le_mul hL_bnd hrat
            _ = bSig st exps * sigmaPP q e * (slotsLd st * q ^ eMin) := by ring
        exact Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos hLd0 (pow_pos hq.pos eMin))
      have he_succ : e = (e - 1) + 1 := by omega
      rw [he_succ] at hprim ⊢
      refine certified_prime_power_pseudoperfect hcert hq hcop hq3 hprim ?_ ?_
      · unfold Excess; rw [← he_succ, hsig_m]; omega
      · intro hj0
        have he1 : e = 1 := by omega
        rcases hdef2 with hgt1 | hdg2
        · omega
        · exact deficGeTwo_sound hm hb_def hdg2
  unfold checkFamilyQ at hchk
  have hns : hasSmallFactor q = false := by
    cases hsf : hasSmallFactor q
    · rfl
    · exact absurd hq (not_prime_of_hasSmallFactor hsf)
  rw [hns] at hchk
  simp only [Bool.false_eq_true, ↓reduceIte] at hchk
  split_ifs at hchk with he1 hnp1
  · exact False.elim (checkNonPrimMaxSig_false_of_prim hm hq le_rfl he hlt hprim (by simpa [pow_one, sigmaPP] using hnp1))
  · refine hclose good 1 le_rfl he ?_ hgood
    cases good with
    | none => simp at hchk
    | some lg =>
      rcases lg with ⟨L, G⟩
      simpa [pow_one, sigmaPP, Nat.blt_eq] using hchk
  · cases hmin : findMinExpStrict (slotsUn st) (slotsUd st) q 60 1 q (q + 1) with
    | none => rw [hmin] at hchk; simp at hchk
    | some res =>
      rcases res with ⟨eMin, qP, sigQ⟩
      rw [hmin] at hchk
      dsimp only at hchk
      obtain ⟨heMin1, hqP, hsigQ, _⟩ :=
        findMinExpStrict_sound (by simp) (by simp [sigmaPP]) (fun t h1 h2 => by omega) hmin
      have he_ge : eMin ≤ e := exp_ge_of_findMinExpStrict hm hq.pos le_rfl he hab_m hmin
      subst hqP; subst hsigQ
      split_ifs at hchk with hnp
      · exact False.elim (checkNonPrimMaxSig_false_of_prim hm hq le_rfl he_ge hlt hprim hnp)
      · exact hclose good eMin heMin1 he_ge hchk hgood

private def uniformGiven (st : List Slot) (good : Option (ℕ × ℕ)) (Un Ud Ln Ld eMin xP Qtop : ℕ) : Bool :=
  match good with
  | none => false
  | some (L, _) =>
    if Nat.beq eMin 1 then
      deficGeTwo st Un Ud Ld && Nat.ble (2 * Ld * Qtop + L) (Ln * (Qtop + 1))
    else
      let Qpow := Qtop ^ eMin
      let sigQ := sigmaPP Qtop eMin
      Nat.ble (2 * Ld * Qpow * xP + L * Qpow) (Ln * sigQ * xP)

private lemma uniformGiven_sound {st : List Slot} {exps : List ℕ} {good : Option (ℕ × ℕ)}
    {q e Qtop eMin x : ℕ}
    (hm : SlotsMatch st exps)
    (hgood : match good with | none => True | some (L, G) => FamilyCertified st L G)
    (hq : q.Prime) (hq3 : 3 ≤ q) (hlast_q : lastPrime st < q) (hqQ : q ≤ Qtop)
    (hx0 : 0 < x) (hxq : x ≤ q) (he : 1 ≤ e) (heMin1 : 1 ≤ eMin) (he_ge : eMin ≤ e)
    (_hab : (bVal st exps * q ^ e).Abundant)
    (hprim : ∀ d ∈ (bVal st exps * q ^ e).properDivisors, d.Deficient)
    (hchk : uniformGiven st good (slotsUn st) (slotsUd st) (slotsLn st) (slotsLd st) eMin (x ^ eMin) Qtop = true) :
    (bVal st exps * q ^ e).Pseudoperfect := by
  have hlt : ∀ s ∈ st, s.p < q := all_lt_of_lastPrime_lt hm hlast_q
  have hcop : (bVal st exps).Coprime q := by
    rw [bVal_eq_valF_zip]
    refine coprime_valF_of_last_lt (validFactors_zipWith_of_slotsMatch hm) hq (fun pa hpa => ?_)
    obtain ⟨s, hs, _, _, rfl⟩ := mem_zipWith_fst hpa
    exact hlt s hs
  have hsig_m : sigma 1 (bVal st exps * q ^ e) = bSig st exps * sigmaPP q e := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right e),
      bSig_eq_sigma_one_bVal hm, sigmaPP_eq_sigma_one_prime_pow hq]
  have hb_def : bSig st exps < 2 * bVal st exps := by
    have hmem : bVal st exps ∈ (bVal st exps * q ^ e).properDivisors := by
      refine Nat.mem_properDivisors.mpr ⟨dvd_mul_right _ _, ?_⟩
      have hq1 : 1 < q ^ e := one_lt_pow₀ hq.one_lt (by omega)
      nlinarith [bVal_pos hm]
    have hdef := hprim _ hmem
    change ∑ d ∈ (bVal st exps).properDivisors, d < bVal st exps at hdef
    have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := bVal st exps)
    rw [← sigma_one_apply, ← bSig_eq_sigma_one_bVal hm] at h2
    omega
  unfold uniformGiven at hchk
  cases good with
  | none => simp at hchk
  | some lg =>
    rcases lg with ⟨L, G⟩
    have hcert : CertifiedBase (bVal st exps) L G :=
      certifiedBase_of_familyCertified (gapSum st exps) rfl hm hgood
    obtain ⟨hLd0, _, hLd_le, hL_bnd, _⟩ := slots_bounds hm
    have hLn_lt : slotsLn st < 2 * slotsLd st := by
      have hbpos := bVal_pos hm
      have h1 : slotsLn st * bVal st exps < 2 * slotsLd st * bVal st exps := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right h1
    have he_succ : e = (e - 1) + 1 := by omega
    dsimp only at hchk
    split_ifs at hchk with he1
    · simp only [Bool.and_eq_true, Nat.ble_eq] at hchk
      obtain ⟨hdg2, hEL⟩ := hchk
      have hEL_q : 2 * slotsLd st * q + L ≤ slotsLn st * (q + 1) := by
        zify at hEL hLn_lt hqQ ⊢; nlinarith
      have hrat : (q + 1) * q ^ e ≤ sigmaPP q e * q := by
        simpa [sigmaPP, pow_one] using sigmaPP_mono_ratio hq.pos he
      have hEx : 2 * (bVal st exps * q ^ e) + L ≤ bSig st exps * sigmaPP q e := by
        have hq_le : q ≤ q ^ e := by simpa [pow_one] using Nat.pow_le_pow_right hq.pos he
        have hmul : (2 * (bVal st exps * q ^ e) + L) * (slotsLd st * q) ≤
            bSig st exps * sigmaPP q e * (slotsLd st * q) :=
          calc (2 * (bVal st exps * q ^ e) + L) * (slotsLd st * q)
              = 2 * (bVal st exps * q ^ e) * (slotsLd st * q) + L * (slotsLd st * q) := by ring
            _ ≤ 2 * (bVal st exps * q ^ e) * (slotsLd st * q) + L * (bVal st exps * q ^ e) :=
                Nat.add_le_add_left (Nat.mul_le_mul_left L (Nat.mul_le_mul hLd_le hq_le)) _
            _ = (bVal st exps * q ^ e) * (2 * slotsLd st * q + L) := by ring
            _ ≤ (bVal st exps * q ^ e) * (slotsLn st * (q + 1)) := Nat.mul_le_mul_left _ hEL_q
            _ = (slotsLn st * bVal st exps) * ((q + 1) * q ^ e) := by ring
            _ ≤ (bSig st exps * slotsLd st) * (sigmaPP q e * q) := Nat.mul_le_mul hL_bnd hrat
            _ = bSig st exps * sigmaPP q e * (slotsLd st * q) := by ring
        exact Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos hLd0 hq.pos)
      rw [he_succ] at hprim ⊢
      refine certified_prime_power_pseudoperfect hcert hq hcop hq3 hprim ?_ ?_
      · unfold Excess; rw [← he_succ, hsig_m]; omega
      · intro _; exact deficGeTwo_sound hm hb_def hdg2
    · have heMin2 : 2 ≤ eMin := by
        have : eMin ≠ 1 := fun h => he1 (by simpa [Nat.beq_eq] using h)
        omega
      simp only [Nat.ble_eq] at hchk
      have hrat : sigmaPP Qtop eMin * q ^ e ≤ sigmaPP q e * Qtop ^ eMin :=
        sigmaPP_ratio_ge hq.pos hqQ he_ge
      have hx_le_qe : x ^ eMin ≤ q ^ e :=
        (Nat.pow_le_pow_left hxq eMin).trans (Nat.pow_le_pow_right hq.pos he_ge)
      have hQpos : 0 < Qtop ^ eMin := pow_pos (by omega) eMin
      have hXpos : 0 < x ^ eMin := pow_pos hx0 eMin
      have hEx : 2 * (bVal st exps * q ^ e) + L ≤ bSig st exps * sigmaPP q e := by
        have hmul : (2 * (bVal st exps * q ^ e) + L) * (slotsLd st * Qtop ^ eMin * x ^ eMin) ≤
            bSig st exps * sigmaPP q e * (slotsLd st * Qtop ^ eMin * x ^ eMin) :=
          calc (2 * (bVal st exps * q ^ e) + L) * (slotsLd st * Qtop ^ eMin * x ^ eMin)
              = 2 * (bVal st exps * q ^ e) * (slotsLd st * Qtop ^ eMin * x ^ eMin) +
                  L * Qtop ^ eMin * (slotsLd st * x ^ eMin) := by ring
            _ ≤ 2 * (bVal st exps * q ^ e) * (slotsLd st * Qtop ^ eMin * x ^ eMin) +
                  L * Qtop ^ eMin * (bVal st exps * q ^ e) :=
                Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul hLd_le hx_le_qe)) _
            _ = (bVal st exps * q ^ e) * (2 * slotsLd st * Qtop ^ eMin * x ^ eMin + L * Qtop ^ eMin) := by ring
            _ ≤ (bVal st exps * q ^ e) * (slotsLn st * sigmaPP Qtop eMin * x ^ eMin) :=
                Nat.mul_le_mul_left _ hchk
            _ = (slotsLn st * bVal st exps) * (sigmaPP Qtop eMin * q ^ e) * x ^ eMin := by ring
            _ ≤ (bSig st exps * slotsLd st) * (sigmaPP q e * Qtop ^ eMin) * x ^ eMin :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul hL_bnd hrat)
            _ = bSig st exps * sigmaPP q e * (slotsLd st * Qtop ^ eMin * x ^ eMin) := by ring
        exact Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos (Nat.mul_pos hLd0 hQpos) hXpos)
      rw [he_succ] at hprim ⊢
      refine certified_prime_power_pseudoperfect hcert hq hcop hq3 hprim ?_ ?_
      · unfold Excess; rw [← he_succ, hsig_m]; omega
      · intro hj0; omega

private def propagateGood (good : Option (ℕ × ℕ)) (p Ln Ld : ℕ) : Option (ℕ × ℕ) :=
  match good with
  | none => none
  | some (L, G) =>
    if Nat.ble Ld Ln && Nat.ble (p * G + 2 * L) (Ln - Ld + 1) && Nat.ble (Ld + 2 * L) ((p + 1) * (Ln - Ld) + 1) then
      some (L, G)
    else none

private def withGood (st : List Slot) (good : Option (ℕ × ℕ)) (cond : Bool)
    (f : Option (ℕ × ℕ) → Bool) : Bool :=
  match good with
  | some lg => f (some lg)
  | none =>
    if cond then
      match findGoodFamily st with
      | none => f none
      | some lg => f (some lg)
    else f none

private def checkTreeAux : ℕ → List Slot → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ) → Bool
  | 0, _, _, _, _, _, _, _, _, _, _ => false
  | fuel + 1, st, rem, Un, Ud, Ln, Ld, maxSig, last, nextP, good =>
    if Nat.beq rem 0 then false
    else if Nat.ble (2 * Ld) Ln then true
    else if Nat.beq rem 1 then
      if Nat.ble (Un * nextP) (2 * Ud * (nextP - 1)) then true
      else if Nat.blt Un (2 * Ud) then
        let qMax := (2 * Ud - 1) / (2 * Ud - Un)
        if Nat.ble qMax last then true
        else if Nat.blt (2 * Ud * nextP) (Un * (nextP + 1)) then
          if Nat.ble (2 * Ld * maxSig * qMax) (Ln * (maxSig - 1) * (qMax + 1)) then true
          else
            withGood st good (Nat.ble 3 st.length || st.all Slot.fixed) fun g' =>
              if uniformGiven st g' Un Ud Ln Ld 1 nextP qMax then true
              else
                let allFix := st.all Slot.fixed
                let worthPrev :=
                  allFix || Nat.ble (qMax - last) 140 ||
                  match g' with
                  | none => false
                  | some (L, _) =>
                    let qLow := if Nat.blt 120 qMax then qMax - 120 else last + 1
                    Nat.ble (2 * Ld * qLow + L) (Ln * (qLow + 1))
                let tryShrunk :=
                  if !worthPrev then false
                  else
                    let Qlim0 := prevPrimeLE qMax
                    let Qlim := if Nat.blt Qlim0 2 then qMax else Qlim0
                    if Nat.ble Qlim last then true
                    else if Nat.blt Qlim qMax &&
                       (Nat.ble (2 * Ld * maxSig * Qlim) (Ln * (maxSig - 1) * (Qlim + 1)) ||
                        uniformGiven st g' Un Ud Ln Ld 1 nextP Qlim) then true
                    else
                      let splitQMax :=
                        if Nat.beq Qlim qMax && checkFamilyQ st g' Un Ud Ln Ld maxSig qMax then
                          let Q10 := prevPrimeLE (qMax - 1)
                          let Q1 := if Nat.blt Q10 2 then qMax - 1 else Q10
                          if Nat.ble Q1 last then true
                          else Nat.ble (2 * Ld * maxSig * Q1) (Ln * (maxSig - 1) * (Q1 + 1)) ||
                               uniformGiven st g' Un Ud Ln Ld 1 nextP Q1
                        else false
                      if splitQMax then true
                      else if Nat.ble (Qlim - last) 16 &&
                          checkOddRange (checkFamilyQ st g' Un Ud Ln Ld maxSig) 6 (last + 1) Qlim then true
                      else if allFix then
                        checkOddRange (checkConcreteQ st g') 13 (last + 1) Qlim
                      else false
                if tryShrunk then true
                else
                  match pickBestFree st with
                  | none => false
                  | some i =>
                    let stF := fixIdx st i
                    let stB := bumpIdx st i
                    checkTreeAux fuel stF 1 (slotsUnF stF) (slotsUdF stF) Ln Ld maxSig last nextP g' &&
                    checkTreeAux fuel stB 1 Un Ud (slotsLnF stB) (slotsLdF stB) (slotsMaxSig stB) last nextP g'
        else
          match findMinExpStrict Un Ud nextP 60 1 nextP (nextP + 1) with
          | none => false
          | some (eMin, xP, _) =>
            let QpowM := qMax ^ eMin
            let sigQM := sigmaPP qMax eMin
            if Nat.ble (2 * Ld * maxSig * QpowM) (Ln * (maxSig - 1) * sigQM) then true
            else
              withGood st good (Nat.ble 3 st.length || st.all Slot.fixed) fun g' =>
                if uniformGiven st g' Un Ud Ln Ld eMin xP qMax then true
                else
                  let Qlim0 := prevPrimeLE qMax
                  let Qlim := if Nat.blt Qlim0 2 then qMax else Qlim0
                  if Nat.ble Qlim last then true
                  else
                    let Qpow := Qlim ^ eMin
                    let sigQ := sigmaPP Qlim eMin
                    if Nat.blt Qlim qMax &&
                       (Nat.ble (2 * Ld * maxSig * Qpow) (Ln * (maxSig - 1) * sigQ) ||
                        uniformGiven st g' Un Ud Ln Ld eMin xP Qlim) then true
                    else
                      let splitQMax :=
                        if Nat.beq Qlim qMax && checkFamilyQ st g' Un Ud Ln Ld maxSig qMax then
                          let Q10 := prevPrimeLE (qMax - 1)
                          let Q1 := if Nat.blt Q10 2 then qMax - 1 else Q10
                          if Nat.ble Q1 last then true
                          else
                            Nat.ble (2 * Ld * maxSig * Q1 ^ eMin) (Ln * (maxSig - 1) * sigmaPP Q1 eMin) ||
                            uniformGiven st g' Un Ud Ln Ld eMin xP Q1
                        else false
                      if splitQMax then true
                      else if Nat.ble (Qlim - last) 16 &&
                          checkOddRange (checkFamilyQ st g' Un Ud Ln Ld maxSig) 6 (last + 1) Qlim then true
                      else if st.all Slot.fixed then
                        checkOddRange (checkConcreteQ st g') 13 (last + 1) Qlim
                      else
                        match pickBestFree st with
                        | none => false
                        | some i =>
                          let stF := fixIdx st i
                          let stB := bumpIdx st i
                          checkTreeAux fuel stF 1 (slotsUnF stF) (slotsUdF stF) Ln Ld maxSig last nextP g' &&
                          checkTreeAux fuel stB 1 Un Ud (slotsLnF stB) (slotsLdF stB) (slotsMaxSig stB) last nextP g'
      else
        withGood st good (Nat.ble 3 st.length) fun g' =>
          match pickBestFree st with
          | none => false
          | some i =>
            let stF := fixIdx st i
            let stB := bumpIdx st i
            checkTreeAux fuel stF 1 (slotsUnF stF) (slotsUdF stF) Ln Ld maxSig last nextP g' &&
            checkTreeAux fuel stB 1 Un Ud (slotsLnF stB) (slotsLdF stB) (slotsMaxSig stB) last nextP g'
    else if tailDeadAux Un Ud last rem then true
    else
      withGood st good (Nat.ble 3 st.length) fun g' =>
        if Nat.blt Un (2 * Ud) then
          let pMax := (2 * Ud * rem - 1) / (2 * Ud - Un)
          checkOddRange (fun p =>
            if hasSmallFactor p then true
            else if tailDeadAux (Un * p) (Ud * (p - 1)) p (rem - 1) then true
            else
              let mSig' := if Nat.ble maxSig (p + 1) then p + 1 else maxSig
              match propagateGood g' p Ln Ld with
              | none => checkTreeAux fuel (st ++ [mkSlot p]) (rem - 1) (Un * p) (Ud * (p - 1)) (Ln * (p + 1)) (Ld * p) mSig' p (nextPrimeAfter p) none
              | some lg2 => checkTreeAux fuel (st ++ [mkSlot p]) (rem - 1) (Un * p) (Ud * (p - 1)) (Ln * (p + 1)) (Ld * p) mSig' p (nextPrimeAfter p) (some lg2))
            13 (last + 1) pMax
        else
          match pickBestFree st with
          | none => false
          | some i =>
            let stF := fixIdx st i
            let stB := bumpIdx st i
            checkTreeAux fuel stF rem (slotsUnF stF) (slotsUdF stF) Ln Ld maxSig last nextP g' &&
            checkTreeAux fuel stB rem Un Ud (slotsLnF stB) (slotsLdF stB) (slotsMaxSig stB) last nextP g'

private def checkTree (fuel : ℕ) (st : List Slot) (rem : ℕ) (good : Option (ℕ × ℕ)) : Bool :=
  let last := lastPrime st
  checkTreeAux fuel st rem (slotsUnF st) (slotsUdF st) (slotsLnF st) (slotsLdF st) (slotsMaxSig st) last (nextPrimeAfter last) good

private lemma slotsMatch_append_mkSlot {st : List Slot} {exps : List ℕ} {p a : ℕ}
    (hm : SlotsMatch st exps) (hp : p.Prime) (hp3 : 3 ≤ p) (ha : 1 ≤ a)
    (hlt : ∀ s ∈ st, s.p < p) :
    SlotsMatch (st ++ [mkSlot p]) (exps ++ [a]) := by
  have happ : List.Forall₂ SlotMatches (st ++ [mkSlot p]) (exps ++ [a]) := by
    have aux : ∀ {l1 : List Slot} {l2 : List ℕ}, List.Forall₂ SlotMatches l1 l2 →
        List.Forall₂ SlotMatches (l1 ++ [mkSlot p]) (l2 ++ [a]) := by
      intro l1 l2 h1
      induction h1 with
      | nil => exact List.Forall₂.cons ⟨hp, hp3, le_rfl, by simp [mkSlot], by simp [mkSlot, sigmaPP], by simp [mkSlot, ha]⟩ List.Forall₂.nil
      | cons hx _ ih => exact List.Forall₂.cons hx ih
    exact aux hm.1
  refine ⟨happ, ?_⟩
  rw [List.pairwise_append]
  refine ⟨hm.2, List.pairwise_singleton _ _, fun s hs t ht => ?_⟩
  simp only [List.mem_singleton] at ht
  subst ht
  exact hlt s hs

private lemma bVal_append_mkSlot (st : List Slot) (exps : List ℕ) (p a : ℕ)
    (hlen : st.length = exps.length) :
    bVal (st ++ [mkSlot p]) (exps ++ [a]) = bVal st exps * p ^ a := by
  unfold bVal
  rw [List.zipWith_append (h := hlen)]
  simp [mkSlot]

private lemma lastPrime_append_mkSlot (st : List Slot) (p : ℕ) :
    lastPrime (st ++ [mkSlot p]) = p := by
  simp [lastPrime, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), mkSlot]

private lemma lastPrime_eq_of_map_p_eq {l1 l2 : List Slot} (heq : l1.map Slot.p = l2.map Slot.p) :
    lastPrime l1 = lastPrime l2 := by
  unfold lastPrime
  have h := congrArg List.getLast? heq
  rw [List.getLast?_map, List.getLast?_map] at h
  cases h1 : l1.getLast? <;> cases h2 : l2.getLast? <;> simp [h1, h2] at h ⊢
  exact h

private lemma slotsUn_pos {st : List Slot} {exps : List ℕ} (hm : SlotsMatch st exps) :
    1 ≤ slotsUn st := by
  rw [show slotsUn st = (st.map fun s => if s.fixed then s.sigPow else s.p).prod by
    simpa [slotsUn] using foldl_map_mul (fun s : Slot => if s.fixed then s.sigPow else s.p) st 1]
  obtain ⟨hf, hpw⟩ := hm
  clear hpw
  induction hf with
  | nil => simp
  | @cons s a rest arest hs _ ih =>
    simp only [List.map_cons, List.prod_cons]
    have h1 : 1 ≤ (if s.fixed then s.sigPow else s.p) := by
      split_ifs
      · rw [hs.2.2.2.2.1]; exact sigmaPP_pos _ _
      · exact hs.1.pos
    exact Nat.mul_pos h1 ih

private def OptFamilyCertified (st : List Slot) : Option (ℕ × ℕ) → Prop
  | none => True
  | some (L, G) => FamilyCertified st L G

private lemma optFamilyCertified_fixIdx {st : List Slot} {i : ℕ} {g : Option (ℕ × ℕ)}
    (h : OptFamilyCertified st g) : OptFamilyCertified (fixIdx st i) g := by
  cases g with
  | none => trivial
  | some lg => exact familyCertified_fixIdx h

private lemma optFamilyCertified_bumpIdx {st : List Slot} {exps : List ℕ} {i : ℕ} {s : Slot}
    {g : Option (ℕ × ℕ)} (hm : SlotsMatch st exps) (hget : st[i]? = some s) (hfree : s.fixed = false)
    (h : OptFamilyCertified st g) : OptFamilyCertified (bumpIdx st i) g := by
  cases g with
  | none => trivial
  | some lg => exact familyCertified_bumpIdx hm hget hfree h

private lemma with_good_sound {st : List Slot} {exps : List ℕ} {good : Option (ℕ × ℕ)}
    {cond : Bool} {f : Option (ℕ × ℕ) → Bool} {P : Prop}
    (hcall : withGood st good cond f = true)
    (hm : SlotsMatch st exps) (hgood : OptFamilyCertified st good)
    (hf : ∀ g', OptFamilyCertified st g' → f g' = true → P) : P := by
  unfold withGood at hcall
  cases good with
  | some lg => exact hf (some lg) hgood hcall
  | none =>
    dsimp only at hcall
    split_ifs at hcall with hc
    · cases hfg : findGoodFamily st with
      | none => rw [hfg] at hcall; exact hf none trivial hcall
      | some lg => rw [hfg] at hcall; exact hf (some lg) (findGoodFamily_sound hm hfg) hcall
    · exact hf none trivial hcall

private lemma checkTreeAux_sound :
    ∀ (fuel : ℕ) {st : List Slot} {exps : List ℕ} {rem Un Ud Ln Ld maxSig last nextP : ℕ}
      {good : Option (ℕ × ℕ)} {tail : List (ℕ × ℕ)},
      Un = slotsUn st →
      Ud = slotsUd st →
      Ln = slotsLn st →
      Ld = slotsLd st →
      maxSig = slotsMaxSig st →
      last = lastPrime st →
      nextP = nextPrimeAfter last →
      SlotsMatch st exps →
      OptFamilyCertified st good →
      1 ≤ rem →
      TailMatch (lastPrime st) rem tail →
      (bVal st exps * valF tail).Abundant →
      (∀ d ∈ (bVal st exps * valF tail).properDivisors, d.Deficient) →
      checkTreeAux fuel st rem Un Ud Ln Ld maxSig last nextP good = true →
      (bVal st exps * valF tail).Pseudoperfect
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hchk => by
      simp [checkTreeAux] at hchk
  | fuel + 1, st, exps, rem, Un, Ud, Ln, Ld, maxSig, last, nextP, good, tail,
      hUn_eq, hUd_eq, hLn_eq, hLd_eq, hMax_eq, hLast_eq, hNext_eq,
      hm, hgood, hrem, htail, hab, hprim, hchk => by
    subst hUn_eq; subst hUd_eq; subst hLn_eq; subst hLd_eq; subst hMax_eq; subst hLast_eq; subst hNext_eq
    have hcop_bt : (bVal st exps).Coprime (valF tail) := by
      rw [bVal_eq_valF_zip]
      have hst_lt : ∀ pa ∈ st.zipWith (fun s a => (s.p, a)) exps, ∀ pb ∈ tail, pa.1 < pb.1 := by
        intro pa hpa pb hpb
        obtain ⟨s, hs, _, _, rfl⟩ := mem_zipWith_fst hpa
        exact all_lt_of_lastPrime_lt hm (htail.2.2 pb hpb) s hs
      have aux : ∀ (F1 F2 : List (ℕ × ℕ)), ValidFactors F1 → ValidFactors F2 →
          (∀ pa ∈ F1, ∀ pb ∈ F2, pa.1 < pb.1) → (valF F1).Coprime (valF F2) := by
        intro F1 F2 hF1
        induction F1 with
        | nil => intro _ _; simp [valF]
        | cons pa r1 ih =>
          rcases pa with ⟨p, a⟩
          rcases hF1 with ⟨hp, _, _, hr1⟩
          intro hF2 hlt'
          have h1 : (p ^ a).Coprime (valF F2) :=
            (coprime_valF_of_lt hp hF2 (fun pb hpb => hlt' (p, a) List.mem_cons_self pb hpb)).pow_left a
          have h2 : (valF r1).Coprime (valF F2) :=
            ih hr1 hF2 (fun x hx pb hpb => hlt' x (List.mem_cons_of_mem _ hx) pb hpb)
          simpa [valF] using h1.mul_left h2
      exact aux _ tail (validFactors_zipWith_of_slotsMatch hm) htail.2.1 hst_lt
    have hsig_m : sigma 1 (bVal st exps * valF tail) = bSig st exps * sigF tail := by
      rw [isMultiplicative_sigma.map_mul_of_coprime hcop_bt, bSig_eq_sigma_one_bVal hm,
        sigF_eq_sigma_one htail.2.1]
    have hab_m : 2 * (bVal st exps * valF tail) < bSig st exps * sigF tail := by
      have h1 := hab
      change bVal st exps * valF tail < ∑ d ∈ (bVal st exps * valF tail).properDivisors, d at h1
      have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := bVal st exps * valF tail)
      rw [← sigma_one_apply, hsig_m] at h2
      omega
    have hvalT_gt1 : 1 < valF tail := by
      cases tail with
      | nil => have := htail.1; simp at this; omega
      | cons pa rest =>
        rcases pa with ⟨q, a⟩
        rcases htail.2.1 with ⟨hq, ha, _, hrest⟩
        have h1 : 1 < q ^ a := one_lt_pow₀ hq.one_lt (by omega)
        have h2 : 1 ≤ valF rest := valF_pos hrest
        simp only [valF]
        nlinarith
    have hb_def : bSig st exps < 2 * bVal st exps := by
      have hmem : bVal st exps ∈ (bVal st exps * valF tail).properDivisors :=
        Nat.mem_properDivisors.mpr ⟨dvd_mul_right _ _, by nlinarith [bVal_pos hm]⟩
      have hdef := hprim _ hmem
      change ∑ d ∈ (bVal st exps).properDivisors, d < bVal st exps at hdef
      have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := bVal st exps)
      rw [← sigma_one_apply, ← bSig_eq_sigma_one_bVal hm] at h2
      omega
    obtain ⟨hLd0, hUd0, hLd_le, hL_bnd, hU_bnd⟩ := slots_bounds hm
    unfold checkTreeAux at hchk
    dsimp only at hchk
    have hrem0 : ¬ Nat.beq rem 0 = true := by simp [Nat.beq_eq]; omega
    rw [if_neg hrem0] at hchk
    by_cases hA : Nat.ble (2 * slotsLd st) (slotsLn st) = true
    · exfalso
      simp only [Nat.ble_eq] at hA
      have h1 : 2 * bVal st exps * slotsLd st ≤ bSig st exps * slotsLd st :=
        calc 2 * bVal st exps * slotsLd st
            = 2 * slotsLd st * bVal st exps := by ring
          _ ≤ slotsLn st * bVal st exps := Nat.mul_le_mul_right _ hA
          _ ≤ bSig st exps * slotsLd st := hL_bnd
      have h2 : 2 * bVal st exps ≤ bSig st exps := Nat.le_of_mul_le_mul_right h1 hLd0
      omega
    rw [if_neg hA] at hchk
    have hsplit_fn : ∀ (g' : Option (ℕ × ℕ)),
        OptFamilyCertified st g' →
        (match pickBestFree st with
         | none => false
         | some i =>
           let stF := fixIdx st i
           let stB := bumpIdx st i
           checkTreeAux fuel stF rem (slotsUnF stF) (slotsUdF stF) (slotsLn st) (slotsLd st)
             (slotsMaxSig st) (lastPrime st) (nextPrimeAfter (lastPrime st)) g' &&
           checkTreeAux fuel stB rem (slotsUn st) (slotsUd st) (slotsLnF stB) (slotsLdF stB)
             (slotsMaxSig stB) (lastPrime st) (nextPrimeAfter (lastPrime st)) g') = true →
        (bVal st exps * valF tail).Pseudoperfect := by
      intro g' hg' hsp
      cases hpick : pickBestFree st with
      | none => rw [hpick] at hsp; simp at hsp
      | some i =>
        rw [hpick] at hsp
        simp only [Bool.and_eq_true] at hsp
        obtain ⟨s, hget, hfree⟩ := pickBestFree_sound hpick
        rcases split_free_slot hm hget hfree with hm_fix | hm_bmp
        · have hg_fix : OptFamilyCertified (fixIdx st i) g' := optFamilyCertified_fixIdx hg'
          have hbv := bVal_eq_of_map_p_eq (exps := exps) (map_p_fixIdx st i)
          have hlp := lastPrime_eq_of_map_p_eq (map_p_fixIdx st i)
          rw [← hbv] at hab hprim ⊢
          rw [← hlp] at htail
          exact checkTreeAux_sound fuel (slotsUnF_eq _) (slotsUdF_eq _)
            (slotsLn_fixIdx st i).symm (slotsLd_fixIdx st i).symm (slotsMaxSig_fixIdx st i).symm
            hlp.symm rfl hm_fix hg_fix hrem htail hab hprim hsp.1
        · have hg_bmp : OptFamilyCertified (bumpIdx st i) g' := optFamilyCertified_bumpIdx hm hget hfree hg'
          have hbv := bVal_eq_of_map_p_eq (exps := exps) (map_p_bumpIdx st i)
          have hlp := lastPrime_eq_of_map_p_eq (map_p_bumpIdx st i)
          rw [← hbv] at hab hprim ⊢
          rw [← hlp] at htail
          exact checkTreeAux_sound fuel (slotsUn_bumpIdx_of_free hget hfree).symm
            (slotsUd_bumpIdx_of_free hget hfree).symm (slotsLnF_eq _) (slotsLdF_eq _) rfl
            hlp.symm rfl hm_bmp hg_bmp hrem htail hab hprim hsp.2
    by_cases hrem1 : Nat.beq rem 1 = true
    · -- Case rem == 1: tail = [(q, e)]
      rw [if_pos hrem1] at hchk
      have hrem_eq : rem = 1 := Nat.eq_of_beq_eq_true hrem1
      subst hrem_eq
      set x := nextPrimeAfter (lastPrime st)
      by_cases hdead1 : Nat.ble (slotsUn st * x) (2 * slotsUd st * (x - 1)) = true
      · exfalso
        simp only [Nat.ble_eq] at hdead1
        have htd1 : tailDeadAux (slotsUn st) (slotsUd st) (lastPrime st) 1 = true := by
          simp only [tailDeadAux, decide_eq_true_eq]
          change slotsUn st * x ≤ 2 * (slotsUd st * (x - 1))
          rw [← mul_assoc]; exact hdead1
        have hlt := tailDeadAux_sound (lastPrime_ge_two hm) le_rfl hUd0 htail htd1 (bVal_pos hm) hU_bnd
        omega
      rw [if_neg hdead1] at hchk
      cases tail with
      | nil => have := htail.1; simp at this
      | cons pa rest =>
        rcases pa with ⟨q, e⟩
        have hrest_nil : rest = [] := by
          have := htail.1; simp at this
          exact this
        subst hrest_nil
        rcases htail.2.1 with ⟨hq, he, _, _⟩
        have hlast_q : lastPrime st < q := htail.2.2 (q, e) List.mem_cons_self
        have hq3 : 3 ≤ q := by have := lastPrime_ge_two hm; omega
        have hlt_all : ∀ s ∈ st, s.p < q := all_lt_of_lastPrime_lt hm hlast_q
        have hval_eq : valF [(q, e)] = q ^ e := by simp [valF]
        have hsig_eq : sigF [(q, e)] = sigmaPP q e := by simp [sigF]
        obtain ⟨hlast_x, hcomp_x⟩ := nextPrimeAfter_spec_odd (lastPrime_ge_two hm)
        have hx0 : 0 < x := by have := lastPrime_ge_two hm; omega
        have hxq : x ≤ q := by
          by_contra hlt'; exact hcomp_x q hlast_q (by omega) hq
        rw [hval_eq] at hab hprim ⊢
        rw [hval_eq, hsig_eq] at hab_m
        by_cases hUn : Nat.blt (slotsUn st) (2 * slotsUd st) = true
        · rw [if_pos hUn] at hchk
          have hUn_lt : slotsUn st < 2 * slotsUd st := by simpa [Nat.blt_eq] using hUn
          set qMax := (2 * slotsUd st - 1) / (2 * slotsUd st - slotsUn st)
          have hq_le_qMax : q ≤ qMax := by
            have h1 := tail_head_le_pMax (Un := slotsUn st) (Ud := slotsUd st) (rem := 1)
              (p := q) (a := e) (rest := []) (bS := bSig st exps) (bV := bVal st exps)
              le_rfl (slotsUn_pos hm) hUd0 hUn_lt rfl ⟨hq, he, fun _ hx => by simp at hx, trivial⟩
              hq3 (bVal_pos hm) hU_bnd (by simpa [valF, sigF] using hab_m)
            simpa [qMax] using h1
          by_cases hqm : Nat.ble qMax (lastPrime st) = true
          · exfalso; simp only [Nat.ble_eq] at hqm; omega
          rw [if_neg hqm] at hchk
          have hprev_le : ∀ (N : ℕ), q ≤ N →
              q ≤ (let r := prevPrimeLE N; if Nat.blt r 2 then N else r) := by
            intro N hqN
            dsimp only
            by_cases hlt2 : Nat.blt (prevPrimeAux N 120) 2 = true
            · simpa [prevPrimeLE, hlt2] using hqN
            · rw [prevPrimeLE, if_neg hlt2]
              have hge2 : 2 ≤ prevPrimeAux N 120 := by simp [Nat.blt_eq] at hlt2; omega
              obtain ⟨_, hnot⟩ := allComposite_of_prevPrimeAux (k := N) (fuel := 120) hge2
              by_contra hgt
              exact hnot q (by omega) hqN hq
          by_cases he1 : Nat.blt (2 * slotsUd st * x) (slotsUn st * (x + 1)) = true
          · rw [if_pos he1] at hchk
            by_cases hnpM : Nat.ble (2 * slotsLd st * slotsMaxSig st * qMax)
                (slotsLn st * (slotsMaxSig st - 1) * (qMax + 1)) = true
            · exfalso
              exact checkNonPrimMaxSig_false_of_prim hm hq hq_le_qMax he hlt_all hprim
                (by simpa [pow_one, sigmaPP] using hnpM)
            rw [if_neg hnpM] at hchk
            refine with_good_sound hchk hm hgood (fun g' hg' hgo => ?_)
            by_cases hunifM : uniformGiven st g' (slotsUn st) (slotsUd st) (slotsLn st) (slotsLd st) 1 x qMax = true
            · exact uniformGiven_sound hm hg' hq hq3 hlast_q hq_le_qMax hx0 hxq he le_rfl he hab hprim
                (by simpa [pow_one] using hunifM)
            rw [if_neg hunifM] at hgo
            have hts : ∀ (w b1 b2 : Bool),
                (if (if w then false else b1) then true else b2) = true →
                b1 = true ∨ b2 = true := by
              intro w b1 b2 h
              cases w <;> cases b1 <;> simp at h ⊢ <;> exact h
            rcases hts _ _ _ hgo with hgo | hgo
            · set Qlim0 := prevPrimeLE qMax
              set Qlim := if Nat.blt Qlim0 2 then qMax else Qlim0
              have hq_le_Qlim : q ≤ Qlim := hprev_le qMax hq_le_qMax
              by_cases hQl : Nat.ble Qlim (lastPrime st) = true
              · exfalso; simp only [Nat.ble_eq] at hQl; omega
              rw [if_neg hQl] at hgo
              by_cases hsh : (Nat.blt Qlim qMax &&
                  (Nat.ble (2 * slotsLd st * slotsMaxSig st * Qlim) (slotsLn st * (slotsMaxSig st - 1) * (Qlim + 1)) ||
                   uniformGiven st g' (slotsUn st) (slotsUd st) (slotsLn st) (slotsLd st) 1 x Qlim)) = true
              · simp only [Bool.and_eq_true, Bool.or_eq_true] at hsh
                rcases hsh.2 with hnpQ | hunifQ
                · exfalso
                  exact checkNonPrimMaxSig_false_of_prim hm hq hq_le_Qlim he hlt_all hprim
                    (by simpa [pow_one, sigmaPP] using hnpQ)
                · exact uniformGiven_sound hm hg' hq hq3 hlast_q hq_le_Qlim hx0 hxq he le_rfl he hab hprim
                    (by simpa [pow_one] using hunifQ)
              rw [if_neg hsh] at hgo
              by_cases hspQ : (if Nat.beq Qlim qMax && checkFamilyQ st g' (slotsUn st) (slotsUd st)
                  (slotsLn st) (slotsLd st) (slotsMaxSig st) qMax then
                  let Q10 := prevPrimeLE (qMax - 1)
                  let Q1 := if Nat.blt Q10 2 then qMax - 1 else Q10
                  if Nat.ble Q1 (lastPrime st) then true
                  else Nat.ble (2 * slotsLd st * slotsMaxSig st * Q1) (slotsLn st * (slotsMaxSig st - 1) * (Q1 + 1)) ||
                       uniformGiven st g' (slotsUn st) (slotsUd st) (slotsLn st) (slotsLd st) 1 x Q1
                else false) = true
              · by_cases hqmc : (Nat.beq Qlim qMax && checkFamilyQ st g' (slotsUn st) (slotsUd st)
                    (slotsLn st) (slotsLd st) (slotsMaxSig st) qMax) = true
                · rw [if_pos hqmc] at hspQ
                  simp only [Bool.and_eq_true] at hqmc
                  by_cases hqqm : q = qMax
                  · subst hqqm
                    exact checkFamilyQ_sound hm hg' hq hq3 he hlt_all hab hprim hqmc.2
                  · set Q10 := prevPrimeLE (qMax - 1)
                    set Q1 := if Nat.blt Q10 2 then qMax - 1 else Q10
                    have hq_le_Q1 : q ≤ Q1 := hprev_le (qMax - 1) (by omega)
                    by_cases hQ1l : Nat.ble Q1 (lastPrime st) = true
                    · simp only [Nat.ble_eq] at hQ1l; exfalso; omega
                    · rw [if_neg hQ1l] at hspQ
                      simp only [Bool.or_eq_true] at hspQ
                      rcases hspQ with hnp1 | hunif1
                      · exfalso
                        exact checkNonPrimMaxSig_false_of_prim hm hq hq_le_Q1 he hlt_all hprim
                          (by rw [pow_one, sigmaPP, sigmaPP, one_mul]; exact hnp1)
                      · exact uniformGiven_sound hm hg' hq hq3 hlast_q hq_le_Q1 hx0 hxq he le_rfl he hab hprim
                          (by rw [pow_one]; exact hunif1)
                · rw [if_neg hqmc] at hspQ; simp at hspQ
              rw [if_neg hspQ] at hgo
              by_cases hfam : (Nat.ble (Qlim - lastPrime st) 16 &&
                  checkOddRange (checkFamilyQ st g' (slotsUn st) (slotsUd st) (slotsLn st) (slotsLd st)
                    (slotsMaxSig st)) 6 (lastPrime st + 1) Qlim) = true
              · simp only [Bool.and_eq_true] at hfam
                have hfq := checkOddRange_sound hfam.2 hq hq3 (by omega) hq_le_Qlim
                exact checkFamilyQ_sound hm hg' hq hq3 he hlt_all hab hprim hfq
              rw [if_neg hfam] at hgo
              by_cases hfix : st.all Slot.fixed = true
              · rw [if_pos hfix] at hgo
                have hcq := checkOddRange_sound hgo hq hq3 (by omega) hq_le_Qlim
                exact checkConcreteQ_sound hm hfix hg' hq hq3 he hlt_all hab hprim hcq
              · rw [if_neg hfix] at hgo; simp at hgo
            · rw [← hval_eq] at hab hprim ⊢
              exact hsplit_fn g' hg' hgo
          · rw [if_neg he1] at hchk
            cases hmin : findMinExpStrict (slotsUn st) (slotsUd st) x 60 1 x (x + 1) with
            | none => rw [hmin] at hchk; simp at hchk
            | some res =>
              rcases res with ⟨eMin, xP, sigX⟩
              rw [hmin] at hchk
              dsimp only at hchk
              obtain ⟨heMin1, hxP, _, _⟩ :=
                findMinExpStrict_sound (by simp) (by simp [sigmaPP]) (fun t h1 h2 => by omega) hmin
              have he_ge : eMin ≤ e := exp_ge_of_findMinExpStrict hm hx0 hxq he hab_m hmin
              subst hxP
              by_cases hnpM : Nat.ble (2 * slotsLd st * slotsMaxSig st * qMax ^ eMin)
                  (slotsLn st * (slotsMaxSig st - 1) * sigmaPP qMax eMin) = true
              · exfalso
                exact checkNonPrimMaxSig_false_of_prim hm hq hq_le_qMax he_ge hlt_all hprim hnpM
              rw [if_neg hnpM] at hchk
              refine with_good_sound hchk hm hgood (fun g' hg' hgo => ?_)
              by_cases hunifM : uniformGiven st g' (slotsUn st) (slotsUd st) (slotsLn st) (slotsLd st)
                  eMin (x ^ eMin) qMax = true
              · exact uniformGiven_sound hm hg' hq hq3 hlast_q hq_le_qMax hx0 hxq he heMin1 he_ge hab hprim hunifM
              rw [if_neg hunifM] at hgo
              set Qlim0 := prevPrimeLE qMax
              set Qlim := if Nat.blt Qlim0 2 then qMax else Qlim0
              have hq_le_Qlim : q ≤ Qlim := hprev_le qMax hq_le_qMax
              by_cases hQl : Nat.ble Qlim (lastPrime st) = true
              · exfalso; simp only [Nat.ble_eq] at hQl; omega
              rw [if_neg hQl] at hgo
              by_cases hsh : (Nat.blt Qlim qMax &&
                  (Nat.ble (2 * slotsLd st * slotsMaxSig st * Qlim ^ eMin)
                    (slotsLn st * (slotsMaxSig st - 1) * sigmaPP Qlim eMin) ||
                   uniformGiven st g' (slotsUn st) (slotsUd st) (slotsLn st) (slotsLd st) eMin (x ^ eMin) Qlim)) = true
              · simp only [Bool.and_eq_true, Bool.or_eq_true] at hsh
                rcases hsh.2 with hnpQ | hunifQ
                · exfalso
                  exact checkNonPrimMaxSig_false_of_prim hm hq hq_le_Qlim he_ge hlt_all hprim hnpQ
                · exact uniformGiven_sound hm hg' hq hq3 hlast_q hq_le_Qlim hx0 hxq he heMin1 he_ge hab hprim hunifQ
              rw [if_neg hsh] at hgo
              by_cases hspQ : (if Nat.beq Qlim qMax && checkFamilyQ st g' (slotsUn st) (slotsUd st)
                  (slotsLn st) (slotsLd st) (slotsMaxSig st) qMax then
                  let Q10 := prevPrimeLE (qMax - 1)
                  let Q1 := if Nat.blt Q10 2 then qMax - 1 else Q10
                  if Nat.ble Q1 (lastPrime st) then true
                  else
                    Nat.ble (2 * slotsLd st * slotsMaxSig st * Q1 ^ eMin)
                      (slotsLn st * (slotsMaxSig st - 1) * sigmaPP Q1 eMin) ||
                    uniformGiven st g' (slotsUn st) (slotsUd st) (slotsLn st) (slotsLd st) eMin (x ^ eMin) Q1
                else false) = true
              · by_cases hqmc : (Nat.beq Qlim qMax && checkFamilyQ st g' (slotsUn st) (slotsUd st)
                    (slotsLn st) (slotsLd st) (slotsMaxSig st) qMax) = true
                · rw [if_pos hqmc] at hspQ
                  simp only [Bool.and_eq_true] at hqmc
                  by_cases hqqm : q = qMax
                  · subst hqqm
                    exact checkFamilyQ_sound hm hg' hq hq3 he hlt_all hab hprim hqmc.2
                  · set Q10 := prevPrimeLE (qMax - 1)
                    set Q1 := if Nat.blt Q10 2 then qMax - 1 else Q10
                    have hq_le_Q1 : q ≤ Q1 := hprev_le (qMax - 1) (by omega)
                    by_cases hQ1l : Nat.ble Q1 (lastPrime st) = true
                    · simp only [Nat.ble_eq] at hQ1l; exfalso; omega
                    · rw [if_neg hQ1l] at hspQ
                      simp only [Bool.or_eq_true] at hspQ
                      rcases hspQ with hnp1 | hunif1
                      · exfalso
                        exact checkNonPrimMaxSig_false_of_prim hm hq hq_le_Q1 he_ge hlt_all hprim hnp1
                      · exact uniformGiven_sound hm hg' hq hq3 hlast_q hq_le_Q1 hx0 hxq he heMin1 he_ge hab hprim hunif1
                · rw [if_neg hqmc] at hspQ; simp at hspQ
              rw [if_neg hspQ] at hgo
              by_cases hfam : (Nat.ble (Qlim - lastPrime st) 16 &&
                  checkOddRange (checkFamilyQ st g' (slotsUn st) (slotsUd st) (slotsLn st) (slotsLd st)
                    (slotsMaxSig st)) 6 (lastPrime st + 1) Qlim) = true
              · simp only [Bool.and_eq_true] at hfam
                have hfq := checkOddRange_sound hfam.2 hq hq3 (by omega) hq_le_Qlim
                exact checkFamilyQ_sound hm hg' hq hq3 he hlt_all hab hprim hfq
              rw [if_neg hfam] at hgo
              by_cases hfix : st.all Slot.fixed = true
              · rw [if_pos hfix] at hgo
                have hcq := checkOddRange_sound hgo hq hq3 (by omega) hq_le_Qlim
                exact checkConcreteQ_sound hm hfix hg' hq hq3 he hlt_all hab hprim hcq
              · rw [if_neg hfix] at hgo
                rw [← hval_eq] at hab hprim ⊢
                exact hsplit_fn g' hg' hgo
        · rw [if_neg hUn] at hchk
          rw [← hval_eq] at hab hprim ⊢
          exact with_good_sound hchk hm hgood hsplit_fn
    · -- Case rem ≥ 2: tail = (p, a) :: rest
      rw [if_neg hrem1] at hchk
      have hrem2 : 2 ≤ rem := by simp [Nat.beq_eq] at hrem1; omega
      by_cases hB : tailDeadAux (slotsUn st) (slotsUd st) (lastPrime st) rem = true
      · exfalso
        have hlt := tailDeadAux_sound (lastPrime_ge_two hm) hrem hUd0 htail hB (bVal_pos hm) hU_bnd
        omega
      rw [if_neg hB] at hchk
      refine with_good_sound hchk hm hgood (fun g' hg' hgo => ?_)
      by_cases hUn : Nat.blt (slotsUn st) (2 * slotsUd st) = true
      · rw [if_pos hUn] at hgo
        have hUn_lt : slotsUn st < 2 * slotsUd st := by simpa [Nat.blt_eq] using hUn
        cases tail with
        | nil => have := htail.1; simp at this; omega
        | cons pa rest =>
          rcases pa with ⟨p, a⟩
          rcases htail.2.1 with ⟨hp, ha, hprest, hvf_rest⟩
          have hlast_p : lastPrime st < p := htail.2.2 (p, a) List.mem_cons_self
          have hp3 : 3 ≤ p := by have := lastPrime_ge_two hm; omega
          have hp_le : p ≤ (2 * slotsUd st * rem - 1) / (2 * slotsUd st - slotsUn st) :=
            tail_head_le_pMax hrem (slotsUn_pos hm) hUd0 hUn_lt htail.1 ⟨hp, ha, hprest, hvf_rest⟩
              hp3 (bVal_pos hm) hU_bnd hab_m
          have hfp := checkOddRange_sound hgo hp hp3 (by omega) hp_le
          have hns : hasSmallFactor p = false := by
            cases hsf : hasSmallFactor p
            · rfl
            · exact absurd hp (not_prime_of_hasSmallFactor hsf)
          rw [hns] at hfp
          simp only [Bool.false_eq_true, ↓reduceIte] at hfp
          have htail_rest : TailMatch p (rem - 1) rest :=
            ⟨by have := htail.1; simp at this; omega, hvf_rest, hprest⟩
          by_cases htd : tailDeadAux (slotsUn st * p) (slotsUd st * (p - 1)) p (rem - 1) = true
          · exfalso
            have hsig_p : sigmaPP p a * (p - 1) ≤ p * p ^ a := le_of_lt (sigmaPP_lt_limit hp.one_lt a)
            have hUb' : (bSig st exps * sigmaPP p a) * (slotsUd st * (p - 1)) ≤
                (slotsUn st * p) * (bVal st exps * p ^ a) := by
              calc (bSig st exps * sigmaPP p a) * (slotsUd st * (p - 1))
                  = (bSig st exps * slotsUd st) * (sigmaPP p a * (p - 1)) := by ring
                _ ≤ (slotsUn st * bVal st exps) * (p * p ^ a) := Nat.mul_le_mul hU_bnd hsig_p
                _ = (slotsUn st * p) * (bVal st exps * p ^ a) := by ring
            have hdead := tailDeadAux_sound (by omega) (by omega) (Nat.mul_pos hUd0 (by omega))
              htail_rest htd (Nat.mul_pos (bVal_pos hm) (pow_pos hp.pos a)) hUb'
            simp only [valF, sigF] at hab_m
            have h1 : bSig st exps * (sigmaPP p a * sigF rest) = (bSig st exps * sigmaPP p a) * sigF rest := by ring
            have h2 : bVal st exps * (p ^ a * valF rest) = (bVal st exps * p ^ a) * valF rest := by ring
            omega
          rw [if_neg htd] at hfp
          have hlt_all : ∀ s ∈ st, s.p < p := all_lt_of_lastPrime_lt hm hlast_p
          have hm' : SlotsMatch (st ++ [mkSlot p]) (exps ++ [a]) :=
            slotsMatch_append_mkSlot hm hp hp3 ha hlt_all
          have hbv' : bVal (st ++ [mkSlot p]) (exps ++ [a]) * valF rest = bVal st exps * valF ((p, a) :: rest) := by
            rw [bVal_append_mkSlot st exps p a hm.1.length_eq]
            simp only [valF]; ring
          have hgood2 : OptFamilyCertified (st ++ [mkSlot p]) (propagateGood g' p (slotsLn st) (slotsLd st)) := by
            unfold propagateGood
            cases hge : g' with
            | none => trivial
            | some lg =>
              rcases lg with ⟨L, G⟩
              rw [hge] at hg'
              dsimp only
              split_ifs with hc
              · simp only [Bool.and_eq_true, Nat.ble_eq] at hc
                exact familyCertified_append_prime hm hp hp3 hlt_all hg' hc.1.2 hc.2
              · trivial
          have htail' : TailMatch (lastPrime (st ++ [mkSlot p])) (rem - 1) rest := by
            rw [lastPrime_append_mkSlot]; exact htail_rest
          rw [← hbv'] at hab hprim ⊢
          cases hpg : propagateGood g' p (slotsLn st) (slotsLd st) with
          | none =>
            rw [hpg] at hfp hgood2
            exact checkTreeAux_sound fuel (slotsUn_append_mkSlot st p).symm (slotsUd_append_mkSlot st p).symm
              (slotsLn_append_mkSlot st p).symm (slotsLd_append_mkSlot st p).symm
              (slotsMaxSig_append_mkSlot st p).symm (lastPrime_append_mkSlot st p).symm rfl
              hm' hgood2 (by omega) htail' hab hprim hfp
          | some lg2 =>
            rw [hpg] at hfp hgood2
            exact checkTreeAux_sound fuel (slotsUn_append_mkSlot st p).symm (slotsUd_append_mkSlot st p).symm
              (slotsLn_append_mkSlot st p).symm (slotsLd_append_mkSlot st p).symm
              (slotsMaxSig_append_mkSlot st p).symm (lastPrime_append_mkSlot st p).symm rfl
              hm' hgood2 (by omega) htail' hab hprim hfp
      · rw [if_neg hUn] at hgo
        exact hsplit_fn g' hg' hgo

private lemma checkTree_sound (fuel : ℕ) {st : List Slot} {exps : List ℕ} {rem : ℕ}
    {good : Option (ℕ × ℕ)} {tail : List (ℕ × ℕ)}
    (hm : SlotsMatch st exps)
    (hgood : OptFamilyCertified st good)
    (hrem : 1 ≤ rem)
    (htail : TailMatch (lastPrime st) rem tail)
    (hab : (bVal st exps * valF tail).Abundant)
    (hprim : ∀ d ∈ (bVal st exps * valF tail).properDivisors, d.Deficient)
    (hchk : checkTree fuel st rem good = true) :
    (bVal st exps * valF tail).Pseudoperfect :=
  checkTreeAux_sound fuel (slotsUnF_eq st) (slotsUdF_eq st) (slotsLnF_eq st) (slotsLdF_eq st)
    rfl rfl rfl hm hgood hrem htail hab hprim hchk

private def checkPrimeRange (fuel : ℕ) (st : List Slot) (rem lo hi : ℕ) : Bool :=
  let Un := slotsUnF st
  let Ud := slotsUdF st
  let Ln := slotsLnF st
  let Ld := slotsLdF st
  let maxSig := slotsMaxSig st
  let go (g' : Option (ℕ × ℕ)) : Bool :=
    checkOddRange (fun p =>
      if hasSmallFactor p then true
      else if tailDeadAux (Un * p) (Ud * (p - 1)) p (rem - 1) then true
      else
        let mSig' := if Nat.ble maxSig (p + 1) then p + 1 else maxSig
        match propagateGood g' p Ln Ld with
        | none => checkTreeAux fuel (st ++ [mkSlot p]) (rem - 1) (Un * p) (Ud * (p - 1)) (Ln * (p + 1)) (Ld * p) mSig' p (nextPrimeAfter p) none
        | some lg2 => checkTreeAux fuel (st ++ [mkSlot p]) (rem - 1) (Un * p) (Ud * (p - 1)) (Ln * (p + 1)) (Ld * p) mSig' p (nextPrimeAfter p) (some lg2))
      12 lo hi
  if Nat.ble 3 st.length then
    match findGoodFamily st with
    | none => go none
    | some lg => go (some lg)
  else go none

private lemma checkPrimeRange_sound {fuel : ℕ} {st : List Slot} {exps : List ℕ}
    {rem lo hi p a : ℕ} {rest : List (ℕ × ℕ)}
    (hm : SlotsMatch st exps) (hrem : 2 ≤ rem)
    (htail : TailMatch (lastPrime st) rem ((p, a) :: rest))
    (hp_lo : lo ≤ p) (hp_hi : p ≤ hi)
    (hab : (bVal st exps * valF ((p, a) :: rest)).Abundant)
    (hprim : ∀ d ∈ (bVal st exps * valF ((p, a) :: rest)).properDivisors, d.Deficient)
    (hchk : checkPrimeRange fuel st rem lo hi = true) :
    (bVal st exps * valF ((p, a) :: rest)).Pseudoperfect := by
  unfold checkPrimeRange at hchk
  rw [slotsUnF_eq, slotsUdF_eq, slotsLnF_eq, slotsLdF_eq] at hchk
  have hrun : ∀ g', OptFamilyCertified st g' →
      checkOddRange (fun p =>
        if hasSmallFactor p then true
        else if tailDeadAux (slotsUn st * p) (slotsUd st * (p - 1)) p (rem - 1) then true
        else
          let mSig' := if Nat.ble (slotsMaxSig st) (p + 1) then p + 1 else slotsMaxSig st
          match propagateGood g' p (slotsLn st) (slotsLd st) with
          | none => checkTreeAux fuel (st ++ [mkSlot p]) (rem - 1) (slotsUn st * p) (slotsUd st * (p - 1))
              (slotsLn st * (p + 1)) (slotsLd st * p) mSig' p (nextPrimeAfter p) none
          | some lg2 => checkTreeAux fuel (st ++ [mkSlot p]) (rem - 1) (slotsUn st * p) (slotsUd st * (p - 1))
              (slotsLn st * (p + 1)) (slotsLd st * p) mSig' p (nextPrimeAfter p) (some lg2))
        12 lo hi = true →
      (bVal st exps * valF ((p, a) :: rest)).Pseudoperfect := by
    intro g' hg' hgo
    rcases htail.2.1 with ⟨hp, ha, hprest, hvf_rest⟩
    have hlast_p : lastPrime st < p := htail.2.2 (p, a) List.mem_cons_self
    have hp3 : 3 ≤ p := by have := lastPrime_ge_two hm; omega
    have hfp := checkOddRange_sound hgo hp hp3 hp_lo hp_hi
    have hns : hasSmallFactor p = false := by
      cases hsf : hasSmallFactor p
      · rfl
      · exact absurd hp (not_prime_of_hasSmallFactor hsf)
    rw [hns] at hfp
    simp only [Bool.false_eq_true, ↓reduceIte] at hfp
    have htail_rest : TailMatch p (rem - 1) rest :=
      ⟨by have := htail.1; simp at this; omega, hvf_rest, hprest⟩
    obtain ⟨_, hUd0, _, _, hU_bnd⟩ := slots_bounds hm
    by_cases htd : tailDeadAux (slotsUn st * p) (slotsUd st * (p - 1)) p (rem - 1) = true
    · exfalso
      have hcop_bt : (bVal st exps).Coprime (valF ((p, a) :: rest)) := by
        rw [bVal_eq_valF_zip]
        have aux : ∀ (F1 F2 : List (ℕ × ℕ)), ValidFactors F1 → ValidFactors F2 →
            (∀ pa ∈ F1, ∀ pb ∈ F2, pa.1 < pb.1) → (valF F1).Coprime (valF F2) := by
          intro F1 F2 hF1; induction F1 with
          | nil => intro _ _; simp [valF]
          | cons pa r1 ih =>
            rcases pa with ⟨p1, a1⟩; rcases hF1 with ⟨hp1, _, _, hr1⟩; intro hF2 hlt'
            simpa [valF] using ((coprime_valF_of_lt hp1 hF2 (fun pb hpb => hlt' (p1, a1) List.mem_cons_self pb hpb)).pow_left a1).mul_left
              (ih hr1 hF2 (fun x hx pb hpb => hlt' x (List.mem_cons_of_mem _ hx) pb hpb))
        refine aux _ _ (validFactors_zipWith_of_slotsMatch hm) htail.2.1 (fun pa hpa pb hpb => ?_)
        obtain ⟨s, hs, _, _, rfl⟩ := mem_zipWith_fst hpa
        exact all_lt_of_lastPrime_lt hm (htail.2.2 pb hpb) s hs
      have hsig_m : sigma 1 (bVal st exps * valF ((p, a) :: rest)) = bSig st exps * sigF ((p, a) :: rest) := by
        rw [isMultiplicative_sigma.map_mul_of_coprime hcop_bt, bSig_eq_sigma_one_bVal hm,
          sigF_eq_sigma_one htail.2.1]
      have hab_m : 2 * (bVal st exps * valF ((p, a) :: rest)) < bSig st exps * sigF ((p, a) :: rest) := by
        have h1 := hab
        change bVal st exps * valF ((p, a) :: rest) < ∑ d ∈ (bVal st exps * valF ((p, a) :: rest)).properDivisors, d at h1
        have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := bVal st exps * valF ((p, a) :: rest))
        rw [← sigma_one_apply, hsig_m] at h2
        omega
      have hsig_p : sigmaPP p a * (p - 1) ≤ p * p ^ a := le_of_lt (sigmaPP_lt_limit hp.one_lt a)
      have hUb' : (bSig st exps * sigmaPP p a) * (slotsUd st * (p - 1)) ≤
          (slotsUn st * p) * (bVal st exps * p ^ a) := by
        calc (bSig st exps * sigmaPP p a) * (slotsUd st * (p - 1))
            = (bSig st exps * slotsUd st) * (sigmaPP p a * (p - 1)) := by ring
          _ ≤ (slotsUn st * bVal st exps) * (p * p ^ a) := Nat.mul_le_mul hU_bnd hsig_p
          _ = (slotsUn st * p) * (bVal st exps * p ^ a) := by ring
      have hdead := tailDeadAux_sound (by omega) (by omega) (Nat.mul_pos hUd0 (by omega))
        htail_rest htd (Nat.mul_pos (bVal_pos hm) (pow_pos hp.pos a)) hUb'
      simp only [valF, sigF] at hab_m
      have h1 : bSig st exps * (sigmaPP p a * sigF rest) = (bSig st exps * sigmaPP p a) * sigF rest := by ring
      have h2 : bVal st exps * (p ^ a * valF rest) = (bVal st exps * p ^ a) * valF rest := by ring
      omega
    rw [if_neg htd] at hfp
    have hlt_all : ∀ s ∈ st, s.p < p := all_lt_of_lastPrime_lt hm hlast_p
    have hm' : SlotsMatch (st ++ [mkSlot p]) (exps ++ [a]) :=
      slotsMatch_append_mkSlot hm hp hp3 ha hlt_all
    have hbv' : bVal (st ++ [mkSlot p]) (exps ++ [a]) * valF rest = bVal st exps * valF ((p, a) :: rest) := by
      rw [bVal_append_mkSlot st exps p a hm.1.length_eq]
      simp only [valF]; ring
    have hgood2 : OptFamilyCertified (st ++ [mkSlot p]) (propagateGood g' p (slotsLn st) (slotsLd st)) := by
      unfold propagateGood
      cases hge : g' with
      | none => trivial
      | some lg =>
        rcases lg with ⟨L, G⟩
        rw [hge] at hg'
        dsimp only
        split_ifs with hc
        · simp only [Bool.and_eq_true, Nat.ble_eq] at hc
          exact familyCertified_append_prime hm hp hp3 hlt_all hg' hc.1.2 hc.2
        · trivial
    have htail' : TailMatch (lastPrime (st ++ [mkSlot p])) (rem - 1) rest := by
      rw [lastPrime_append_mkSlot]; exact htail_rest
    rw [← hbv'] at hab hprim ⊢
    cases hpg : propagateGood g' p (slotsLn st) (slotsLd st) with
    | none =>
      rw [hpg] at hfp hgood2
      exact checkTreeAux_sound fuel (slotsUn_append_mkSlot st p).symm (slotsUd_append_mkSlot st p).symm
        (slotsLn_append_mkSlot st p).symm (slotsLd_append_mkSlot st p).symm
        (slotsMaxSig_append_mkSlot st p).symm (lastPrime_append_mkSlot st p).symm rfl
        hm' hgood2 (by omega) htail' hab hprim hfp
    | some lg2 =>
      rw [hpg] at hfp hgood2
      exact checkTreeAux_sound fuel (slotsUn_append_mkSlot st p).symm (slotsUd_append_mkSlot st p).symm
        (slotsLn_append_mkSlot st p).symm (slotsLd_append_mkSlot st p).symm
        (slotsMaxSig_append_mkSlot st p).symm (lastPrime_append_mkSlot st p).symm rfl
        hm' hgood2 (by omega) htail' hab hprim hfp
  dsimp only at hchk
  split_ifs at hchk with hc
  · cases hfg : findGoodFamily st with
    | none => rw [hfg] at hchk; exact hrun none trivial hchk
    | some lg => rw [hfg] at hchk; exact hrun (some lg) (findGoodFamily_sound hm hfg) hchk
  · exact hrun none trivial hchk

/- ### Section 8: Kernel Verification Chunks and Main Theorem -/

private lemma check_s1 : checkTree 55 [] 1 none = true := rfl
private lemma check_s2 : checkTree 55 [] 2 none = true := rfl
private lemma check_s3 : checkTree 55 [] 3 none = true := rfl
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 4096 in
private lemma check_s4 : checkTree 55 [] 4 none = true := rfl

private lemma dead_s5_p1 : tailDeadAux 1 1 4 5 = true := rfl
private lemma dead_s5_3_p2 : tailDeadAux 3 2 12 4 = true := rfl
private lemma dead_s5_3_11_p3 : tailDeadAux 33 20 16 3 = true := rfl
private lemma dead_s5_3_7_p3 : tailDeadAux 21 12 22 3 = true := rfl
private lemma dead_s5_3_5_p3 : tailDeadAux 15 8 42 3 = true := rfl
private lemma dead_s5_3_5_17_p4 : tailDeadAux 255 128 508 2 = true := rfl
private lemma dead_s5_3_5_19_p4 : tailDeadAux 285 144 182 2 = true := rfl

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_11_13 :
    checkTree 55 [mkSlot 3, mkSlot 11, mkSlot 13] 2 none = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_7 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 7] 3 11 19 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_7 :
    checkTree 55 [mkSlot 3, mkSlot 5, mkSlot 7] 2 none = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_11 :
    checkTree 55 [mkSlot 3, mkSlot 5, mkSlot 11] 2 none = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_13 :
    checkTree 55 [mkSlot 3, mkSlot 5, mkSlot 13] 2 none = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_17_c1 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 17] 2 19 137 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_17_c2 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 17] 2 138 199 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_17_c3 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 17] 2 200 251 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_17_c4 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 17] 2 252 263 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_17_c5 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 17] 2 264 281 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_17_c6 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 17] 2 282 331 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_17_c7 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 17] 2 332 397 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_17_c8 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 17] 2 398 508 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_19_c1 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 19] 2 23 89 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_19_c2 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 19] 2 90 107 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_19_c3 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5, mkSlot 19] 2 108 182 = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_23 :
    checkTree 55 [mkSlot 3, mkSlot 5, mkSlot 23] 2 none = true := rfl
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
private lemma check_s5_3_5_24_42 :
    checkPrimeRange 55 [mkSlot 3, mkSlot 5] 3 24 42 = true := rfl

private lemma not_abundant_of_tailDead {st : List Slot} {exps : List ℕ} {last rem : ℕ}
    {tail : List (ℕ × ℕ)}
    (hm : SlotsMatch st exps) (hlast : 2 ≤ last) (hrem : 1 ≤ rem)
    (hlt_st : ∀ s ∈ st, ∀ pa ∈ tail, s.p < pa.1)
    (htail : TailMatch last rem tail)
    (hdead : tailDeadAux (slotsUn st) (slotsUd st) last rem = true)
    (hab : (bVal st exps * valF tail).Abundant) : False := by
  have hcop : (bVal st exps).Coprime (valF tail) := by
    rw [bVal_eq_valF_zip]
    have aux : ∀ (F1 F2 : List (ℕ × ℕ)), ValidFactors F1 → ValidFactors F2 →
        (∀ pa ∈ F1, ∀ pb ∈ F2, pa.1 < pb.1) → (valF F1).Coprime (valF F2) := by
      intro F1 F2 hF1; induction F1 with
      | nil => intro _ _; simp [valF]
      | cons pa r1 ih =>
        rcases pa with ⟨p1, a1⟩; rcases hF1 with ⟨hp1, _, _, hr1⟩; intro hF2 hlt'
        simpa [valF] using ((coprime_valF_of_lt hp1 hF2 (fun pb hpb => hlt' (p1, a1) List.mem_cons_self pb hpb)).pow_left a1).mul_left
          (ih hr1 hF2 (fun x hx pb hpb => hlt' x (List.mem_cons_of_mem _ hx) pb hpb))
    refine aux _ _ (validFactors_zipWith_of_slotsMatch hm) htail.2.1 (fun pa hpa pb hpb => ?_)
    obtain ⟨s, hs, _, _, rfl⟩ := mem_zipWith_fst hpa
    exact hlt_st s hs pb hpb
  have hsig : sigma 1 (bVal st exps * valF tail) = bSig st exps * sigF tail := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop, bSig_eq_sigma_one_bVal hm,
      sigF_eq_sigma_one htail.2.1]
  have hab_m : 2 * (bVal st exps * valF tail) < bSig st exps * sigF tail := by
    have h1 := hab
    change bVal st exps * valF tail < ∑ d ∈ (bVal st exps * valF tail).properDivisors, d at h1
    have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := bVal st exps * valF tail)
    rw [← sigma_one_apply, hsig] at h2
    omega
  obtain ⟨_, hUd0, _, _, hU_bnd⟩ := slots_bounds hm
  have hlt := tailDeadAux_sound hlast hrem hUd0 htail hdead (bVal_pos hm) hU_bnd
  omega

private lemma s5_pseudoperfect {tail : List (ℕ × ℕ)}
    (htail : TailMatch 2 5 tail)
    (hab : (valF tail).Abundant)
    (hprim : ∀ d ∈ (valF tail).properDivisors, d.Deficient) :
    (valF tail).Pseudoperfect := by
  have hm0 : SlotsMatch [] [] := ⟨List.Forall₂.nil, List.Pairwise.nil⟩
  have hbv0 : bVal [] [] * valF tail = valF tail := by simp [bVal]
  cases tail with
  | nil => have := htail.1; simp at this
  | cons pa1 t1 =>
    rcases pa1 with ⟨p1, a1⟩
    rcases htail.2.1 with ⟨hp1, ha1, hp1_lt, hvf1⟩
    have hp1_gt2 : 2 < p1 := htail.2.2 (p1, a1) List.mem_cons_self
    have hp1_eq : p1 = 3 := by
      by_contra hne
      have hp1_ge5 : 5 ≤ p1 := by
        rcases Nat.Prime.eq_two_or_odd hp1 with h2 | hodd <;> omega
      have ht5 : TailMatch 4 5 ((p1, a1) :: t1) := by
        refine ⟨htail.1, ⟨hp1, ha1, hp1_lt, hvf1⟩, fun pa hpa => ?_⟩
        simp only [List.mem_cons] at hpa
        rcases hpa with rfl | hpa
        · omega
        · exact lt_of_lt_of_le (by omega) (le_of_lt (hp1_lt pa hpa))
      exact not_abundant_of_tailDead hm0 (by omega) (by omega)
        (fun _ hs => by simp at hs) ht5 dead_s5_p1 (by simpa [hbv0] using hab)
    subst hp1_eq
    have hm1 : SlotsMatch [mkSlot 3] [a1] :=
      slotsMatch_append_mkSlot hm0 hp1 (by omega) ha1 (fun _ hs => by simp at hs)
    have hbv1 : bVal [mkSlot 3] [a1] * valF t1 = valF ((3, a1) :: t1) := by
      simp [bVal, mkSlot, valF]
    rw [← hbv1] at hab hprim ⊢
    cases t1 with
    | nil => have := htail.1; simp at this
    | cons pa2 t2 =>
      rcases pa2 with ⟨p2, a2⟩
      rcases hvf1 with ⟨hp2, ha2, hp2_lt, hvf2⟩
      have hp2_gt3 : 3 < p2 := hp1_lt (p2, a2) List.mem_cons_self
      have hp2_le12 : p2 ≤ 12 := by
        by_contra hgt
        have ht4 : TailMatch 12 4 ((p2, a2) :: t2) := by
          refine ⟨by have := htail.1; simp at this ⊢; omega, ⟨hp2, ha2, hp2_lt, hvf2⟩, fun pa hpa => ?_⟩
          simp only [List.mem_cons] at hpa
          rcases hpa with rfl | hpa
          · omega
          · exact lt_of_lt_of_le (by omega) (le_of_lt (hp2_lt pa hpa))
        exact not_abundant_of_tailDead hm1 (by omega) (by omega)
          (fun s hs pa hpa => by
            simp only [List.mem_singleton] at hs; subst hs
            exact hp1_lt pa hpa) ht4 dead_s5_3_p2 hab
      have hp2_cases : p2 = 5 ∨ p2 = 7 ∨ p2 = 11 := by
        interval_cases p2 <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact absurd hp2 (by decide)
      rcases hp2_cases with rfl | rfl | rfl
      · -- p2 = 5
        have hm2 : SlotsMatch [mkSlot 3, mkSlot 5] [a1, a2] :=
          slotsMatch_append_mkSlot hm1 hp2 (by omega) ha2 (fun s hs => by simp [mkSlot] at hs; subst hs; omega)
        have hbv2 : bVal [mkSlot 3, mkSlot 5] [a1, a2] * valF t2 = bVal [mkSlot 3] [a1] * valF ((5, a2) :: t2) := by
          simp [bVal, mkSlot, valF]; ring
        rw [← hbv2] at hab hprim ⊢
        cases t2 with
        | nil => have := htail.1; simp at this
        | cons pa3 t3 =>
          rcases pa3 with ⟨p3, a3⟩
          rcases hvf2 with ⟨hp3, ha3, hp3_lt, hvf3⟩
          have hp3_gt5 : 5 < p3 := hp2_lt (p3, a3) List.mem_cons_self
          have hp3_le42 : p3 ≤ 42 := by
            by_contra hgt
            have ht3 : TailMatch 42 3 ((p3, a3) :: t3) := by
              refine ⟨by have := htail.1; simp at this ⊢; omega, ⟨hp3, ha3, hp3_lt, hvf3⟩, fun pa hpa => ?_⟩
              simp only [List.mem_cons] at hpa
              rcases hpa with rfl | hpa
              · omega
              · exact lt_of_lt_of_le (by omega) (le_of_lt (hp3_lt pa hpa))
            exact not_abundant_of_tailDead hm2 (by omega) (by omega)
              (fun s hs pa hpa => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
                rcases hs with rfl | rfl
                · exact hp1_lt pa (List.mem_cons_of_mem _ hpa)
                · exact hp2_lt pa hpa) ht3 dead_s5_3_5_p3 hab
          by_cases hp3_24 : 24 ≤ p3
          · have ht3 : TailMatch (lastPrime [mkSlot 3, mkSlot 5]) 3 ((p3, a3) :: t3) :=
              ⟨by have := htail.1; simp at this ⊢; omega, ⟨hp3, ha3, hp3_lt, hvf3⟩, fun pa hpa => by
                simpa [lastPrime, mkSlot] using hp2_lt pa hpa⟩
            exact checkPrimeRange_sound hm2 (by omega) ht3 hp3_24 hp3_le42 hab hprim check_s5_3_5_24_42
          · have hp3_cases : p3 = 7 ∨ p3 = 11 ∨ p3 = 13 ∨ p3 = 17 ∨ p3 = 19 ∨ p3 = 23 := by
              interval_cases p3 <;>
                first
                | exact Or.inl rfl
                | exact Or.inr (Or.inl rfl)
                | exact Or.inr (Or.inr (Or.inl rfl))
                | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
                | exact absurd hp3 (by decide)
            have hstep3 : ∀ (q : ℕ), q = p3 →
                SlotsMatch [mkSlot 3, mkSlot 5, mkSlot q] [a1, a2, a3] ∧
                bVal [mkSlot 3, mkSlot 5, mkSlot q] [a1, a2, a3] * valF t3 =
                  bVal [mkSlot 3, mkSlot 5] [a1, a2] * valF ((q, a3) :: t3) ∧
                TailMatch (lastPrime [mkSlot 3, mkSlot 5, mkSlot q]) 2 t3 := by
              intro q hq; subst hq
              refine ⟨slotsMatch_append_mkSlot hm2 hp3 (by omega) ha3 (fun s hs => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
                rcases hs with rfl | rfl <;> simp [mkSlot] <;> omega),
                by simp [bVal, mkSlot, valF]; ring,
                ⟨by have := htail.1; simp at this; omega, hvf3, fun pa hpa => by
                  simpa [lastPrime, mkSlot] using hp3_lt pa hpa⟩⟩
            rcases hp3_cases with rfl | rfl | rfl | rfl | rfl | rfl
            · obtain ⟨hm3, hbv3, ht3⟩ := hstep3 7 rfl
              rw [← hbv3] at hab hprim ⊢
              exact checkTree_sound 55 hm3 (good := none) trivial (by omega) ht3 hab hprim check_s5_3_5_7
            · obtain ⟨hm3, hbv3, ht3⟩ := hstep3 11 rfl
              rw [← hbv3] at hab hprim ⊢
              exact checkTree_sound 55 hm3 (good := none) trivial (by omega) ht3 hab hprim check_s5_3_5_11
            · obtain ⟨hm3, hbv3, ht3⟩ := hstep3 13 rfl
              rw [← hbv3] at hab hprim ⊢
              exact checkTree_sound 55 hm3 (good := none) trivial (by omega) ht3 hab hprim check_s5_3_5_13
            · obtain ⟨hm3, hbv3, ht3⟩ := hstep3 17 rfl
              rw [← hbv3] at hab hprim ⊢
              cases t3 with
              | nil => have := ht3.1; simp at this
              | cons pa4 t4 =>
                rcases pa4 with ⟨p4, a4⟩
                rcases hvf3 with ⟨hp4, ha4, hp4_lt, hvf4⟩
                have hp4_ge19 : 19 ≤ p4 := by
                  have h17 : 17 < p4 := hp3_lt (p4, a4) List.mem_cons_self
                  rcases Nat.Prime.eq_two_or_odd hp4 with h2 | hodd <;> omega
                have hp4_le508 : p4 ≤ 508 := by
                  by_contra hgt
                  have ht2' : TailMatch 508 2 ((p4, a4) :: t4) := by
                    refine ⟨ht3.1, ⟨hp4, ha4, hp4_lt, hvf4⟩, fun pa hpa => ?_⟩
                    simp only [List.mem_cons] at hpa
                    rcases hpa with rfl | hpa
                    · omega
                    · exact lt_of_lt_of_le (by omega) (le_of_lt (hp4_lt pa hpa))
                  exact not_abundant_of_tailDead hm3 (by omega) (by omega)
                    (fun s hs pa hpa => all_lt_of_lastPrime_lt hm3 (ht3.2.2 pa hpa) s hs)
                    ht2' dead_s5_3_5_17_p4 hab
                by_cases h1 : p4 ≤ 137
                · exact checkPrimeRange_sound hm3 le_rfl ht3 hp4_ge19 h1 hab hprim check_s5_3_5_17_c1
                · by_cases h2 : p4 ≤ 199
                  · exact checkPrimeRange_sound hm3 le_rfl ht3 (by omega) h2 hab hprim check_s5_3_5_17_c2
                  · by_cases h3 : p4 ≤ 251
                    · exact checkPrimeRange_sound hm3 le_rfl ht3 (by omega) h3 hab hprim check_s5_3_5_17_c3
                    · by_cases h4 : p4 ≤ 263
                      · exact checkPrimeRange_sound hm3 le_rfl ht3 (by omega) h4 hab hprim check_s5_3_5_17_c4
                      · by_cases h5 : p4 ≤ 281
                        · exact checkPrimeRange_sound hm3 le_rfl ht3 (by omega) h5 hab hprim check_s5_3_5_17_c5
                        · by_cases h6 : p4 ≤ 331
                          · exact checkPrimeRange_sound hm3 le_rfl ht3 (by omega) h6 hab hprim check_s5_3_5_17_c6
                          · by_cases h7 : p4 ≤ 397
                            · exact checkPrimeRange_sound hm3 le_rfl ht3 (by omega) h7 hab hprim check_s5_3_5_17_c7
                            · exact checkPrimeRange_sound hm3 le_rfl ht3 (by omega) hp4_le508 hab hprim check_s5_3_5_17_c8
            · obtain ⟨hm3, hbv3, ht3⟩ := hstep3 19 rfl
              rw [← hbv3] at hab hprim ⊢
              cases t3 with
              | nil => have := ht3.1; simp at this
              | cons pa4 t4 =>
                rcases pa4 with ⟨p4, a4⟩
                rcases hvf3 with ⟨hp4, ha4, hp4_lt, hvf4⟩
                have hp4_ge23 : 23 ≤ p4 := by
                  have h19 : 19 < p4 := hp3_lt (p4, a4) List.mem_cons_self
                  by_contra hlt
                  interval_cases p4 <;> exact absurd hp4 (by decide)
                have hp4_le182 : p4 ≤ 182 := by
                  by_contra hgt
                  have ht2' : TailMatch 182 2 ((p4, a4) :: t4) := by
                    refine ⟨ht3.1, ⟨hp4, ha4, hp4_lt, hvf4⟩, fun pa hpa => ?_⟩
                    simp only [List.mem_cons] at hpa
                    rcases hpa with rfl | hpa
                    · omega
                    · exact lt_of_lt_of_le (by omega) (le_of_lt (hp4_lt pa hpa))
                  exact not_abundant_of_tailDead hm3 (by omega) (by omega)
                    (fun s hs pa hpa => all_lt_of_lastPrime_lt hm3 (ht3.2.2 pa hpa) s hs)
                    ht2' dead_s5_3_5_19_p4 hab
                by_cases h1 : p4 ≤ 89
                · exact checkPrimeRange_sound hm3 le_rfl ht3 hp4_ge23 h1 hab hprim check_s5_3_5_19_c1
                · by_cases h2 : p4 ≤ 107
                  · exact checkPrimeRange_sound hm3 le_rfl ht3 (by omega) h2 hab hprim check_s5_3_5_19_c2
                  · exact checkPrimeRange_sound hm3 le_rfl ht3 (by omega) hp4_le182 hab hprim check_s5_3_5_19_c3
            · obtain ⟨hm3, hbv3, ht3⟩ := hstep3 23 rfl
              rw [← hbv3] at hab hprim ⊢
              exact checkTree_sound 55 hm3 (good := none) trivial (by omega) ht3 hab hprim check_s5_3_5_23
      · -- p2 = 7
        have hm2 : SlotsMatch [mkSlot 3, mkSlot 7] [a1, a2] :=
          slotsMatch_append_mkSlot hm1 hp2 (by omega) ha2 (fun s hs => by simp [mkSlot] at hs; subst hs; omega)
        have hbv2 : bVal [mkSlot 3, mkSlot 7] [a1, a2] * valF t2 = bVal [mkSlot 3] [a1] * valF ((7, a2) :: t2) := by
          simp [bVal, mkSlot, valF]; ring
        rw [← hbv2] at hab hprim ⊢
        cases t2 with
        | nil => have := htail.1; simp at this
        | cons pa3 t3 =>
          rcases pa3 with ⟨p3, a3⟩
          rcases hvf2 with ⟨hp3, ha3, hp3_lt, hvf3⟩
          have hp3_ge11 : 11 ≤ p3 := by
            have h7 : 7 < p3 := hp2_lt (p3, a3) List.mem_cons_self
            by_contra hlt
            interval_cases p3 <;> exact absurd hp3 (by decide)
          have hp3_le22 : p3 ≤ 22 := by
            by_contra hgt
            have ht3 : TailMatch 22 3 ((p3, a3) :: t3) := by
              refine ⟨by have := htail.1; simp at this ⊢; omega, ⟨hp3, ha3, hp3_lt, hvf3⟩, fun pa hpa => ?_⟩
              simp only [List.mem_cons] at hpa
              rcases hpa with rfl | hpa
              · omega
              · exact lt_of_lt_of_le (by omega) (le_of_lt (hp3_lt pa hpa))
            exact not_abundant_of_tailDead hm2 (by omega) (by omega)
              (fun s hs pa hpa => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
                rcases hs with rfl | rfl
                · exact hp1_lt pa (List.mem_cons_of_mem _ hpa)
                · exact hp2_lt pa hpa) ht3 dead_s5_3_7_p3 hab
          have hp3_le19 : p3 ≤ 19 := by
            by_contra hgt
            interval_cases p3 <;> exact absurd hp3 (by decide)
          have ht3 : TailMatch (lastPrime [mkSlot 3, mkSlot 7]) 3 ((p3, a3) :: t3) :=
            ⟨by have := htail.1; simp at this ⊢; omega, ⟨hp3, ha3, hp3_lt, hvf3⟩, fun pa hpa => by
              simpa [lastPrime, mkSlot] using hp2_lt pa hpa⟩
          exact checkPrimeRange_sound hm2 (by omega) ht3 hp3_ge11 hp3_le19 hab hprim check_s5_3_7
      · -- p2 = 11
        have hm2 : SlotsMatch [mkSlot 3, mkSlot 11] [a1, a2] :=
          slotsMatch_append_mkSlot hm1 hp2 (by omega) ha2 (fun s hs => by simp [mkSlot] at hs; subst hs; omega)
        have hbv2 : bVal [mkSlot 3, mkSlot 11] [a1, a2] * valF t2 = bVal [mkSlot 3] [a1] * valF ((11, a2) :: t2) := by
          simp [bVal, mkSlot, valF]; ring
        rw [← hbv2] at hab hprim ⊢
        cases t2 with
        | nil => have := htail.1; simp at this
        | cons pa3 t3 =>
          rcases pa3 with ⟨p3, a3⟩
          rcases hvf2 with ⟨hp3, ha3, hp3_lt, hvf3⟩
          have hp3_gt11 : 11 < p3 := hp2_lt (p3, a3) List.mem_cons_self
          have hp3_le16 : p3 ≤ 16 := by
            by_contra hgt
            have ht3 : TailMatch 16 3 ((p3, a3) :: t3) := by
              refine ⟨by have := htail.1; simp at this ⊢; omega, ⟨hp3, ha3, hp3_lt, hvf3⟩, fun pa hpa => ?_⟩
              simp only [List.mem_cons] at hpa
              rcases hpa with rfl | hpa
              · omega
              · exact lt_of_lt_of_le (by omega) (le_of_lt (hp3_lt pa hpa))
            exact not_abundant_of_tailDead hm2 (by omega) (by omega)
              (fun s hs pa hpa => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
                rcases hs with rfl | rfl
                · exact hp1_lt pa (List.mem_cons_of_mem _ hpa)
                · exact hp2_lt pa hpa) ht3 dead_s5_3_11_p3 hab
          have hp3_eq : p3 = 13 := by
            interval_cases p3 <;> first | rfl | exact absurd hp3 (by decide)
          subst hp3_eq
          have hm3 : SlotsMatch [mkSlot 3, mkSlot 11, mkSlot 13] [a1, a2, a3] :=
            slotsMatch_append_mkSlot hm2 hp3 (by omega) ha3 (fun s hs => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
              rcases hs with rfl | rfl <;> simp [mkSlot])
          have hbv3 : bVal [mkSlot 3, mkSlot 11, mkSlot 13] [a1, a2, a3] * valF t3 =
              bVal [mkSlot 3, mkSlot 11] [a1, a2] * valF ((13, a3) :: t3) := by
            simp [bVal, mkSlot, valF]; ring
          have ht3 : TailMatch (lastPrime [mkSlot 3, mkSlot 11, mkSlot 13]) 2 t3 :=
            ⟨by have := htail.1; simp at this; omega, hvf3, fun pa hpa => by
              simpa [lastPrime, mkSlot] using hp3_lt pa hpa⟩
          rw [← hbv3] at hab hprim ⊢
          exact checkTree_sound 55 hm3 (good := none) trivial (by omega) ht3 hab hprim check_s5_3_11_13

private lemma odd_primitive_abundant_pseudoperfect {m : ℕ}
    (hodd : Odd m) (hab : m.Abundant)
    (hprim : ∀ d ∈ m.properDivisors, d.Deficient)
    (hcard : m.primeFactors.card ≤ 5) :
    m.Pseudoperfect := by
  have hm_pos : 0 < m := by
    by_contra h0
    have hmz : m = 0 := by omega
    subst hmz
    change 0 < ∑ d ∈ (0 : ℕ).properDivisors, d at hab
    simp at hab
  let ps : List ℕ := m.primeFactors.sort (· ≤ ·)
  let tail : List (ℕ × ℕ) := ps.map (fun p => (p, m.factorization p))
  have hps_nodup : ps.Nodup := m.primeFactors.sort_nodup (· ≤ ·)
  have hps_le : ps.Pairwise (· ≤ ·) := m.primeFactors.pairwise_sort (· ≤ ·)
  have hps_lt : ps.Pairwise (· < ·) := by
    have aux : ∀ (l : List ℕ), l.Pairwise (· ≤ ·) → l.Nodup → l.Pairwise (· < ·) := by
      intro l; induction l with
      | nil => intro _ _; exact List.Pairwise.nil
      | cons x xs ih =>
        intro hle hnd
        rw [List.pairwise_cons] at hle ⊢
        rw [List.nodup_cons] at hnd
        exact ⟨fun y hy => lt_of_le_of_ne (hle.1 y hy) (fun heq => hnd.1 (heq ▸ hy)), ih hle.2 hnd.2⟩
    exact aux ps hps_le hps_nodup
  have hmem_ps : ∀ p, p ∈ ps ↔ p ∈ m.primeFactors := fun p => Finset.mem_sort (· ≤ ·)
  have hval_prod : ∀ (l : List ℕ), l.Nodup →
      valF (l.map (fun p => (p, m.factorization p))) = ∏ p ∈ l.toFinset, p ^ m.factorization p := by
    intro l; induction l with
    | nil => intro _; simp [valF]
    | cons x xs ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      have hnx : x ∉ xs.toFinset := by simpa using hnd.1
      simp only [List.map_cons, valF, List.toFinset_cons, Finset.prod_insert hnx, ih hnd.2]
  have htoFin : ps.toFinset = m.primeFactors := by
    ext p; simp [hmem_ps]
  have hvalF_eq : valF tail = m := by
    rw [hval_prod ps hps_nodup, htoFin]
    have hfac := Nat.prod_factorization_pow_eq_self hm_pos.ne'
    rw [Finsupp.prod, Nat.support_factorization] at hfac
    exact hfac
  have hvf : ValidFactors tail := by
    have aux : ∀ (l : List ℕ), l.Pairwise (· < ·) → (∀ p ∈ l, p ∈ m.primeFactors) →
        ValidFactors (l.map (fun p => (p, m.factorization p))) := by
      intro l; induction l with
      | nil => intro _ _; trivial
      | cons x xs ih =>
        intro hlt hmem
        rw [List.pairwise_cons] at hlt
        have hxmem := hmem x List.mem_cons_self
        have hxp : x.Prime := Nat.prime_of_mem_primeFactors hxmem
        have hxexp : 1 ≤ m.factorization x := by
          have hne : m.factorization x ≠ 0 := by
            rw [← Nat.support_factorization] at hxmem
            exact Finsupp.mem_support_iff.mp hxmem
          omega
        refine ⟨hxp, hxexp, fun pa hpa => ?_, ih hlt.2 (fun y hy => hmem y (List.mem_cons_of_mem _ hy))⟩
        rw [List.mem_map] at hpa
        obtain ⟨y, hy, rfl⟩ := hpa
        exact hlt.1 y hy
    exact aux ps hps_lt (fun p hp => (hmem_ps p).mp hp)
  have hgt2 : ∀ pa ∈ tail, 2 < pa.1 := by
    intro pa hpa
    rw [List.mem_map] at hpa
    obtain ⟨p, hp, rfl⟩ := hpa
    have hpm := (hmem_ps p).mp hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hp_dvd : p ∣ m := Nat.dvd_of_mem_primeFactors hpm
    rcases Nat.Prime.eq_two_or_odd hp_prime with rfl | hpo
    · obtain ⟨k, hk⟩ := hodd
      obtain ⟨j, hj⟩ := hp_dvd
      omega
    · have := hp_prime.two_le; omega
  have hlen_eq : tail.length = m.primeFactors.card := by
    simp [tail, ps, Finset.length_sort]
  have hlen_pos : 1 ≤ tail.length := by
    by_contra h0
    have hnil : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil] at hvalF_eq
    simp only [valF] at hvalF_eq
    subst hvalF_eq
    change 1 < ∑ d ∈ (1 : ℕ).properDivisors, d at hab
    simp at hab
  have hm0 : SlotsMatch [] [] := ⟨List.Forall₂.nil, List.Pairwise.nil⟩
  rw [← hvalF_eq] at hab hprim ⊢
  have hlen5 : tail.length ≤ 5 := by omega
  have hcase : tail.length = 1 ∨ tail.length = 2 ∨ tail.length = 3 ∨ tail.length = 4 ∨ tail.length = 5 := by omega
  rcases hcase with h1 | h2 | h3 | h4 | h5
  · have hres := checkTree_sound 55 hm0 (good := none) trivial le_rfl ⟨h1, hvf, hgt2⟩ (by simpa [bVal] using hab)
      (by simpa [bVal] using hprim) check_s1
    simpa [bVal] using hres
  · have hres := checkTree_sound 55 hm0 (good := none) trivial (by omega) ⟨h2, hvf, hgt2⟩ (by simpa [bVal] using hab)
      (by simpa [bVal] using hprim) check_s2
    simpa [bVal] using hres
  · have hres := checkTree_sound 55 hm0 (good := none) trivial (by omega) ⟨h3, hvf, hgt2⟩ (by simpa [bVal] using hab)
      (by simpa [bVal] using hprim) check_s3
    simpa [bVal] using hres
  · have hres := checkTree_sound 55 hm0 (good := none) trivial (by omega) ⟨h4, hvf, hgt2⟩ (by simpa [bVal] using hab)
      (by simpa [bVal] using hprim) check_s4
    simpa [bVal] using hres
  · exact s5_pseudoperfect ⟨h5, hvf, hgt2⟩ hab hprim

private lemma pseudoperfect_of_dvd {m n : ℕ} (hn : 0 < n) (hmn : m ∣ n)
    (hp : m.Pseudoperfect) : n.Pseudoperfect := by
  obtain ⟨_, s, hs, hsum⟩ := hp
  obtain ⟨k, rfl⟩ := hmn
  have hk : 0 < k := Nat.pos_of_ne_zero (by intro h; subst h; simp at hn)
  refine ⟨hn, s.image (· * k), ?_, ?_⟩
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp (hs hd)
    exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_right hdvd k, Nat.mul_lt_mul_of_pos_right hlt hk⟩
  · rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hk hab),
      ← Finset.sum_mul, hsum]

end Erdos470OddWeird

theorem OMA.solution : type_of% @Erdos470.erdos_470.variants.odd_weird_prime_div := by
  classical
  intro n hodd hweird
  obtain ⟨hab, hnp⟩ := hweird
  have hn_pos : 0 < n := by
    by_contra h0
    have hnz : n = 0 := by omega
    subst hnz
    change 0 < ∑ d ∈ (0 : ℕ).properDivisors, d at hab
    simp at hab
  have hset : {m | m ∈ n.divisors ∧ m.Prime} = (n.primeFactors : Set ℕ) := by
    ext p
    simp [Nat.mem_primeFactors, Nat.mem_divisors, hn_pos.ne', and_comm]
  rw [hset, Set.ncard_coe_finset]
  by_contra hlt
  have hcard : n.primeFactors.card ≤ 5 := by omega
  have hex : ∃ d, d ∣ n ∧ ¬ d.Deficient := by
    refine ⟨n, dvd_refl n, fun hdef => ?_⟩
    change n < ∑ d ∈ n.properDivisors, d at hab
    change ∑ d ∈ n.properDivisors, d < n at hdef
    omega
  let m := Nat.find hex
  have hm_spec := Nat.find_spec hex
  have hm_dvd : m ∣ n := hm_spec.1
  have hm_nd : ¬ m.Deficient := hm_spec.2
  have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos hm_dvd hn_pos
  have hm_odd : Odd m := by
    obtain ⟨k, hk⟩ := hm_dvd
    rw [hk] at hodd
    exact (Nat.odd_mul.mp hodd).1
  have hm_prim : ∀ d ∈ m.properDivisors, d.Deficient := by
    intro d hd
    obtain ⟨hd_dvd, hd_lt⟩ := Nat.mem_properDivisors.mp hd
    by_contra hnd
    exact Nat.find_min hex hd_lt ⟨hd_dvd.trans hm_dvd, hnd⟩
  have hm_card : m.primeFactors.card ≤ 5 :=
    (Finset.card_le_card (Nat.primeFactors_mono hm_dvd hn_pos.ne')).trans hcard
  have hm_pp : m.Pseudoperfect := by
    by_cases hm_ab : m.Abundant
    · exact Erdos470OddWeird.odd_primitive_abundant_pseudoperfect hm_odd hm_ab hm_prim hm_card
    · refine ⟨hm_pos, m.properDivisors, Finset.Subset.refl _, ?_⟩
      change ¬ ∑ d ∈ m.properDivisors, d < m at hm_nd
      change ¬ m < ∑ d ∈ m.properDivisors, d at hm_ab
      omega
  exact hnp (Erdos470OddWeird.pseudoperfect_of_dvd hn_pos hm_dvd hm_pp)
