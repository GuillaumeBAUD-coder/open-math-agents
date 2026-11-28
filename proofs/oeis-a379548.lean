import OMAStatements.S_oeis_a379548
import Mathlib.NumberTheory.Primorial
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic

/-!
# A379548 permutes the squarefree positive integers

Source: https://oeis.org/A379548 (David James Sycamore, December 25, 2024).

This proves existence of the original greedy sequence, injectivity, and
coverage of every positive squarefree integer. A repeatedly selected prime
exhausts its squarefree multiples. If queue 2 stopped, all late terms would
be even and the selected odd primes would be bounded by the early terms.
A fresh large prime r gives missing odd squarefree candidates p*r and
therefore bounds all late outputs, contradicting injectivity. Primorials
multiplied by fresh primes then force every prime queue to recur.

Related queue-exhaustion method for a different selector:
https://the-omega-institute.github.io/trureturing-mdbook/Library/Factorization/shannon2023a363956.html
Related unrestricted conjecture and concurrent proof:
https://github.com/lefttosolve2/open-math-agents/pull/38679
-/

open scoped BigOperators
open OMA.S_oeis_a379548

namespace A379548Proof

section Coverage
variable (a p : ℕ → ℕ)
variable (h0 : a 0 = 1)
variable (hp : ∀ n, IsLeast {q : ℕ | q.Prime ∧ ¬ q ∣ a n} (p n))
variable (hs : ∀ n, IsLeast {m : ℕ | 0 < m ∧ Squarefree m ∧ p n ∣ m ∧ ∀ i ≤ n, a i ≠ m} (a (n+1)))
include h0 hp hs

lemma positive (n : ℕ) : 0 < a n := by
  cases n with
  | zero => omega
  | succ n => exact (hs n).1.1

lemma squarefree (n : ℕ) : Squarefree (a n) := by
  cases n with
  | zero => simpa [h0] using (squarefree_one : Squarefree (1 : ℕ))
  | succ n => exact (hs n).1.2.1

lemma injective : Function.Injective a := by
  have hnot : ∀ i j, i < j → a i ≠ a j := by
    intro i j hij
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (hs k).1.2.2.2 i (by omega)
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hnot i j h hij)
  · exact h
  · exact False.elim (hnot j i h hij.symm)

lemma eventually_large (B : ℕ) : ∃ N, ∀ n ≥ N, B < a n := by
  have hi := injective a p h0 hp hs
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hi.nat_tendsto_atTop.eventually (Filter.eventually_ge_atTop (B+1)))
  exact ⟨N, fun n hn => by have := hN n hn; omega⟩

lemma selector_of_odd (n : ℕ) (ho : Odd (a n)) : p n = 2 := by
  have hle := (hp n).2 (show (2 : ℕ).Prime ∧ ¬ 2 ∣ a n from
    ⟨Nat.prime_two, by simpa using ho.not_two_dvd_nat⟩)
  have hge := (hp n).1.1.two_le
  omega

/-- A queue chosen arbitrarily late exhausts all its positive multiples. -/
lemma queue_full (q : ℕ) (hrec : ∀ N, ∃ n ≥ N, p n = q)
    (m : ℕ) (hm : 0 < m) (hms : Squarefree m) (hqm : q ∣ m) : m ∈ Set.range a := by
  by_contra hmiss
  have hmiss' : ∀ i, a i ≠ m := by simpa [Set.mem_range] using hmiss
  obtain ⟨N, hN⟩ := eventually_large a p h0 hp hs m
  obtain ⟨n, hn, hpn⟩ := hrec N
  have hle := (hs n).2 (show 0 < m ∧ Squarefree m ∧ p n ∣ m ∧ ∀ i ≤ n, a i ≠ m from
    ⟨hm, hms, hpn ▸ hqm, fun i _ => hmiss' i⟩)
  have hgt := hN (n+1) (by omega)
  omega

/-- Queue 2 cannot stop: otherwise all late values are even, forcing all late
queues into the finite set of prime values already seen. Multiplication by
a fresh prime gives missing odd squarefree candidates and bounds every late output. -/
lemma two_recurrent : ∀ N, ∃ n ≥ N, p n = 2 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨N, hN⟩ := h
  let B := 2 + ∑ i ∈ Finset.range (N+1), a i
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hearly : ∀ i ≤ N, a i < B := by
    intro i hi
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (a j))
      (Finset.mem_range.mpr (by omega : i < N+1))
    dsimp [B]
    omega
  have hoddmiss : ∀ m, B < m → Odd m → ∀ i, a i ≠ m := by
    intro m hm ho i heq
    by_cases hi : i ≤ N
    · have := hearly i hi; omega
    · have hp2 := selector_of_odd a p h0 hp hs i (heq ▸ ho)
      exact hN i (by omega) hp2
  have hbound : ∀ n ≥ N, p n ≤ B := by
    intro n hn
    by_contra hbig
    have hbig' : B < p n := by omega
    have hodd := (hp n).1.1.odd_of_ne_two (hN n hn)
    have hmissing := hoddmiss (p n) hbig' hodd
    have hle := (hs n).2 (show 0 < p n ∧ Squarefree (p n) ∧ p n ∣ p n ∧ ∀ i ≤ n, a i ≠ p n from
      ⟨(hp n).1.1.pos, (hp n).1.1.squarefree, dvd_rfl, fun i _ => hmissing i⟩)
    have hge := Nat.le_of_dvd (positive a p h0 hp hs (n+1)) (hs n).1.2.2.1
    have heq : a (n+1) = p n := by omega
    have hp2 := selector_of_odd a p h0 hp hs (n+1) (heq ▸ hodd)
    exact hN (n+1) (by omega) hp2
  obtain ⟨r, hrB, hr⟩ := Nat.exists_infinite_primes (B+1)
  have hro : Odd r := hr.odd_of_ne_two (by omega)
  obtain ⟨K, hK⟩ := eventually_large a p h0 hp hs (B*r)
  let n := max K N
  have hnN : N ≤ n := le_max_right _ _
  have hpB := hbound n hnN
  have hpo := (hp n).1.1.odd_of_ne_two (hN n hnN)
  have hpr : p n ≠ r := by omega
  have hsf : Squarefree (p n*r) :=
    (Nat.squarefree_mul ((Nat.coprime_primes (hp n).1.1 hr).mpr hpr)).mpr
      ⟨(hp n).1.1.squarefree, hr.squarefree⟩
  have hmB : B < p n*r := by
    have := Nat.le_mul_of_pos_left r (hp n).1.1.pos
    omega
  have hmiss := hoddmiss (p n*r) hmB (hpo.mul hro)
  have hle := (hs n).2 (show 0 < p n*r ∧ Squarefree (p n*r) ∧
      p n ∣ p n*r ∧ ∀ i ≤ n, a i ≠ p n*r from
    ⟨by omega, hsf, dvd_mul_right _ _, fun i _ => hmiss i⟩)
  have hgt := hK (n+1) (by dsimp [n]; omega)
  have := Nat.mul_le_mul_right r hpB
  omega

/-- Squarefree even multiples of `primorial (q-1)` avoiding `q` force
arbitrarily late activations of queue `q`. -/
lemma prime_recurrent (q : ℕ) (hq : q.Prime) : ∀ N, ∃ n ≥ N, p n = q := by
  classical
  by_cases hq2 : q = 2
  · subst q
    exact two_recurrent a p h0 hp hs
  have hqgt : 2 < q := lt_of_le_of_ne hq.two_le (Ne.symm hq2)
  intro N
  let B := 2 + ∑ i ∈ Finset.range (N+1), a i
  let D := primorial (q-1)
  obtain ⟨r, hrbig, hr⟩ := Nat.exists_infinite_primes (max B q+1)
  let m := D*r
  have hDpos : 0 < D := primorial_pos _
  have hm : B < m := by
    have hmul : r ≤ D*r := Nat.le_mul_of_pos_left _ hDpos
    dsimp [m]
    have := le_max_left B q
    omega
  have htwo : 2 ∣ m := dvd_mul_of_dvd_left
    (Nat.prime_two.dvd_primorial_iff.mpr (by omega : 2 ≤ q-1)) _
  have hrD : ¬ r ∣ D := by
    intro h
    have := hr.dvd_primorial_iff.mp h
    have := le_max_right B q
    omega
  have hsf : Squarefree m :=
    (Nat.squarefree_mul (hr.coprime_iff_not_dvd.mpr hrD).symm).mpr
      ⟨squarefree_primorial _, hr.squarefree⟩
  have hqm : ¬ q ∣ m := by
    intro hdiv
    rcases hq.dvd_mul.mp hdiv with h | h
    · have := hq.dvd_primorial_iff.mp h
      omega
    · have hqr := (Nat.dvd_prime hr).mp h
      have := le_max_right B q
      rcases hqr with h | h <;> omega
  obtain ⟨i, hi⟩ := queue_full a p h0 hp hs 2 (two_recurrent a p h0 hp hs) m (by omega) hsf htwo
  have hiN : N < i := by
    by_contra hn
    have hsum := Finset.single_le_sum (fun j _ => Nat.zero_le (a j))
      (Finset.mem_range.mpr (by omega : i < N+1))
    dsimp [B] at hm
    omega
  refine ⟨i, by omega, ?_⟩
  have hle : p i ≤ q := (hp i).2 ⟨hq, by simpa [hi] using hqm⟩
  have hge : q ≤ p i := by
    by_contra hlt
    have hdD : p i ∣ D := (hp i).1.1.dvd_primorial_iff.mpr (by omega)
    have hdM : p i ∣ m := dvd_mul_of_dvd_left hdD _
    exact (hp i).1.2 (hi ▸ hdM)
  omega

lemma covers : Set.range a = {m : ℕ | 0 < m ∧ Squarefree m} := by
  ext m
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨positive a p h0 hp hs n, squarefree a p h0 hp hs n⟩
  · intro hm
    by_cases hm1 : m = 1
    · exact ⟨0, by simpa [hm1] using h0⟩
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    exact queue_full a p h0 hp hs q (prime_recurrent a p h0 hp hs q hq) m hm.1 hm.2 hqm

end Coverage

/-- Euclid supplies a prime outside the finite prime support of a positive value. -/
lemma least_prime (x : ℕ) (hx : 0 < x) :
    ∃ p, IsLeast {q : ℕ | q.Prime ∧ ¬ q ∣ x} p := by
  classical
  have hex : ∃ p, p.Prime ∧ ¬ p ∣ x := by
    obtain ⟨p, hpx, hp⟩ := Nat.exists_infinite_primes (x+1)
    exact ⟨p, hp, Nat.not_dvd_of_pos_of_lt hx (by omega)⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun q hq => Nat.find_min' hex hq⟩

lemma least_fresh (S : Finset ℕ) (p : ℕ) (hp : p.Prime) :
    ∃ m, IsLeast {m : ℕ | 0 < m ∧ Squarefree m ∧ p ∣ m ∧ m ∉ S} m := by
  classical
  have hex : ∃ m, 0 < m ∧ Squarefree m ∧ p ∣ m ∧ m ∉ S := by
    obtain ⟨r, hrbig, hr⟩ := Nat.exists_infinite_primes (max (S.sup id) p+1)
    have hpr : p ≠ r := by have := le_max_right (S.sup id) p; omega
    have hsf := (Nat.squarefree_mul ((Nat.coprime_primes hp hr).mpr hpr)).mpr
      ⟨hp.squarefree, hr.squarefree⟩
    refine ⟨p*r, Nat.mul_pos hp.pos hr.pos, hsf, dvd_mul_right _ _, ?_⟩
    intro hm
    have hle : p*r ≤ S.sup id := Finset.le_sup (f := id) hm
    have hge := Nat.le_mul_of_pos_left r hp.pos
    have := le_max_left (S.sup id) p
    omega
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min' hex hm⟩

structure BuildState where
  value : ℕ
  history : Finset ℕ
  pos : 0 < value

noncomputable def primeOf (s : BuildState) : ℕ :=
  (least_prime s.value s.pos).choose

lemma primeOf_spec (s : BuildState) :
    IsLeast {q : ℕ | q.Prime ∧ ¬ q ∣ s.value} (primeOf s) :=
  (least_prime s.value s.pos).choose_spec

noncomputable def freshOf (s : BuildState) : ℕ :=
  (least_fresh s.history (primeOf s) (primeOf_spec s).1.1).choose

lemma freshOf_spec (s : BuildState) :
    IsLeast {m : ℕ | 0 < m ∧ Squarefree m ∧ primeOf s ∣ m ∧ m ∉ s.history} (freshOf s) :=
  (least_fresh s.history (primeOf s) (primeOf_spec s).1.1).choose_spec

noncomputable def advance (s : BuildState) : BuildState where
  value := freshOf s
  history := insert (freshOf s) s.history
  pos := (freshOf_spec s).1.1

noncomputable def states : ℕ → BuildState
  | 0 => ⟨1, {1}, by decide⟩
  | n+1 => advance (states n)

lemma history_eq (n : ℕ) :
    (states n).history = (Finset.range (n+1)).image (fun i => (states i).value) := by
  classical
  induction n with
  | zero => simp [states]
  | succ n ih =>
    change insert (freshOf (states n)) (states n).history = _
    rw [ih, Finset.range_add_one (n := n+1), Finset.image_insert]
    rfl

lemma exists_greedy : ∃ a, Greedy a := by
  classical
  refine ⟨fun n => (states n).value, rfl, ?_⟩
  intro n
  refine ⟨primeOf (states n), primeOf_spec _, ?_⟩
  have hf := freshOf_spec (states n)
  change IsLeast {m : ℕ | 0 < m ∧ Squarefree m ∧ primeOf (states n) ∣ m ∧
    ∀ i ≤ n, (states i).value ≠ m} (freshOf (states n))
  have hmem (m : ℕ) : m ∈ (states n).history ↔ ∃ i ≤ n, (states i).value = m := by
    rw [history_eq]
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, heq⟩; exact ⟨i, by omega, heq⟩
    · rintro ⟨i, hi, heq⟩; exact ⟨i, by omega, heq⟩
  constructor
  · refine ⟨hf.1.1, hf.1.2.1, hf.1.2.2.1, ?_⟩
    intro i hi heq
    exact hf.1.2.2.2 ((hmem _).mpr ⟨i, hi, heq⟩)
  · intro m hm
    refine hf.2 ⟨hm.1, hm.2.1, hm.2.2.1, ?_⟩
    intro h
    obtain ⟨i, hi, heq⟩ := (hmem m).mp h
    exact hm.2.2.2 i hi heq

end A379548Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a379548.main := by
  refine ⟨A379548Proof.exists_greedy, ?_⟩
  intro a ha
  let p : ℕ → ℕ := fun n => (ha.2 n).choose
  have hp : ∀ n, IsLeast {q : ℕ | q.Prime ∧ ¬ q ∣ a n} (p n) :=
    fun n => (ha.2 n).choose_spec.1
  have hs : ∀ n, IsLeast {m : ℕ | 0 < m ∧ Squarefree m ∧ p n ∣ m ∧ ∀ i ≤ n, a i ≠ m} (a (n+1)) :=
    fun n => (ha.2 n).choose_spec.2
  exact ⟨A379548Proof.injective a p ha.1 hp hs,
    A379548Proof.covers a p ha.1 hp hs⟩
