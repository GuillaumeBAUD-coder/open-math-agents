import OMAStatements.S_oeis_a363504
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic

/-!
# A363504 is a permutation of the positive integers

Source: https://oeis.org/A363504 (Scott R. Shannon, June 6, 2023).

The selector is prime(Omega(x)), with multiplicity in Omega. The proof
constructs the actual greedy sequence and proves full coverage. Recurrent
prime queues exhaust their multiples. If queue 2 stopped, selected primes
would be bounded by a finite early prefix. Prime powers of one fixed large
exponent would then be missing, bounding every late output, a contradiction.
Even numbers 2^t*r with r prime then force every prime queue to recur.

The general queue-exhaustion viewpoint is also used for the different,
distinct-factor selector A363956 in this public development, which explicitly
excludes the multiplicity-count variant treated here:
https://the-omega-institute.github.io/trureturing-mdbook/Library/Factorization/shannon2023a363956.html
-/

open scoped BigOperators
open OMA.S_oeis_a363504

namespace A363504Proof

lemma selected_prime (x : ℕ) : (selectedPrime x).Prime := Nat.prime_nth_prime _

lemma selected_of_prime {r : ℕ} (hr : r.Prime) : selectedPrime r = 2 := by
  simp [selectedPrime, Nat.primeFactorsList_prime hr, Nat.nth_prime_zero_eq_two]

lemma selected_of_pow {r : ℕ} (hr : r.Prime) (k : ℕ) :
    selectedPrime (r^k) = Nat.nth Nat.Prime (k-1) := by
  simp [selectedPrime, hr.primeFactorsList_pow]

lemma selected_of_mul_pow {r : ℕ} (hr : r.Prime) (t : ℕ) :
    selectedPrime (2^t*r) = Nat.nth Nat.Prime t := by
  have hlen := (Nat.perm_primeFactorsList_mul
    (pow_ne_zero t (by decide : (2 : ℕ) ≠ 0)) hr.ne_zero).length_eq
  simp only [List.length_append, Nat.prime_two.primeFactorsList_pow,
    List.length_replicate, Nat.primeFactorsList_prime hr, List.length_singleton] at hlen
  simp [selectedPrime, hlen]

section Coverage
variable (a p : ℕ → ℕ)
variable (h0 : a 0 = 2)
variable (hp : ∀ n, p n = selectedPrime (a n))
variable (hs : ∀ n, IsLeast {m : ℕ | 0 < m ∧ p n ∣ m ∧ ∀ i ≤ n, a i ≠ m} (a (n+1)))
include h0 hp hs

lemma positive (n : ℕ) : 0 < a n := by
  cases n with
  | zero => omega
  | succ n => exact (hs n).1.1

lemma prime_queue (n : ℕ) : (p n).Prime := by
  rw [hp n]
  exact Nat.prime_nth_prime _

lemma gt_one (n : ℕ) : 1 < a n := by
  cases n with
  | zero => omega
  | succ n =>
    have hle := Nat.le_of_dvd (positive a p h0 hp hs (n+1)) (hs n).1.2.1
    have := (prime_queue a p h0 hp hs n).two_le
    omega

lemma injective : Function.Injective a := by
  have hnot : ∀ i j, i < j → a i ≠ a j := by
    intro i j hij
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (hs k).1.2.2 i (by omega)
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

/-- A queue chosen arbitrarily late exhausts all its positive multiples. -/
lemma queue_full (q : ℕ) (hrec : ∀ N, ∃ n ≥ N, p n = q)
    (m : ℕ) (hm : 0 < m) (hqm : q ∣ m) : m ∈ Set.range a := by
  by_contra hmiss
  have hmiss' : ∀ i, a i ≠ m := by simpa [Set.mem_range] using hmiss
  obtain ⟨N, hN⟩ := eventually_large a p h0 hp hs m
  obtain ⟨n, hn, hpn⟩ := hrec N
  have hle := (hs n).2 (show 0 < m ∧ p n ∣ m ∧ ∀ i ≤ n, a i ≠ m from
    ⟨hm, hpn ▸ hqm, fun i _ => hmiss' i⟩)
  have hgt := hN (n+1) (by omega)
  omega


/-- Bounded queue indices would make all sufficiently high prime powers
missing, uniformly bounding the greedy outputs. -/
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
  have hprime_miss : ∀ r, r.Prime → B < r → ∀ i, a i ≠ r := by
    intro r hr hBr i heq
    by_cases hi : i ≤ N
    · have := hearly i hi; omega
    · have hp2 : p i = 2 := by rw [hp i, heq, selected_of_prime hr]
      exact hN i (by omega) hp2
  have hbound : ∀ n ≥ N, p n ≤ B := by
    intro n hn
    by_contra hbig
    have hprime := prime_queue a p h0 hp hs n
    have hmissing := hprime_miss (p n) hprime (by omega)
    have hle := (hs n).2 (show 0 < p n ∧ p n ∣ p n ∧ ∀ i ≤ n, a i ≠ p n from
      ⟨hprime.pos, dvd_rfl, fun i _ => hmissing i⟩)
    have hge := Nat.le_of_dvd (positive a p h0 hp hs (n+1)) (hs n).1.2.1
    have heq : a (n+1) = p n := by omega
    have hp2 : p (n+1) = 2 := by rw [hp (n+1), heq, selected_of_prime hprime]
    exact hN (n+1) (by omega) hp2
  let k := B+2
  have hk : 0 < k := by dsimp [k]; omega
  have hindex : B < Nat.nth Nat.Prime (k-1) := by
    have := Nat.add_two_le_nth_prime (k-1)
    dsimp [k] at *
    omega
  have hpowbig : ∀ r, r.Prime → B < r^k := by
    intro r hr
    have htwo : k < 2^k := Nat.lt_two_pow_self
    have hle : 2^k ≤ r^k := Nat.pow_le_pow_left hr.two_le k
    dsimp [k] at *
    omega
  have hpowmiss : ∀ r, r.Prime → ∀ i, a i ≠ r^k := by
    intro r hr i heq
    by_cases hi : i ≤ N
    · have := hearly i hi; have := hpowbig r hr; omega
    · have hb := hbound i (by omega)
      rw [hp i, heq, selected_of_pow hr] at hb
      omega
  obtain ⟨K, hK⟩ := eventually_large a p h0 hp hs (B^k)
  let n := max K N
  have hpn := prime_queue a p h0 hp hs n
  have hle := (hs n).2 (show 0 < (p n)^k ∧ p n ∣ (p n)^k ∧
      ∀ i ≤ n, a i ≠ (p n)^k from
    ⟨pow_pos hpn.pos _, dvd_pow_self _ (by omega), fun i _ => hpowmiss (p n) hpn i⟩)
  have hboundpow : (p n)^k ≤ B^k := Nat.pow_le_pow_left (hbound n (le_max_right _ _)) k
  have hgt := hK (n+1) (by dsimp [n]; omega)
  omega

/-- The even family 2^t*r has exactly t+1 prime factors with multiplicity. -/
lemma prime_recurrent (q : ℕ) (hq : q.Prime) : ∀ N, ∃ n ≥ N, p n = q := by
  classical
  let t := Nat.count Nat.Prime q
  have hqn : Nat.nth Nat.Prime t = q := Nat.nth_count hq
  by_cases ht : t = 0
  · have hq2 : q = 2 := by simpa [ht, Nat.nth_prime_zero_eq_two] using hqn.symm
    simpa only [hq2] using (two_recurrent a p h0 hp hs)
  intro N
  let B := 2 + ∑ i ∈ Finset.range (N+1), a i
  obtain ⟨r, hrB, hr⟩ := Nat.exists_infinite_primes (B+1)
  let m := 2^t*r
  have hpowpos : 0 < (2 : ℕ)^t := pow_pos (by decide) _
  have hm : B < m := by
    have := Nat.le_mul_of_pos_left r hpowpos
    dsimp [m]
    omega
  have htwo : 2 ∣ m := dvd_mul_of_dvd_left (dvd_pow_self 2 ht) _
  obtain ⟨i, hi⟩ := queue_full a p h0 hp hs 2 (two_recurrent a p h0 hp hs) m (by omega) htwo
  have hiN : N < i := by
    by_contra hn
    have hsum := Finset.single_le_sum (fun j _ => Nat.zero_le (a j))
      (Finset.mem_range.mpr (by omega : i < N+1))
    dsimp [B] at hm
    omega
  refine ⟨i, by omega, ?_⟩
  rw [hp i, hi, selected_of_mul_pow hr, hqn]

lemma covers : Set.range a = Set.Ioi 1 := by
  ext m
  constructor
  · rintro ⟨n, rfl⟩
    exact gt_one a p h0 hp hs n
  · intro hm
    change 1 < m at hm
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    exact queue_full a p h0 hp hs q (prime_recurrent a p h0 hp hs q hq) m (by omega) hqm

end Coverage

def TailGreedy (b : ℕ → ℕ) : Prop :=
  b 0 = 2 ∧ ∀ n, IsLeast {m : ℕ | 0 < m ∧ selectedPrime (b n) ∣ m ∧
    ∀ i ≤ n, b i ≠ m} (b (n+1))

lemma least_fresh (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ m, IsLeast {m : ℕ | 0 < m ∧ p ∣ m ∧ m ∉ S} m := by
  classical
  have hex : ∃ m, 0 < m ∧ p ∣ m ∧ m ∉ S := by
    refine ⟨p*(S.sup id+1), Nat.mul_pos hp (by omega), dvd_mul_right _ _, ?_⟩
    intro hm
    have hle : p*(S.sup id+1) ≤ S.sup id := Finset.le_sup (f := id) hm
    have hge := Nat.le_mul_of_pos_left (S.sup id+1) hp
    omega
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min' hex hm⟩

structure BuildState where
  value : ℕ
  history : Finset ℕ
  pos : 0 < value

noncomputable def primeOf (s : BuildState) : ℕ := selectedPrime s.value

lemma primeOf_spec (s : BuildState) : (primeOf s).Prime := selected_prime _

noncomputable def freshOf (s : BuildState) : ℕ :=
  (least_fresh s.history (primeOf s) (primeOf_spec s).pos).choose

lemma freshOf_spec (s : BuildState) :
    IsLeast {m : ℕ | 0 < m ∧ primeOf s ∣ m ∧ m ∉ s.history} (freshOf s) :=
  (least_fresh s.history (primeOf s) (primeOf_spec s).pos).choose_spec

noncomputable def advance (s : BuildState) : BuildState where
  value := freshOf s
  history := insert (freshOf s) s.history
  pos := (freshOf_spec s).1.1

noncomputable def states : ℕ → BuildState
  | 0 => ⟨2, {2}, by decide⟩
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

lemma exists_tail : ∃ a, TailGreedy a := by
  classical
  refine ⟨fun n => (states n).value, rfl, ?_⟩
  intro n
  have hf := freshOf_spec (states n)
  change IsLeast {m : ℕ | 0 < m ∧ primeOf (states n) ∣ m ∧
    ∀ i ≤ n, (states i).value ≠ m} (freshOf (states n))
  have hmem (m : ℕ) : m ∈ (states n).history ↔ ∃ i ≤ n, (states i).value = m := by
    rw [history_eq]
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, heq⟩; exact ⟨i, by omega, heq⟩
    · rintro ⟨i, hi, heq⟩; exact ⟨i, by omega, heq⟩
  constructor
  · refine ⟨hf.1.1, hf.1.2.1, ?_⟩
    intro i hi heq
    exact hf.1.2.2 ((hmem _).mpr ⟨i, hi, heq⟩)
  · intro m hm
    refine hf.2 ⟨hm.1, hm.2.1, ?_⟩
    intro h
    obtain ⟨i, hi, heq⟩ := (hmem m).mp h
    exact hm.2.2 i hi heq


def prependOne (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => b n

lemma greedy_of_tail (b : ℕ → ℕ) (hb : TailGreedy b) : Greedy (prependOne b) := by
  refine ⟨rfl, hb.1, ?_⟩
  intro n
  have h := hb.2 n
  change IsLeast {m : ℕ | 0 < m ∧ selectedPrime (b n) ∣ m ∧
    ∀ i ≤ n+1, prependOne b i ≠ m} (b (n+1))
  have hgt : 1 < b (n+1) := by
    have hle := Nat.le_of_dvd h.1.1 h.1.2.1
    have := (selected_prime (b n)).two_le
    omega
  constructor
  · refine ⟨h.1.1, h.1.2.1, ?_⟩
    intro i hi
    cases i with
    | zero => change 1 ≠ b (n+1); omega
    | succ i => exact h.1.2.2 i (by omega)
  · intro m hm
    refine h.2 ⟨hm.1, hm.2.1, ?_⟩
    intro i hi
    exact hm.2.2 (i+1) (by omega)

lemma tail_of_greedy (a : ℕ → ℕ) (ha : Greedy a) : TailGreedy (fun n => a (n+1)) := by
  refine ⟨ha.2.1, ?_⟩
  intro n
  have h := ha.2.2 n
  constructor
  · exact ⟨h.1.1, h.1.2.1, fun i hi => h.1.2.2 (i+1) (by omega)⟩
  · intro m hm
    refine h.2 ⟨hm.1, hm.2.1, ?_⟩
    have hgt : 1 < m := by
      have hle := Nat.le_of_dvd hm.1 hm.2.1
      change selectedPrime (a (n+1)) ≤ m at hle
      have := (selected_prime (a (n+1))).two_le
      omega
    intro i hi
    cases i with
    | zero => rw [ha.1]; omega
    | succ i => exact hm.2.2 i (by omega)

lemma full_of_tail (b : ℕ → ℕ) (hb : TailGreedy b) :
    Function.Injective (prependOne b) ∧ Set.range (prependOne b) = Set.Ioi 0 := by
  let p : ℕ → ℕ := fun n => selectedPrime (b n)
  have hp : ∀ n, p n = selectedPrime (b n) := fun _ => rfl
  have hgt : ∀ n, 1 < b n := gt_one b p hb.1 hp hb.2
  have hinj := injective b p hb.1 hp hb.2
  have hcover := covers b p hb.1 hp hb.2
  constructor
  · intro i j hij
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => have := hgt j; change 1 = b j at hij; omega
    | succ i =>
      cases j with
      | zero => have := hgt i; change b i = 1 at hij; omega
      | succ j => exact congrArg Nat.succ (hinj hij)
  · ext m
    constructor
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => change 0 < 1; omega
      | succ n => have := hgt n; change 0 < b n; omega
    · intro hm
      by_cases hm1 : m = 1
      · exact ⟨0, by simpa [prependOne] using hm1.symm⟩
      have hmem : m ∈ Set.range b := hcover.symm ▸ (show m ∈ Set.Ioi 1 from by change 1 < m; change 0 < m at hm; omega)
      obtain ⟨n, hn⟩ := hmem
      exact ⟨n+1, hn⟩

end A363504Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a363504.main := by
  constructor
  · obtain ⟨b, hb⟩ := A363504Proof.exists_tail
    exact ⟨A363504Proof.prependOne b, A363504Proof.greedy_of_tail b hb⟩
  · intro a ha
    let b : ℕ → ℕ := fun n => a (n+1)
    have hb : A363504Proof.TailGreedy b := A363504Proof.tail_of_greedy a ha
    have heq : a = A363504Proof.prependOne b := by
      funext n
      cases n with
      | zero => exact ha.1
      | succ n => rfl
    rw [heq]
    exact A363504Proof.full_of_tail b hb
