import OMAStatements.S_oeis_a353026
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic

/-!
# A353026: the least-exponent prime-factor permutation conjecture

Source: https://oeis.org/A353026 (Scott R. Shannon, April 18, 2022).

This proves existence, injectivity, and full positive range for the original
minimum rule. The selector minimizes factorization exponent among prime
divisors, breaking ties by the smallest prime. Its exact valuation behavior
on 2*q, 2^k*q, and 2*q^k supplies the recurrence argument. A two-step
least-unused-multiple argument rules out unbounded selected primes if queue
2 stops; missing numbers 2*q^k then bound every late output. Even terms
2^k*q force all other prime queues to recur.

The general queue-exhaustion viewpoint is also used for a different selector
in the public A363956 development:
https://the-omega-institute.github.io/trureturing-mdbook/Library/Factorization/shannon2023a363956.html
The present proof handles the distinct least-exponent selector of A353026.
The entry's separate empirical prime-successor observation is not asserted.
-/

open scoped BigOperators
open OMA.S_oeis_a353026

namespace A353026Proof

lemma selected_prime {r p : ℕ} (hr : r.Prime) (h : Selected r p) : p = r := by
  rcases (Nat.dvd_prime hr).mp h.2.1 with h1 | heq
  · exact False.elim (h.1.ne_one h1)
  · exact heq

lemma factorization_two_pow_mul {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (k : ℕ) :
    (2^k*r).factorization 2 = k ∧ (2^k*r).factorization r = 1 := by
  constructor <;>
    simp [Nat.factorization_mul (pow_ne_zero k (by decide : (2 : ℕ) ≠ 0)) hr.ne_zero,
      Nat.factorization_pow, Nat.prime_two.factorization, hr.factorization, hr2, Ne.symm hr2]

lemma selected_two_mul_prime {r p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : Selected (2*r) p) : p = 2 := by
  rcases h.1.dvd_mul.mp h.2.1 with h2 | hrdiv
  · exact (Nat.prime_dvd_prime_iff_eq h.1 Nat.prime_two).mp h2
  · have hpr := (Nat.prime_dvd_prime_iff_eq h.1 hr).mp hrdiv
    subst p
    have hf := factorization_two_pow_mul hr hr2 1
    simp only [pow_one] at hf
    have hle := (h.2.2 2 Nat.prime_two (dvd_mul_right 2 r)).2 (by omega)
    have := hr.two_le
    omega

lemma selected_two_pow_mul {r p k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : 2 ≤ k)
    (h : Selected (2^k*r) p) : p = r := by
  rcases h.1.dvd_mul.mp h.2.1 with h2 | hrdiv
  · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq h.1 Nat.prime_two).mp
      (h.1.dvd_of_dvd_pow h2)
    subst p
    have hf := factorization_two_pow_mul hr hr2 k
    have hle := (h.2.2 r hr (dvd_mul_left r (2^k))).1
    omega
  · exact (Nat.prime_dvd_prime_iff_eq h.1 hr).mp hrdiv

lemma selected_two_mul_pow {r p k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : 2 ≤ k)
    (h : Selected (2*r^k) p) : p = 2 := by
  rcases h.1.dvd_mul.mp h.2.1 with h2 | hrdiv
  · exact (Nat.prime_dvd_prime_iff_eq h.1 Nat.prime_two).mp h2
  · have hpr : p = r := (Nat.prime_dvd_prime_iff_eq h.1 hr).mp
      (h.1.dvd_of_dvd_pow hrdiv)
    subst p
    have hfac2 : (2*r^k).factorization 2 = 1 := by
      simp [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) (pow_ne_zero k hr.ne_zero),
        Nat.factorization_pow, Nat.prime_two.factorization, hr.factorization, hr2, Ne.symm hr2]
    have hfacr : (2*r^k).factorization r = k := by
      simp [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) (pow_ne_zero k hr.ne_zero),
        Nat.factorization_pow, Nat.prime_two.factorization, hr.factorization, hr2, Ne.symm hr2]
    have hle := (h.2.2 2 Nat.prime_two (dvd_mul_right 2 (r^k))).1
    omega

lemma exists_selected (x : ℕ) (hx : 1 < x) : ∃ p, Selected x p := by
  classical
  have hex : ∃ e, ∃ p, p.Prime ∧ p ∣ x ∧ x.factorization p = e := by
    obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (by omega : x ≠ 1)
    exact ⟨x.factorization p, p, hp, hpx, rfl⟩
  let e := Nat.find hex
  have hexp : ∃ p, p.Prime ∧ p ∣ x ∧ x.factorization p = e := Nat.find_spec hex
  let p := Nat.find hexp
  have hp : p.Prime ∧ p ∣ x ∧ x.factorization p = e := Nat.find_spec hexp
  refine ⟨p, hp.1, hp.2.1, ?_⟩
  intro q hq hqx
  constructor
  · have he : e ≤ x.factorization q := Nat.find_min' hex ⟨q, hq, hqx, rfl⟩
    omega
  · intro heq
    exact Nat.find_min' hexp ⟨hq, hqx, by omega⟩

lemma one_or_two_multiple {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hd : q ∣ m) (hle : m ≤ 2*q) : m = q ∨ m = 2*q := by
  obtain ⟨t, rfl⟩ := hd
  have htpos : 0 < t := by nlinarith
  have htbound : t ≤ 2 := by nlinarith
  rcases (show t = 1 ∨ t = 2 from by omega) with h | h
  · left; simp [h]
  · right; simp [h, mul_comm]

section Coverage
variable (a p : ℕ → ℕ)
variable (h0 : a 0 = 2)
variable (hp : ∀ n, Selected (a n) (p n))
variable (hs : ∀ n, IsLeast {m : ℕ | 0 < m ∧ p n ∣ m ∧ ∀ i ≤ n, a i ≠ m} (a (n+1)))
include h0 hp hs

lemma positive (n : ℕ) : 0 < a n := by
  cases n with
  | zero => omega
  | succ n => exact (hs n).1.1

lemma prime_queue (n : ℕ) : (p n).Prime := (hp n).1

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


/-- If queue 2 stopped, prime and twice-prime candidates force bounded
selected primes. Missing twice-prime-powers then bound all late outputs. -/
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
  have hmiss : ∀ m, B < m → (∀ q, Selected m q → q = 2) → ∀ i, a i ≠ m := by
    intro m hm hselect i heq
    by_cases hi : i ≤ N
    · have := hearly i hi; omega
    · have hsi : Selected m (p i) := heq ▸ hp i
      exact hN i (by omega) (hselect (p i) hsi)
  have hbound : ∀ n ≥ N, p n ≤ B := by
    intro n hn
    by_contra hbig
    let q := p n
    have hq : q.Prime := prime_queue a p h0 hp hs n
    have hq2 : q ≠ 2 := by dsimp [q]; omega
    have hqB : B < q := by dsimp [q]; omega
    have hmissing : ∀ i, a i ≠ 2*q := hmiss (2*q) (by omega)
      (fun t ht => selected_two_mul_prime hq hq2 ht)
    have hle := (hs n).2 (show 0 < 2*q ∧ p n ∣ 2*q ∧ ∀ i ≤ n, a i ≠ 2*q from
      ⟨by omega, dvd_mul_left _ _, fun i _ => hmissing i⟩)
    rcases one_or_two_multiple hq.pos (positive a p h0 hp hs (n+1)) (hs n).1.2.1 hle with heq | heq
    · have hnext : p (n+1) = q := selected_prime hq (heq ▸ hp (n+1))
      have hle2 := (hs (n+1)).2 (show 0 < 2*q ∧ p (n+1) ∣ 2*q ∧
          ∀ i ≤ n+1, a i ≠ 2*q from
        ⟨by omega, hnext ▸ dvd_mul_left q 2, fun i _ => hmissing i⟩)
      have hd2 : q ∣ a (n+2) := by simpa only [hnext] using (hs (n+1)).1.2.1
      rcases one_or_two_multiple hq.pos (positive a p h0 hp hs (n+2)) hd2 hle2 with heq2 | heq2
      · exact (hs (n+1)).1.2.2 (n+1) (by omega) (heq.trans heq2.symm)
      · exact hmissing (n+2) heq2
    · exact hmissing (n+1) heq
  let k := B+2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hpowbig : ∀ q, q.Prime → B < 2*q^k := by
    intro q hq
    have ht : k < 2^k := Nat.lt_two_pow_self
    have hpow : 2^k ≤ q^k := Nat.pow_le_pow_left hq.two_le k
    dsimp [k] at *
    omega
  obtain ⟨K, hK⟩ := eventually_large a p h0 hp hs (2*B^k)
  let n := max K N
  have hnN : N ≤ n := le_max_right _ _
  have hpn := prime_queue a p h0 hp hs n
  have hp2 : p n ≠ 2 := hN n hnN
  have hmissing := hmiss (2*(p n)^k) (hpowbig (p n) hpn)
    (fun t ht => selected_two_mul_pow hpn hp2 hk ht)
  have hle := (hs n).2 (show 0 < 2*(p n)^k ∧ p n ∣ 2*(p n)^k ∧
      ∀ i ≤ n, a i ≠ 2*(p n)^k from
    ⟨by have := pow_pos hpn.pos k; omega,
      dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _, fun i _ => hmissing i⟩)
  have hboundpow := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hbound n hnN) k)
  have hgt := hK (n+1) (by dsimp [n]; omega)
  omega

/-- Every even family 2^k*q with k>=2 selects the odd prime q. -/
lemma prime_recurrent (q : ℕ) (hq : q.Prime) : ∀ N, ∃ n ≥ N, p n = q := by
  classical
  by_cases hq2 : q = 2
  · subst q
    exact two_recurrent a p h0 hp hs
  intro N
  let B := 2 + ∑ i ∈ Finset.range (N+1), a i
  let k := B+2
  let m := 2^k*q
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hm : B < m := by
    have ht : k < 2^k := Nat.lt_two_pow_self
    have hmul := Nat.le_mul_of_pos_right (2^k) hq.pos
    dsimp [m, k] at *
    omega
  have htwo : 2 ∣ m := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
  obtain ⟨i, hi⟩ := queue_full a p h0 hp hs 2 (two_recurrent a p h0 hp hs) m (by omega) htwo
  have hiN : N < i := by
    by_contra hn
    have hsum := Finset.single_le_sum (fun j _ => Nat.zero_le (a j))
      (Finset.mem_range.mpr (by omega : i < N+1))
    dsimp [B] at hm
    omega
  exact ⟨i, by omega, selected_two_pow_mul hq hq2 hk (by simpa only [hi, m] using hp i)⟩

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
  b 0 = 2 ∧ ∀ n, ∃ p, Selected (b n) p ∧
    IsLeast {m : ℕ | 0 < m ∧ p ∣ m ∧ ∀ i ≤ n, b i ≠ m} (b (n+1))

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
  pos : 1 < value

noncomputable def primeOf (s : BuildState) : ℕ :=
  (exists_selected s.value s.pos).choose

lemma primeOf_spec (s : BuildState) : Selected s.value (primeOf s) :=
  (exists_selected s.value s.pos).choose_spec

noncomputable def freshOf (s : BuildState) : ℕ :=
  (least_fresh s.history (primeOf s) (primeOf_spec s).1.pos).choose

lemma freshOf_spec (s : BuildState) :
    IsLeast {m : ℕ | 0 < m ∧ primeOf s ∣ m ∧ m ∉ s.history} (freshOf s) :=
  (least_fresh s.history (primeOf s) (primeOf_spec s).1.pos).choose_spec

noncomputable def advance (s : BuildState) : BuildState where
  value := freshOf s
  history := insert (freshOf s) s.history
  pos := by
    have hle := Nat.le_of_dvd (freshOf_spec s).1.1 (freshOf_spec s).1.2.1
    have := (primeOf_spec s).1.two_le
    omega

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
  refine ⟨primeOf (states n), primeOf_spec _, ?_⟩
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
  obtain ⟨p, hp, h⟩ := hb.2 n
  refine ⟨p, hp, ?_⟩
  change IsLeast {m : ℕ | 0 < m ∧ p ∣ m ∧
    ∀ i ≤ n+1, prependOne b i ≠ m} (b (n+1))
  have hgt : 1 < b (n+1) := by
    have hle := Nat.le_of_dvd h.1.1 h.1.2.1
    have := hp.1.two_le
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
  obtain ⟨p, hp, h⟩ := ha.2.2 n
  refine ⟨p, hp, ?_⟩
  constructor
  · exact ⟨h.1.1, h.1.2.1, fun i hi => h.1.2.2 (i+1) (by omega)⟩
  · intro m hm
    refine h.2 ⟨hm.1, hm.2.1, ?_⟩
    have hgt : 1 < m := by
      have hle := Nat.le_of_dvd hm.1 hm.2.1
      change p ≤ m at hle
      have := hp.1.two_le
      omega
    intro i hi
    cases i with
    | zero => rw [ha.1]; omega
    | succ i => exact hm.2.2 i (by omega)

lemma full_of_tail (b : ℕ → ℕ) (hb : TailGreedy b) :
    Function.Injective (prependOne b) ∧ Set.range (prependOne b) = Set.Ioi 0 := by
  let p : ℕ → ℕ := fun n => (hb.2 n).choose
  have hp : ∀ n, Selected (b n) (p n) := fun n => (hb.2 n).choose_spec.1
  have hs : ∀ n, IsLeast {m : ℕ | 0 < m ∧ p n ∣ m ∧ ∀ i ≤ n, b i ≠ m} (b (n+1)) :=
    fun n => (hb.2 n).choose_spec.2
  have hgt : ∀ n, 1 < b n := gt_one b p hb.1 hp hs
  have hinj := injective b p hb.1 hp hs
  have hcover := covers b p hb.1 hp hs
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

end A353026Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a353026.main := by
  constructor
  · obtain ⟨b, hb⟩ := A353026Proof.exists_tail
    exact ⟨A353026Proof.prependOne b, A353026Proof.greedy_of_tail b hb⟩
  · intro a ha
    let b : ℕ → ℕ := fun n => a (n+1)
    have hb : A353026Proof.TailGreedy b := A353026Proof.tail_of_greedy a ha
    have heq : a = A353026Proof.prependOne b := by
      funext n
      cases n with
      | zero => exact ha.1
      | succ n => rfl
    rw [heq]
    exact A353026Proof.full_of_tail b hb
