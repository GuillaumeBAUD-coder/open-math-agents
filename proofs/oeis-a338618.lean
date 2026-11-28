import OMAStatements.S_oeis_a338618
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.PNat.Basic
import Mathlib.Order.PiLex
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Nodup
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Positivity

/-!
We construct the lexicographically least admissible sequence by choosing the least
unused locally admissible next positive integer. If a value were omitted, all
fixed prime factors would eventually disappear. A minimal remaining prime factor
then forces three consecutive distinct primes, contradicting admissibility.

Source: Remy Sigrist's conjecture in https://oeis.org/A338618.
The unchanged statement was contributed by @yuka30240.
-/

namespace A338618Proof

def GoodTriple (x y z : ℕ) : Prop :=
  1 < Nat.gcd x y ∨ 1 < Nat.gcd x z ∨ 1 < Nat.gcd y z

end A338618Proof

namespace A338618Proof

def Allowed (l : List ℕ) (m : ℕ) : Prop :=
  match l.reverse with
  | x :: y :: _ => GoodTriple y x m
  | _ => True

def Candidate (l : List ℕ) (m : ℕ) : Prop :=
  0 < m ∧ m ∉ l ∧ Allowed l m

lemma candidate_exists (l : List ℕ) (hn : l.Nodup)
    (hp : ∀ x ∈ l, 0 < x) : ∃ m, Candidate l m := by
  have fresh : ∀ m, l.sum < m → m ∉ l := by
    intro m hm hmem
    have := List.le_sum_of_mem hmem
    omega
  cases hr : l.reverse with
  | nil => exact ⟨l.sum + 1, by simp [Candidate, Allowed, hr, fresh]⟩
  | cons x xs =>
    cases xs with
    | nil => exact ⟨l.sum + 1, by simp [Candidate, Allowed, hr, fresh]⟩
    | cons y ys =>
      have hxmem : x ∈ l := by
        rw [← List.mem_reverse, hr]
        simp
      have hymem : y ∈ l := by
        rw [← List.mem_reverse, hr]
        simp
      have hx := hp x hxmem
      have hy := hp y hymem
      have hnd : (x :: y :: ys).Nodup := by
        rw [← hr]
        exact List.nodup_reverse.mpr hn
      have hxy : x ≠ y := by
        intro h
        exact (List.nodup_cons.mp hnd).1 (by simp [h])
      have hlarge : 1 < x ∨ 1 < y := by omega
      let m := (l.sum + 1) * (x * y)
      have hprod : 1 ≤ x * y := Nat.mul_pos hx hy
      have hm : l.sum < m := by dsimp [m]; nlinarith
      refine ⟨m, by omega, fresh m hm, ?_⟩
      simp only [Allowed, hr]
      rcases hlarge with hxl | hyl
      · right; right
        have hd : x ∣ m := ⟨(l.sum + 1) * y, by dsimp [m]; ring⟩
        simpa [Nat.gcd_eq_left hd] using hxl
      · right; left
        have hd : y ∣ m := ⟨(l.sum + 1) * x, by dsimp [m]; ring⟩
        simpa [Nat.gcd_eq_left hd] using hyl

def HistState := {l : List ℕ // l.Nodup ∧ ∀ x ∈ l, 0 < x}

noncomputable def next (s : HistState) : ℕ :=
  by classical exact Nat.find (candidate_exists s.val s.property.1 s.property.2)

lemma next_spec (s : HistState) : Candidate s.val (next s) :=
  by classical exact Nat.find_spec (candidate_exists s.val s.property.1 s.property.2)

lemma next_le (s : HistState) (m : ℕ) (hm : Candidate s.val m) : next s ≤ m :=
  by classical exact Nat.find_min' (candidate_exists s.val s.property.1 s.property.2) hm

noncomputable def extend (s : HistState) : HistState :=
  ⟨s.val ++ [next s], by
    have h := next_spec s
    constructor
    · simpa using List.Nodup.concat h.2.1 s.property.1
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact s.property.2 x hx
      · simp only [List.mem_singleton] at hx
        simpa [hx] using h.1⟩

noncomputable def historyState : ℕ → HistState
  | 0 => ⟨[], by simp⟩
  | n + 1 => extend (historyState n)

noncomputable def history (n : ℕ) : List ℕ := (historyState n).val

noncomputable def a (n : ℕ) : ℕ := next (historyState n)

@[simp] lemma history_zero : history 0 = [] := rfl

lemma history_succ (n : ℕ) : history (n + 1) = history n ++ [a n] := rfl

lemma a_spec (n : ℕ) : Candidate (history n) (a n) := next_spec (historyState n)

lemma a_pos (n : ℕ) : 0 < a n := (a_spec n).1

lemma a_fresh (n : ℕ) : a n ∉ history n := (a_spec n).2.1

lemma a_le_candidate (n m : ℕ) (hm : Candidate (history n) m) : a n ≤ m :=
  next_le (historyState n) m hm

lemma mem_history (n m : ℕ) : m ∈ history n ↔ ∃ i < n, a i = m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [history_succ, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h.symm⟩
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n
      · exact Or.inl ⟨i, hlt, h⟩
      · have : i = n := by omega
        exact Or.inr (this ▸ h.symm)

lemma a_injective : Function.Injective a := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact a_fresh j ((mem_history j (a j)).2 ⟨i, h, hij⟩)
  · exact a_fresh i ((mem_history i (a i)).2 ⟨j, h, hij.symm⟩)

lemma a_zero : a 0 = 1 := by
  have hp := a_pos 0
  have hl := a_le_candidate 0 1 (by simp [Candidate, Allowed])
  omega

lemma a_one : a 1 = 2 := by
  have hp := a_pos 1
  have hn := a_injective.ne (show (1 : ℕ) ≠ 0 by omega)
  rw [a_zero] at hn
  have hl := a_le_candidate 1 2 (by
    rw [show (1 : ℕ) = 0 + 1 by rfl, history_succ]
    simp [Candidate, Allowed, a_zero])
  omega

lemma allowed_history (n m : ℕ) :
    Allowed (history (n + 2)) m ↔ GoodTriple (a n) (a (n + 1)) m := by
  rw [show n + 2 = (n + 1) + 1 by omega, history_succ, history_succ]
  simp [Allowed, List.reverse_append]

lemma a_triple (n : ℕ) : GoodTriple (a n) (a (n + 1)) (a (n + 2)) :=
  (allowed_history n _).mp (a_spec (n + 2)).2.2

lemma a_greedy (n m : ℕ) (hm : 0 < m) (hu : ∀ i < n + 2, a i ≠ m)
    (hg : GoodTriple (a n) (a (n + 1)) m) : a (n + 2) ≤ m := by
  apply a_le_candidate
  refine ⟨hm, ?_, (allowed_history n m).mpr hg⟩
  rintro hmem
  obtain ⟨i, hi, he⟩ := (mem_history (n + 2) m).mp hmem
  exact hu i hi he

lemma a_greedy_unused (n m : ℕ) (hm : 0 < m) (hu : ∀ k, a k ≠ m)
    (hg : GoodTriple (a n) (a (n + 1)) m) : a (n + 2) ≤ m :=
  a_greedy n m hm (fun i _ => hu i) hg

lemma a_min_prefix (b : ℕ → ℕ) (hp : ∀ n, 0 < b n)
    (hi : Function.Injective b)
    (ht : ∀ n, GoodTriple (b n) (b (n + 1)) (b (n + 2)))
    (n : ℕ) (he : ∀ i < n, a i = b i) : a n ≤ b n := by
  rcases n with _ | (_ | n)
  · rw [a_zero]
    exact hp 0
  · rw [a_one]
    change 2 ≤ b 1
    have hb0 : b 0 = 1 := by simpa [a_zero] using (he 0 (by omega)).symm
    have hb1 : b 1 ≠ 1 := by
      intro h
      have := hi (h.trans hb0.symm)
      omega
    have := hp 1
    omega
  · apply a_greedy n (b (n + 2)) (hp _) _ _
    · intro i hii h
      have hbi := (he i hii).symm.trans h
      have := hi hbi
      omega
    · rw [he n (by omega), he (n + 1) (by omega)]
      exact ht n

end A338618Proof

namespace A338618Proof

def idx (n : ℕ) : ℕ+ := ⟨n + 1, by omega⟩

lemma idx_injective : Function.Injective idx := by
  intro n m h
  have := congrArg PNat.val h
  change n + 1 = m + 1 at this
  omega

lemma idx_pred (k : ℕ+) : idx (k.val - 1) = k := by
  apply Subtype.ext
  change k.val - 1 + 1 = k.val
  have := k.pos
  omega

lemma idx_surjective : Function.Surjective idx := fun k => ⟨k.val - 1, idx_pred k⟩

lemma idx_add_one (n : ℕ) : idx (n + 1) = idx n + 1 := by
  apply Subtype.ext
  change n + 1 + 1 = n + 1 + 1
  rfl

lemma idx_add_two (n : ℕ) : idx (n + 2) = idx n + 2 := by
  apply Subtype.ext
  change n + 2 + 1 = n + 1 + 2
  omega

def natSeq (b : ℕ+ → ℕ+) (n : ℕ) : ℕ := b (idx n)

lemma natSeq_pos (b : ℕ+ → ℕ+) (n : ℕ) : 0 < natSeq b n := (b (idx n)).pos

lemma natSeq_injective (b : ℕ+ → ℕ+) (hb : Function.Injective b) :
    Function.Injective (natSeq b) := by
  intro n m h
  apply idx_injective
  apply hb
  exact Subtype.ext h

lemma natSeq_triple (b : ℕ+ → ℕ+) (hb : OMA.S_oeis_a338618.Admissible b) (n : ℕ) :
    GoodTriple (natSeq b n) (natSeq b (n + 1)) (natSeq b (n + 2)) := by
  change GoodTriple (b (idx n)) (b (idx (n + 1))) (b (idx (n + 2)))
  rw [idx_add_two n, idx_add_one n]
  exact hb.2 (idx n)

noncomputable def posA (k : ℕ+) : ℕ+ := ⟨a (k.val - 1), a_pos _⟩

@[simp] lemma posA_idx (n : ℕ) : (posA (idx n) : ℕ) = a n := by
  simp [posA, idx]

lemma posA_admissible : OMA.S_oeis_a338618.Admissible posA := by
  constructor
  · intro k l h
    have he : a (k.val - 1) = a (l.val - 1) := congrArg PNat.val h
    have hn := a_injective he
    calc
      k = idx (k.val - 1) := (idx_pred k).symm
      _ = idx (l.val - 1) := congrArg idx hn
      _ = l := idx_pred l
  · intro k
    obtain ⟨n, rfl⟩ := idx_surjective k
    change GoodTriple (posA (idx n)) (posA (idx n + 1)) (posA (idx n + 2))
    rw [← idx_add_one, ← idx_add_two]
    simpa only [posA_idx] using a_triple n

lemma posA_lex_le (b : ℕ+ → ℕ+) (hb : OMA.S_oeis_a338618.Admissible b) :
    toLex posA ≤ toLex b := by
  classical
  apply le_of_not_gt
  intro hlt
  change Pi.Lex (· < ·) (· < ·) b posA at hlt
  obtain ⟨k, hprev, hlt⟩ := hlt
  let n := k.val - 1
  have hk : idx n = k := idx_pred k
  have he : ∀ i < n, a i = natSeq b i := by
    intro i hi
    have hik : idx i < k := by
      change i + 1 < k.val
      dsimp [n] at hi
      have := k.pos
      omega
    have h := congrArg PNat.val (hprev (idx i) hik)
    simpa only [posA_idx, natSeq] using h.symm
  have hmin := a_min_prefix (natSeq b) (natSeq_pos b) (natSeq_injective b hb.1)
    (natSeq_triple b hb) n he
  have hsmall : natSeq b n < a n := by
    change (b (idx n) : ℕ) < a n
    rw [hk]
    exact hlt
  omega

lemma posA_surjective_of (ha : ∀ m, 0 < m → ∃ n, a n = m) :
    Function.Surjective posA := by
  intro k
  obtain ⟨n, hn⟩ := ha k.val k.pos
  refine ⟨idx n, ?_⟩
  apply Subtype.ext
  change a n = k.val
  exact hn

end A338618Proof

namespace A338618Proof

lemma eventually_gt_of_injective {f : ℕ → ℕ} (hi : Function.Injective f) (b : ℕ) :
    ∃ N, ∀ n, N ≤ n → b < f n := by
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp hi.nat_tendsto_atTop (b + 1)
  exact ⟨N, fun n hn => by have := hN n hn; omega⟩

lemma common_prime_gcd_gt_one {x y p : ℕ} (hx : 0 < x) (hp : Nat.Prime p)
    (hpx : p ∣ x) (hpy : p ∣ y) : 1 < Nat.gcd x y := by
  exact hp.one_lt.trans_le
    (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left y hx) (Nat.dvd_gcd hpx hpy))

lemma prime_of_small_and_minFac {n q : ℕ} (hn : 0 < n)
    (hq : q ≤ n.minFac) (hsmall : n < q ^ 2) : Nat.Prime n := by
  by_contra h
  have hh := Nat.minFac_sq_le_self hn h
  nlinarith [Nat.mul_le_mul hq hq]

section Abstract

variable (f : ℕ → ℕ)

lemma unused_eventually_coprime (hpos : ∀ n, 0 < f n) (hi : Function.Injective f)
    (hg : ∀ n m, 0 < m → (∀ k, f k ≠ m) →
      GoodTriple (f n) (f (n + 1)) m → f (n + 2) ≤ m)
    (m : ℕ) (hm : 0 < m) (hu : ∀ k, f k ≠ m) :
    ∃ N, ∀ n, N ≤ n → Nat.Coprime (f n) m := by
  obtain ⟨N, hN⟩ := eventually_gt_of_injective hi m
  refine ⟨N, fun n hn => ?_⟩
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hh
  have hp := Nat.gcd_pos_of_pos_left m (hpos n)
  have hbad : 1 < Nat.gcd (f n) m := by omega
  have hle := hg n m hm hu (Or.inr (Or.inl hbad))
  have hgt := hN (n + 2) (by omega)
  omega

lemma missing_implies_eventual_coprime (hpos : ∀ n, 0 < f n) (hi : Function.Injective f)
    (hg : ∀ n m, 0 < m → (∀ k, f k ≠ m) →
      GoodTriple (f n) (f (n + 1)) m → f (n + 2) ≤ m)
    (hzero : f 0 = 1) (m : ℕ)
    (hm : 0 < m) (hu : ∀ k, f k ≠ m) (B : ℕ) (hB : 0 < B) :
    ∃ N, ∀ n, N ≤ n → Nat.Coprime (f n) B := by
  have hm1 : 1 < m := by
    have hz := hu 0
    rw [hzero] at hz
    omega
  obtain ⟨K, hK⟩ := unused_eventually_coprime f hpos hi hg m hm hu
  let S := (Finset.range K).sup f
  let M := (m * B) * (S + 1)
  have hMpos : 0 < M := mul_pos (mul_pos hm hB) (Nat.succ_pos S)
  have hmM : m ∣ M := dvd_mul_of_dvd_left (dvd_mul_right m B) (S + 1)
  have hBM : B ∣ M := dvd_mul_of_dvd_left (dvd_mul_left B m) (S + 1)
  have hSM : S + 1 ≤ M := by
    have hab : 1 ≤ m * B := Nat.succ_le_of_lt (mul_pos hm hB)
    simpa [M] using Nat.mul_le_mul_right (S + 1) hab
  have hMun : ∀ n, f n ≠ M := by
    intro n hn
    by_cases hnk : n < K
    · have hs : f n ≤ S := Finset.le_sup (f := f) (Finset.mem_range.mpr hnk)
      omega
    · have hc := hK n (by omega)
      rw [hn] at hc
      have he := Nat.eq_one_of_dvd_coprimes hc hmM (dvd_refl m)
      omega
  obtain ⟨N, hN⟩ := unused_eventually_coprime f hpos hi hg M hMpos hMun
  exact ⟨N, fun n hn => (hN n hn).of_dvd_right hBM⟩

lemma even_values_bounded
    (hall : ∀ B, 0 < B → ∃ N, ∀ n, N ≤ n → Nat.Coprime (f n) B) :
    ∃ E, 4 < E ∧ ∀ n, 2 ∣ f n → f n < E := by
  obtain ⟨N, hN⟩ := hall 2 (by decide)
  refine ⟨(Finset.range N).sup f + 5, by omega, ?_⟩
  intro n hn
  by_cases hlt : n < N
  · have hs : f n ≤ (Finset.range N).sup f :=
      Finset.le_sup (f := f) (Finset.mem_range.mpr hlt)
    omega
  · have hc := hN n (by omega)
    have hh := Nat.eq_one_of_dvd_coprimes hc hn (dvd_refl 2)
    omega

theorem abstract_surjective_positive (hpos : ∀ n, 0 < f n) (hi : Function.Injective f)
    (hg : ∀ n m, 0 < m → (∀ k, f k ≠ m) →
      GoodTriple (f n) (f (n + 1)) m → f (n + 2) ≤ m)
    (hzero : f 0 = 1)
    (htr : ∀ n, GoodTriple (f n) (f (n + 1)) (f (n + 2))) :
    ∀ m, 0 < m → ∃ n, f n = m := by
  classical
  intro m hm
  by_contra hmissing
  have hu : ∀ n, f n ≠ m := by simpa only [not_exists] using hmissing
  have hall : ∀ B, 0 < B → ∃ N, ∀ n, N ≤ n → Nat.Coprime (f n) B :=
    missing_implies_eventual_coprime f hpos hi hg hzero m hm hu
  obtain ⟨E, hE, hEven⟩ := even_values_bounded f hall
  obtain ⟨L, hL⟩ := hall E.factorial (Nat.factorial_pos E)
  obtain ⟨J, hJ⟩ := eventually_gt_of_injective hi 1
  let N := max L J + 1
  have hNpos : 1 ≤ N := by omega
  have htail : ∀ n, N ≤ n → 1 < f n ∧ E < (f n).minFac := by
    intro n hn
    have hnL : L ≤ n := by dsimp [N] at hn; omega
    have hnJ : J ≤ n := by dsimp [N] at hn; omega
    have hv := hJ n hnJ
    exact ⟨hv, (Nat.coprime_factorial_iff (by omega : f n ≠ 1)).mp (hL n hnL)⟩
  have hex : ∃ q, ∃ k, N ≤ k ∧ (f k).minFac = q :=
    ⟨(f N).minFac, N, le_rfl, rfl⟩
  let q := Nat.find hex
  obtain ⟨k, hk, hkq⟩ := Nat.find_spec hex
  change (f k).minFac = q at hkq
  have hqE : E < q := by simpa only [hkq] using (htail k hk).2
  have hqprime : Nat.Prime q := by
    rw [← hkq]
    exact Nat.minFac_prime (by have := (htail k hk).1; omega)
  have hqdvd : q ∣ f k := by rw [← hkq]; exact Nat.minFac_dvd _
  have hqmin : ∀ j, N ≤ j → q ≤ (f j).minFac := by
    intro j hj
    exact Nat.find_min' hex ⟨j, hj, rfl⟩
  have hq4 : 4 < q := by omega
  have hkpos : 1 ≤ k := hNpos.trans hk
  have h2qun : ∀ j, f j ≠ 2 * q := by
    intro j hj
    have hh := hEven j (by rw [hj]; exact dvd_mul_right 2 q)
    omega
  have hG := common_prime_gcd_gt_one (hpos k) hqprime hqdvd (dvd_mul_left q 2)
  have hrle : f (k + 1) ≤ 2 * q := by
    have hgg : GoodTriple (f (k - 1)) (f ((k - 1) + 1)) (2 * q) := by
      rw [show k - 1 + 1 = k by omega]
      exact Or.inr (Or.inr hG)
    have hh := hg (k - 1) (2 * q) (by omega) h2qun hgg
    simpa only [show k - 1 + 2 = k + 1 by omega] using hh
  have hsle : f (k + 2) ≤ 2 * q :=
    hg k (2 * q) (by omega) h2qun (Or.inr (Or.inl hG))
  have hrp : Nat.Prime (f (k + 1)) :=
    prime_of_small_and_minFac (hpos _) (hqmin _ (by omega)) (by nlinarith)
  have hsp : Nat.Prime (f (k + 2)) :=
    prime_of_small_and_minFac (hpos _) (hqmin _ (by omega)) (by nlinarith)
  have hqr : q ≤ f (k + 1) := by
    simpa only [hrp.minFac_eq] using hqmin (k + 1) (by omega)
  have h2run : ∀ j, f j ≠ 2 * f (k + 1) := by
    intro j hj
    have hh := hEven j (by rw [hj]; exact dvd_mul_right 2 (f (k + 1)))
    omega
  have hGr := common_prime_gcd_gt_one (hpos (k + 1)) hrp
    (dvd_refl _) (dvd_mul_left (f (k + 1)) 2)
  have htle : f (k + 3) ≤ 2 * f (k + 1) := by
    simpa only [Nat.add_assoc] using
      hg (k + 1) (2 * f (k + 1)) (by have := hpos (k + 1); omega)
        h2run (Or.inr (Or.inl hGr))
  have htp : Nat.Prime (f (k + 3)) :=
    prime_of_small_and_minFac (hpos _) (hqmin _ (by omega)) (by nlinarith)
  have hrs : Nat.Coprime (f (k + 1)) (f (k + 2)) :=
    (Nat.coprime_primes hrp hsp).mpr (fun he => by have := hi he; omega)
  have hrt : Nat.Coprime (f (k + 1)) (f (k + 3)) :=
    (Nat.coprime_primes hrp htp).mpr (fun he => by have := hi he; omega)
  have hst : Nat.Coprime (f (k + 2)) (f (k + 3)) :=
    (Nat.coprime_primes hsp htp).mpr (fun he => by have := hi he; omega)
  have hbad := htr (k + 1)
  simp only [GoodTriple, Nat.add_assoc, Nat.reduceAdd,
    hrs.gcd_eq_one, hrt.gcd_eq_one, hst.gcd_eq_one] at hbad
  omega

end Abstract
end A338618Proof

namespace A338618Proof

theorem solution : ∃ b : ℕ+ → ℕ+, OMA.S_oeis_a338618.Admissible b ∧
    (∀ c : ℕ+ → ℕ+, OMA.S_oeis_a338618.Admissible c → toLex b ≤ toLex c) ∧
    Function.Surjective b := by
  refine ⟨posA, posA_admissible, posA_lex_le, ?_⟩
  apply posA_surjective_of
  exact abstract_surjective_positive a a_pos a_injective a_greedy_unused a_zero a_triple

end A338618Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a338618.main := by
  exact A338618Proof.solution
