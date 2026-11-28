import OMAStatements.S_oeis_a076072
import Mathlib

/-!
# A076072. A divisible permutation of the digits in each successive block

Amarnath Murthy's conjecture uses the n consecutive integers beginning at
1 + n(n−1)/2. The registered Lean statement uses the n integers beginning at
n+1. `DecimalPermutations.original_conjecture` and `OMA.solution` establish
these two versions from the same general large-block theorem.

A swap of the adjacent digits d+1 and d changes the represented integer by
9 times a power of 10. Reserve enough trailing zeroes for the 2-part and the
5-part of n. The compatible factor shared with 9 is handled by digit sums.
In the reduced cyclic group, each optional swap translates by a generator.
Consequently m−1 available swaps cover all residues modulo m. The low three
digit positions provide enough pairs in every sufficiently long block. The
last section checks finite permutation certificates for the smaller sizes.

Source: https://oeis.org/A076072
-/

namespace DecimalPermutations

variable {m : ℕ} [NeZero m]

/-- Adding the option to use a unit strictly enlarges any proper, nonempty
set of attainable residues. -/
private theorem grow (s : Finset (ZMod m)) (hz : 0 ∈ s) (hs : s ≠ Finset.univ)
    (u : (ZMod m)ˣ) : s.card < (s ∪ s.image (· + (u : ZMod m))).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
  intro heq
  have close {x : ZMod m} (hx : x ∈ s) : x + u ∈ s := by
    rw [heq]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)
  have mult (k : ℕ) : (k : ZMod m) * u ∈ s := by
    induction k with
    | zero => simpa using hz
    | succ k ih => simpa [Nat.cast_succ, add_mul] using close ih
  apply hs
  apply Finset.eq_univ_of_forall
  intro a
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (a * (↑u⁻¹ : ZMod m))
  simpa [hk, mul_assoc] using mult k

private def optionalSums (m : ℕ) [NeZero m] : List (ZMod m)ˣ → Finset (ZMod m)
  | [] => {0}
  | u :: us => optionalSums m us ∪ (optionalSums m us).image (· + (u : ZMod m))

private theorem zero_mem_optionalSums (l : List (ZMod m)ˣ) : 0 ∈ optionalSums m l := by
  induction l with
  | nil => simp [optionalSums]
  | cons _ _ ih => exact Finset.mem_union_left _ ih

private theorem optionalSums_full_or_growing (l : List (ZMod m)ˣ) :
    optionalSums m l = Finset.univ ∨ l.length < (optionalSums m l).card := by
  induction l with
  | nil => right; simp [optionalSums]
  | cons u us ih =>
    by_cases h : optionalSums m us = Finset.univ
    · left; simp [optionalSums, h]
    · right
      have h1 := ih.resolve_left h
      have h2 := grow (optionalSums m us) (zero_mem_optionalSums us) h u
      simp only [List.length_cons, optionalSums]
      omega

/-- Every residue is the sum of a sublist of any list of at least m-1 units
of Z/m. Repetitions are allowed and the units can differ. -/
theorem exists_sublist_sum_units (l : List (ZMod m)ˣ) (hl : m ≤ l.length + 1)
    (r : ZMod m) : ∃ t : List (ZMod m)ˣ, t.Sublist l ∧ (t.map Units.val).sum = r := by
  have cover : optionalSums m l = Finset.univ := by
    rcases optionalSums_full_or_growing l with h | h
    · exact h
    · apply Finset.eq_univ_of_card
      have hbound := Finset.card_le_univ (optionalSums m l)
      rw [ZMod.card] at hbound ⊢
      omega
  have hr : r ∈ optionalSums m l := by simp [cover]
  clear cover hl
  induction l generalizing r with
  | nil =>
    simp [optionalSums] at hr
    exact ⟨[], .slnil, by simp [hr]⟩
  | cons u us ih =>
    obtain h | h := Finset.mem_union.mp hr
    · obtain ⟨t, ht, hs⟩ := ih _ h
      exact ⟨t, ht.cons _, hs⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨t, ht, hs⟩ := ih _ hx
      exact ⟨u :: t, ht.cons_cons _, by simp [hs, add_comm]⟩

end DecimalPermutations

namespace DecimalPermutations

/-- Each entry `a` of the list specifies a pair of digits `a+1,a`. The first
entry specifies the most significant pair. The digits of a word are stored
least significant first, as in `Nat.digits`. -/
def pairWord : List ℕ → List ℕ
  | [] => []
  | a :: as => pairWord as ++ [a + 1, a]

private theorem length_pairWord (as : List ℕ) : (pairWord as).length = 2 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [pairWord, ih]; omega

private def weights {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) : ℕ → List (ZMod m)ˣ
  | 0 => []
  | k+1 => u ^ k :: weights u k

private lemma length_weights {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) (n : ℕ) :
    (weights u n).length = n := by induction n <;> simp [weights, *]

private theorem realize {m : ℕ} [NeZero m] (h : Nat.Coprime 100 m) (as : List ℕ)
    (r : ZMod m) (hr : r ∈ optionalSums m (weights (ZMod.unitOfCoprime 100 h) as.length)) :
    ∃ w : List ℕ, w.Perm (pairWord as) ∧ ∃ k : ℕ,
      Nat.ofDigits 10 w = Nat.ofDigits 10 (pairWord as) + 9*k ∧ (k : ZMod m) = r := by
  induction as generalizing r with
  | nil =>
    simp [weights, optionalSums] at hr
    exact ⟨[], .nil, 0, by rfl, by simp [hr]⟩
  | cons a as ih =>
    simp only [List.length_cons, weights, optionalSums, Finset.mem_union, Finset.mem_image] at hr
    have hp : Nat.ofDigits 10 [a+1,a] + 9 = Nat.ofDigits 10 [a,a+1] := by
      simp [Nat.ofDigits]; omega
    have hpow : 10 ^ (pairWord as).length = 100 ^ as.length := by
      rw [length_pairWord, pow_mul]; norm_num
    obtain hr | ⟨s, hs, rfl⟩ := hr
    · obtain ⟨w, hw, k, hk, hkr⟩ := ih r hr
      refine ⟨w ++ [a+1,a], hw.append_right _, k, ?_, hkr⟩
      rw [pairWord, Nat.ofDigits_append, Nat.ofDigits_append, hw.length_eq, hk]; omega
    · obtain ⟨w, hw, k, hk, hkr⟩ := ih s hs
      refine ⟨w ++ [a,a+1], hw.append (List.Perm.swap _ _ _), k + 100 ^ as.length, ?_, ?_⟩
      · rw [pairWord, Nat.ofDigits_append, Nat.ofDigits_append, hw.length_eq, hk, hpow, ← hp]; ring
      · simp [hkr, ZMod.coe_unitOfCoprime]

/-- Independently swapping adjacent digits whose values differ by one permits
any prescribed correction to the decimal value, after dividing the correction
by nine. -/
theorem decimal_swap_residues {m : ℕ} [NeZero m] (h : Nat.Coprime 100 m)
    (as : List ℕ) (ha : m ≤ as.length+1) (r : ZMod m) :
    ∃ w : List ℕ, w.Perm (pairWord as) ∧ ∃ k : ℕ,
      Nat.ofDigits 10 w = Nat.ofDigits 10 (pairWord as) + 9*k ∧ (k : ZMod m) = r := by
  apply realize h as r
  have hcover := optionalSums_full_or_growing (weights (ZMod.unitOfCoprime 100 h) as.length)
  rcases hcover with heq | hlt
  · simp [heq]
  · have hupper := Finset.card_le_univ (optionalSums m (weights (ZMod.unitOfCoprime 100 h) as.length))
    rw [ZMod.card] at hupper
    rw [length_weights] at hlt
    by_cases heq : optionalSums m (weights (ZMod.unitOfCoprime 100 h) as.length) = Finset.univ
    · simp [heq]
    · have hs := Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨Finset.subset_univ _, heq⟩)
      rw [Finset.card_univ, ZMod.card] at hs
      omega

end DecimalPermutations

namespace DecimalPermutations

/-- Reserve the low zeroes for powers of 2 and 5.  In the remaining part,
`g` is the common divisor with 9, and `m` is the residual modulus. -/
theorem decimal_swap_multiple {m : ℕ} [NeZero m] (hm : Nat.Coprime 100 m)
    (g c n z : ℕ) (h9 : 9 = g*c) (hc : Nat.Coprime c m)
    (hn : n ∣ 10^z * (g*m)) (pairs high : List ℕ)
    (hl : m ≤ pairs.length + 1) (hg : g ∣ Nat.ofDigits 10 (pairWord pairs ++ high)) :
    ∃ w : List ℕ, w.Perm (pairWord pairs) ∧
      n ∣ Nat.ofDigits 10 (List.replicate z 0 ++ w ++ high) := by
  obtain ⟨v, hv⟩ := hg
  let cu := ZMod.unitOfCoprime c hc
  obtain ⟨w, hw, k, hk, hkr⟩ := decimal_swap_residues hm pairs hl (-(v : ZMod m) * (↑cu⁻¹ : ZMod m))
  refine ⟨w, hw, ?_⟩
  have hd : m ∣ v + c*k := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [hkr]
    have hu : (c : ZMod m) = (↑cu : ZMod m) := (ZMod.coe_unitOfCoprime _ _).symm
    rw [hu]
    simp [mul_left_comm]
  have hval : Nat.ofDigits 10 (w ++ high) = g * (v+c*k) := by
    rw [Nat.ofDigits_append] at hv ⊢
    rw [hw.length_eq, hk]
    calc
      _ = (Nat.ofDigits 10 (pairWord pairs) + 10 ^ (pairWord pairs).length * Nat.ofDigits 10 high) + 9*k := by ring
      _ = g * (v+c*k) := by rw [hv, h9]; ring
  rw [List.append_assoc, Nat.ofDigits_append, Nat.ofDigits_replicate_zero, List.length_replicate, zero_add, hval]
  exact hn.trans (Nat.mul_dvd_mul_left _ (Nat.mul_dvd_mul_left _ hd))

end DecimalPermutations

namespace DecimalPermutations

/-- All decimal digits (little endian in each entry) in a consecutive block. -/
def blockDigits (s n : ℕ) : List ℕ := (List.range n).flatMap (fun i => Nat.digits 10 (s+i))

private theorem block_count (s n d : ℕ) :
    (blockDigits s n).count d = ∑ i ∈ Finset.range n, (Nat.digits 10 (s+i)).count d := by
  induction n with
  | zero => simp [blockDigits]
  | succ n ih => simpa [blockDigits, List.range_succ, Finset.sum_range_succ] using ih

private def occurrence (p d x : ℕ) : ℕ := if x / p % 10 = d then 1 else 0

private theorem first_three (x d : ℕ) (hx : 100 ≤ x) :
    occurrence 1 d x + occurrence 10 d x + occurrence 100 d x ≤ (Nat.digits 10 x).count d := by
  have h1 : x ≠ 0 := by omega
  have h2 : x / 10 ≠ 0 := by omega
  have h3 : x / 10 / 10 ≠ 0 := by omega
  rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 10) h1,
    Nat.digits_eq_cons_digits_div (by decide : 1 < 10) h2,
    Nat.digits_eq_cons_digits_div (by decide : 1 < 10) h3]
  simp only [List.count_cons, beq_iff_eq, Nat.div_div_eq_div_mul, Nat.reduceMul,
    occurrence, Nat.div_one]
  split <;> split <;> split <;> omega

private theorem periodic_sum_shift (f : ℕ → ℕ) (T : ℕ) (periodic : ∀ x, f (x+T) = f x)
    (s : ℕ) : (∑ i ∈ Finset.range T, f (s+i)) = ∑ i ∈ Finset.range T, f i := by
  induction s with
  | zero => simp
  | succ s ih =>
    have a := Finset.sum_range_succ (fun i => f (s+i)) T
    have b := Finset.sum_range_succ' (fun i => f (s+i)) T
    simp only [Nat.add_zero, periodic] at a b
    have move : (fun i => f (s + (i+1))) = (fun i => f (s+1+i)) := by
      funext i; congr 1; omega
    rw [move] at b
    omega

private theorem periodic_lower (f : ℕ → ℕ) (T A : ℕ) (_hT : 0 < T)
    (periodic : ∀ x, f (x+T) = f x) (total : ∑ i ∈ Finset.range T, f i = A)
    (s n : ℕ) : n / T * A ≤ ∑ i ∈ Finset.range n, f (s+i) := by
  have blocks (q : ℕ) : (∑ i ∈ Finset.range (q*T), f (s+i)) = q*A := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simp_rw [← Nat.add_assoc]
      rw [periodic_sum_shift f T periodic (s+q*T), total, Nat.succ_mul]
  rw [← blocks]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.div_mul_le_self n T))
  intros; omega

private theorem unit_total (d : ℕ) (hd : d < 10) :
    (∑ i ∈ Finset.range 10, occurrence 1 d i) = 1 := by
  interval_cases d <;> decide
private theorem tens_total (d : ℕ) (hd : d < 10) :
    (∑ i ∈ Finset.range 100, occurrence 10 d i) = 10 := by
  interval_cases d <;> decide +kernel
private theorem hundreds_total (d : ℕ) (hd : d < 10) :
    (∑ i ∈ Finset.range 1000, occurrence 100 d i) = 100 := by
  interval_cases d <;> decide +kernel

/-- In any block of n consecutive integers of at least three digits, each
of the ten digits occurs at least this often in the lowest three places. -/
theorem digit_count_lower (s n d : ℕ) (hs : 100 ≤ s) (hd : d < 10) :
    n / 10 + 10 * (n / 100) + 100 * (n / 1000) ≤ (blockDigits s n).count d := by
  have hu := periodic_lower (occurrence 1 d) 10 1 (by decide)
    (by intro x; simp [occurrence]) (unit_total d hd) s n
  have ht := periodic_lower (occurrence 10 d) 100 10 (by decide)
    (by intro x; rw [occurrence, occurrence, show (x+100)/10%10 = x/10%10 by omega]) (tens_total d hd) s n
  have hh := periodic_lower (occurrence 100 d) 1000 100 (by decide)
    (by intro x; rw [occurrence, occurrence, show (x+1000)/100%10 = x/100%10 by omega]) (hundreds_total d hd) s n
  rw [block_count]
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun (i : ℕ) _ => first_three (s+i) d (by omega))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  omega

end DecimalPermutations

namespace DecimalPermutations

/-- The sum of a consecutive block of length n is a multiple of every odd
divisor of n, in particular every common divisor of n and 9. -/
private theorem block_sum_dvd (s n g : ℕ) (hg : g ∣ 9) (hn : g ∣ n) :
    g ∣ ∑ i ∈ Finset.range n, (s+i) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine dvd_add (dvd_mul_of_dvd_left hn _) ?_
  have hp : Nat.Coprime g 2 := Nat.Coprime.of_dvd_left hg (by decide : Nat.Coprime 9 2)
  apply hp.dvd_of_dvd_mul_left
  rw [Nat.mul_comm 2, Finset.sum_range_id_mul_two]
  exact dvd_mul_of_dvd_left hn _

private theorem block_modNine (s n : ℕ) :
    ∑ i ∈ Finset.range n, (s+i) ≡ (blockDigits s n).sum [MOD 9] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [Finset.sum_range_succ, blockDigits, List.range_succ] using
      ih.add (Nat.modEq_digits_sum 9 10 (by decide) (s+n))

/-- Any permutation of all decimal digits in a block of length n is
already divisible by the common part of n and 9. -/
theorem block_divisor_nine (s n g : ℕ) (hg : g ∣ 9) (hn : g ∣ n)
    (w : List ℕ) (hw : w.Perm (blockDigits s n)) : g ∣ Nat.ofDigits 10 w := by
  have hw9 : Nat.ofDigits 10 w ≡ w.sum [MOD 9] := by
    simpa [Nat.ofDigits_one] using Nat.ofDigits_modEq' 10 1 9 (by decide) w
  rw [hw.sum_eq] at hw9
  have hc := ((block_modNine s n).trans hw9.symm).of_dvd hg
  exact (hc.dvd_iff (dvd_refl g)).mp (block_sum_dvd s n g hg hn)

theorem block_digit_lt (s n d : ℕ) (hd : d ∈ blockDigits s n) : d < 10 := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hd
  exact Nat.digits_lt_base (by decide) hi

end DecimalPermutations

namespace DecimalPermutations

lemma allocation_size (n : ℕ) (hn : 1000 ≤ n) :
    let z := n / 100 + 2
    let T := n / 10 + 10 * (n / 100) + 100 * (n / 1000)
    z + 1 ≤ T ∧ n ≤ 5 * (T-z-1) ∧ n ≤ 2^z := by
  dsimp only
  have hpow : ∀ k : ℕ, 10 ≤ k → 100 * (k+1) ≤ 2^(k+2) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      rw [show k+1+2 = (k+2)+1 by omega, pow_succ]; omega
  have := hpow (n/100) (by omega)
  omega

lemma decimal_factors (n z : ℕ) (hn : 0 < n) (hz : n ≤ 2^z) :
    ∃ m g c : ℕ, 0 < m ∧ m ≤ n ∧ Nat.Coprime 100 m ∧ 9 = g*c ∧ Nat.Coprime c m ∧
      n ∣ 10^z * (g*m) ∧ g ∣ 9 ∧ g ∣ n := by
  let u := ordCompl[2] n
  let v := ordCompl[5] u
  have hu : 0 < u := Nat.ordCompl_pos _ hn.ne'
  have hv : 0 < v := Nat.ordCompl_pos _ hu.ne'
  have hun : u ∣ n := Nat.ordCompl_dvd _ _
  have hvu : v ∣ u := Nat.ordCompl_dvd _ _
  have hvn := hvu.trans hun
  let g := Nat.gcd 9 v
  let m := v / g
  let c := 9 / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by decide)
  have hgv : g ∣ v := Nat.gcd_dvd_right _ _
  have hg9 : g ∣ 9 := Nat.gcd_dvd_left _ _
  have hgm : g*m = v := Nat.mul_div_cancel' hgv
  have hgc : g*c = 9 := Nat.mul_div_cancel' hg9
  have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd hv hgv) hg
  have hmv : m ∣ v := ⟨g, by simpa [Nat.mul_comm] using hgm.symm⟩
  have h2 : Nat.Coprime 2 m := (Nat.coprime_ordCompl Nat.prime_two hn.ne').of_dvd_right (hmv.trans hvu)
  have h5 : Nat.Coprime 5 m := (Nat.coprime_ordCompl (by decide : Nat.Prime 5) hu.ne').of_dvd_right hmv
  have hc : Nat.Coprime c m := Nat.coprime_div_gcd_div_gcd hg
  refine ⟨m,g,c,hm,Nat.le_of_dvd hn (hmv.trans hvn),?_,hgc.symm,hc,?_,hg9,hgv.trans hvn⟩
  · convert (h2.mul_left h5).pow_left 2 using 1
  · rw [hgm]
    have hx : ordProj[2] n ∣ 2^z := pow_dvd_pow _ (Nat.factorization_le_of_le_pow hz)
    have hy : ordProj[5] u ∣ 5^z := pow_dvd_pow _ (Nat.factorization_le_of_le_pow
      ((Nat.le_of_dvd hn hun).trans (hz.trans (Nat.pow_le_pow_left (by decide : 2 ≤ 5) _))))
    have he : ordProj[2] n * ordProj[5] u * v = n := by
      rw [Nat.mul_assoc, show ordProj[5] u * v = u from Nat.ordProj_mul_ordCompl_eq_self u 5]
      exact Nat.ordProj_mul_ordCompl_eq_self n 2
    rw [← he]
    convert Nat.mul_dvd_mul_right (Nat.mul_dvd_mul hx hy) v using 1 <;> norm_num [← mul_pow]

end DecimalPermutations

namespace DecimalPermutations

/-- Each round takes one copy of each of the ten digits, in five pairs. -/
private def pairRounds : ℕ → List ℕ
  | 0 => []
  | r+1 => 0 :: 2 :: 4 :: 6 :: 8 :: pairRounds r

private theorem length_rounds (r : ℕ) : (pairRounds r).length = 5*r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [pairRounds, ih]; omega

private theorem count_rounds (d r : ℕ) : (pairWord (pairRounds r)).count d = if d<10 then r else 0 := by
  induction r with
  | zero => simp [pairRounds, pairWord]
  | succ r ih =>
    simp only [pairRounds, pairWord, List.count_append, List.count_cons, List.count_nil, ih]
    by_cases h : d < 10
    · interval_cases d <;> simp
    · simp only [h, ↓reduceIte, beq_iff_eq]
      split_ifs <;> omega

/-- Given enough digits for r rounds, reserve z zeroes and one leading 9,
then rearrange the remaining digits above the optional pairs. -/
theorem from_inventory (s n z g m c r : ℕ) [NeZero m] (hs : 100 ≤ s)
    (hm : Nat.Coprime 100 m) (hc : Nat.Coprime c m) (hg : g*c = 9) (hg₁ : g ∣ n)
    (hdiv : n ∣ 10^z * (g*m))
    (hcount : r+z+1 ≤ n/10+10*(n/100)+100*(n/1000)) (hpairs : m ≤ 5*r+1) :
    ∃ x : ℕ, 0 < x ∧ n ∣ x ∧ (Nat.digits 10 x).Perm (blockDigits s n) := by
  let zeros := List.replicate z 0
  let pairs := pairWord (pairRounds r)
  let used := zeros ++ pairs ++ [9]
  let free := (blockDigits s n).diff used
  let high := free ++ [9]
  have avail (d : ℕ) : used.count d ≤ (blockDigits s n).count d := by
    simp only [used, zeros, pairs, List.count_append, count_rounds, List.count_replicate,
      List.count_cons, List.count_nil, beq_iff_eq]
    by_cases h : d < 10
    · have hb := digit_count_lower s n d hs h
      split_ifs <;> omega
    · split_ifs <;> omega
  have perm_base : (zeros ++ pairs ++ high).Perm (blockDigits s n) := by
    apply List.perm_iff_count.mpr
    intro d
    have ha := avail d
    simp only [high, free, List.count_append, List.count_diff, used] at ha ⊢
    omega
  have perm_highzeros : ((pairs ++ high) ++ zeros).Perm (blockDigits s n) := by
    apply (List.perm_append_comm (l₁ := pairs ++ high) (l₂ := zeros)).trans
    simpa only [List.append_assoc] using perm_base
  have nine : g ∣ 9 := by rw [← hg]; exact dvd_mul_right _ _
  have hstart := block_divisor_nine s n g nine hg₁ _ perm_highzeros
  have hp : g ∣ Nat.ofDigits 10 (pairs ++ high) := by
    simpa only [zeros, Nat.ofDigits_append_replicate_zero] using hstart
  obtain ⟨w, hw, hd⟩ := decimal_swap_multiple hm g c n z hg.symm hc hdiv (pairRounds r) high
    (by simpa only [length_rounds] using hpairs) hp
  let result := zeros ++ w ++ high
  have hp' : result.Perm (blockDigits s n) := ((hw.append_left zeros).append_right high).trans perm_base
  have bounds (d : ℕ) (hd : d ∈ result) := block_digit_lt s n d (hp'.mem_iff.mp hd)
  have nz (h : result ≠ []) : result.getLast h ≠ 0 := by
    simp [result, high, ← List.append_assoc]
  have decode := Nat.digits_ofDigits 10 (by decide) result bounds nz
  refine ⟨Nat.ofDigits 10 result, ?_, hd, by rw [decode]; exact hp'⟩
  by_contra! h
  have hn : Nat.ofDigits 10 result = 0 := by omega
  have : result = [] := by simpa [hn] using decode.symm
  simp [result, high] at this

end DecimalPermutations

namespace DecimalPermutations

/-- Above the finite range, the same construction works for every
consecutive block with a three-digit starting number or larger. -/
theorem multiple_from_large_block (s n : ℕ) (hn : 1000 ≤ n) (hs : 100 ≤ s) :
    ∃ x : ℕ, 0 < x ∧ n ∣ x ∧ (Nat.digits 10 x).Perm (blockDigits s n) := by
  let z := n/100 + 2
  let T := n/10 + 10*(n/100) + 100*(n/1000)
  have ⟨hz, hr, hp⟩ := allocation_size n hn
  obtain ⟨m, g, c, hm, hmn, h100, hgc, hcm, hdiv, _, hgn⟩ :=
    decimal_factors n z (by omega) hp
  have : NeZero m := ⟨hm.ne'⟩
  apply from_inventory s n z g m c (T-z-1) hs h100 hcm hgc.symm hgn hdiv
  · dsimp only [T,z] at *; omega
  · dsimp only [T,z] at *; omega

end DecimalPermutations

namespace DecimalPermutations

/-- Convert a block indexed from zero to the inclusive interval in the target. -/
private theorem block_to_interval (s n : ℕ) : (blockDigits s n : Multiset ℕ) =
    (Finset.Ico s (s+n)).sum (fun k => (Nat.digits 10 k : Multiset ℕ)) := by
  induction n with
  | zero => simp [blockDigits]
  | succ n ih =>
    have h : s+n ∉ Finset.Ico s (s+n) := by simp
    rw [show s + (n + 1) = (s+n).succ by omega, Nat.Ico_succ_right_eq_insert_Ico (show s ≤ s+n by omega), Finset.sum_insert h, ← ih]
    simpa [blockDigits, List.range_succ] using List.perm_append_comm (l₁ := (blockDigits s n)) (l₂ := Nat.digits 10 (s+n))

private theorem max_ne_zero_of_witness (D : Multiset ℕ) (n x : ℕ)
    (hx : 0 < x) (hd : n ∣ x) (hw : (Nat.digits 10 x : Multiset ℕ) = D) :
    sSup {m : ℕ | 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m : Multiset ℕ) = D} ≠ 0 := by
  have hb : BddAbove {m : ℕ | 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m : Multiset ℕ) = D} := by
    refine ⟨10 ^ D.card, ?_⟩
    intro y hy
    have hc := congrArg Multiset.card hy.2.2
    change (Nat.digits 10 y).length = D.card at hc
    exact (Nat.lt_base_pow_length_digits (b := 10) (m := y) (by decide) |>.le.trans (by rw [hc]))
  have hx' := le_csSup hb (show x ∈ {m : ℕ | 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m : Multiset ℕ) = D} from ⟨hx, hd, hw⟩)
  omega

/-- The formalized interval is n+1 through 2n. -/
theorem pinned_of_interval (n : ℕ)
    (h : ∃ x : ℕ, 0 < x ∧ n ∣ x ∧ (Nat.digits 10 x).Perm (blockDigits (n+1) n)) :
    OMA.S_oeis_a076072.a n ≠ 0 := by
  obtain ⟨x, hx, hd, hw⟩ := h
  apply max_ne_zero_of_witness _ n x hx hd
  calc
    _ = (blockDigits (n+1) n : Multiset ℕ) := Quot.sound hw
    _ = OMA.S_oeis_a076072.nextDigits n := by
      rw [block_to_interval, OMA.S_oeis_a076072.nextDigits]
      congr 1
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Icc]; omega

/-- The original OEIS problem starts its n-th block at 1+n(n−1)/2. -/
theorem original_of_interval (n : ℕ)
    (h : ∃ x : ℕ, 0 < x ∧ n ∣ x ∧ (Nat.digits 10 x).Perm
      (blockDigits (1 + n*(n-1)/2) n)) :
    sSup {m : ℕ | 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m : Multiset ℕ) =
      (Finset.Icc (1 + n*(n-1)/2) (n*(n+1)/2)).sum (fun k => (Nat.digits 10 k : Multiset ℕ))} ≠ 0 := by
  obtain ⟨x, hx, hd, hw⟩ := h
  apply max_ne_zero_of_witness _ n x hx hd
  calc
    _ = (blockDigits (1 + n*(n-1)/2) n : Multiset ℕ) := Quot.sound hw
    _ = _ := by
      rw [block_to_interval]
      have step : n * (n+1) = n*(n-1) + 2*n := by
        cases n with
        | zero => rfl
        | succ k => simp; ring
      rw [step]
      congr 1
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Icc]; omega

end DecimalPermutations

namespace DecimalPermutations

private theorem number_of_word {n s : ℕ} (h : ∃ w : List ℕ,
    w.Perm (blockDigits s n) ∧ (∀ hw : w ≠ [], w.getLast hw ≠ 0) ∧
      w ≠ [] ∧ n ∣ Nat.ofDigits 10 w) :
    ∃ x : ℕ, 0 < x ∧ n ∣ x ∧ (Nat.digits 10 x).Perm (blockDigits s n) := by
  obtain ⟨w, hw, hlast, hn, hd⟩ := h
  have hsmall (d : ℕ) (hmem : d ∈ w) := block_digit_lt s n d (hw.mem_iff.mp hmem)
  have hh := Nat.digits_ofDigits 10 (by decide) w hsmall hlast
  refine ⟨Nat.ofDigits 10 w, ?_, hd, by rw [hh]; exact hw⟩
  by_contra! hz
  have he : Nat.ofDigits 10 w = 0 := by omega
  exact hn (by simpa [he] using hh.symm)

/-- The OEIS block and the project's separately indexed block both have
positive divisible rearrangements. -/
theorem both_endpoints (small : ∀ n : ℕ, 0 < n → n < 1000 →
    (∃ w : List ℕ, w.Perm (blockDigits (n+1) n) ∧ (∀ h : w ≠ [], w.getLast h ≠ 0) ∧ w ≠ [] ∧ n ∣ Nat.ofDigits 10 w) ∧
    (∃ w : List ℕ, w.Perm (blockDigits (1+n*(n-1)/2) n) ∧ (∀ h : w ≠ [], w.getLast h ≠ 0) ∧ w ≠ [] ∧ n ∣ Nat.ofDigits 10 w))
    (large : ∀ s n : ℕ, 1000 ≤ n → 100 ≤ s →
      ∃ x : ℕ, 0 < x ∧ n ∣ x ∧ (Nat.digits 10 x).Perm (blockDigits s n))
    (n : ℕ) (hn : 0 < n) :
    OMA.S_oeis_a076072.a n ≠ 0 ∧
    sSup {m : ℕ | 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m : Multiset ℕ) =
      (Finset.Icc (1 + n*(n-1)/2) (n*(n+1)/2)).sum (fun k => (Nat.digits 10 k : Multiset ℕ))} ≠ 0 := by
  constructor
  · apply pinned_of_interval
    by_cases h : n < 1000
    · exact number_of_word ((small n hn h).1)
    · exact large _ n (by omega) (by omega)
  · apply original_of_interval
    by_cases h : n < 1000
    · exact number_of_word ((small n hn h).2)
    · have hh : 1000 ≤ n*(n-1) := by
        have := Nat.mul_le_mul (show 1000 ≤ n by omega) (show 1 ≤ n-1 by omega)
        omega
      exact large _ n (by omega) (by omega)

end DecimalPermutations

namespace DecimalFinite

/-- Least significant digit first. `len` fixes the number of places even when
a reordered low block ends in a zero. -/
def places : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k+1, v => v % 10 :: places k (v/10)

private theorem places_ofDigits (l : List ℕ) (hl : ∀ d ∈ l, d < 10) :
    places l.length (Nat.ofDigits 10 l) = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    have hd := hl d (by simp)
    simp only [List.length_cons, Nat.ofDigits, places]
    simp only [Nat.cast_id] at *
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd, Nat.add_mul_div_left _ _ (by decide),
      Nat.div_eq_of_lt hd, Nat.zero_add, ih (fun i hi => hl i (by simp [hi]))]

def width (s : ℕ) : ℕ :=
  if s < 10 then 1 else if s < 100 then 2 else if s < 1000 then 3 else
    if s < 10000 then 4 else if s < 100000 then 5 else if s < 1000000 then 6 else Nat.log 10 s + 1

private theorem width_eq (s : ℕ) (hs : 0 < s) : width s = (Nat.digits 10 s).length := by
  rw [Nat.length_digits 10 s (by decide) hs.ne']
  unfold width
  split_ifs with h1 h2 h3 h4 h5 h6
  · rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 0) (by norm_num; omega) (by norm_num; omega)]
  · rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 1) (by norm_num; omega) (by norm_num; omega)]
  · rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 2) (by norm_num; omega) (by norm_num; omega)]
  · rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 3) (by norm_num; omega) (by norm_num; omega)]
  · rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 4) (by norm_num; omega) (by norm_num; omega)]
  · rw [Nat.log_eq_of_pow_le_of_lt_pow (m := 5) (by norm_num; omega) (by norm_num; omega)]
  · rfl

def block (s : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => places (width s) s ++ block (s+1) k
termination_by structural k => k

private theorem block_succ (s k : ℕ) : block s (k+1) = places (width s) s ++ block (s+1) k := by
  rw [block]

private theorem block_zero (s : ℕ) : block s 0 = [] := by rw [block]

private theorem block_spec (s k : ℕ) (hs : 0 < s) :
    block s k = (List.range k).flatMap (fun i => Nat.digits 10 (s+i)) := by
  induction k generalizing s with
  | zero => simp [block_zero]
  | succ k ih =>
    rw [block_succ, width_eq _ hs]
    have hd := places_ofDigits (Nat.digits 10 s) (fun _ ha => Nat.digits_lt_base (by decide) ha)
    rw [Nat.ofDigits_digits] at hd
    rw [ih (s+1) (by omega), hd, List.range_succ_eq_map]
    simp only [List.flatMap_cons, Nat.add_zero, List.flatMap_map,
      Nat.succ_eq_add_one]
    congr 2
    funext i
    congr 1
    omega

private theorem block_split (s k j : ℕ) :
    block s (k+j) = block s k ++ block (s+k) j := by
  induction k generalizing s with
  | zero => simp [block_zero]
  | succ k ih =>
    rw [Nat.succ_add, block_succ, block_succ, ih]
    simp [List.append_assoc, Nat.add_assoc, Nat.add_comm 1]

def tailRem (n s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => (s + 10 ^ width s * tailRem n (s+1) k) % n
termination_by structural k => k

private theorem tailRem_spec (n s k : ℕ) (hs : 0 < s) :
    tailRem n s k = Nat.ofDigits 10 (block s k) % n := by
  induction k generalizing s with
  | zero => simp [tailRem, block_zero]
  | succ k ih =>
    rw [tailRem, ih _ (by omega), block_succ, Nat.ofDigits_append]
    have hd := places_ofDigits (Nat.digits 10 s) (fun _ ha => Nat.digits_lt_base (by decide) ha)
    rw [Nat.ofDigits_digits] at hd
    rw [width_eq _ hs, hd, Nat.ofDigits_digits]
    exact Nat.ModEq.add_left _ (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _))

/-- Concatenating consecutive equally wide decimal numbers gives a weighted
arithmetic progression. Clearing the square of the common ratio minus one
produces a closed form whose exponentiation is evaluated by the kernel. -/
private def arithmeticBlock (b s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => arithmeticBlock b s k + (s+k)*b^k

private theorem arithmetic_identity (b s k : ℕ) (hb : 1 ≤ b) :
    (b-1)^2 * arithmeticBlock b s k + (s*(b-1) + b^(k+1)) =
    (s+k)*(b-1)*b^k + b := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  change a^2 * arithmeticBlock (a+1) s k + (s*a+(a+1)^(k+1)) = (s+k)*a*(a+1)^k + (a+1)
  induction k with
  | zero => simp [arithmeticBlock]
  | succ k ih =>
    rw [arithmeticBlock, pow_succ _ (k+1), pow_succ _ k]
    rw [pow_succ _ k] at ih
    linear_combination ih

private def closedBlock (b s k : ℕ) : ℕ :=
  ((s+k)*(b-1)*b^k+b - (s*(b-1)+b^(k+1))) / ((b-1)^2)

private theorem closedBlock_eq (b s k : ℕ) (hb : 1 < b) :
    closedBlock b s k = arithmeticBlock b s k := by
  unfold closedBlock
  rw [← arithmetic_identity b s k (by omega), Nat.add_sub_cancel,
    Nat.mul_div_cancel_left _ (pow_pos (by omega) _)]

private theorem width_mono {s t : ℕ} (hs : 0 < s) (hst : s ≤ t) : width s ≤ width t := by
  rw [width_eq _ hs, width_eq _ (by omega), Nat.length_digits 10 s (by decide) (by omega),
    Nat.length_digits 10 t (by decide) (by omega)]
  exact Nat.add_le_add_right (Nat.log_monotone hst) 1

private theorem width_pos {s : ℕ} (hs : 0 < s) : 0 < width s := by
  rw [width_eq _ hs, Nat.length_digits 10 s (by decide) hs.ne']; omega

private theorem uniform (s k w : ℕ) (hs : 0 < s) (h : ∀ i < k, width (s+i) = w) :
    (block s k).length = k*w ∧
    Nat.ofDigits 10 (block s k) = arithmeticBlock (10^w) s k := by
  induction k with
  | zero => simp [block_zero, arithmeticBlock]
  | succ k ih =>
    obtain ⟨hlen,hval⟩ := ih (fun i hi => h i (by omega))
    rw [block_split s k 1, block_spec _ 1 (by omega)]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons,
      Nat.add_zero, List.flatMap_nil, List.append_nil, List.length_append, Nat.ofDigits_append,
      Nat.ofDigits_digits, hval, hlen, ← width_eq (s+k) (by omega), h k (by omega), arithmeticBlock]
    constructor
    · ring
    · rw [← pow_mul, Nat.mul_comm k w]; ring

private def segment (n s k : ℕ) : ℕ :=
  if width s = width (s+k-1) then closedBlock (10^width s) s k % n else tailRem n s k

private theorem segment_spec (n s k : ℕ) (hs : 0 < s) :
    segment n s k = Nat.ofDigits 10 (block s k) % n := by
  unfold segment
  split
  · rename_i he
    have h := uniform s k (width s) hs (fun i hi => by
      have l := width_mono hs (by omega : s ≤ s+i)
      have r := width_mono (by omega : 0 < s+i) (by omega : s+i ≤ s+k-1)
      omega)
    rw [h.2, closedBlock_eq]
    exact Nat.one_lt_pow (width_pos hs).ne' (by decide)
  · exact tailRem_spec _ _ _ hs

private def fastRem (n s k : ℕ) : ℕ :=
  let j := min k (10^width s-s)
  if width s = width (s+j-1) then
    (segment n s j + 10^(j*width s) * segment n (s+j) (k-j)) % n
  else tailRem n s k

private theorem fastRem_spec (n s k : ℕ) (hs : 0 < s) :
    fastRem n s k = Nat.ofDigits 10 (block s k) % n := by
  let j := min k (10^width s-s)
  have hj : j ≤ k := min_le_left _ _
  change (if width s = width (s+j-1) then _ else _) = _
  split
  · rename_i he
    have h := uniform s j (width s) hs (fun i hi => by
      have l := width_mono hs (by omega : s ≤ s+i)
      have r := width_mono (by omega : 0 < s+i) (by omega : s+i ≤ s+j-1)
      omega)
    have heq : block s k = block s j ++ block (s+j) (k-j) := by
      simpa only [Nat.add_sub_of_le hj] using block_split s j (k-j)
    rw [heq, Nat.ofDigits_append, h.1, segment_spec _ _ _ hs, segment_spec _ _ _ (by omega)]
    exact (Nat.mod_modEq _ n).add ((Nat.mod_modEq _ n).mul_left _)
  · exact tailRem_spec _ _ _ hs

/-- Only the low block is permuted. The rest is checked through its residue. -/
def valid (n s k v : ℕ) : Bool :=
  let a := block s k
  let b := places a.length v
  decide (k ≤ n) && b.isPerm a &&
    (decide (k < n) || decide (b.getLast?.getD 0 ≠ 0)) &&
    decide ((Nat.ofDigits 10 b + 10^b.length * fastRem n (s+k) (n-k)) % n = 0)

private theorem last_block (p : List ℕ) (s k : ℕ) (hs : 0 < s) :
    (p ++ block s (k+1)).getLast?.getD 0 ≠ 0 := by
  rw [block_split s k 1, ← List.append_assoc, block_spec _ 1 (by omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons,
    Nat.add_zero, List.flatMap_nil, List.append_nil]
  rw [List.getLast?_append, List.getLast?_eq_some_getLast (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega))]
  exact Nat.getLast_digit_ne_zero _ (by omega)

def ValidWord (n s : ℕ) := ∃ w : List ℕ,
  w.Perm ((List.range n).flatMap (fun i => Nat.digits 10 (s+i))) ∧
  (∀ hw : w ≠ [], w.getLast hw ≠ 0) ∧ w ≠ [] ∧ n ∣ Nat.ofDigits 10 w

theorem valid_sound {n s k v : ℕ} (hs : 0 < s) (h : valid n s k v) : ValidWord n s := by
  let a := block s k
  let b := places a.length v
  let t := block (s+k) (n-k)
  change ((_ && b.isPerm a && (_ || _) && _) = true) at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.isPerm_iff] at h
  obtain ⟨⟨⟨hk, hp⟩, hb⟩, hr⟩ := h
  have hlast : (b ++ t).getLast?.getD 0 ≠ 0 := by
    rcases eq_or_lt_of_le hk with rfl | hlt
    · simpa [t,block_zero] using hb.resolve_left (by omega)
    · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n-k ≠ 0)
      exact (show t = block (s+k) (j+1) by simp [t,hj]) ▸ last_block b (s+k) j (by omega)
  have hn : b ++ t ≠ [] := by intro h0; simp [h0] at hlast
  refine ⟨b ++ t, ?_, ?_, hn, ?_⟩
  · rw [← block_spec s n hs, show n = k+(n-k) by omega, block_split]
    simpa [t, Nat.add_sub_cancel_left] using hp.append_right t
  · intro hw
    rwa [List.getLast?_eq_some_getLast hw] at hlast
  · apply Nat.dvd_of_mod_eq_zero
    rw [Nat.ofDigits_append]
    change (Nat.ofDigits 10 b + 10^b.length * fastRem n (s+k) (n-k)) % n = 0 at hr
    rw [fastRem_spec _ _ _ (by omega)] at hr
    calc
      _ = (Nat.ofDigits 10 b + 10^b.length * (Nat.ofDigits 10 t % n)) % n :=
        (Nat.ModEq.add_left _ (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _))).symm
      _ = 0 := hr

end DecimalFinite
namespace DecimalFinite

private abbrev Entry := ℕ × ℕ × ℕ × ℕ

private def checkRows (n : ℕ) : List Entry → Bool
  | [] => true
  | (k, v, j, z) :: rest => valid n (n+1) k v && valid n (1+n*(n-1)/2) j z && checkRows (n+1) rest
termination_by structural rest => rest

private def Both (n : ℕ) : Prop := ValidWord n (n+1) ∧ ValidWord n (1+n*(n-1)/2)

private theorem checkRows_sound (n : ℕ) (l : List Entry) (h : checkRows n l) :
    ∀ i < l.length, Both (n+i) := by
  induction l generalizing n with
  | nil => simp
  | cons item rest ih =>
    obtain ⟨k,v,j,z⟩ := item
    simp only [checkRows, Bool.and_eq_true] at h
    intro i hi
    cases i with
    | zero =>
      simpa [Both] using And.intro (valid_sound (by omega) h.1.1) (valid_sound (by omega) h.1.2)
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (n+1) h.2 i (by simpa using hi)

private def rows_1 : List Entry := [
  (1, 2, 1, 1),
  (2, 34, 1, 2),
  (1, 4, 1, 4),
  (2, 56, 4, 19708),
  (5, 891760, 5, 1121311145),
  (2, 78, 1, 16),
  (3, 198, 2, 2232),
  (4, 1119120, 2, 3920),
  (1, 10, 1, 37),
  (10, 11215111184619137210, 5, 5446984740),
  (1, 12, 1, 56),
  (4, 54311116, 1, 76),
  (2, 1415, 1, 97),
  (2, 1156, 2, 3992),
  (5, 9716211810, 1, 160),
  (4, 97108112, 1, 112),
  (2, 1198, 2, 131783),
  (2, 2190, 1, 154),
  (2, 2201, 1, 217),
  (10, 26221522273982222340, 10, 201111921179999951899193119460),
  (1, 22, 2, 211122),
  (2, 2324, 1, 232),
  (3, 426225, 2, 254525),
  (2, 2256, 2, 727872),
  (10, 32338032329143372625, 2, 233100),
  (2, 8272, 1, 326),
  (1, 28, 1, 352),
  (3, 93132, 3, 313978380),
  (2, 3031, 2, 708044),
  (10, 35933638347343332130, 5, 487333444436490),
  (4, 53334332, 2, 676446),
  (4, 35334336, 2, 899744)]

private theorem rows_1_ok : checkRows 1 rows_1 := by decide +kernel

private def rows_33 : List Entry := [
  (1, 34, 1, 259),
  (3, 753336, 2, 356256),
  (5, 6379334380, 2, 796595),
  (4, 43937308, 1, 316),
  (3, 340893, 1, 667),
  (2, 934, 2, 7754),
  (1, 40, 2, 774324),
  (10, 94473444246514845440, 10, 678788878487979577777378281880),
  (3, 434244, 2, 182822),
  (3, 544344, 1, 862),
  (3, 444645, 2, 90594),
  (5, 4494674584, 2, 994784),
  (5, 4986574440, 5, 999999991949235),
  (3, 447948, 1, 316),
  (3, 594408, 1, 2018),
  (2, 5904, 2, 9111312),
  (3, 150525, 2, 78117711),
  (10, 48552165559535657550, 10, 2221128393233421112123271122621123123250),
  (3, 325455, 1, 2167),
  (4, 55435556, 1, 7132),
  (4, 54565557, 2, 13017983),
  (3, 755556, 1, 1432),
  (2, 7565, 5, 19811484447868149810),
  (5, 5608591576, 2, 14554112),
  (2, 8955, 1, 1579),
  (2, 6590, 1, 4516),
  (3, 266610, 2, 17321711),
  (10, 64666626791666537680, 10, 4111771777717897761777157871777377711120),
  (3, 663624, 2, 11831382),
  (4, 53666646, 2, 89319182),
  (2, 4665, 1, 1954),
  (3, 766656, 2, 80211072)]

private theorem rows_33_ok : checkRows 33 rows_33 := by decide +kernel

private def rows_65 : List Entry := [
  (5, 6986766670, 2, 18822020),
  (2, 8676, 1, 2146),
  (3, 967608, 2, 22212231),
  (3, 907716, 2, 92722820),
  (3, 217770, 2, 83472243),
  (10, 87377977548761277770, 5, 97211428241642421240),
  (3, 772347, 2, 22447688),
  (4, 73777456, 1, 5752),
  (2, 5477, 2, 66932202),
  (7, 89787675707718, 2, 70723220),
  (10, 48288860879871787375, 10, 7877277722677727277830872828972148822275),
  (4, 77798780, 2, 88152252),
  (4, 1798878, 2, 82292279),
  (3, 879180, 1, 3004),
  (3, 288180, 3, 830883003423),
  (10, 96881828587438988880, 10, 6366313117631132136341618651367369311360),
  (1, 28, 1, 3241),
  (3, 843858, 3, 232332433332),
  (3, 486588, 2, 345344),
  (3, 785688, 2, 34873848),
  (5, 8969788880, 2, 33277515),
  (3, 988788, 2, 67653356),
  (4, 98190889, 1, 3724),
  (4, 80199992, 1, 3928),
  (4, 39991902, 2, 93181397),
  (10, 939951894996997929100, 1, 4060),
  (4, 29993945, 2, 97446090),
  (4, 99935964, 2, 88711844),
  (3, 994695, 2, 4749228),
  (4, 99756998, 1, 3472),
  (5, 99199768090, 8, 64444444444772447674474666391480),
  (5, 11199979008, 2, 41254656)]

private theorem rows_65_ok : checkRows 65 rows_65 := by decide +kernel

private def rows_97 : List Entry := [
  (3, 9090981, 2, 46674855),
  (3, 19109100, 2, 57455474),
  (3, 10111020, 1, 4852),
  (2, 111200, 20, 79549694514594364466569449495549449499696992465596468794441956999459463429458700),
  (3, 100431201, 1, 5051),
  (1, 310, 2, 55351512),
  (2, 110450, 3, 555245552526),
  (3, 517101600, 4, 5395785535533056),
  (2, 176010, 2, 41246655),
  (2, 101708, 2, 55665756),
  (2, 901018, 2, 55673726),
  (2, 119100, 2, 57577980),
  (4, 12111111311, 3, 789585588888),
  (10, 111111111113181279116521411110, 5, 59906896559999599070),
  (1, 112, 1, 6106),
  (4, 151411111136, 1, 2176),
  (3, 115114116, 2, 32630369),
  (2, 111156, 1, 4246),
  (5, 111628191111710, 1, 6565),
  (5, 121017191811112, 1, 6176),
  (2, 191118, 1, 6787),
  (3, 211011192, 2, 66590094),
  (2, 21121, 2, 32702270),
  (10, 314871122112192121212251232160, 10, 9774475757441774641311111721717474411480),
  (3, 122213241, 1, 7261),
  (2, 312142, 2, 73378382),
  (1, 421, 2, 47505075),
  (3, 227151216, 2, 77862276),
  (11, 167412331822319331031113632111125, 2, 75777125),
  (2, 781122, 1, 7876),
  (2, 292181, 2, 8020803),
  (2, 930112, 2, 31198208)]

private theorem rows_97_ok : checkRows 97 rows_97 := by decide +kernel

private def rows_129 : List Entry := [
  (3, 312301311, 2, 85882257),
  (10, 333112133411391113133861175430, 5, 36837938888988388380),
  (3, 231343131, 2, 88157651),
  (4, 313331115436, 2, 64678848),
  (2, 153134, 2, 80879778),
  (2, 315316, 2, 32919188),
  (5, 311639833114710, 1, 9640),
  (7, 413111190334112138744, 3, 989111198328),
  (2, 183139, 1, 7193),
  (2, 311904, 2, 55594944),
  (3, 411024114, 2, 99253599),
  (10, 849641111514421114371414145440, 10, 7797373733399731999596933478797739327940),
  (2, 124134, 2, 91882797),
  (2, 113444, 1, 112),
  (2, 514441, 2, 5011014551),
  (2, 514416, 1, 19072),
  (5, 194414417018165, 2, 1104421440),
  (2, 181474, 1, 18650),
  (2, 148941, 1, 13720),
  (2, 195104, 2, 1900180788),
  (2, 150151, 2, 7028101112),
  (10, 911155555452161653518151171150, 10, 71191871411171187811111161231718111118111811111850),
  (2, 251315, 2, 1323121167),
  (6, 855151541155151736, 2, 7771114184),
  (2, 514515, 1, 11269),
  (5, 157155511519856, 1, 12178),
  (2, 511765, 5, 1933917119113943811699110),
  (4, 617595111508, 1, 1912),
  (2, 118955, 2, 2741428212),
  (2, 165910, 1, 2414),
  (2, 106611, 2, 5262213156),
  (10, 616182676936116115461671116160, 10, 21122722772911772722281264232211227213717727211520)]

private theorem rows_129_ok : checkRows 129 rows_129 := by decide +kernel

private def rows_161 : List Entry := [
  (3, 134661126, 2, 2888211821),
  (3, 165631614, 2, 11334342),
  (3, 561416661, 2, 1010423253),
  (3, 516616716, 2, 3813763136),
  (5, 916766116781160, 2, 3132513135),
  (3, 191716668, 2, 9313166976),
  (3, 709186161, 2, 3318268613),
  (3, 119011776, 2, 4490311200),
  (3, 121717071, 2, 4798419111),
  (10, 728118775717117716713791711410, 5, 3144133341847361461796660),
  (3, 173121747, 2, 4467153153),
  (4, 457717711136, 2, 1407701784),
  (3, 611774571, 2, 9141708848),
  (3, 177175716, 2, 2013555150),
  (14, 891197714811681871118188101711688818782375, 2, 2761215225),
  (8, 911371418770871181888112, 2, 5110012544),
  (3, 718081719, 2, 5785517715),
  (3, 101817198, 2, 5155755714),
  (3, 88211118, 2, 3125335199),
  (10, 562188189811838118818171119840, 10, 66411111116811111161111169111156711626111161321660),
  (3, 284811813, 2, 2911621692),
  (3, 113845188, 2, 6747316214),
  (3, 118548861, 2, 6465165516),
  (3, 751811688, 2, 3176881368),
  (5, 918781188891160, 2, 2217127010),
  (3, 898718118, 2, 1712207706),
  (3, 898910118, 2, 1739321379),
  (4, 911191909812, 3, 177517718155908),
  (3, 291910911, 2, 7771867176),
  (10, 123991974119298999116190915110, 5, 7971571619659799851519770),
  (3, 191919324, 2, 1184147681),
  (4, 911914951936, 3, 331189373133888)]

private theorem rows_161_ok : checkRows 161 rows_161 := by decide +kernel

private def rows_193 : List Entry := [
  (3, 919649115, 2, 8205911853),
  (7, 599110198116297919020, 2, 1723728812),
  (5, 979919082119610, 5, 9989181271811118611898990),
  (4, 799101189920, 4, 91143191911111191112),
  (3, 9121989, 2, 7900819313),
  (3, 990001212, 2, 1059459510),
  (3, 200221200, 2, 9217973001),
  (3, 123022200, 2, 9191991200),
  (3, 23220420, 2, 210210201),
  (3, 203400252, 3, 34203230223000),
  (3, 642025200, 2, 2040555200),
  (3, 200605272, 2, 2077280700),
  (3, 222607800, 2, 1211990220),
  (3, 922807020, 2, 1111112726),
  (3, 9228201, 2, 3311322222),
  (3, 120102192, 2, 5232951120),
  (5, 121423221121210, 2, 8317737212),
  (10, 122316222481211975211211222120, 5, 2446199494119292128197520),
  (3, 212432112, 2, 5122652712),
  (3, 152234112, 2, 2286376232),
  (3, 114222615, 2, 2208279255),
  (3, 527221116, 2, 2392972722),
  (5, 611182227292120, 2, 620372030),
  (3, 872112912, 2, 3222122232),
  (4, 122801221922, 2, 3323724438),
  (3, 222109212, 2, 5643256352),
  (4, 222322022122, 2, 8332827273),
  (10, 122224222923222286222225227320, 2, 2924920140),
  (4, 222322222425, 2, 3311422124),
  (3, 225223224, 2, 2323434552),
  (3, 242225226, 2, 2474555427),
  (3, 526222272, 2, 7742499872)]

private theorem rows_193_ok : checkRows 193 rows_193 := by decide +kernel

private def rows_225 : List Entry := [
  (10, 184222263333220227229223323225, 2, 1522220250),
  (3, 922272282, 2, 2725422546),
  (3, 202228329, 2, 5525265263),
  (3, 923322120, 2, 8085572892),
  (3, 23213232, 2, 6170262810),
  (10, 924237433322332283323321252260, 5, 9233336836226763362246330),
  (4, 323242523332, 2, 6562625667),
  (4, 262253333432, 2, 2967976872),
  (3, 254233632, 2, 7370202902),
  (3, 322653372, 2, 2626272372),
  (5, 262322238379340, 5, 7290269978720994774242745),
  (3, 338237292, 2, 2772177332),
  (3, 934022283, 2, 6272779986),
  (3, 422143290, 2, 8820225240),
  (4, 42223214424, 2, 2483282444),
  (10, 222225242349144524428674442240, 10, 88816688862222866862262268684786888928988538262880),
  (4, 242243224544, 2, 9128228292),
  (3, 224543442, 2, 6391622192),
  (3, 465442422, 2, 440925942),
  (3, 424652472, 2, 2986427964),
  (5, 548246472222490, 5, 9984829219299229299888935),
  (3, 228794424, 2, 3163701330),
  (3, 92854224, 2, 8383332300),
  (3, 192402552, 2, 2330609360),
  (3, 252210255, 2, 7080873387),
  (10, 522245522692526573825525512250, 10, 11483111113913121313332113231161331311712333331250),
  (3, 253242525, 2, 7331713637),
  (3, 553242552, 2, 2376321168),
  (3, 252545256, 2, 1180739883),
  (3, 256575252, 2, 3332132312),
  (3, 856522725, 5, 8333828332382993832372630),
  (4, 892565227520, 2, 2413266432)]

private theorem rows_225_ok : checkRows 225 rows_225 := by decide +kernel

private def rows_257 : List Entry := [
  (3, 582590262, 2, 8922973838),
  (3, 210229656, 2, 1353353514),
  (3, 62226162, 2, 3431334213),
  (10, 212292266622623626266764526780, 10, 67738367633633367263537373336439363333633787771660),
  (3, 264662232, 2, 3139333239),
  (3, 226423566, 2, 3934211934),
  (3, 465662262, 2, 4444355435),
  (3, 666722256, 2, 4733117784),
  (5, 226667297286260, 5, 3443498489398433892418395),
  (3, 967822662, 2, 2323755464),
  (3, 827220669, 2, 2353551531),
  (3, 961720272, 3, 731759783735580),
  (3, 172722702, 2, 4800436367),
  (10, 722259746222217227787727873270, 5, 3173336136663632183136930),
  (3, 772742322, 2, 3875668563),
  (3, 742772352, 2, 3857683856),
  (3, 625277427, 2, 3133971207),
  (3, 772722576, 2, 3243770304),
  (10, 612223248272787229880227828875, 10, 66873487333773677378277963667760833386176388677675),
  (3, 722877792, 2, 7593715932),
  (3, 272788029, 2, 2832828732),
  (3, 982071822, 2, 5533854800),
  (3, 822208182, 2, 8833378782),
  (10, 249822528286888272912222883880, 2, 9363601920),
  (3, 828324282, 2, 3439319342),
  (3, 482838522, 2, 3923922366),
  (3, 882426582, 2, 930493599),
  (3, 865272288, 2, 881748104),
  (5, 982297286882280, 2, 4041772440),
  (3, 828982728, 2, 7544567700),
  (3, 988820292, 2, 44341421),
  (3, 929028192, 2, 4314309312)]

private theorem rows_257_ok : checkRows 257 rows_257 := by decide +kernel

private def rows_289 : List Entry := [
  (3, 102929229, 2, 6176181144),
  (10, 272229392921982699590293294920, 2, 9071149460),
  (3, 924229239, 2, 1176299424),
  (3, 939252924, 2, 7488444228),
  (3, 429299526, 2, 4028779274),
  (3, 796925922, 2, 3033470472),
  (5, 923789296922090, 5, 3446333693383433446736670),
  (3, 279289992, 2, 3443626616),
  (3, 29290389, 2, 5744989353),
  (3, 192390030, 2, 2455425444),
  (3, 13300230, 2, 5452544354),
  (3, 332330100, 20, 4428844864844586384486268454446889844645885648684581464745545185844764454784964444448544484443448600),
  (3, 43033023, 2, 4514511525),
  (3, 3334530, 2, 4435455452),
  (3, 306504330, 2, 5555445477),
  (3, 37003536, 2, 6057465840),
  (3, 300368730, 5, 6644243666663664334633145),
  (3, 37830930, 2, 7666466466),
  (3, 83310930, 2, 9794626347),
  (4, 111933001332, 2, 7277920484),
  (3, 313113210, 2, 4878558774),
  (10, 231361333113491111333852711330, 5, 8497874494687489778799090),
  (3, 343111323, 2, 2480426780),
  (4, 313451133136, 2, 4875115488),
  (4, 113711453363, 2, 4403982888),
  (3, 371331516, 2, 1392941444),
  (5, 393386712311130, 2, 5644997445),
  (4, 972131133380, 3, 923797477179744),
  (3, 131283309, 3, 5508800097885),
  (3, 322913310, 2, 450540504),
  (3, 222323130, 2, 5705222307),
  (10, 235323223232274333239321633280, 2, 4151045120)]

private theorem rows_289_ok : checkRows 289 rows_289 := by decide +kernel

private def rows_321 : List Entry := [
  (3, 323422323, 2, 3156532161),
  (3, 223323354, 2, 6583125816),
  (3, 352243263, 2, 2002040555),
  (3, 262337352, 2, 5252723328),
  (10, 237233138033339336332233334325, 2, 6525125625),
  (3, 227333298, 2, 5257979726),
  (3, 902338332, 2, 3055230333),
  (4, 303313323392, 2, 5233639056),
  (3, 333231330, 2, 5553997538),
  (10, 343363333133333338343739325330, 5, 8255857844994442582282650),
  (4, 333353323433, 3, 514557668661441),
  (5, 373433333333356, 2, 5974598444),
  (3, 334336335, 2, 5058275529),
  (4, 333573383336, 3, 263161455555516),
  (5, 943373338363330, 2, 4597565495),
  (5, 173033398333344, 2, 5218682256),
  (3, 438339303, 2, 7861566651),
  (3, 433331940, 2, 4659559556),
  (3, 44143233, 2, 5272295397),
  (10, 363439345344344334132473843540, 10, 67363653545363761734775559733756736585767575366620),
  (6, 633443454332444373, 2, 7927751957),
  (3, 433433454, 2, 5823353118),
  (3, 635344344, 2, 8565586455),
  (3, 653347344, 3, 975559999998888),
  (5, 794338336043445, 2, 4345992315),
  (3, 933483744, 2, 6768998556),
  (3, 938450343, 2, 6023030063),
  (3, 391553340, 2, 6700039368),
  (3, 133535250, 4, 706602273976877206),
  (10, 359523133533663554335375385550, 2, 1671766700),
  (3, 333325455, 2, 7622646411),
  (4, 335353545536, 2, 1671787776)]

private theorem rows_321_ok : checkRows 321 rows_321 := by decide +kernel

private def rows_353 : List Entry := [
  (3, 356455353, 2, 6196212320),
  (3, 553337556, 2, 2882366424),
  (3, 853536375, 5, 9832867286848226623633680),
  (4, 558333957360, 2, 9193663112),
  (3, 335908536, 2, 5836753464),
  (3, 303961356, 2, 6390493506),
  (3, 163026633, 2, 6642236624),
  (10, 314373523633663676636866339360, 10, 66222646622263616468964226643664227645664444666640),
  (3, 363236346, 2, 9488266149),
  (3, 634353636, 2, 4336455632),
  (3, 366546363, 2, 6057405765),
  (3, 373663656, 2, 666786660),
  (6, 366833363796773160, 9, 466664343436324686464346639664363663646766135),
  (3, 673369368, 2, 7967666976),
  (3, 893366370, 2, 7266613716),
  (3, 373913760, 2, 6739675520),
  (3, 770332137, 2, 8698896777),
  (10, 337973773538337737763371837420, 5, 6668268666268782882626790),
  (3, 473233773, 2, 3668676863),
  (4, 334377537376, 2, 7096006908),
  (3, 357467373, 2, 3979639680),
  (5, 377337978357376, 2, 3779559662),
  (10, 837874381338367838337933082375, 3, 782767172121000),
  (6, 372387973033137888, 2, 5727510000),
  (3, 337889703, 2, 7807778807),
  (3, 398783310, 2, 5457215712),
  (3, 882330318, 2, 7121763363),
  (10, 988253933883388738383333184680, 2, 2717121020),
  (3, 383883324, 2, 7322127399),
  (3, 833353848, 3, 772722727773774),
  (3, 354863838, 2, 3574571513),
  (3, 388853376, 4, 35373737370373955584)]

private theorem rows_353_ok : checkRows 353 rows_353 := by decide +kernel

private def rows_385 : List Entry := [
  (5, 983738386893380, 5, 2279277933293329237173495),
  (3, 988338378, 2, 3467470370),
  (3, 838083399, 2, 4734926769),
  (4, 331990939328, 2, 5750789700),
  (3, 333190992, 2, 4577476658),
  (10, 393281339903599463749939399330, 5, 8775558557888675755869570),
  (4, 235934339939, 2, 4266476727),
  (4, 393335993496, 2, 6736767368),
  (3, 943399365, 2, 2037079770),
  (3, 939395376, 2, 4773227724),
  (5, 799433980996330, 5, 7978786778177877718781120),
  (4, 970933439980, 2, 8781221712),
  (3, 89493093, 2, 7706788068),
  (3, 139040094, 2, 5994007700),
  (3, 40404201, 2, 3249779004),
  (3, 320414400, 2, 1989877200),
  (3, 40444230, 2, 8001220802),
  (3, 44054340, 2, 8620080306),
  (3, 46445004, 2, 8140058100),
  (3, 404547600, 2, 474110888),
  (3, 764440800, 5, 8288188181811181811181435),
  (3, 49704048, 2, 8212672182),
  (3, 41009844, 2, 2263822268),
  (3, 414011904, 2, 2833309080),
  (3, 401124411, 2, 4333873884),
  (10, 111451441141641274444429181430, 5, 3483889886844785388483830),
  (3, 444411321, 2, 6425728845),
  (3, 443511144, 2, 4874686668),
  (3, 151644414, 2, 8058795008),
  (3, 164715414, 2, 2935588494),
  (5, 911144864244170, 2, 9698580075),
  (3, 189411744, 2, 2226818336)]

private theorem rows_385_ok : checkRows 385 rows_385 := by decide +kernel

private def rows_417 : List Entry := [
  (3, 182144904, 2, 3766788738),
  (3, 142190424, 2, 7751855418),
  (3, 224142024, 2, 7873785527),
  (10, 265722424242249414444382243420, 10, 89779998779888481995887979309077999989897987926980),
  (3, 244244322, 2, 8841112488),
  (3, 234245244, 2, 8832338888),
  (3, 524642424, 2, 8225998455),
  (3, 567442224, 2, 9887768976),
  (20, 444334933421444244415443844723443603444224746484333493444025, 2, 199112000),
  (3, 849274224, 2, 595906722),
  (3, 444398022, 2, 9059953902),
  (3, 394413204, 3, 978113119393980),
  (3, 241344033, 2, 8891090718),
  (10, 444513337836434343334249444430, 5, 2349223632273922298929290),
  (3, 443433423, 2, 9292666766),
  (3, 353443344, 2, 9933979008),
  (3, 334546344, 2, 9530399253),
  (3, 453337446, 2, 6999693332),
  (5, 983673344434440, 5, 7993369934894434949099940),
  (3, 873343944, 2, 4813984932),
  (3, 403493844, 3, 875962929559662),
  (3, 314404494, 2, 597905574),
  (4, 134444424404, 2, 6423199461),
  (10, 421449448745444445443444444640, 10, 97856346662855915999656855865859869985869699985680),
  (3, 424443444, 2, 7729209120),
  (3, 544444344, 2, 7629469374),
  (3, 444445644, 2, 4799909705),
  (4, 444547684444, 2, 3949388748),
  (5, 464974444448450, 5, 9199782899979898977948375),
  (4, 454474944048, 2, 2769399392),
  (3, 448495404, 2, 3998992668),
  (3, 494541504, 2, 900310101120)]

private theorem rows_417_ok : checkRows 417 rows_417 := by decide +kernel

private def rows_449 : List Entry := [
  (3, 504542145, 2, 158077050071),
  (10, 555474444455545563484491624550, 2, 160211172000),
  (4, 535452544454, 2, 717141004176),
  (3, 344555544, 2, 192110089712),
  (3, 455565444, 2, 19028317032),
  (3, 565745454, 2, 318018302322),
  (3, 457446855, 2, 112287033680),
  (3, 954475584, 2, 14047337112),
  (3, 54498546, 2, 498111041970),
  (3, 644560914, 2, 406455506114),
  (3, 164624460, 2, 110031125115),
  (10, 453649444268647466614647666440, 2, 512151757500),
  (3, 266434464, 2, 20106136031),
  (3, 434665464, 2, 619249306140),
  (3, 446644656, 2, 190596505641),
  (3, 476446656, 2, 171477001184),
  (5, 876644474696460, 2, 782817801810),
  (3, 984644676, 2, 487683101430),
  (3, 944078646, 2, 801032811881),
  (3, 449477160, 2, 119009902872),
  (3, 77741424, 2, 94109178747),
  (10, 347444177745774474748746274980, 2, 211112611070),
  (3, 277734444, 2, 161101087686),
  (3, 445377744, 5, 171115111111111611981111151056),
  (3, 474767454, 2, 906116131121),
  (3, 774546774, 2, 200112311112),
  (10, 480874429847444644387818874475, 2, 117251677125),
  (3, 974778744, 2, 131112551300),
  (3, 498407784, 2, 513182211753),
  (3, 48987414, 2, 401501144010),
  (3, 82488441, 2, 814448411213),
  (10, 884479844888134859824446484480, 10, 891969641616141541691194491946161411471113166794994611141920)]

private theorem rows_449_ok : checkRows 449 rows_449 := by decide +kernel

private def rows_481 : List Entry := [
  (4, 248358444884, 2, 412511411445),
  (3, 584834448, 2, 123215919152),
  (3, 548868444, 2, 614644005111),
  (3, 465478884, 2, 886817116188),
  (5, 944748648849880, 6, 137111731712771377614337171173311775),
  (3, 498874848, 2, 775618517118),
  (3, 480994488, 2, 214131483183),
  (3, 991844904, 2, 181031981288),
  (3, 940492194, 2, 119371118193),
  (10, 498794423959594964904444999140, 2, 711016898910),
  (3, 994239444, 2, 792691022120),
  (3, 994345944, 2, 72781287108),
  (3, 964454949, 2, 872190221121),
  (3, 959974446, 2, 773727111212),
  (5, 944648999040975, 5, 226212222221826721222662179160),
  (3, 499978944, 2, 166722722112),
  (4, 10949590548, 2, 252812753231),
  (3, 519594, 2, 315251743572),
  (3, 200105505, 2, 144252212253),
  (3, 513205500, 20, 472776174614226542517662422247711214517411572211556774276172374857425477671191747485222716956214416221211477641443442500),
  (3, 20055354, 2, 251251521225),
  (3, 354550500, 2, 152157255372),
  (3, 55540506, 2, 212652526514),
  (3, 500575056, 2, 167756127528),
  (3, 765505800, 5, 122671732472227262716111226265),
  (3, 505950078, 2, 677712721766),
  (3, 815509500, 2, 322127218728),
  (4, 551595011012, 2, 897270188712),
  (3, 52511151, 2, 288722181929),
  (10, 125511515928531155551511745610, 5, 172290799218779729996981219910),
  (3, 411155523, 2, 101603703330),
  (4, 113515155456, 2, 111103738880)]

private theorem rows_481_ok : checkRows 481 rows_481 := by decide +kernel

private def rows_513 : List Entry := [
  (3, 154651551, 2, 32333111931),
  (5, 561115911555758, 2, 313218341184),
  (3, 115176855, 2, 762213335135),
  (4, 598110551752, 2, 382372187112),
  (3, 511955820, 2, 831383373318),
  (4, 29121525552, 3, 35619309013339134),
  (3, 225510522, 2, 431422342314),
  (10, 452555232595225287222556315520, 10, 433333411344341992449381199431491343794451491494454614991440),
  (3, 535422522, 2, 142165363451),
  (3, 352524552, 2, 998133253518),
  (3, 255525426, 2, 114603055563),
  (3, 525562572, 2, 780231173720),
  (3, 565272825, 2, 371575131525),
  (3, 272955852, 2, 787387161030),
  (3, 598525230, 2, 838061163302),
  (3, 503593152, 2, 933191131920),
  (3, 535313250, 2, 615653937918),
  (10, 895337354314363555525333355550, 2, 814670141180),
  (3, 355543233, 2, 477071141610),
  (4, 555345335336, 2, 714111842244),
  (3, 543355365, 2, 114871041977),
  (3, 553353576, 2, 221311213344),
  (3, 538653375, 5, 682884221424047244814414988115),
  (4, 305933575584, 3, 311182333483413384),
  (3, 350598543, 2, 371199431814),
  (3, 505345194, 2, 444154554144),
  (3, 452404515, 2, 341444999129),
  (10, 546945445454285455453551457540, 10, 143133445359415264155558511531145557433133554455145451553540),
  (3, 455424435, 2, 246471710610),
  (4, 444544553556, 2, 112641346166),
  (3, 445455465, 2, 544117741515),
  (3, 745556544, 2, 779694147168)]

private theorem rows_513_ok : checkRows 513 rows_513 := by decide +kernel

private def rows_545 : List Entry := [
  (3, 654484755, 8, 214844482422826318844412414172481148448448214125),
  (3, 475945584, 2, 677741818848),
  (3, 585494055, 2, 331442931933),
  (4, 519554555052, 2, 148997041988),
  (3, 551505552, 2, 55744122018),
  (10, 655559555356155572555555554850, 2, 601979157750),
  (3, 555545523, 2, 217516511255),
  (5, 555554535555576, 2, 780501257712),
  (3, 545555565, 2, 129263512605),
  (4, 655755555558, 2, 131318152538),
  (4, 557856555595, 2, 533773131675),
  (4, 555955758560, 2, 221551921944),
  (3, 695585505, 2, 445718484185),
  (3, 965505516, 2, 55044551154),
  (3, 165566520, 2, 916555623519),
  (10, 555766456621655766555658936560, 10, 183115526555251616652615556625573512615512262156515452552960),
  (3, 566546532, 2, 810251770518),
  (3, 556456536, 2, 773621651454),
  (3, 565554666, 2, 884010521552),
  (3, 556667556, 2, 617578185876),
  (3, 687565665, 2, 219131539335),
  (3, 596567856, 2, 969915951788),
  (3, 595086567, 2, 16626403146),
  (3, 155907576, 2, 391260101016),
  (3, 507717552, 2, 619156958171),
  (10, 777557557575555289167475578730, 5, 126816716922671162661111662610),
  (3, 557243775, 2, 617133262767),
  (7, 755775758757955374756, 2, 380331136760),
  (3, 556577754, 2, 963880817136),
  (5, 957555775785776, 2, 245356411464),
  (3, 578657775, 2, 520260661175),
  (4, 779555775808, 2, 162165061056)]

private theorem rows_545_ok : checkRows 545 rows_545 := by decide +kernel

private def rows_577 : List Entry := [
  (3, 558857097, 2, 816766117176),
  (3, 505859178, 2, 614577655616),
  (3, 828801555, 2, 371133362367),
  (10, 978518688588595585855858543520, 10, 661191216777637679977516199691611919117716712179191961411860),
  (3, 238585854, 2, 421881196964),
  (3, 885354558, 2, 397197660120),
  (3, 855845586, 2, 461661965559),
  (3, 555885768, 2, 307723017128),
  (3, 886588755, 2, 128218077120),
  (3, 785885598, 3, 117111770810046744),
  (3, 588955098, 2, 111979299317),
  (3, 551995908, 2, 525810717792),
  (3, 559059129, 2, 131713861677),
  (10, 519299496555596895059957955930, 5, 577571675317767177973781313350),
  (3, 539255499, 2, 316474417734),
  (4, 995553959456, 2, 174793739184),
  (4, 565555999749, 2, 511975207553),
  (3, 557959596, 2, 737121611262),
  (3, 956958795, 7, 717116667711162717771769772172112766877610),
  (4, 989009595756, 2, 171731711732),
  (3, 806509959, 2, 709179708177),
  (3, 590669100, 2, 47851051758),
  (3, 1600266, 2, 321019079171),
  (3, 126360600, 2, 171971797200),
  (3, 234660006, 2, 233101800810),
  (3, 650636004, 2, 818012009930),
  (3, 64660065, 2, 158015541108),
  (3, 600566076, 2, 210110781288),
  (3, 760686060, 5, 177181122213114711172288881275),
  (3, 9686706, 2, 813117833316),
  (3, 980006616, 2, 933182382921),
  (3, 191066016, 2, 451858910432)]

private theorem rows_577_ok : checkRows 577 rows_577 := by decide +kernel

private def rows_609 : List Entry := [
  (3, 111620661, 2, 318515871831),
  (10, 611518661161436761926626161160, 5, 888117744575451691554858177870),
  (3, 116462613, 2, 185733165686),
  (3, 514161636, 2, 961889667816),
  (3, 666561411, 2, 895180178757),
  (3, 665711616, 2, 113981812988),
  (5, 611268619667160, 2, 180888871680),
  (3, 166918176, 2, 128912921448),
  (3, 602891661, 2, 109019830037),
  (3, 109122666, 2, 151400969556),
  (3, 662622120, 2, 272719112931),
  (10, 372662958232646122662662266620, 10, 115948999111911111988999929909891891991181117889118969191380),
  (3, 222362664, 2, 915212195112),
  (3, 465236226, 3, 912131193331331934),
  (3, 266566422, 2, 351971755439),
  (3, 666522672, 2, 173971879344),
  (12, 639626167336637632466336226338666250, 2, 105091091250),
  (3, 287266962, 2, 515122969676),
  (3, 296683620, 2, 293661219525),
  (3, 160329636, 2, 698691710988),
  (3, 236103366, 2, 758171909570),
  (10, 666416663264636335938366333730, 5, 918999111883468739131819381110),
  (3, 336236364, 2, 978711687669),
  (3, 366343536, 5, 119999103399499190999731909184),
  (3, 336346665, 2, 9002223000),
  (3, 736563636, 2, 62606026302),
  (6, 336664398136466670, 2, 261217029290),
  (3, 736836936, 2, 39129110232),
  (3, 689046633, 2, 276052850622),
  (3, 364961604, 2, 502202040332),
  (3, 16664442, 2, 830382342240),
  (10, 666646945464144467346562864640, 2, 204484241280)]

private theorem rows_609_ok : checkRows 609 rows_609 := by decide +kernel

private def rows_641 : List Entry := [
  (3, 434624664, 2, 510250222211),
  (3, 664454346, 2, 702565263702),
  (4, 644644666457, 2, 652020464040),
  (3, 574646664, 2, 704047002872),
  (5, 480464674696665, 2, 709766292210),
  (3, 674694468, 2, 278638203330),
  (3, 56968644, 2, 882900938228),
  (3, 566105496, 2, 229069230096),
  (3, 106625565, 2, 280217212707),
  (10, 646595566657661665556658526350, 2, 922712169200),
  (3, 524666553, 2, 217126551771),
  (3, 553465656, 2, 282222122712),
  (4, 654665556657, 2, 279802288211),
  (3, 675565656, 2, 331332253512),
  (3, 665567685, 7, 424149411128181221482611149111729114298280),
  (3, 665579856, 2, 241484428112),
  (3, 695665806, 2, 155298174429),
  (3, 619650666, 2, 165116254152),
  (3, 666160266, 2, 816112312628),
  (10, 666566666666617696624667638660, 10, 112177736241272142741771744447172482742928714727477175177720),
  (4, 645666266663, 2, 813211321812),
  (3, 664563666, 2, 289321797218),
  (4, 466656666667, 2, 145495145292),
  (4, 666666866576, 2, 128110021272),
  (6, 667667668666176960, 2, 270822172820),
  (3, 669667668, 2, 741124244226),
  (3, 966866067, 2, 221123222211),
  (3, 976766160, 2, 227807722292),
  (3, 701726766, 2, 422724334428),
  (10, 772967767875616667746867667360, 5, 242121241211124291214812624720),
  (3, 276634767, 2, 487222277864),
  (3, 377674656, 2, 525472542528)]

private theorem rows_641_ok : checkRows 641 rows_641 := by decide +kernel

private def rows_673 : List Entry := [
  (3, 767466765, 2, 322021662912),
  (3, 677677566, 2, 600232628822),
  (10, 806718376786886266878666964675, 10, 822487229212224742727477282474782264770422788222748377424275),
  (3, 877766976, 2, 218551282212),
  (3, 807667896, 2, 282882272882),
  (3, 988667160, 2, 420059225952),
  (3, 606821868, 2, 223880310321),
  (10, 768886168966648568268389666880, 2, 106282238360),
  (3, 634826688, 2, 341312245125),
  (3, 686838654, 3, 222223232423222322),
  (3, 666845886, 2, 290920253342),
  (3, 686665788, 2, 273353382588),
  (5, 869678668698860, 10, 242222843747302422322297234234724427322473144378723723722635),
  (3, 887668968, 2, 554243693972),
  (3, 668690889, 2, 454652363223),
  (3, 198696960, 2, 392660333232),
  (3, 69166299, 2, 737217021830),
  (10, 697419997596696669966260939860, 2, 773206777320),
  (3, 629966394, 2, 873322899363),
  (3, 939665964, 2, 937908822308),
  (3, 954966696, 2, 97832737929),
  (3, 769965966, 2, 472304424702),
  (5, 787969069969660, 6, 412111641482691211411621477662214170),
  (3, 996697968, 2, 282681211464),
  (3, 967900986, 2, 528545724252),
  (3, 900716970, 2, 544235524322),
  (3, 770271000, 2, 253232993445),
  (3, 307127700, 20, 654444622444252486624446419446464667644246525426226646428425224764446342446459466447246656664642362564456212426542645600),
  (3, 724703007, 2, 252215534354),
  (3, 573704700, 2, 226326450054),
  (4, 760500707774, 2, 446472526557),
  (3, 70757760, 2, 745454277824)]

private theorem rows_673_ok : checkRows 673 rows_673 := by decide +kernel

private def rows_705 : List Entry := [
  (3, 707778060, 5, 626141241848126841224613868245),
  (3, 977078070, 2, 742884668682),
  (3, 710987007, 2, 724923525497),
  (3, 117771900, 2, 200522780952),
  (3, 271711701, 2, 508289289507),
  (10, 712151177116177918742777711730, 5, 259219669797529685162125506110),
  (3, 711477123, 2, 642220245570),
  (4, 175417713176, 2, 158321315712),
  (3, 774751611, 2, 532822305839),
  (4, 771617517718, 2, 452325424554),
  (5, 672717178177190, 2, 255275256525),
  (4, 877071779112, 2, 957255952172),
  (3, 790871712, 2, 567266682588),
  (3, 927771210, 2, 704557544220),
  (3, 277217220, 2, 285213518222),
  (10, 777722229378772217422275776320, 10, 885845542482882846588458785135422452482952258548288828854880),
  (3, 277242723, 2, 255592916526),
  (3, 527237724, 2, 802226682230),
  (3, 576272472, 2, 601020250146),
  (3, 262757772, 3, 221921687276727612),
  (10, 677271093734237337737782723725, 2, 262225641425),
  (4, 279370827772, 2, 676677123312),
  (3, 777829230, 2, 926230392063),
  (3, 730713792, 2, 922466023664),
  (3, 331727703, 2, 635872525563),
  (10, 733777633733198733537477374720, 2, 862676806620),
  (3, 433727373, 2, 861668162762),
  (4, 373337477356, 2, 762775564248),
  (3, 574733637, 2, 229626088782),
  (3, 737753736, 2, 121096203926),
  (5, 433873797736770, 5, 67299777499672762248269644965),
  (4, 793777738304, 2, 772148242080)]

private theorem rows_705_ok : checkRows 705 rows_705 := by decide +kernel

private def rows_737 : List Entry := [
  (3, 777934830, 2, 127812711722),
  (3, 371479470, 2, 575972951412),
  (3, 770144742, 2, 726292722369),
  (10, 527777741747544344787744649740, 10, 732344324573333724327373312433438737246444342224337723397720),
  (3, 724447347, 2, 212411747772),
  (4, 576473447474, 2, 422397119742),
  (3, 645774447, 2, 567227555546),
  (3, 745744776, 2, 722939687376),
  (5, 746877954747470, 8, 112724712717217247177847774772447737474216412215),
  (3, 947774874, 2, 777827628788),
  (3, 749787045, 2, 223838276763),
  (4, 594707757152, 2, 790338792972),
  (3, 251707557, 2, 721182880022),
  (10, 656571734577572577977555587750, 3, 778782788888622000),
  (3, 747575352, 2, 621862272618),
  (5, 555753475757776, 2, 238823277872),
  (3, 546575775, 2, 39328181232),
  (4, 755557775678, 2, 338283828288),
  (3, 765877575, 9, 232483468962148446866243884682638824444244867236622440),
  (4, 758705795776, 2, 539282859132),
  (3, 575870967, 3, 818428941216864627),
  (3, 175676790, 2, 869094250682),
  (3, 772601667, 2, 222766886367),
  (10, 774761563677266777767668679760, 10, 388822183848422484226888888429448482228848822254222422882720),
  (3, 677672463, 2, 281281188992),
  (3, 576737466, 2, 932949848922),
  (3, 647766765, 2, 900054277209),
  (4, 778667766576, 2, 178146249692),
  (5, 776667667779870, 5, 232224292223922391923329222235),
  (3, 778976676, 2, 927992969292),
  (4, 601767877779, 2, 326726927933),
  (3, 707179776, 2, 395424052992)]

private theorem rows_737_ok : checkRows 737 rows_737 := by decide +kernel

private def rows_769 : List Entry := [
  (3, 277077771, 2, 259759922298),
  (10, 777987427777777717776777758730, 2, 662960676920),
  (3, 734777772, 2, 876832693269),
  (4, 777773747756, 2, 660289777092),
  (3, 657777774, 2, 883982793029),
  (4, 777777777658, 2, 991325219952),
  (10, 777747387672198777878787887075, 11, 299192233992929939929699999999969929929923894392739209322292399925),
  (6, 717777089777778288, 2, 700313000720),
  (3, 779788770, 2, 143107837470),
  (3, 701778978, 2, 400253225352),
  (3, 871808727, 2, 200333033330),
  (10, 738788818887779879758274778760, 2, 383211330180),
  (3, 477388287, 2, 930350491425),
  (3, 387778854, 2, 735375330032),
  (3, 788658477, 2, 530164351065),
  (3, 578887776, 2, 733303809696),
  (5, 788787897876790, 2, 722713273700),
  (3, 797778888, 2, 805030035876),
  (3, 809797878, 2, 922993330092),
  (3, 917979780, 2, 981317000300),
  (3, 207179979, 2, 638388067110),
  (10, 949799759207977971377997798680, 5, 183176636166511111951163355360),
  (3, 929777943, 2, 137426344142),
  (4, 759399479776, 2, 133333237128),
  (3, 576749799, 2, 30931414023),
  (3, 777979956, 3, 423238312134841284),
  (5, 798767999807970, 2, 311766316155),
  (5, 818779097798900, 2, 361144321116),
  (3, 889090977, 2, 877271030312),
  (3, 901708908, 2, 430010130588),
  (3, 808002018, 2, 130012388883),
  (3, 301288800, 2, 121331969600)]

private theorem rows_769_ok : checkRows 769 rows_769 := by decide +kernel

private def rows_801 : List Entry := [
  (3, 4388082, 2, 124003324002),
  (3, 84850380, 2, 233220310122),
  (3, 858048006, 2, 52420323002),
  (3, 68057880, 2, 282382783200),
  (3, 600888780, 5, 163331633261631212132343263235),
  (3, 908887008, 2, 316414322474),
  (3, 1888980, 2, 222323232525),
  (3, 181198008, 2, 630290223360),
  (3, 812181108, 2, 682387826333),
  (10, 848738168812111588821181189810, 5, 436633732677262962744574832670),
  (3, 412831188, 2, 642338455278),
  (3, 511838184, 2, 232629798236),
  (3, 458611881, 2, 890007303033),
  (3, 818715168, 2, 33808939332),
  (6, 888821181912786180, 2, 17733361730),
  (3, 891117888, 2, 522133232352),
  (3, 888811902, 3, 333833333333973333),
  (3, 18892812, 2, 543133535414),
  (3, 282802182, 2, 939423373437),
  (10, 288828212292828428688388357220, 10, 359772739733333983753753950336535955793533997973915333578340),
  (3, 328828224, 2, 663613631321),
  (3, 423852882, 2, 327337334334),
  (3, 482526828, 2, 353585282334),
  (3, 526272888, 6, 913933320399397007780330399733838008),
  (11, 330882268283238188838433868932875, 2, 399393291300),
  (3, 829728828, 2, 744330277260),
  (3, 308928882, 2, 135241554353),
  (3, 233819808, 2, 484723333092),
  (3, 823818330, 2, 40237343328),
  (10, 858333983333836884883234881780, 2, 447344306330),
  (3, 848832333, 2, 446764833846),
  (3, 433533888, 2, 453376699584)]

private theorem rows_801_ok : checkRows 801 rows_801 := by decide +kernel

private def rows_833 : List Entry := [
  (3, 336888534, 2, 346320596345),
  (3, 353388876, 2, 337673246334),
  (6, 331888678433848980, 6, 884163442903927388340833141989118940),
  (4, 438383709888, 2, 39433132940),
  (3, 483398880, 2, 694733868489),
  (3, 938440818, 2, 535035400770),
  (3, 218088444, 2, 535155443321),
  (10, 881459448648887883448544244880, 10, 583322559382233453375533228325832239331863333332858585352880),
  (3, 384488424, 2, 235223233251),
  (3, 844854438, 2, 52333450466),
  (3, 864484458, 2, 954340955034),
  (3, 864547848, 2, 755475735384),
  (5, 868948484804785, 2, 265959136355),
  (3, 474849888, 2, 453677373534),
  (3, 448805898, 2, 358822853238),
  (4, 128508595488, 2, 959331103952),
  (3, 858501285, 2, 599933877957),
  (10, 548883258568855551598875868850, 2, 838262663700),
  (3, 885535284, 2, 671733661676),
  (3, 385554588, 2, 652275223836),
  (3, 568554885, 2, 339336337806),
  (3, 785558568, 2, 264633323342),
  (3, 788865585, 2, 856607836035),
  (4, 859788855680, 2, 963314559624),
  (3, 985868850, 2, 799676336678),
  (3, 188589606, 2, 365366574576),
  (3, 86818662, 2, 285516833613),
  (10, 986681687888863865686866428760, 10, 969736333773397896936337372343933798366331363669576979739360),
  (3, 884623668, 2, 313200737223),
  (3, 634568688, 2, 132971339070),
  (3, 666856848, 2, 733719554519),
  (3, 666758688, 2, 782817371328)]

private theorem rows_833_ok : checkRows 833 rows_833 := by decide +kernel

private def rows_865 : List Entry := [
  (5, 888666689878670, 10, 333776997733268368678833833683788831766383363636437363707375),
  (3, 788688696, 2, 374563754474),
  (3, 806889867, 2, 447133527135),
  (3, 887187096, 2, 736627273980),
  (3, 770187288, 2, 747734381177),
  (10, 877872888854787778317788796880, 2, 880713173760),
  (3, 878477238, 2, 877888873683),
  (3, 577738848, 4, 777377973798399059557736),
  (3, 878647785, 2, 900233866308),
  (3, 778685778, 2, 130338582150),
  (10, 888986887718088882888838747875, 10, 373482822933333728237288333870888123888388382232333338862375),
  (3, 789777888, 2, 821852333532),
  (3, 888907788, 2, 734884812132),
  (3, 889788018, 3, 3854506038803550),
  (3, 281808888, 2, 538835828388),
  (10, 688289888887988835188888884880, 10, 764836266386367377367668368787768686396875673688373616673680),
  (3, 382488888, 2, 837342687146),
  (3, 858834888, 2, 285825238338),
  (4, 846888888578, 2, 5394883944),
  (3, 885678888, 2, 393092278088),
  (5, 788898886888890, 5, 111939117173339211171477913935),
  (4, 998880878888, 2, 269073505392),
  (3, 880988889, 2, 293494332929),
  (3, 918998088, 2, 993839333280),
  (3, 908192889, 2, 337978719144),
  (10, 999898899878193995299848068880, 2, 336079956560),
  (3, 834899298, 2, 497639439696),
  (3, 939859884, 4, 373337793999939037388788),
  (3, 954988698, 3, 923838288309182979),
  (3, 789859986, 2, 937199319732),
  (5, 969888979988090, 2, 6600744600),
  (4, 908798999808, 2, 912694640000)]

private theorem rows_865_ok : checkRows 865 rows_865 := by decide +kernel

private def rows_897 : List Entry := [
  (3, 998880909, 2, 858704014158),
  (3, 8919990, 2, 740255724540),
  (3, 902100909, 2, 460525433360),
  (3, 993291000, 2, 451255544400),
  (3, 994029003, 2, 454504042551),
  (3, 390594090, 2, 234354365006),
  (3, 60959904, 2, 452075270454),
  (3, 95097096, 2, 54141705888),
  (3, 96097890, 2, 406209640910),
  (3, 997909800, 2, 796949946060),
  (3, 909800991, 2, 384420017718),
  (4, 190991191092, 3, 771971181107441148),
  (3, 91119912, 2, 474861128682),
  (10, 969919829199792113911154119910, 5, 681139759155433944354901691430),
  (3, 239919411, 2, 141756454004),
  (6, 691391991115917984, 2, 551417184144),
  (3, 614119959, 2, 439430612613),
  (3, 151719996, 2, 411722744342),
  (5, 116799219989910, 2, 157688111445),
  (4, 919807199912, 2, 107499011724),
  (3, 829110999, 2, 919949188847),
  (3, 199029912, 2, 449005022904),
  (4, 922292029319, 2, 828412224213),
  (10, 912998279923229625992432992920, 10, 542247247446447222227227742143724572448244479274224422227440),
  (3, 299942223, 2, 262664324136),
  (3, 542929392, 2, 825253444428),
  (3, 622994925, 2, 520245555404),
  (3, 992276952, 2, 674462224824),
  (12, 739929396932243992989197299339363350, 2, 724324317525),
  (4, 99298799232, 2, 287827672442),
  (3, 938990922, 2, 304920422922),
  (3, 103999392, 2, 39312431040)]

private theorem rows_897_ok : checkRows 897 rows_897 := by decide +kernel

private def rows_929 : List Entry := [
  (3, 390392913, 2, 745083131045),
  (10, 799368499129399399934533933330, 5, 849449184981348391839991336170),
  (3, 349329339, 2, 619433172942),
  (4, 933959339364, 2, 334843384748),
  (3, 335496399, 2, 373497044847),
  (4, 933739593986, 2, 523517137434),
  (5, 399999846733930, 6, 466636614340634643466438374445666695),
  (4, 893993993704, 2, 354182773584),
  (3, 909339894, 2, 711488435385),
  (3, 931094994, 2, 444993355544),
  (3, 49449219, 2, 342439049034),
  (10, 794441999543599924994494484960, 10, 414444433313543421343344711319343313136341414344833433444140),
  (3, 934249494, 2, 774242424122),
  (3, 493995444, 2, 124433432142),
  (3, 944594649, 3, 441414445441645455),
  (3, 499976544, 2, 454495709408),
  (5, 997460994494985, 2, 641024464440),
  (4, 798995449904, 2, 969484766484),
  (3, 498099495, 2, 433923497447),
  (4, 551509499992, 2, 809447884848),
  (3, 250951599, 2, 448979242884),
  (10, 599545295999395585595697691950, 2, 567704477750),
  (3, 945523995, 2, 774567221451),
  (5, 599995953455576, 2, 724657425768),
  (4, 995955575649, 2, 493653456302),
  (3, 579595956, 2, 845583542544),
  (3, 575899695, 2, 534453555765),
  (4, 985570999956, 2, 694416594524),
  (3, 99699558, 2, 844757445744),
  (4, 995092196696, 2, 544445540880),
  (3, 921066996, 2, 544932639653),
  (10, 769295996996664696639967919680, 2, 224246031360)]

private theorem rows_929_ok : checkRows 929 rows_929 := by decide +kernel

private def rows_961 : List Entry := [
  (3, 649966239, 2, 824628241161),
  (3, 935969466, 2, 432242626442),
  (3, 964666959, 2, 443205436062),
  (4, 966695798696, 2, 484176664164),
  (5, 998669679699670, 2, 653414213615),
  (3, 696799896, 2, 690094664766),
  (3, 976908996, 2, 607606436724),
  (3, 109999776, 2, 986300268440),
  (3, 791970927, 2, 997699846488),
  (10, 799174979975789939779897776290, 5, 977669694996866496944699664990),
  (3, 977743992, 2, 90777364439),
  (4, 734795999776, 2, 791090147784),
  (3, 794997765, 2, 842792877804),
  (4, 976977597798, 2, 558337374842),
  (10, 908997819378989848997876992975, 10, 487333869382884274484274474444734738714448784444747328024875),
  (6, 898999719870987792, 2, 45127570848),
  (3, 989797809, 2, 674477877776),
  (3, 879899910, 2, 457747557774),
  (3, 989898120, 2, 237784387734),
  (10, 995874899189999898238988689980, 10, 917911199746749377219971749774417772747748497174719917757440),
  (3, 429998388, 2, 416840969028),
  (3, 989583984, 2, 368416127478),
  (3, 898968459, 2, 465588262544),
  (3, 885899976, 2, 834768483336),
  (6, 999999689987198880, 5, 644268416488324422442466844825),
  (4, 899878998990, 2, 458004766568),
  (3, 908998998, 2, 462435658989),
  (7, 919399909992599999948, 2, 450797578884),
  (4, 999992999013, 2, 868844568587),
  (10, 9899290499599991999999930991760, 5, 658888585949594559859544469570),
  (3, 999399294, 2, 650454409794),
  (4, 999495999936, 2, 943751931584)]

private theorem rows_961_ok : checkRows 961 rows_961 := by decide +kernel

private def rows_993 : List Entry := [
  (3, 959699499, 2, 549229209345),
  (4, 999799965998, 2, 539542933422),
  (5, 9909989909197960, 2, 191596474445),
  (4, 9899990979100, 2, 559115415924),
  (3, 9009109989, 2, 964897560504),
  (3, 90010919100, 2, 75544975940),
  (2, 1010010, 2, 488550024939)]

private theorem rows_993_ok : checkRows 993 rows_993 := by decide +kernel

private theorem fromRows {n lo size : ℕ} {l : List Entry} (h : checkRows lo l)
    (hlen : l.length = size) (hlo : lo ≤ n) (hhi : n < lo + size) : Both n := by
  have hv := checkRows_sound lo l h (n-lo) (by omega)
  simpa [Nat.add_sub_of_le hlo] using hv

/-- Both registered interpretations of the source interval have explicit decimal
permutation certificates for every positive row below one thousand. -/
theorem finite_rows (n : ℕ) (hn : 0 < n) (hmax : n < 1000) :
    ValidWord n (n+1) ∧ ValidWord n (1+n*(n-1)/2) := by
  by_cases h1 : n < 33
  · exact fromRows rows_1_ok (size := 32) rfl (by omega) (by omega)
  by_cases h33 : n < 65
  · exact fromRows rows_33_ok (size := 32) rfl (by omega) (by omega)
  by_cases h65 : n < 97
  · exact fromRows rows_65_ok (size := 32) rfl (by omega) (by omega)
  by_cases h97 : n < 129
  · exact fromRows rows_97_ok (size := 32) rfl (by omega) (by omega)
  by_cases h129 : n < 161
  · exact fromRows rows_129_ok (size := 32) rfl (by omega) (by omega)
  by_cases h161 : n < 193
  · exact fromRows rows_161_ok (size := 32) rfl (by omega) (by omega)
  by_cases h193 : n < 225
  · exact fromRows rows_193_ok (size := 32) rfl (by omega) (by omega)
  by_cases h225 : n < 257
  · exact fromRows rows_225_ok (size := 32) rfl (by omega) (by omega)
  by_cases h257 : n < 289
  · exact fromRows rows_257_ok (size := 32) rfl (by omega) (by omega)
  by_cases h289 : n < 321
  · exact fromRows rows_289_ok (size := 32) rfl (by omega) (by omega)
  by_cases h321 : n < 353
  · exact fromRows rows_321_ok (size := 32) rfl (by omega) (by omega)
  by_cases h353 : n < 385
  · exact fromRows rows_353_ok (size := 32) rfl (by omega) (by omega)
  by_cases h385 : n < 417
  · exact fromRows rows_385_ok (size := 32) rfl (by omega) (by omega)
  by_cases h417 : n < 449
  · exact fromRows rows_417_ok (size := 32) rfl (by omega) (by omega)
  by_cases h449 : n < 481
  · exact fromRows rows_449_ok (size := 32) rfl (by omega) (by omega)
  by_cases h481 : n < 513
  · exact fromRows rows_481_ok (size := 32) rfl (by omega) (by omega)
  by_cases h513 : n < 545
  · exact fromRows rows_513_ok (size := 32) rfl (by omega) (by omega)
  by_cases h545 : n < 577
  · exact fromRows rows_545_ok (size := 32) rfl (by omega) (by omega)
  by_cases h577 : n < 609
  · exact fromRows rows_577_ok (size := 32) rfl (by omega) (by omega)
  by_cases h609 : n < 641
  · exact fromRows rows_609_ok (size := 32) rfl (by omega) (by omega)
  by_cases h641 : n < 673
  · exact fromRows rows_641_ok (size := 32) rfl (by omega) (by omega)
  by_cases h673 : n < 705
  · exact fromRows rows_673_ok (size := 32) rfl (by omega) (by omega)
  by_cases h705 : n < 737
  · exact fromRows rows_705_ok (size := 32) rfl (by omega) (by omega)
  by_cases h737 : n < 769
  · exact fromRows rows_737_ok (size := 32) rfl (by omega) (by omega)
  by_cases h769 : n < 801
  · exact fromRows rows_769_ok (size := 32) rfl (by omega) (by omega)
  by_cases h801 : n < 833
  · exact fromRows rows_801_ok (size := 32) rfl (by omega) (by omega)
  by_cases h833 : n < 865
  · exact fromRows rows_833_ok (size := 32) rfl (by omega) (by omega)
  by_cases h865 : n < 897
  · exact fromRows rows_865_ok (size := 32) rfl (by omega) (by omega)
  by_cases h897 : n < 929
  · exact fromRows rows_897_ok (size := 32) rfl (by omega) (by omega)
  by_cases h929 : n < 961
  · exact fromRows rows_929_ok (size := 32) rfl (by omega) (by omega)
  by_cases h961 : n < 993
  · exact fromRows rows_961_ok (size := 32) rfl (by omega) (by omega)
  exact fromRows rows_993_ok (size := 7) rfl (by omega) (by omega)
end DecimalFinite

/-- The original sequence uses the successive disjoint triangular blocks. -/
theorem DecimalPermutations.original_conjecture (n : ℕ) (hn : 0 < n) :
    sSup {m : ℕ | 0 < m ∧ n ∣ m ∧ (Nat.digits 10 m : Multiset ℕ) =
      (Finset.Icc (1 + n*(n-1)/2) (n*(n+1)/2)).sum (fun k => (Nat.digits 10 k : Multiset ℕ))} ≠ 0 :=
  (both_endpoints DecimalFinite.finite_rows multiple_from_large_block n hn).2

theorem OMA.solution : type_of% @OMA.S_oeis_a076072.main := by
  intro n hn
  exact (DecimalPermutations.both_endpoints DecimalFinite.finite_rows
    DecimalPermutations.multiple_from_large_block n hn).1
