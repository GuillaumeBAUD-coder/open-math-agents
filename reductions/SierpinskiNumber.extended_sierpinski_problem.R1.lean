import FormalConjectures.Wikipedia.SierpinskiNumber
import Mathlib.NumberTheory.Fermat

-- Credit: @desenyon
/-!
# Reduction by admissible exponent residues modulo 72

An exponent residue is admissible for k when k * 2^r + 1 is coprime to 2^72 - 1.
The two bit masks in the sieve track coefficients having zero and at most one
admissible residue among those processed so far. Bits are indexed by k itself.
The sieve uses every prime divisor of the modulus and covers the whole interval.
The period 72 is the least common multiple of the periods 24 and 36 of the two
classical covers. The cutoff 1200 allows a short initial search using Proth tests.

Seven odd coefficients below 271129 have exactly one admissible residue.
Four are eliminated by Proth certificates below. H1 asks for a prime in each
of the remaining three progressions. H2 and H3 handle coefficients with at least
two admissible residues that survive the first 1201 exponent tests.
The final converse establishes necessity of all three search tasks.

Project status and the numerical rank question are described at
https://www.primegrid.com/stats_esp_llr.php and https://ibethune.github.io/files/cmcgs_bethune.pdf.
-/

namespace OMA.R_SierpinskiNumber_extended_sierpinski_problem_R1

set_option maxHeartbeats 1600000 in
private theorem covered : Nat.IsSierpinskiNumber 271129 := by
  refine ⟨by decide, fun n => ?_⟩
  have hpow := Nat.one_le_two_pow (n := n)
  have hn : 241 < 271129 * 2 ^ n + 1 := by omega
  have cover : ∀ r, r < 24 → ∃ p ∈ ([3, 5, 7, 13, 17, 241] : List ℕ),
      p ∣ 271129 * 2 ^ r + 1 := by decide +kernel
  obtain ⟨p, hp, hd⟩ := cover (n % 24) (Nat.mod_lt _ (by decide))
  have bounds : 1 < p ∧ p ≤ 241 := by fin_cases hp <;> decide
  have h24 : (2 : ℕ) ^ 24 ≡ 1 [MOD p] := by fin_cases hp <;> decide +kernel
  have he : (2 : ℕ) ^ n ≡ 2 ^ (n % 24) [MOD p] := by
    conv_lhs => rw [← Nat.div_add_mod n 24, pow_add, pow_mul]
    simpa using (h24.pow (n / 24)).mul_right (2 ^ (n % 24))
  have hdiv := (Nat.modEq_zero_iff_dvd).mp
    (((he.mul_left 271129).add_right 1).trans (Nat.modEq_zero_iff_dvd.mpr hd))
  refine ⟨by omega, fun hprime => ?_⟩
  rcases hprime.eq_one_or_self_of_dvd p hdiv with h | h <;> omega

-- A divisor of a ^ (2 ^ m) + 1 of the specified Proth shape is prime.
private theorem proth_of_dvd {k a m : ℕ} (hk : 0 < k) (hsize : k < 2 ^ (m + 1))
    (hd : k * 2 ^ (m + 1) + 1 ∣ a ^ (2 ^ m) + 1) :
    (k * 2 ^ (m + 1) + 1).Prime := by
  let N := k * 2 ^ (m + 1) + 1
  have hpos : 1 < N := by simpa [N] using Nat.mul_pos hk (Nat.two_pow_pos (m + 1))
  let p := N.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hdiv : p ∣ N := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro heq
    rw [heq] at hdiv
    dsimp [N] at hdiv
    rw [pow_succ, ← Nat.mul_assoc] at hdiv
    omega
  obtain ⟨t, ht⟩ := Nat.pow_pow_add_primeFactors_one_lt hp hp2 (hdiv.trans hd)
  have ht0 : 0 < t := by
    by_contra! hz
    have := hp.one_lt
    simp [show t = 0 by omega] at ht
    omega
  have hle : 2 ^ (m + 1) < p := by nlinarith [Nat.le_mul_of_pos_left (2 ^ (m + 1)) ht0]
  by_contra hn
  have hs : p ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega : 0 < N) hn
  dsimp [N] at hs
  nlinarith [Nat.mul_le_mul (by omega : k ≤ p - 1) (by omega : 2 ^ (m + 1) ≤ p - 1),
    Nat.sub_add_cancel (by omega : 1 ≤ p)]

private theorem proth_residue {k a m : ℕ} (hk : 0 < k) (hsize : k < 2 ^ (m + 1))
    (h : (fun x : ℕ => x ^ 2 % (k * 2 ^ (m + 1) + 1))^[m] (a ^ k % (k * 2 ^ (m + 1) + 1)) =
      k * 2 ^ (m + 1)) : (k * 2 ^ (m + 1) + 1).Prime := by
  let N := k * 2 ^ (m + 1) + 1
  have lift (i : ℕ) : (fun x : ℕ => x ^ 2 % N)^[i] (a ^ k % N) ≡
      (a ^ k) ^ (2 ^ i) [MOD N] := by
    induction i with
    | zero => simpa using Nat.mod_modEq (a ^ k) N
    | succ i ih =>
      rw [Function.iterate_succ_apply', pow_succ 2 i, pow_mul]
      exact (Nat.mod_modEq _ _).trans (ih.pow 2)
  apply proth_of_dvd (a := a ^ k) hk hsize
  apply Nat.modEq_zero_iff_dvd.mp
  have he := (lift m).symm.add_right 1
  change (fun x : ℕ => x ^ 2 % N)^[m] (a ^ k % N) = _ at h
  rw [h] at he
  exact he.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl N))

-- Break long square chains into blocks for the kernel's recursion depth.
private theorem proth_blocks {k a q s : ℕ} (hk : 0 < k)
    (hsize : k < 2 ^ (128 * q + s + 1))
    (h : let N := k * 2 ^ (128 * q + s + 1) + 1
         let square := fun x : ℕ => x ^ 2 % N
         (square^[128])^[q] (square^[s] (a ^ k % N)) = k * 2 ^ (128 * q + s + 1)) :
    (k * 2 ^ (128 * q + s + 1) + 1).Prime := by
  apply proth_residue (a := a) hk hsize
  rwa [Function.iterate_add_apply, Function.iterate_mul]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
private theorem certified_singletons :
    (39079 * 2 ^ 26506 + 1).Prime ∧ (117557 * 2 ^ 51511 + 1).Prime ∧
    (127501 * 2 ^ 48 + 1).Prime ∧ (260993 * 2 ^ 313 + 1).Prime := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (26506 : ℕ) = 128 * 207 + 9 + 1 by decide]
    apply proth_blocks (k := 39079) (a := 3) (q := 207) (s := 9) <;> decide +kernel
  · rw [show (51511 : ℕ) = 128 * 402 + 54 + 1 by decide]
    apply proth_blocks (k := 117557) (a := 3) (q := 402) (s := 54) <;> decide +kernel
  · exact proth_residue (k := 127501) (a := 3) (m := 47)
      (by decide) (by decide +kernel) (by decide +kernel)
  · rw [show (313 : ℕ) = 312 + 1 by decide]
    apply proth_residue (k := 260993) (a := 3) (m := 312) <;> decide +kernel

private theorem tile_spec (p s d j : ℕ) (hs : s < p) :
    (Nat.rec (motive := fun _ => ℕ) (2 ^ s)
      (fun h a => a ||| (a <<< (p * 2 ^ h))) d).testBit j = true ↔
      j < p * 2 ^ d ∧ j % p = s := by
  induction d generalizing j with
  | zero =>
    simp only [Nat.rec_zero, Nat.testBit_two_pow, decide_eq_true_eq, pow_zero, mul_one]
    constructor
    · rintro rfl
      exact ⟨hs, Nat.mod_eq_of_lt hs⟩
    · rintro ⟨hj, he⟩
      simpa [Nat.mod_eq_of_lt hj] using he.symm
  | succ d ih =>
    simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, ih, pow_succ, ← Nat.mul_assoc]
    by_cases hj : p * 2 ^ d ≤ j
    · have hm : (j - p * 2 ^ d) % p = j % p := Nat.sub_mul_mod hj
      rw [hm]
      omega
    · omega

private theorem bit_union (f : ℕ → ℕ) (xs : List ℕ) (k : ℕ) :
    (xs.foldr (fun p b => b ||| f p) 0).testBit k = true ↔
      ∃ p ∈ xs, (f p).testBit k = true := by
  induction xs with
  | nil => simp
  | cons p xs ih => simp [ih, or_comm]

private theorem sparse_bits (B : ℕ → ℕ) (ok : ℕ → Bool) (I k : ℕ)
    (hi : I.testBit k = true) (rs : List ℕ)
    (hB : ∀ r ∈ rs, ok r = false → (B r).testBit k = true) :
    let a := rs.foldr (fun r (a : ℕ × ℕ) =>
      (a.1 &&& B r, a.1 ||| (a.2 &&& B r))) (I, I)
    (((rs.filter ok).length = 0 → a.1.testBit k = true) ∧
     ((rs.filter ok).length ≤ 1 → a.2.testBit k = true)) := by
  induction rs with
  | nil => exact ⟨fun _ => hi, fun _ => hi⟩
  | cons r rs ih =>
    obtain ⟨h0, h1⟩ := ih (fun s hs => hB s (List.mem_cons_of_mem _ hs))
    cases hr : ok r with
    | false =>
      have h := hB r (by simp) hr
      simp only [List.filter_cons, hr, Bool.false_eq_true, ↓reduceIte, List.foldr_cons,
        Nat.testBit_and, Nat.testBit_or, h, Bool.and_true, Bool.or_eq_true]
      exact ⟨h0, fun hs => Or.inr (h1 hs)⟩
    | true =>
      simp only [List.filter_cons_of_pos hr, List.length_cons, List.foldr_cons,
        Nat.testBit_or, Bool.or_eq_true]
      exact ⟨fun h => by omega, fun h => Or.inl (h0 (by omega))⟩

private theorem bit_below (w k : ℕ) (hk : k < w) :
    (((1 : ℕ) <<< w) - 1).testBit k = true := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact hk

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem sparse_coefficients (k : ℕ) (hk : k < 271129) (ho : ¬2 ∣ k)
    (hs : ((List.range 72).filter fun r => (k * 2 ^ r + 1).Coprime (2 ^ 72 - 1)).length ≤ 1) :
    k ∈ ([22699, 39079, 78557, 79309, 117557, 127501, 156511, 260993] : List ℕ) := by
  let ps : List ℕ := [3, 3, 3, 5, 7, 13, 17, 19, 37, 73, 109, 241, 433, 38737]
  -- Modulo p, the obstructed coefficient is congruent to the negative inverse of 2 ^ r.
  let offset (p r : ℕ) := p - 2 ^ (72 - r) % p
  let depth (p : ℕ) := Nat.log2 (271130 / p) + 1
  let tile (p s : ℕ) := Nat.rec (motive := fun _ => ℕ) (2 ^ s)
    (fun h a => a ||| (a <<< (p * 2 ^ h))) (depth p)
  let B (r : ℕ) := ps.foldr (fun p b => b ||| tile p (offset p r)) 0
  let I := ((1 <<< 271130) - 1) &&& tile 2 1
  let ok (r : ℕ) := decide ((k * 2 ^ r + 1).Coprime (2 ^ 72 - 1))
  have hstart : I.testBit k = true := by
    have ht := (tile_spec 2 1 (depth 2) k (by decide)).2
      ⟨lt_trans hk (by decide +kernel), by omega⟩
    change (((1 <<< 271130) - 1) &&& tile 2 1).testBit k = true
    rw [Nat.testBit_and, Bool.and_eq_true]
    exact ⟨bit_below _ _ (by omega), ht⟩
  have primes : ∀ p ∈ ps, p.Prime := by
    intro p hp
    dsimp [ps] at hp
    fin_cases hp <;> norm_num
  have table : ∀ r : Fin 72, ∀ p ∈ ps,
      offset p r < p ∧ 271129 ≤ p * 2 ^ (depth p) ∧ p.Coprime (2 ^ r.val) ∧
      p ∣ offset p r * 2 ^ r.val + 1 := by decide +kernel
  have hB (r : ℕ) (hr : r ∈ List.range 72) (hno : ok r = false) :
      (B r).testBit k = true := by
    have hn : ¬(k * 2 ^ r + 1).Coprime (2 ^ 72 - 1) := by simpa [ok] using hno
    obtain ⟨p, hp, hpk, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have fac : 2 ^ 72 - 1 = ps.prod := by decide +kernel
    have hmem := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hp)
      (fun q hq => Nat.prime_iff.mp (primes q hq)) (fac ▸ hpM)
    obtain ⟨hoffs, hlen, hc, hd⟩ := table ⟨r, List.mem_range.mp hr⟩ p hmem
    have he := Nat.ModEq.cancel_right_of_coprime hc (Nat.ModEq.add_right_cancel' 1
      ((Nat.modEq_zero_iff_dvd.mpr hpk).trans (Nat.modEq_zero_iff_dvd.mpr hd).symm))
    have hrem : k % p = offset p r := (show k % p = offset p r % p from he).trans (Nat.mod_eq_of_lt hoffs)
    apply (bit_union (fun p => tile p (offset p r)) ps k).2
    exact ⟨p, hmem, (tile_spec p _ (depth p) k hoffs).2 ⟨lt_of_lt_of_le hk hlen, hrem⟩⟩
  -- Start with every odd index. A further obstruction preserves its current count
  -- of admissible residues. An unobstructed residue increments that count.
  let out := (List.range 72).foldr (fun r (a : ℕ × ℕ) =>
    (a.1 &&& B r, a.1 ||| (a.2 &&& B r))) (I, I)
  let exceptions : List ℕ := [22699, 39079, 78557, 79309, 117557, 127501, 156511, 260993, 271129]
  have computed : out.2 = exceptions.foldr (fun j b => b ||| 2 ^ j) 0 := by decide +kernel
  have hbit : out.2.testBit k = true := (sparse_bits B ok I k hstart _ hB).2 hs
  rw [computed] at hbit
  obtain ⟨j, hj, heq⟩ := (bit_union (fun j => 2 ^ j) exceptions k).1 hbit
  have hjk : j = k := by simpa only [Nat.testBit_two_pow, decide_eq_true_eq] using heq
  subst j
  simp only [exceptions, List.mem_cons, List.not_mem_nil, or_false] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Complete classification below the proposed second coefficient when at most one
exponent residue is coprime to the period modulus. -/
theorem sparse_classification {k : ℕ} (hk : k < 271129) (ho : ¬ 2 ∣ k) :
    let residues := (List.range 72).filter fun r => (k * 2 ^ r + 1).Coprime (2 ^ 72 - 1)
    residues.length ≤ 1 ↔ k = 78557 ∨
      ∃ r, (k, r) ∈ ([(22699, 46), (39079, 10), (79309, 38), (117557, 31),
        (127501, 48), (156511, 48), (260993, 25)] : List (ℕ × ℕ)) ∧ residues = [r] := by
  dsimp only
  constructor
  · intro h
    have H := sparse_coefficients k hk ho h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at H
    rcases H with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨46, by decide, by decide +kernel⟩
    · exact Or.inr ⟨10, by decide, by decide +kernel⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨38, by decide, by decide +kernel⟩
    · exact Or.inr ⟨31, by decide, by decide +kernel⟩
    · exact Or.inr ⟨48, by decide, by decide +kernel⟩
    · exact Or.inr ⟨48, by decide, by decide +kernel⟩
    · exact Or.inr ⟨25, by decide, by decide +kernel⟩
  · rintro (rfl | ⟨r, _, hr⟩)
    · decide +kernel
    · rw [hr]
      exact le_rfl

private theorem large_term_not_dvd {k n : ℕ} (hk : 0 < k) (hn : 72 ≤ n) :
    ¬ k * 2 ^ n + 1 ∣ 2 ^ 72 - 1 := by
  intro hd
  have lower := (Nat.pow_le_pow_right (by decide : 0 < 2) hn).trans
    (Nat.le_mul_of_pos_left (2 ^ n) hk)
  have := Nat.le_of_dvd (by decide +kernel : 0 < 2 ^ 72 - 1) hd
  omega

private theorem admissible_of_prime {k n : ℕ} (hp : (k * 2 ^ n + 1).Prime)
    (hd : ¬ k * 2 ^ n + 1 ∣ 2 ^ 72 - 1) :
    (k * 2 ^ (n % 72) + 1).Coprime (2 ^ 72 - 1) := by
  let M : ℕ := 2 ^ 72 - 1
  have period : (2 : ℕ) ^ 72 ≡ 1 [MOD M] := by decide +kernel
  have ep : (2 : ℕ) ^ n ≡ 2 ^ (n % 72) [MOD M] := by
    conv_lhs => rw [← Nat.div_add_mod n 72, pow_add, pow_mul]
    simpa using (period.pow (n / 72)).mul_right (2 ^ (n % 72))
  change (k * 2 ^ (n % 72) + 1).gcd M = 1
  exact ((ep.mul_left k).add_right 1).gcd_eq.symm.trans (hp.coprime_iff_not_dvd.mpr hd)

private theorem single_progression_iff (c : ℕ × ℕ)
    (hc : c ∈ [(22699, 46), (79309, 38), (156511, 48)]) :
    (∃ n : ℕ, (c.1 * 2 ^ n + 1).Prime) ↔
      ∃ t : ℕ, (c.1 * 2 ^ (72 * t + c.2) + 1).Prime := by
  have data : ∀ a ∈ ([(22699, 46), (79309, 38), (156511, 48)] : List (ℕ × ℕ)),
      0 < a.1 ∧ ((List.range 72).filter fun r => (a.1 * 2 ^ r + 1).Coprime (2 ^ 72 - 1)) = [a.2] ∧
      ∀ r : Fin 72, ¬ a.1 * 2 ^ r.val + 1 ∣ 2 ^ 72 - 1 := by decide +kernel
  obtain ⟨hk, residues, hsmall⟩ := data c hc
  constructor
  · rintro ⟨n, hn⟩
    have hd : ¬ c.1 * 2 ^ n + 1 ∣ 2 ^ 72 - 1 := by
      by_cases h : n < 72
      · exact hsmall ⟨n, h⟩
      · exact large_term_not_dvd hk (by omega)
    have hm : n % 72 ∈ (List.range 72).filter
        (fun r => (c.1 * 2 ^ r + 1).Coprime (2 ^ 72 - 1)) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.mod_lt n (by decide : 0 < 72)),
        decide_eq_true (admissible_of_prime hn hd)⟩
    rw [residues, List.mem_singleton] at hm
    exact ⟨n / 72, by rwa [← hm, Nat.div_add_mod]⟩
  · rintro ⟨t, ht⟩
    exact ⟨72 * t + c.2, ht⟩

/-- Restrict the search for a prime beyond the finite initial segment to the
residues coprime to the period modulus. -/
private theorem search_progressions {k : ℕ} (hk : 0 < k)
    (hinit : ∀ n ≤ 1200, (k * 2 ^ n + 1).Composite) :
    (∃ n, (k * 2 ^ n + 1).Prime) ↔
      ∃ r ∈ (List.range 72).filter (fun r => (k * 2 ^ r + 1).Coprime (2 ^ 72 - 1)),
        ∃ t, (k * 2 ^ (72 * t + r) + 1).Prime := by
  constructor
  · rintro ⟨n, hn⟩
    have hn72 : 72 ≤ n := by
      by_contra! h
      exact (hinit n (by omega)).2 hn
    refine ⟨n % 72, List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩,
      n / 72, ?_⟩
    · apply decide_eq_true
      exact admissible_of_prime hn (large_term_not_dvd hk hn72)
    · rwa [Nat.div_add_mod]
  · rintro ⟨r, _, t, ht⟩
    exact ⟨72 * t + r, ht⟩

/-- The three uncertified single - residue families. -/
def H1 : Prop :=
  ∀ c ∈ ([(22699, 46), (79309, 38), (156511, 48)] : List (ℕ × ℕ)),
    ∃ t : ℕ, (c.1 * 2 ^ (72 * t + c.2) + 1).Prime

/-- Multiple admissible residues below Selfridge's coefficient. -/
def H2 : Prop :=
  ∀ k : ℕ, ¬ 2 ∣ k → k < 78557 →
    let residues := (List.range 72).filter fun r => (k * 2 ^ r + 1).Coprime (2 ^ 72 - 1)
    2 ≤ residues.length → (∀ n ≤ 1200, (k * 2 ^ n + 1).Composite) →
      ∃ r ∈ residues, ∃ t : ℕ, (k * 2 ^ (72 * t + r) + 1).Prime

/-- Multiple admissible residues strictly between the two known coefficients. -/
def H3 : Prop :=
  ∀ k : ℕ, ¬ 2 ∣ k → 78557 < k → k < 271129 →
    let residues := (List.range 72).filter fun r => (k * 2 ^ r + 1).Coprime (2 ^ 72 - 1)
    2 ≤ residues.length → (∀ n ≤ 1200, (k * 2 ^ n + 1).Composite) →
      ∃ r ∈ residues, ∃ t : ℕ, (k * 2 ^ (72 * t + r) + 1).Prime

theorem main : H1 → H2 → H3 → type_of% @SierpinskiNumber.extended_sierpinski_problem := by
  intro single below between
  have only_smaller (k : ℕ) (hk : k < 271129) (hS : k.IsSierpinskiNumber) : k = 78557 := by
    by_contra hne
    have exclude {n : ℕ} (hp : (k * 2 ^ n + 1).Prime) : False := (hS.2 n).2 hp
    by_cases hs : ((List.range 72).filter (fun r => (k * 2 ^ r + 1).Coprime (2 ^ 72 - 1))).length ≤ 1
    · rcases (sparse_classification hk hS.1).mp hs with h | ⟨r, hr, _⟩
      · exact hne h
      obtain ⟨p₁, p₂, p₃, p₄⟩ := certified_singletons
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, _⟩ | ⟨rfl, rfl⟩ | ⟨rfl, _⟩ |
        ⟨rfl, _⟩ | ⟨rfl, rfl⟩ | ⟨rfl, _⟩
      · obtain ⟨t, ht⟩ := single (22699, 46) (by decide)
        exact exclude ht
      · exact exclude p₁
      · obtain ⟨t, ht⟩ := single (79309, 38) (by decide)
        exact exclude ht
      · exact exclude p₂
      · exact exclude p₃
      · obtain ⟨t, ht⟩ := single (156511, 48) (by decide)
        exact exclude ht
      · exact exclude p₄
    · have hkpos : 0 < k := by have := hS.1; omega
      have init : ∀ n ≤ 1200, (k * 2 ^ n + 1).Composite := fun n _ => hS.2 n
      apply (not_exists.mpr (fun n => @exclude n))
      apply (search_progressions hkpos init).mpr
      rcases lt_or_gt_of_ne hne with h | h
      · exact below k hS.1 h (by omega) init
      · exact between k hS.1 h hk (by omega) init
  refine ⟨⟨covered, 78557, SierpinskiNumber.selfridge_78557, by decide⟩, ?_⟩
  rintro k ⟨hS, j, hj, hjk⟩
  by_contra! hk
  have := only_smaller k hk hS
  have := only_smaller j (lt_trans hjk hk) hj
  omega

/-- Conversely, the rank statement supplies all three hypotheses. -/
theorem necessary (rank : type_of% @SierpinskiNumber.extended_sierpinski_problem) : H1 ∧ H2 ∧ H3 := by
  have bound {a b : ℕ} (ha : a.IsSierpinskiNumber) (hb : b.IsSierpinskiNumber) (hab : a < b) :
      271129 ≤ b := rank.2 ⟨hb, a, ha, hab⟩
  have witness (k : ℕ) (ho : ¬ 2 ∣ k) (hk : k < 271129) (hne : k ≠ 78557) :
      ∃ n : ℕ, (k * 2 ^ n + 1).Prime := by
    by_contra! h
    have kpos : 0 < k := by omega
    have hS : k.IsSierpinskiNumber := ⟨ho, fun n =>
      ⟨by simpa using Nat.mul_pos kpos (Nat.two_pow_pos n), h n⟩⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := bound hS SierpinskiNumber.selfridge_78557 hlt
      omega
    · have := bound SierpinskiNumber.selfridge_78557 hS hgt
      omega
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    have bounds : ∀ a ∈ ([(22699, 46), (79309, 38), (156511, 48)] : List (ℕ × ℕ)),
        ¬ 2 ∣ a.1 ∧ a.1 < 271129 ∧ a.1 ≠ 78557 := by decide
    obtain ⟨ho, hk, hne⟩ := bounds c hc
    exact (single_progression_iff c hc).mp (witness c.1 ho hk hne)
  · intro k ho hk residues _ init
    exact (search_progressions (k := k) (by omega) init).mp (witness k ho (by omega) (by omega))
  · intro k ho hlo hhi residues _ init
    exact (search_progressions (k := k) (by omega) init).mp (witness k ho hhi (by omega))

end OMA.R_SierpinskiNumber_extended_sierpinski_problem_R1
