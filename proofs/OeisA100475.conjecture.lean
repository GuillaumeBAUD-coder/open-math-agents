import FormalConjectures.OEIS.«100475»

-- Problem: Prime-th recurrence with reversal at each step
-- Upstream: formal-conjectures FormalConjectures/OEIS/100475.lean:126 (declaration OeisA100475.conjecture)
-- Credit: @implicitall (the owner of the agent is credited as the solver)
-- Disproof: no positive start other than 1 makes the sequence ultimately periodic.
-- Proof idea: the decimal length never decreases along an orbit (p_y > y and a prime never ends
-- in 0), so in a periodic tail it is a constant D and every tail value y satisfies
-- 10^(D-1) ≤ y ≤ π(10^D). Chebyshev-type bounds (central binomial / primorial ≤ 4^n, plus exact
-- counts of integers coprime to z! up to 10^5 and 5·10^5) give π(10^D) < 10^(D-1) for D ≥ 5, so
-- the tail lies in [1, 1229]; a finite check with the primes below 10^4 shows no such tail exists.

namespace OMA_A100475

open Nat

/-- Counts the `k < n` with `gcd (k + 1) P = 1`. -/
def cnt (P : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cnt P n + if Nat.gcd (n + 1) P = 1 then 1 else 0

lemma cnt_eq (P n : ℕ) :
    cnt P n = ((Finset.range n).filter (fun k => Nat.gcd (k + 1) P = 1)).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cnt, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem]
      simp
    · simp

lemma count_prime_le (z x : ℕ) :
    Nat.count Nat.Prime (x + 1) ≤ (z + 1) + cnt (Nat.factorial z) x := by
  rw [Nat.count_eq_card_filter_range, cnt_eq]
  calc ((Finset.range (x + 1)).filter Nat.Prime).card
      ≤ ((Finset.range (z + 1)) ∪ ((Finset.range x).filter
          (fun k => Nat.gcd (k + 1) z.factorial = 1)).image (· + 1)).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp
        have hp1 := hp.2.one_lt
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, Finset.mem_filter]
        by_cases hpz : p ≤ z
        · left; omega
        · right
          refine ⟨p - 1, ⟨by omega, ?_⟩, by omega⟩
          have h1 : p - 1 + 1 = p := by omega
          rw [h1]
          exact (Nat.Prime.coprime_iff_not_dvd hp.2).2 (by rw [hp.2.dvd_factorial]; omega)
    _ ≤ (z + 1) + ((Finset.range x).filter (fun k => Nat.gcd (k + 1) z.factorial = 1)).card := by
        refine (Finset.card_union_le _ _).trans ?_
        rw [Finset.card_range]
        exact Nat.add_le_add_left Finset.card_image_le _

/-- Primes in `(m, M]` and the split of the prime count. -/
lemma split (m M : ℕ) (h : m ≤ M) :
    Nat.count Nat.Prime (M + 1) = Nat.count Nat.Prime (m + 1) +
        ((Finset.Ico (m + 1) (M + 1)).filter Nat.Prime).card ∧
      primorial M = primorial m * ∏ p ∈ (Finset.Ico (m + 1) (M + 1)).filter Nat.Prime, p := by
  have hU : Finset.range (M + 1) = Finset.range (m + 1) ∪ Finset.Ico (m + 1) (M + 1) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  have hD : Disjoint ((Finset.range (m + 1)).filter Nat.Prime)
      ((Finset.Ico (m + 1) (M + 1)).filter Nat.Prime) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive _ _ _
  constructor
  · rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range, hU, Finset.filter_union,
      Finset.card_union_of_disjoint hD]
  · unfold primorial
    rw [hU, Finset.filter_union, Finset.prod_union hD]

lemma pow_le_prod (m : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, m < p) : m ^ S.card ≤ ∏ p ∈ S, p := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => (hS p hp).le)

lemma bigK (m M : ℕ) (h : m ≤ M) :
    m ^ (Nat.count Nat.Prime (M + 1) - Nat.count Nat.Prime (m + 1)) ≤ 4 ^ M := by
  obtain ⟨h1, h2⟩ := split m M h
  rw [h1, Nat.add_sub_cancel_left]
  refine (pow_le_prod m _ ?_).trans ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    omega
  · have hpos := primorial_pos m
    calc ∏ p ∈ (Finset.Ico (m + 1) (M + 1)).filter Nat.Prime, p
        ≤ primorial m * ∏ p ∈ (Finset.Ico (m + 1) (M + 1)).filter Nat.Prime, p :=
          Nat.le_mul_of_pos_left _ hpos
      _ = primorial M := h2.symm
      _ ≤ 4 ^ M := primorial_le_four_pow M

lemma block (m : ℕ) :
    m ^ (Nat.count Nat.Prime (2 * m + 1) - Nat.count Nat.Prime (m + 1)) ≤ 4 ^ m := by
  obtain ⟨h1, h2⟩ := split m (2 * m) (by omega)
  rw [h1, Nat.add_sub_cancel_left]
  refine (pow_le_prod m _ ?_).trans ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    omega
  · have hpos := primorial_pos m
    have h3 : primorial (m + m) ≤ primorial m * Nat.choose (m + m) m := primorial_add_le le_rfl
    rw [show m + m = 2 * m by ring, h2] at h3
    have h4 := Nat.le_of_mul_le_mul_left h3 hpos
    refine h4.trans ?_
    have := Nat.centralBinom_le_four_pow m
    rwa [Nat.centralBinom_eq_two_mul_choose] at this

lemma exp_le_of (L m : ℕ) (h : (2.7182818286 : ℝ) ^ L ≤ m) : Real.exp L ≤ m := by
  have : Real.exp L = Real.exp 1 ^ L := by rw [← Real.exp_nat_mul, mul_one]
  rw [this]
  exact le_trans (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le L) h

lemma log_bound (m c k L : ℕ) (hm : Real.exp L ≤ m) (h : m ^ c ≤ 4 ^ k) :
    10000 * c * L ≤ 13863 * k := by
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (Real.exp_pos _) hm
  have h1 : (L : ℝ) ≤ Real.log m := (Real.le_log_iff_exp_le hm0).2 hm
  have h2 : (c : ℝ) * Real.log m ≤ k * Real.log 4 := by
    have h' : ((m : ℝ)) ^ c ≤ (4 : ℝ) ^ k := by exact_mod_cast h
    have := Real.log_le_log (by positivity) h'
    rwa [Real.log_pow, Real.log_pow] at this
  have h3 : Real.log 4 < 1.3863 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  have h4 : (c : ℝ) * L ≤ c * Real.log m := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h5 : (k : ℝ) * Real.log 4 ≤ k * 1.3863 := mul_le_mul_of_nonneg_left h3.le (by positivity)
  have h6 : ((10000 * c * L : ℕ) : ℝ) ≤ ((13863 * k : ℕ) : ℝ) := by
    push_cast; nlinarith
  exact_mod_cast h6

lemma blk (m L : ℕ) (h : (2.7182818286 : ℝ) ^ L ≤ m) :
    10000 * (Nat.count Nat.Prime (2 * m + 1) - Nat.count Nat.Prime (m + 1)) * L ≤ 13863 * m :=
  log_bound m _ m L (exp_le_of L m h) (block m)

end OMA_A100475

namespace OMA_A100475

open Nat

lemma cnt_316 : cnt (Nat.factorial 316) 100000 = 9528 := by decide +kernel

lemma cnt_708 : cnt (Nat.factorial 708) 500000 = 41413 := by decide +kernel

lemma pi5 : Nat.count Nat.Prime 100001 ≤ 9845 := by
  have := count_prime_le 316 100000
  rw [cnt_316] at this
  omega

lemma pi6 : Nat.count Nat.Prime (10 ^ 6) < 10 ^ 5 := by
  have h1 := count_prime_le 708 500000
  rw [cnt_708] at h1
  have h2 := blk 500000 13 (by norm_num)
  have h3 : Nat.count Nat.Prime (10 ^ 6) ≤ Nat.count Nat.Prime (2 * 500000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have h4 : Nat.count Nat.Prime (500000 + 1) ≤ Nat.count Nat.Prime (2 * 500000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  norm_num at h1 h2 h3 h4 ⊢
  omega

lemma pi7 : Nat.count Nat.Prime (10 ^ 7) < 10 ^ 6 := by
  have b0 := blk 78125 11 (by norm_num)
  have b1 := blk 156250 11 (by norm_num)
  have b2 := blk 312500 12 (by norm_num)
  have b3 := blk 625000 13 (by norm_num)
  have b4 := blk 1250000 14 (by norm_num)
  have b5 := blk 2500000 14 (by norm_num)
  have b6 := blk 5000000 15 (by norm_num)
  have m0 : Nat.count Nat.Prime (78125 + 1) ≤ Nat.count Nat.Prime (2 * 78125 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m1 : Nat.count Nat.Prime (156250 + 1) ≤ Nat.count Nat.Prime (2 * 156250 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m2 : Nat.count Nat.Prime (312500 + 1) ≤ Nat.count Nat.Prime (2 * 312500 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m3 : Nat.count Nat.Prime (625000 + 1) ≤ Nat.count Nat.Prime (2 * 625000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m4 : Nat.count Nat.Prime (1250000 + 1) ≤ Nat.count Nat.Prime (2 * 1250000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m5 : Nat.count Nat.Prime (2500000 + 1) ≤ Nat.count Nat.Prime (2 * 2500000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m6 : Nat.count Nat.Prime (5000000 + 1) ≤ Nat.count Nat.Prime (2 * 5000000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have h0 : Nat.count Nat.Prime (78125 + 1) ≤ Nat.count Nat.Prime 100001 :=
    Nat.count_monotone _ (by norm_num)
  have hx : Nat.count Nat.Prime (10 ^ 7) ≤ Nat.count Nat.Prime (2 * 5000000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have p5 := pi5
  norm_num at b0 b1 b2 b3 b4 b5 b6 m0 m1 m2 m3 m4 m5 m6 h0 hx ⊢
  omega

lemma pi8 : Nat.count Nat.Prime (10 ^ 8) < 10 ^ 7 := by
  have b0 := blk 390625 12 (by norm_num)
  have b1 := blk 781250 13 (by norm_num)
  have b2 := blk 1562500 14 (by norm_num)
  have b3 := blk 3125000 14 (by norm_num)
  have b4 := blk 6250000 15 (by norm_num)
  have b5 := blk 12500000 16 (by norm_num)
  have b6 := blk 25000000 17 (by norm_num)
  have b7 := blk 50000000 17 (by norm_num)
  have m0 : Nat.count Nat.Prime (390625 + 1) ≤ Nat.count Nat.Prime (2 * 390625 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m1 : Nat.count Nat.Prime (781250 + 1) ≤ Nat.count Nat.Prime (2 * 781250 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m2 : Nat.count Nat.Prime (1562500 + 1) ≤ Nat.count Nat.Prime (2 * 1562500 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m3 : Nat.count Nat.Prime (3125000 + 1) ≤ Nat.count Nat.Prime (2 * 3125000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m4 : Nat.count Nat.Prime (6250000 + 1) ≤ Nat.count Nat.Prime (2 * 6250000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m5 : Nat.count Nat.Prime (12500000 + 1) ≤ Nat.count Nat.Prime (2 * 12500000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m6 : Nat.count Nat.Prime (25000000 + 1) ≤ Nat.count Nat.Prime (2 * 25000000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have m7 : Nat.count Nat.Prime (50000000 + 1) ≤ Nat.count Nat.Prime (2 * 50000000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  have h0 : Nat.count Nat.Prime (390625 + 1) ≤ 390625 + 1 := Nat.count_le _
  have hx : Nat.count Nat.Prime (10 ^ 8) ≤ Nat.count Nat.Prime (2 * 50000000 + 1) :=
    Nat.count_monotone _ (by norm_num)
  norm_num at b0 b1 b2 b3 b4 b5 b6 b7 m0 m1 m2 m3 m4 m5 m6 m7 h0 hx ⊢
  omega

lemma piBig (m : ℕ) (hm : 10 ^ 7 ≤ m) : Nat.count Nat.Prime (100 * m) < 10 * m := by
  have hK := bigK m (100 * m) (by omega)
  have he : Real.exp (16 : ℕ) ≤ m := by
    refine le_trans (exp_le_of 16 (10 ^ 7) (by norm_num)) ?_
    exact_mod_cast hm
  have hb := log_bound m _ (100 * m) 16 he hK
  have h0 : Nat.count Nat.Prime (m + 1) ≤ m + 1 := Nat.count_le _
  have h1 : Nat.count Nat.Prime (m + 1) ≤ Nat.count Nat.Prime (100 * m + 1) :=
    Nat.count_monotone _ (by omega)
  have h2 : Nat.count Nat.Prime (100 * m) ≤ Nat.count Nat.Prime (100 * m + 1) :=
    Nat.count_monotone _ (by omega)
  omega

lemma piD (D : ℕ) (hD : 5 ≤ D) : Nat.count Nat.Prime (10 ^ D) < 10 ^ (D - 1) := by
  rcases (show D = 5 ∨ D = 6 ∨ D = 7 ∨ D = 8 ∨ 9 ≤ D by omega) with h | h | h | h | h
  · subst h
    have : Nat.count Nat.Prime (10 ^ 5) ≤ Nat.count Nat.Prime 100001 :=
      Nat.count_monotone _ (by norm_num)
    have := pi5
    norm_num at *
    omega
  · subst h; exact pi6
  · subst h; exact pi7
  · subst h; exact pi8
  · obtain ⟨k, rfl⟩ : ∃ k, D = k + 9 := ⟨D - 9, by omega⟩
    have e1 : 10 ^ (k + 9) = 100 * 10 ^ (k + 7) := by ring
    have e2 : 10 ^ (k + 9 - 1) = 10 * 10 ^ (k + 7) := by
      rw [show k + 9 - 1 = k + 8 by omega]; ring
    rw [e1, e2]
    apply piBig
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

end OMA_A100475

namespace OMA_A100475

open Nat OeisA100475

/-- Trial division by `d, d+1, ...` with fuel. -/
def tdAux (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, d => if n < d * d then true else if n % d = 0 then false else tdAux n fuel (d + 1)

def isPrimeB (n : ℕ) : Bool := 2 ≤ n && tdAux n n 2

lemma tdAux_spec (n : ℕ) : ∀ fuel d, n < (d + fuel) * (d + fuel) →
    (tdAux n fuel d = true ↔ ∀ k, d ≤ k → k * k ≤ n → n % k ≠ 0) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d hd
    simp only [tdAux, true_iff]
    intro k hk hkn
    have : d * d ≤ k * k := Nat.mul_le_mul hk hk
    simp at hd
    omega
  | succ f ih =>
    intro d hd
    simp only [tdAux]
    by_cases h1 : n < d * d
    · simp only [h1, if_true, true_iff]
      intro k hk hkn
      have : d * d ≤ k * k := Nat.mul_le_mul hk hk
      omega
    · simp only [h1, if_false]
      by_cases h2 : n % d = 0
      · simp only [h2, if_true, Bool.false_eq_true, false_iff, not_forall]
        exact ⟨d, le_rfl, by omega, by simp [h2]⟩
      · simp only [h2, if_false]
        rw [ih (d + 1) (by
          have : d + 1 + f = d + (f + 1) := by omega
          rw [this]; exact hd)]
        constructor
        · intro H k hk hkn
          rcases Nat.eq_or_lt_of_le hk with h | h
          · subst h; exact h2
          · exact H k h hkn
        · intro H k hk hkn
          exact H k (by omega) hkn

lemma isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  unfold isPrimeB
  rw [Bool.and_eq_true, decide_eq_true_iff, tdAux_spec n n 2 (by nlinarith)]
  apply and_congr_right
  intro _
  constructor
  · intro H m hm hms hdvd
    have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
    exact H m hm hmm (Nat.mod_eq_zero_of_dvd hdvd)
  · intro H k hk hkn hmod
    exact H k hk (Nat.le_sqrt.mpr hkn) (Nat.dvd_of_mod_eq_zero hmod)

def walk : ℕ → List ℕ
  | 0 => []
  | n + 1 => if isPrimeB n then walk n ++ [n] else walk n

lemma walk_spec (n : ℕ) : (walk n).length = Nat.count Nat.Prime n ∧
    ∀ k (h : k < (walk n).length), (walk n)[k] = Nat.nth Nat.Prime k := by
  induction n with
  | zero => simp [walk]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases hp : n.Prime
    · have hb : isPrimeB n = true := (isPrimeB_iff n).2 hp
      simp only [walk, hb, if_true, List.length_append, List.length_singleton]
      refine ⟨by rw [Nat.count_succ, ih1]; simp [hp], ?_⟩
      intro k hk
      by_cases hk' : k < (walk n).length
      · rw [List.getElem_append_left hk']; exact ih2 k hk'
      · have : k = (walk n).length := by omega
        subst this
        rw [List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem_singleton]
        rw [ih1, Nat.nth_count hp]
    · have hb : isPrimeB n = false := by
        cases h : isPrimeB n
        · rfl
        · exact absurd ((isPrimeB_iff n).1 h) hp
      simp only [walk, hb, Bool.false_eq_true, if_false]
      refine ⟨by rw [Nat.count_succ, ih1]; simp [hp], ?_⟩
      exact ih2

def tbl : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973]

lemma walk_eq : walk 10000 = tbl := by decide +kernel

lemma tbl_len : tbl.length = 1229 := by decide +kernel

lemma count_10000 : Nat.count Nat.Prime 10000 = 1229 := by
  rw [← (walk_spec 10000).1, walk_eq, tbl_len]

lemma nth_tbl (k : ℕ) (hk : k < 1229) : Nat.nth Nat.Prime k = tbl.getD k 0 := by
  have h := (walk_spec 10000).2 k (by rw [walk_eq, tbl_len]; exact hk)
  rw [← h]
  simp only [walk_eq]
  rw [List.getD_eq_getElem]

def ln (k : ℕ) : ℕ := (Nat.digits 10 k).length

def gc (y : ℕ) : ℕ := reverseDigits (tbl.getD (y - 1) 0)

def good : ℕ → ℕ → Bool
  | 0, y => 1 ≤ y && y ≤ 1229 && ln (gc y) == ln y
  | i + 1, y => good i y && good i (gc y)

lemma no_good : ∀ y < 1230, good 5 y = false := by decide +kernel

end OMA_A100475

namespace OMA_A100475

open Nat OeisA100475

lemma prime_mod_ten {p : ℕ} (hp : p.Prime) : p % 10 ≠ 0 := by
  intro h
  have h2 : 2 ∣ p := by omega
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h' | h' <;> omega

lemma digits_rev (p : ℕ) (hp : p % 10 ≠ 0) :
    Nat.digits 10 (reverseDigits p) = (Nat.digits 10 p).reverse := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hd : Nat.digits 10 p = (p % 10) :: Nat.digits 10 (p / 10) :=
    Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hp0)
  unfold reverseDigits
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro l hl
    exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hl)
  · intro h
    simp [hd, hp]

lemma ln_rev {p : ℕ} (hp : p.Prime) : ln (reverseDigits p) = ln p := by
  unfold ln
  rw [digits_rev p (prime_mod_ten hp), List.length_reverse]

lemma rev_ne_zero {p : ℕ} (hp : p.Prime) : reverseDigits p ≠ 0 := by
  intro h
  have := digits_rev p (prime_mod_ten hp)
  rw [h, Nat.digits_zero] at this
  have h2 : Nat.digits 10 p = [] := by
    have := congrArg List.reverse this
    simpa using this.symm
  rw [Nat.digits_eq_nil_iff_eq_zero] at h2
  exact hp.ne_zero h2

lemma ln_mono {a b : ℕ} (h : a ≤ b) : ln a ≤ ln b := by
  unfold ln
  rw [Nat.digits_length_le_iff (by norm_num)]
  exact lt_of_le_of_lt h (Nat.lt_base_pow_length_digits (by norm_num))

lemma step (x n : ℕ) : aStartAt x (n + 1) =
    if aStartAt x n = 0 then 0 else reverseDigits (Nat.nth Nat.Prime (aStartAt x n - 1)) := rfl

lemma orbit_ne_zero (x : ℕ) (hx : 0 < x) : ∀ n, aStartAt x n ≠ 0 := by
  intro n
  induction n with
  | zero => show x ≠ 0; omega
  | succ n ih =>
    rw [step, if_neg ih]
    exact rev_ne_zero (Nat.prime_nth_prime _)

lemma orbit_succ (x : ℕ) (hx : 0 < x) (n : ℕ) :
    aStartAt x (n + 1) = reverseDigits (Nat.nth Nat.Prime (aStartAt x n - 1)) := by
  rw [step, if_neg (orbit_ne_zero x hx n)]

lemma ln_orbit_le (x : ℕ) (hx : 0 < x) (n : ℕ) : ln (aStartAt x n) ≤ ln (aStartAt x (n + 1)) := by
  rw [orbit_succ x hx, ln_rev (Nat.prime_nth_prime _)]
  apply ln_mono
  have := Nat.add_two_le_nth_prime (aStartAt x n - 1)
  omega

/-- A value `y` whose image keeps its digit length lies below `1230`. -/
lemma small_of_ln (y : ℕ) (hy : y ≠ 0)
    (h : ln (Nat.nth Nat.Prime (y - 1)) = ln y) : y ≤ 1229 := by
  set D := ln y with hD
  have h1 : 10 ^ D ≤ 10 * y := Nat.base_pow_length_digits_le 10 y (by norm_num) hy
  have h2 : Nat.nth Nat.Prime (y - 1) < 10 ^ D := by
    rw [← h]; exact Nat.lt_base_pow_length_digits (by norm_num)
  have h3 : y ≤ Nat.count Nat.Prime (10 ^ D) := by
    by_contra hc
    have : Nat.count Nat.Prime (10 ^ D) ≤ y - 1 := by omega
    rw [Nat.count_le_iff_le_nth (p := Nat.Prime) Nat.infinite_setOfPred_prime] at this
    omega
  by_cases hD5 : 5 ≤ D
  · have := piD D hD5
    have e : 10 ^ D = 10 * 10 ^ (D - 1) := by
      rw [← _root_.pow_succ']; congr 1; omega
    omega
  · have : 10 ^ D ≤ 10 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.count_monotone Nat.Prime this
    rw [show (10 : ℕ) ^ 4 = 10000 by norm_num, count_10000] at this
    omega

end OMA_A100475

open OMA_A100475 OeisA100475 in
theorem OMA.disproof : ¬ (type_of% @OeisA100475.conjecture) := by
  rintro ⟨x, hx0, -, N, P, hP, hper⟩
  have hmono : Monotone (fun n => ln (aStartAt x n)) :=
    monotone_nat_of_le_succ (fun n => ln_orbit_le x hx0 n)
  -- in the periodic tail the digit length is constant
  have htail : ∀ n, N ≤ n → ln (aStartAt x (n + 1)) = ln (aStartAt x n) := by
    intro n hn
    apply le_antisymm
    · have h1 : ln (aStartAt x (n + 1)) ≤ ln (aStartAt x (n + P)) := hmono (by omega)
      rwa [hper n hn] at h1
    · exact hmono (by omega)
  have hkey : ∀ n, N ≤ n → aStartAt x n ≤ 1229 ∧ OMA_A100475.gc (aStartAt x n) = aStartAt x (n + 1) ∧
      ln (aStartAt x (n + 1)) = ln (aStartAt x n) := by
    intro n hn
    have hne := orbit_ne_zero x hx0 n
    have hs := orbit_succ x hx0 n
    have hl := htail n hn
    rw [hs, ln_rev (Nat.prime_nth_prime _)] at hl
    have hsmall := small_of_ln (aStartAt x n) hne hl
    refine ⟨hsmall, ?_, htail n hn⟩
    rw [hs]
    unfold OMA_A100475.gc
    rw [nth_tbl _ (by omega)]
  have hgood : ∀ i n, N ≤ n → OMA_A100475.good i (aStartAt x n) = true := by
    intro i
    induction i with
    | zero =>
      intro n hn
      obtain ⟨h1, h2, h3⟩ := hkey n hn
      have hne := orbit_ne_zero x hx0 n
      simp only [OMA_A100475.good, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨⟨by omega, h1⟩, ?_⟩
      rw [h2, h3]
    | succ i ih =>
      intro n hn
      obtain ⟨-, h2, -⟩ := hkey n hn
      simp only [OMA_A100475.good, Bool.and_eq_true]
      refine ⟨ih n hn, ?_⟩
      rw [h2]
      exact ih (n + 1) (by omega)
  have h5 := hgood 5 N le_rfl
  have hN := (hkey N le_rfl).1
  rw [no_good (aStartAt x N) (by omega)] at h5
  exact Bool.false_ne_true h5
