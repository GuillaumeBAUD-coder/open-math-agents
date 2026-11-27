import OMAReductions.R_Gilbreath_gilbreath_conjecture_R1

-- Gilbreath's conjecture for rows 1 to 500.
-- walk checks a list against the integers 0, 1, 2, ... (each entry prime by trial division, each skipped
-- integer composite by an explicit divisor), which identifies the list with the first 501 values of
-- Nat.nth Nat.Prime (walk_spec, through Nat.nth_count and Nat.count_succ). gil then takes absolute differences
-- 500 times and checks that each row starts with 1 (adiff_spec ties the list rows to the definition).
-- A verified numerical range only; not progress on the conjecture.

namespace OMA.PS

/-- Trial division with fuel: `q` has no divisor `m` with `d ≤ m` and `m * m ≤ q`. -/
def tdiv : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, d, q => if q < d * d then true else if q % d = 0 then false else tdiv f (d + 1) q

theorem tdiv_spec : ∀ (f d q : ℕ), tdiv f d q = true → 2 ≤ q →
    (∀ m, 2 ≤ m → m < d → ¬ m ∣ q) → q.Prime := by
  intro f
  induction f with
  | zero =>
    intro d q h
    simp [tdiv] at h
  | succ f ih =>
    intro d q h hq hm
    rw [tdiv] at h
    split_ifs at h with h1 h2
    · rw [Nat.prime_def_le_sqrt]
      refine ⟨hq, fun m hm1 hm2 => hm m hm1 ?_⟩
      have h3 : m * m ≤ q := Nat.le_sqrt.mp hm2
      by_contra hc
      have hc' : d ≤ m := Nat.le_of_not_lt hc
      have h4 : d * d ≤ m * m := Nat.mul_le_mul hc' hc'
      omega
    · refine ih (d + 1) q h hq (fun m hm1 hm2 => ?_)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm2 with hlt | rfl
      · exact hm m hm1 hlt
      · intro hdvd
        exact h2 (Nat.mod_eq_zero_of_dvd hdvd)

/-- A kernel-friendly primality test. -/
def isP (q : ℕ) : Bool := decide (2 ≤ q) && tdiv q 2 q

theorem isP_spec (q : ℕ) (h : isP q = true) : q.Prime := by
  rw [isP, Bool.and_eq_true, decide_eq_true_eq] at h
  exact tdiv_spec q 2 q h.2 h.1 (fun m h1 h2 => by omega)

end OMA.PS
namespace OMA.PS

/-- `m` has a divisor `d'` with `d ≤ d' < m` (search with fuel). -/
def hasDiv : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, d, m => (decide (d < m) && decide (m % d = 0)) || hasDiv f (d + 1) m

theorem hasDiv_spec : ∀ (f d m : ℕ), hasDiv f d m = true → 2 ≤ d → ¬ m.Prime := by
  intro f
  induction f with
  | zero =>
    intro d m h
    simp [hasDiv] at h
  | succ f ih =>
    intro d m h hd
    rw [hasDiv, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    rcases h with h | h
    · intro hp
      have h1 := (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h.2)
      omega
    · exact ih (d + 1) m h (by omega)

/-- A kernel-friendly compositeness test (also true for `0` and `1`). -/
def notP (m : ℕ) : Bool := decide (m < 2) || hasDiv m 2 m

theorem notP_spec (m : ℕ) (h : notP m = true) : ¬ m.Prime := by
  rw [notP, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · intro hp
    have := hp.two_le
    omega
  · exact hasDiv_spec m 2 m h (le_refl 2)

/-- Walk through the integers from `m`, where `i` primes lie below `m`, and check that the primes
met are exactly the entries of the list, in order. -/
def walk : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | 0, _, _ :: _ => false
  | f + 1, m, p :: l =>
    if m = p then isP m && walk f (m + 1) l else notP m && walk f (m + 1) (p :: l)

/-- `l` lists the primes number `i`, `i + 1`, ... (counting from zero). -/
def IsPL : ℕ → List ℕ → Prop
  | _, [] => True
  | i, p :: l => Nat.nth Nat.Prime i = p ∧ IsPL (i + 1) l

theorem walk_spec : ∀ (f m : ℕ) (l : List ℕ) (i : ℕ), Nat.count Nat.Prime m = i →
    walk f m l = true → IsPL i l := by
  intro f
  induction f with
  | zero =>
    intro m l i _ h
    cases l with
    | nil => trivial
    | cons p l => simp [walk] at h
  | succ f ih =>
    intro m l i hi h
    cases l with
    | nil => trivial
    | cons p l =>
      rw [walk] at h
      by_cases hmp : m = p
      · rw [if_pos hmp, Bool.and_eq_true] at h
        have hp : m.Prime := isP_spec m h.1
        have hc : Nat.count Nat.Prime (m + 1) = i + 1 := by
          rw [Nat.count_succ, if_pos hp, hi]
        refine ⟨?_, ih (m + 1) l (i + 1) hc h.2⟩
        rw [← hi, Nat.nth_count hp]
        exact hmp
      · rw [if_neg hmp, Bool.and_eq_true] at h
        have hnp : ¬ m.Prime := notP_spec m h.1
        have hc : Nat.count Nat.Prime (m + 1) = i := by
          rw [Nat.count_succ, if_neg hnp, hi, Nat.add_zero]
        exact ih (m + 1) (p :: l) i hc h.2

end OMA.PS
namespace OMA.Gil

open OMA.PS

/-- `l` lists `d k o, d k (o + 1), ...`, a segment of row `k` of the Gilbreath triangle. -/
def IsRow (k : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | o, a :: l => a = Gilbreath.d k o ∧ IsRow k (o + 1) l

theorem isRow_zero : ∀ (l : List ℕ) (o : ℕ), IsPL o l → IsRow 0 o l := by
  intro l
  induction l with
  | nil =>
    intro o _
    trivial
  | cons a l ih =>
    intro o h
    exact ⟨h.1.symm, ih (o + 1) h.2⟩

/-- Absolute differences of neighbours. -/
def adiff : List ℕ → List ℕ
  | a :: b :: l => ((b - a) + (a - b)) :: adiff (b :: l)
  | _ => []

theorem adiff_spec (k : ℕ) : ∀ (l : List ℕ) (o : ℕ), IsRow k o l → IsRow (k + 1) o (adiff l) := by
  intro l
  induction l with
  | nil =>
    intro o _
    trivial
  | cons a l ih =>
    intro o h
    cases l with
    | nil => trivial
    | cons b l =>
      have ha : a = Gilbreath.d k o := h.1
      have hb : b = Gilbreath.d k (o + 1) := h.2.1
      refine ⟨?_, ih (o + 1) h.2⟩
      show (b - a) + (a - b) = Int.natAbs ((Gilbreath.d k (o + 1) : ℤ) - (Gilbreath.d k o : ℤ))
      rw [← ha, ← hb]
      omega

/-- Take differences `f` times and check that every new row starts with `1`. -/
def gil : ℕ → List ℕ → Bool
  | 0, _ => true
  | f + 1, l =>
    match adiff l with
    | [] => false
    | x :: r => decide (x = 1) && gil f (x :: r)

theorem gil_spec : ∀ (f k : ℕ) (l : List ℕ), IsRow k 0 l → gil f l = true →
    ∀ i, 1 ≤ i → i ≤ f → Gilbreath.d (k + i) 0 = 1 := by
  intro f
  induction f with
  | zero =>
    intro k l _ _ i h1 h2
    omega
  | succ f ih =>
    intro k l hl h i h1 h2
    have hr := adiff_spec k l 0 hl
    rw [gil] at h
    cases hd : adiff l with
    | nil =>
      rw [hd] at h
      simp at h
    | cons x r =>
      rw [hd] at h hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · rw [← hr.1]
        exact h.1
      · have h3 := ih (k + 1) (x :: r) hr h.2 (i - 1) (by omega) (by omega)
        have e : k + 1 + (i - 1) = k + i := by omega
        rwa [e] at h3

def ps : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581]

set_option maxRecDepth 1000000 in
theorem t1 : walk 3582 0 ps = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t2 : gil 500 ps = true := by decide +kernel

theorem range (k : ℕ) (h1 : 1 ≤ k) (hK : k ≤ 500) : Gilbreath.d k 0 = 1 := by
  have hpl : IsPL 0 ps := walk_spec 3582 0 ps 0 (by simp) t1
  have h := gil_spec 500 0 ps (isRow_zero ps 0 hpl) t2 k h1 hK
  rwa [Nat.zero_add] at h

end OMA.Gil

theorem OMA.solution : OMA.R_Gilbreath_gilbreath_conjecture_R1.H1 := by
  intro k hk
  exact OMA.Gil.range k k.pos hk
