import FormalConjectures.OEIS.«92243»

-- Problem: OEIS A092243, conjecture 1: the prime-gap tug-of-war score is positive for some
-- n > 250000.
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Witness: n = 261150, where the score is 1 and the n-th prime (0-indexed) is 3666581.
-- The kernel scans every integer from 4 to 3666581. Primality of q in [B, B^2) is tested by
-- one gcd of q with the product of all primes below B. The scan is cut into small chunks,
-- each checked by kernel evaluation; no native code is trusted.

namespace OMA

/-- For `B ≤ q < B * B`, `q` is prime iff it is coprime to the product of the primes below `B`. -/
theorem gtest (B P : ℕ) (L : List ℕ) (hL : L.prod = P) (hlt : ∀ l ∈ L, 0 < l ∧ l < B)
    (hdiv : ∀ r, r < B → r.Prime → r ∣ P) (q : ℕ) (h1 : B ≤ q) (h2 : q < B * B) (h0 : 2 ≤ q) :
    Nat.gcd q P = 1 ↔ q.Prime := by
  constructor
  · intro hg
    by_contra hnp
    have hr : (q.minFac).Prime := Nat.minFac_prime (by omega)
    have hrq : q.minFac ∣ q := Nat.minFac_dvd q
    have hsq : q.minFac ^ 2 ≤ q := Nat.minFac_sq_le_self (by omega) hnp
    have hrB : q.minFac < B := by
      by_contra hge
      have hge' : B ≤ q.minFac := Nat.le_of_not_lt hge
      have : B * B ≤ q.minFac * q.minFac := Nat.mul_le_mul hge' hge'
      have h3 : q.minFac ^ 2 = q.minFac * q.minFac := sq _
      omega
    have hrP := hdiv _ hrB hr
    have h1' : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd hrq hrP
    rw [hg] at h1'
    exact hr.one_lt.ne' (Nat.dvd_one.mp h1')
  · intro hq
    rcases Nat.coprime_or_dvd_of_prime hq P with h | h
    · exact h
    · exfalso
      rw [← hL] at h
      obtain ⟨l, hl, hql⟩ := (Prime.dvd_prod_iff (Nat.Prime.prime hq)).mp h
      have := hlt l hl
      have := Nat.le_of_dvd this.1 hql
      omega

/-- One scan step. State: next number, number of primes below it, last prime, last gap,
number of gap increases, number of gap decreases. -/
def step (P : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  match st with
  | (q, c, p, g, u, d) =>
    cond (Nat.beq (Nat.gcd q P) 1)
      (q + 1, c + 1, q, q - p, cond (Nat.blt g (q - p)) (u + 1) u, cond (Nat.blt (q - p) g) (d + 1) d)
      (q + 1, c, p, g, u, d)

def run (P : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
  | 0, st => st
  | f + 1, st => run P f (step P st)

/-- The invariant tying the scan state to `Nat.nth Nat.Prime` and the score. -/
def Inv (st : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  match st with
  | (q, c, p, g, u, d) =>
    2 ≤ c ∧ Nat.count Nat.Prime q = c ∧ Nat.nth Nat.Prime (c - 1) = p ∧
      g = OeisA92243.primeGap (c - 1) ∧ OeisA92243.a (c - 1) = (u : ℤ) - (d : ℤ)

theorem a_succ (m : ℕ) (hm : 1 ≤ m) : OeisA92243.a (m + 1) = OeisA92243.a m +
    ((OeisA92243.primeGap (m + 1) : ℤ) - (OeisA92243.primeGap m : ℤ)).sign := by
  unfold OeisA92243.a
  rw [if_neg (by omega)]
  rcases Nat.eq_or_lt_of_le hm with h | h
  · subst h
    simp
  · rw [if_neg (by omega), Finset.sum_Icc_succ_top (by omega)]
    simp

theorem step_fst (P : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : (step P st).1 = st.1 + 1 := by
  obtain ⟨q, c, p, g, u, d⟩ := st
  simp only [step]
  cases Nat.beq (Nat.gcd q P) 1 <;> rfl

theorem step_inv (P : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (hI : Inv st)
    (htest : Nat.gcd st.1 P = 1 ↔ (st.1).Prime) : Inv (step P st) := by
  obtain ⟨q, c, p, g, u, d⟩ := st
  obtain ⟨hc, hcount, hnth, hg, ha⟩ := hI
  simp only at htest
  simp only [step]
  cases hb : Nat.beq (Nat.gcd q P) 1
  · have hnp : ¬ q.Prime := by
      intro hq
      have := htest.mpr hq
      rw [this] at hb
      exact absurd hb (by decide)
    refine ⟨hc, ?_, hnth, hg, ha⟩
    rw [Nat.count_succ, if_neg hnp, hcount, Nat.add_zero]
  · have hq : q.Prime := htest.mp (Nat.eq_of_beq_eq_true hb)
    have hnthc : Nat.nth Nat.Prime c = q := by
      rw [← hcount]; exact Nat.nth_count hq
    have hgap : OeisA92243.primeGap c = q - p := by
      unfold OeisA92243.primeGap
      rw [hnthc, hnth]
    have hsucc := a_succ (c - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ c)] at hsucc
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · rw [Nat.count_succ, if_pos hq, hcount]
    · rw [Nat.add_sub_cancel]; exact hnthc
    · rw [Nat.add_sub_cancel]; exact hgap.symm
    · rw [Nat.add_sub_cancel, hsucc, ha, hgap, ← hg]
      rcases Nat.lt_trichotomy g (q - p) with h | h | h
      · have e1 : Nat.blt g (q - p) = true := by rw [Nat.blt_eq]; exact h
        have e2 : Nat.blt (q - p) g = false := by
          rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega
        have hs : (((q - p : ℕ) : ℤ) - (g : ℤ)).sign = 1 :=
          Int.sign_eq_one_of_pos (by omega)
        rw [e1, e2, hs]
        simp only [cond_true, cond_false]
        push_cast
        ring
      · have e1 : Nat.blt g (q - p) = false := by
          rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega
        have e2 : Nat.blt (q - p) g = false := by
          rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega
        have hs : (((q - p : ℕ) : ℤ) - (g : ℤ)).sign = 0 := by
          rw [h, sub_self]; rfl
        rw [e1, e2, hs]
        simp only [cond_false]
        ring
      · have e1 : Nat.blt g (q - p) = false := by
          rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega
        have e2 : Nat.blt (q - p) g = true := by rw [Nat.blt_eq]; exact h
        have hs : (((q - p : ℕ) : ℤ) - (g : ℤ)).sign = -1 :=
          Int.sign_eq_neg_one_of_neg (by omega)
        rw [e1, e2, hs]
        simp only [cond_true, cond_false]
        push_cast
        ring

theorem run_inv (B P : ℕ) (htest : ∀ q, B ≤ q → q < B * B → 2 ≤ q → (Nat.gcd q P = 1 ↔ q.Prime))
    (hB : 2 ≤ B) : ∀ (n : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ), Inv st → B ≤ st.1 → st.1 + n ≤ B * B →
      Inv (run P n st) := by
  intro n
  induction n with
  | zero => intro st hI _ _; exact hI
  | succ n ih =>
    intro st hI h1 h2
    have hs := step_fst P st
    exact ih (step P st) (step_inv P st hI (htest st.1 h1 (by omega) (by omega)))
      (by omega) (by omega)

theorem chain (B P : ℕ) (htest : ∀ q, B ≤ q → q < B * B → 2 ≤ q → (Nat.gcd q P = 1 ↔ q.Prime))
    (hB : 2 ≤ B) (n : ℕ) (s s' : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (h : run P n s = s') (hI : Inv s)
    (h1 : B ≤ s.1) (h2 : s.1 + n ≤ B * B) : Inv s' := by
  subst h
  exact run_inv B P htest hB n s hI h1 h2

/-- `k n`, written so that kernel evaluation computes `n` to a numeral first. -/
def seqN (n : ℕ) (k : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem seqN_eq (n : ℕ) (k : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : seqN n k = k n := by
  cases n <;> rfl

/-- The first `x ≥ q` (within `f` steps) that is coprime to `P`. -/
def nextP (P : ℕ) : ℕ → ℕ → ℕ
  | 0, q => q
  | f + 1, q => cond (Nat.beq (Nat.gcd q P) 1) q (nextP P f (q + 1))

theorem nextP_spec (P : ℕ) : ∀ (f q : ℕ), q ≤ nextP P f q ∧
    ∀ x, q ≤ x → x < nextP P f q → Nat.gcd x P ≠ 1 := by
  intro f
  induction f with
  | zero =>
    intro q
    exact ⟨le_refl q, fun x h1 h2 => absurd h2 (by simp only [nextP]; omega)⟩
  | succ f ih =>
    intro q
    cases hb : Nat.beq (Nat.gcd q P) 1
    · have hne : Nat.gcd q P ≠ 1 := Nat.ne_of_beq_eq_false hb
      obtain ⟨h1, h2⟩ := ih (q + 1)
      have e : nextP P (f + 1) q = nextP P f (q + 1) := by
        simp only [nextP, hb, cond_false]
      rw [e]
      refine ⟨by omega, fun x hx1 hx2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hx1 with h | h
      · rw [← h]; exact hne
      · exact h2 x (by omega) hx2
    · have e : nextP P (f + 1) q = q := by
        simp only [nextP, hb, cond_true]
      rw [e]
      exact ⟨le_refl q, fun x h1 h2 => absurd h2 (by omega)⟩

/-- The scan, one prime per step, with plain number arguments. -/
def scanP (P : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
  | 0, q, c, p, g, u, d => (q, c, p, g, u, d)
  | n + 1, q, c, p, g, u, d =>
    seqN (nextP P 400 q) fun q' =>
      cond (Nat.beq (Nat.gcd q' P) 1)
        (scanP P n (q' + 1) (c + 1) q' (q' - p) (cond (Nat.blt g (q' - p)) (u + 1) u)
          (cond (Nat.blt (q' - p) g) (d + 1) d))
        (scanP P n (q' + 1) c p g u d)

theorem scanP_fst_ge (P : ℕ) : ∀ (n q c p g u d : ℕ), q ≤ (scanP P n q c p g u d).1 := by
  intro n
  induction n with
  | zero => intro q c p g u d; exact le_refl q
  | succ n ih =>
    intro q c p g u d
    have hle := (nextP_spec P 400 q).1
    simp only [scanP, seqN_eq]
    cases Nat.beq (Nat.gcd (nextP P 400 q) P) 1
    · simp only [cond_false]
      have := ih (nextP P 400 q + 1) c p g u d
      omega
    · simp only [cond_true]
      have := ih (nextP P 400 q + 1) (c + 1) (nextP P 400 q) (nextP P 400 q - p)
        (cond (Nat.blt g (nextP P 400 q - p)) (u + 1) u)
        (cond (Nat.blt (nextP P 400 q - p) g) (d + 1) d)
      omega

theorem count_skip (q : ℕ) : ∀ k : ℕ, (∀ x, q ≤ x → x < q + k → ¬ x.Prime) →
    Nat.count Nat.Prime (q + k) = Nat.count Nat.Prime q := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [← Nat.add_assoc, Nat.count_succ, if_neg (h (q + k) (by omega) (by omega)), Nat.add_zero]
    exact ih (fun x h1 h2 => h x h1 (by omega))

theorem skip_inv (q q' c p g u d : ℕ) (hI : Inv (q, c, p, g, u, d)) (hle : q ≤ q')
    (h : ∀ x, q ≤ x → x < q' → ¬ x.Prime) : Inv (q', c, p, g, u, d) := by
  obtain ⟨hc, hcount, hnth, hg, ha⟩ := hI
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact ⟨hc, by rw [count_skip q k h]; exact hcount, hnth, hg, ha⟩

theorem scanP_inv (A B P : ℕ) (htest : ∀ x, A ≤ x → x < B * B → (Nat.gcd x P = 1 ↔ x.Prime)) :
    ∀ (n q c p g u d : ℕ), Inv (q, c, p, g, u, d) → A ≤ q →
      (scanP P n q c p g u d).1 ≤ B * B → Inv (scanP P n q c p g u d) := by
  intro n
  induction n with
  | zero => intro q c p g u d hI _ _; exact hI
  | succ n ih =>
    intro q c p g u d hI hA hfin
    obtain ⟨hle, hcomp⟩ := nextP_spec P 400 q
    simp only [scanP, seqN_eq] at hfin ⊢
    generalize nextP P 400 q = q' at hle hcomp hfin ⊢
    cases hb : Nat.beq (Nat.gcd q' P) 1
    · simp only [hb, cond_false] at hfin ⊢
      have hge := scanP_fst_ge P n (q' + 1) c p g u d
      have hlt : q' < B * B := by omega
      have I' : Inv (q', c, p, g, u, d) := skip_inv q q' c p g u d hI hle
        (fun x h1 h2 hp => hcomp x h1 h2 ((htest x (by omega) (by omega)).mpr hp))
      have I2 := step_inv P (q', c, p, g, u, d) I' (htest q' (by omega) hlt)
      simp only [step, hb, cond_false] at I2
      exact ih (q' + 1) c p g u d I2 (by omega) hfin
    · simp only [hb, cond_true] at hfin ⊢
      have hge := scanP_fst_ge P n (q' + 1) (c + 1) q' (q' - p)
        (cond (Nat.blt g (q' - p)) (u + 1) u) (cond (Nat.blt (q' - p) g) (d + 1) d)
      have hlt : q' < B * B := by omega
      have I' : Inv (q', c, p, g, u, d) := skip_inv q q' c p g u d hI hle
        (fun x h1 h2 hp => hcomp x h1 h2 ((htest x (by omega) (by omega)).mpr hp))
      have I2 := step_inv P (q', c, p, g, u, d) I' (htest q' (by omega) hlt)
      simp only [step, hb, cond_true] at I2
      exact ih (q' + 1) (c + 1) q' (q' - p) _ _ I2 (by omega) hfin

theorem chainP (A B P : ℕ) (htest : ∀ x, A ≤ x → x < B * B → (Nat.gcd x P = 1 ↔ x.Prime))
    (n q c p g u d : ℕ) (s' : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (h : scanP P n q c p g u d = s')
    (hI : Inv (q, c, p, g, u, d)) (hA : A ≤ q) (hfin : s'.1 ≤ B * B) : Inv s' := by
  subst h
  exact scanP_inv A B P htest n q c p g u d hI hA hfin

def L3 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251]
def P3 : ℕ := 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230
def L4 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913]
def P4 : ℕ := 330299814997665459752503875936311543658654867563977165754682006007076789023726298028755353475271999414453764134871401945863424316247498974525140884502213619463897242701793280976314619522940952707678656355866315555813453709146270396483864711972590100553162544989477344756108882470964672146103057849578011704570100638149372613055636349494040526380005363336573870322107486828807474961912982325253455883323020690855949007426633568611938908672810913185726817817735856245280443222830596087494005801000571579740438132076783124492309104396505888935213078665394872422903777412625904361394221872967927700481448076066485794738700362833072432132949703400435636025207134810624436376055618005498163855585536582182713434179261367383522239622181965584795602707040077669355630046755401445847804541645846120576194385396822416810

theorem test1 : ∀ q, 4 ≤ q → q < 4 * 4 → 2 ≤ q → (Nat.gcd q 6 = 1 ↔ q.Prime) :=
  gtest 4 6 [2, 3] (by decide) (by decide) (by decide)

theorem test2 : ∀ q, 16 ≤ q → q < 16 * 16 → 2 ≤ q → (Nat.gcd q 30030 = 1 ↔ q.Prime) :=
  gtest 16 30030 [2, 3, 5, 7, 11, 13] (by decide) (by decide) (by decide)

theorem div3a : ∀ r, r < 16 → r.Prime → r ∣ P3 := by decide +kernel

theorem div3b : ∀ r, r < 256 → 16 ≤ r → Nat.gcd r 30030 = 1 → r ∣ P3 := by decide +kernel

theorem div3 : ∀ r, r < 256 → r.Prime → r ∣ P3 := by
  intro r hr hp
  rcases Nat.lt_or_ge r 16 with h | h
  · exact div3a r h hp
  · exact div3b r hr h ((test2 r h (by omega) (by omega)).mpr hp)

theorem prod3 : L3.prod = P3 := by decide +kernel

theorem lt3 : ∀ l ∈ L3, 0 < l ∧ l < 256 := by decide +kernel

theorem test3 : ∀ q, 256 ≤ q → q < 256 * 256 → 2 ≤ q → (Nat.gcd q P3 = 1 ↔ q.Prime) :=
  gtest 256 P3 L3 prod3 lt3 div3

theorem dvd34 : P3 ∣ P4 := Nat.dvd_of_mod_eq_zero (by decide +kernel)

theorem div4b : ∀ r, r < 1915 → 256 ≤ r → Nat.gcd r P3 = 1 → r ∣ P4 := by decide +kernel

theorem div4 : ∀ r, r < 1915 → r.Prime → r ∣ P4 := by
  intro r hr hp
  rcases Nat.lt_or_ge r 256 with h | h
  · exact Nat.dvd_trans (div3 r h hp) dvd34
  · exact div4b r hr h ((test3 r h (by omega) (by omega)).mpr hp)

theorem prod4 : L4.prod = P4 := by decide +kernel

theorem lt4 : ∀ l ∈ L4, 0 < l ∧ l < 1915 := by decide +kernel

theorem test4 : ∀ q, 1915 ≤ q → q < 1915 * 1915 → 2 ≤ q → (Nat.gcd q P4 = 1 ↔ q.Prime) :=
  gtest 1915 P4 L4 prod4 lt4 div4

theorem test4' : ∀ x, 1915 ≤ x → x < 1915 * 1915 → (Nat.gcd x P4 = 1 ↔ x.Prime) :=
  fun x h1 h2 => test4 x h1 h2 (by omega)

theorem inv0 : Inv (4, 2, 3, 1, 0, 0) := by
  refine ⟨le_refl 2, by decide, Nat.nth_prime_one_eq_three, ?_, ?_⟩
  · unfold OeisA92243.primeGap
    rw [Nat.nth_prime_one_eq_three, Nat.nth_prime_zero_eq_two]
  · unfold OeisA92243.a
    simp

theorem i1 : Inv (16, 6, 13, 2, 2, 1) :=
  chain 4 6 test1 (by decide) 12 (4, 2, 3, 1, 0, 0) _ (by decide +kernel) inv0 (by decide) (by decide)

theorem i2 : Inv (256, 54, 251, 10, 25, 22) :=
  chain 16 30030 test2 (by decide) 240 (16, 6, 13, 2, 2, 1) _ (by decide +kernel) i1 (by decide) (by decide)

theorem i3 : Inv (1915, 293, 1913, 6, 139, 128) :=
  chain 256 P3 test3 (by decide) 1659 (256, 54, 251, 10, 25, 22) _ (by decide +kernel) i2 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i4 : Inv (51720, 5293, 51719, 6, 2536, 2502) :=
  chainP 1915 1915 P4 test4' 5000 1915 293 1913 6 139 128 _ (by decide +kernel) i3 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i5 : Inv (108194, 10293, 108193, 2, 4939, 4892) :=
  chainP 1915 1915 P4 test4' 5000 51720 5293 51719 6 2536 2502 _ (by decide +kernel) i4 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i6 : Inv (167414, 15293, 167413, 6, 7359, 7274) :=
  chainP 1915 1915 P4 test4' 5000 108194 10293 108193 2 4939 4892 _ (by decide +kernel) i5 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i7 : Inv (228420, 20293, 228419, 10, 9739, 9695) :=
  chainP 1915 1915 P4 test4' 5000 167414 15293 167413 6 7359 7274 _ (by decide +kernel) i6 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i8 : Inv (290804, 25293, 290803, 12, 12140, 12105) :=
  chainP 1915 1915 P4 test4' 5000 228420 20293 228419 10 9739 9695 _ (by decide +kernel) i7 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i9 : Inv (354018, 30293, 354017, 10, 14533, 14506) :=
  chainP 1915 1915 P4 test4' 5000 290804 25293 290803 12 12140 12105 _ (by decide +kernel) i8 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i10 : Inv (418794, 35293, 418793, 6, 16947, 16905) :=
  chainP 1915 1915 P4 test4' 5000 354018 30293 354017 10 14533 14506 _ (by decide +kernel) i9 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i11 : Inv (483710, 40293, 483709, 12, 19351, 19325) :=
  chainP 1915 1915 P4 test4' 5000 418794 35293 418793 6 16947 16905 _ (by decide +kernel) i10 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i12 : Inv (549608, 45293, 549607, 18, 21756, 21735) :=
  chainP 1915 1915 P4 test4' 5000 483710 40293 483709 12 19351 19325 _ (by decide +kernel) i11 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i13 : Inv (615800, 50293, 615799, 6, 24185, 24112) :=
  chainP 1915 1915 P4 test4' 5000 549608 45293 549607 18 21756 21735 _ (by decide +kernel) i12 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i14 : Inv (683150, 55293, 683149, 6, 26590, 26549) :=
  chainP 1915 1915 P4 test4' 5000 615800 50293 615799 6 24185 24112 _ (by decide +kernel) i13 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i15 : Inv (750798, 60293, 750797, 6, 28985, 28969) :=
  chainP 1915 1915 P4 test4' 5000 683150 55293 683149 6 26590 26549 _ (by decide +kernel) i14 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i16 : Inv (818328, 65293, 818327, 18, 31409, 31356) :=
  chainP 1915 1915 P4 test4' 5000 750798 60293 750797 6 28985 28969 _ (by decide +kernel) i15 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i17 : Inv (886422, 70293, 886421, 34, 33826, 33749) :=
  chainP 1915 1915 P4 test4' 5000 818328 65293 818327 18 31409 31356 _ (by decide +kernel) i16 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i18 : Inv (955310, 75293, 955309, 2, 36239, 36172) :=
  chainP 1915 1915 P4 test4' 5000 886422 70293 886421 34 33826 33749 _ (by decide +kernel) i17 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i19 : Inv (1024412, 80293, 1024411, 12, 38652, 38573) :=
  chainP 1915 1915 P4 test4' 5000 955310 75293 955309 2 36239 36172 _ (by decide +kernel) i18 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i20 : Inv (1094090, 85293, 1094089, 8, 41084, 40968) :=
  chainP 1915 1915 P4 test4' 5000 1024412 80293 1024411 12 38652 38573 _ (by decide +kernel) i19 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i21 : Inv (1163340, 90293, 1163339, 6, 43499, 43364) :=
  chainP 1915 1915 P4 test4' 5000 1094090 85293 1094089 8 41084 40968 _ (by decide +kernel) i20 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i22 : Inv (1233494, 95293, 1233493, 20, 45907, 45791) :=
  chainP 1915 1915 P4 test4' 5000 1163340 90293 1163339 6 43499 43364 _ (by decide +kernel) i21 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i23 : Inv (1303740, 100293, 1303739, 28, 48333, 48189) :=
  chainP 1915 1915 P4 test4' 5000 1233494 95293 1233493 20 45907 45791 _ (by decide +kernel) i22 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i24 : Inv (1374692, 105293, 1374691, 8, 50730, 50616) :=
  chainP 1915 1915 P4 test4' 5000 1303740 100293 1303739 28 48333 48189 _ (by decide +kernel) i23 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i25 : Inv (1445288, 110293, 1445287, 26, 53147, 53030) :=
  chainP 1915 1915 P4 test4' 5000 1374692 105293 1374691 8 50730 50616 _ (by decide +kernel) i24 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i26 : Inv (1515810, 115293, 1515809, 18, 55540, 55451) :=
  chainP 1915 1915 P4 test4' 5000 1445288 110293 1445287 26 53147 53030 _ (by decide +kernel) i25 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i27 : Inv (1587900, 120293, 1587899, 22, 57926, 57885) :=
  chainP 1915 1915 P4 test4' 5000 1515810 115293 1515809 18 55540 55451 _ (by decide +kernel) i26 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i28 : Inv (1659348, 125293, 1659347, 24, 60306, 60317) :=
  chainP 1915 1915 P4 test4' 5000 1587900 120293 1587899 22 57926 57885 _ (by decide +kernel) i27 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i29 : Inv (1731228, 130293, 1731227, 6, 62722, 62742) :=
  chainP 1915 1915 P4 test4' 5000 1659348 125293 1659347 24 60306 60317 _ (by decide +kernel) i28 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i30 : Inv (1803254, 135293, 1803253, 2, 65120, 65195) :=
  chainP 1915 1915 P4 test4' 5000 1731228 130293 1731227 6 62722 62742 _ (by decide +kernel) i29 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i31 : Inv (1875012, 140293, 1875011, 4, 67541, 67625) :=
  chainP 1915 1915 P4 test4' 5000 1803254 135293 1803253 2 65120 65195 _ (by decide +kernel) i30 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i32 : Inv (1946780, 145293, 1946779, 8, 69938, 70042) :=
  chainP 1915 1915 P4 test4' 5000 1875012 140293 1875011 4 67541 67625 _ (by decide +kernel) i31 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i33 : Inv (2019468, 150293, 2019467, 4, 72355, 72450) :=
  chainP 1915 1915 P4 test4' 5000 1946780 145293 1946779 8 69938 70042 _ (by decide +kernel) i32 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i34 : Inv (2092382, 155293, 2092381, 12, 74759, 74881) :=
  chainP 1915 1915 P4 test4' 5000 2019468 150293 2019467 4 72355 72450 _ (by decide +kernel) i33 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i35 : Inv (2164980, 160293, 2164979, 16, 77170, 77317) :=
  chainP 1915 1915 P4 test4' 5000 2092382 155293 2092381 12 74759 74881 _ (by decide +kernel) i34 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i36 : Inv (2238378, 165293, 2238377, 16, 79594, 79726) :=
  chainP 1915 1915 P4 test4' 5000 2164980 160293 2164979 16 77170 77317 _ (by decide +kernel) i35 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i37 : Inv (2311344, 170293, 2311343, 10, 82003, 82171) :=
  chainP 1915 1915 P4 test4' 5000 2238378 165293 2238377 16 79594 79726 _ (by decide +kernel) i36 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i38 : Inv (2385542, 175293, 2385541, 42, 84441, 84572) :=
  chainP 1915 1915 P4 test4' 5000 2311344 170293 2311343 10 82003 82171 _ (by decide +kernel) i37 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i39 : Inv (2458904, 180293, 2458903, 2, 86834, 86984) :=
  chainP 1915 1915 P4 test4' 5000 2385542 175293 2385541 42 84441 84572 _ (by decide +kernel) i38 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i40 : Inv (2532404, 185293, 2532403, 2, 89204, 89443) :=
  chainP 1915 1915 P4 test4' 5000 2458904 180293 2458903 2 86834 86984 _ (by decide +kernel) i39 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i41 : Inv (2606354, 190293, 2606353, 42, 91618, 91868) :=
  chainP 1915 1915 P4 test4' 5000 2532404 185293 2532403 2 89204 89443 _ (by decide +kernel) i40 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i42 : Inv (2680242, 195293, 2680241, 10, 94039, 94296) :=
  chainP 1915 1915 P4 test4' 5000 2606354 190293 2606353 42 91618 91868 _ (by decide +kernel) i41 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i43 : Inv (2754492, 200293, 2754491, 10, 96477, 96702) :=
  chainP 1915 1915 P4 test4' 5000 2680242 195293 2680241 10 94039 94296 _ (by decide +kernel) i42 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i44 : Inv (2828282, 205293, 2828281, 24, 98880, 99100) :=
  chainP 1915 1915 P4 test4' 5000 2754492 200293 2754491 10 96477 96702 _ (by decide +kernel) i43 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i45 : Inv (2902772, 210293, 2902771, 42, 101285, 101530) :=
  chainP 1915 1915 P4 test4' 5000 2828282 205293 2828281 24 98880 99100 _ (by decide +kernel) i44 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i46 : Inv (2977550, 215293, 2977549, 12, 103708, 103943) :=
  chainP 1915 1915 P4 test4' 5000 2902772 210293 2902771 42 101285 101530 _ (by decide +kernel) i45 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i47 : Inv (3052452, 220293, 3052451, 4, 106159, 106350) :=
  chainP 1915 1915 P4 test4' 5000 2977550 215293 2977549 12 103708 103943 _ (by decide +kernel) i46 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i48 : Inv (3126822, 225293, 3126821, 18, 108584, 108769) :=
  chainP 1915 1915 P4 test4' 5000 3052452 220293 3052451 4 106159 106350 _ (by decide +kernel) i47 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i49 : Inv (3201132, 230293, 3201131, 18, 111018, 111173) :=
  chainP 1915 1915 P4 test4' 5000 3126822 225293 3126821 18 108584 108769 _ (by decide +kernel) i48 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i50 : Inv (3275708, 235293, 3275707, 14, 113422, 113621) :=
  chainP 1915 1915 P4 test4' 5000 3201132 230293 3201131 18 111018 111173 _ (by decide +kernel) i49 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i51 : Inv (3350952, 240293, 3350951, 22, 115865, 116016) :=
  chainP 1915 1915 P4 test4' 5000 3275708 235293 3275707 14 113422 113621 _ (by decide +kernel) i50 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i52 : Inv (3426120, 245293, 3426119, 6, 118273, 118454) :=
  chainP 1915 1915 P4 test4' 5000 3350952 240293 3350951 22 115865 116016 _ (by decide +kernel) i51 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i53 : Inv (3502364, 250293, 3502363, 26, 120723, 120854) :=
  chainP 1915 1915 P4 test4' 5000 3426120 245293 3426119 6 118273 118454 _ (by decide +kernel) i52 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i54 : Inv (3578384, 255293, 3578383, 24, 123165, 123258) :=
  chainP 1915 1915 P4 test4' 5000 3502364 250293 3502363 26 120723 120854 _ (by decide +kernel) i53 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i55 : Inv (3653762, 260293, 3653761, 24, 125617, 125639) :=
  chainP 1915 1915 P4 test4' 5000 3578384 255293 3578383 24 123165 123258 _ (by decide +kernel) i54 (by decide) (by decide)

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 0 in
theorem i56 : Inv (3666582, 261151, 3666581, 42, 126044, 126043) :=
  chainP 1915 1915 P4 test4' 858 3653762 260293 3653761 24 125617 125639 _ (by decide +kernel) i55 (by decide) (by decide)

end OMA

theorem OMA.solution : type_of% @OeisA92243.conjecture1 := by
  obtain ⟨-, -, -, -, ha⟩ := OMA.i56
  refine ⟨261150, by norm_num, ?_⟩
  have h : OeisA92243.a 261150 = ((126044 : ℕ) : ℤ) - ((126043 : ℕ) : ℤ) := ha
  rw [h]
  norm_num
