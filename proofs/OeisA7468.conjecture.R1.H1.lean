import OMAReductions.R_OeisA7468_conjecture_R1

/-!
# Square rows among the first 100 rows of the prime triangle

For each row, count the primes in its interval and add them. The counting
invariant identifies those primes with the indexed primes in OEIS A007468.
The only square row sum in this range is 207936 at row 38.
-/

namespace PrimeTriangleCheck

def trialPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
   71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
   151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223]

abbrev passes (m : ℕ) : Prop :=
  2 ≤ m ∧ ∀ d ∈ trialPrimes, d = m ∨ m % d ≠ 0

lemma trial_complete : ∀ i : Fin 224, i.val.Prime → i.val ∈ trialPrimes := by
  decide +kernel

lemma trial_correct (m : ℕ) (hm : m < 50000) : passes m ↔ m.Prime := by
  constructor
  · rintro ⟨hm2, h⟩
    by_contra hc
    have hs := Nat.minFac_sq_le_self (by omega : 0 < m) hc
    rw [pow_two] at hs
    have hb : m.minFac < 224 := by
      by_contra! hge
      have hh : 224 * 224 ≤ m.minFac * m.minFac := Nat.mul_le_mul hge hge
      omega
    have hp := Nat.minFac_prime (by omega : m ≠ 1)
    rcases h _ (trial_complete ⟨_, hb⟩ hp) with heq | hn
    · exact hc (heq ▸ hp)
    · exact hn (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd m))
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    intro d hd
    by_cases hmod : m % d = 0
    · apply Or.inl
      have hd2 : 2 ≤ d := by
        have hall : ∀ t ∈ trialPrimes, 2 ≤ t := by decide
        exact hall d hd
      exact (Nat.dvd_prime_two_le hp hd2).1 (Nat.dvd_of_mod_eq_zero hmod)
    · exact Or.inr hmod

/-- Count and sum the primes in the half-open interval starting at lo. -/
def tally (lo : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | len + 1 =>
    let prev := tally lo len
    if passes (lo + len) then (prev.1 + 1, prev.2 + (lo + len)) else prev

lemma tally_spec (lo len : ℕ) (hb : lo + len ≤ 50000) :
    Nat.count Nat.Prime (lo + len) = Nat.count Nat.Prime lo + (tally lo len).1 ∧
    (∑ i ∈ Finset.range (tally lo len).1, Nat.nth Nat.Prime (Nat.count Nat.Prime lo + i))
      = (tally lo len).2 := by
  induction len with
  | zero => simp [tally]
  | succ len ih =>
    obtain ⟨hcount, hsum⟩ := ih (by omega)
    have ht := trial_correct (lo + len) (by omega)
    by_cases hp : (lo + len).Prime
    · simp only [tally, if_pos (ht.2 hp), Nat.add_succ, Nat.count_succ, if_pos hp,
        Finset.sum_range_succ, hsum, ← hcount, Nat.nth_count hp]
      exact ⟨trivial, trivial⟩
    · simp only [tally, if_neg (fun h => hp (ht.1 h)), Nat.add_succ, Nat.count_succ,
        if_neg hp, Nat.add_zero, hcount, hsum, and_self]

/-- Each certified interval must contain exactly one row's primes.
The square test uses the integer square root, so all comparisons are exact. -/
def rowsPass (row lo : ℕ) : List ℕ → Bool
  | [] => true
  | w :: ws =>
    let t := tally lo w
    decide (lo + w ≤ 50000 ∧ t.1 = row ∧ (row = 38 ∨ t.2.sqrt * t.2.sqrt ≠ t.2))
      && rowsPass (row + 1) (lo + w) ws

lemma next_start (r : ℕ) : (r + 1) * ((r + 1) - 1) / 2 = r * (r - 1) / 2 + r := by
  cases r with
  | zero => decide
  | succ k =>
    simp only [Nat.succ_sub_one, Nat.succ_mul, Nat.mul_succ]
    omega

lemma rows_sound (ws : List ℕ) (row lo : ℕ)
    (hstart : Nat.count Nat.Prime lo = row * (row - 1) / 2)
    (hok : rowsPass row lo ws = true) :
    ∀ n : ℕ, row ≤ n → n < row + ws.length → IsSquare (OeisA7468.a n) → n = 38 := by
  induction ws generalizing row lo with
  | nil =>
    intro n hlo hhi
    simp only [List.length_nil, Nat.add_zero] at hhi
    omega
  | cons w ws ih =>
    simp only [rowsPass, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hb, hcard, htest⟩, hrest⟩ := hok
    obtain ⟨hc, hs⟩ := tally_spec lo w hb
    rw [hstart, hcard] at hc hs
    intro n hlow hhigh hsq
    by_cases heq : n = row
    · subst n
      change IsSquare (∑ i ∈ Finset.range row, Nat.nth Nat.Prime (row * (row - 1) / 2 + i)) at hsq
      rw [hs] at hsq
      obtain ⟨x, hx⟩ := hsq
      rcases htest with h | h
      · exact h
      · exact False.elim (h (by rw [hx, Nat.sqrt_eq]))
    · have hnext : Nat.count Nat.Prime (lo + w) = (row + 1) * ((row + 1) - 1) / 2 := by
        rw [next_start, hc]
      apply ih (row + 1) (lo + w) hnext hrest n (by omega) _ hsq
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhigh

lemma rows_append (xs ys : List ℕ) (row lo : ℕ) :
    rowsPass row lo (xs ++ ys) =
      (rowsPass row lo xs && rowsPass (row + xs.length) (lo + xs.sum) ys) := by
  induction xs generalizing row lo with
  | nil => simp [rowsPass]
  | cons x xs ih =>
    simp [rowsPass, ih, Bool.and_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/- Each list gives the widths of five consecutive intervals, starting at the
next unexamined integer. Small chunks bound the kernel memory needed. -/

def widths1to5 : List ℕ := [3, 3, 8, 16, 18]

set_option maxRecDepth 2048 in
lemma widths1to5_checked : rowsPass 1 0 widths1to5 = true := by
  decide +kernel

def widths6to10 : List ℕ := [26, 34, 44, 46, 60]

set_option maxRecDepth 2048 in
lemma widths6to10_checked : rowsPass 6 48 widths6to10 = true := by
  decide +kernel

def widths11to15 : List ℕ := [60, 80, 70, 104, 88]

set_option maxRecDepth 2048 in
lemma widths11to15_checked : rowsPass 11 258 widths11to15 = true := by
  decide +kernel

def widths16to20 : List ℕ := [110, 114, 136, 132, 140]

set_option maxRecDepth 2048 in
lemma widths16to20_checked : rowsPass 16 660 widths16to20 = true := by
  decide +kernel

def widths21to25 : List ℕ := [162, 154, 176, 204, 166]

set_option maxRecDepth 2048 in
lemma widths21to25_checked : rowsPass 21 1292 widths21to25 = true := by
  decide +kernel

def widths26to30 : List ℕ := [218, 222, 198, 246, 270]

set_option maxRecDepth 2048 in
lemma widths26to30_checked : rowsPass 26 2154 widths26to30 = true := by
  decide +kernel

def widths31to35 : List ℕ := [234, 256, 276, 284, 300]

set_option maxRecDepth 2048 in
lemma widths31to35_checked : rowsPass 31 3308 widths31to35 = true := by
  decide +kernel

def widths36to40 : List ℕ := [316, 330, 338, 298, 362]

set_option maxRecDepth 2048 in
lemma widths36to40_checked : rowsPass 36 4658 widths36to40 = true := by
  decide +kernel

def widths41to45 : List ℕ := [378, 340, 458, 352, 414]

set_option maxRecDepth 2048 in
lemma widths41to45_checked : rowsPass 41 6302 widths41to45 = true := by
  decide +kernel

def widths46to50 : List ℕ := [438, 410, 400, 440, 496]

set_option maxRecDepth 2048 in
lemma widths46to50_checked : rowsPass 46 8244 widths46to50 = true := by
  decide +kernel

def widths51to55 : List ℕ := [476, 520, 516, 498, 486]

set_option maxRecDepth 2048 in
lemma widths51to55_checked : rowsPass 51 10428 widths51to55 = true := by
  decide +kernel

def widths56to60 : List ℕ := [540, 546, 612, 528, 530]

set_option maxRecDepth 2048 in
lemma widths56to60_checked : rowsPass 56 12924 widths56to60 = true := by
  decide +kernel

def widths61to65 : List ℕ := [594, 658, 588, 624, 654]

set_option maxRecDepth 2048 in
lemma widths61to65_checked : rowsPass 61 15680 widths61to65 = true := by
  decide +kernel

def widths66to70 : List ℕ := [686, 660, 714, 664, 636]

set_option maxRecDepth 2048 in
lemma widths66to70_checked : rowsPass 66 18798 widths66to70 = true := by
  decide +kernel

def widths71to75 : List ℕ := [744, 722, 694, 830, 766]

set_option maxRecDepth 2048 in
lemma widths71to75_checked : rowsPass 71 22158 widths71to75 = true := by
  decide +kernel

def widths76to80 : List ℕ := [774, 794, 808, 770, 862]

set_option maxRecDepth 2048 in
lemma widths76to80_checked : rowsPass 76 25914 widths76to80 = true := by
  decide +kernel

def widths81to85 : List ℕ := [888, 834, 848, 852, 870]

set_option maxRecDepth 2048 in
lemma widths81to85_checked : rowsPass 81 29922 widths81to85 = true := by
  decide +kernel

def widths86to90 : List ℕ := [876, 928, 906, 948, 996]

set_option maxRecDepth 2048 in
lemma widths86to90_checked : rowsPass 86 34214 widths86to90 = true := by
  decide +kernel

def widths91to95 : List ℕ := [962, 1020, 960, 894, 1080]

set_option maxRecDepth 2048 in
lemma widths91to95_checked : rowsPass 91 38868 widths91to95 = true := by
  decide +kernel

def widths96to100 : List ℕ := [1014, 1090, 1110, 1052, 1074]

set_option maxRecDepth 2048 in
lemma widths96to100_checked : rowsPass 96 43784 widths96to100 = true := by
  decide +kernel

def widths : List ℕ :=
  widths1to5 ++ widths6to10 ++ widths11to15 ++ widths16to20 ++ widths21to25 ++ widths26to30 ++
  widths31to35 ++ widths36to40 ++ widths41to45 ++ widths46to50 ++ widths51to55 ++ widths56to60
  ++ widths61to65 ++ widths66to70 ++ widths71to75 ++ widths76to80 ++ widths81to85 ++
  widths86to90 ++ widths91to95 ++ widths96to100

lemma widths_checked : rowsPass 1 0 widths = true := by
  unfold widths
  simp only [List.append_assoc]
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths1to5_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths6to10_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths11to15_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths16to20_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths21to25_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths26to30_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths31to35_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths36to40_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths41to45_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths46to50_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths51to55_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths56to60_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths61to65_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths66to70_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths71to75_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths76to80_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths81to85_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths86to90_checked, ?_⟩
  rw [rows_append, Bool.and_eq_true]
  refine ⟨widths91to95_checked, ?_⟩
  exact widths96to100_checked

theorem finite_rows : ∀ n : ℕ, 0 < n → n ≤ 100 → IsSquare (OeisA7468.a n) → n = 38 := by
  intro n hpos hn
  exact rows_sound widths 1 0 (by decide) widths_checked n hpos (by
    change n < 101
    omega)

end PrimeTriangleCheck

theorem OMA.solution : OMA.R_OeisA7468_conjecture_R1.H1 := by
  exact PrimeTriangleCheck.finite_rows
