import FormalConjectures.GreensOpenProblems.«15»

/-
Own proof, following the idea (not the code) of a published argument: a six-letter 4-uniform
substitution, a base-3 tag making the three endpoint letters equal, and a finite invariant checked
by kernel reduction. It excludes 3-term progressions in the graph, hence 4-term ones.
-/

-- Problem: Green 15, 4-term progressions
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Green15Solution

open scoped NNReal

def HL : List (List ℕ) := [[0,2,0,1],[0,4,0,1],[0,2,5,1],[5,4,0,3],[5,2,5,3],[5,4,5,3]]
def BL : List (List ℤ) := [[0,-3,-4,-7],[0,-3,-1,-4],[0,-3,-4,-1],[0,3,5,2],[0,3,2,5],[0,3,5,8]]
def WL : List ℤ := [0,1,2,4,5,6]
def QL : List ℤ := [0,1,3,4,9,10]

def hh (a x : ℕ) : ℕ := (HL.getD a []).getD x 0
def bb (a x : ℕ) : ℤ := (BL.getD a []).getD x 0
def ww (a : ℕ) : ℤ := WL.getD a 0
def qq (a : ℕ) : ℤ := QL.getD a 0

def letter (n : ℕ) : ℕ :=
  if h : n = 0 then 5 else hh (letter (n / 4)) (n % 4)
termination_by n
decreasing_by omega

def gg (n : ℕ) : ℤ :=
  if h : n = 0 then 0 else 3 * gg (n / 4) + bb (letter (n / 4)) (n % 4)
termination_by n
decreasing_by omega

lemma letter_zero : letter 0 = 5 := by rw [letter]; simp
lemma gg_zero : gg 0 = 0 := by rw [gg]; simp

lemma letter_div_mod (n : ℕ) : letter n = if n = 0 then 5 else hh (letter (n / 4)) (n % 4) := by
  rw [letter]; split_ifs <;> simp_all

lemma letter_four (m j : ℕ) (hj : j < 4) : letter (4 * m + j) = hh (letter m) j := by
  rcases Nat.eq_zero_or_pos (4 * m + j) with h | h
  · have hm : m = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hm; subst hj0
    simp [letter_zero, hh, HL]
  · have h1 : 4 * m + j ≠ 0 := by omega
    have h2 : (4 * m + j) / 4 = m := by omega
    have h3 : (4 * m + j) % 4 = j := by omega
    rw [letter, dif_neg h1, h2, h3]

lemma gg_four (m j : ℕ) (hj : j < 4) : gg (4 * m + j) = 3 * gg m + bb (letter m) j := by
  rcases Nat.eq_zero_or_pos (4 * m + j) with h | h
  · have hm : m = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hm; subst hj0
    simp [gg_zero, letter_zero, bb, BL]
  · have h1 : 4 * m + j ≠ 0 := by omega
    have h2 : (4 * m + j) / 4 = m := by omega
    have h3 : (4 * m + j) % 4 = j := by omega
    rw [gg, dif_neg h1, h2, h3]

lemma hh_lt : ∀ a < 6, ∀ x < 4, hh a x < 6 := by decide
lemma bb_range : ∀ a < 6, ∀ x < 4, -7 ≤ bb a x ∧ bb a x ≤ 8 := by decide
lemma bb_step : ∀ a < 6, ∀ x < 3, bb a (x + 1) - bb a x = ww (hh a x) - 3 := by decide
lemma bb_last : ∀ a < 6, ∀ x < 4, hh a x < 6 ∧ bb a 3 = 3 * ww a - 9 - ww (hh a 3) + 3 := by
  decide
lemma bb_zero : ∀ a < 6, bb a 0 = 0 := by decide

lemma letter_lt (n : ℕ) : letter n < 6 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨m, j, hj, rfl⟩ : ∃ m j, j < 4 ∧ n = 4 * m + j := ⟨n / 4, n % 4, by omega, by omega⟩
    rw [letter_four m j hj]
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; rw [letter_zero]; exact hh_lt 5 (by norm_num) j hj
    · exact hh_lt _ (ih m (by omega)) j hj

lemma gg_succ (n : ℕ) : gg (n + 1) - gg n = ww (letter n) - 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨m, j, hj, rfl⟩ : ∃ m j, j < 4 ∧ n = 4 * m + j := ⟨n / 4, n % 4, by omega, by omega⟩
    have hl := letter_lt m
    rcases (show j < 3 ∨ j = 3 by omega) with h3 | h3
    · have e : 4 * m + j + 1 = 4 * m + (j + 1) := by ring
      rw [e, gg_four m (j+1) (by omega), gg_four m j hj, letter_four m j hj]
      have := bb_step (letter m) hl j h3
      linarith
    · subst h3
      have e : 4 * m + 3 + 1 = 4 * (m + 1) + 0 := by ring
      rw [e, gg_four (m+1) 0 (by omega), gg_four m 3 (by omega), letter_four m 3 (by omega)]
      have hm : gg (m+1) - gg m = ww (letter m) - 3 := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp [gg_zero, letter_zero, ww, WL]
          rw [show gg 1 = 3 * gg 0 + bb (letter 0) 1 by simpa using gg_four 0 1 (by omega)]
          simp [gg_zero, letter_zero, bb, BL]
        · exact ih m (by omega)
      have h1 := (bb_last (letter m) hl 3 (by norm_num)).2
      have h0 := bb_zero (letter m) hl
      have h0' := bb_zero (letter (m+1)) (letter_lt _)
      rw [h0'] ; linarith

def ff (n : ℕ) : ℤ := 21 * (gg n + 3 * n) + qq (letter n) - 10

lemma qq_range : ∀ a < 6, 0 ≤ qq a ∧ qq a ≤ 10 := by decide
lemma ww_range : ∀ a < 6, 0 ≤ ww a ∧ ww a ≤ 6 := by decide

lemma ff_step (n : ℕ) : |ff (n + 1) - ff n| ≤ 136 := by
  have h := gg_succ n
  have e1 := qq_range _ (letter_lt (n+1))
  have e2 := qq_range _ (letter_lt n)
  have e3 := ww_range _ (letter_lt n)
  unfold ff
  rw [abs_le]
  push_cast
  constructor <;> nlinarith

lemma ff_lip (m d : ℕ) : |ff (m + d) - ff m| ≤ 136 * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have := ff_step (m + d)
    rw [show m + (d+1) = m + d + 1 by ring]
    push_cast
    calc |ff (m + d + 1) - ff m| = |(ff (m+d+1) - ff (m+d)) + (ff (m+d) - ff m)| := by ring_nf
      _ ≤ |ff (m+d+1) - ff (m+d)| + |ff (m+d) - ff m| := abs_add_le _ _
      _ ≤ 136 * (d+1) := by linarith

lemma ff_lip_int (x y : ℕ) : |ff x - ff y| ≤ 136 * |(x : ℤ) - y| := by
  rcases le_total x y with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have := ff_lip x d
    rw [abs_sub_comm]
    have e : |((x : ℤ)) - ((x + d : ℕ) : ℤ)| = d := by
      rw [abs_sub_comm]; push_cast; rw [abs_of_nonneg (by omega)]; omega
    rw [e]; exact_mod_cast this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have := ff_lip y d
    have e : |((y + d : ℕ) : ℤ) - (y : ℤ)| = d := by
      push_cast; rw [abs_of_nonneg (by omega)]; omega
    rw [e]; exact_mod_cast this

lemma ff_lipschitz : LipschitzWith 136 ff := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Int.dist_eq, Nat.dist_eq]
  have := ff_lip_int x y
  have h2 : ((|ff x - ff y| : ℤ) : ℝ) ≤ ((136 * |(x : ℤ) - y| : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at h2
  simpa using h2

/- The finite invariant -/

def TT : ℕ := 0x1fffdfffc00000006db6db6d00000000db6db6dadb6db6d800000006db6db6db6db6db4000000036db6db6b6db6db600000001b6db6db00000000fffffffe0000000000000002492492400000000924924900000000492492494924924800000000924924924924924000000012492492524924920000000024924924000000012492492000000000000000049249248000000012492492000000009249249092492490000000092492492492492480000000249249242492492400000002492492480000000249249240000000000000002492492400000000924924900000000492492494924924800000000924924924924924000000012492492524924920000000024924924000000012492492000000000000000049249248000000012492492000000009249249092492490000000092492492492492480000000249249242492492400000002492492480000000249249240000000000000007fffffff00000001b6db6db4000000036db6db6b6db6db600000001b6db6db6db6db6d00000000db6db6dadb6db6d800000006db6db6c00000003fffffff80000000db6db6da00000001b6db6db000000000000000000000000000000036db6db6000000000000000000000000000000000000000db6db6d800000006db6db6d00000000db6db6d92492492000000009249249200000002492092480000000000000000000000000000000000000092492492000000000000000000000000000000092492490000000049249249249249240000000124924920000000049249248000000000000000000000000000000000000001249249200000000000000000000000000000001249249200000000924924912492492000000009249249200000002492492480000000000000000000000000000000000000092492492000000000000000000000000000000092492490000000049249249249249240000000124924920000000049249248000000000000000000000000000000000000001249249200000000000000000000000000000001249249200000000924924936db6db6800000006db6db6c0000000000000000000000000000000db6db6d80000000000000000000000000000000000000036db6db600000001b6db6db4000000036db6db6b6db6db600000001b6db6db000000006db6db6c000000000000000000000000000000000000001b6db6db00000000000000000000000000000005b6db6db00000000db6db6d9249249200000000249249240000000000000000000000000000000492492480000000000000000000000000000000000000012492492000000009249249000000001249249224924924000000024924924800000000000000000000000000000049241249000000000000000000000000000000000000001249249240000000124924920000000124924925249249200000000249249240000000000000000000000000000000492492480000000000000000000000000000000000000012492492000000009249249000000001249249224924924000000024924924800000000000000000000000000000049249249000000000000000000000000000000000000001249249240000000124924920000000124924926db6db6d800000006db6db6c00000001b6db6db0000000000000000000000000000000000000006db6db6c00000000000000000000000000000016db6db6c000000036db6db6db6db6da00000001b6db6db000000000000000000000000000000036db6db6000000000000000000000000000000000000000db6db6d800000006db6db6d00000000db6db6d92492492000000009249249200000002492492480000000000000000000000000000000000000092492492000000000000000000000000000000092492490000000049249249249249240000000124924920000000049249248000000000000000000000000000000000000001249249200000000000000000000000000000001249249200000000924924912492492000000009249249200000002492492480000000000000000000000000000000000000092482492000000000000000000000000000000092492490000000049249249249249240000000124924920000000049249248000000000000000000000000000000000000001249249200000000000000000000000000000001249249200000000924924936db6db6800000006db6db6c0000000000000000000000000000000db6db6d80000000000000000000000000000000000000036db6db600000001b6db6db4000000036db6db6b6db6db600000001b6db6db000000006db6db6c000000000000000000000000000000000000001b6db6db00000000000000000000000000000005b6db6db00000000db6db6d9249249200000000249249240000000000000000000000000000000492492480000000000000000000000000000000000000012492492000000009249249000000001249249224924924000000024924924800000000000000000000000000000049249249000000000000000000000000000000000000001249249240000000124924920000000124924925249249200000000249249240000000000000000000000000000000492492480000000000000000000000000000000000000012492492000000009249249000000001249249224924924000000024924924800000000000000000000000000000049249249000000000000000000000000000000000000001249049240000000124924920000000124924926db6db6d800000006db6db6c00000001b6db6db0000000000000000000000000000000000000006db6db6c00000000000000000000000000000016db6db6c000000036db6db600000001fffffffc00000006db6db6d00000000db6db6dadb6db6d800000006db6db6db6db6db4000000036db6db6b6db6db600000001b6db6db00000000fffffffe0000000000000002492492400000000924924900000000492492494924924800000000924924924924924000000012492492524924920000000024924924000000012492492000000000000000049249248000000012492492000000009249249092492490000000092492492492492480000000249249242492492400000002492492480000000249249240000000000000002492492400000000924924900000000492492494924924800000000924924924924924000000012492492524924920000000024924924000000012492492000000000000000049249248000000012492492000000009249249092492490000000092492492492492480000000249249242492492400000002492492480000000249249240000000000000007fffffff00000001b6db6db4000000036db6db6b6db6db600000001b6db6db6db6db6d00000000db6db6dadb6db6d800000006db6db6c00000003fffbfff80000000

def memB (a b c : ℕ) (A D : ℤ) : Bool :=
  (TT >>> ((((a * 6 + b) * 6 + c) * 3 + (A + 1).toNat) * 31 + (D + 15).toNat)) % 2 == 1

def Step (a b c u v : ℕ) : Prop :=
  memB a b c ((u : ℤ) - 1) ((v : ℤ) - 15) = true →
    ∀ x : ℕ, x < 4 → ∀ y : ℕ, y < 4 → ∀ z : ℕ, z < 4 →
      (-1 ≤ 4 * ((u : ℤ) - 1) + x - 2 * y + z ∧ 4 * ((u : ℤ) - 1) + x - 2 * y + z ≤ 1 ∧
        -15 ≤ 3 * ((v : ℤ) - 15) + bb a x - 2 * bb b y + bb c z ∧
        3 * ((v : ℤ) - 15) + bb a x - 2 * bb b y + bb c z ≤ 15) →
      memB (hh a x) (hh b y) (hh c z) (4 * ((u : ℤ) - 1) + x - 2 * y + z)
        (3 * ((v : ℤ) - 15) + bb a x - 2 * bb b y + bb c z) = true

instance (a b c u v : ℕ) : Decidable (Step a b c u v) := by unfold Step; infer_instance

lemma closure_ok : ∀ a : ℕ, a < 6 → ∀ b : ℕ, b < 6 → ∀ c : ℕ, c < 6 → ∀ u : ℕ, u < 3 →
    ∀ v : ℕ, v < 31 → Step a b c u v := by
  decide +kernel

def Seed (a x y z : ℕ) : Prop :=
  ¬ (x = y ∧ y = z) →
    (-1 ≤ (x : ℤ) - 2 * y + z ∧ (x : ℤ) - 2 * y + z ≤ 1 ∧
      -15 ≤ bb a x - 2 * bb a y + bb a z ∧ bb a x - 2 * bb a y + bb a z ≤ 15) →
    memB (hh a x) (hh a y) (hh a z) ((x : ℤ) - 2 * y + z) (bb a x - 2 * bb a y + bb a z) = true

instance (a x y z : ℕ) : Decidable (Seed a x y z) := by unfold Seed; infer_instance

lemma seed_ok : ∀ a : ℕ, a < 6 → ∀ x : ℕ, x < 4 → ∀ y : ℕ, y < 4 → ∀ z : ℕ, z < 4 →
    Seed a x y z := by
  decide +kernel

lemma forbidden_ok : ∀ a : ℕ, a < 6 → memB a a a 0 0 = false := by
  decide +kernel


lemma closure_int (a b c : ℕ) (ha : a < 6) (hb : b < 6) (hc : c < 6) (A D : ℤ)
    (hA1 : -1 ≤ A) (hA2 : A ≤ 1) (hD1 : -15 ≤ D) (hD2 : D ≤ 15)
    (hm : memB a b c A D = true) (x y z : ℕ) (hx : x < 4) (hy : y < 4) (hz : z < 4)
    (hb1 : -1 ≤ 4 * A + x - 2 * y + z) (hb2 : 4 * A + x - 2 * y + z ≤ 1)
    (hb3 : -15 ≤ 3 * D + bb a x - 2 * bb b y + bb c z)
    (hb4 : 3 * D + bb a x - 2 * bb b y + bb c z ≤ 15) :
    memB (hh a x) (hh b y) (hh c z) (4 * A + x - 2 * y + z)
      (3 * D + bb a x - 2 * bb b y + bb c z) = true := by
  obtain ⟨u, hu, rfl⟩ : ∃ u : ℕ, u < 3 ∧ A = (u : ℤ) - 1 := ⟨(A + 1).toNat, by omega, by omega⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℕ, v < 31 ∧ D = (v : ℤ) - 15 := ⟨(D + 15).toNat, by omega, by omega⟩
  exact closure_ok a ha b hb c hc u hu v hv hm x hx y hy z hz ⟨hb1, hb2, hb3, hb4⟩

lemma inv_all : ∀ s n m k : ℕ, n + m + k = s → ¬ (n = m ∧ m = k) →
    -1 ≤ (n : ℤ) - 2 * m + k → (n : ℤ) - 2 * m + k ≤ 1 →
    -15 ≤ gg n - 2 * gg m + gg k → gg n - 2 * gg m + gg k ≤ 15 →
    memB (letter n) (letter m) (letter k) ((n : ℤ) - 2 * m + k) (gg n - 2 * gg m + gg k) = true := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro n m k hs hne hA1 hA2 hD1 hD2
    obtain ⟨n', x, hx, rfl⟩ : ∃ n' x, x < 4 ∧ n = 4 * n' + x := ⟨n / 4, n % 4, by omega, by omega⟩
    obtain ⟨m', y, hy, rfl⟩ : ∃ m' y, y < 4 ∧ m = 4 * m' + y := ⟨m / 4, m % 4, by omega, by omega⟩
    obtain ⟨k', z, hz, rfl⟩ : ∃ k' z, z < 4 ∧ k = 4 * k' + z := ⟨k / 4, k % 4, by omega, by omega⟩
    rw [letter_four n' x hx, letter_four m' y hy, letter_four k' z hz, gg_four n' x hx,
      gg_four m' y hy, gg_four k' z hz]
    have ln := letter_lt n'
    have lm := letter_lt m'
    have lk := letter_lt k'
    have bx := bb_range _ ln x hx
    have by' := bb_range _ lm y hy
    have bz := bb_range _ lk z hz
    have eA : (((4 * n' + x : ℕ) : ℤ) - 2 * ((4 * m' + y : ℕ) : ℤ) + ((4 * k' + z : ℕ) : ℤ)) =
        4 * ((n' : ℤ) - 2 * m' + k') + x - 2 * y + z := by push_cast; ring
    have eD : (3 * gg n' + bb (letter n') x - 2 * (3 * gg m' + bb (letter m') y) +
        (3 * gg k' + bb (letter k') z)) =
        3 * (gg n' - 2 * gg m' + gg k') + bb (letter n') x - 2 * bb (letter m') y +
          bb (letter k') z := by ring
    rw [eA, eD]
    rw [eA] at hA1 hA2
    rw [gg_four n' x hx, gg_four m' y hy, gg_four k' z hz] at hD1 hD2
    rw [eD] at hD1 hD2
    have hA'1 : -1 ≤ (n' : ℤ) - 2 * m' + k' := by omega
    have hA'2 : (n' : ℤ) - 2 * m' + k' ≤ 1 := by omega
    have hD'1 : -15 ≤ gg n' - 2 * gg m' + gg k' := by omega
    have hD'2 : gg n' - 2 * gg m' + gg k' ≤ 15 := by omega
    by_cases hq : n' = m' ∧ m' = k'
    · obtain ⟨rfl, rfl⟩ := hq
      have hxyz : ¬ (x = y ∧ y = z) := by
        intro h; apply hne; omega
      have h0 : (n' : ℤ) - 2 * n' + n' = 0 := by ring
      have h0' : gg n' - 2 * gg n' + gg n' = 0 := by ring
      rw [h0, h0']
      have := seed_ok (letter n') ln x hx y hy z hz hxyz
        ⟨by omega, by omega, by omega, by omega⟩
      simpa using this
    · have hpos : n' + m' + k' < s := by
        have : 0 < n' + m' + k' := by
          by_contra h0
          apply hq; omega
        omega
      have hinv := ih (n' + m' + k') hpos n' m' k' rfl hq hA'1 hA'2 hD'1 hD'2
      exact closure_int _ _ _ ln lm lk _ _ hA'1 hA'2 hD'1 hD'2 hinv x y z hx hy hz hA1 hA2 hD1 hD2

lemma qq_inj : ∀ a : ℕ, a < 6 → ∀ b : ℕ, b < 6 → ∀ c : ℕ, c < 6 →
    qq a - 2 * qq b + qq c = 0 → a = b ∧ b = c := by decide

lemma ap3 (i j k : ℕ) (h : (i : ℤ) + k = 2 * j) (hf : ff i + ff k = 2 * ff j) : i = j ∧ j = k := by
  have e1 := qq_range _ (letter_lt i)
  have e2 := qq_range _ (letter_lt j)
  have e3 := qq_range _ (letter_lt k)
  unfold ff at hf
  have hD : gg i - 2 * gg j + gg k = 0 := by omega
  have hT : qq (letter i) - 2 * qq (letter j) + qq (letter k) = 0 := by omega
  obtain ⟨h1, h2⟩ := qq_inj _ (letter_lt i) _ (letter_lt j) _ (letter_lt k) hT
  by_contra hne
  have := inv_all (i + j + k) i j k rfl hne (by omega) (by omega) (by omega) (by omega)
  have hA : (i : ℤ) - 2 * j + k = 0 := by omega
  rw [hA, hD, h1, ← h2] at this
  rw [forbidden_ok _ (letter_lt j)] at this
  simp at this

lemma main : ∃ K : ℝ≥0, ∃ f : ℕ → ℤ, LipschitzWith K f ∧
    Set.IsAPOfLengthFree {((n, f n) : ℤ × ℤ) | (n : ℕ)} 4 := by
  refine ⟨136, ff, ff_lipschitz, ?_⟩
  intro t hts ht
  exfalso
  obtain ⟨a, d, hcard, hteq⟩ := ht
  have g : ∀ n : ℕ, n < 4 → ∃ i : ℕ, ((i : ℤ), ff i) = a + n • d := by
    intro n hn
    have hmem : a + n • d ∈ t := by
      rw [hteq]; exact ⟨n, by exact_mod_cast hn, rfl⟩
    exact hts hmem
  obtain ⟨i0, h0⟩ := g 0 (by norm_num)
  obtain ⟨i1, h1⟩ := g 1 (by norm_num)
  obtain ⟨i2, h2⟩ := g 2 (by norm_num)
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at h0 h1 h2
  have key := ap3 i0 i1 i2 (by simp at h0 h1 h2; omega) (by simp at h0 h1 h2; omega)
  have hd1 : d.1 = 0 := by simp at h0 h1 h2; omega
  have hd2 : d.2 = 0 := by
    have : i0 = i1 := key.1
    subst this
    simp at h0 h1; omega
  have hd : d = 0 := Prod.ext hd1 hd2
  subst hd
  have hsub : t ⊆ {a} := by
    rw [hteq]
    rintro _ ⟨n, hn, rfl⟩
    simp
  have hle : ENat.card t ≤ 1 := by
    calc ENat.card t = t.encard := rfl
      _ ≤ ({a} : Set (ℤ × ℤ)).encard := Set.encard_le_encard hsub
      _ = 1 := Set.encard_singleton a
  rw [hcard] at hle
  norm_num at hle

end Green15Solution

theorem OMA.solution : type_of% @Green15.green_15_ap4 := by
  exact Green15Solution.main
