import OMAStatements.S_oeis_a006960
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Digits.Lemmas

-- The two cases of the one-step palindrome criterion are also stated in
-- Ando, Carry Asymmetry, Palindrome Characterization, and Conditional Non-Convergence
-- in the Reverse-and-Add Process, https://github.com/nkc-daiki/196-carry-asymmetry.
namespace OMA.R_oeis_a006960_R1

open OMA.S_oeis_a006960

-- In a same-length step, some pair of mirrored digits generates a carry.
def H1 : Prop :=
  ∀ k : ℕ,
    let n := revAdd^[k] 196
    let L := (Nat.digits 10 n).length
    revAdd n < 10 ^ L →
      ∃ i < L, 10 ≤ n / 10 ^ i % 10 + n / 10 ^ (L - 1 - i) % 10

-- In a length-increasing step, some mirrored pair sum differs from both 0 and 11.
def H2 : Prop :=
  ∀ k : ℕ,
    let n := revAdd^[k] 196
    let L := (Nat.digits 10 n).length
    10 ^ L ≤ revAdd n →
      ∃ i < L,
        let sum := n / 10 ^ i % 10 + n / 10 ^ (L - 1 - i) % 10
        sum ≠ 0 ∧ sum ≠ 11

lemma carry_free_of_reflected_output {L : ℕ} {s c y : ℕ → ℕ}
    (hc : ∀ i, c i ≤ 1) (hc₀ : c 0 = 0) (hcL : c L = 0)
    (hs : ∀ i < L, s i = s (L - 1 - i))
    (hy : ∀ i < L, y i = y (L - 1 - i))
    (hcol : ∀ i < L, y i + 10 * c (i + 1) = s i + c i)
    (hylt : ∀ i, y i < 10) : ∀ i < L, s i < 10 := by
  have reflect (i : ℕ) (hi : i < L) :
      c i = c (L - 1 - i) ∧ c (i + 1) = c (L - i) := by
    have hindex : L - 1 - i + 1 = L - i := by omega
    have hleft := hcol i hi
    have hright := hcol (L - 1 - i) (by omega)
    rw [hindex, ← hs i hi, ← hy i hi] at hright
    have hci := hc i
    have hcj := hc (L - 1 - i)
    omega
  -- The two reflected equalities imply a two-column recurrence for the carries.
  have zero_carries (i : ℕ) (hi : i ≤ L) : c i = 0 := by
    induction i using Nat.strongRecOn with
    | ind i ih =>
      obtain _ | j := i
      · exact hc₀
      obtain _ | j := j
      · exact (reflect 0 (by omega)).2.trans (by simpa using hcL)
      have hleft := (reflect (j + 1) (by omega)).2
      have hright := (reflect j (by omega)).1
      have hindex : L - (j + 1) = L - 1 - j := by omega
      rw [hindex, ← hright, ih j (by omega) (by omega)] at hleft
      exact hleft
  intro i hi
  have h := hcol i hi
  rw [zero_carries i (by omega), zero_carries (i + 1) (by omega)] at h
  have := hylt i
  omega

lemma overflow_sums_of_reflected_output {L : ℕ} {s c y : ℕ → ℕ} (hL : 0 < L)
    (hc : ∀ i, c i ≤ 1) (hc₀ : c 0 = 0) (hcL : c L = 1) (hyL : y L = 1)
    (hs : ∀ i < L, s i = s (L - 1 - i))
    (hy : ∀ i ≤ L, y i = y (L - i))
    (hcol : ∀ i < L, y i + 10 * c (i + 1) = s i + c i)
    (hylt : ∀ i, y i < 10) : ∀ i < L, s i = 0 ∨ s i = 11 := by
  -- The extra leading digit shifts the output reflection by one column.
  have paired (i : ℕ) (hi : i < L) :
      s i = 11 * c (i + 1) ∧ c (i + 1) = c (L - i) := by
    induction i with
    | zero =>
      have hzero : y 0 = 1 := by simpa using (hy 0 (by omega)).trans hyL
      have hleft := hcol 0 hL
      have hright := hcol (L - 1) (by omega)
      have hindex : L - 1 + 1 = L := by omega
      have hmirror : s 0 = s (L - 1) := by simpa using hs 0 hL
      rw [hindex, hcL, ← hmirror] at hright
      have hbound := hc (L - 1)
      have hone := hc 1
      simp only [Nat.sub_zero, Nat.zero_add] at hleft ⊢
      omega
    | succ i ih =>
      obtain ⟨hprev, hmirror⟩ := ih (by omega)
      have hleft := hcol (i + 1) hi
      have hright := hcol (L - (i + 1)) (by omega)
      have houter : L - 1 - i = L - (i + 1) := by omega
      have hnext : L - (i + 1) + 1 = L - i := by omega
      have hequal := hy (i + 1) (by omega)
      rw [← hequal, hnext, ← hmirror, ← houter, ← hs i (by omega), hprev, houter] at hright
      have hincoming := hcol (L - 1 - (i + 1)) (by omega)
      have hincomingIndex : L - 1 - (i + 1) + 1 = L - (i + 1) := by omega
      rw [hincomingIndex, ← hs (i + 1) hi] at hincoming
      have hbound := hylt (L - 1 - (i + 1))
      have hdiff : s (i + 1) = 10 * c (i + 1 + 1) + c (L - (i + 1)) := by omega
      have ha := hc (i + 1 + 1)
      have hb := hc (L - (i + 1))
      have hd := hc (L - 1 - (i + 1))
      change s (i + 1) = 11 * c (i + 1 + 1) ∧ c (i + 1 + 1) = c (L - (i + 1))
      omega
  intro i hi
  have h := (paired i hi).1
  have := hc (i + 1)
  omega

lemma ofDigits_column (l : List ℕ) (i : ℕ) (hl : ∀ d ∈ l, d < 10) :
    Nat.ofDigits 10 l / 10 ^ i % 10 = l.getD i 0 := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i (by decide) l hl]
  have hget : (l.drop i).headD 0 = l.getD i 0 := by
    simp [List.getD_eq_getElem?_getD, List.head?_eq_getElem?]
  rw [← hget]
  cases h : l.drop i with
  | nil => simp
  | cons a rest =>
    have ha := hl a (List.mem_of_mem_drop (h.symm ▸ List.mem_cons_self))
    simp [Nat.ofDigits_cons, Nat.mod_eq_of_lt ha]

lemma reflected_decimal_column {n L : ℕ} (hlen : (Nat.digits 10 n).length = L)
    (hp : IsPalindrome n) (i : ℕ) (hi : i < L) :
    n / 10 ^ i % 10 = n / 10 ^ (L - 1 - i) % 10 := by
  have heq := congrArg (fun l : List ℕ => l.getD i 0) hp
  change (Nat.digits 10 n).reverse.getD i 0 = (Nat.digits 10 n).getD i 0 at heq
  rw [List.getD_reverse i (by omega), hlen, Nat.getD_digits (b := 10) n _ (by decide),
    Nat.getD_digits (b := 10) n _ (by decide)] at heq
  exact heq.symm

lemma step_palindrome_sums (n : ℕ) (hn : 0 < n) (hp : IsPalindrome (revAdd n)) :
    let L := (Nat.digits 10 n).length
    (revAdd n < 10 ^ L → ∀ i < L, n / 10 ^ i % 10 + n / 10 ^ (L - 1 - i) % 10 < 10) ∧
    (10 ^ L ≤ revAdd n → ∀ i < L,
      let sum := n / 10 ^ i % 10 + n / 10 ^ (L - 1 - i) % 10
      sum = 0 ∨ sum = 11) := by
  let L := (Nat.digits 10 n).length
  let r := reverse n
  let m := n + r
  let s := fun i : ℕ => n / 10 ^ i % 10 + n / 10 ^ (L - 1 - i) % 10
  let y := fun i : ℕ => m / 10 ^ i % 10
  -- Truncating the sum includes the carry from the columns below i.
  let c := fun i : ℕ => m / 10 ^ i - (n / 10 ^ i + r / 10 ^ i)
  have hL : 0 < L := by
    exact List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega))
  have hnlt : n < 10 ^ L := Nat.lt_base_pow_length_digits (by decide)
  have hrlt : r < 10 ^ L := by
    have hdigits (d : ℕ) (hd : d ∈ (Nat.digits 10 n).reverse) : d < 10 :=
      Nat.digits_lt_base (by decide) (List.mem_reverse.mp hd)
    simpa only [r, reverse, L, List.length_reverse] using
      Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10) hdigits
  have hmlt : m < 10 ^ (L + 1) := by
    rw [Nat.pow_succ]
    dsimp [m]
    omega
  have hlenLower : L ≤ (Nat.digits 10 m).length :=
    Nat.le_length_digits_le 10 n m (by dsimp [m]; omega)
  have hlenUpper : (Nat.digits 10 m).length ≤ L + 1 :=
    (Nat.digits_length_le_iff (b := 10) (by decide) m).2 hmlt
  have hs (i : ℕ) (hi : i < L) : s i = s (L - 1 - i) := by
    have hindex : L - 1 - (L - 1 - i) = i := by omega
    dsimp only [s]
    rw [hindex, Nat.add_comm]
  have hrev (i : ℕ) (hi : i < L) : r / 10 ^ i % 10 = n / 10 ^ (L - 1 - i) % 10 := by
    dsimp [r, reverse]
    rw [ofDigits_column _ _ (fun d hd => Nat.digits_lt_base (by decide) (List.mem_reverse.mp hd)),
      List.getD_reverse i hi, Nat.getD_digits (b := 10) n _ (by decide)]
  have hc (i : ℕ) : c i ≤ 1 := by
    dsimp [c, m]
    rw [Nat.add_div (Nat.pow_pos_iff.mpr (Or.inl (by decide : 0 < 10)))]
    split <;> omega
  have hc₀ : (c 0) = 0 := by simp [c, m]
  have hcL : c L = m / 10 ^ L := by
    simp [c, Nat.div_eq_of_lt hnlt, Nat.div_eq_of_lt hrlt]
  have hquot (i : ℕ) : m / 10 ^ i = n / 10 ^ i + r / 10 ^ i + c i := by
    have hle := Nat.div_add_div_le_add_div (x := n) (y := r) (z := 10 ^ i)
    change n / 10 ^ i + r / 10 ^ i ≤ m / 10 ^ i at hle
    dsimp only [c]
    omega
  have hdigit (a i : ℕ) : a / 10 ^ i % 10 + 10 * (a / 10 ^ (i + 1)) = a / 10 ^ i := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    exact Nat.mod_add_div _ _
  have hcol (i : ℕ) (hi : i < L) : y i + 10 * c (i + 1) = s i + c i := by
    have ha := hdigit n i
    have hb := hdigit r i
    have hm := hdigit m i
    have hq := hquot i
    have hq' := hquot (i + 1)
    rw [hrev i hi] at hb
    dsimp only [y, s]
    omega
  have hylt (i : ℕ) : y i < 10 := Nat.mod_lt _ (by decide)
  change IsPalindrome m at hp
  change (m < 10 ^ L → ∀ i < L, s i < 10) ∧
    (10 ^ L ≤ m → ∀ i < L, s i = 0 ∨ s i = 11)
  constructor
  · intro hsmall
    have hlen : (Nat.digits 10 m).length = L :=
      Nat.le_antisymm ((Nat.digits_length_le_iff (b := 10) (by decide) m).2 hsmall) hlenLower
    have hy (i : ℕ) (hi : i < L) : y i = y (L - 1 - i) :=
      reflected_decimal_column hlen hp i hi
    exact carry_free_of_reflected_output hc hc₀ (hcL.trans (Nat.div_eq_of_lt hsmall)) hs hy hcol hylt
  · intro hlarge
    have hlen : (Nat.digits 10 m).length = L + 1 := by
      have h := (Nat.lt_digits_length_iff (b := 10) (by decide) m).2 hlarge
      omega
    have hb : m / 10 ^ L = 1 := by
      have h := hc L
      rw [hcL] at h
      have hpos : 0 < m / 10 ^ L := Nat.div_pos hlarge
        (Nat.pow_pos_iff.mpr (Or.inl (by decide : 0 < 10)))
      omega
    have hyL : y L = 1 := by simp [y, hb]
    have hy (i : ℕ) (hi : i ≤ L) : y i = y (L - i) := by
      have h := reflected_decimal_column hlen hp i (by omega)
      simpa [y] using h
    exact overflow_sums_of_reflected_output hL hc hc₀ (hcL.trans hb) hyL hs hy hcol hylt

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma smaller_seeds (n : ℕ) (hn : n < 196) :
    ∃ k ≤ 24, IsPalindrome (revAdd^[k] n) := by
  let isPal := fun m : ℕ => decide ((Nat.digits 10 m).reverse = Nat.digits 10 m)
  have verified : (List.range 196).all
      (fun a => (List.range 25).any (fun k => isPal (revAdd^[k] a))) = true := by
    decide +revert
  obtain ⟨k, hk, hpal⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp verified n (List.mem_range.mpr hn))
  refine ⟨k, Nat.le_of_lt_succ (List.mem_range.mp hk), ?_⟩
  unfold IsPalindrome
  exact of_decide_eq_true hpal

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a006960.main := by
  intro hcarry hnd
  have hpos (k : ℕ) : 0 < revAdd^[k] 196 := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change 0 < revAdd^[k] 196 + reverse (revAdd^[k] 196)
      omega
  constructor
  · intro k hp
    cases k with
    | zero => exact (by decide : ¬ ((Nat.digits 10 196).reverse = Nat.digits 10 196)) hp
    | succ k =>
      rw [Function.iterate_succ_apply'] at hp
      obtain ⟨hsmall, hlarge⟩ := step_palindrome_sums _ (hpos k) hp
      by_cases h : revAdd (revAdd^[k] 196) < 10 ^ (Nat.digits 10 (revAdd^[k] 196)).length
      · obtain ⟨i, hi, hs⟩ := hcarry k h
        exact (Nat.not_lt_of_ge hs) (hsmall h i hi)
      · have h' := Nat.le_of_not_gt h
        obtain ⟨i, hi, hzero, heleven⟩ := hnd k h'
        exact (hlarge h' i hi).elim hzero heleven
  · intro n _ hn
    obtain ⟨k, _, hk⟩ := smaller_seeds n hn
    exact ⟨k, hk⟩

end OMA.R_oeis_a006960_R1
