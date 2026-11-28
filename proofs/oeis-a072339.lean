import OMAStatements.S_oeis_a072339
import Mathlib

-- Problem: OEIS A072339, conjecture of Layman: for the minimal number a(n) of terms of an
-- alternating representation n = 2^k_1 - 2^k_2 + 2^k_3 - ... (k_1 > k_2 > ...),
-- a(2^k) = 1 and a(2^k + i) = a(2^k - i) + 1 for 0 < i < 2^k.
-- Statement: statements/oeis-a072339.lean (declaration OMA.S_oeis_a072339.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let S(l) be the alternating sum of a strictly decreasing list l. If l has head h,
-- then S(l) = 2^h - S(tail), and induction gives 2^h <= 2 S(l) and S(l) <= 2^h.
-- So a representation of n = 2^k + i with 0 < i < 2^k has head k + 1, and its tail is a
-- representation of 2^(k+1) - n = 2^k - i. Conversely a representation of 2^k - i has
-- head at most k, so k + 1 can be put in front. This is a bijection that adds one term.
-- Representations exist for each positive integer (strong induction with the same
-- reflection), so the minimum of the lengths increases by exactly one.

namespace OMA.A072339

open OMA.S_oeis_a072339

/-- The alternating sum of powers of two of a list of exponents. -/
def S (l : List ℕ) : ℤ := (l.map (fun k => (2 : ℤ) ^ k)).alternatingSum

lemma S_nil : S [] = 0 := by simp [S]

lemma S_cons (h : ℕ) (t : List ℕ) : S (h :: t) = 2 ^ h - S t := by
  simp [S, List.alternatingSum_cons, sub_eq_add_neg]

/-- Size of a nonempty representation with head `h`: 2^h <= 2 S and S <= 2^h. -/
lemma bound : ∀ (l : List ℕ) (h : ℕ), (h :: l).Pairwise (· > ·) →
    (2 : ℤ) ^ h ≤ 2 * S (h :: l) ∧ S (h :: l) ≤ 2 ^ h := by
  intro l
  induction l with
  | nil =>
    intro h _
    rw [S_cons, S_nil]
    have : (0 : ℤ) < 2 ^ h := by positivity
    constructor <;> linarith
  | cons h2 t ih =>
    intro h hp
    have hp2 : (h2 :: t).Pairwise (· > ·) := (List.pairwise_cons.mp hp).2
    have hlt : h2 < h := (List.pairwise_cons.mp hp).1 h2 (by simp)
    obtain ⟨b1, b2⟩ := ih h2 hp2
    rw [S_cons]
    have h3 : (2 : ℤ) * 2 ^ h2 ≤ 2 ^ h := by
      have : (2 : ℤ) ^ (h2 + 1) ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) hlt
      rw [pow_succ] at this
      linarith
    have : (0 : ℤ) < 2 ^ h2 := by positivity
    constructor <;> linarith

lemma pos_of_rep {n : ℕ} {l : List ℕ} (hn : 0 < n) (hr : IsRep n l) : l ≠ [] := by
  rintro rfl
  have := hr.2
  simp at this
  omega

/-- Reflection: representations of 2^k + i are the representations of 2^k - i with the
exponent k + 1 in front. -/
lemma rep_iff (k i : ℕ) (hi : 0 < i) (hik : i < 2 ^ k) (m : ℕ) :
    (∃ l : List ℕ, IsRep (2 ^ k + i) l ∧ l.length = m) ↔
    ∃ m', m = m' + 1 ∧ ∃ l : List ℕ, IsRep (2 ^ k - i) l ∧ l.length = m' := by
  have hik' : (i : ℤ) < 2 ^ k := by exact_mod_cast hik
  have hi' : (0 : ℤ) < i := by exact_mod_cast hi
  have hcast : ((2 ^ k - i : ℕ) : ℤ) = 2 ^ k - i := by
    rw [Nat.cast_sub hik.le]; push_cast; ring
  constructor
  · rintro ⟨l, hr, hl⟩
    cases l with
    | nil => exact absurd rfl (pos_of_rep (by positivity) hr)
    | cons h t =>
      obtain ⟨hp, hs⟩ := hr
      have hs' : S (h :: t) = 2 ^ k + i := by rw [S]; rw [hs]; push_cast; ring
      obtain ⟨b1, b2⟩ := bound t h hp
      have hh : h = k + 1 := by
        have h1 : (2 : ℤ) ^ k < 2 ^ h := by linarith
        have h2 : (2 : ℤ) ^ h < 2 ^ (k + 2) := by rw [pow_succ, pow_succ]; linarith
        have h1' : k < h := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).mp h1
        have h2' : h < k + 2 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).mp h2
        omega
      subst hh
      refine ⟨t.length, by simpa using hl.symm, t, ⟨(List.pairwise_cons.mp hp).2, ?_⟩, rfl⟩
      rw [S_cons] at hs'
      show S t = _
      rw [hcast]
      rw [pow_succ] at hs'
      linarith
  · rintro ⟨m', rfl, l, ⟨hp, hs⟩, hl⟩
    have hs' : S l = 2 ^ k - i := by rw [S, hs, hcast]
    refine ⟨(k + 1) :: l, ⟨?_, ?_⟩, by simp [hl]⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, hp⟩
      cases l with
      | nil => simp
      | cons h t =>
        obtain ⟨b1, b2⟩ := bound t h hp
        have h1 : (2 : ℤ) ^ h < 2 ^ (k + 1) := by rw [pow_succ]; linarith
        have h1' : h < k + 1 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).mp h1
        intro x hx
        have := (List.pairwise_cons.mp hp).1
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h1'
        · exact lt_trans (this x hx) h1'
    · show S ((k + 1) :: l) = _
      rw [S_cons, hs', pow_succ]; push_cast; ring

lemma rep_pow (k : ℕ) : IsRep (2 ^ k) [k] := by
  refine ⟨by simp, ?_⟩
  simp

/-- Each positive integer has a representation. -/
lemma exists_rep : ∀ n : ℕ, 0 < n → ∃ l : List ℕ, IsRep n l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨k, hk1, hk2⟩ : ∃ k, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) :=
      ⟨Nat.log 2 n, Nat.pow_log_le_self 2 hn.ne', Nat.lt_pow_succ_log_self (by norm_num) n⟩
    rcases Nat.eq_or_lt_of_le hk1 with h | h
    · exact ⟨[k], h ▸ rep_pow k⟩
    · obtain ⟨i, rfl⟩ : ∃ i, n = 2 ^ k + i := ⟨n - 2 ^ k, by omega⟩
      have hi : 0 < i := by omega
      have hik : i < 2 ^ k := by rw [pow_succ] at hk2; omega
      obtain ⟨l, hl⟩ := ih (2 ^ k - i) (by omega) (by omega)
      obtain ⟨l', hl', -⟩ := (rep_iff k i hi hik (l.length + 1)).mpr ⟨l.length, rfl, l, hl, rfl⟩
      exact ⟨l', hl'⟩

lemma a_pow (k : ℕ) : a (2 ^ k) = 1 := by
  unfold a
  apply le_antisymm
  · exact Nat.sInf_le ⟨[k], rep_pow k, rfl⟩
  · refine le_csInf ⟨1, [k], rep_pow k, rfl⟩ ?_
    rintro m ⟨l, hr, rfl⟩
    have := pos_of_rep (by positivity) hr
    exact Nat.one_le_iff_ne_zero.mpr (by simpa using this)

lemma a_reflect (k i : ℕ) (hi : 0 < i) (hik : i < 2 ^ k) :
    a (2 ^ k + i) = a (2 ^ k - i) + 1 := by
  have hne : {m : ℕ | ∃ l : List ℕ, IsRep (2 ^ k - i) l ∧ l.length = m}.Nonempty := by
    obtain ⟨l, hl⟩ := exists_rep (2 ^ k - i) (by omega)
    exact ⟨l.length, l, hl, rfl⟩
  have hmem := Nat.sInf_mem hne
  unfold a
  apply le_antisymm
  · exact Nat.sInf_le ((rep_iff k i hi hik _).mpr ⟨_, rfl, hmem⟩)
  · apply le_csInf
    · exact ⟨_, (rep_iff k i hi hik _).mpr ⟨_, rfl, hmem⟩⟩
    · intro m hm
      obtain ⟨m', rfl, hm'⟩ := (rep_iff k i hi hik m).mp hm
      exact Nat.succ_le_succ (Nat.sInf_le hm')

end OMA.A072339


theorem OMA.solution : type_of% @OMA.S_oeis_a072339.main :=
  ⟨OMA.A072339.a_pow, OMA.A072339.a_reflect⟩
