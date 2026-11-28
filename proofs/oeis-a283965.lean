import OMAStatements.S_oeis_a283965
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Count
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A283965: positions of 1 in the fixed point of 0 -> 1, 1 -> 1010

All positions use the one-based convention of the OEIS sequence.  We first
prove a discrepancy bound for every finite prefix of every substitution
iterate.  A prefix ending in 1 then gives exactly the conjectured bound
for the position of its last 1.
-/

namespace A283965

open OMA.S_oeis_a283965 (Word letter subst iter ones nthOne a)

noncomputable def rho : ℝ := Real.sqrt 3

noncomputable def discrepancy (w : Word) : ℝ :=
  rho * (ones w : ℝ) - (w.length : ℝ)

lemma rho_sq : rho ^ 2 = 3 := by
  exact Real.sq_sqrt (by norm_num)

lemma rho_gt_one : 1 < rho := by
  have h := Real.sqrt_nonneg (3 : ℝ)
  have hs := rho_sq
  dsimp [rho] at *
  nlinarith

lemma rho_lt_two : rho < 2 := by
  have h := Real.sqrt_nonneg (3 : ℝ)
  have hs := rho_sq
  dsimp [rho] at *
  nlinarith

@[simp] lemma subst_nil : subst [] = [] := rfl
@[simp] lemma subst_cons (b : Bool) (w : Word) :
    subst (b :: w) = letter b ++ subst w := rfl
@[simp] lemma subst_append (u v : Word) :
    subst (u ++ v) = subst u ++ subst v := by simp [subst]

@[simp] lemma ones_nil : ones [] = 0 := rfl
@[simp] lemma ones_append (u v : Word) : ones (u ++ v) = ones u + ones v := by
  simp [ones]

@[simp] lemma discrepancy_nil : discrepancy [] = 0 := by simp [discrepancy]

lemma discrepancy_append (u v : Word) :
    discrepancy (u ++ v) = discrepancy u + discrepancy v := by
  simp [discrepancy]
  ring

lemma length_subst (w : Word) :
    (subst w).length = w.length + 3 * ones w := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b <;> simp_all [letter, ones] <;> omega

lemma ones_subst (w : Word) :
    ones (subst w) = w.length + ones w := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b <;> simp_all [letter, ones] <;> omega

lemma discrepancy_subst (w : Word) :
    discrepancy (subst w) = -(rho - 1) * discrepancy w := by
  rw [discrepancy, ones_subst, length_subst]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  unfold discrepancy
  nlinarith [rho_sq]

/-- The possible unfinished pieces at the end of a substituted prefix. -/
def TailPiece (r : Word) : Prop :=
  r = [] ∨ r = [true] ∨ r = [true, false] ∨ r = [true, false, true]

lemma proper_letter_prefix {b : Bool} {r : Word}
    (hr : r <+: letter b) (hlen : r.length < (letter b).length) : TailPiece r := by
  have heq := List.prefix_iff_eq_take.mp hr
  cases b <;> simp only [letter, List.length_cons, List.length_nil] at hlen heq
  · have hz : r.length = 0 := by omega
    simp [hz] at heq
    exact Or.inl heq
  · have hcases : r.length = 0 ∨ r.length = 1 ∨ r.length = 2 ∨ r.length = 3 := by omega
    rcases hcases with h | h | h | h
    · exact Or.inl (by simpa [h] using heq)
    · exact Or.inr (Or.inl (by simpa [h] using heq))
    · exact Or.inr (Or.inr (Or.inl (by simpa [h] using heq)))
    · exact Or.inr (Or.inr (Or.inr (by simpa [h] using heq)))

/-- Every prefix splits into complete substituted letters and an unfinished piece. -/
lemma prefix_subst {w v : Word} (hv : v <+: subst w) :
    ∃ p r : Word, p <+: w ∧ v = subst p ++ r ∧ TailPiece r := by
  induction w generalizing v with
  | nil =>
    have he : v = [] := by simpa using hv
    subst v
    exact ⟨[], [], List.prefix_refl _, rfl, Or.inl rfl⟩
  | cons b w ih =>
    rw [subst_cons] at hv
    by_cases hlen : v.length < (letter b).length
    · have hpre : v <+: letter b :=
        List.prefix_of_prefix_length_le hv (List.prefix_append _ _) (Nat.le_of_lt hlen)
      exact ⟨[], v, List.nil_prefix, rfl, proper_letter_prefix hpre hlen⟩
    · have hpre : letter b <+: v :=
        List.prefix_of_prefix_length_le (List.prefix_append _ _) hv (by omega)
      obtain ⟨u, rfl⟩ := hpre
      have hu : u <+: subst w := (List.prefix_append_right_inj _).mp hv
      obtain ⟨p, r, hp, he, hr⟩ := ih hu
      refine ⟨b :: p, r, ?_, ?_, hr⟩
      · simpa using hp
      · simp [he, List.append_assoc]

lemma tailPiece_bounds {r : Word} (hr : TailPiece r) :
    rho - 2 ≤ discrepancy r ∧ discrepancy r ≤ rho - 1 := by
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp [discrepancy, ones] <;>
    (try constructor) <;> linarith [rho_gt_one, rho_lt_two]

lemma interval_preserved {d e : ℝ}
    (hd : -rho < d ∧ d < 2) (he : rho - 2 ≤ e ∧ e ≤ rho - 1) :
    -rho < -(rho - 1) * d + e ∧ -(rho - 1) * d + e < 2 := by
  have hp : 0 < rho - 1 := by linarith [rho_gt_one]
  have hlo := mul_lt_mul_of_pos_left hd.2 hp
  have hhi := mul_lt_mul_of_pos_left hd.1 hp
  constructor <;> nlinarith [rho_sq]

/-- A uniform bound for all prefixes, including prefixes ending in 0. -/
theorem prefix_bounds (k : ℕ) {v : Word} (hv : v <+: iter k) :
    -rho < discrepancy v ∧ discrepancy v < 2 := by
  induction k generalizing v with
  | zero =>
    have hpre : v <+: [true] := hv
    have heq := List.prefix_iff_eq_take.mp hpre
    have hlen := hpre.length_le
    have hcases : v.length = 0 ∨ v.length = 1 := by simp at hlen; omega
    rcases hcases with h | h
    · have he : v = [] := by simpa [h] using heq
      subst v
      simp only [discrepancy_nil]
      constructor <;> linarith [rho_gt_one]
    · have he : v = [true] := by simpa [h] using heq
      subst v
      simp [discrepancy, ones]
      constructor <;> linarith [rho_gt_one, rho_lt_two]
  | succ k ih =>
    obtain ⟨p, r, hp, rfl, hr⟩ := prefix_subst hv
    rw [discrepancy_append, discrepancy_subst]
    exact interval_preserved (ih hp) (tailPiece_bounds hr)

/-- Exactly the conjectured inequality for every prefix ending in 1. -/
theorem one_ending_prefix_bounds (k : ℕ) (v : Word)
    (hv : v ++ [true] <+: iter k) :
    -1 < discrepancy (v ++ [true]) ∧ discrepancy (v ++ [true]) < 2 := by
  have hp : v <+: iter k := (List.prefix_append v [true]).trans hv
  have hbefore := prefix_bounds k hp
  have hwhole := prefix_bounds k hv
  have hstep : discrepancy (v ++ [true]) = discrepancy v + rho - 1 := by
    rw [discrepancy_append]
    simp [discrepancy, ones]
    ring
  constructor
  · linarith
  · exact hwhole.2

/-- `IsOnePosition n m` says that the m-th letter is the n-th 1, with both
indices one-based.  Every finite prefix of the fixed point appears in an
iterate; the predicate states that fact directly, without a choice of limit. -/
def IsOnePosition (n m : ℕ) : Prop :=
  ∃ k : ℕ, ∃ v : Word,
    v ++ [true] <+: iter k ∧ ones (v ++ [true]) = n ∧ (v ++ [true]).length = m

/-- OEIS A283965's conjecture, in a representation-independent position form. -/
theorem position_bounds {n m : ℕ} (h : IsOnePosition n m) :
    -1 < Real.sqrt 3 * (n : ℝ) - (m : ℝ) ∧
      Real.sqrt 3 * (n : ℝ) - (m : ℝ) < 2 := by
  obtain ⟨k, v, hv, hn, hm⟩ := h
  have hb := one_ending_prefix_bounds k v hv
  simpa only [discrepancy, rho, hn, hm] using hb

/-- One-based position of the n-th 1 in a finite word. Only values with
1 ≤ n ≤ `ones w` are used below. This is an explicit finite algorithm. -/
lemma nthOne_spec (w : Word) (n : ℕ) (hn : 0 < n) (hc : n ≤ ones w) :
    ∃ v : Word, v ++ [true] <+: w ∧
      ones (v ++ [true]) = n ∧ (v ++ [true]).length = nthOne n w := by
  induction w generalizing n with
  | nil => simp at hc; omega
  | cons b w ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases b with
      | false =>
        have hc' : n + 1 ≤ ones w := by simpa [ones] using hc
        obtain ⟨v, hv, hvc, hvl⟩ := ih (n + 1) (by omega) hc'
        refine ⟨false :: v, ?_, ?_, ?_⟩
        · simpa using hv
        · simpa [ones] using hvc
        · simpa [nthOne] using congrArg Nat.succ hvl
      | true =>
        cases n with
        | zero =>
          refine ⟨[], ?_, ?_, ?_⟩
          · simp
          · simp [ones]
          · rfl
        | succ n =>
          have hc' : n + 1 ≤ ones w := by
            simp [ones] at hc ⊢
            omega
          obtain ⟨v, hv, hvc, hvl⟩ := ih (n + 1) (by omega) hc'
          refine ⟨true :: v, ?_, ?_, ?_⟩
          · simpa using hv
          · simpa [ones] using congrArg Nat.succ hvc
          · simpa [nthOne] using congrArg Nat.succ hvl

lemma ones_iter_ge (k : ℕ) : k + 1 ≤ ones (iter k) := by
  induction k with
  | zero => simp [iter, ones]
  | succ k ih =>
    rw [iter, ones_subst]
    have hl : ones (iter k) ≤ (iter k).length := List.count_le_length
    omega

/-- An explicit formula sufficient to define the entire OEIS sequence:
iterate n times, then find the n-th 1. The preceding bound proves that
this finite word always contains enough 1s. -/
theorem a_isOnePosition (n : ℕ) (hn : 0 < n) : IsOnePosition n (a n) := by
  have hc : n ≤ ones (iter n) := by have h := ones_iter_ge n; omega
  obtain ⟨v, hv, hvc, hvl⟩ := nthOne_spec (iter n) n hn hc
  exact ⟨n, v, hv, hvc, hvl⟩

lemma iter_prefix_succ (k : ℕ) : iter k <+: iter (k + 1) := by
  induction k with
  | zero => exact ⟨[false, true, false], rfl⟩
  | succ k ih => exact ih.flatMap letter

lemma iter_prefix_add (k d : ℕ) : iter k <+: iter (k + d) := by
  induction d with
  | zero => simp
  | succ d ih => exact ih.trans (iter_prefix_succ (k + d))

lemma nthOne_of_prefix (v s : Word) :
    nthOne (ones (v ++ [true])) ((v ++ [true]) ++ s) = (v ++ [true]).length := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    cases b <;> simp [ones, nthOne] at * <;> omega

/-- The nth position is independent of which sufficiently long iterate
is used to read it. -/
theorem onePosition_unique {n m₁ m₂ : ℕ}
    (h₁ : IsOnePosition n m₁) (h₂ : IsOnePosition n m₂) : m₁ = m₂ := by
  obtain ⟨k₁, v₁, hp₁, hc₁, hl₁⟩ := h₁
  obtain ⟨k₂, v₂, hp₂, hc₂, hl₂⟩ := h₂
  have hb₁ : v₁ ++ [true] <+: iter (k₁ + k₂) :=
    hp₁.trans (iter_prefix_add k₁ k₂)
  have hb₂ : v₂ ++ [true] <+: iter (k₁ + k₂) :=
    hp₂.trans (by simpa [Nat.add_comm] using iter_prefix_add k₂ k₁)
  obtain ⟨s₁, hs₁⟩ := hb₁
  obtain ⟨s₂, hs₂⟩ := hb₂
  have hval₁ := nthOne_of_prefix v₁ s₁
  have hval₂ := nthOne_of_prefix v₂ s₂
  rw [hc₁, hs₁, hl₁] at hval₁
  rw [hc₂, hs₂, hl₂] at hval₂
  exact hval₁.symm.trans hval₂

/-- The complete conjecture for the OEIS sequence, with no existence or
other mathematical conjecture assumed. -/
theorem main (n : ℕ) (hn : 0 < n) :
    -1 < Real.sqrt 3 * (n : ℝ) - (a n : ℝ) ∧
      Real.sqrt 3 * (n : ℝ) - (a n : ℝ) < 2 :=
  position_bounds (a_isOnePosition n hn)


end A283965

theorem OMA.solution : type_of% @OMA.S_oeis_a283965.main := A283965.main
