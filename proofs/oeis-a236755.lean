import OMAStatements.S_oeis_a236755
import Mathlib

/-!
# OEIS A236755: expanded semicircle spirals

A lap over an even-length list is a translation. For n = 4t+2 the translation
is nonzero by parity, for n = 4t explicit witnesses are given.
-/

namespace OMA.A236755Proof

open OMA.S_oeis_a236755

theorem traverse_append (as bs : List ℕ) (x : ℤ) :
    traverse (as ++ bs) x = traverse bs (traverse as x) := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih => simp [S_oeis_a236755.traverse, ih]

theorem traverse_lin (cs : List ℕ) :
    ∃ a : ℤ, a % 2 = (cs.sum : ℤ) % 2 ∧
      ∀ x, traverse cs x = (-1) ^ cs.length * x + 2 * a := by
  induction cs with
  | nil => exact ⟨0, by simp, fun x => by simp [S_oeis_a236755.traverse]⟩
  | cons c cs ih =>
    obtain ⟨a, ha, h⟩ := ih
    rcases neg_one_pow_eq_or ℤ cs.length with h1 | h1
    · refine ⟨a + c, by rw [List.sum_cons, Nat.cast_add]; omega, fun x => ?_⟩
      simp only [S_oeis_a236755.traverse, h, List.length_cons, pow_succ, h1]; ring
    · refine ⟨a - c, by rw [List.sum_cons, Nat.cast_add]; omega, fun x => ?_⟩
      simp only [S_oeis_a236755.traverse, h, List.length_cons, pow_succ, h1]; ring

theorem afterLaps_shift (cs : List ℕ) (d : ℤ) (h : ∀ x, traverse cs x = x + d)
    (x : ℤ) (k : ℕ) : afterLaps cs x k = x + k * d := by
  induction k with
  | zero => simp [afterLaps]
  | succ k ih => simp only [afterLaps, ih, h]; push_cast; ring

theorem expanded_of_shift (cs : List ℕ) (hne : cs ≠ []) (d : ℤ) (hd : d ≠ 0)
    (h : ∀ x, traverse cs x = x + d) : IsExpanded cs := by
  intro B
  cases cs with
  | nil => exact absurd rfl hne
  | cons c cs =>
    refine ⟨B + 2, ⟨0, by simp⟩, ?_⟩
    rw [afterLaps_shift _ d h]
    change B < ((c : ℤ) - 1 + ((B + 2 : ℕ) : ℤ) * d - (c : ℤ)).natAbs
    have key : (B : ℤ) + 2 ≤ |((B + 2 : ℕ) : ℤ) * d| := by
      rw [abs_mul]
      have h1 : (1 : ℤ) ≤ |d| := Int.one_le_abs hd
      have h2 : (0 : ℤ) ≤ |((B + 2 : ℕ) : ℤ)| := abs_nonneg _
      have h3 : |((B + 2 : ℕ) : ℤ)| = (B : ℤ) + 2 := by
        rw [abs_of_nonneg (by positivity)]; push_cast; ring
      nlinarith
    generalize ((B + 2 : ℕ) : ℤ) * d = z at key
    rcases abs_cases z with ⟨hz, _⟩ | ⟨hz, _⟩ <;> omega

def wl : ℕ → List ℕ
  | 0 => []
  | t + 1 => wl t ++ [4 * t, 4 * t + 1, 4 * t + 3, 4 * t + 2]

def we : ℕ → List ℕ
  | 0 => []
  | t + 1 => we t ++ [4 * t, 4 * t + 1, 4 * t + 2, 4 * t + 3]

theorem range_block (t : ℕ) :
    List.range (4 * (t + 1)) = List.range (4 * t) ++ [4 * t, 4 * t + 1, 4 * t + 2, 4 * t + 3] := by
  have : 4 * (t + 1) = 4 * t + 1 + 1 + 1 + 1 := by ring
  rw [this]
  simp [List.range_succ]

theorem wl_perm (t : ℕ) : (wl t).Perm (List.range (4 * t)) := by
  induction t with
  | zero => simp [wl]
  | succ t ih =>
    rw [range_block, wl]
    refine ih.append ?_
    exact List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))

theorem we_perm (t : ℕ) : (we t).Perm (List.range (4 * t)) := by
  induction t with
  | zero => simp [we]
  | succ t ih =>
    rw [range_block, we]
    exact ih.append (List.Perm.refl _)

theorem wl_traverse (t : ℕ) (x : ℤ) : traverse (wl t) x = x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [wl, traverse_append, ih]
    simp only [S_oeis_a236755.traverse]; push_cast; ring

theorem we_traverse (t : ℕ) (x : ℤ) : traverse (we t) x = x + 4 * t := by
  induction t with
  | zero => simp [we, S_oeis_a236755.traverse]
  | succ t ih =>
    rw [we, traverse_append, ih]
    simp only [S_oeis_a236755.traverse]; push_cast; ring

theorem range_sum_two (n : ℕ) : (List.range n).sum * 2 = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.sum_append, Nat.add_mul, ih]
    cases n with
    | zero => rfl
    | succ m => simp; ring

theorem expanded_of_mod (n : ℕ) (hn : n % 4 = 2) (cs : List ℕ)
    (hp : cs.Perm (List.range n)) : IsExpanded cs := by
  obtain ⟨a, ha, h⟩ := traverse_lin cs
  have hlen : cs.length = n := by rw [hp.length_eq, List.length_range]
  have hsum : cs.sum * 2 = n * (n - 1) := by rw [hp.sum_eq, range_sum_two]
  have hodd : cs.sum % 2 = 1 := by
    obtain ⟨t, rfl⟩ : ∃ t, n = 4 * t + 2 := ⟨n / 4, by omega⟩
    have h1 : 4 * t + 2 - 1 = 4 * t + 1 := by omega
    rw [h1] at hsum
    have h2 : cs.sum = (2 * t + 1) * (4 * t + 1) := by nlinarith
    rw [h2, Nat.mul_mod]
    have e1 : (2 * t + 1) % 2 = 1 := by omega
    have e2 : (4 * t + 1) % 2 = 1 := by omega
    rw [e1, e2]
  have ha0 : a ≠ 0 := by
    intro h0; subst h0; omega
  have hev : Even cs.length := by rw [hlen]; exact ⟨n / 2, by omega⟩
  refine expanded_of_shift cs ?_ (2 * a) (by omega) (fun x => ?_)
  · intro h0; subst h0; simp at hlen; omega
  · rw [h, hev.neg_one_pow]; ring

end OMA.A236755Proof

open OMA.S_oeis_a236755 OMA.A236755Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a236755.main := by
  refine ⟨fun n hn => ⟨expanded_of_mod n hn, ?_⟩, fun n hpos hn => ?_⟩
  · unfold expandedCount
    rw [List.filter_eq_self.2, List.length_permutations, List.length_range]
    intro cs hcs
    rw [List.mem_permutations] at hcs
    simpa using expanded_of_mod n hn cs hcs
  · obtain ⟨t, rfl⟩ : ∃ t, n = 4 * t := ⟨n / 4, by omega⟩
    refine ⟨⟨wl t, wl_perm t, 1, Nat.one_pos, ?_, ?_⟩, we t, we_perm t, ?_⟩
    · rw [(wl_perm t).length_eq, List.length_range]; omega
    · simp [afterLaps, wl_traverse]
    · refine expanded_of_shift _ ?_ (4 * t) (by omega) (we_traverse t)
      intro h0
      have := (we_perm t).length_eq
      rw [h0, List.length_range] at this
      simp at this; omega
