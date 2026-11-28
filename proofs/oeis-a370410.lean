import OMAStatements.S_oeis_a370410
import Mathlib

/-!
Proof of a(n) = A007055(n) - A056458(n) for A370410, following Gabric's argument in the entry.

Among the strings of length n ≥ 1 that are a concatenation of two possibly empty palindromes,
those that are not a concatenation of two nonempty palindromes are exactly the primitive
palindromes. If one factor is empty the string is a palindrome, and a palindrome z^k with k ≥ 2
splits as z and z^(k-1), both nonempty palindromes. Conversely a palindrome u ++ v with u, v
palindromes satisfies u ++ v = v ++ u, and commuting strings are powers of a common string
(Lyndon and Schützenberger, proved here by strong induction on the total length), so u ++ v is a
proper power. Hence the set counted by A007055 is the disjoint union of the other two sets.
-/

namespace A370410

open OMA.S_oeis_a370410

/-- The power z^k. -/
def pw (z : List Bool) (k : ℕ) : List Bool := (List.replicate k z).flatten

theorem pw_zero (z : List Bool) : pw z 0 = [] := by
  unfold pw; simp

theorem pw_one (z : List Bool) : pw z 1 = z := by
  unfold pw; simp

theorem pw_nil (k : ℕ) : pw [] k = [] := by
  unfold pw; simp

theorem pw_succ (z : List Bool) (k : ℕ) : pw z (k + 1) = z ++ pw z k := by
  unfold pw; rw [List.replicate_succ, List.flatten_cons]

theorem pw_add (z : List Bool) (i j : ℕ) : pw z (i + j) = pw z i ++ pw z j := by
  unfold pw; rw [List.replicate_add, List.flatten_append]

theorem pw_reverse (z : List Bool) (k : ℕ) : (pw z k).reverse = pw z.reverse k := by
  unfold pw; rw [List.reverse_flatten, List.map_replicate, List.reverse_replicate]

/-- Commuting strings are powers of a common string. -/
theorem comm_pow : ∀ (m : ℕ) (u v : List Bool), u.length + v.length ≤ m → u ++ v = v ++ u →
    ∃ (z : List Bool) (i j : ℕ), u = pw z i ∧ v = pw z j := by
  intro m
  induction m with
  | zero =>
    intro u v h _
    have hu : u = [] := List.length_eq_zero_iff.mp (by omega)
    have hv : v = [] := List.length_eq_zero_iff.mp (by omega)
    exact ⟨[], 0, 0, by rw [hu, pw_zero], by rw [hv, pw_zero]⟩
  | succ m ih =>
    intro u v h huv
    by_cases hu : u = []
    · exact ⟨v, 0, 1, by rw [hu, pw_zero], (pw_one v).symm⟩
    by_cases hv : v = []
    · exact ⟨u, 1, 0, (pw_one u).symm, by rw [hv, pw_zero]⟩
    have hul : 0 < u.length := List.length_pos_iff.mpr hu
    have hvl : 0 < v.length := List.length_pos_iff.mpr hv
    rcases List.append_eq_append_iff.mp huv with ⟨t, h1, h2⟩ | ⟨t, h1, h2⟩
    · -- v = u ++ t and v = t ++ u
      have hlen : v.length = u.length + t.length := by rw [h1]; simp
      obtain ⟨z, i, j, hi, hj⟩ := ih u t (by omega) (h1.symm.trans h2)
      refine ⟨z, i, i + j, hi, ?_⟩
      rw [pw_add, ← hi, ← hj]; exact h1
    · -- u = v ++ t and u = t ++ v
      have hlen : u.length = v.length + t.length := by rw [h1]; simp
      obtain ⟨z, i, j, hi, hj⟩ := ih v t (by omega) (h1.symm.trans h2)
      refine ⟨z, i + j, i, ?_, hi⟩
      rw [pw_add, ← hi, ← hj]; exact h1

/-- A commuting product of nonempty strings is a proper power. -/
theorem comm_proper (u v : List Bool) (hu : u ≠ []) (hv : v ≠ []) (huv : u ++ v = v ++ u) :
    ∃ (z : List Bool) (k : ℕ), 2 ≤ k ∧ u ++ v = pw z k := by
  obtain ⟨z, i, j, hi, hj⟩ := comm_pow _ u v le_rfl huv
  have i0 : i ≠ 0 := by
    rintro rfl; exact hu (by rw [hi, pw_zero])
  have j0 : j ≠ 0 := by
    rintro rfl; exact hv (by rw [hj, pw_zero])
  refine ⟨z, i + j, by omega, ?_⟩
  rw [pw_add, ← hi, ← hj]

/-- A nonempty palindrome that is a proper power is a product of two nonempty palindromes. -/
theorem power_split (z : List Bool) (k : ℕ) (hk : 2 ≤ k) (hne : pw z k ≠ [])
    (hp : IsPal (pw z k)) :
    ∃ u v : List Bool, u ≠ [] ∧ v ≠ [] ∧ IsPal u ∧ IsPal v ∧ pw z k = u ++ v := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  have hz : z ≠ [] := by
    rintro rfl; exact hne (pw_nil _)
  have hzp : z.reverse = z := by
    have h := hp
    unfold IsPal at h
    rw [pw_reverse, pw_succ, pw_succ z] at h
    exact (List.append_inj h (List.length_reverse)).1
  refine ⟨z, pw z (k + 1), hz, ?_, hzp, ?_, pw_succ z (k + 1)⟩
  · rw [pw_succ]; simp [hz]
  · unfold IsPal; rw [pw_reverse, hzp]

theorem key (n : ℕ) (hn : 1 ≤ n) : a n + A056458 n = A007055 n := by
  unfold a A056458 A007055
  set A : Set (List Bool) := {w : List Bool | w.length = n ∧
    ∃ u v : List Bool, u ≠ [] ∧ v ≠ [] ∧ IsPal u ∧ IsPal v ∧ w = u ++ v} with hA
  set B : Set (List Bool) := {w : List Bool | w.length = n ∧ IsPal w ∧ IsPrimitive w} with hB
  set C : Set (List Bool) :=
    {w : List Bool | w.length = n ∧ ∃ u v : List Bool, IsPal u ∧ IsPal v ∧ w = u ++ v} with hC
  have hfin : {w : List Bool | w.length = n}.Finite := List.finite_length_eq Bool n
  have hAf : A.Finite := hfin.subset (fun w hw => hw.1)
  have hBf : B.Finite := hfin.subset (fun w hw => hw.1)
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro w ⟨_, u, v, hu, hv, hup, hvp, rfl⟩ ⟨_, hwp, _, hprim⟩
    apply hprim
    have hcomm : u ++ v = v ++ u := by
      have h := hwp
      unfold IsPal at h hup hvp
      rw [List.reverse_append, hup, hvp] at h
      exact h.symm
    exact comm_proper u v hu hv hcomm
  have hunion : C = A ∪ B := by
    ext w
    constructor
    · rintro ⟨hl, u, v, hup, hvp, rfl⟩
      by_cases hmem : (u ++ v) ∈ A
      · exact Or.inl hmem
      right
      have hwne : u ++ v ≠ [] := by
        intro h0; rw [h0] at hl; simp at hl; omega
      have hpal : IsPal (u ++ v) := by
        by_cases hu : u = []
        · simpa [hu] using hvp
        by_cases hv : v = []
        · simpa [hv] using hup
        exact absurd ⟨hl, u, v, hu, hv, hup, hvp, rfl⟩ hmem
      refine ⟨hl, hpal, hwne, ?_⟩
      rintro ⟨z, k, hk, hzk⟩
      apply hmem
      refine ⟨hl, ?_⟩
      rw [hzk] at hwne hpal ⊢
      exact power_split z k hk hwne hpal
    · rintro (⟨hl, u, v, _, _, hup, hvp, rfl⟩ | ⟨hl, hwp, _⟩)
      · exact ⟨hl, u, v, hup, hvp, rfl⟩
      · exact ⟨hl, w, [], hwp, rfl, by simp⟩
  rw [hunion, Set.ncard_union_eq hdisj hAf hBf]

end A370410

theorem OMA.solution : type_of% @OMA.S_oeis_a370410.main := by
  intro n hn
  have h := A370410.key n hn
  refine ⟨h, ?_⟩
  rw [← h]; push_cast; ring
