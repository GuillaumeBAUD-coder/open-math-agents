import OMAStatements.S_oeis_a383501

/-!
# Repdigits 88...8 connect every two terms

Adapted from the accepted proof of the sibling entry A383246. A repdigit of eights starts
with the even digit 8, so it may follow every term. It ends with 8, so every admissible number
may follow it. Fresh repdigits keep the recursion defined, and omitting one forever would
bound the injective sequence. A repdigit chosen sufficiently late then forces any omitted
admissible value to bound a later choice, contradicting finiteness of the smaller choices.
-/

namespace OMA.A383501

open OMA.S_oeis_a383501

/-- A repdigit of eights of length k + 1. -/
private def conn (k : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate (k + 1) 8)

private lemma conn_digits (k : ℕ) :
    Nat.digits 10 (conn k) = List.replicate (k + 1) 8 := by
  apply Nat.digits_ofDigits 10 (by decide)
  · intro x hx
    have hx' : x = 8 := (List.mem_replicate.mp hx).2
    omega
  · intro h
    simp

private lemma infinite_conn : (Set.range conn).Infinite := by
  apply Set.infinite_range_of_injective
  intro i j hij
  have h := congrArg (fun x => (Nat.digits 10 x).length) hij
  simp only [conn_digits, List.length_replicate] at h
  omega

private lemma conn_admissible (k : ℕ) : admissible (conn k) := by
  refine ⟨?_, ?_⟩
  · rw [conn_digits]
    simp
  · rw [conn_digits, List.reverse_replicate]
    exact List.isChain_replicate_of_rel _ (by norm_num [digitStep] : digitStep 8 8)

private lemma before_conn (previous k : ℕ) : follows previous (conn k) := by
  rw [follows, firstDigit, conn_digits, List.reverse_replicate,
    List.replicate_succ, List.headD_cons]
  unfold digitStep
  omega

private lemma firstDigit_le {m : ℕ} (hm : admissible m) : firstDigit m ≤ 8 := by
  unfold firstDigit
  cases h : (Nat.digits 10 m).reverse with
  | nil => simp
  | cons d l =>
    have hd : d ∈ Nat.digits 10 m := List.mem_reverse.mp (h ▸ List.mem_cons_self ..)
    have h1 := Nat.digits_lt_base (by norm_num) hd
    have h2 : d ≠ 9 := fun h9 => hm.1 (h9 ▸ hd)
    simp only [List.headD_cons]
    omega

private lemma after_conn (k m : ℕ) (hm : admissible m) : follows (conn k) m := by
  have h := firstDigit_le hm
  simp only [follows, lastDigit, conn_digits, List.replicate_succ, List.headD_cons, digitStep]
  omega

private lemma state_step (n : ℕ) :
    state (n + 1) = (insert (a (n + 1)) (state n).1, a (n + 1)) := rfl

private lemma a_succ (n : ℕ) : a (n + 1) = next (state n).1 (a n) := rfl

private lemma next_spec (used : Finset ℕ) (previous : ℕ) :
    admissible (next used previous) ∧ next used previous ∉ used ∧
      follows previous (next used previous) := by
  obtain ⟨_, ⟨k, rfl⟩, hfresh⟩ := infinite_conn.exists_notMem_finset used
  exact Nat.sInf_mem (s := {v | admissible v ∧ v ∉ used ∧ follows previous v})
    ⟨conn k, conn_admissible k, hfresh, before_conn _ k⟩

private lemma a_zero : a 0 = 0 := rfl

private lemma admissible_zero : admissible 0 := by
  refine ⟨by simp, ?_⟩
  simp

private lemma a_admissible (n : ℕ) : admissible (a n) := by
  cases n with
  | zero => exact admissible_zero
  | succ n =>
    rw [a_succ]
    exact (next_spec (state n).1 (a n)).1

private lemma step_spec (n : ℕ) :
    a (n + 1) ∉ (state n).1 ∧ follows (a n) (a (n + 1)) := by
  have h := next_spec (state n).1 (a n)
  exact ⟨h.2.1, h.2.2⟩

private lemma step_le (n m : ℕ) (hm : admissible m) (hfresh : m ∉ (state n).1)
    (hfollow : follows (a n) m) : a (n + 1) ≤ m := by
  exact Nat.sInf_le (s := {v | admissible v ∧ v ∉ (state n).1 ∧ follows (a n) v})
    ⟨hm, hfresh, hfollow⟩

private lemma used_mono : Monotone (fun n => (state n).1) := by
  apply monotone_nat_of_le_succ
  intro n m hm
  rw [state_step]
  exact Finset.mem_insert_of_mem hm

private lemma used_self (n : ℕ) : a n ∈ (state n).1 := by
  cases n with
  | zero => simp [a, state]
  | succ n => rw [state_step]; exact Finset.mem_insert_self _ _

private lemma used_occurs {m : ℕ} (n : ℕ) (hm : m ∈ (state n).1) : ∃ i, a i = m := by
  induction n with
  | zero =>
    simp only [state, Finset.mem_singleton] at hm
    exact ⟨0, hm.symm⟩
  | succ n ih =>
    rw [state_step, Finset.mem_insert] at hm
    rcases hm with h | h
    · exact ⟨n + 1, h.symm⟩
    · exact ih h

private lemma injective_a : Function.Injective a := by
  have distinct (i j : ℕ) (hij : i < j) : a i ≠ a j := by
    intro h
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact (step_spec j').1 (h ▸ used_mono (by omega : i ≤ j') (used_self i))
  intro i j h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (distinct i j hij h)
  · exact hij
  · exact False.elim (distinct j i hij h.symm)

private lemma conn_occurs (k : ℕ) : ∃ i, a i = conn k := by
  by_contra h
  have hbound : Set.range a ⊆ Set.Iic (conn k) := by
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => rw [a_zero]; exact Nat.zero_le _
    | succ n =>
      exact step_le n _ (conn_admissible k) (fun hf => h (used_occurs n hf))
        (before_conn _ k)
  exact (Set.infinite_range_of_injective injective_a) ((Set.finite_Iic _).subset hbound)

private lemma admissible_occurs (m : ℕ) (hm : admissible m) : ∃ i, a i = m := by
  by_contra h
  have hfinite : {i | a i ≤ m}.Finite :=
    (Set.finite_Iic m).preimage injective_a.injOn
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  obtain ⟨_, ⟨k, rfl⟩, hfresh⟩ := infinite_conn.exists_notMem_finset (state N).1
  obtain ⟨i, hi⟩ := conn_occurs k
  have hiN : N < i := by
    by_contra! hle
    apply hfresh
    rw [← hi]
    exact used_mono hle (used_self i)
  have hle : a (i + 1) ≤ m :=
    step_le i m hm (fun hf => h (used_occurs i hf)) (hi ▸ after_conn k m hm)
  have hindex : i + 1 ≤ N := hN hle
  omega

end OMA.A383501

theorem OMA.solution : type_of% @OMA.S_oeis_a383501.main := by
  refine ⟨A383501.injective_a, fun m => ⟨?_, A383501.admissible_occurs m⟩⟩
  rintro ⟨n, rfl⟩
  exact A383501.a_admissible n
