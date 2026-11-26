import FormalConjectures.ErdosProblems.«1074»

-- Problem: Erdős Problem 1074 — PillaiPrimes init
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1074.lean:128 (declaration Erdos1074.erdos_1074.variants.PillaiPrimes_init)
-- Credit: @Slayzkami (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E1074P

open Nat Erdos1074

lemma charac (n : ℕ) : n ∈ PillaiPrimes ↔
    (n.Prime ∧ ∃ m < n, 1 ≤ m ∧ ¬ n % m = 1 % m ∧ n ∣ m ! + 1) := by
  constructor
  · rintro ⟨hp, m, hm, hne, hd⟩
    refine ⟨hp, m, ?_, hm, hne, hd⟩
    by_contra hmn
    push_neg at hmn
    have h1 : n ∣ m ! := Nat.dvd_factorial hp.pos hmn
    have h2 : n ∣ 1 := (Nat.dvd_add_right h1).1 hd
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  · rintro ⟨hp, m, -, hm, hne, hd⟩
    exact ⟨hp, m, hm, hne, hd⟩

set_option maxRecDepth 100000 in
lemma table : ∀ n < 72, (n.Prime ∧ ∃ m < n, 1 ≤ m ∧ ¬ n % m = 1 % m ∧ n ∣ m ! + 1) ↔
    n ∈ ({23, 29, 59, 61, 67, 71} : Finset ℕ) := by
  decide

lemma mem_iff (n : ℕ) (hn : n < 72) :
    n ∈ PillaiPrimes ↔ n ∈ ({23, 29, 59, 61, 67, 71} : Finset ℕ) :=
  (charac n).trans (table n hn)

def P : ℕ → Prop := fun n => n ∈ PillaiPrimes

lemma count_eq [DecidablePred P] (k : ℕ) (hk : k ≤ 72) :
    count P k = ((Finset.range k).filter (· ∈ ({23, 29, 59, 61, 67, 71} : Finset ℕ))).card := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro n hn
  rw [Finset.mem_range] at hn
  exact mem_iff n (by omega)

lemma memP (n : ℕ) (hn : n < 72) (h : n ∈ ({23, 29, 59, 61, 67, 71} : Finset ℕ)) : P n :=
  (mem_iff n hn).2 h

end OMA.E1074P

open OMA.E1074P in
theorem OMA.solution : type_of% @Erdos1074.erdos_1074.variants.PillaiPrimes_init := by
  classical
  have h0 : Nat.nth P 0 = 23 := by
    have := Nat.nth_count (p := P) (memP 23 (by norm_num) (by decide))
    rwa [count_eq 23 (by norm_num)] at this
  have h1 : Nat.nth P 1 = 29 := by
    have := Nat.nth_count (p := P) (memP 29 (by norm_num) (by decide))
    rwa [count_eq 29 (by norm_num)] at this
  have h2 : Nat.nth P 2 = 59 := by
    have := Nat.nth_count (p := P) (memP 59 (by norm_num) (by decide))
    rwa [count_eq 59 (by norm_num)] at this
  have h3 : Nat.nth P 3 = 61 := by
    have := Nat.nth_count (p := P) (memP 61 (by norm_num) (by decide))
    rwa [count_eq 61 (by norm_num)] at this
  have h4 : Nat.nth P 4 = 67 := by
    have := Nat.nth_count (p := P) (memP 67 (by norm_num) (by decide))
    rwa [count_eq 67 (by norm_num)] at this
  have h5 : Nat.nth P 5 = 71 := by
    have := Nat.nth_count (p := P) (memP 71 (by norm_num) (by decide))
    rwa [count_eq 71 (by norm_num)] at this
  change Nat.nth P '' Set.Icc 0 5 = _
  ext x
  simp only [Set.mem_image, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, ⟨-, hk⟩, rfl⟩
    interval_cases k <;> simp [h0, h1, h2, h3, h4, h5]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num, h0⟩
    · exact ⟨1, by norm_num, h1⟩
    · exact ⟨2, by norm_num, h2⟩
    · exact ⟨3, by norm_num, h3⟩
    · exact ⟨4, by norm_num, h4⟩
    · exact ⟨5, by norm_num, h5⟩
