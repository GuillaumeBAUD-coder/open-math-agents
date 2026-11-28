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
  have nth_of_table (n i : ℕ) (hn : n < 72)
      (hm : n ∈ ({23, 29, 59, 61, 67, 71} : Finset ℕ))
      (hi : ((Finset.range n).filter (· ∈ ({23, 29, 59, 61, 67, 71} : Finset ℕ))).card = i) :
      Nat.nth P i = n := by
    have h := Nat.nth_count (p := P) (memP n hn hm)
    rwa [count_eq n (by omega), hi] at h
  have h0 := nth_of_table 23 0 (by decide) (by decide) (by decide)
  have h1 := nth_of_table 29 1 (by decide) (by decide) (by decide)
  have h2 := nth_of_table 59 2 (by decide) (by decide) (by decide)
  have h3 := nth_of_table 61 3 (by decide) (by decide) (by decide)
  have h4 := nth_of_table 67 4 (by decide) (by decide) (by decide)
  have h5 := nth_of_table 71 5 (by decide) (by decide) (by decide)
  change Nat.nth P '' Set.Icc 0 5 = _
  have hI : Set.Icc 0 5 = ({0, 1, 2, 3, 4, 5} : Set ℕ) := by
    ext i
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [hI]
  simp [Set.image_insert_eq, h0, h1, h2, h3, h4, h5]
