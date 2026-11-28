import FormalConjectures.ErdosProblems.«1074»

open Nat Erdos1074 in
theorem OMA.solution : type_of% @Erdos1074.erdos_1074.variants.PillaiPrimes_init := by
  classical
  have T : ∀ n < 72, n ∈ PillaiPrimes ↔ n ∈ ({23, 29, 59, 61, 67, 71} : Finset ℕ) := by
    refine fun n hn => Iff.trans (b := n.Prime ∧ ∃ m < n, 1 ≤ m ∧ ¬ n ≡ 1 [MOD m] ∧ n ∣ m ! + 1)
      ⟨fun ⟨hp, m, hm, hne, hd⟩ => ⟨hp, m, lt_of_not_ge fun h =>
        hp.not_dvd_one ((Nat.dvd_add_right (hp.dvd_factorial.2 h)).1 hd), hm, hne, hd⟩,
        fun ⟨hp, m, _, hm, hne, hd⟩ => ⟨hp, m, hm, hne, hd⟩⟩ ?_
    revert n
    set_option maxRecDepth 100000 in decide
  have c : count (· ∈ PillaiPrimes) 72 = 6 := by
    rw [count_eq_card_filter_range, Finset.filter_congr fun n hn => T n (Finset.mem_range.1 hn)]
    decide
  have e : ({23, 29, 59, 61, 67, 71} : Finset ℕ) = (Finset.Icc 0 5).image (nth (· ∈ PillaiPrimes)) :=
    Finset.eq_of_subset_of_card_le (fun p hp => by
      have hs : p < 72 := by simp at hp; omega
      have h := count_strict_mono (p := (· ∈ PillaiPrimes)) ((T p hs).2 hp) hs
      rw [c] at h
      exact Finset.mem_image.2 ⟨_, Finset.mem_Icc.2 ⟨zero_le _, by omega⟩, nth_count (p := (· ∈ PillaiPrimes)) ((T p hs).2 hp)⟩)
      (Finset.card_image_le.trans (by decide))
  change nth (· ∈ PillaiPrimes) '' _ = _
  rw [← Finset.coe_Icc, ← Finset.coe_image]
  rw [← e]
  simp
