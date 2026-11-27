import OMAStatements.S_oeis_a267262

-- Complete proof of OEIS A267262 (Rule 111 OFF cells, Barker's conjectures)
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v5

open OMA.S_oeis_a267262 PowerSeries

private lemma rule111_eq (l c x : Bool) : rule 111 l c x = (!l || (c != x)) := by
  cases l <;> cases c <;> cases x <;> decide

private lemma row_succ (n : ℕ) (i : ℤ) :
    row 111 (n + 1) i = rule 111 (row 111 n (i - 1)) (row 111 n i) (row 111 n (i + 1)) := rfl

private lemma row0 (i : ℤ) : row 111 0 i = decide (i = 0) := rfl

private lemma row1 (i : ℤ) : row 111 1 i = decide (i ≠ 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, row_succ, rule111_eq, row0, row0, row0]
  by_cases h1 : i = 1
  · subst h1; decide
  · have h0 : i - 1 ≠ 0 := by omega
    simp [h1, h0]

private lemma row2 (i : ℤ) : row 111 2 i = decide (i = 0 ∨ i = 1 ∨ i = 2) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, row_succ, rule111_eq, row1, row1, row1]
  by_cases h0 : i = 0
  · subst h0; decide
  · by_cases h1 : i = 1
    · subst h1; decide
    · by_cases h2 : i = 2
      · subst h2; decide
      · have ha : i - 1 ≠ 1 := by omega
        have hb : i + 1 ≠ 1 := by omega
        simp [h0, h1, h2, ha, hb]

private lemma row3 (i : ℤ) : row 111 3 i = decide (i ≠ 1 ∧ i ≠ 3) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, row_succ, rule111_eq, row2, row2, row2]
  by_cases h1 : i = 1
  · subst h1; decide
  · by_cases h2 : i = 2
    · subst h2; decide
    · by_cases h3 : i = 3
      · subst h3; decide
      · have ha : i - 1 ≠ 0 := by omega
        have hb : i - 1 ≠ 1 := by omega
        have hc : i - 1 ≠ 2 := by omega
        simp [h1, h3, ha, hb, hc]

private lemma row4 (i : ℤ) :
    row 111 4 i = decide (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, row_succ, rule111_eq, row3, row3, row3]
  by_cases h : 0 ≤ i ∧ i ≤ 4
  · have hd : (i - 0).toNat ≤ 4 := by omega
    have hi : i = ((i - 0).toNat : ℤ) := by omega
    rw [hi]
    generalize (i - 0).toNat = d at hd
    interval_cases d <;> decide
  · have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    have h2 : i ≠ 2 := by omega
    have h3 : i ≠ 3 := by omega
    have h4 : i ≠ 4 := by omega
    have ha : i - 1 ≠ 1 := by omega
    have hb : i - 1 ≠ 3 := by omega
    have hc : i + 1 ≠ 1 := by omega
    have hd : i + 1 ≠ 3 := by omega
    simp [h0, h1, h2, h3, h4, ha, hb, hc, hd]

private lemma row5 (i : ℤ) :
    row 111 5 i = decide (i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 5) := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, row_succ, rule111_eq, row4, row4, row4]
  by_cases h : 1 ≤ i ∧ i ≤ 5
  · have hd : (i - 1).toNat ≤ 4 := by omega
    have hi : i = ((i - 1).toNat : ℤ) + 1 := by omega
    rw [hi]
    generalize (i - 1).toNat = d at hd
    interval_cases d <;> decide
  · have h1 : i ≠ 1 := by omega
    have h2 : i ≠ 2 := by omega
    have h3 : i ≠ 3 := by omega
    have h5 : i ≠ 5 := by omega
    have ha : i - 1 ≠ 0 := by omega
    have hb : i - 1 ≠ 1 := by omega
    have hc : i - 1 ≠ 2 := by omega
    have hd : i - 1 ≠ 3 := by omega
    have he : i - 1 ≠ 4 := by omega
    simp [h1, h2, h3, h5, ha, hb, hc, hd, he]

private lemma step_odd_to_even (m : ℤ) (f : ℤ → Bool)
    (hf : ∀ i : ℤ, f i = decide (i ≠ m + 1 ∧ i ≠ m + 2 ∧ i ≠ m + 3 ∧ i ≠ m + 5))
    (i : ℤ) :
    rule 111 (f (i - 1)) (f i) (f (i + 1)) =
      decide (i = m ∨ i = m + 2 ∨ i = m + 3 ∨ i = m + 4 ∨ i = m + 5 ∨ i = m + 6) := by
  rw [rule111_eq, hf, hf, hf]
  by_cases h : m ≤ i ∧ i ≤ m + 6
  · have hd : (i - m).toNat ≤ 6 := by omega
    have hi : i = m + ((i - m).toNat : ℤ) := by omega
    rw [hi]
    generalize (i - m).toNat = d at hd
    interval_cases d <;>
      simp [show ∀ a b : ℤ, (m + a = m + b) ↔ a = b by intro a b; omega,
            show ∀ a : ℤ, (m + a - 1 = m + 1) ↔ a = 2 by intro a; omega,
            show ∀ a : ℤ, (m + a - 1 = m + 2) ↔ a = 3 by intro a; omega,
            show ∀ a : ℤ, (m + a - 1 = m + 3) ↔ a = 4 by intro a; omega,
            show ∀ a : ℤ, (m + a - 1 = m + 5) ↔ a = 6 by intro a; omega,
            show ∀ a : ℤ, (m + a + 1 = m + 1) ↔ a = 0 by intro a; omega,
            show ∀ a : ℤ, (m + a + 1 = m + 2) ↔ a = 1 by intro a; omega,
            show ∀ a : ℤ, (m + a + 1 = m + 3) ↔ a = 2 by intro a; omega,
            show ∀ a : ℤ, (m + a + 1 = m + 5) ↔ a = 4 by intro a; omega]
  · have h0 : i ≠ m := by omega
    have h2 : i ≠ m + 2 := by omega
    have h3 : i ≠ m + 3 := by omega
    have h4 : i ≠ m + 4 := by omega
    have h5 : i ≠ m + 5 := by omega
    have h6 : i ≠ m + 6 := by omega
    have h1 : i ≠ m + 1 := by omega
    have hl1 : i - 1 ≠ m + 1 := by omega
    have hl2 : i - 1 ≠ m + 2 := by omega
    have hl3 : i - 1 ≠ m + 3 := by omega
    have hl5 : i - 1 ≠ m + 5 := by omega
    have hr1 : i + 1 ≠ m + 1 := by omega
    have hr2 : i + 1 ≠ m + 2 := by omega
    have hr3 : i + 1 ≠ m + 3 := by omega
    have hr5 : i + 1 ≠ m + 5 := by omega
    simp [h0, h1, h2, h3, h4, h5, h6, hl1, hl2, hl3, hl5, hr1, hr2, hr3, hr5]

private lemma step_even_to_odd (m : ℤ) (f : ℤ → Bool)
    (hf : ∀ i : ℤ, f i =
      decide (i = m ∨ i = m + 2 ∨ i = m + 3 ∨ i = m + 4 ∨ i = m + 5 ∨ i = m + 6))
    (i : ℤ) :
    rule 111 (f (i - 1)) (f i) (f (i + 1)) =
      decide (i ≠ m + 3 ∧ i ≠ m + 4 ∧ i ≠ m + 5 ∧ i ≠ m + 7) := by
  rw [rule111_eq, hf, hf, hf]
  by_cases h : m + 1 ≤ i ∧ i ≤ m + 7
  · have hd : (i - (m + 1)).toNat ≤ 6 := by omega
    have hi : i = m + ((i - (m + 1)).toNat : ℤ) + 1 := by omega
    rw [hi]
    generalize (i - (m + 1)).toNat = d at hd
    interval_cases d <;>
      simp [show ∀ a : ℤ, (m + a + 1 = m) ↔ a = -1 by intro a; omega,
            show ∀ a b : ℤ, (m + a + 1 = m + b) ↔ a + 1 = b by intro a b; omega,
            show ∀ a : ℤ, (m + a + 1 + 1 = m) ↔ a = -2 by intro a; omega,
            show ∀ a b : ℤ, (m + a + 1 + 1 = m + b) ↔ a + 2 = b by intro a b; omega]
  · have h3 : i ≠ m + 3 := by omega
    have h4 : i ≠ m + 4 := by omega
    have h5 : i ≠ m + 5 := by omega
    have h7 : i ≠ m + 7 := by omega
    have hl0 : i - 1 ≠ m := by omega
    have hl2 : i - 1 ≠ m + 2 := by omega
    have hl3 : i - 1 ≠ m + 3 := by omega
    have hl4 : i - 1 ≠ m + 4 := by omega
    have hl5 : i - 1 ≠ m + 5 := by omega
    have hl6 : i - 1 ≠ m + 6 := by omega
    simp [h3, h4, h5, h7, hl0, hl2, hl3, hl4, hl5, hl6]

private lemma row_odd_even :
    ∀ k : ℕ,
      (∀ i : ℤ, row 111 (2 * k + 5) i =
        decide (i ≠ (2 * k : ℤ) + 1 ∧ i ≠ (2 * k : ℤ) + 2 ∧
                i ≠ (2 * k : ℤ) + 3 ∧ i ≠ (2 * k : ℤ) + 5)) ∧
      (∀ i : ℤ, row 111 (2 * k + 6) i =
        decide (i = (2 * k : ℤ) ∨ i = (2 * k : ℤ) + 2 ∨ i = (2 * k : ℤ) + 3 ∨
                i = (2 * k : ℤ) + 4 ∨ i = (2 * k : ℤ) + 5 ∨ i = (2 * k : ℤ) + 6))
  | 0 => by
    have h5 : ∀ i : ℤ, row 111 5 i =
        decide (i ≠ (0 : ℤ) + 1 ∧ i ≠ (0 : ℤ) + 2 ∧ i ≠ (0 : ℤ) + 3 ∧ i ≠ (0 : ℤ) + 5) := by
      intro i; simpa using row5 i
    refine ⟨by simpa using h5, ?_⟩
    intro i
    rw [show 2 * 0 + 6 = 5 + 1 from rfl, row_succ]
    simpa using step_odd_to_even 0 (row 111 5) h5 i
  | k + 1 => by
    obtain ⟨_, heven⟩ := row_odd_even k
    have hodd : ∀ i : ℤ, row 111 (2 * (k + 1) + 5) i =
        decide (i ≠ (2 * (k + 1) : ℤ) + 1 ∧ i ≠ (2 * (k + 1) : ℤ) + 2 ∧
                i ≠ (2 * (k + 1) : ℤ) + 3 ∧ i ≠ (2 * (k + 1) : ℤ) + 5) := by
      intro i
      rw [show 2 * (k + 1) + 5 = (2 * k + 6) + 1 by omega, row_succ]
      have hst := step_even_to_odd (2 * k : ℤ) (row 111 (2 * k + 6)) heven i
      rw [hst]
      have h1 : (2 * (k + 1) : ℤ) + 1 = (2 * k : ℤ) + 3 := by ring
      have h2 : (2 * (k + 1) : ℤ) + 2 = (2 * k : ℤ) + 4 := by ring
      have h3 : (2 * (k + 1) : ℤ) + 3 = (2 * k : ℤ) + 5 := by ring
      have h5 : (2 * (k + 1) : ℤ) + 5 = (2 * k : ℤ) + 7 := by ring
      rw [h1, h2, h3, h5]
    refine ⟨hodd, ?_⟩
    intro i
    rw [show 2 * (k + 1) + 6 = (2 * (k + 1) + 5) + 1 by omega, row_succ]
    exact step_odd_to_even (2 * (k + 1) : ℤ) (row 111 (2 * (k + 1) + 5)) hodd i

private lemma off_0 : off 0 = 0 := by
  unfold off
  have h : (Finset.range (2 * 0 + 1)).filter
      (fun k : ℕ => row 111 0 ((k : ℤ) - (0 : ℕ)) = false) = ∅ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, row0, decide_eq_false_iff_not,
      Finset.notMem_empty, iff_false]
    omega
  rw [h, Finset.card_empty]

private lemma off_1 : off 1 = 1 := by
  unfold off
  have h : (Finset.range (2 * 1 + 1)).filter
      (fun k : ℕ => row 111 1 ((k : ℤ) - (1 : ℕ)) = false) = {2} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, row1, decide_eq_false_iff_not,
      Finset.mem_singleton]
    omega
  rw [h, Finset.card_singleton]

private lemma off_2 : off 2 = 2 := by
  unfold off
  have h : (Finset.range (2 * 2 + 1)).filter
      (fun k : ℕ => row 111 2 ((k : ℤ) - (2 : ℕ)) = false) = {0, 1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, row2, decide_eq_false_iff_not,
      Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h]; decide

private lemma off_3 : off 3 = 2 := by
  unfold off
  have h : (Finset.range (2 * 3 + 1)).filter
      (fun k : ℕ => row 111 3 ((k : ℤ) - (3 : ℕ)) = false) = {4, 6} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, row3, decide_eq_false_iff_not,
      Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h]; decide

private lemma off_4 : off 4 = 4 := by
  unfold off
  have h : (Finset.range (2 * 4 + 1)).filter
      (fun k : ℕ => row 111 4 ((k : ℤ) - (4 : ℕ)) = false) = {0, 1, 2, 3} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, row4, decide_eq_false_iff_not,
      Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h]; decide

private lemma off_odd (k : ℕ) : off (2 * k + 5) = 4 := by
  unfold off
  have h : (Finset.range (2 * (2 * k + 5) + 1)).filter
      (fun j : ℕ => row 111 (2 * k + 5) ((j : ℤ) - (2 * k + 5 : ℕ)) = false) =
      {4 * k + 6, 4 * k + 7, 4 * k + 8, 4 * k + 10} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, (row_odd_even k).1,
      decide_eq_false_iff_not, Finset.mem_insert, Finset.mem_singleton]
    omega
  have h1 : 4 * k + 6 ∉ ({4 * k + 7, 4 * k + 8, 4 * k + 10} : Finset ℕ) := by simp
  have h2 : 4 * k + 7 ∉ ({4 * k + 8, 4 * k + 10} : Finset ℕ) := by simp
  have h3 : 4 * k + 8 ∉ ({4 * k + 10} : Finset ℕ) := by simp
  rw [h, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]

private lemma off_even (k : ℕ) : off (2 * k + 6) = 4 * k + 7 := by
  unfold off
  have hcomp :
      ((Finset.range (2 * (2 * k + 6) + 1)).filter
        (fun j : ℕ => row 111 (2 * k + 6) ((j : ℤ) - (2 * k + 6 : ℕ)) = false)).card +
      ((Finset.range (2 * (2 * k + 6) + 1)).filter
        (fun j : ℕ => ¬ row 111 (2 * k + 6) ((j : ℤ) - (2 * k + 6 : ℕ)) = false)).card =
      (Finset.range (2 * (2 * k + 6) + 1)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext j
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    · rw [Finset.disjoint_filter]
      intro j _ h1 h2
      exact h2 h1
  have hneg : (Finset.range (2 * (2 * k + 6) + 1)).filter
      (fun j : ℕ => ¬ row 111 (2 * k + 6) ((j : ℤ) - (2 * k + 6 : ℕ)) = false) =
      {4 * k + 6, 4 * k + 8, 4 * k + 9, 4 * k + 10, 4 * k + 11, 4 * k + 12} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, (row_odd_even k).2,
      Bool.not_eq_false, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
    omega
  have h1 : 4 * k + 6 ∉ ({4 * k + 8, 4 * k + 9, 4 * k + 10, 4 * k + 11, 4 * k + 12} : Finset ℕ) := by
    simp
  have h2 : 4 * k + 8 ∉ ({4 * k + 9, 4 * k + 10, 4 * k + 11, 4 * k + 12} : Finset ℕ) := by
    simp
  have h3 : 4 * k + 9 ∉ ({4 * k + 10, 4 * k + 11, 4 * k + 12} : Finset ℕ) := by simp
  have h4 : 4 * k + 10 ∉ ({4 * k + 11, 4 * k + 12} : Finset ℕ) := by simp
  have h5 : 4 * k + 11 ∉ ({4 * k + 12} : Finset ℕ) := by simp
  have hcard_neg : ((Finset.range (2 * (2 * k + 6) + 1)).filter
      (fun j : ℕ => ¬ row 111 (2 * k + 6) ((j : ℤ) - (2 * k + 6 : ℕ)) = false)).card = 6 := by
    rw [hneg, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h4,
        Finset.card_insert_of_notMem h5, Finset.card_singleton]
  rw [hcard_neg, Finset.card_range] at hcomp
  omega

private lemma a_succ (n : ℕ) : a (n + 1) = a n + off (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]

private lemma a_0 : a 0 = 0 := by unfold a; simp [off_0]
private lemma a_1 : a 1 = 1 := by rw [a_succ 0, a_0, off_1]
private lemma a_2 : a 2 = 3 := by rw [a_succ 1, a_1, off_2]
private lemma a_3 : a 3 = 5 := by rw [a_succ 2, a_2, off_3]
private lemma a_4 : a 4 = 9 := by rw [a_succ 3, a_3, off_4]

private lemma a_even_odd_ge4 :
    ∀ k : ℕ, a (2 * k + 4) = 2 * k ^ 2 + 9 * k + 9 ∧ a (2 * k + 5) = 2 * k ^ 2 + 9 * k + 13
  | 0 => by
    constructor
    · simpa using a_4
    · rw [show 2 * 0 + 5 = 4 + 1 from rfl, a_succ 4, a_4,
          show (4 + 1 : ℕ) = 2 * 0 + 5 from rfl, off_odd 0]
      norm_num
  | k + 1 => by
    obtain ⟨_, hodd⟩ := a_even_odd_ge4 k
    have hev : a (2 * (k + 1) + 4) = 2 * (k + 1) ^ 2 + 9 * (k + 1) + 9 := by
      rw [show 2 * (k + 1) + 4 = (2 * k + 5) + 1 by omega, a_succ, hodd,
          show (2 * k + 5) + 1 = 2 * k + 6 by omega, off_even k]
      ring
    refine ⟨hev, ?_⟩
    rw [show 2 * (k + 1) + 5 = (2 * (k + 1) + 4) + 1 by omega, a_succ, hev,
        show (2 * (k + 1) + 4) + 1 = 2 * (k + 1) + 5 by omega, off_odd (k + 1)]

private lemma a_closed (n : ℕ) (hn : 3 < n) :
    2 * (a n : ℤ) = (n : ℤ) ^ 2 + (-1 : ℤ) ^ n * ((n : ℤ) - 4) + 2 := by
  have hge : 4 ≤ n := by omega
  rcases Nat.even_or_odd (n - 4) with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hn_eq : n = 2 * k + 4 := by omega
    rw [hn_eq, (a_even_odd_ge4 k).1]
    have hp : (-1 : ℤ) ^ (2 * k + 4) = 1 := by
      rw [show 2 * k + 4 = 2 * (k + 2) by omega, pow_mul]; norm_num
    rw [hp]; push_cast; ring
  · have hn_eq : n = 2 * k + 5 := by omega
    rw [hn_eq, (a_even_odd_ge4 k).2]
    have hp : (-1 : ℤ) ^ (2 * k + 5) = -1 := by
      rw [show 2 * k + 5 = 2 * (k + 2) + 1 by omega, pow_succ, pow_mul]; norm_num
    rw [hp]; push_cast; ring

private lemma a_rec (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  have h0 := a_closed n (by omega)
  have h1 := a_closed (n - 1) (by omega)
  have h2 := a_closed (n - 2) (by omega)
  have h3 := a_closed (n - 3) (by omega)
  have h4 := a_closed (n - 4) (by omega)
  have h5 := a_closed (n - 5) (by omega)
  have c1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have c2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have c3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  have c4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
  have c5 : ((n - 5 : ℕ) : ℤ) = (n : ℤ) - 5 := by omega
  have p0 : (-1 : ℤ) ^ n = -((-1 : ℤ) ^ (n - 5)) := by
    conv_lhs => rw [show n = (n - 5) + 5 by omega, pow_add]
    norm_num
  have p1 : (-1 : ℤ) ^ (n - 1) = (-1 : ℤ) ^ (n - 5) := by
    conv_lhs => rw [show n - 1 = (n - 5) + 4 by omega, pow_add]
    norm_num
  have p2 : (-1 : ℤ) ^ (n - 2) = -((-1 : ℤ) ^ (n - 5)) := by
    conv_lhs => rw [show n - 2 = (n - 5) + 3 by omega, pow_add]
    norm_num
  have p3 : (-1 : ℤ) ^ (n - 3) = (-1 : ℤ) ^ (n - 5) := by
    conv_lhs => rw [show n - 3 = (n - 5) + 2 by omega, pow_add]
    norm_num
  have p4 : (-1 : ℤ) ^ (n - 4) = -((-1 : ℤ) ^ (n - 5)) := by
    conv_lhs => rw [show n - 4 = (n - 5) + 1 by omega, pow_add]
    norm_num
  rw [p0] at h0
  rw [c1, p1] at h1
  rw [c2, p2] at h2
  rw [c3, p3] at h3
  rw [c4, p4] at h4
  rw [c5] at h5
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a267262.main := by
  refine ⟨a_closed, a_rec, ?_⟩
  ext n
  have hden : ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℤ) =
      1 - X - 2 * X ^ 2 + 2 * X ^ 3 + X ^ 4 - X ^ 5 := by ring
  have hnum : (X * (1 + 2 * X + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) : PowerSeries ℤ) =
      X + 2 * X ^ 2 + X ^ 5 + X ^ 6 - 2 * X ^ 7 + X ^ 8 := by ring
  rw [hden, hnum]
  have h2_2 : (2 : PowerSeries ℤ) * X ^ 2 = PowerSeries.C 2 * X ^ 2 := by rw [map_ofNat]
  have h2_3 : (2 : PowerSeries ℤ) * X ^ 3 = PowerSeries.C 2 * X ^ 3 := by rw [map_ofNat]
  have h2_7 : (2 : PowerSeries ℤ) * X ^ 7 = PowerSeries.C 2 * X ^ 7 := by rw [map_ofNat]
  have hrhs : PowerSeries.coeff n
      (X + 2 * X ^ 2 + X ^ 5 + X ^ 6 - 2 * X ^ 7 + X ^ 8 : PowerSeries ℤ) =
      (if n = 1 then 1 else 0) + 2 * (if n = 2 then 1 else 0) +
      (if n = 5 then 1 else 0) + (if n = 6 then 1 else 0) -
      2 * (if n = 7 then 1 else 0) + (if n = 8 then 1 else 0) := by
    rw [h2_2, h2_7]
    simp only [map_add, map_sub, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
               PowerSeries.coeff_C_mul]
  rw [hrhs]
  have hmul_pow : ∀ (f : PowerSeries ℤ) (d k : ℕ),
      PowerSeries.coeff k (f * X ^ d) = if d ≤ k then PowerSeries.coeff (k - d) f else 0 := by
    intro f d k
    rw [mul_comm, PowerSeries.coeff_X_pow_mul']
  have hmul_X : ∀ (f : PowerSeries ℤ) (k : ℕ),
      PowerSeries.coeff k (f * X) = if 1 ≤ k then PowerSeries.coeff (k - 1) f else 0 := by
    intro f k
    simpa [pow_one] using hmul_pow f 1 k
  have hmul_c : ∀ (f : PowerSeries ℤ) (c : ℤ) (d k : ℕ),
      PowerSeries.coeff k (f * (PowerSeries.C c * X ^ d)) =
        if d ≤ k then c * PowerSeries.coeff (k - d) f else 0 := by
    intro f c d k
    rw [← mul_assoc, mul_comm f (PowerSeries.C c), mul_assoc, PowerSeries.coeff_C_mul, hmul_pow]
    split_ifs <;> ring
  rw [mul_sub, mul_add, mul_add, mul_sub, mul_sub, mul_one, h2_2, h2_3]
  simp only [map_add, map_sub, hmul_X, hmul_c, hmul_pow, PowerSeries.coeff_mk]
  have ha5 : a 5 = 13 := by simpa using (a_even_odd_ge4 0).2
  have ha6 : a 6 = 20 := by simpa using (a_even_odd_ge4 1).1
  have ha7 : a 7 = 24 := by simpa using (a_even_odd_ge4 1).2
  have ha8 : a 8 = 35 := by simpa using (a_even_odd_ge4 2).1
  by_cases hn : n ≤ 8
  · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, ha5, ha6, ha7, ha8]
  · have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn5 : n ≠ 5 := by omega
    have hn6 : n ≠ 6 := by omega
    have hn7 : n ≠ 7 := by omega
    have hn8 : n ≠ 8 := by omega
    simp only [h1, h2, h3, h4, h5, hn1, hn2, hn5, hn6, hn7, hn8, ↓reduceIte]
    have hr := a_rec n (by omega)
    linarith
