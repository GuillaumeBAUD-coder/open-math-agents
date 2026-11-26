import FormalConjectures.ErdosProblems.«1074»

-- Problem: Erdős Problem 1074 — EHSNumbers init
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1074.lean:122 (declaration Erdos1074.erdos_1074.variants.EHSNumbers_init)
-- Credit: @Slayzkami (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA.E1074

open Nat Erdos1074

lemma not_mem (m : ℕ) (h : ∀ p, p.Prime → p ∣ m ! + 1 → p % m = 1 % m) :
    m ∉ EHSNumbers := by
  rintro ⟨-, p, hp, hne, hd⟩
  exact hne (h p hp hd)

lemma eq_of_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ∣ q) : p = q :=
  (Nat.prime_dvd_prime_iff_eq hp hq).1 h

lemma mem_of (m p : ℕ) (hm : 1 ≤ m) (hp : p.Prime) (hne : p % m ≠ 1 % m) (hd : p ∣ m ! + 1) :
    m ∈ EHSNumbers := ⟨hm, p, hp, hne, hd⟩

lemma n0 : 0 ∉ EHSNumbers := fun h => absurd h.1 (by norm_num)
lemma n1 : 1 ∉ EHSNumbers := not_mem 1 (fun p _ _ => (Nat.mod_one p).trans (Nat.mod_one 1).symm)
lemma n2 : 2 ∉ EHSNumbers := not_mem 2 (fun p hp hd => by
  have : p = 3 := eq_of_dvd_prime hp (by norm_num) (by simpa [Nat.factorial] using hd)
  subst this; norm_num)
lemma n3 : 3 ∉ EHSNumbers := not_mem 3 (fun p hp hd => by
  have : p = 7 := eq_of_dvd_prime hp (by norm_num) (by simpa [Nat.factorial] using hd)
  subst this; norm_num)
lemma n4 : 4 ∉ EHSNumbers := not_mem 4 (fun p hp hd => by
  have hd' : p ∣ 5 * 5 := by simpa [Nat.factorial] using hd
  rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h <;>
  · have : p = 5 := eq_of_dvd_prime hp (by norm_num) h
    subst this; norm_num)
lemma n5 : 5 ∉ EHSNumbers := not_mem 5 (fun p hp hd => by
  have hd' : p ∣ 11 * 11 := by simpa [Nat.factorial] using hd
  rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h <;>
  · have : p = 11 := eq_of_dvd_prime hp (by norm_num) h
    subst this; norm_num)
lemma n6 : 6 ∉ EHSNumbers := not_mem 6 (fun p hp hd => by
  have hd' : p ∣ 7 * 103 := by simpa [Nat.factorial] using hd
  rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h
  · have : p = 7 := eq_of_dvd_prime hp (by norm_num) h
    subst this; norm_num
  · have : p = 103 := eq_of_dvd_prime hp (by norm_num) h
    subst this; norm_num)
lemma n7 : 7 ∉ EHSNumbers := not_mem 7 (fun p hp hd => by
  have hd' : p ∣ 71 * 71 := by simpa [Nat.factorial] using hd
  rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h <;>
  · have : p = 71 := eq_of_dvd_prime hp (by norm_num) h
    subst this; norm_num)
lemma n10 : 10 ∉ EHSNumbers := not_mem 10 (fun p hp hd => by
  have hd' : p ∣ 11 * 329891 := by simpa [Nat.factorial] using hd
  rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h
  · have : p = 11 := eq_of_dvd_prime hp (by norm_num) h
    subst this; norm_num
  · have : p = 329891 := eq_of_dvd_prime hp (by norm_num) h
    subst this; norm_num)
lemma n11 : 11 ∉ EHSNumbers := not_mem 11 (fun p hp hd => by
  have : p = 39916801 := eq_of_dvd_prime hp (by norm_num) (by simpa [Nat.factorial] using hd)
  subst this; norm_num)
lemma n12 : 12 ∉ EHSNumbers := not_mem 12 (fun p hp hd => by
  have hd' : p ∣ 13 * 13 * 2834329 := by simpa [Nat.factorial] using hd
  rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h <;>
    · have : p = 13 := eq_of_dvd_prime hp (by norm_num) h
      subst this; norm_num
  · have : p = 2834329 := eq_of_dvd_prime hp (by norm_num) h
    subst this; norm_num)

lemma m8 : 8 ∈ EHSNumbers := mem_of 8 61 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num [Nat.factorial])
lemma m9 : 9 ∈ EHSNumbers := mem_of 9 71 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num [Nat.factorial])
lemma m13 : 13 ∈ EHSNumbers := mem_of 13 83 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num [Nat.factorial])
lemma m14 : 14 ∈ EHSNumbers := mem_of 14 23 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num [Nat.factorial])
lemma m15 : 15 ∈ EHSNumbers := mem_of 15 59 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num [Nat.factorial])
lemma m16 : 16 ∈ EHSNumbers := mem_of 16 61 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num [Nat.factorial])
lemma m17 : 17 ∈ EHSNumbers := mem_of 17 661 (by norm_num) (by norm_num) (by norm_num)
  (by norm_num [Nat.factorial])

def P : ℕ → Prop := fun n => n ∈ EHSNumbers

lemma counts [DecidablePred P] : count P 8 = 0 ∧ count P 9 = 1 ∧ count P 13 = 2 ∧
    count P 14 = 3 ∧ count P 15 = 4 ∧ count P 16 = 5 ∧ count P 17 = 6 := by
  have q0 : ¬ P 0 := n0
  have q1 : ¬ P 1 := n1
  have q2 : ¬ P 2 := n2
  have q3 : ¬ P 3 := n3
  have q4 : ¬ P 4 := n4
  have q5 : ¬ P 5 := n5
  have q6 : ¬ P 6 := n6
  have q7 : ¬ P 7 := n7
  have q8 : P 8 := m8
  have q9 : P 9 := m9
  have q10 : ¬ P 10 := n10
  have q11 : ¬ P 11 := n11
  have q12 : ¬ P 12 := n12
  have q13 : P 13 := m13
  have q14 : P 14 := m14
  have q15 : P 15 := m15
  have q16 : P 16 := m16
  simp [Nat.count_succ, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14,
    q15, q16]

end OMA.E1074

open OMA.E1074 in
theorem OMA.solution : type_of% @Erdos1074.erdos_1074.variants.EHSNumbers_init := by
  classical
  obtain ⟨c8, c9, c13, c14, c15, c16, c17⟩ := counts
  have h0 : Nat.nth P 0 = 8 := c8 ▸ Nat.nth_count (p := P) m8
  have h1 : Nat.nth P 1 = 9 := c9 ▸ Nat.nth_count (p := P) m9
  have h2 : Nat.nth P 2 = 13 := c13 ▸ Nat.nth_count (p := P) m13
  have h3 : Nat.nth P 3 = 14 := c14 ▸ Nat.nth_count (p := P) m14
  have h4 : Nat.nth P 4 = 15 := c15 ▸ Nat.nth_count (p := P) m15
  have h5 : Nat.nth P 5 = 16 := c16 ▸ Nat.nth_count (p := P) m16
  have h6 : Nat.nth P 6 = 17 := c17 ▸ Nat.nth_count (p := P) m17
  change Nat.nth P '' Set.Icc 0 6 = _
  ext x
  simp only [Set.mem_image, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, ⟨-, hk⟩, rfl⟩
    interval_cases k <;> simp [h0, h1, h2, h3, h4, h5, h6]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num, h0⟩
    · exact ⟨1, by norm_num, h1⟩
    · exact ⟨2, by norm_num, h2⟩
    · exact ⟨3, by norm_num, h3⟩
    · exact ⟨4, by norm_num, h4⟩
    · exact ⟨5, by norm_num, h5⟩
    · exact ⟨6, by norm_num, h6⟩
