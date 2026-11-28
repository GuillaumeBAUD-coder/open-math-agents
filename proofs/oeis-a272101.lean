import OMAStatements.S_oeis_a272101
import Mathlib

/-!
Irwin's three conjectures on OEIS A272101. A gap of at least four between
odd primes contains a multiple of four. In a twin-prime gap the difference
of the squares is four times the midpoint. Conversely, if the square of the
gap divides the difference of the squares, coprimality forces the gap to
divide two.
-/

open OMA.S_oeis_a272101

private lemma squarefree_interior_iff (n : ℕ) :
    InA068361 n ↔ ∀ t, p n < t → t < p (n + 1) → Squarefree t := by
  unfold InA068361
  rw [← Nat.card_Ioo, Finset.card_filter_eq_iff]
  simp [Finset.mem_Ioo]

private lemma square_max (m : ℕ) (hm : 0 < m) :
    Nat.findGreatest (fun k : ℕ => k ^ 2 ∣ 4 * m) (4 * m) = 2 ↔ Squarefree m := by
  let A := Nat.findGreatest (fun k : ℕ => k ^ 2 ∣ 4 * m) (4 * m)
  have two : 2 ≤ A := Nat.le_findGreatest (P := fun k : ℕ => k ^ 2 ∣ 4 * m) (by omega) (dvd_mul_right 4 m)
  have spec : A ^ 2 ∣ 4 * m :=
    Nat.findGreatest_spec (P := fun k : ℕ => k ^ 2 ∣ 4 * m) (m := 2) (by omega) (dvd_mul_right 4 m)
  change A = 2 ↔ _
  constructor
  · intro h k hk
    have hd : (2 * k) ^ 2 ∣ 4 * m := by
      rw [show (2 * k)^2 = 4 * (k * k) by ring]
      exact Nat.mul_dvd_mul_left 4 hk
    have hpos : 0 < k := by
      by_contra! hz
      have : k = 0 := by omega
      simp [this] at hk
      omega
    have hle : 2 * k ≤ 4 * m :=
      (show 2 * k ≤ (2 * k)^2 by nlinarith).trans (Nat.le_of_dvd (by omega) hd)
    have : 2 * k ≤ A := Nat.le_findGreatest hle hd
    exact Nat.isUnit_iff.mpr (by omega)
  · intro hs
    rcases Nat.even_or_odd A with ⟨k, hk⟩ | ho
    · have hd : 4 * (k * k) ∣ 4 * m := by
        rw [show 4 * (k * k) = A ^ 2 by rw [hk]; ring]
        exact spec
      have hu := Nat.isUnit_iff.mp (hs k ((Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp hd))
      omega
    · have cop : (A ^ 2).Coprime (2 ^ 2) := (ho.coprime_two_right.pow_left _).pow_right _
      have hd : A ^ 2 ∣ m := cop.dvd_of_dvd_mul_left spec
      have := Nat.isUnit_iff.mp (hs A (by simpa [pow_two] using hd))
      omega

private lemma twin_character (n : ℕ) (hn : 2 ≤ n) :
    (InA068361 n ↔ g n = 2 ∧ Squarefree (p n + 1)) ∧
    (a n = g n ↔ g n = 2 ∧ Squarefree (p n + 1)) := by
  let P := p n
  let Q := p (n + 1)
  let d := g n
  have hp : P.Prime := Nat.prime_nth_prime _
  have hq : Q.Prime := Nat.prime_nth_prime _
  have lt : P < Q := Nat.nth_strictMono Nat.infinite_setOfPred_prime (by dsimp; omega)
  have three : 3 ≤ P := by
    have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
        (show 1 ≤ n - 1 by omega)
    simpa [P, p, Nat.nth_prime_one_eq_three] using h
  have op := hp.odd_of_ne_two (by omega)
  have oq := hq.odd_of_ne_two (by omega)
  have plus : Q = P + d := by dsimp [P, Q, d, g] at *; omega
  have evenGap : 2 ∣ d := by obtain ⟨u,hu⟩ := op; obtain ⟨v,hv⟩ := oq; omega
  have dpos : 0 < d := by omega
  have delta : A069482 n = d * (2 * P + d) := by
    change Q^2 - P^2 = _
    rw [plus]
    exact Nat.sub_eq_of_eq_add (by ring)
  have twin (he : d = 2) : a n = 2 ↔ Squarefree (P + 1) := by
    have h : A069482 n = 4 * (P + 1) := by rw [delta, he]; ring
    simpa only [a, h] using square_max (P + 1) (by omega)
  change (InA068361 n ↔ d = 2 ∧ Squarefree (P + 1)) ∧
    (a n = d ↔ d = 2 ∧ Squarefree (P + 1))
  constructor
  · rw [squarefree_interior_iff]
    change (∀ t, P < t → t < Q → Squarefree t) ↔ _
    constructor
    · intro allSq
      have small : d ≤ 2 := by
        by_contra! big
        obtain ⟨u,hu⟩ := op
        have hs := allSq (4 * (P / 4 + 1)) (by omega) (by omega)
        exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) (dvd_mul_right _ _)
      exact ⟨by omega, allSq _ (by omega) (by omega)⟩
    · rintro ⟨hd, hs⟩ t h₁ h₂
      have : t = P + 1 := by omega
      simpa [this] using hs
  · constructor
    · intro he
      have hdA : d ^ 2 ∣ A069482 n := by
        rw [← he]
        unfold a
        apply Nat.findGreatest_spec (P := fun k : ℕ => k ^ 2 ∣ A069482 n) (m := 1)
        · rw [delta]; exact Nat.mul_pos dpos (by omega)
        · simp
      rw [delta, pow_two] at hdA
      have hdSum := (Nat.mul_dvd_mul_iff_left dpos).mp hdA
      have hdP : d ∣ 2 * P := by
        simpa using Nat.dvd_sub hdSum (dvd_refl d)
      have cop : P.Coprime d := hp.coprime_iff_not_dvd.mpr (by
        intro h
        have hPQ : P ∣ Q := plus ▸ dvd_add (dvd_refl _) h
        rcases hq.eq_one_or_self_of_dvd P hPQ with h | h <;> omega)
      have hd2 : d ∣ 2 := cop.symm.dvd_of_dvd_mul_right hdP
      have hh := Nat.le_of_dvd (by decide : 0 < 2) hd2
      have eq : d = 2 := by omega
      exact ⟨eq, (twin eq).mp (he.trans eq)⟩
    · rintro ⟨eq, hs⟩
      exact ((twin eq).mpr hs).trans eq.symm

theorem OMA.solution : type_of% @OMA.S_oeis_a272101.main := by
  have first : a 1 = g 1 ∧ InA068361 1 := by
    constructor
    · norm_num [a, A069482, g, p, Nat.findGreatest, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
    · apply (squarefree_interior_iff 1).2
      simp only [p, Nat.reduceSub, Nat.reduceAdd, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
      omega
  refine ⟨?_, ?_, ?_⟩
  · intro n hn h
    by_cases h1 : n = 1
    · simpa [h1] using first.1
    · have t := twin_character n (by omega)
      exact t.2.mpr (t.1.mp h)
  · intro n hn h
    have t := twin_character n hn
    exact (t.2.mpr (t.1.mp h)).trans (t.1.mp h).1
  · intro n hn h
    by_cases h1 : n = 1
    · simpa [h1] using first.2
    · have t := twin_character n (by omega)
      exact t.1.mpr (t.2.mp h)
