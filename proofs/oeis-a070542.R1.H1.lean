import OMAReductions.R_oeis_a070542_R1

/-!
Proof of `oeis-a070542.R1.H1`: the ten known terms `1, 2, 3, 4, 6, 10, 15, 26, 28, 64` are
positive integers such that `Nat.choose (2 * n) n` has no two distinct prime factors adding
up to `2 * n`. Verified directly by kernel computation over `Finset.range (2 * n)`.
-/

namespace OeisA070542H1

private def noPrimePair (n : ℕ) : Bool :=
  let c := Nat.choose (2 * n) n
  (List.range (2 * n)).all fun p =>
    let q := 2 * n - p
    !(decide p.Prime && decide q.Prime && decide (p ≠ q) && decide (p ∣ c) && decide (q ∣ c))

private lemma noPrimePair_sound {n : ℕ} (h : noPrimePair n = true) :
    ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * n) n ∧
      q ∣ Nat.choose (2 * n) n ∧ p + q = 2 * n := by
  rintro ⟨p, q, hp, hq, hne, hpd, hqd, hsum⟩
  have hplt : p < 2 * n := by
    have := hq.pos
    omega
  have hqeq : q = 2 * n - p := by omega
  subst hqeq
  unfold noPrimePair at h
  rw [List.all_eq_true] at h
  have hmem := h p (List.mem_range.mpr hplt)
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    decide_eq_true_eq] at hmem
  tauto

private lemma check_all :
    ([1, 2, 3, 4, 6, 10, 15, 26, 28, 64] : List ℕ).all noPrimePair = true := by
  decide +kernel

theorem main_proof : OMA.R_oeis_a070542_R1.H1 := by
  intro n hn
  have hmem : n ∈ ([1, 2, 3, 4, 6, 10, 15, 26, 28, 64] : List ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    simpa [List.mem_cons] using hn
  have hpos : 1 ≤ n := by
    have h1 : ([1, 2, 3, 4, 6, 10, 15, 26, 28, 64] : List ℕ).all (fun k => decide (1 ≤ k)) = true := by
      decide
    rw [List.all_eq_true] at h1
    exact decide_eq_true_eq.mp (h1 n hmem)
  have hok : noPrimePair n = true := (List.all_eq_true.mp check_all) n hmem
  exact ⟨hpos, noPrimePair_sound hok⟩

end OeisA070542H1

theorem OMA.solution : OMA.R_oeis_a070542_R1.H1 :=
  OeisA070542H1.main_proof
