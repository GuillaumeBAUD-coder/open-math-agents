import OMAReductions.R_Erdos954_erdos_954_variants_upper_R1

/-!
Step H1 of reduction Erdos954.erdos_954.variants.upper.R1: `k ^ 2 ≤ 100 * rosen k`.

Write `a = rosen`. Two facts from the construction: `a m ≤ (m + 1) ^ 2`, and for `m < n`
(`n ≥ 3`) every set of admissible pairs with indices below `n` and sums in `(a m, a n]` has fewer
than `a n - a m` elements (`rosen_spec` above, minimality below). By strong induction on `M`,
`M ^ 2 ≤ 100 * (a n - a (n - M))` for `M ≤ n`: for `M ≤ 100` use `a n - a (n - M) ≥ M`; otherwise
put `t = M / 22`, `h = 10 t`, and pair `i < t` with `n - M + t < j ≤ n - h`. The induction
hypothesis at `h` gives `t ^ 2 ≤ a n - a (n - h)`, so all these `t (M - 11 t)` sums lie in
`(a (n - M), a n]`.
-/

open Erdos954 OMA.R_Erdos954_erdos_954_variants_upper_R1

namespace OMA.E954H1

lemma rosen_add (x d : ℕ) : rosen x + d ≤ rosen (x + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have := rosen_lt_succ (x + d)
    rw [show x + (d + 1) = x + d + 1 by omega]
    omega

lemma rosen_le_sq (m : ℕ) : rosen m ≤ (m + 1) ^ 2 := by
  rcases m with _ | _ | k
  · rw [rosen_zero]; exact Nat.zero_le _
  · rw [rosen_one]; norm_num
  · have h1 := le_pairCount_of_le k (rosen (k + 2)) le_rfl
    have h2 := pairCount_le_sq rosen (k + 2) (rosen (k + 2))
    rw [sq]
    exact h1.trans h2

lemma count_bound (k m : ℕ) (hm : m < k + 3) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 < k + 3 ∧ p.2 < k + 3 ∧ p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧
      rosen p.1 + rosen p.2 ≤ rosen (k + 3) ∧ rosen m < rosen p.1 + rosen p.2) :
    S.card + rosen m < rosen (k + 3) := by
  have hspec : pairCount rosen (k + 2) (rosen (k + 3)) < rosen (k + 3) := rosen_spec (k + 1)
  have hlow := le_pairCount_of_le k (rosen m) (rosen_strictMono.monotone (by omega))
  unfold pairCount at hspec hlow
  set U := Finset.range (k + 2 + 1) ×ˢ Finset.range (k + 2 + 1)
  have hsub : S ∪ U.filter (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧ rosen p.1 + rosen p.2 ≤ rosen m)
      ⊆ U.filter (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧
        rosen p.1 + rosen p.2 ≤ rosen (k + 3)) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨h1, h2, h3, h4, h5, _⟩ := hS p hp
      simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, h3, h4, h5⟩
    · simp only [U, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      obtain ⟨hr, h3, h4, h5⟩ := hp
      have : rosen m ≤ rosen (k + 3) := rosen_strictMono.monotone (by omega)
      exact ⟨hr, h3, h4, by omega⟩
  have hdisj : Disjoint S (U.filter (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ 1 ≤ p.2 ∧
      rosen p.1 + rosen p.2 ≤ rosen m)) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter] at hp'
    have := (hS p hp).2.2.2.2.2
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at this
  omega

lemma block (M : ℕ) : ∀ n, M ≤ n → M ^ 2 ≤ 100 * (rosen n - rosen (n - M)) := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro n hn
    have hgap := rosen_add (n - M) M
    rw [show n - M + M = n by omega] at hgap
    by_cases hM : M ≤ 100
    · calc M ^ 2 = M * M := sq M
        _ ≤ 100 * M := Nat.mul_le_mul_right M hM
        _ ≤ 100 * (rosen n - rosen (n - M)) := Nat.mul_le_mul_left 100 (by omega)
    · rw [not_le] at hM
      set t := M / 22 with ht
      have ht1 : 22 * t ≤ M := by omega
      have ht2 : M ≤ 50 * t := by omega
      have ht4 : 4 ≤ t := by omega
      have hih := ih (10 * t) (by omega) n (by omega)
      have htsq : t ^ 2 ≤ rosen n - rosen (n - 10 * t) := by
        have : (10 * t) ^ 2 = 100 * t ^ 2 := by ring
        omega
      have hmono1 : rosen (n - 10 * t) ≤ rosen n := rosen_strictMono.monotone (by omega)
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      let S := Finset.range t ×ˢ Finset.Ioc (k + 3 - M + t) (k + 3 - 10 * t)
      have hcard : S.card = t * (M - 11 * t) := by
        simp only [S, Finset.card_product, Finset.card_range, Nat.card_Ioc]
        congr 1
        omega
      have hb := count_bound k (k + 3 - M) (by omega) S (by
        intro p hp
        simp only [S, Finset.mem_product, Finset.mem_range, Finset.mem_Ioc] at hp
        obtain ⟨hi, hj1, hj2⟩ := hp
        have hai : rosen p.1 ≤ t ^ 2 :=
          (rosen_le_sq p.1).trans (Nat.pow_le_pow_left (by omega) 2)
        have haj : rosen p.2 ≤ rosen (k + 3 - 10 * t) := rosen_strictMono.monotone hj2
        have hlt : rosen (k + 3 - M) < rosen p.2 := rosen_strictMono (by omega)
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)
      rw [hcard] at hb
      have hu : 11 * t ≤ M - 11 * t := by omega
      calc M ^ 2 = M * M := sq M
        _ ≤ (50 * t) * M := Nat.mul_le_mul_right M ht2
        _ = 50 * t * (M - 11 * t) + 50 * t * (11 * t) := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
        _ ≤ 50 * t * (M - 11 * t) + 50 * t * (M - 11 * t) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ hu) _
        _ = 100 * (t * (M - 11 * t)) := by ring
        _ ≤ 100 * (rosen (k + 3) - rosen (k + 3 - M)) := Nat.mul_le_mul_left 100 (by omega)

end OMA.E954H1

theorem OMA.solution : OMA.R_Erdos954_erdos_954_variants_upper_R1.H1 := by
  intro k
  have h := OMA.E954H1.block k k le_rfl
  rwa [Nat.sub_self, rosen_zero, Nat.sub_zero] at h
