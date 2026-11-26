import FormalConjectures.ErdosProblems.«673»

-- Problem: Erdős Problem 673 — tao
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/673.lean:80 (declaration Erdos673.erdos_673.variants.tao)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Erdős Problem 673, Tao's bounds

Let `1 = d_1 < ... < d_t = n` be the divisors of `n`, so `G n = ∑_{i < t} d_i / d_{i+1}`.

* Upper bound: there are `t - 1` terms, each at most `1`.
* Lower bound: every divisor `d` of `n / m` is a divisor of `n` below `n`, say `d = d_j`, and `m * d`
  is a divisor of `n` above `d`, so `d_{j+1} ≤ m * d` and the `j`-th term is at least `1 / m`.
  Distinct `d` give distinct `j` and every term is nonnegative, so `G n ≥ τ(n / m) / m`.
-/

open Finset

namespace OMA673

lemma toFinset_dvd {n : ℕ} (hn : 0 < n) (hf : {x : ℕ | x ∣ n}.Finite) :
    hf.toFinset = n.divisors := by
  ext d
  simp [Set.Finite.mem_toFinset, Nat.mem_divisors, hn.ne']

lemma dvd_finite {n : ℕ} (hn : 0 < n) : {x : ℕ | x ∣ n}.Finite :=
  (Set.finite_le_nat n).subset (fun _ hd => Nat.le_of_dvd hn hd)

/-- The number of divisors of `n` below `n`. -/
lemma count_dvd_self {n : ℕ} (hn : 0 < n) :
    Nat.count (· ∣ n) n = n.divisors.card - 1 := by
  rw [Nat.count_eq_card_filter_range]
  have h : (range n).filter (· ∣ n) = n.properDivisors := by
    ext d
    simp [Nat.mem_properDivisors, and_comm]
  rw [h, ← Nat.insert_self_properDivisors hn.ne',
    card_insert_of_notMem Nat.self_notMem_properDivisors]
  simp

lemma G_eq (n : ℕ) :
    Erdos673.G n = ∑ i ∈ range (n.divisors.card - 1),
      (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1) := by
  unfold Erdos673.G
  exact Fin.sum_univ_eq_sum_range
    (fun i => (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)) _

lemma lt_card_toFinset {n j : ℕ} (hn : 0 < n) (hj : j < n.divisors.card)
    (hf : {x : ℕ | x ∣ n}.Finite) : j < hf.toFinset.card := by
  have h := congrArg Finset.card (toFinset_dvd hn hf)
  omega

lemma nth_lt_nth_dvd {n i j : ℕ} (hn : 0 < n) (hij : i < j) (hj : j < n.divisors.card) :
    Nat.nth (· ∣ n) i < Nat.nth (· ∣ n) j :=
  Nat.nth_lt_nth' hij (fun hf => lt_card_toFinset hn hj hf)

lemma nth_dvd {n j : ℕ} (hn : 0 < n) (hj : j < n.divisors.card) :
    Nat.nth (· ∣ n) j ∣ n :=
  Nat.nth_mem_of_lt_card (dvd_finite hn) (lt_card_toFinset hn hj (dvd_finite hn))

theorem upper {n : ℕ} (hn : 0 < n) : Erdos673.G n ≤ n.divisors.card := by
  rw [G_eq]
  calc ∑ i ∈ range (n.divisors.card - 1),
        (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)
      ≤ ∑ _i ∈ range (n.divisors.card - 1), (1 : ℝ) := by
        apply sum_le_sum
        intro i hi
        rw [mem_range] at hi
        apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
        exact_mod_cast (nth_lt_nth_dvd hn (Nat.lt_succ_self i) (by omega)).le
    _ ≤ n.divisors.card := by
        simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
        exact_mod_cast Nat.sub_le _ _

theorem lower {n m : ℕ} (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    ((n / m).divisors.card : ℝ) / m ≤ Erdos673.G n := by
  set p : ℕ → Prop := (· ∣ n) with hp
  set f : ℕ → ℝ := fun i => (Nat.nth p i : ℝ) / Nat.nth p (i + 1) with hf
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hτ : Nat.count p n = n.divisors.card - 1 := count_dvd_self hn
  -- what a divisor `d` of `n / m` contributes
  have key : ∀ d ∈ (n / m).divisors,
      Nat.count p d ∈ range (n.divisors.card - 1) ∧ (1 : ℝ) / m ≤ f (Nat.count p d) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdnm, hnm0⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdnm (Nat.pos_of_ne_zero hnm0)
    have hdn : p d := dvd_trans hdnm (Nat.div_dvd_of_dvd hmn)
    have hdlt : d < n :=
      lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hnm0) hdnm) (Nat.div_lt_self hn hm)
    have hmd : p (m * d) := Nat.mul_dvd_of_dvd_div hmn hdnm
    have hmdn : m * d ≤ n := Nat.le_of_dvd hn hmd
    have hdmd : d < m * d := by nlinarith
    have hc1 : Nat.count p d < Nat.count p (m * d) := Nat.count_strict_mono hdn hdmd
    have hc2 : Nat.count p (m * d) ≤ Nat.count p n := Nat.count_monotone p hmdn
    refine ⟨mem_range.2 (by rw [← hτ]; exact Nat.count_strict_mono hdn hdlt), ?_⟩
    -- the divisor following `d` is at most `m * d`
    have hnext : Nat.nth p (Nat.count p d + 1) ≤ m * d := by
      have hsucc : Nat.count p (m * d + 1) = Nat.count p (m * d) + 1 :=
        (Nat.count_succ_eq_succ_count_iff (p := p) (n := m * d)).2 hmd
      have : Nat.count p d + 1 < Nat.count p (m * d + 1) := by omega
      exact Nat.lt_succ_iff.1 (Nat.nth_lt_of_lt_count this)
    have hpos : 0 < Nat.nth p (Nat.count p d + 1) := by
      have hlt : Nat.count p d + 1 < n.divisors.card := by omega
      exact Nat.pos_of_dvd_of_pos (nth_dvd hn hlt) hn
    have hnd : Nat.nth p (Nat.count p d) = d := Nat.nth_count hdn
    simp only [hf, hnd]
    have hpos' : (0 : ℝ) < Nat.nth p (Nat.count p d + 1) := by exact_mod_cast hpos
    have hnext' : (Nat.nth p (Nat.count p d + 1) : ℝ) ≤ (m : ℝ) * d := by exact_mod_cast hnext
    rw [div_le_div_iff₀ hm0 hpos']
    nlinarith
  rw [G_eq]
  calc ((n / m).divisors.card : ℝ) / m
      = ∑ _d ∈ (n / m).divisors, (1 : ℝ) / m := by
        rw [sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ ∑ d ∈ (n / m).divisors, f (Nat.count p d) := sum_le_sum (fun d hd => (key d hd).2)
    _ = ∑ i ∈ (n / m).divisors.image (Nat.count p), f i := by
        rw [sum_image]
        intro a ha b hb hab
        have ha' : p a := dvd_trans (Nat.dvd_of_mem_divisors ha) (Nat.div_dvd_of_dvd hmn)
        have hb' : p b := dvd_trans (Nat.dvd_of_mem_divisors hb) (Nat.div_dvd_of_dvd hmn)
        exact Nat.count_injective ha' hb' hab
    _ ≤ ∑ i ∈ range (n.divisors.card - 1), f i := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨d, hd, rfl⟩ := mem_image.1 hi
          exact (key d hd).1
        · intro i _ _
          exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end OMA673

theorem OMA.solution : type_of% @Erdos673.erdos_673.variants.tao := by
  intro n m hn hm hmn
  exact ⟨OMA673.lower hn hm hmn, OMA673.upper hn⟩
