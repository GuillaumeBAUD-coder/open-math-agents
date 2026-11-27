import OMAStatements.S_arxiv_2008_10398
import Mathlib

open Finset OMA.S_arxiv_2008_10398

namespace OMA.Fink

/-- Unfolded recursion without the `attach`. -/
lemma R_eq (n : ℕ) :
    recursiveDivisors n = 1 + ∑ d ∈ n.properDivisors, recursiveDivisors d := by
  rw [recursiveDivisors]
  rw [Finset.sum_attach n.properDivisors (fun d => recursiveDivisors d)]

lemma R_pos (n : ℕ) : 1 ≤ recursiveDivisors n := by
  rw [R_eq]
  exact Nat.le_add_right _ _

/-- Step 2: the quotients `n / q` for distinct primes `q ∣ n` are distinct proper divisors. -/
lemma step2 (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (n : ℕ) (hn : 0 < n) :
    ∑ q ∈ Q, (if q ∣ n then recursiveDivisors (n / q) else 0) ≤ recursiveDivisors n := by
  rw [R_eq n, ← Finset.sum_filter]
  have hinj : ∀ a ∈ Q.filter (fun q => q ∣ n), ∀ b ∈ Q.filter (fun q => q ∣ n),
      n / a = n / b → a = b := by
    intro a ha b hb hab
    have hda : a ∣ n := (Finset.mem_filter.mp ha).2
    have hdb : b ∣ n := (Finset.mem_filter.mp hb).2
    have hpos : 0 < n / a := Nat.div_pos (Nat.le_of_dvd hn hda) (hQ a (Finset.mem_filter.mp ha).1).pos
    have h1 : n / a * a = n := Nat.div_mul_cancel hda
    have h2 : n / b * b = n := Nat.div_mul_cancel hdb
    rw [← hab] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have himg : ∑ q ∈ Q.filter (fun q => q ∣ n), recursiveDivisors (n / q)
      = ∑ d ∈ (Q.filter (fun q => q ∣ n)).image (fun q => n / q), recursiveDivisors d :=
    (Finset.sum_image hinj).symm
  have hsub : (Q.filter (fun q => q ∣ n)).image (fun q => n / q) ⊆ n.properDivisors := by
    intro d hd
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    have hdq : q ∣ n := (Finset.mem_filter.mp hq).2
    have hqp : q.Prime := hQ q (Finset.mem_filter.mp hq).1
    exact Nat.mem_properDivisors.mpr ⟨Nat.div_dvd_of_dvd hdq, Nat.div_lt_self hn hqp.one_lt⟩
  rw [himg]
  exact (Finset.sum_le_sum_of_subset hsub).trans (Nat.le_add_left _ _)

/-- The number of ordered factorisations of `n` into `j` primes of `Q` is at most `R n`. -/
lemma count_le (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) : ∀ (j n : ℕ),
    (Finset.univ.filter (fun w : Fin j → Q => ∏ i, ((w i : ℕ)) = n)).card
      ≤ recursiveDivisors n := by
  intro j
  induction j with
  | zero =>
    intro n
    refine (Finset.card_filter_le _ _).trans ?_
    refine le_trans (le_of_eq ?_) (R_pos n)
    simp
  | succ j ih =>
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hempty : (Finset.univ.filter (fun w : Fin (j + 1) → Q => ∏ i, ((w i : ℕ)) = n)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro w _ h
        rw [hn, Finset.prod_eq_zero_iff] at h
        obtain ⟨i, _, hi⟩ := h
        exact (hQ _ (w i).2).ne_zero hi
      rw [hempty]
      simp
    · rw [Finset.card_filter]
      have hre : ∑ w : Fin (j + 1) → Q, (if ∏ i, ((w i : ℕ)) = n then 1 else 0)
          = ∑ q : Q, ∑ v : Fin j → Q, (if (q : ℕ) * ∏ i, ((v i : ℕ)) = n then 1 else 0) := by
        rw [← Fintype.sum_prod_type']
        refine (Fintype.sum_equiv (Fin.consEquiv (fun _ => (Q : Type))) _ _ ?_).symm
        intro p
        simp [Fin.consEquiv, Fin.prod_univ_succ]
      rw [hre]
      have hterm : ∀ q : Q, ∑ v : Fin j → Q, (if (q : ℕ) * ∏ i, ((v i : ℕ)) = n then 1 else 0)
          ≤ (if (q : ℕ) ∣ n then recursiveDivisors (n / (q : ℕ)) else 0) := by
        intro q
        have hqpos : 0 < (q : ℕ) := (hQ _ q.2).pos
        by_cases hd : (q : ℕ) ∣ n
        · rw [if_pos hd]
          obtain ⟨c, hc⟩ := hd
          have hdiv : n / (q : ℕ) = c := by
            rw [hc]
            exact Nat.mul_div_cancel_left c hqpos
          rw [hdiv]
          refine le_trans (le_of_eq ?_) (ih c)
          rw [Finset.card_filter]
          apply Finset.sum_congr rfl
          intro v _
          have hiff : ((q : ℕ) * ∏ i, ((v i : ℕ)) = n) ↔ (∏ i, ((v i : ℕ)) = c) := by
            rw [hc]
            constructor
            · intro h
              exact Nat.eq_of_mul_eq_mul_left hqpos h
            · intro h
              rw [h]
          simp only [hiff]
        · rw [if_neg hd]
          apply le_of_eq
          apply Finset.sum_eq_zero
          intro v _
          rw [if_neg]
          intro h
          exact hd ⟨_, h.symm⟩
      refine (Finset.sum_le_sum (fun q _ => hterm q)).trans ?_
      rw [Finset.sum_coe_sort Q (fun q => if q ∣ n then recursiveDivisors (n / q) else 0)]
      exact step2 Q hQ n hn

/-- Step 1: a finite set of primes above `k` with reciprocal sum at least `3`. -/
lemma exists_primes (k : ℕ) : ∃ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) ∧ (∀ q ∈ Q, k < q) ∧
    (3 : ℝ) ≤ ∑ q ∈ Q, (1 / (q : ℝ)) := by
  have hns : ¬ Summable (Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n)) :=
    not_summable_one_div_on_primes
  have hnn : ∀ n, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n :=
    fun n => Set.indicator_nonneg (fun _ _ => by positivity) n
  have hns' : ¬ Summable (fun n =>
      Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) (n + (k + 1))) :=
    fun h => hns ((summable_nat_add_iff (k + 1)).mp h)
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => hnn (n + (k + 1)))).mp hns'
  obtain ⟨N, hN⟩ := (ht.eventually_ge_atTop 3).exists
  refine ⟨((Finset.range N).image (fun i => i + (k + 1))).filter Nat.Prime, ?_, ?_, ?_⟩
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hq).1
    omega
  · rw [Finset.sum_filter, Finset.sum_image (by intro a _ b _ h; simpa using h)]
    refine hN.trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro i _
    simp [Set.indicator_apply]

lemma num_bound : ∀ t : ℕ, 2 * (t * t) + 1 ≤ 4 ^ t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    have h := Nat.le_mul_self t
    rw [pow_succ]
    nlinarith

/-- Step 4 counting: the products of words of length `j` take at most `(j+1)^|Q|` values. -/
lemma card_image_le_pow (Q : Finset ℕ) (j : ℕ) :
    ((Finset.univ : Finset (Fin j → Q)).image (fun w => ∏ i, ((w i : ℕ)))).card
      ≤ (j + 1) ^ Q.card := by
  have hsub : (Finset.univ : Finset (Fin j → Q)).image (fun w => ∏ i, ((w i : ℕ)))
      ⊆ (Finset.univ : Finset (Q → Fin (j + 1))).image
          (fun e => ∏ q : Q, (q : ℕ) ^ ((e q : ℕ))) := by
    intro n hn
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hn
    refine Finset.mem_image.mpr ⟨fun q => ⟨(Finset.univ.filter (fun i => w i = q)).card, ?_⟩,
      Finset.mem_univ _, ?_⟩
    · refine Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans ?_)
      simp
    · rw [← Finset.prod_fiberwise' Finset.univ w (fun q : Q => (q : ℕ))]
      apply Finset.prod_congr rfl
      intro q _
      rw [Finset.prod_const]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp

end OMA.Fink

open OMA.Fink
theorem OMA.solution : type_of% @OMA.S_arxiv_2008_10398.main := by
  intro k
  obtain ⟨Q, hQp, hQk, hZ⟩ := exists_primes k
  by_contra hcon
  push Not at hcon
  -- every product of primes of `Q` fails to be ample
  have key : ∀ (j : ℕ) (w : Fin j → Q),
      recursiveDivisors (∏ i, ((w i : ℕ))) ≤ ∏ i, ((w i : ℕ)) := by
    intro j w
    by_contra hlt
    rw [not_le] at hlt
    have hpos : 0 < ∏ i, ((w i : ℕ)) :=
      Finset.prod_pos (fun i _ => (hQp _ (w i).2).pos)
    obtain ⟨p, hp, hpk, hpd⟩ := hcon _ hpos hlt
    obtain ⟨i, _, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpd
    have heq : p = (w i : ℕ) := (Nat.prime_dvd_prime_iff_eq hp (hQp _ (w i).2)).mp hi
    have := hQk _ (w i).2
    omega
  -- the averaging bound
  have bound : ∀ j : ℕ, (∑ q ∈ Q, (1 / (q : ℝ))) ^ j ≤ (((j + 1) ^ Q.card : ℕ) : ℝ) := by
    intro j
    rw [← Finset.sum_coe_sort Q (fun q => 1 / (q : ℝ)), Fintype.sum_pow]
    have h1 : ∀ w : Fin j → Q, ∏ i, (1 / ((w i : ℕ) : ℝ))
        = (fun n : ℕ => 1 / (n : ℝ)) (∏ i, ((w i : ℕ))) := by
      intro w
      simp [Finset.prod_inv_distrib]
    rw [Finset.sum_congr rfl (fun w _ => h1 w),
      Finset.sum_comp (fun n : ℕ => 1 / (n : ℝ)) (fun w : Fin j → Q => ∏ i, ((w i : ℕ)))]
    have h2 : ∀ n ∈ (Finset.univ : Finset (Fin j → Q)).image (fun w => ∏ i, ((w i : ℕ))),
        (Finset.univ.filter (fun w : Fin j → Q => ∏ i, ((w i : ℕ)) = n)).card • (1 / (n : ℝ))
          ≤ 1 := by
      intro n hn
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hn
      have hpos : 0 < ∏ i, ((w i : ℕ)) :=
        Finset.prod_pos (fun i _ => (hQp _ (w i).2).pos)
      have hle : (Finset.univ.filter (fun v : Fin j → Q =>
          ∏ i, ((v i : ℕ)) = ∏ i, ((w i : ℕ)))).card ≤ ∏ i, ((w i : ℕ)) :=
        (count_le Q hQp j _).trans (key j w)
      have hposR : (0 : ℝ) < ((∏ i, ((w i : ℕ)) : ℕ) : ℝ) := by exact_mod_cast hpos
      rw [nsmul_eq_mul, mul_one_div, div_le_one hposR]
      exact_mod_cast hle
    refine (Finset.sum_le_sum h2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_image_le_pow Q j
  -- numerics
  have ht : Q.card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hZ
    norm_num at hZ
  have hb := bound (2 * (Q.card * Q.card))
  have h3 : (3 : ℝ) ^ (2 * (Q.card * Q.card)) ≤ (∑ q ∈ Q, (1 / (q : ℝ))) ^ (2 * (Q.card * Q.card)) :=
    pow_le_pow_left₀ (by norm_num) hZ _
  have h4 : (2 * (Q.card * Q.card) + 1) ^ Q.card ≤ 4 ^ (Q.card * Q.card) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (num_bound Q.card) _
  have h5 : (3 : ℝ) ^ (2 * (Q.card * Q.card)) ≤ ((4 ^ (Q.card * Q.card) : ℕ) : ℝ) :=
    (h3.trans hb).trans (by exact_mod_cast h4)
  have h6 : 9 ^ (Q.card * Q.card) ≤ 4 ^ (Q.card * Q.card) := by
    have h7 : ((9 ^ (Q.card * Q.card) : ℕ) : ℝ) ≤ ((4 ^ (Q.card * Q.card) : ℕ) : ℝ) := by
      refine le_trans (le_of_eq ?_) h5
      push_cast
      rw [pow_mul (3 : ℝ) 2 (Q.card * Q.card)]
      norm_num
    exact_mod_cast h7
  have h8 : 4 ^ (Q.card * Q.card) < 9 ^ (Q.card * Q.card) :=
    Nat.pow_lt_pow_left (by norm_num) (Nat.mul_ne_zero ht ht)
  omega
