import FormalConjectures.ErdosProblems.«1062»

/-!
# Proof of Erdős Problem 1062 (Lebensold's bounds)

We prove `∀ᶠ n in atTop, 0.6725 * n ≤ f n ∧ f n ≤ 0.6736 * n` using:
- Upper bound: partitioning `{1, ..., n}` by `{2, 3}`-free parts `m`, applying an exact
  row-sweeping dynamic program on `{2, 3}`-smooth numbers up to `6560`, and a 2-antichain
  tail bound `2 * (Nat.log 3 K + 1)` for `K ≥ 6561 = 3^8`, giving density `≤ 0.6735 < 0.6736`.
- Lower bound: an explicit zero-conflict 3-tier construction on `{2, 3}`-cosets indexed by
  the 5-adic tier (`5 ∤ m`, `5 ∣∣ m`, `25 ∣ m`) for `K ≤ 2000` and `3 * x > n` for `K ≥ 2001`,
  giving density `≥ 0.67255 > 0.6725`.
-/

-- Problem: Erdős Problem 1062 — lebensold bounds
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1062.lean:82 (declaration Erdos1062.erdos_1062.variants.lebensold_bounds)
-- Credit: @Dugongue (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Finset

namespace Erdos1062Proof

/- ### Section 1: `{2, 3}`-factorization and 3-smooth numbers -/

private def p6 (m : ℕ) : Bool :=
  (m % 2 != 0) && (m % 3 != 0)

private def oddPart23 (n : ℕ) : ℕ :=
  if h0 : n = 0 then 0
  else if h2 : n % 2 = 0 then oddPart23 (n / 2)
  else if h3 : n % 3 = 0 then oddPart23 (n / 3)
  else n
termination_by n

private def oddPart23Aux : ℕ → ℕ → ℕ
  | 0, n => n
  | fuel + 1, n =>
    if n = 0 then 0
    else if n % 2 = 0 then oddPart23Aux fuel (n / 2)
    else if n % 3 = 0 then oddPart23Aux fuel (n / 3)
    else n

private def isSmooth3 (n : ℕ) : Bool :=
  oddPart23 n == 1

private def isSmooth3Fast (n : ℕ) : Bool :=
  oddPart23Aux 25 n == 1

private lemma p6_pos {m : ℕ} (hm : p6 m = true) : 0 < m := by
  simp only [p6, Bool.and_eq_true, bne_iff_ne] at hm; omega

private lemma oddPart23_pos {n : ℕ} (hn : 0 < n) : 0 < oddPart23 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold oddPart23
    split_ifs with h0 h2 h3
    · omega
    · exact ih (n / 2) (by omega) (by omega)
    · exact ih (n / 3) (by omega) (by omega)
    · exact hn

private lemma oddPart23_p6 {n : ℕ} (hn : 0 < n) : p6 (oddPart23 n) = true := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold oddPart23
    split_ifs with h0 h2 h3
    · omega
    · exact ih (n / 2) (by omega) (by omega)
    · exact ih (n / 3) (by omega) (by omega)
    · simp only [p6, Bool.and_eq_true, bne_iff_ne]
      exact ⟨h2, h3⟩

private lemma oddPart23_one : oddPart23 1 = 1 := by
  unfold oddPart23; simp

private lemma oddPart23_mul_two (n : ℕ) : oddPart23 (2 * n) = oddPart23 n := by
  by_cases hn : n = 0
  · subst hn; rfl
  · conv_lhs => unfold oddPart23
    have h0 : 2 * n ≠ 0 := by omega
    have h2 : (2 * n) % 2 = 0 := by omega
    simp [h0, h2]

private lemma oddPart23_mul_three (n : ℕ) : oddPart23 (3 * n) = oddPart23 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst hn; rfl
    · by_cases h2 : n % 2 = 0
      · have h32 : (3 * n) % 2 = 0 := by omega
        have hdiv : 3 * n / 2 = 3 * (n / 2) := by omega
        conv_lhs => unfold oddPart23
        conv_rhs => unfold oddPart23
        simp only [show 3 * n ≠ 0 by omega, h32, ↓reduceDIte, hn, h2, hdiv]
        exact ih (n / 2) (by omega)
      · conv_lhs => unfold oddPart23
        have h0 : 3 * n ≠ 0 := by omega
        have h32 : (3 * n) % 2 ≠ 0 := by omega
        have h33 : (3 * n) % 3 = 0 := by omega
        simp [h0, h32, h33]

private lemma oddPart23_of_p6 {m : ℕ} (hm : p6 m = true) : oddPart23 m = m := by
  simp only [p6, Bool.and_eq_true, bne_iff_ne] at hm
  unfold oddPart23
  have h0 : m ≠ 0 := by omega
  simp [h0, hm.1, hm.2]

private lemma oddPart23_mul_pow (m a b : ℕ) :
    oddPart23 (m * (2 ^ a * 3 ^ b)) = oddPart23 m := by
  induction a generalizing m with
  | zero =>
    induction b generalizing m with
    | zero => simp
    | succ b ih =>
      have : m * (2 ^ 0 * 3 ^ (b + 1)) = 3 * (m * (2 ^ 0 * 3 ^ b)) := by ring
      rw [this, oddPart23_mul_three, ih]
  | succ a ih =>
    have : m * (2 ^ (a + 1) * 3 ^ b) = 2 * (m * (2 ^ a * 3 ^ b)) := by ring
    rw [this, oddPart23_mul_two, ih]

private lemma factor_23 (n : ℕ) (hn : 0 < n) :
    ∃ a b, n = oddPart23 n * (2 ^ a * 3 ^ b) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h2 : n % 2 = 0
    · obtain ⟨a, b, hab⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨a + 1, b, ?_⟩
      have hmul : oddPart23 n = oddPart23 (n / 2) := by
        conv_lhs => unfold oddPart23
        simp [show n ≠ 0 by omega, h2]
      rw [hmul]
      have : n = 2 * (n / 2) := by omega
      calc n = 2 * (n / 2) := this
        _ = 2 * (oddPart23 (n / 2) * (2 ^ a * 3 ^ b)) := by rw [← hab]
        _ = oddPart23 (n / 2) * (2 ^ (a + 1) * 3 ^ b) := by ring
    · by_cases h3 : n % 3 = 0
      · obtain ⟨a, b, hab⟩ := ih (n / 3) (by omega) (by omega)
        refine ⟨a, b + 1, ?_⟩
        have hmul : oddPart23 n = oddPart23 (n / 3) := by
          conv_lhs => unfold oddPart23
          simp [show n ≠ 0 by omega, h2, h3]
        rw [hmul]
        have : n = 3 * (n / 3) := by omega
        calc n = 3 * (n / 3) := this
          _ = 3 * (oddPart23 (n / 3) * (2 ^ a * 3 ^ b)) := by rw [← hab]
          _ = oddPart23 (n / 3) * (2 ^ a * 3 ^ (b + 1)) := by ring
      · refine ⟨0, 0, ?_⟩
        have : oddPart23 n = n := by
          unfold oddPart23
          simp [show n ≠ 0 by omega, h2, h3]
        simp [this]

private lemma isSmooth3_iff (s : ℕ) :
    isSmooth3 s = true ↔ ∃ a b, s = 2 ^ a * 3 ^ b := by
  constructor
  · intro h
    simp only [isSmooth3, beq_iff_eq] at h
    have hs : 0 < s := by
      by_contra h0
      have : s = 0 := by omega
      subst this; unfold oddPart23 at h; simp at h
    obtain ⟨a, b, hab⟩ := factor_23 s hs
    rw [h, one_mul] at hab
    exact ⟨a, b, hab⟩
  · rintro ⟨a, b, rfl⟩
    simp only [isSmooth3, beq_iff_eq]
    have h1 : 1 * (2 ^ a * 3 ^ b) = 2 ^ a * 3 ^ b := one_mul _
    rw [← h1, oddPart23_mul_pow, oddPart23_one]

private lemma isSmooth3_of_fast {n : ℕ} (h : isSmooth3Fast n = true) : isSmooth3 n = true := by
  simp only [isSmooth3Fast, beq_iff_eq] at h
  suffices ∀ fuel m, oddPart23Aux fuel m = 1 → isSmooth3 m = true from this 25 n h
  intro fuel
  induction fuel with
  | zero =>
    intro m hm
    simp only [oddPart23Aux] at hm
    subst hm; rw [isSmooth3_iff]; exact ⟨0, 0, by norm_num⟩
  | succ fuel ih =>
    intro m hm
    unfold oddPart23Aux at hm
    by_cases h0 : m = 0
    · rw [if_pos h0] at hm; omega
    · rw [if_neg h0] at hm
      by_cases h2 : m % 2 = 0
      · rw [if_pos h2] at hm
        have hrec := ih (m / 2) hm
        obtain ⟨a, b, hab⟩ := (isSmooth3_iff (m / 2)).mp hrec
        rw [isSmooth3_iff]
        refine ⟨a + 1, b, ?_⟩
        have : m = 2 * (m / 2) := by omega
        rw [this, hab]; ring
      · rw [if_neg h2] at hm
        by_cases h3 : m % 3 = 0
        · rw [if_pos h3] at hm
          have hrec := ih (m / 3) hm
          obtain ⟨a, b, hab⟩ := (isSmooth3_iff (m / 3)).mp hrec
          rw [isSmooth3_iff]
          refine ⟨a, b + 1, ?_⟩
          have : m = 3 * (m / 3) := by omega
          rw [this, hab]; ring
        · rw [if_neg h3] at hm
          subst hm; rw [isSmooth3_iff]; exact ⟨0, 0, by norm_num⟩

private lemma isSmooth3_pos {s : ℕ} (hs : isSmooth3 s = true) : 0 < s := by
  obtain ⟨a, b, rfl⟩ := (isSmooth3_iff s).mp hs
  positivity

private lemma oddPart23_mul_smooth {m s : ℕ} (hm : p6 m = true) (hs : isSmooth3 s = true) :
    oddPart23 (m * s) = m := by
  obtain ⟨a, b, rfl⟩ := (isSmooth3_iff s).mp hs
  rw [oddPart23_mul_pow, oddPart23_of_p6 hm]

private lemma oddPart23_dvd (n : ℕ) (hn : 0 < n) : oddPart23 n ∣ n := by
  obtain ⟨a, b, hab⟩ := factor_23 n hn
  exact ⟨2 ^ a * 3 ^ b, hab⟩

private lemma smoothPart_isSmooth3 {n : ℕ} (hn : 0 < n) :
    isSmooth3 (n / oddPart23 n) = true := by
  obtain ⟨a, b, hab⟩ := factor_23 n hn
  have hpos := oddPart23_pos hn
  have hdiv : n / oddPart23 n = 2 ^ a * 3 ^ b := by
    conv_lhs => rw [hab]
    rw [oddPart23_mul_pow, oddPart23_of_p6 (oddPart23_p6 hn), Nat.mul_div_right _ hpos]
  rw [hdiv, isSmooth3_iff]
  exact ⟨a, b, rfl⟩

private lemma mul_smoothPart {n : ℕ} (hn : 0 < n) :
    oddPart23 n * (n / oddPart23 n) = n :=
  Nat.mul_div_cancel' (oddPart23_dvd n hn)

private lemma oddPart23_le (n : ℕ) (hn : 0 < n) : oddPart23 n ≤ n :=
  Nat.le_of_dvd hn (oddPart23_dvd n hn)

private lemma pow23_dvd_iff (a1 b1 a2 b2 : ℕ) :
    2 ^ a1 * 3 ^ b1 ∣ 2 ^ a2 * 3 ^ b2 ↔ a1 ≤ a2 ∧ b1 ≤ b2 := by
  constructor
  · intro h
    have h2 : 2 ^ a1 ∣ 2 ^ a2 := by
      have hc : Nat.Coprime (2 ^ a1) (3 ^ b2) := (by decide : Nat.Coprime 2 3).pow a1 b2
      exact hc.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) h)
    have h3 : 3 ^ b1 ∣ 3 ^ b2 := by
      have hc : Nat.Coprime (3 ^ b1) (2 ^ a2) := (by decide : Nat.Coprime 3 2).pow b1 a2
      exact hc.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) h)
    exact ⟨(Nat.pow_dvd_pow_iff_le_right (by omega)).mp h2,
           (Nat.pow_dvd_pow_iff_le_right (by omega)).mp h3⟩
  · rintro ⟨ha, hb⟩
    exact mul_dvd_mul (Nat.pow_dvd_pow 2 ha) (Nat.pow_dvd_pow 3 hb)

private lemma isSmooth3_mul {s1 s2 : ℕ} (h1 : isSmooth3 s1 = true) (h2 : isSmooth3 s2 = true) :
    isSmooth3 (s1 * s2) = true := by
  obtain ⟨a1, b1, rfl⟩ := (isSmooth3_iff s1).mp h1
  obtain ⟨a2, b2, rfl⟩ := (isSmooth3_iff s2).mp h2
  rw [isSmooth3_iff]
  exact ⟨a1 + a2, b1 + b2, by ring⟩

/- ### Section 2: Periodic counting lemmas -/

private def cntP (P : ℕ → Bool) (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun m => P m)).card

private def cntPeriod (P : ℕ → Bool) (M : ℕ) : ℕ :=
  ((Finset.Icc 1 M).filter (fun m => P m)).card

private lemma cntP_mono (P : ℕ → Bool) {X Y : ℕ} (h : X ≤ Y) : cntP P X ≤ cntP P Y :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right h))

private lemma periodic_add_mul (P : ℕ → Bool) (M : ℕ)
    (hper : ∀ x, P (x + M) = P x) (q x : ℕ) :
    P (x + q * M) = P x := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : x + (q + 1) * M = (x + q * M) + M := by ring
    rw [this, hper, ih]

private lemma cntP_mul_period (P : ℕ → Bool) (M : ℕ)
    (hper : ∀ x, P (x + M) = P x) (q : ℕ) :
    cntP P (q * M) = q * cntPeriod P M := by
  induction q with
  | zero => simp [cntP]
  | succ q ih =>
    unfold cntP at ih ⊢
    have hmul_eq : (q + 1) * M = q * M + M := Nat.succ_mul q M
    have hsplit : Finset.Icc 1 ((q + 1) * M) =
        Finset.Icc 1 (q * M) ∪ Finset.Icc (q * M + 1) ((q + 1) * M) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 (q * M)) (Finset.Icc (q * M + 1) ((q + 1) * M)) := by
      rw [Finset.disjoint_left]; intro k hk1 hk2
      simp only [Finset.mem_Icc] at hk1 hk2; omega
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), ih, Nat.succ_mul q (cntPeriod P M)]
    congr 1
    unfold cntPeriod
    refine Finset.card_bij (fun k _ => k - q * M) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hkeq : k = (k - q * M) + q * M := by omega
      have h1 := hk.2
      rw [hkeq, periodic_add_mul P M hper q] at h1
      exact h1
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb; omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      refine ⟨j + q * M, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [periodic_add_mul P M hper q]
      exact hj.2

private lemma cntP_bounds (P : ℕ → Bool) (M : ℕ) (hM : 0 < M)
    (hper : ∀ x, P (x + M) = P x) (X : ℕ) :
    (X / M) * cntPeriod P M ≤ cntP P X ∧ cntP P X ≤ (X / M + 1) * cntPeriod P M := by
  have hlo : (X / M) * M ≤ X := by
    rw [mul_comm]; exact Nat.mul_div_le X M
  have hhi : X ≤ (X / M + 1) * M := by
    have h1 := Nat.lt_div_mul_add hM (a := X)
    rw [Nat.succ_mul]
    omega
  exact ⟨(cntP_mul_period P M hper (X / M)) ▸ cntP_mono P hlo,
         (cntP_mul_period P M hper (X / M + 1)) ▸ cntP_mono P hhi⟩

private lemma cntP_real_bounds (P : ℕ → Bool) (M : ℕ) (hM : 0 < M)
    (hper : ∀ x, P (x + M) = P x) (X : ℕ) :
    ((cntPeriod P M : ℝ) / M) * X - cntPeriod P M ≤ cntP P X ∧
    (cntP P X : ℝ) ≤ ((cntPeriod P M : ℝ) / M) * X + cntPeriod P M := by
  obtain ⟨h1, h2⟩ := cntP_bounds P M hM hper X
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hdiv1 : (X : ℝ) / M - 1 ≤ (X / M : ℕ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hMpos]
    have : X ≤ (X / M) * M + M := by
      have := Nat.lt_div_mul_add hM (a := X); omega
    have hcast : (X : ℝ) ≤ ((X / M : ℕ) : ℝ) * M + M := by exact_mod_cast this
    linarith
  have hdiv2 : ((X / M : ℕ) : ℝ) ≤ (X : ℝ) / M := Nat.cast_div_le
  have hr : (0 : ℝ) ≤ cntPeriod P M := Nat.cast_nonneg _
  constructor
  · have h1r : ((X / M : ℕ) : ℝ) * cntPeriod P M ≤ cntP P X := by exact_mod_cast h1
    have hmul : ((X : ℝ) / M - 1) * cntPeriod P M ≤ ((X / M : ℕ) : ℝ) * cntPeriod P M :=
      mul_le_mul_of_nonneg_right hdiv1 hr
    linarith [show ((X : ℝ) / M - 1) * cntPeriod P M = ((cntPeriod P M : ℝ) / M) * X - cntPeriod P M by ring]
  · have h2r : (cntP P X : ℝ) ≤ (((X / M : ℕ) : ℝ) + 1) * cntPeriod P M := by exact_mod_cast h2
    have hmul : (((X / M : ℕ) : ℝ) + 1) * cntPeriod P M ≤ ((X : ℝ) / M + 1) * cntPeriod P M :=
      mul_le_mul_of_nonneg_right (by linarith) hr
    linarith [show ((X : ℝ) / M + 1) * cntPeriod P M = ((cntPeriod P M : ℝ) / M) * X + cntPeriod P M by ring]

private lemma card_filter_Icc_sub (P : ℕ → Bool) {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Icc (a + 1) b).filter (fun m => P m)).card = cntP P b - cntP P a := by
  unfold cntP
  have hsplit : Finset.Icc 1 b = Finset.Icc 1 a ∪ Finset.Icc (a + 1) b := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Icc (a + 1) b) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2; omega
  rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hdisj)]
  omega

private lemma cntP_interval_real_bounds (P : ℕ → Bool) (M : ℕ) (hM : 0 < M)
    (hper : ∀ x, P (x + M) = P x) (n lo hi : ℕ) (hlo : 0 < lo) (hlh : lo ≤ hi) :
    ((cntPeriod P M : ℝ) / M) * ((1 : ℝ) / lo - 1 / hi) * n - (3 * cntPeriod P M + 1) ≤
      (((Finset.Icc (n / hi + 1) (n / lo)).filter (fun m => P m)).card : ℝ) ∧
    (((Finset.Icc (n / hi + 1) (n / lo)).filter (fun m => P m)).card : ℝ) ≤
      ((cntPeriod P M : ℝ) / M) * ((1 : ℝ) / lo - 1 / hi) * n + (3 * cntPeriod P M + 1) := by
  have hdiv_le : n / hi ≤ n / lo := Nat.div_le_div_left hlh hlo
  rw [card_filter_Icc_sub P hdiv_le]
  have hcnt_le : cntP P (n / hi) ≤ cntP P (n / lo) := cntP_mono P hdiv_le
  rw [Nat.cast_sub hcnt_le]
  obtain ⟨hlo1, hlo2⟩ := cntP_real_bounds P M hM hper (n / lo)
  obtain ⟨hhi1, hhi2⟩ := cntP_real_bounds P M hM hper (n / hi)
  have hlo_pos : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hhi_pos : (0 : ℝ) < hi := by exact_mod_cast (show 0 < hi by omega)
  have hd_lo_ub : ((n / lo : ℕ) : ℝ) ≤ (n : ℝ) / lo := Nat.cast_div_le
  have hd_hi_ub : ((n / hi : ℕ) : ℝ) ≤ (n : ℝ) / hi := Nat.cast_div_le
  have hd_lo_lb : (n : ℝ) / lo - 1 ≤ ((n / lo : ℕ) : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hlo_pos]
    have : n ≤ (n / lo) * lo + lo := by have := Nat.lt_div_mul_add hlo (a := n); omega
    have hcast : (n : ℝ) ≤ ((n / lo : ℕ) : ℝ) * lo + lo := by exact_mod_cast this
    linarith
  have hd_hi_lb : (n : ℝ) / hi - 1 ≤ ((n / hi : ℕ) : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hhi_pos]
    have : n ≤ (n / hi) * hi + hi := by have := Nat.lt_div_mul_add (by omega : 0 < hi) (a := n); omega
    have hcast : (n : ℝ) ≤ ((n / hi : ℕ) : ℝ) * hi + hi := by exact_mod_cast this
    linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hratio_nn : (0 : ℝ) ≤ (cntPeriod P M : ℝ) / M := by positivity
  have hratio_le1 : (cntPeriod P M : ℝ) / M ≤ 1 := by
    rw [div_le_one hMpos]
    have : cntPeriod P M ≤ M := by
      unfold cntPeriod
      calc ((Finset.Icc 1 M).filter (fun m => P m)).card
          ≤ (Finset.Icc 1 M).card := Finset.card_filter_le _ _
        _ = M := by simp
    exact_mod_cast this
  have hcoef_eq : ((cntPeriod P M : ℝ) / M) * ((1 : ℝ) / lo - 1 / hi) * n =
      ((cntPeriod P M : ℝ) / M) * ((n : ℝ) / lo - (n : ℝ) / hi) := by ring
  rw [hcoef_eq]
  have hrm : ((cntPeriod P M : ℝ) / M) * 1 ≤ 1 := by linarith
  have hcnt_nn : (0 : ℝ) ≤ cntPeriod P M := Nat.cast_nonneg _
  constructor
  · have hstep : ((cntPeriod P M : ℝ) / M) * ((n : ℝ) / lo - (n : ℝ) / hi - 1) ≤
        ((cntPeriod P M : ℝ) / M) * (((n / lo : ℕ) : ℝ) - ((n / hi : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hratio_nn
    linarith [show ((cntPeriod P M : ℝ) / M) * ((n : ℝ) / lo - (n : ℝ) / hi - 1) =
      ((cntPeriod P M : ℝ) / M) * ((n : ℝ) / lo - (n : ℝ) / hi) - ((cntPeriod P M : ℝ) / M) * 1 by ring,
      show ((cntPeriod P M : ℝ) / M) * (((n / lo : ℕ) : ℝ) - ((n / hi : ℕ) : ℝ)) =
      ((cntPeriod P M : ℝ) / M) * ((n / lo : ℕ) : ℝ) - ((cntPeriod P M : ℝ) / M) * ((n / hi : ℕ) : ℝ) by ring]
  · have hstep : ((cntPeriod P M : ℝ) / M) * (((n / lo : ℕ) : ℝ) - ((n / hi : ℕ) : ℝ)) ≤
        ((cntPeriod P M : ℝ) / M) * ((n : ℝ) / lo - (n : ℝ) / hi + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hratio_nn
    linarith [show ((cntPeriod P M : ℝ) / M) * ((n : ℝ) / lo - (n : ℝ) / hi + 1) =
      ((cntPeriod P M : ℝ) / M) * ((n : ℝ) / lo - (n : ℝ) / hi) + ((cntPeriod P M : ℝ) / M) * 1 by ring,
      show ((cntPeriod P M : ℝ) / M) * (((n / lo : ℕ) : ℝ) - ((n / hi : ℕ) : ℝ)) =
      ((cntPeriod P M : ℝ) / M) * ((n / lo : ℕ) : ℝ) - ((cntPeriod P M : ℝ) / M) * ((n / hi : ℕ) : ℝ) by ring]

private lemma p6_periodic (x : ℕ) : p6 (x + 6) = p6 x := by
  unfold p6
  have h2 : (x + 6) % 2 = x % 2 := by omega
  have h3 : (x + 6) % 3 = x % 3 := by omega
  rw [h2, h3]

private lemma cntPeriod_p6 : cntPeriod p6 6 = 2 := by decide

private lemma cntP_p6_upper (X : ℕ) : (cntP p6 X : ℝ) ≤ (X : ℝ) / 3 + 2 := by
  have h := (cntP_real_bounds p6 6 (by omega) p6_periodic X).2
  rw [cntPeriod_p6] at h
  linarith

/- ### Section 3: Upper bound `f n ≤ 0.6736 * n` -/

private def bonus (p1 p2 a : ℕ) : ℕ :=
  (if a ≤ p1 then 1 else 0) + (if a ≤ p2 then 1 else 0)

private def ValidAbove (p1 p2 : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  p2 ≤ p1 ∧ (∀ x ∈ S, 1 ≤ x.1) ∧
  ∀ x ∈ S, (S.filter (fun y => x.1 ≤ y.1 ∧ x.2 ≤ y.2 ∧ y ≠ x)).card + bonus p1 p2 x.1 ≤ 1

private lemma ValidAbove.mono {p1 p2 q1 q2 : ℕ} {S : Finset (ℕ × ℕ)}
    (h : ValidAbove q1 q2 S) (hp : p2 ≤ p1) (h1 : p1 ≤ q1) (h2 : p2 ≤ q2) :
    ValidAbove p1 p2 S := by
  refine ⟨hp, h.2.1, fun x hx => ?_⟩
  have hbon : bonus p1 p2 x.1 ≤ bonus q1 q2 x.1 := by
    unfold bonus; split_ifs <;> omega
  exact le_trans (Nat.add_le_add_left hbon _) (h.2.2 x hx)

private def grid : List ℕ → Finset (ℕ × ℕ)
  | [] => ∅
  | ma :: rest => (Finset.Icc 1 ma).image (fun a => (a, rest.length)) ∪ grid rest

private lemma mem_grid_snd_lt {rows : List ℕ} {x : ℕ × ℕ} (hx : x ∈ grid rows) :
    x.2 < rows.length := by
  induction rows with
  | nil => simp [grid] at hx
  | cons ma rest ih =>
    simp only [grid, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hx
    rw [List.length_cons]
    rcases hx with ⟨a, _, rfl⟩ | hrest
    · omega
    · exact Nat.lt_succ_of_lt (ih hrest)

private def lookupV (tbl : List (List ℕ)) (p1 p2 : ℕ) : ℕ :=
  (tbl.getD p1 []).getD p2 0

private def foldOne (ma p1 p2 : ℕ) (prev : List (List ℕ)) : ℕ :=
  (List.range ma).foldl (fun acc a0 =>
    let a := a0 + 1
    if p2 < a then max acc (1 + lookupV prev (max p1 a) (min p1 a))
    else acc) (lookupV prev p1 p2)

private def stepVal (ma : ℕ) (prev : List (List ℕ)) (p1 p2 : ℕ) : ℕ :=
  let v1 := foldOne ma p1 p2 prev
  if p1 + 2 ≤ ma then max v1 (2 + lookupV prev (p1 + 2) (p1 + 1)) else v1

private lemma foldl_max_ge_init {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ) :
    init ≤ l.foldl (fun acc x => max acc (f x)) init := by
  induction l generalizing init with
  | nil => exact le_rfl
  | cons a l ih =>
    exact le_trans (le_max_left init (f a)) (ih (max init (f a)))

private lemma foldl_max_ge_mem {α : Type*} (f : α → ℕ) (l : List α) (init : ℕ)
    {x : α} (hx : x ∈ l) :
    f x ≤ l.foldl (fun acc y => max acc (f y)) init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hl
    · exact le_trans (le_max_right init (f x)) (foldl_max_ge_init f l _)
    · exact ih _ hl

private lemma foldOne_eq_foldl_max (ma p1 p2 : ℕ) (prev : List (List ℕ)) :
    foldOne ma p1 p2 prev =
      (List.range ma).foldl
        (fun acc a0 => max acc (if p2 < a0 + 1 then 1 + lookupV prev (max p1 (a0 + 1)) (min p1 (a0 + 1)) else 0))
        (lookupV prev p1 p2) := by
  unfold foldOne
  congr 1
  funext acc a0
  by_cases h : p2 < a0 + 1
  · simp [h]
  · simp [h]

private lemma lookupV_le_foldOne (ma p1 p2 : ℕ) (prev : List (List ℕ)) :
    lookupV prev p1 p2 ≤ foldOne ma p1 p2 prev := by
  rw [foldOne_eq_foldl_max]
  exact foldl_max_ge_init _ _ _

private lemma one_add_le_foldOne {ma p1 p2 a : ℕ} (prev : List (List ℕ))
    (ha1 : 1 ≤ a) (ha2 : a ≤ ma) (hp2 : p2 < a) :
    1 + lookupV prev (max p1 a) (min p1 a) ≤ foldOne ma p1 p2 prev := by
  rw [foldOne_eq_foldl_max]
  have hmem : a - 1 ∈ List.range ma := List.mem_range.mpr (by omega)
  have h := foldl_max_ge_mem
    (fun a0 => if p2 < a0 + 1 then 1 + lookupV prev (max p1 (a0 + 1)) (min p1 (a0 + 1)) else 0)
    (List.range ma) (lookupV prev p1 p2) hmem
  have haeq : a - 1 + 1 = a := by omega
  rw [haeq, if_pos hp2] at h
  exact h

private def validDPStep (lim ma : ℕ) (cur prev : List (List ℕ)) : Bool :=
  (List.range (lim + 1)).all fun p1 =>
    (List.range (p1 + 1)).all fun p2 =>
      stepVal ma prev p1 p2 ≤ lookupV cur p1 p2

private def validDPTrace (lim : ℕ) : List ℕ → List (List (List ℕ)) → Bool
  | [], [] => true
  | ma :: rest, cur :: restT =>
      validDPStep lim ma cur (restT.headD []) && validDPTrace (max lim ma) rest restT
  | _, _ => false

private lemma validDPStep_spec {lim ma : ℕ} {cur prev : List (List ℕ)}
    (h : validDPStep lim ma cur prev = true) {p1 p2 : ℕ} (hp1 : p1 ≤ lim) (hp2 : p2 ≤ p1) :
    stepVal ma prev p1 p2 ≤ lookupV cur p1 p2 := by
  have h1 := List.all_eq_true.mp h p1 (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 p2 (List.mem_range.mpr (by omega))
  exact of_decide_eq_true h2

private lemma validDPTrace_sound (rows : List ℕ) :
    ∀ (lim : ℕ) (trace : List (List (List ℕ))), validDPTrace lim rows trace = true →
    ∀ p1 p2, p2 ≤ p1 → p1 ≤ lim → ∀ S : Finset (ℕ × ℕ), S ⊆ grid rows →
      ValidAbove p1 p2 S → S.card ≤ lookupV (trace.headD []) p1 p2 := by
  induction rows with
  | nil =>
    intro lim trace htr p1 p2 _ _ S hS _
    have hE : S = ∅ := Finset.subset_empty.mp hS
    subst hE; simp
  | cons ma rest ih =>
    intro lim trace htr p1 p2 hp21 hp1lim S hS hV
    cases trace with
    | nil => simp [validDPTrace] at htr
    | cons cur restT =>
      simp only [validDPTrace, Bool.and_eq_true] at htr
      obtain ⟨hstep, hrestT⟩ := htr
      have hcur_ge := validDPStep_spec hstep hp1lim hp21
      set prev := restT.headD []
      set Stop := S.filter (fun x => x.2 = rest.length)
      set Sbot := S.filter (fun x => x.2 ≠ rest.length)
      have hcard : S.card = Stop.card + Sbot.card := by
        rw [← Finset.card_filter_add_card_filter_not (s := S) (p := fun x => x.2 = rest.length)]
      have hSbot_sub : Sbot ⊆ grid rest := by
        intro x hx
        simp only [Sbot, Finset.mem_filter] at hx
        have hxg := hS hx.1
        simp only [grid, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hxg
        rcases hxg with ⟨a, _, hEq⟩ | hrest
        · exfalso; exact hx.2 (by rw [← hEq])
        · exact hrest
      have hStop_spec : ∀ x ∈ Stop, 1 ≤ x.1 ∧ x.1 ≤ ma ∧ x.2 = rest.length := by
        intro x hx
        simp only [Stop, Finset.mem_filter] at hx
        have hxg := hS hx.1
        simp only [grid, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hxg
        rcases hxg with ⟨a, ⟨ha1, ha2⟩, hEq⟩ | hrest
        · rw [← hEq]; exact ⟨ha1, ha2, rfl⟩
        · exfalso; exact absurd hx.2 (ne_of_lt (mem_grid_snd_lt hrest))
      have hStop_le2 : Stop.card ≤ 2 := by
        by_contra hgt
        have h3 : 2 < Stop.card := by omega
        have hne : Stop.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨x0, hx0, hmin⟩ := Finset.exists_min_image Stop Prod.fst hne
        have hx0S : x0 ∈ S := (Finset.mem_filter.mp hx0).1
        have hx0snd : x0.2 = rest.length := (Finset.mem_filter.mp hx0).2
        have hsub : Stop.erase x0 ⊆ S.filter (fun y => x0.1 ≤ y.1 ∧ x0.2 ≤ y.2 ∧ y ≠ x0) := by
          intro y hy
          rw [Finset.mem_erase] at hy
          rw [Finset.mem_filter]
          refine ⟨(Finset.mem_filter.mp hy.2).1, hmin y hy.2, ?_, hy.1⟩
          have hysnd : y.2 = rest.length := (Finset.mem_filter.mp hy.2).2
          omega
        have hc1 : 2 ≤ (Stop.erase x0).card := by
          rw [Finset.card_erase_of_mem hx0]; omega
        have hc2 := le_trans hc1 (Finset.card_le_card hsub)
        have hv := hV.2.2 x0 hx0S
        omega
      have hbot_bonus : ∀ x ∈ Sbot,
          (Sbot.filter (fun y => x.1 ≤ y.1 ∧ x.2 ≤ y.2 ∧ y ≠ x)).card +
          (Stop.filter (fun y => x.1 ≤ y.1)).card + bonus p1 p2 x.1 ≤ 1 := by
        intro x hx
        have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
        have hxsnd : x.2 < rest.length := mem_grid_snd_lt (hSbot_sub hx)
        have hdisj : Disjoint (Sbot.filter (fun y => x.1 ≤ y.1 ∧ x.2 ≤ y.2 ∧ y ≠ x))
            (Stop.filter (fun y => x.1 ≤ y.1)) := by
          rw [Finset.disjoint_left]; intro y hy1 hy2
          simp only [Sbot, Stop, Finset.mem_filter] at hy1 hy2
          exact hy1.1.2 hy2.1.2
        have hunion : Sbot.filter (fun y => x.1 ≤ y.1 ∧ x.2 ≤ y.2 ∧ y ≠ x) ∪
            Stop.filter (fun y => x.1 ≤ y.1) ⊆
            S.filter (fun y => x.1 ≤ y.1 ∧ x.2 ≤ y.2 ∧ y ≠ x) := by
          intro y hy
          simp only [Finset.mem_union, Sbot, Stop, Finset.mem_filter] at hy ⊢
          rcases hy with ⟨⟨hyS, _⟩, hycond⟩ | ⟨⟨hyS, hysnd⟩, hy1⟩
          · exact ⟨hyS, hycond⟩
          · refine ⟨hyS, hy1, by omega, ?_⟩
            intro hEq; subst hEq; omega
        have hsum := Finset.card_union_of_disjoint hdisj
        have hle := Finset.card_le_card hunion
        have hv := hV.2.2 x hxS
        omega
      refine le_trans ?_ hcur_ge
      unfold stepVal
      rcases (show Stop.card = 0 ∨ Stop.card = 1 ∨ Stop.card = 2 by omega) with h0 | h1 | h2
      · have hVbot : ValidAbove p1 p2 Sbot := by
          refine ⟨hp21, fun x hx => hV.2.1 x (Finset.mem_filter.mp hx).1, fun x hx => ?_⟩
          have hb := hbot_bonus x hx
          omega
        have hih := ih (max lim ma) restT hrestT p1 p2 hp21 (le_trans hp1lim (le_max_left lim ma)) Sbot hSbot_sub hVbot
        have hle1 := lookupV_le_foldOne ma p1 p2 prev
        rw [hcard, h0, zero_add]
        split_ifs
        · exact le_trans hih (le_trans hle1 (le_max_left _ _))
        · exact le_trans hih hle1
      · obtain ⟨u, huEq⟩ := Finset.card_eq_one.mp h1
        have hu : u ∈ Stop := by rw [huEq]; simp
        obtain ⟨ha1, ha2, husnd⟩ := hStop_spec u hu
        have huS : u ∈ S := (Finset.mem_filter.mp hu).1
        have hbonu : bonus p1 p2 u.1 ≤ 1 := by
          have hv := hV.2.2 u huS; omega
        have hp2lt : p2 < u.1 := by
          unfold bonus at hbonu; split_ifs at hbonu <;> omega
        have hVbot : ValidAbove (max p1 u.1) (min p1 u.1) Sbot := by
          refine ⟨min_le_max, fun x hx => hV.2.1 x (Finset.mem_filter.mp hx).1, fun x hx => ?_⟩
          have hb := hbot_bonus x hx
          have htop_cnt : (Stop.filter (fun y => x.1 ≤ y.1)).card = if x.1 ≤ u.1 then 1 else 0 := by
            rw [huEq, Finset.filter_singleton]; split_ifs <;> simp
          rw [htop_cnt] at hb
          have hbon_cmp : bonus (max p1 u.1) (min p1 u.1) x.1 ≤
              bonus p1 p2 x.1 + (if x.1 ≤ u.1 then 1 else 0) := by
            unfold bonus; split_ifs <;> omega
          omega
        have hih := ih (max lim ma) restT hrestT (max p1 u.1) (min p1 u.1) min_le_max
          (max_le (le_trans hp1lim (le_max_left lim ma)) (le_trans ha2 (le_max_right lim ma))) Sbot hSbot_sub hVbot
        have hle1 := one_add_le_foldOne (p1 := p1) prev ha1 ha2 hp2lt
        rw [hcard, h1]
        split_ifs
        · exact le_trans (Nat.add_le_add_left hih 1) (le_trans hle1 (le_max_left _ _))
        · exact le_trans (Nat.add_le_add_left hih 1) hle1
      · obtain ⟨u, v, huv, huvEq⟩ := Finset.card_eq_two.mp h2
        have hu : u ∈ Stop := by rw [huvEq]; simp
        have hv : v ∈ Stop := by rw [huvEq]; simp
        obtain ⟨hu1, hu2, husnd⟩ := hStop_spec u hu
        obtain ⟨hv1, hv2, hvsnd⟩ := hStop_spec v hv
        have huv_fst : u.1 ≠ v.1 := by
          intro hEq; exact huv (Prod.ext hEq (by omega))
        have hmain : ∀ u1 u2 : ℕ × ℕ, Stop = {u1, u2} → u1.1 < u2.1 →
            1 ≤ u1.1 → u2.1 ≤ ma → u1.2 = rest.length → u2.2 = rest.length →
            S.card ≤ if p1 + 2 ≤ ma then
              max (foldOne ma p1 p2 prev) (2 + lookupV prev (p1 + 2) (p1 + 1))
            else foldOne ma p1 p2 prev := by
          intro u1 u2 hEq hlt h1a h2a h1s h2s
          have hu1S : u1 ∈ S := (Finset.mem_filter.mp (by rw [hEq]; simp : u1 ∈ Stop)).1
          have hu2S : u2 ∈ S := (Finset.mem_filter.mp (by rw [hEq]; simp : u2 ∈ Stop)).1
          have hu2_in : u2 ∈ S.filter (fun y => u1.1 ≤ y.1 ∧ u1.2 ≤ y.2 ∧ y ≠ u1) := by
            rw [Finset.mem_filter]
            refine ⟨hu2S, by omega, by omega, ?_⟩
            intro he; rw [he] at hlt; omega
          have hc1 : 1 ≤ (S.filter (fun y => u1.1 ≤ y.1 ∧ u1.2 ≤ y.2 ∧ y ≠ u1)).card :=
            Finset.card_pos.mpr ⟨u2, hu2_in⟩
          have hvu1 := hV.2.2 u1 hu1S
          have hp1lt : p1 < u1.1 := by
            have hbon0 : bonus p1 p2 u1.1 = 0 := by omega
            unfold bonus at hbon0; split_ifs at hbon0 <;> omega
          have hp12 : p1 + 2 ≤ ma := by omega
          have hVbot2 : ValidAbove u2.1 u1.1 Sbot := by
            refine ⟨by omega, fun x hx => hV.2.1 x (Finset.mem_filter.mp hx).1, fun x hx => ?_⟩
            have hb := hbot_bonus x hx
            have hne12 : u1 ≠ u2 := by intro he; rw [he] at hlt; omega
            have htop_cnt : (Stop.filter (fun y => x.1 ≤ y.1)).card =
                (if x.1 ≤ u1.1 then 1 else 0) + (if x.1 ≤ u2.1 then 1 else 0) := by
              rw [hEq, Finset.filter_insert, Finset.filter_singleton]
              split_ifs with h1x h2x
              · rw [Finset.card_pair hne12]
              · simp
              · simp
              · simp
            rw [htop_cnt] at hb
            have hbon_cmp : bonus u2.1 u1.1 x.1 ≤
                ((if x.1 ≤ u1.1 then 1 else 0) + (if x.1 ≤ u2.1 then 1 else 0)) + bonus p1 p2 x.1 := by
              unfold bonus; split_ifs <;> omega
            omega
          have hVbot : ValidAbove (p1 + 2) (p1 + 1) Sbot :=
            hVbot2.mono (by omega) (by omega) (by omega)
          have hih := ih (max lim ma) restT hrestT (p1 + 2) (p1 + 1) (by omega)
            (le_trans hp12 (le_max_right lim ma)) Sbot hSbot_sub hVbot
          rw [if_pos hp12, hcard, h2]
          exact le_trans (Nat.add_le_add_left hih 2) (le_max_right _ _)
        rcases lt_or_gt_of_ne huv_fst with hlt | hgt
        · exact hmain u v huvEq hlt hu1 hv2 husnd hvsnd
        · exact hmain v u (by rw [huvEq, Finset.pair_comm]) hgt hv1 hu2 hvsnd husnd

private def log2Aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n < 2 then 0 else log2Aux fuel (n / 2) + 1

private def log3Aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n < 3 then 0 else log3Aux fuel (n / 3) + 1

private lemma log2Aux_eq (fuel n : ℕ) (h : n < 2 ^ fuel) : log2Aux fuel n = Nat.log 2 n := by
  induction fuel generalizing n with
  | zero => simp at h; subst h; rfl
  | succ fuel ih =>
    unfold log2Aux
    by_cases h2 : n < 2
    · rw [if_pos h2, Nat.log_of_lt h2]
    · rw [if_neg h2, ih (n / 2) (by rw [pow_succ'] at h; omega)]
      symm
      exact Nat.log_of_one_lt_of_le (by omega) (by omega)

private lemma log3Aux_eq (fuel n : ℕ) (h : n < 3 ^ fuel) : log3Aux fuel n = Nat.log 3 n := by
  induction fuel generalizing n with
  | zero => simp at h; subst h; rfl
  | succ fuel ih =>
    unfold log3Aux
    by_cases h3 : n < 3
    · rw [if_pos h3, Nat.log_of_lt h3]
    · rw [if_neg h3, ih (n / 3) (by rw [pow_succ'] at h; omega)]
      symm
      exact Nat.log_of_one_lt_of_le (by omega) (by omega)

private def rowsOf (K : ℕ) : List ℕ :=
  ((List.range (Nat.log 3 K + 1)).map fun b => Nat.log 2 (K / 3 ^ b) + 1).reverse

private def rowsOfFast (K : ℕ) : List ℕ :=
  ((List.range (log3Aux 10 K + 1)).map fun b => log2Aux 15 (K / 3 ^ b) + 1).reverse

private lemma rowsOfFast_eq {K : ℕ} (hK : K < 6561) : rowsOfFast K = rowsOf K := by
  unfold rowsOfFast rowsOf
  have h2 : K < 2 ^ 15 := by omega
  have h3 : K < 3 ^ 10 := by omega
  rw [log3Aux_eq 10 K h3]
  congr 1
  apply List.map_congr_left
  intro b _
  have hd : K / 3 ^ b < 2 ^ 15 := lt_of_le_of_lt (Nat.div_le_self K _) h2
  rw [log2Aux_eq 15 (K / 3 ^ b) hd]

private lemma mem_grid_reverse_map {f : ℕ → ℕ} {B a b : ℕ}
    (hb : b < B) (ha1 : 1 ≤ a) (ha2 : a ≤ f b) :
    (a, b) ∈ grid (((List.range B).map f).reverse) := by
  induction B with
  | zero => omega
  | succ B ih =>
    rw [List.range_succ, List.map_append, List.reverse_append]
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, grid, Finset.mem_union, Finset.mem_image, Finset.mem_Icc,
      List.length_reverse, List.length_map, List.length_range]
    rcases (show b = B ∨ b < B by omega) with rfl | hlt
    · left; exact ⟨a, ⟨ha1, ha2⟩, rfl⟩
    · right; exact ih hlt

private lemma forkFree_smooth_card_le_trace {K : ℕ} (hK : 1 ≤ K) {trace : List (List (List ℕ))}
    (htr : validDPTrace 0 (rowsOf K) trace = true) {S : Finset ℕ}
    (hS_sub : ∀ s ∈ S, s ≤ K ∧ isSmooth3 s = true)
    (hFF : Erdos1062.ForkFree (S : Set ℕ)) :
    S.card ≤ lookupV (trace.headD []) 0 0 := by
  classical
  have hex : ∀ s ∈ S, ∃ p : ℕ × ℕ, s = 2 ^ (p.1 - 1) * 3 ^ p.2 ∧ 1 ≤ p.1 ∧ p ∈ grid (rowsOf K) := by
    intro s hs
    obtain ⟨hsK, hsm⟩ := hS_sub s hs
    obtain ⟨a, b, rfl⟩ := (isSmooth3_iff s).mp hsm
    refine ⟨(a + 1, b), by simp, by omega, ?_⟩
    have h3le : 3 ^ b ≤ K := le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hsK
    have hblt : b < Nat.log 3 K + 1 :=
      Nat.lt_succ_of_le ((Nat.le_log_iff_pow_le (by omega) (by omega)).mpr h3le)
    have h2le : 2 ^ a ≤ K / 3 ^ b := (Nat.le_div_iff_mul_le (by positivity)).mpr hsK
    have hdiv_pos : 0 < K / 3 ^ b := Nat.div_pos h3le (by positivity)
    have hale : a + 1 ≤ Nat.log 2 (K / 3 ^ b) + 1 :=
      Nat.add_le_add_right ((Nat.le_log_iff_pow_le (by omega) (by omega)).mpr h2le) 1
    exact mem_grid_reverse_map hblt (by omega) hale
  choose φ hφ_eq hφ_pos hφ_grid using hex
  let T : Finset (ℕ × ℕ) := S.attach.image (fun x => φ x.1 x.2)
  have hT_card : T.card = S.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro x y hxy
      dsimp only at hxy
      apply Subtype.ext
      rw [hφ_eq x.1 x.2, hφ_eq y.1 y.2, hxy]
  have hT_sub : T ⊆ grid (rowsOf K) := by
    intro p hp
    simp only [T, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    exact hφ_grid s hs
  have hT_val : ValidAbove 0 0 T := by
    refine ⟨le_rfl, ?_, ?_⟩
    · intro p hp
      simp only [T, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hp
      obtain ⟨s, hs, rfl⟩ := hp
      exact hφ_pos s hs
    · intro p hp
      simp only [T, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hp
      obtain ⟨s, hs, rfl⟩ := hp
      have hbon0 : bonus 0 0 (φ s hs).1 = 0 := by
        have := hφ_pos s hs; unfold bonus; split_ifs <;> omega
      rw [hbon0, add_zero]
      by_contra hgt
      have h2 : 1 < (T.filter (fun y => (φ s hs).1 ≤ y.1 ∧ (φ s hs).2 ≤ y.2 ∧ y ≠ φ s hs)).card := by omega
      obtain ⟨q1, hq1, q2, hq2, hqne⟩ := Finset.one_lt_card.mp h2
      simp only [Finset.mem_filter, T, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hq1 hq2
      obtain ⟨⟨t1, ht1, rfl⟩, h1a, h1b, h1ne⟩ := hq1
      obtain ⟨⟨t2, ht2, rfl⟩, h2a, h2b, h2ne⟩ := hq2
      have hsub := hFF s (Finset.mem_coe.mpr hs)
      have hmem1 : t1 ∈ ({b | b ∈ (S : Set ℕ) \ {s} ∧ s ∣ b} : Set ℕ) := by
        refine ⟨⟨Finset.mem_coe.mpr ht1, ?_⟩, ?_⟩
        · intro he; subst he; exact h1ne rfl
        · rw [hφ_eq s hs, hφ_eq t1 ht1, pow23_dvd_iff]
          exact ⟨by omega, h1b⟩
      have hmem2 : t2 ∈ ({b | b ∈ (S : Set ℕ) \ {s} ∧ s ∣ b} : Set ℕ) := by
        refine ⟨⟨Finset.mem_coe.mpr ht2, ?_⟩, ?_⟩
        · intro he; subst he; exact h2ne rfl
        · rw [hφ_eq s hs, hφ_eq t2 ht2, pow23_dvd_iff]
          exact ⟨by omega, h2b⟩
      have hteq : t1 = t2 := hsub hmem1 hmem2
      subst hteq
      exact hqne rfl
  rw [← hT_card]
  exact validDPTrace_sound (rowsOf K) 0 trace htr 0 0 le_rfl le_rfl T hT_sub hT_val

private lemma forkFree_smooth_card_le_two_log {K : ℕ} (hK : 1 ≤ K) {S : Finset ℕ}
    (hS_sub : ∀ s ∈ S, s ≤ K ∧ isSmooth3 s = true)
    (hFF : Erdos1062.ForkFree (S : Set ℕ)) :
    S.card ≤ 2 * (Nat.log 3 K + 1) := by
  classical
  have hex : ∀ s ∈ S, ∃ p : ℕ × ℕ, s = 2 ^ p.1 * 3 ^ p.2 ∧ p.2 ≤ Nat.log 3 K := by
    intro s hs
    obtain ⟨hsK, hsm⟩ := hS_sub s hs
    obtain ⟨a, b, rfl⟩ := (isSmooth3_iff s).mp hsm
    have h3le : 3 ^ b ≤ K := le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hsK
    exact ⟨(a, b), rfl, (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr h3le⟩
  choose φ hφ_eq hφ_le using hex
  let Mset := S.filter (fun s => ∀ t ∈ S, s < t → ¬ s ∣ t)
  let Nset := S.filter (fun s => ¬ (∀ t ∈ S, s < t → ¬ s ∣ t))
  have hsplit : S.card = Mset.card + Nset.card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have hM_le : Mset.card ≤ Nat.log 3 K + 1 := by
    have hinj : Set.InjOn (fun x : {s // s ∈ Mset} => (φ x.1 (Finset.mem_filter.mp x.2).1).2) Set.univ := by
      intro x _ y _ hxy
      dsimp only at hxy
      apply Subtype.ext
      have hxS : x.1 ∈ S := (Finset.mem_filter.mp x.2).1
      have hyS : y.1 ∈ S := (Finset.mem_filter.mp y.2).1
      have hxM := (Finset.mem_filter.mp x.2).2
      have hyM := (Finset.mem_filter.mp y.2).2
      rcases lt_trichotomy (φ x.1 hxS).1 (φ y.1 hyS).1 with hlt | heq | hgt
      · exfalso
        have hdvd : x.1 ∣ y.1 := by
          rw [hφ_eq x.1 hxS, hφ_eq y.1 hyS, pow23_dvd_iff]; exact ⟨le_of_lt hlt, le_of_eq hxy⟩
        have hltv : x.1 < y.1 := by
          rw [hφ_eq x.1 hxS, hφ_eq y.1 hyS, hxy]
          exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by omega) hlt) (by positivity)
        exact hxM y.1 hyS hltv hdvd
      · rw [hφ_eq x.1 hxS, hφ_eq y.1 hyS, heq, hxy]
      · exfalso
        have hdvd : y.1 ∣ x.1 := by
          rw [hφ_eq x.1 hxS, hφ_eq y.1 hyS, pow23_dvd_iff]; exact ⟨le_of_lt hgt, le_of_eq hxy.symm⟩
        have hltv : y.1 < x.1 := by
          rw [hφ_eq x.1 hxS, hφ_eq y.1 hyS, hxy]
          exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by omega) hgt) (by positivity)
        exact hyM x.1 hxS hltv hdvd
    calc Mset.card = Mset.attach.card := Finset.card_attach.symm
      _ = (Mset.attach.image (fun x => (φ x.1 (Finset.mem_filter.mp x.2).1).2)).card :=
          (Finset.card_image_of_injOn (fun x _ y _ h => hinj (Set.mem_univ x) (Set.mem_univ y) h)).symm
      _ ≤ (Finset.range (Nat.log 3 K + 1)).card := by
          refine Finset.card_le_card fun b hb => ?_
          simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range] at hb ⊢
          obtain ⟨s, hs, rfl⟩ := hb
          exact Nat.lt_succ_of_le (hφ_le s (Finset.mem_filter.mp hs).1)
      _ = Nat.log 3 K + 1 := Finset.card_range _
  have hN_le : Nset.card ≤ Nat.log 3 K + 1 := by
    have hinj : Set.InjOn (fun x : {s // s ∈ Nset} => (φ x.1 (Finset.mem_filter.mp x.2).1).2) Set.univ := by
      intro x _ y _ hxy
      dsimp only at hxy
      apply Subtype.ext
      have hxS : x.1 ∈ S := (Finset.mem_filter.mp x.2).1
      have hyS : y.1 ∈ S := (Finset.mem_filter.mp y.2).1
      have hxN := (Finset.mem_filter.mp x.2).2
      have hyN := (Finset.mem_filter.mp y.2).2
      push Not at hxN hyN
      rcases lt_trichotomy (φ x.1 hxS).1 (φ y.1 hyS).1 with hlt | heq | hgt
      · exfalso
        obtain ⟨z, hzS, hyz, hyzdvd⟩ := hyN
        have hxy_dvd : x.1 ∣ y.1 := by
          rw [hφ_eq x.1 hxS, hφ_eq y.1 hyS, pow23_dvd_iff]; exact ⟨le_of_lt hlt, le_of_eq hxy⟩
        have hxy_lt : x.1 < y.1 := by
          rw [hφ_eq x.1 hxS, hφ_eq y.1 hyS, hxy]
          exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by omega) hlt) (by positivity)
        have hsub := hFF x.1 (Finset.mem_coe.mpr hxS)
        have h1 : y.1 ∈ ({b | b ∈ (S : Set ℕ) \ {x.1} ∧ x.1 ∣ b} : Set ℕ) :=
          ⟨⟨Finset.mem_coe.mpr hyS, ne_of_gt hxy_lt⟩, hxy_dvd⟩
        have h2 : z ∈ ({b | b ∈ (S : Set ℕ) \ {x.1} ∧ x.1 ∣ b} : Set ℕ) :=
          ⟨⟨Finset.mem_coe.mpr hzS, ne_of_gt (lt_trans hxy_lt hyz)⟩, dvd_trans hxy_dvd hyzdvd⟩
        have heqyz := hsub h1 h2
        omega
      · rw [hφ_eq x.1 hxS, hφ_eq y.1 hyS, heq, hxy]
      · exfalso
        obtain ⟨z, hzS, hxz, hxzdvd⟩ := hxN
        have hyx_dvd : y.1 ∣ x.1 := by
          rw [hφ_eq x.1 hxS, hφ_eq y.1 hyS, pow23_dvd_iff]; exact ⟨le_of_lt hgt, le_of_eq hxy.symm⟩
        have hyx_lt : y.1 < x.1 := by
          rw [hφ_eq x.1 hxS, hφ_eq y.1 hyS, hxy]
          exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by omega) hgt) (by positivity)
        have hsub := hFF y.1 (Finset.mem_coe.mpr hyS)
        have h1 : x.1 ∈ ({b | b ∈ (S : Set ℕ) \ {y.1} ∧ y.1 ∣ b} : Set ℕ) :=
          ⟨⟨Finset.mem_coe.mpr hxS, ne_of_gt hyx_lt⟩, hyx_dvd⟩
        have h2 : z ∈ ({b | b ∈ (S : Set ℕ) \ {y.1} ∧ y.1 ∣ b} : Set ℕ) :=
          ⟨⟨Finset.mem_coe.mpr hzS, ne_of_gt (lt_trans hyx_lt hxz)⟩, dvd_trans hyx_dvd hxzdvd⟩
        have heqxz := hsub h1 h2
        omega
    calc Nset.card = Nset.attach.card := Finset.card_attach.symm
      _ = (Nset.attach.image (fun x => (φ x.1 (Finset.mem_filter.mp x.2).1).2)).card :=
          (Finset.card_image_of_injOn (fun x _ y _ h => hinj (Set.mem_univ x) (Set.mem_univ y) h)).symm
      _ ≤ (Finset.range (Nat.log 3 K + 1)).card := by
          refine Finset.card_le_card fun b hb => ?_
          simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range] at hb ⊢
          obtain ⟨s, hs, rfl⟩ := hb
          exact Nat.lt_succ_of_le (hφ_le s (Finset.mem_filter.mp hs).1)
      _ = Nat.log 3 K + 1 := Finset.card_range _
  omega

private def ubTable : List (ℕ × ℕ × ℕ) := [
  (1, 2, 1),
  (2, 4, 2),
  (4, 8, 3),
  (8, 16, 4),
  (16, 27, 5),
  (27, 54, 6),
  (54, 81, 7),
  (81, 162, 8),
  (162, 256, 9),
  (256, 512, 10),
  (512, 1024, 11),
  (1024, 2048, 12),
  (2048, 4096, 13),
  (4096, 6561, 14)
]

private def ubContig (cur : ℕ) : List (ℕ × ℕ × ℕ) → Bool
  | [] => cur == 6561
  | (lo, hi, _) :: rest => (lo == cur) && (lo < hi) && ubContig hi rest

private lemma ubTable_contig : ubContig 1 ubTable = true := by decide

private def ubTraces : List (List (List (List ℕ))) := [
  [[[1]]],
  [[[2]], [[2], [1, 1]]],
  [[[3]], [[2], [2, 2], [1, 1, 1]]],
  [[[4]], [[4], [3, 3]], [[2], [2, 2], [2, 2, 2], [1, 1, 1, 1]]],
  [[[5]], [[4], [4, 4], [3, 3, 3]], [[2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [1, 1, 1, 1, 1]]],
  [[[6]], [[6], [5, 5]], [[4], [4, 4], [4, 4, 4], [3, 3, 3, 3]], [[2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1]]],
  [[[7]], [[6], [6, 6], [5, 5, 5]], [[4], [4, 4], [4, 4, 4], [4, 4, 4, 4], [3, 3, 3, 3, 3]], [[2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2]]],
  [[[8]], [[8], [7, 7]], [[6], [6, 6], [6, 6, 6], [5, 5, 5, 5]], [[4], [4, 4], [4, 4, 4], [4, 4, 4, 4], [4, 4, 4, 4, 4], [3, 3, 3, 3, 3, 3]], [[2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2]]],
  [[[9]], [[9], [8, 8]], [[8], [7, 7], [7, 7, 7]], [[6], [6, 6], [6, 6, 6], [5, 5, 5, 5], [5, 5, 5, 5, 4]], [[4], [4, 4], [4, 4, 4], [4, 4, 4, 4], [4, 4, 4, 4, 4], [3, 3, 3, 3, 3, 3]], [[2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1]]],
  [[[10]], [[9], [9, 9], [8, 8, 8]], [[8], [8, 8], [7, 7, 7], [7, 7, 7, 7]], [[6], [6, 6], [6, 6, 6], [6, 6, 6, 6], [5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 4]], [[4], [4, 4], [4, 4, 4], [4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [3, 3, 3, 3, 3, 3, 3]], [[2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1]]],
  [[[11]], [[11], [10, 10]], [[10], [9, 9], [9, 9, 9], [8, 8, 8, 8]], [[8], [8, 8], [8, 8, 8], [7, 7, 7, 7], [7, 7, 7, 7, 7]], [[6], [6, 6], [6, 6, 6], [6, 6, 6, 6], [6, 6, 6, 6, 6], [5, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5, 4]], [[4], [4, 4], [4, 4, 4], [4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4], [3, 3, 3, 3, 3, 3, 3, 3]], [[2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]],
  [[[12]], [[11], [11, 11], [10, 10, 10]], [[10], [10, 10], [9, 9, 9], [9, 9, 9, 9], [8, 8, 8, 8, 8]], [[8], [8, 8], [8, 8, 8], [8, 8, 8, 8], [7, 7, 7, 7, 7], [7, 7, 7, 7, 7, 7]], [[6], [6, 6], [6, 6, 6], [6, 6, 6, 6], [6, 6, 6, 6, 6], [6, 6, 6, 6, 6, 6], [5, 5, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5, 5, 4]], [[4], [4, 4], [4, 4, 4], [4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4, 4], [3, 3, 3, 3, 3, 3, 3, 3, 3]], [[2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]],
  [[[13]], [[13], [12, 12]], [[12], [11, 11], [11, 11, 11], [10, 10, 10, 10]], [[10], [10, 10], [10, 10, 10], [9, 9, 9, 9], [9, 9, 9, 9, 9], [8, 8, 8, 8, 8, 8]], [[8], [8, 8], [8, 8, 8], [8, 8, 8, 8], [8, 8, 8, 8, 8], [7, 7, 7, 7, 7, 7], [7, 7, 7, 7, 7, 7, 7]], [[6], [6, 6], [6, 6, 6], [6, 6, 6, 6], [6, 6, 6, 6, 6], [6, 6, 6, 6, 6, 6], [6, 6, 6, 6, 6, 6, 6], [5, 5, 5, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5, 5, 5, 4]], [[4], [4, 4], [4, 4, 4], [4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4, 4, 4], [3, 3, 3, 3, 3, 3, 3, 3, 3, 3]], [[2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]],
  [[[14]], [[13], [13, 13], [12, 12, 12]], [[12], [12, 12], [11, 11, 11], [11, 11, 11, 11], [10, 10, 10, 10, 10]], [[10], [10, 10], [10, 10, 10], [10, 10, 10, 10], [9, 9, 9, 9, 9], [9, 9, 9, 9, 9, 9]], [[8], [8, 8], [8, 8, 8], [8, 8, 8, 8], [8, 8, 8, 8, 8], [8, 8, 8, 8, 8, 8], [7, 7, 7, 7, 7, 7, 7], [7, 7, 7, 7, 7, 7, 7, 6]], [[6], [6, 6], [6, 6, 6], [6, 6, 6, 6], [6, 6, 6, 6, 6], [6, 6, 6, 6, 6, 6], [6, 6, 6, 6, 6, 6, 6], [6, 6, 6, 6, 6, 6, 6, 6], [5, 5, 5, 5, 5, 5, 5, 5, 5]], [[4], [4, 4], [4, 4, 4], [4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4, 4, 4, 4], [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]], [[2], [2, 2], [2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]]
]

private lemma ubTable_dp_ok :
    ubTable.all (fun e => (1 ≤ e.1) && (e.1 < e.2.1) && (e.2.1 ≤ 6561) &&
      ubTraces.any (fun tr => validDPTrace 0 (rowsOfFast (e.2.1 - 1)) tr && (lookupV (tr.headD []) 0 0 ≤ e.2.2))) = true := by
  decide

private lemma ubTable_covers (K : ℕ) (h1 : 1 ≤ K) (h2 : K < 6561) :
    ∃ e ∈ ubTable, e.1 ≤ K ∧ K < e.2.1 := by
  suffices ∀ (cur : ℕ) (l : List (ℕ × ℕ × ℕ)), ubContig cur l = true →
      cur ≤ K → K < 6561 → ∃ e ∈ l, e.1 ≤ K ∧ K < e.2.1 from
    this 1 ubTable ubTable_contig h1 h2
  intro cur l
  induction l generalizing cur with
  | nil =>
    intro hc hlo hhi; simp only [ubContig, beq_iff_eq] at hc; omega
  | cons e rest ih =>
    intro hc hlo hhi
    rcases e with ⟨lo, hi, g⟩
    simp only [ubContig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨rfl, hlh⟩, hrest⟩ := hc
    by_cases hK : K < hi
    · exact ⟨(lo, hi, g), List.mem_cons_self .., hlo, hK⟩
    · obtain ⟨e', he', h1', h2'⟩ := ih hi hrest (by omega) hhi
      exact ⟨e', List.mem_cons_of_mem _ he', h1', h2'⟩

private def ubCeilSum : ℕ :=
  ubTable.foldl (fun acc e =>
    let lo := e.1; let hi := e.2.1; let g := e.2.2
    acc + (1000000000 * g * (hi - lo) + 3 * lo * hi - 1) / (3 * lo * hi)) 0

private lemma ubCeilSum_ok :
    ubCeilSum + (1000000000 * 19 + 19682) / 19683 ≤ 673500000 := by
  decide

private lemma nat_ceil_div_real {a b : ℕ} (hb : 0 < b) :
    (a : ℝ) / b ≤ (((a + b - 1) / b : ℕ) : ℝ) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hbpos]
  have h : a ≤ ((a + b - 1) / b) * b := by
    have := Nat.lt_div_mul_add hb (a := a + b - 1); omega
  exact_mod_cast h

private lemma nat_floor_div_real {a b : ℕ} (_hb : 0 < b) :
    (((a / b : ℕ) : ℝ)) ≤ (a : ℝ) / b :=
  Nat.cast_div_le

private lemma ub_term_le_ceil {lo hi : ℕ} (g : ℕ) (hlo : 1 ≤ lo) (hlh : lo < hi) :
    (g : ℝ) / 3 * ((1 : ℝ) / lo - 1 / hi) ≤
      (((1000000000 * g * (hi - lo) + 3 * lo * hi - 1) / (3 * lo * hi) : ℕ) : ℝ) / 1000000000 := by
  have hlo0 : (lo : ℝ) ≠ 0 := by exact_mod_cast (by omega : lo ≠ 0)
  have hhi0 : (hi : ℝ) ≠ 0 := by exact_mod_cast (by omega : hi ≠ 0)
  have h1 : (g : ℝ) / 3 * ((1 : ℝ) / lo - 1 / hi) =
      ((1000000000 * g * (hi - lo) : ℕ) : ℝ) / (3 * lo * hi : ℕ) / 1000000000 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (le_of_lt hlh)]
    push_cast
    field_simp
  rw [h1]
  have hden : 0 < 3 * lo * hi := by nlinarith
  exact div_le_div_of_nonneg_right (nat_ceil_div_real hden) (by positivity)

private lemma ub_table_real_sum :
    (ubTable.map (fun e => (e.2.2 : ℝ) / 3 * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum +
      (19 : ℝ) / 19683 ≤ (6735 : ℝ) / 10000 := by
  have hfold : ∀ (l : List (ℕ × ℕ × ℕ)) (init : ℕ),
      (∀ e ∈ l, 1 ≤ e.1 ∧ e.1 < e.2.1) →
      (l.map (fun e => (e.2.2 : ℝ) / 3 * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum + (init : ℝ) / 1000000000 ≤
        ((l.foldl (fun acc e =>
          acc + (1000000000 * e.2.2 * (e.2.1 - e.1) + 3 * e.1 * e.2.1 - 1) / (3 * e.1 * e.2.1)) init : ℕ) : ℝ) / 1000000000 := by
    intro l
    induction l with
    | nil => intro init _; simp
    | cons e l ih =>
      intro init hok
      have he := hok e (List.mem_cons_self ..)
      have hl : ∀ e' ∈ l, 1 ≤ e'.1 ∧ e'.1 < e'.2.1 := fun e' he' => hok e' (List.mem_cons_of_mem _ he')
      simp only [List.map_cons, List.sum_cons, List.foldl_cons]
      have hterm := ub_term_le_ceil e.2.2 he.1 he.2
      have hstep := ih (init + (1000000000 * e.2.2 * (e.2.1 - e.1) + 3 * e.1 * e.2.1 - 1) / (3 * e.1 * e.2.1)) hl
      push_cast at hstep
      linarith
  have hok : ∀ e ∈ ubTable, 1 ≤ e.1 ∧ e.1 < e.2.1 := by
    intro e he
    have h := List.all_eq_true.mp ubTable_dp_ok e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hbody := hfold ubTable 0 hok
  simp only [Nat.cast_zero, zero_div, add_zero] at hbody
  have htail : (19 : ℝ) / 19683 ≤
      (((1000000000 * 19 + 19682) / 19683 : ℕ) : ℝ) / 1000000000 := by
    have h := nat_ceil_div_real (a := 1000000000 * 19) (b := 19683) (by omega)
    have h2 : ((1000000000 * 19 : ℕ) : ℝ) / 19683 / 1000000000 = (19 : ℝ) / 19683 := by norm_num
    rw [← h2]
    exact div_le_div_of_nonneg_right h (by positivity)
  have htot : ((ubCeilSum + (1000000000 * 19 + 19682) / 19683 : ℕ) : ℝ) ≤ 673500000 := by
    exact_mod_cast ubCeilSum_ok
  unfold ubCeilSum at htot
  push_cast at htot
  linarith

private lemma geom_sum_third (L : ℕ) :
    ∑ j ∈ Finset.Icc 9 L, ((1 : ℝ) / (3 : ℝ) ^ (j + 1)) ≤ 1 / (2 * 19683 : ℝ) := by
  by_cases hL : L < 9
  · have : Finset.Icc 9 L = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty]; positivity
  · have hsum : ∀ k : ℕ, ∑ i ∈ Finset.range k, ((1 : ℝ) / 3) ^ i ≤ 3 / 2 := by
      intro k
      induction k with
      | zero => simp; norm_num
      | succ k ih =>
        rw [Finset.sum_range_succ']
        have hmul : ∑ i ∈ Finset.range k, ((1 : ℝ) / 3) ^ (i + 1) =
            (1 / 3 : ℝ) * ∑ i ∈ Finset.range k, ((1 : ℝ) / 3) ^ i := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
        rw [hmul, pow_zero]
        linarith
    have hshift : ∑ j ∈ Finset.Icc 9 L, ((1 : ℝ) / (3 : ℝ) ^ (j + 1)) =
        ((1 : ℝ) / (3 : ℝ) ^ 10) * ∑ i ∈ Finset.range (L - 9 + 1), ((1 : ℝ) / 3) ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun j _ => j - 9) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
      · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
      · intro i hi; simp only [Finset.mem_range] at hi
        refine ⟨i + 9, by simp only [Finset.mem_Icc]; omega, by omega⟩
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        have hpow : j + 1 = 10 + (j - 9) := by omega
        rw [hpow, pow_add, one_div_pow]; ring
    rw [hshift]
    have hb := hsum (L - 9 + 1)
    have h1 : ((1 : ℝ) / (3 : ℝ) ^ 10) * (3 / 2 : ℝ) = 1 / (2 * 19683 : ℝ) := by norm_num
    nlinarith [show (0 : ℝ) ≤ (1 : ℝ) / (3 : ℝ) ^ 10 by positivity]

private lemma log3_le_linear (n : ℕ) (hn : 3 ^ 20 ≤ n) :
    ((Nat.log 3 n : ℕ) : ℝ) ≤ (n : ℝ) / 1000000 := by
  have hpow : ∀ k : ℕ, 20 ≤ k → 1000000 * k ≤ 3 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      calc 1000000 * (k + 1) ≤ 3 * (1000000 * k) := by omega
        _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (k + 1) := by ring
  have hlog20 : 20 ≤ Nat.log 3 n := (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr hn
  have h1 : 1000000 * Nat.log 3 n ≤ 3 ^ Nat.log 3 n := hpow _ hlog20
  have h2 : 3 ^ Nat.log 3 n ≤ n := Nat.pow_log_le_self 3 (by omega)
  have h3 : (1000000 : ℝ) * (Nat.log 3 n : ℕ) ≤ n := by exact_mod_cast le_trans h1 h2
  linarith

private lemma tail_sum_bound (n : ℕ) (hn : 6561 ≤ n) :
    ((∑ m ∈ (Finset.Icc 1 (n / 6561)).filter (fun m => p6 m),
        2 * (Nat.log 3 (n / m) + 1) : ℕ) : ℝ) ≤
      (19 : ℝ) / 19683 * n + 4 * (Nat.log 3 n : ℕ) + 40 := by
  let Mtail := (Finset.Icc 1 (n / 6561)).filter (fun m => p6 m)
  let L := Nat.log 3 n
  have hterm : ∀ m ∈ Mtail,
      Nat.log 3 (n / m) + 1 = 9 + ((Finset.Icc 9 L).filter (fun j => m ≤ n / 3 ^ j)).card := by
    intro m hm
    simp only [Mtail, Finset.mem_filter, Finset.mem_Icc] at hm
    have hmpos : 0 < m := by omega
    have hge : 6561 ≤ n / m := (Nat.le_div_iff_mul_le hmpos).mpr (by
      have := Nat.mul_div_le n 6561; nlinarith)
    have hlog_ge : 8 ≤ Nat.log 3 (n / m) :=
      (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr (by norm_num; exact hge)
    have hlog_le : Nat.log 3 (n / m) ≤ L := Nat.log_mono_right (Nat.div_le_self n m)
    have hfilt : (Finset.Icc 9 L).filter (fun j => m ≤ n / 3 ^ j) =
        Finset.Icc 9 (Nat.log 3 (n / m)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hj9, _⟩, hmj⟩
        refine ⟨hj9, (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr ?_⟩
        have hmul : m * 3 ^ j ≤ n := (Nat.le_div_iff_mul_le (by positivity : 0 < 3 ^ j)).mp hmj
        exact (Nat.le_div_iff_mul_le hmpos).mpr (by linarith)
      · rintro ⟨hj9, hjlog⟩
        refine ⟨⟨hj9, le_trans hjlog hlog_le⟩, ?_⟩
        have hpow : 3 ^ j ≤ n / m := (Nat.le_log_iff_pow_le (by omega) (by omega)).mp hjlog
        have hmul : 3 ^ j * m ≤ n := (Nat.le_div_iff_mul_le hmpos).mp hpow
        exact (Nat.le_div_iff_mul_le (by positivity : 0 < 3 ^ j)).mpr (by linarith)
    rw [hfilt, Nat.card_Icc]
    omega
  have hsum_eq : ∑ m ∈ Mtail, (Nat.log 3 (n / m) + 1) =
      9 * Mtail.card + ∑ j ∈ Finset.Icc 9 L, (Mtail.filter (fun m => m ≤ n / 3 ^ j)).card := by
    calc ∑ m ∈ Mtail, (Nat.log 3 (n / m) + 1)
        = ∑ m ∈ Mtail, (9 + ((Finset.Icc 9 L).filter (fun j => m ≤ n / 3 ^ j)).card) :=
          Finset.sum_congr rfl hterm
      _ = 9 * Mtail.card + ∑ m ∈ Mtail, ∑ j ∈ Finset.Icc 9 L, if m ≤ n / 3 ^ j then 1 else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
          congr 1; refine Finset.sum_congr rfl fun m _ => ?_; rw [Finset.card_filter]
      _ = 9 * Mtail.card + ∑ j ∈ Finset.Icc 9 L, ∑ m ∈ Mtail, if m ≤ n / 3 ^ j then 1 else 0 := by
          rw [Finset.sum_comm]
      _ = 9 * Mtail.card + ∑ j ∈ Finset.Icc 9 L, (Mtail.filter (fun m => m ≤ n / 3 ^ j)).card := by
          congr 1; refine Finset.sum_congr rfl fun j _ => ?_; rw [Finset.card_filter]
  have h2sum : ∑ m ∈ Mtail, 2 * (Nat.log 3 (n / m) + 1) =
      2 * (9 * Mtail.card + ∑ j ∈ Finset.Icc 9 L, (Mtail.filter (fun m => m ≤ n / 3 ^ j)).card) := by
    rw [← Finset.mul_sum, hsum_eq]
  change ((∑ m ∈ Mtail, 2 * (Nat.log 3 (n / m) + 1) : ℕ) : ℝ) ≤ _
  rw [h2sum]
  have hMtail_ub : (Mtail.card : ℝ) ≤ (n : ℝ) / 19683 + 2 := by
    have h1 := cntP_p6_upper (n / 6561)
    have h2 : ((n / 6561 : ℕ) : ℝ) ≤ (n : ℝ) / 6561 := Nat.cast_div_le
    change (cntP p6 (n / 6561) : ℝ) ≤ (n : ℝ) / 19683 + 2
    linarith
  have hj_ub : ∀ j ∈ Finset.Icc 9 L,
      ((Mtail.filter (fun m => m ≤ n / 3 ^ j)).card : ℝ) ≤ (n : ℝ) / (3 : ℝ) ^ (j + 1) + 2 := by
    intro j _
    have hsub : Mtail.filter (fun m => m ≤ n / 3 ^ j) ⊆
        (Finset.Icc 1 (n / 3 ^ j)).filter (fun m => p6 m) := by
      intro m hm
      simp only [Mtail, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      exact ⟨⟨hm.1.1.1, hm.2⟩, hm.1.2⟩
    have hc : ((Mtail.filter (fun m => m ≤ n / 3 ^ j)).card : ℝ) ≤ (cntP p6 (n / 3 ^ j) : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h1 := cntP_p6_upper (n / 3 ^ j)
    have h2 : ((n / 3 ^ j : ℕ) : ℝ) ≤ (n : ℝ) / (3 ^ j : ℕ) := Nat.cast_div_le
    have h3 : ((n : ℝ) / (3 ^ j : ℕ)) / 3 = (n : ℝ) / (3 : ℝ) ^ (j + 1) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]; ring
    linarith
  have hsum_j : ((∑ j ∈ Finset.Icc 9 L, (Mtail.filter (fun m => m ≤ n / 3 ^ j)).card : ℕ) : ℝ) ≤
      (n : ℝ) / (2 * 19683 : ℝ) + 2 * (L : ℝ) := by
    rw [Nat.cast_sum]
    calc ∑ j ∈ Finset.Icc 9 L, ((Mtail.filter (fun m => m ≤ n / 3 ^ j)).card : ℝ)
        ≤ ∑ j ∈ Finset.Icc 9 L, ((n : ℝ) / (3 : ℝ) ^ (j + 1) + 2) := Finset.sum_le_sum hj_ub
      _ = (n : ℝ) * (∑ j ∈ Finset.Icc 9 L, (1 : ℝ) / (3 : ℝ) ^ (j + 1)) +
          2 * ((Finset.Icc 9 L).card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
          congr 1
          · refine Finset.sum_congr rfl fun j _ => ?_; ring
          · ring
      _ ≤ (n : ℝ) * (1 / (2 * 19683 : ℝ)) + 2 * (L : ℝ) := by
          have hg := geom_sum_third L
          have hcardL : ((Finset.Icc 9 L).card : ℝ) ≤ L := by
            rw [Nat.card_Icc]; exact_mod_cast (by omega : L + 1 - 9 ≤ L)
          nlinarith [show (0 : ℝ) ≤ n by positivity]
      _ = (n : ℝ) / (2 * 19683 : ℝ) + 2 * (L : ℝ) := by ring
  dsimp only [Mtail, L] at hMtail_ub hsum_j ⊢
  rw [Nat.cast_sum] at hsum_j
  push_cast
  linarith

private lemma upper_bound_eventually :
    ∀ᶠ n in atTop, (Erdos1062.f n : ℝ) ≤ (0.6736 : ℝ) * n := by
  rw [Filter.eventually_atTop]
  refine ⟨3 ^ 20, fun n hn => ?_⟩
  classical
  have hn6561 : 6561 ≤ n := le_trans (by decide : 6561 ≤ 3 ^ 20) hn
  have hwit : ∃ A ⊆ Set.Icc 1 n, Erdos1062.ForkFree A ∧ A.ncard = Erdos1062.f n := by
    have h0 : ∃ A ⊆ Set.Icc 1 n, Erdos1062.ForkFree A ∧ A.ncard = 0 :=
      ⟨∅, Set.empty_subset _, fun a ha => False.elim ha, Set.ncard_empty _⟩
    exact Nat.findGreatest_spec (P := fun k => ∃ A ⊆ Set.Icc 1 n, Erdos1062.ForkFree A ∧ A.ncard = k)
      (Nat.zero_le n) h0
  obtain ⟨A, hAsub, hAFF, hAcard⟩ := hwit
  have hAfin : A.Finite := (Set.finite_Icc 1 n).subset hAsub
  let Af : Finset ℕ := hAfin.toFinset
  have hAf_card : Af.card = Erdos1062.f n := by
    rw [← hAcard, Set.ncard_eq_toFinset_card A hAfin]
  have hAf_sub : Af ⊆ Finset.Icc 1 n := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    exact Finset.mem_Icc.mpr (hAsub hx)
  have hAf_FF : Erdos1062.ForkFree (Af : Set ℕ) := by
    have : (Af : Set ℕ) = A := Set.Finite.coe_toFinset hAfin
    rwa [this]
  let M_all := (Finset.Icc 1 n).filter (fun m => p6 m)
  have hmap : ∀ x ∈ Af, oddPart23 x ∈ M_all := by
    intro x hx
    have hxIcc := Finset.mem_Icc.mp (hAf_sub hx)
    simp only [M_all, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨oddPart23_pos hxIcc.1, le_trans (oddPart23_le x hxIcc.1) hxIcc.2⟩,
           oddPart23_p6 hxIcc.1⟩
  have hpart : Af.card = ∑ m ∈ M_all, (Af.filter (fun x => oddPart23 x = m)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext x
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun hx => ⟨oddPart23 x, hmap x hx, hx, rfl⟩, fun ⟨_, _, hx, _⟩ => hx⟩
    · intro m1 _ m2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]; intro x hx1 hx2
      rw [Finset.mem_filter] at hx1 hx2
      exact hne (hx1.2.symm.trans hx2.2)
  have hfiber_ff : ∀ m ∈ M_all, ∃ S : Finset ℕ,
      S.card = (Af.filter (fun x => oddPart23 x = m)).card ∧
      (∀ s ∈ S, s ≤ n / m ∧ isSmooth3 s = true) ∧
      Erdos1062.ForkFree (S : Set ℕ) := by
    intro m hm
    simp only [M_all, Finset.mem_filter, Finset.mem_Icc] at hm
    let Fm := Af.filter (fun x => oddPart23 x = m)
    let S := Fm.image (fun x => x / m)
    refine ⟨S, ?_, ?_, ?_⟩
    · refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
      rw [Finset.mem_coe] at hx hy
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      have hxpos : 0 < x := (Finset.mem_Icc.mp (hAf_sub hx'.1)).1
      have hypos : 0 < y := (Finset.mem_Icc.mp (hAf_sub hy'.1)).1
      have hxm := mul_smoothPart hxpos; rw [hx'.2] at hxm
      have hym := mul_smoothPart hypos; rw [hy'.2] at hym
      rw [← hxm, ← hym, hxy]
    · intro s hs
      simp only [S, Fm, Finset.mem_image, Finset.mem_filter] at hs
      obtain ⟨x, ⟨hxAf, hxm⟩, rfl⟩ := hs
      have hxIcc := Finset.mem_Icc.mp (hAf_sub hxAf)
      refine ⟨Nat.div_le_div_right hxIcc.2, ?_⟩
      rw [← hxm]; exact smoothPart_isSmooth3 hxIcc.1
    · intro s hs
      simp only [Finset.mem_coe, S, Fm, Finset.mem_image, Finset.mem_filter] at hs
      obtain ⟨x, ⟨hxAf, hxm⟩, rfl⟩ := hs
      have hxpos : 0 < x := (Finset.mem_Icc.mp (hAf_sub hxAf)).1
      have hmx : m * (x / m) = x := by rw [← hxm]; exact mul_smoothPart hxpos
      intro t1 ht1 t2 ht2
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe,
        S, Fm, Finset.mem_image, Finset.mem_filter] at ht1 ht2
      obtain ⟨⟨⟨y1, ⟨hy1Af, hy1m⟩, rfl⟩, hne1⟩, hdvd1⟩ := ht1
      obtain ⟨⟨⟨y2, ⟨hy2Af, hy2m⟩, rfl⟩, hne2⟩, hdvd2⟩ := ht2
      have hy1pos : 0 < y1 := (Finset.mem_Icc.mp (hAf_sub hy1Af)).1
      have hy2pos : 0 < y2 := (Finset.mem_Icc.mp (hAf_sub hy2Af)).1
      have hmy1 : m * (y1 / m) = y1 := by rw [← hy1m]; exact mul_smoothPart hy1pos
      have hmy2 : m * (y2 / m) = y2 := by rw [← hy2m]; exact mul_smoothPart hy2pos
      have hsub := hAf_FF x (Finset.mem_coe.mpr hxAf)
      have hm1 : y1 ∈ ({b | b ∈ (Af : Set ℕ) \ {x} ∧ x ∣ b} : Set ℕ) := by
        refine ⟨⟨Finset.mem_coe.mpr hy1Af, ?_⟩, ?_⟩
        · intro he; subst he; exact hne1 rfl
        · rw [← hmx, ← hmy1]; exact mul_dvd_mul_left m hdvd1
      have hm2 : y2 ∈ ({b | b ∈ (Af : Set ℕ) \ {x} ∧ x ∣ b} : Set ℕ) := by
        refine ⟨⟨Finset.mem_coe.mpr hy2Af, ?_⟩, ?_⟩
        · intro he; subst he; exact hne2 rfl
        · rw [← hmx, ← hmy2]; exact mul_dvd_mul_left m hdvd2
      have hy12 := hsub hm1 hm2
      rw [hy12]
  let Mtail := (Finset.Icc 1 (n / 6561)).filter (fun m => p6 m)
  let Mbody := (Finset.Icc (n / 6561 + 1) n).filter (fun m => p6 m)
  have hMsplit : M_all = Mtail ∪ Mbody := by
    ext m; simp only [M_all, Mtail, Mbody, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    have : n / 6561 ≤ n := Nat.div_le_self n 6561
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      rcases le_or_gt m (n / 6561) with hle | hgt
      · left; exact ⟨⟨h1, hle⟩, hp⟩
      · right; exact ⟨⟨by omega, h2⟩, hp⟩
    · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩) <;> exact ⟨⟨by omega, by omega⟩, hp⟩
  have hMdisj : Disjoint Mtail Mbody := by
    rw [Finset.disjoint_left]; intro m h1 h2
    simp only [Mtail, Mbody, Finset.mem_filter, Finset.mem_Icc] at h1 h2; omega
  have htail_le : ∑ m ∈ Mtail, (Af.filter (fun x => oddPart23 x = m)).card ≤
      ∑ m ∈ Mtail, 2 * (Nat.log 3 (n / m) + 1) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm_all : m ∈ M_all := by rw [hMsplit]; exact Finset.mem_union_left _ hm
    obtain ⟨S, hSc, hSs, hSff⟩ := hfiber_ff m hm_all
    rw [← hSc]
    have hmIcc := (Finset.mem_filter.mp hm_all).1
    have hKpos : 1 ≤ n / m := Nat.div_pos (Finset.mem_Icc.mp hmIcc).2 (Finset.mem_Icc.mp hmIcc).1
    exact forkFree_smooth_card_le_two_log hKpos hSs hSff
  have hbody_le : ∑ m ∈ Mbody, (Af.filter (fun x => oddPart23 x = m)).card ≤
      (ubTable.map (fun e => e.2.2 * ((Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => p6 m)).card)).sum := by
    let piece (e : ℕ × ℕ × ℕ) : Finset ℕ := (Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => p6 m)
    have hcov : ∀ m ∈ Mbody, ∃ e ∈ ubTable, m ∈ piece e ∧
        (Af.filter (fun x => oddPart23 x = m)).card ≤ e.2.2 := by
      intro m hm
      have hm_all : m ∈ M_all := by rw [hMsplit]; exact Finset.mem_union_right _ hm
      simp only [Mbody, Finset.mem_filter, Finset.mem_Icc] at hm
      have hmpos : 0 < m := by omega
      have hK1 : 1 ≤ n / m := Nat.div_pos hm.1.2 hmpos
      have hK2 : n / m < 6561 := by
        rw [Nat.div_lt_iff_lt_mul hmpos]
        have := Nat.lt_div_mul_add (by omega : 0 < 6561) (a := n); nlinarith
      obtain ⟨e, he, hle, hlt⟩ := ubTable_covers (n / m) hK1 hK2
      have hok := List.all_eq_true.mp ubTable_dp_ok e he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      refine ⟨e, he, ?_, ?_⟩
      · simp only [piece, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, hm.2⟩
        · have hlt1 : n < e.2.1 * m := (Nat.div_lt_iff_lt_mul hmpos).mp hlt
          have hlt2 : n / e.2.1 < m := (Nat.div_lt_iff_lt_mul (by omega : 0 < e.2.1)).mpr (by linarith)
          omega
        · have hle1 : e.1 * m ≤ n := (Nat.le_div_iff_mul_le hmpos).mp hle
          exact (Nat.le_div_iff_mul_le (by omega : 0 < e.1)).mpr (by linarith)
      · obtain ⟨S, hSc, hSs, hSff⟩ := hfiber_ff m hm_all
        rw [← hSc]
        have hSs' : ∀ s ∈ S, s ≤ e.2.1 - 1 ∧ isSmooth3 s = true := fun s hs =>
          ⟨le_trans (hSs s hs).1 (by omega), (hSs s hs).2⟩
        have htr_any := List.any_eq_true.mp hok.2
        obtain ⟨tr, _, htr_ok⟩ := htr_any
        simp only [Bool.and_eq_true, decide_eq_true_eq] at htr_ok
        have htr_real : validDPTrace 0 (rowsOf (e.2.1 - 1)) tr = true := by
          rw [← rowsOfFast_eq (by omega)]; exact htr_ok.1
        exact le_trans (forkFree_smooth_card_le_trace (by omega) htr_real hSs' hSff) htr_ok.2
    have hsum_step : ∀ (l : List (ℕ × ℕ × ℕ)) (T : Finset ℕ),
        (∀ m ∈ T, ∃ e ∈ l, m ∈ piece e ∧ (Af.filter (fun x => oddPart23 x = m)).card ≤ e.2.2) →
        ∑ m ∈ T, (Af.filter (fun x => oddPart23 x = m)).card ≤
          (l.map (fun e => e.2.2 * (piece e).card)).sum := by
      intro l
      induction l with
      | nil =>
        intro T hT
        have hTe : T = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro m hm; obtain ⟨_, hmem, _⟩ := hT m hm; simp at hmem
        subst hTe; simp
      | cons e l ih =>
        intro T hT
        let T1 := T.filter (fun m => m ∈ piece e ∧ (Af.filter (fun x => oddPart23 x = m)).card ≤ e.2.2)
        let T2 := T.filter (fun m => ¬ (m ∈ piece e ∧ (Af.filter (fun x => oddPart23 x = m)).card ≤ e.2.2))
        have hTsplit : ∑ m ∈ T, (Af.filter (fun x => oddPart23 x = m)).card =
            ∑ m ∈ T1, (Af.filter (fun x => oddPart23 x = m)).card +
            ∑ m ∈ T2, (Af.filter (fun x => oddPart23 x = m)).card :=
          (Finset.sum_filter_add_sum_filter_not T _ _).symm
        rw [hTsplit, List.map_cons, List.sum_cons]
        refine Nat.add_le_add ?_ (ih T2 fun m hm => ?_)
        · calc ∑ m ∈ T1, (Af.filter (fun x => oddPart23 x = m)).card
              ≤ ∑ _m ∈ T1, e.2.2 := Finset.sum_le_sum fun m hm => (Finset.mem_filter.mp hm).2.2
            _ = T1.card * e.2.2 := by simp
            _ = e.2.2 * T1.card := mul_comm _ _
            _ ≤ e.2.2 * (piece e).card := Nat.mul_le_mul_left _ (Finset.card_le_card fun m hm =>
                (Finset.mem_filter.mp hm).2.1)
        · simp only [T2, Finset.mem_filter] at hm
          obtain ⟨e', he', hp', hle'⟩ := hT m hm.1
          simp only [List.mem_cons] at he'
          rcases he' with rfl | hmem
          · exfalso; exact hm.2 ⟨hp', hle'⟩
          · exact ⟨e', hmem, hp', hle'⟩
    exact hsum_step ubTable Mbody hcov
  have hbody_real :
      (((ubTable.map (fun e => e.2.2 * ((Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => p6 m)).card)).sum : ℕ) : ℝ) ≤
        (ubTable.map (fun e => (e.2.2 : ℝ) / 3 * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum * n + 2000 := by
    have hgen : ∀ l : List (ℕ × ℕ × ℕ),
        (∀ e ∈ l, 1 ≤ e.1 ∧ e.1 < e.2.1) →
        (((l.map (fun e => e.2.2 * ((Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => p6 m)).card)).sum : ℕ) : ℝ) ≤
          (l.map (fun e => (e.2.2 : ℝ) / 3 * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum * n +
            (((l.map (fun e => 7 * e.2.2)).sum : ℕ) : ℝ) := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons e l ih =>
        intro hok
        have he := hok e (List.mem_cons_self ..)
        have hih := ih (fun e' he' => hok e' (List.mem_cons_of_mem _ he'))
        simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul]
        have hint := (cntP_interval_real_bounds p6 6 (by omega) p6_periodic n e.1 e.2.1 (by omega) (le_of_lt he.2)).2
        rw [cntPeriod_p6] at hint
        have hmul := mul_le_mul_of_nonneg_left hint (Nat.cast_nonneg e.2.2)
        have hre : (e.2.2 : ℝ) * (((2 : ℕ) : ℝ) / (6 : ℕ) * ((1 : ℝ) / e.1 - 1 / e.2.1) * n + (3 * ((2 : ℕ) : ℝ) + 1)) =
            (e.2.2 : ℝ) / 3 * ((1 : ℝ) / e.1 - 1 / e.2.1) * n + (7 : ℕ) * e.2.2 := by
          push_cast; ring
        rw [hre] at hmul
        push_cast at hmul hih ⊢
        linarith
    have hok : ∀ e ∈ ubTable, 1 ≤ e.1 ∧ e.1 < e.2.1 := by
      intro e he
      have h := List.all_eq_true.mp ubTable_dp_ok e he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1
    have hconst : (((ubTable.map (fun e => 7 * e.2.2)).sum : ℕ) : ℝ) ≤ 2000 := by
      have : (ubTable.map (fun e => 7 * e.2.2)).sum ≤ 2000 := by decide
      exact_mod_cast this
    have h1 := hgen ubTable hok
    linarith
  have hAf_le : (Erdos1062.f n : ℝ) ≤
      (((ubTable.map (fun e => e.2.2 * ((Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => p6 m)).card)).sum : ℕ) : ℝ) +
      ((∑ m ∈ Mtail, 2 * (Nat.log 3 (n / m) + 1) : ℕ) : ℝ) := by
    rw [← hAf_card, hpart, hMsplit, Finset.sum_union hMdisj]
    have htot := Nat.add_le_add htail_le hbody_le
    have htotr : ((∑ m ∈ Mtail, (Af.filter (fun x => oddPart23 x = m)).card +
        ∑ m ∈ Mbody, (Af.filter (fun x => oddPart23 x = m)).card : ℕ) : ℝ) ≤
      ((∑ m ∈ Mtail, 2 * (Nat.log 3 (n / m) + 1) +
        (ubTable.map (fun e => e.2.2 * ((Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => p6 m)).card)).sum : ℕ) : ℝ) := by
      exact_mod_cast htot
    push_cast at htotr ⊢
    linarith
  have htail_r := tail_sum_bound n hn6561
  have hdens := ub_table_real_sum
  have hlog := log3_le_linear n hn
  have hn_big : (3 ^ 20 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul_dens : ((ubTable.map (fun e => (e.2.2 : ℝ) / 3 * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum +
      (19 : ℝ) / 19683) * n ≤ (6735 : ℝ) / 10000 * n :=
    mul_le_mul_of_nonneg_right hdens (by positivity)
  linarith

/- ### Section 4: Lower bound `0.6725 * n ≤ f n` -/

private def tbl0 : List (ℕ × ℕ × List ℕ) := [
  (1, 2, [1]),
  (2, 3, [1, 2]),
  (3, 4, [2, 3]),
  (4, 6, [2, 3, 4]),
  (6, 8, [3, 4, 6]),
  (8, 9, [3, 4, 6, 8]),
  (9, 12, [4, 6, 8, 9]),
  (12, 16, [6, 8, 9, 12]),
  (16, 18, [6, 8, 9, 12, 16]),
  (18, 24, [8, 9, 12, 16, 18]),
  (24, 27, [9, 12, 16, 18, 24]),
  (27, 32, [6, 8, 9, 12, 16, 27]),
  (32, 36, [12, 16, 18, 24, 27, 32]),
  (36, 48, [16, 18, 24, 27, 32, 36]),
  (48, 54, [18, 24, 27, 32, 36, 48]),
  (54, 64, [12, 16, 18, 24, 27, 32, 54]),
  (64, 72, [24, 27, 32, 36, 48, 54, 64]),
  (72, 81, [27, 32, 36, 48, 54, 64, 72]),
  (81, 108, [18, 24, 27, 32, 36, 48, 64, 81]),
  (108, 128, [24, 32, 36, 48, 54, 64, 81, 108]),
  (128, 144, [48, 54, 64, 72, 81, 96, 108, 128]),
  (144, 162, [54, 64, 72, 81, 96, 108, 128, 144]),
  (162, 216, [36, 48, 54, 64, 72, 81, 96, 128, 162]),
  (216, 243, [48, 64, 72, 81, 96, 108, 128, 162, 216]),
  (243, 256, [54, 72, 81, 96, 108, 128, 144, 192, 243]),
  (256, 324, [54, 72, 81, 96, 108, 128, 144, 192, 243, 256]),
  (324, 432, [72, 96, 108, 128, 144, 162, 192, 243, 256, 324]),
  (432, 486, [96, 128, 144, 162, 192, 216, 243, 256, 324, 432]),
  (486, 512, [108, 144, 162, 192, 216, 243, 256, 288, 384, 486]),
  (512, 648, [108, 144, 162, 192, 216, 243, 256, 288, 384, 486, 512]),
  (648, 729, [144, 192, 216, 243, 256, 288, 324, 384, 486, 512, 648]),
  (729, 768, [162, 216, 243, 256, 288, 324, 384, 432, 512, 576, 729]),
  (768, 864, [162, 216, 243, 288, 324, 384, 432, 512, 576, 729, 768]),
  (864, 972, [192, 256, 288, 324, 384, 432, 486, 512, 648, 729, 864]),
  (972, 1024, [216, 288, 324, 384, 432, 486, 512, 576, 729, 768, 972]),
  (1024, 1296, [216, 288, 324, 384, 432, 486, 512, 576, 729, 768, 972, 1024]),
  (1296, 1458, [288, 384, 432, 486, 512, 576, 648, 729, 768, 972, 1024, 1296]),
  (1458, 1536, [324, 432, 486, 512, 576, 648, 729, 768, 864, 1024, 1152, 1458]),
  (1536, 1728, [324, 432, 486, 576, 648, 729, 768, 864, 1024, 1152, 1458, 1536]),
  (1728, 1944, [384, 512, 576, 648, 729, 768, 864, 972, 1024, 1296, 1458, 1728]),
  (1944, 2001, [432, 576, 648, 729, 768, 864, 972, 1024, 1152, 1458, 1536, 1944])
]

private def tbl1 : List (ℕ × ℕ × List ℕ) := [
  (1, 2, [1]),
  (2, 3, [1, 2]),
  (3, 4, [2, 3]),
  (4, 7, [2, 3, 4]),
  (7, 8, [3, 4, 6]),
  (8, 9, [3, 4, 6, 8]),
  (9, 13, [4, 6, 8, 9]),
  (13, 16, [6, 8, 9, 12]),
  (16, 22, [6, 8, 9, 12, 16]),
  (22, 26, [8, 9, 12, 16, 18]),
  (26, 27, [9, 12, 16, 18, 24]),
  (27, 32, [6, 8, 9, 12, 16, 27]),
  (32, 44, [12, 16, 18, 24, 27, 32]),
  (44, 49, [16, 18, 24, 27, 32, 36]),
  (49, 64, [18, 24, 27, 32, 36, 48]),
  (64, 65, [18, 24, 27, 32, 36, 48, 64]),
  (65, 81, [24, 27, 32, 36, 48, 54, 64]),
  (81, 126, [18, 24, 27, 32, 36, 48, 64, 81]),
  (126, 128, [36, 48, 54, 64, 72, 81, 96]),
  (128, 130, [36, 48, 54, 64, 72, 81, 96, 128]),
  (130, 146, [48, 54, 64, 72, 81, 96, 108, 128]),
  (146, 173, [54, 64, 72, 81, 96, 108, 128, 144]),
  (173, 243, [36, 48, 54, 64, 72, 81, 96, 128, 162]),
  (243, 256, [54, 72, 81, 96, 108, 128, 144, 192, 243]),
  (256, 346, [54, 72, 81, 96, 108, 128, 144, 192, 243, 256]),
  (346, 432, [72, 96, 108, 128, 144, 162, 192, 243, 256, 324]),
  (432, 486, [96, 128, 144, 162, 192, 216, 243, 256, 324, 432]),
  (486, 512, [108, 144, 162, 192, 216, 243, 256, 288, 384, 486]),
  (512, 648, [108, 144, 162, 192, 216, 243, 256, 288, 384, 486, 512]),
  (648, 729, [144, 192, 216, 243, 256, 288, 324, 384, 486, 512, 648]),
  (729, 768, [162, 216, 243, 256, 288, 324, 384, 432, 512, 576, 729]),
  (768, 864, [162, 216, 243, 288, 324, 384, 432, 512, 576, 729, 768]),
  (864, 972, [192, 256, 288, 324, 384, 432, 486, 512, 648, 729, 864]),
  (972, 1024, [216, 288, 324, 384, 432, 486, 512, 576, 729, 768, 972]),
  (1024, 1296, [216, 288, 324, 384, 432, 486, 512, 576, 729, 768, 972, 1024]),
  (1296, 1458, [288, 384, 432, 486, 512, 576, 648, 729, 768, 972, 1024, 1296]),
  (1458, 1536, [324, 432, 486, 512, 576, 648, 729, 768, 864, 1024, 1152, 1458]),
  (1536, 1728, [324, 432, 486, 576, 648, 729, 768, 864, 1024, 1152, 1458, 1536]),
  (1728, 1944, [384, 512, 576, 648, 729, 768, 864, 972, 1024, 1296, 1458, 1728]),
  (1944, 2001, [432, 576, 648, 729, 768, 864, 972, 1024, 1152, 1458, 1536, 1944])
]

private def tbl2 : List (ℕ × ℕ × List ℕ) := [
  (1, 2, [1]),
  (2, 3, [1, 2]),
  (3, 4, [2, 3]),
  (4, 8, [2, 3, 4]),
  (8, 9, [3, 4, 6, 8]),
  (9, 12, [4, 6, 8, 9]),
  (12, 16, [6, 8, 9, 12]),
  (16, 27, [6, 8, 9, 12, 16]),
  (27, 30, [6, 8, 9, 12, 16, 27]),
  (30, 32, [12, 16, 18, 24, 27]),
  (32, 54, [12, 16, 18, 24, 27, 32]),
  (54, 64, [18, 24, 27, 32, 36, 48]),
  (64, 72, [18, 24, 27, 32, 36, 48, 64]),
  (72, 81, [24, 27, 32, 36, 48, 54, 64]),
  (81, 90, [18, 24, 27, 32, 36, 48, 64, 81]),
  (90, 108, [32, 36, 48, 54, 64, 72, 81]),
  (108, 128, [36, 48, 54, 64, 72, 81, 96]),
  (128, 135, [36, 48, 54, 64, 72, 81, 96, 128]),
  (135, 160, [48, 54, 64, 72, 81, 96, 108, 128]),
  (160, 180, [54, 64, 72, 81, 96, 108, 128, 144]),
  (180, 216, [64, 72, 81, 96, 108, 128, 144, 162]),
  (216, 243, [72, 81, 96, 108, 128, 144, 162, 192]),
  (243, 256, [54, 72, 81, 96, 108, 128, 144, 192, 243]),
  (256, 270, [54, 72, 81, 96, 108, 128, 144, 192, 243, 256]),
  (270, 320, [96, 108, 128, 144, 162, 192, 216, 243, 256]),
  (320, 360, [108, 128, 144, 162, 192, 216, 243, 256, 288]),
  (360, 405, [128, 144, 162, 192, 216, 243, 256, 288, 324]),
  (405, 432, [144, 162, 192, 216, 243, 256, 288, 324, 384]),
  (432, 480, [96, 128, 144, 162, 192, 216, 243, 256, 324, 432]),
  (480, 486, [162, 192, 216, 243, 256, 288, 324, 384, 432]),
  (486, 512, [108, 144, 162, 192, 216, 243, 256, 288, 384, 486]),
  (512, 540, [108, 144, 162, 192, 216, 243, 256, 288, 384, 486, 512]),
  (540, 576, [192, 216, 243, 256, 288, 324, 384, 432, 486, 512]),
  (576, 648, [216, 243, 256, 288, 324, 384, 432, 486, 512, 576]),
  (648, 720, [144, 192, 216, 243, 256, 288, 324, 384, 486, 512, 648]),
  (720, 729, [243, 256, 288, 324, 384, 432, 486, 512, 576, 648]),
  (729, 768, [162, 216, 243, 256, 288, 324, 384, 432, 512, 576, 729]),
  (768, 810, [162, 216, 243, 288, 324, 384, 432, 512, 576, 729, 768]),
  (810, 864, [288, 324, 384, 432, 486, 512, 576, 648, 729, 768]),
  (864, 960, [192, 256, 288, 324, 384, 432, 486, 512, 648, 729, 864]),
  (960, 972, [324, 384, 432, 486, 512, 576, 648, 729, 768, 864]),
  (972, 1024, [216, 288, 324, 384, 432, 486, 512, 576, 729, 768, 972]),
  (1024, 1080, [216, 288, 324, 384, 432, 486, 512, 576, 729, 768, 972, 1024]),
  (1080, 1152, [384, 432, 486, 512, 576, 648, 729, 768, 864, 972, 1024]),
  (1152, 1296, [432, 486, 512, 576, 648, 729, 768, 864, 972, 1024, 1152]),
  (1296, 1440, [288, 384, 432, 486, 512, 576, 648, 729, 768, 972, 1024, 1296]),
  (1440, 1458, [486, 512, 576, 648, 729, 768, 864, 972, 1024, 1152, 1296]),
  (1458, 1536, [324, 432, 486, 512, 576, 648, 729, 768, 864, 1024, 1152, 1458]),
  (1536, 1620, [324, 432, 486, 576, 648, 729, 768, 864, 1024, 1152, 1458, 1536]),
  (1620, 1728, [576, 648, 729, 768, 864, 972, 1024, 1152, 1296, 1458, 1536]),
  (1728, 1920, [384, 512, 576, 648, 729, 768, 864, 972, 1024, 1296, 1458, 1728]),
  (1920, 1944, [648, 729, 768, 864, 972, 1024, 1152, 1296, 1458, 1536, 1728]),
  (1944, 2001, [432, 576, 648, 729, 768, 864, 972, 1024, 1152, 1458, 1536, 1944])
]

private def smoothList2000 : List ℕ :=
  [1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36, 48, 54, 64, 72, 81, 96, 108,
   128, 144, 162, 192, 216, 243, 256, 288, 324, 384, 432, 486, 512, 576, 648,
   729, 768, 864, 972, 1024, 1152, 1296, 1458, 1536, 1728, 1944]

private def pTier0 (m : ℕ) : Bool := p6 m && (m % 5 != 0)
private def pTier1 (m : ℕ) : Bool := p6 m && (m % 5 == 0) && (m % 25 != 0)
private def pTier2 (m : ℕ) : Bool := p6 m && (m % 25 == 0)

private lemma pTier0_periodic (x : ℕ) : pTier0 (x + 30) = pTier0 x := by
  unfold pTier0 p6
  have h2 : (x + 30) % 2 = x % 2 := by omega
  have h3 : (x + 30) % 3 = x % 3 := by omega
  have h5 : (x + 30) % 5 = x % 5 := by omega
  rw [h2, h3, h5]

private lemma pTier1_periodic (x : ℕ) : pTier1 (x + 150) = pTier1 x := by
  unfold pTier1 p6
  have h2 : (x + 150) % 2 = x % 2 := by omega
  have h3 : (x + 150) % 3 = x % 3 := by omega
  have h5 : (x + 150) % 5 = x % 5 := by omega
  have h25 : (x + 150) % 25 = x % 25 := by omega
  rw [h2, h3, h5, h25]

private lemma pTier2_periodic (x : ℕ) : pTier2 (x + 150) = pTier2 x := by
  unfold pTier2 p6
  have h2 : (x + 150) % 2 = x % 2 := by omega
  have h3 : (x + 150) % 3 = x % 3 := by omega
  have h25 : (x + 150) % 25 = x % 25 := by omega
  rw [h2, h3, h25]

private lemma cntPeriod_pTier0 : cntPeriod pTier0 30 = 8 := by decide
private lemma cntPeriod_pTier1 : cntPeriod pTier1 150 = 8 := by decide
private lemma cntPeriod_pTier2 : cntPeriod pTier2 150 = 2 := by decide

private def isStrictlySorted : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && isStrictlySorted (b :: rest)

private def tblContig (cur : ℕ) : List (ℕ × ℕ × List ℕ) → Bool
  | [] => cur == 2001
  | (lo, hi, _) :: rest => (lo == cur) && (lo < hi) && tblContig hi rest

private def listForkFree (L : List ℕ) : Bool :=
  L.all fun s => (L.filter fun t => (s < t) && (t % s == 0)).length ≤ 1

private def hasStrictMult (L : List ℕ) (s : ℕ) : Bool :=
  L.any fun t => (s < t) && (t % s == 0)

private def tblValid (multB : ℕ) (tbl : List (ℕ × ℕ × List ℕ)) : Bool :=
  tblContig 1 tbl &&
  tbl.all fun (lo, hi, L) =>
    isStrictlySorted L &&
    listForkFree L &&
    L.all fun s => (1 ≤ s) && (s ≤ lo) && isSmooth3Fast s && (hi ≤ multB * s)

private def crossOk (ta tb : List (ℕ × ℕ × List ℕ)) : Bool :=
  ta.all fun (lo0, hi0, L0) =>
    tb.all fun (lo1, hi1, L1) =>
      if (5 * lo1 < hi0) && (lo0 < 5 * hi1) then
        L0.all fun s => !(hasStrictMult L0 s) || !(L1.contains s)
      else true

private lemma tbl0_valid : tblValid 7 tbl0 = true := by decide
private lemma tbl1_valid : tblValid 7 tbl1 = true := by decide
private lemma tbl2_valid : tblValid 5 tbl2 = true := by decide
private lemma cross_01_ok : crossOk tbl0 tbl1 = true := by decide
private lemma cross_12_ok : crossOk tbl1 tbl2 = true := by decide

private lemma smoothList2000_sorted : isStrictlySorted smoothList2000 = true := by decide

private lemma smoothList2000_all_smooth :
    smoothList2000.all (fun s => (1 ≤ s) && (s ≤ 2000) && isSmooth3Fast s) = true := by decide

private lemma smoothList2000_complete :
    (List.range 11).all (fun a =>
      (List.range 7).all (fun b =>
        (2000 < 2 ^ a * 3 ^ b) || smoothList2000.contains (2 ^ a * 3 ^ b))) = true := by decide

private lemma mem_smoothList2000_iff {s : ℕ} (hs2000 : s ≤ 2000) :
    s ∈ smoothList2000 ↔ isSmooth3 s = true := by
  constructor
  · intro hs
    have h := List.all_eq_true.mp smoothList2000_all_smooth s hs
    simp only [Bool.and_eq_true] at h
    exact isSmooth3_of_fast h.2
  · intro hsm
    obtain ⟨a, b, rfl⟩ := (isSmooth3_iff s).mp hsm
    have ha : a < 11 := by
      by_contra hge
      have h1 : 2 ^ 11 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ a ≤ 2 ^ a * 3 ^ b := Nat.le_mul_of_pos_right _ (by positivity)
      omega
    have hb : b < 7 := by
      by_contra hge
      have h1 : 3 ^ 7 ≤ 3 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 3 ^ b ≤ 2 ^ a * 3 ^ b := Nat.le_mul_of_pos_left _ (by positivity)
      omega
    have h := List.all_eq_true.mp (List.all_eq_true.mp smoothList2000_complete a (List.mem_range.mpr ha)) b (List.mem_range.mpr hb)
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_eq_mem] at h
    rcases h with hgt | hmem
    · omega
    · exact hmem

private lemma isStrictlySorted_head_lt {a : ℕ} {l : List ℕ}
    (h : isStrictlySorted (a :: l) = true) : ∀ c ∈ l, a < c := by
  induction l generalizing a with
  | nil => intro c hc; simp at hc
  | cons b rest ih =>
    intro c hc
    simp only [isStrictlySorted, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc'
    · exact h.1
    · exact lt_trans h.1 (ih h.2 c hc')

private lemma isStrictlySorted_nodup {L : List ℕ} (h : isStrictlySorted L = true) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    cases rest with
    | nil => exact List.nodup_singleton a
    | cons b rest' =>
      have hlt := isStrictlySorted_head_lt h
      simp only [isStrictlySorted, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [List.nodup_cons]
      exact ⟨fun ha => lt_irrefl a (hlt a ha), ih h.2⟩

private def lookupTbl (tbl : List (ℕ × ℕ × List ℕ)) (K : ℕ) : List ℕ :=
  match tbl with
  | [] => []
  | (lo, hi, L) :: rest => if lo ≤ K && K < hi then L else lookupTbl rest K

private lemma tblContig_unique {cur : ℕ} {tbl : List (ℕ × ℕ × List ℕ)}
    (hc : tblContig cur tbl = true) :
    (∀ e ∈ tbl, cur ≤ e.1 ∧ e.1 < e.2.1 ∧ e.2.1 ≤ 2001) ∧
    (∀ K, cur ≤ K → K < 2001 → ∃ e ∈ tbl, e.1 ≤ K ∧ K < e.2.1 ∧ lookupTbl tbl K = e.2.2) ∧
    (∀ e ∈ tbl, ∀ K, e.1 ≤ K → K < e.2.1 → lookupTbl tbl K = e.2.2) := by
  induction tbl generalizing cur with
  | nil =>
    simp only [tblContig, beq_iff_eq] at hc
    refine ⟨by simp, fun K h1 h2 => by omega, by simp⟩
  | cons e rest ih =>
    rcases e with ⟨lo, hi, L⟩
    simp only [tblContig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨rfl, hlh⟩, hrest⟩ := hc
    obtain ⟨hbnd, hex, huniq⟩ := ih hrest
    refine ⟨?_, ?_, ?_⟩
    · intro e' he'
      simp only [List.mem_cons] at he'
      rcases he' with rfl | hmem
      · have hhi : hi ≤ 2001 := by
          cases rest with
          | nil => simp only [tblContig, beq_iff_eq] at hrest; omega
          | cons e2 r2 =>
            have h2 := hbnd e2 (List.mem_cons_self ..); omega
        exact ⟨le_rfl, hlh, hhi⟩
      · have h2 := hbnd e' hmem; exact ⟨by omega, h2.2.1, h2.2.2⟩
    · intro K hK1 hK2
      by_cases hK : K < hi
      · refine ⟨(lo, hi, L), List.mem_cons_self .., hK1, hK, ?_⟩
        simp [lookupTbl, hK1, hK]
      · obtain ⟨e', he', h1, h2, hlu⟩ := hex K (by omega) hK2
        refine ⟨e', List.mem_cons_of_mem _ he', h1, h2, ?_⟩
        simp only [lookupTbl, Bool.and_eq_true, decide_eq_true_eq]
        rw [if_neg (by omega)]; exact hlu
    · intro e' he' K hK1 hK2
      simp only [List.mem_cons] at he'
      rcases he' with rfl | hmem
      · simp [lookupTbl, hK1, hK2]
      · have h2 := hbnd e' hmem
        simp only [lookupTbl, Bool.and_eq_true, decide_eq_true_eq]
        rw [if_neg (by omega)]
        exact huniq e' hmem K hK1 hK2

private def lookupTier (m K : ℕ) : List ℕ :=
  if m % 5 != 0 then lookupTbl tbl0 K
  else if m % 25 != 0 then lookupTbl tbl1 K
  else lookupTbl tbl2 K

private def inLowerSet (n x : ℕ) : Bool :=
  let m := oddPart23 x
  let s := x / m
  let K := n / m
  if 2001 ≤ K then n < 3 * x
  else (lookupTier m K).contains s

private def lowerSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun x => inLowerSet n x)

private lemma mem_lowerSet_iff {n x : ℕ} :
    x ∈ lowerSet n ↔ 1 ≤ x ∧ x ≤ n ∧ inLowerSet n x = true := by
  simp only [lowerSet, Finset.mem_filter, Finset.mem_Icc, and_assoc]

private lemma mem_lowerSet_seven_gt {n x : ℕ} (hx : x ∈ lowerSet n) : n < 7 * x := by
  rw [mem_lowerSet_iff] at hx
  obtain ⟨hx1, hxn, hin⟩ := hx
  unfold inLowerSet at hin
  dsimp only at hin
  set m := oddPart23 x
  set s := x / m
  set K := n / m
  have hmpos : 0 < m := oddPart23_pos hx1
  have hms : m * s = x := mul_smoothPart hx1
  by_cases hK : 2001 ≤ K
  · rw [if_pos hK, decide_eq_true_eq] at hin; omega
  · rw [if_neg hK] at hin
    have hK1 : 1 ≤ K := Nat.div_pos (le_trans (oddPart23_le x hx1) hxn) hmpos
    have hK2 : K < 2001 := by omega
    have h7s : ∀ multB tbl, tblValid multB tbl = true → multB ≤ 7 →
        (lookupTbl tbl K).contains s = true → n < 7 * x := by
      intro multB tbl hval hmb hmem
      simp only [tblValid, Bool.and_eq_true] at hval
      obtain ⟨_, hex, _⟩ := tblContig_unique hval.1
      obtain ⟨⟨lo, hi, L⟩, he, hle, hlt, hlu⟩ := hex K hK1 hK2
      rw [hlu, List.contains_eq_mem, decide_eq_true_eq] at hmem
      have hok := List.all_eq_true.mp hval.2 (lo, hi, L) he
      simp only [Bool.and_eq_true] at hok
      have hsok := List.all_eq_true.mp hok.2 s hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsok
      have h7s_ge : hi ≤ 7 * s := le_trans hsok.2 (Nat.mul_le_mul_right s hmb)
      have hK_lt : n / m < 7 * s := lt_of_lt_of_le hlt h7s_ge
      have hmul : n < 7 * s * m := (Nat.div_lt_iff_lt_mul hmpos).mp hK_lt
      nlinarith
    unfold lookupTier at hin
    split_ifs at hin
    · exact h7s 7 tbl0 tbl0_valid le_rfl hin
    · exact h7s 7 tbl1 tbl1_valid le_rfl hin
    · exact h7s 5 tbl2 tbl2_valid (by omega) hin

private lemma listForkFree_subsingleton {L : List ℕ} (hff : listForkFree L = true)
    {s : ℕ} (hs : s ∈ L) :
    ∀ t1 ∈ L, ∀ t2 ∈ L, s < t1 → s ∣ t1 → s < t2 → s ∣ t2 → t1 = t2 := by
  intro t1 ht1 t2 ht2 hlt1 hd1 hlt2 hd2
  have hlen := List.all_eq_true.mp hff s hs
  simp only [decide_eq_true_eq] at hlen
  let F := L.filter (fun t => (s < t) && (t % s == 0))
  have h1 : t1 ∈ F := by
    rw [List.mem_filter]; refine ⟨ht1, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨hlt1, Nat.mod_eq_zero_of_dvd hd1⟩
  have h2 : t2 ∈ F := by
    rw [List.mem_filter]; refine ⟨ht2, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨hlt2, Nat.mod_eq_zero_of_dvd hd2⟩
  cases hF : F with
  | nil => rw [hF] at h1; simp at h1
  | cons a rest =>
    cases rest with
    | nil =>
      rw [hF, List.mem_singleton] at h1 h2
      rw [h1, h2]
    | cons b r =>
      have hge2 : 2 ≤ F.length := by rw [hF]; simp
      have hle1 : F.length ≤ 1 := hlen
      omega

private lemma lowerSet_forkFree (n : ℕ) : Erdos1062.ForkFree (lowerSet n : Set ℕ) := by
  intro x hx
  rw [Finset.mem_coe] at hx
  have hx7 : n < 7 * x := mem_lowerSet_seven_gt hx
  have hx_raw := mem_lowerSet_iff.mp hx
  obtain ⟨hx1, hxn, hin_x⟩ := hx_raw
  unfold inLowerSet at hin_x
  dsimp only at hin_x
  set m := oddPart23 x
  set s := x / m
  set K := n / m
  have hmpos : 0 < m := oddPart23_pos hx1
  have hmp6 : p6 m = true := oddPart23_p6 hx1
  have hms : m * s = x := mul_smoothPart hx1
  have hssmooth : isSmooth3 s = true := smoothPart_isSmooth3 hx1
  by_cases hK : 2001 ≤ K
  · rw [if_pos hK, decide_eq_true_eq] at hin_x
    refine Set.subsingleton_of_forall_eq (2 * x) ?_
    intro y hy
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe] at hy
    obtain ⟨⟨hyA, hyne⟩, k, rfl⟩ := hy
    have hyIcc := mem_lowerSet_iff.mp hyA
    have hk_ge2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · exfalso; exact hyne (mul_one x)
      · omega
    have hk2 : k = 2 := by nlinarith
    rw [hk2]; ring
  · rw [if_neg hK] at hin_x
    have hK1 : 1 ≤ K := Nat.div_pos (le_trans (oddPart23_le x hx1) hxn) hmpos
    have hK2 : K < 2001 := by omega
    have hmult_k : ∀ y, y ∈ ({b | b ∈ (lowerSet n : Set ℕ) \ {x} ∧ x ∣ b} : Set ℕ) →
        ∃ k, y = k * x ∧ (k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) := by
      intro y hy
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe] at hy
      obtain ⟨⟨hyA, hyne⟩, k, rfl⟩ := hy
      have hyIcc := mem_lowerSet_iff.mp hyA
      have hk_ge2 : 2 ≤ k := by
        rcases k with _ | _ | k
        · omega
        · exfalso; exact hyne (mul_one x)
        · omega
      have hk_le6 : k ≤ 6 := by nlinarith
      refine ⟨k, mul_comm x k, by omega⟩
    have hsame_coset : ∀ k, (k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6) → k * x ∈ lowerSet n →
        k * s ∈ lookupTier m K := by
      intro k hk hyA
      have hksm : isSmooth3 k = true := by
        apply isSmooth3_of_fast; rcases hk with rfl | rfl | rfl | rfl <;> decide
      have hodd : oddPart23 (k * x) = m := by
        rw [← hms, show k * (m * s) = m * (k * s) by ring]
        exact oddPart23_mul_smooth hmp6 (isSmooth3_mul hksm hssmooth)
      have hdiv : (k * x) / m = k * s := by
        rw [← hms, show k * (m * s) = m * (k * s) by ring, Nat.mul_div_right _ hmpos]
      have h2 := (mem_lowerSet_iff.mp hyA).2.2
      unfold inLowerSet at h2; dsimp only at h2
      rw [hodd, hdiv, if_neg hK, List.contains_eq_mem, decide_eq_true_eq] at h2
      exact h2
    have hno_both : 5 * x ∈ lowerSet n →
        ∀ k, (k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6) → k * x ∉ lowerSet n := by
      intro h5A k hk hkA
      have hks_mem : k * s ∈ lookupTier m K := hsame_coset k hk hkA
      have hs_mem : s ∈ lookupTier m K := by
        rw [List.contains_eq_mem, decide_eq_true_eq] at hin_x; exact hin_x
      have hs_pos : 0 < s := isSmooth3_pos hssmooth
      have hks_gt : s < k * s := by rcases hk with rfl | rfl | rfl | rfl <;> omega
      have h5p6 : p6 (5 * m) = true := by
        simp only [p6, Bool.and_eq_true, bne_iff_ne] at hmp6 ⊢; omega
      have hodd5 : oddPart23 (5 * x) = 5 * m := by
        rw [← hms, show 5 * (m * s) = (5 * m) * s by ring]
        exact oddPart23_mul_smooth h5p6 hssmooth
      have hdiv5 : (5 * x) / (5 * m) = s := by
        rw [← hms, show 5 * (m * s) = (5 * m) * s by ring, Nat.mul_div_right _ (by omega)]
      have hK5_eq : n / (5 * m) = K / 5 := by
        rw [mul_comm 5 m, ← Nat.div_div_eq_div_mul]
      have h5raw := mem_lowerSet_iff.mp h5A
      have h5in := h5raw.2.2
      unfold inLowerSet at h5in; dsimp only at h5in
      rw [hodd5, hdiv5, hK5_eq] at h5in
      have hK5_lt : K / 5 < 2001 := by omega
      rw [if_neg (by omega : ¬ 2001 ≤ K / 5), List.contains_eq_mem, decide_eq_true_eq] at h5in
      have hK5_ge1 : 1 ≤ K / 5 := by
        have : 5 * m ≤ n := le_trans (Nat.le_mul_of_pos_right _ hs_pos) (by nlinarith)
        have := Nat.div_pos this (by omega : 0 < 5 * m)
        rwa [hK5_eq] at this
      have hcross_contra : ∀ ta tb, tblValid 7 ta = true → tblValid 7 tb = true →
          crossOk ta tb = true →
          s ∈ lookupTbl ta K → k * s ∈ lookupTbl ta K → s ∈ lookupTbl tb (K / 5) → False := by
        intro ta tb hva hvb hcr h1 h2 h3
        obtain ⟨_, hexa, _⟩ := tblContig_unique (Bool.and_eq_true _ _ |>.mp hva).1
        obtain ⟨_, hexb, _⟩ := tblContig_unique (Bool.and_eq_true _ _ |>.mp hvb).1
        obtain ⟨⟨lo0, hi0, L0⟩, he0, hlo0, hhi0, hlu0⟩ := hexa K hK1 hK2
        obtain ⟨⟨lo1, hi1, L1⟩, he1, hlo1, hhi1, hlu1⟩ := hexb (K / 5) hK5_ge1 hK5_lt
        dsimp only at hlo0 hhi0 hlo1 hhi1
        rw [hlu0] at h1 h2; rw [hlu1] at h3
        have hcr1 := List.all_eq_true.mp (List.all_eq_true.mp hcr (lo0, hi0, L0) he0) (lo1, hi1, L1) he1
        have hdiv5_bnd : 5 * (K / 5) ≤ K ∧ K < 5 * (K / 5) + 5 := by omega
        have hov : ((5 * lo1 < hi0) && (lo0 < 5 * hi1)) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
        dsimp only at hcr1
        rw [if_pos hov] at hcr1
        have hcr2 := List.all_eq_true.mp hcr1 s h1
        have hmult : hasStrictMult L0 s = true := by
          unfold hasStrictMult; rw [List.any_eq_true]
          exact ⟨k * s, h2, by simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; exact ⟨hks_gt, by simp⟩⟩
        have hcont : L1.contains s = true := by
          rw [List.contains_eq_mem, decide_eq_true_eq]; exact h3
        rw [hmult, hcont] at hcr2
        simp at hcr2
      by_cases hm5 : m % 5 ≠ 0
      · have ht0 : lookupTier m K = lookupTbl tbl0 K := by
          unfold lookupTier; simp [hm5]
        have ht1 : lookupTier (5 * m) (K / 5) = lookupTbl tbl1 (K / 5) := by
          unfold lookupTier
          have h5m5 : (5 * m) % 5 = 0 := by omega
          have h5m25 : (5 * m) % 25 ≠ 0 := by omega
          simp [h5m5, h5m25]
        rw [ht0] at hs_mem hks_mem; rw [ht1] at h5in
        exact hcross_contra tbl0 tbl1 tbl0_valid tbl1_valid cross_01_ok hs_mem hks_mem h5in
      · push Not at hm5
        by_cases hm25 : m % 25 ≠ 0
        · have ht1 : lookupTier m K = lookupTbl tbl1 K := by
            unfold lookupTier; simp [hm5, hm25]
          have ht2 : lookupTier (5 * m) (K / 5) = lookupTbl tbl2 (K / 5) := by
            unfold lookupTier
            have h5m5 : (5 * m) % 5 = 0 := by omega
            have h5m25 : (5 * m) % 25 = 0 := by omega
            simp [h5m5, h5m25]
          rw [ht1] at hs_mem hks_mem; rw [ht2] at h5in
          have hv2 : tblValid 7 tbl2 = true := by
            have h := tbl2_valid
            simp only [tblValid, Bool.and_eq_true] at h ⊢
            refine ⟨h.1, List.all_eq_true.mpr fun e he => ?_⟩
            have h1 := List.all_eq_true.mp h.2 e he
            simp only [Bool.and_eq_true] at h1 ⊢
            refine ⟨h1.1, List.all_eq_true.mpr fun t ht => ?_⟩
            have h2 := List.all_eq_true.mp h1.2 t ht
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
            exact ⟨h2.1, by omega⟩
          exact hcross_contra tbl1 tbl2 tbl1_valid hv2 cross_12_ok hs_mem hks_mem h5in
        · push Not at hm25
          have ht2 : lookupTier m K = lookupTbl tbl2 K := by
            unfold lookupTier; simp [hm5, hm25]
          rw [ht2] at hs_mem
          have hval := tbl2_valid
          simp only [tblValid, Bool.and_eq_true] at hval
          obtain ⟨_, hex2, _⟩ := tblContig_unique hval.1
          obtain ⟨⟨lo, hi, L⟩, he, hle, hlt, hlu⟩ := hex2 K hK1 hK2
          rw [hlu] at hs_mem
          have hok := List.all_eq_true.mp hval.2 (lo, hi, L) he
          simp only [Bool.and_eq_true] at hok
          have hsok := List.all_eq_true.mp hok.2 s hs_mem
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hsok
          have h5lt : n / m < 5 * s := lt_of_lt_of_le hlt hsok.2
          have hmul : n < 5 * s * m := (Nat.div_lt_iff_lt_mul hmpos).mp h5lt
          nlinarith
    intro y1 hy1 y2 hy2
    obtain ⟨k1, rfl, hk1⟩ := hmult_k y1 hy1
    obtain ⟨k2, rfl, hk2⟩ := hmult_k y2 hy2
    have hy1A : k1 * x ∈ lowerSet n := Finset.mem_coe.mp hy1.1.1
    have hy2A : k2 * x ∈ lowerSet n := Finset.mem_coe.mp hy2.1.1
    by_cases h15 : k1 = 5
    · subst h15
      by_cases h25 : k2 = 5
      · subst h25; rfl
      · have hk2' : k2 = 2 ∨ k2 = 3 ∨ k2 = 4 ∨ k2 = 6 := by omega
        exact False.elim (hno_both hy1A k2 hk2' hy2A)
    · by_cases h25 : k2 = 5
      · subst h25
        have hk1' : k1 = 2 ∨ k1 = 3 ∨ k1 = 4 ∨ k1 = 6 := by omega
        exact False.elim (hno_both hy2A k1 hk1' hy1A)
      · have hk1' : k1 = 2 ∨ k1 = 3 ∨ k1 = 4 ∨ k1 = 6 := by omega
        have hk2' : k2 = 2 ∨ k2 = 3 ∨ k2 = 4 ∨ k2 = 6 := by omega
        have h1 := hsame_coset k1 hk1' hy1A
        have h2 := hsame_coset k2 hk2' hy2A
        have hs_mem : s ∈ lookupTier m K := by
          rw [List.contains_eq_mem, decide_eq_true_eq] at hin_x; exact hin_x
        have hff : listForkFree (lookupTier m K) = true := by
          have hget : ∀ multB tbl, tblValid multB tbl = true → listForkFree (lookupTbl tbl K) = true := by
            intro multB tbl hv
            simp only [tblValid, Bool.and_eq_true] at hv
            obtain ⟨_, hex, _⟩ := tblContig_unique hv.1
            obtain ⟨⟨lo, hi, L⟩, he, _, _, hlu⟩ := hex K hK1 hK2
            rw [hlu]
            have hok := List.all_eq_true.mp hv.2 (lo, hi, L) he
            simp only [Bool.and_eq_true] at hok
            exact hok.1.2
          unfold lookupTier
          split_ifs
          · exact hget 7 tbl0 tbl0_valid
          · exact hget 7 tbl1 tbl1_valid
          · exact hget 5 tbl2 tbl2_valid
        have hs_pos : 0 < s := isSmooth3_pos hssmooth
        have hk1_gt : s < k1 * s := by rcases hk1' with rfl | rfl | rfl | rfl <;> omega
        have hk2_gt : s < k2 * s := by rcases hk2' with rfl | rfl | rfl | rfl <;> omega
        have heqs := listForkFree_subsingleton hff hs_mem (k1 * s) h1 (k2 * s) h2
          hk1_gt (dvd_mul_left s k1) hk2_gt (dvd_mul_left s k2)
        have hk12 : k1 = k2 := Nat.eq_of_mul_eq_mul_right hs_pos heqs
        rw [hk12]

private def lbTblFloor (num : ℕ) (tbl : List (ℕ × ℕ × List ℕ)) : ℕ :=
  tbl.foldl (fun acc e =>
    let lo := e.1; let hi := e.2.1; let c := e.2.2.length
    acc + (1000000000 * num * c * (hi - lo)) / (75 * lo * hi)) 0

private def lbUCeil : ℕ :=
  smoothList2000.foldl (fun acc s =>
    let d := min 2001 (3 * s)
    acc + (1000000000 * (d - s) + 3 * s * d - 1) / (3 * s * d)) 0

private lemma lb_scaled_ok :
    672550000 + lbUCeil ≤
      666666666 + lbTblFloor 20 tbl0 + lbTblFloor 4 tbl1 + lbTblFloor 1 tbl2 := by
  decide

private lemma lb_tbl_real_sum (num : ℕ) (tbl : List (ℕ × ℕ × List ℕ))
    (hok : ∀ e ∈ tbl, 1 ≤ e.1 ∧ e.1 < e.2.1) :
    ((lbTblFloor num tbl : ℕ) : ℝ) / 1000000000 ≤
      (tbl.map (fun e => ((num : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum := by
  have hfold : ∀ (l : List (ℕ × ℕ × List ℕ)) (init : ℕ),
      (∀ e ∈ l, 1 ≤ e.1 ∧ e.1 < e.2.1) →
      ((l.foldl (fun acc e =>
        acc + (1000000000 * num * e.2.2.length * (e.2.1 - e.1)) / (75 * e.1 * e.2.1)) init : ℕ) : ℝ) / 1000000000 ≤
        (l.map (fun e => ((num : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum +
          (init : ℝ) / 1000000000 := by
    intro l
    induction l with
    | nil => intro init _; simp
    | cons e l ih =>
      intro init hok'
      have he := hok' e (List.mem_cons_self ..)
      have hl : ∀ e' ∈ l, 1 ≤ e'.1 ∧ e'.1 < e'.2.1 := fun e' he' => hok' e' (List.mem_cons_of_mem _ he')
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      have hterm : (((1000000000 * num * e.2.2.length * (e.2.1 - e.1)) / (75 * e.1 * e.2.1) : ℕ) : ℝ) / 1000000000 ≤
          ((num : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1) := by
        have hden : 0 < 75 * e.1 * e.2.1 := by nlinarith
        have hf := nat_floor_div_real (a := 1000000000 * num * e.2.2.length * (e.2.1 - e.1))
          (b := 75 * e.1 * e.2.1) hden
        have h1 : (e.1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : e.1 ≠ 0)
        have h2 : (e.2.1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : e.2.1 ≠ 0)
        have hre : ((1000000000 * num * e.2.2.length * (e.2.1 - e.1) : ℕ) : ℝ) /
            (75 * e.1 * e.2.1 : ℕ) / 1000000000 =
            ((num : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1) := by
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (le_of_lt he.2)]
          push_cast
          field_simp
        rw [← hre]
        exact div_le_div_of_nonneg_right hf (by positivity)
      have hstep := ih (init + (1000000000 * num * e.2.2.length * (e.2.1 - e.1)) / (75 * e.1 * e.2.1)) hl
      push_cast at hstep
      linarith
  have h := hfold tbl 0 hok
  simp only [Nat.cast_zero, zero_div, add_zero] at h
  exact h

private lemma lb_U_real_sum :
    (smoothList2000.map (fun s => (1 : ℝ) / 3 * ((1 : ℝ) / s - 1 / (min 2001 (3 * s) : ℕ)))).sum ≤
      ((lbUCeil : ℕ) : ℝ) / 1000000000 := by
  have hfold : ∀ (l : List ℕ) (init : ℕ),
      (∀ s ∈ l, 1 ≤ s ∧ s ≤ 2000) →
      (l.map (fun s => (1 : ℝ) / 3 * ((1 : ℝ) / s - 1 / (min 2001 (3 * s) : ℕ)))).sum +
          (init : ℝ) / 1000000000 ≤
        ((l.foldl (fun acc s =>
          let d := min 2001 (3 * s)
          acc + (1000000000 * (d - s) + 3 * s * d - 1) / (3 * s * d)) init : ℕ) : ℝ) / 1000000000 := by
    intro l
    induction l with
    | nil => intro init _; simp
    | cons s l ih =>
      intro init hok'
      have hs := hok' s (List.mem_cons_self ..)
      have hl : ∀ s' ∈ l, 1 ≤ s' ∧ s' ≤ 2000 := fun s' hs' => hok' s' (List.mem_cons_of_mem _ hs')
      simp only [List.map_cons, List.sum_cons, List.foldl_cons]
      set d := min 2001 (3 * s)
      have hsd : s < d := by omega
      have hterm : (1 : ℝ) / 3 * ((1 : ℝ) / s - 1 / (d : ℕ)) ≤
          (((1000000000 * (d - s) + 3 * s * d - 1) / (3 * s * d) : ℕ) : ℝ) / 1000000000 := by
        have hden : 0 < 3 * s * d := by nlinarith
        have hc := nat_ceil_div_real (a := 1000000000 * (d - s)) (b := 3 * s * d) hden
        have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
        have hre : ((1000000000 * (d - s) : ℕ) : ℝ) / (3 * s * d : ℕ) / 1000000000 =
            (1 : ℝ) / 3 * ((1 : ℝ) / s - 1 / (d : ℕ)) := by
          rw [Nat.cast_mul, Nat.cast_sub (le_of_lt hsd)]
          push_cast
          field_simp
        rw [← hre]
        exact div_le_div_of_nonneg_right hc (by positivity)
      have hstep := ih (init + (1000000000 * (d - s) + 3 * s * d - 1) / (3 * s * d)) hl
      rw [Nat.cast_add] at hstep
      dsimp only [d] at hterm hstep ⊢
      linarith
  have hok : ∀ s ∈ smoothList2000, 1 ≤ s ∧ s ≤ 2000 := by
    intro s hs
    have h1 := List.all_eq_true.mp smoothList2000_all_smooth s hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1
  have h := hfold smoothList2000 0 hok
  simp only [Nat.cast_zero, zero_div, add_zero] at h
  exact h

private lemma card_tier_body (n : ℕ) (pT : ℕ → Bool) (tbl : List (ℕ × ℕ × List ℕ))
    (hvalid : ∃ multB, tblValid multB tbl = true)
    (hpT : ∀ m, pT m = true → p6 m = true)
    (hmatch : ∀ m K, pT m = true → 1 ≤ K → K < 2001 → lookupTier m K = lookupTbl tbl K) :
    ((lowerSet n).filter (fun x => n / oddPart23 x < 2001 ∧ pT (oddPart23 x) = true)).card =
      (tbl.map (fun e => e.2.2.length * ((Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => pT m)).card)).sum := by
  classical
  obtain ⟨multB, hval⟩ := hvalid
  simp only [tblValid, Bool.and_eq_true] at hval
  obtain ⟨hbnd, hex, huniq⟩ := tblContig_unique hval.1
  let F := (lowerSet n).filter (fun x => n / oddPart23 x < 2001 ∧ pT (oddPart23 x) = true)
  let piece (e : ℕ × ℕ × List ℕ) : Finset ℕ :=
    ((Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => pT m)).biUnion
      (fun m => e.2.2.toFinset.image (fun s => m * s))
  have hpiece_card : ∀ e ∈ tbl, (piece e).card =
      e.2.2.length * ((Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => pT m)).card := by
    intro e he
    have hok := List.all_eq_true.mp hval.2 e he
    simp only [Bool.and_eq_true] at hok
    have hnd : e.2.2.Nodup := isStrictlySorted_nodup hok.1.1
    rw [Finset.card_biUnion]
    · have hconst : ∀ m ∈ (Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => pT m),
          (e.2.2.toFinset.image (fun s => m * s)).card = e.2.2.length := by
        intro m hm
        have hmpos : 0 < m := p6_pos (hpT m (Finset.mem_filter.mp hm).2)
        rw [Finset.card_image_of_injective _ (fun s1 s2 h => Nat.eq_of_mul_eq_mul_left hmpos h),
          List.toFinset_card_of_nodup hnd]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
    · intro m1 hm1 m2 hm2 hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_image, List.mem_toFinset] at hx1 hx2
      obtain ⟨s1, hs1, rfl⟩ := hx1
      obtain ⟨s2, hs2, hEq⟩ := hx2
      have h1sm : isSmooth3 s1 = true := by
        have h := List.all_eq_true.mp hok.2 s1 hs1
        simp only [Bool.and_eq_true] at h; exact isSmooth3_of_fast h.1.2
      have h2sm : isSmooth3 s2 = true := by
        have h := List.all_eq_true.mp hok.2 s2 hs2
        simp only [Bool.and_eq_true] at h; exact isSmooth3_of_fast h.1.2
      have hm1p6 := hpT m1 (Finset.mem_filter.mp hm1).2
      have hm2p6 := hpT m2 (Finset.mem_filter.mp hm2).2
      have ho1 := oddPart23_mul_smooth hm1p6 h1sm
      have ho2 := oddPart23_mul_smooth hm2p6 h2sm
      rw [hEq] at ho2
      exact hne (ho1.symm.trans ho2)
  have hpiece_mem : ∀ e ∈ tbl, ∀ x, x ∈ piece e ↔
      x ∈ F ∧ e.1 ≤ n / oddPart23 x ∧ n / oddPart23 x < e.2.1 := by
    intro e he x
    have hok := List.all_eq_true.mp hval.2 e he
    simp only [Bool.and_eq_true] at hok
    have hebnd := hbnd e he
    constructor
    · intro hx
      simp only [piece, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
        List.mem_toFinset] at hx
      obtain ⟨m, ⟨⟨hm1, hm2⟩, hmpT⟩, s, hsL, rfl⟩ := hx
      have hsok := List.all_eq_true.mp hok.2 s hsL
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsok
      have hssm : isSmooth3 s = true := isSmooth3_of_fast hsok.1.2
      have hmp6 := hpT m hmpT
      have hmpos := p6_pos hmp6
      have hodd := oddPart23_mul_smooth hmp6 hssm
      have hdiv : (m * s) / m = s := Nat.mul_div_right s hmpos
      have hKle : e.1 ≤ n / m := by
        have hle1 : m * e.1 ≤ n := (Nat.le_div_iff_mul_le (by omega : 0 < e.1)).mp hm2
        exact (Nat.le_div_iff_mul_le hmpos).mpr (by linarith)
      have hKlt : n / m < e.2.1 := by
        have hlt0 : n / e.2.1 < m := by omega
        have hlt1 : n < m * e.2.1 := (Nat.div_lt_iff_lt_mul (by omega : 0 < e.2.1)).mp hlt0
        exact (Nat.div_lt_iff_lt_mul hmpos).mpr (by linarith)
      have hms_le : m * s ≤ n := by
        have h1 : e.1 * m ≤ n := (Nat.le_div_iff_mul_le hmpos).mp hKle
        have h2 : s * m ≤ e.1 * m := Nat.mul_le_mul_right m hsok.1.1.2
        nlinarith
      refine ⟨?_, by rw [hodd]; exact hKle, by rw [hodd]; exact hKlt⟩
      rw [Finset.mem_filter, mem_lowerSet_iff]
      refine ⟨⟨by nlinarith, hms_le, ?_⟩, by rw [hodd]; omega, by rw [hodd]; exact hmpT⟩
      unfold inLowerSet; dsimp only
      rw [hodd, hdiv, if_neg (by omega), hmatch m (n / m) hmpT (by omega) (by omega),
        huniq e he (n / m) hKle hKlt, List.contains_eq_mem, decide_eq_true_eq]
      exact hsL
    · rintro ⟨hxF, hKle, hKlt⟩
      rw [Finset.mem_filter, mem_lowerSet_iff] at hxF
      obtain ⟨⟨hx1, hxn, hin⟩, hK2001, hmpT⟩ := hxF
      unfold inLowerSet at hin; dsimp only at hin
      set m := oddPart23 x
      set s := x / m
      have hmpos := oddPart23_pos hx1
      rw [if_neg (by omega), hmatch m (n / m) hmpT (by omega) hK2001, huniq e he (n / m) hKle hKlt,
        List.contains_eq_mem, decide_eq_true_eq] at hin
      simp only [piece, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
        List.mem_toFinset]
      refine ⟨m, ⟨⟨?_, ?_⟩, hmpT⟩, s, hin, mul_smoothPart hx1⟩
      · have hlt1 : n < e.2.1 * m := (Nat.div_lt_iff_lt_mul hmpos).mp hKlt
        have hlt2 : n / e.2.1 < m := (Nat.div_lt_iff_lt_mul (by omega : 0 < e.2.1)).mpr (by linarith)
        omega
      · have hle1 : e.1 * m ≤ n := (Nat.le_div_iff_mul_le hmpos).mp hKle
        exact (Nat.le_div_iff_mul_le (by omega : 0 < e.1)).mpr (by linarith)
  have hsum : ∀ (l : List (ℕ × ℕ × List ℕ)) (cur : ℕ),
      tblContig cur l = true →
      (∀ e ∈ l, e ∈ tbl) →
      (F.filter (fun x => cur ≤ n / oddPart23 x)).card =
        (l.map (fun e => e.2.2.length * ((Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => pT m)).card)).sum := by
    intro l
    induction l with
    | nil =>
      intro cur hc _
      simp only [tblContig, beq_iff_eq] at hc
      have hemp : F.filter (fun x => cur ≤ n / oddPart23 x) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        dsimp only [F] at hx
        rw [Finset.mem_filter, Finset.mem_filter] at hx
        omega
      rw [hemp]; simp
    | cons e rest ih =>
      intro cur hc hsub
      rcases e with ⟨lo, hi, L⟩
      simp only [tblContig, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨rfl, hlh⟩, hrest⟩ := hc
      have he_tbl : (lo, hi, L) ∈ tbl := hsub (lo, hi, L) (List.mem_cons_self ..)
      have hrest_tbl : ∀ e' ∈ rest, e' ∈ tbl := fun e' he' => hsub e' (List.mem_cons_of_mem _ he')
      have hsplit : F.filter (fun x => lo ≤ n / oddPart23 x) =
          piece (lo, hi, L) ∪ F.filter (fun x => hi ≤ n / oddPart23 x) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, hpiece_mem (lo, hi, L) he_tbl]
        constructor
        · rintro ⟨hxF, hlo⟩
          rcases lt_or_ge (n / oddPart23 x) hi with hlt | hge
          · left; exact ⟨hxF, hlo, hlt⟩
          · right; exact ⟨hxF, hge⟩
        · rintro (⟨hxF, hlo, _⟩ | ⟨hxF, hhi⟩)
          · exact ⟨hxF, hlo⟩
          · exact ⟨hxF, by omega⟩
      have hdisj : Disjoint (piece (lo, hi, L)) (F.filter (fun x => hi ≤ n / oddPart23 x)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        rw [hpiece_mem (lo, hi, L) he_tbl] at hx1
        dsimp only at hx1
        rw [Finset.mem_filter] at hx2; omega
      rw [hsplit, Finset.card_union_of_disjoint hdisj, List.map_cons, List.sum_cons,
        hpiece_card (lo, hi, L) he_tbl, ih hi hrest hrest_tbl]
  have h1 : F.filter (fun x => 1 ≤ n / oddPart23 x) = F := by
    ext x; simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hx
    have hx' := (Finset.mem_filter.mp hx).1
    obtain ⟨hx1, hxn, _⟩ := mem_lowerSet_iff.mp hx'
    exact Nat.div_pos (le_trans (oddPart23_le x hx1) hxn) (oddPart23_pos hx1)
  change F.card = _
  rw [← h1]
  exact hsum tbl 1 hval.1 (fun _ h => h)

private lemma card_U_body (n : ℕ) :
    (((Finset.Icc 1 n).filter (fun x => n / oddPart23 x < 2001 ∧ n < 3 * x)).card) =
      (smoothList2000.map (fun s =>
        ((Finset.Icc (n / (min 2001 (3 * s)) + 1) (n / s)).filter (fun m => p6 m)).card)).sum := by
  classical
  let U := (Finset.Icc 1 n).filter (fun x => n / oddPart23 x < 2001 ∧ n < 3 * x)
  have hnd : smoothList2000.Nodup := isStrictlySorted_nodup smoothList2000_sorted
  let fiber (s : ℕ) : Finset ℕ :=
    ((Finset.Icc (n / (min 2001 (3 * s)) + 1) (n / s)).filter (fun m => p6 m)).image (fun m => m * s)
  have hU_eq : U = smoothList2000.toFinset.biUnion fiber := by
    ext x
    simp only [U, Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion, List.mem_toFinset,
      fiber, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx1, hxn⟩, hKlt, h3x⟩
      set m := oddPart23 x
      set s := x / m
      have hmpos := oddPart23_pos hx1
      have hmp6 := oddPart23_p6 hx1
      have hms := mul_smoothPart hx1
      have hsm := smoothPart_isSmooth3 hx1
      have hspos : 0 < s := isSmooth3_pos hsm
      have hsleK : s ≤ n / m := (Nat.le_div_iff_mul_le hmpos).mpr (by rw [mul_comm, hms]; exact hxn)
      have hs2000 : s ≤ 2000 := by omega
      have hs_in : s ∈ smoothList2000 := (mem_smoothList2000_iff hs2000).mpr hsm
      refine ⟨s, hs_in, m, ⟨⟨?_, ?_⟩, hmp6⟩, hms⟩
      · have hlt1 : n / 2001 < m := by
          have h1 : n < 2001 * m := (Nat.div_lt_iff_lt_mul hmpos).mp hKlt
          exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2001)).mpr (by linarith)
        have hlt2 : n / (3 * s) < m := by
          have h1 : n < m * (3 * s) := calc
            n < 3 * x := h3x
            _ = 3 * (m * s) := by rw [hms]
            _ = m * (3 * s) := by ring
          exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 3 * s)).mpr h1
        rcases min_cases 2001 (3 * s) with ⟨hmin, _⟩ | ⟨hmin, _⟩ <;> rw [hmin] <;> omega
      · exact (Nat.le_div_iff_mul_le hspos).mpr (by rw [hms]; exact hxn)
    · rintro ⟨s, hsL, m, ⟨⟨hm1, hm2⟩, hmp6⟩, rfl⟩
      have hsok := List.all_eq_true.mp smoothList2000_all_smooth s hsL
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsok
      have hsm : isSmooth3 s = true := isSmooth3_of_fast hsok.2
      have hspos := isSmooth3_pos hsm
      have hmpos := p6_pos hmp6
      have hodd := oddPart23_mul_smooth hmp6 hsm
      have hms_le : m * s ≤ n := (Nat.le_div_iff_mul_le hspos).mp hm2
      have hmgt : n / min 2001 (3 * s) < m := by omega
      have hmul_gt : n < m * min 2001 (3 * s) :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < min 2001 (3 * s))).mp hmgt
      refine ⟨⟨by nlinarith, hms_le⟩, ?_, ?_⟩
      · rw [hodd]
        have : n < 2001 * m := by nlinarith [min_le_left 2001 (3 * s)]
        exact (Nat.div_lt_iff_lt_mul hmpos).mpr this
      · nlinarith [min_le_right 2001 (3 * s)]
  change U.card = _
  rw [hU_eq, Finset.card_biUnion]
  · have hsum_list : ∀ s ∈ smoothList2000,
        (fiber s).card = ((Finset.Icc (n / (min 2001 (3 * s)) + 1) (n / s)).filter (fun m => p6 m)).card := by
      intro s hsL
      have hsok := List.all_eq_true.mp smoothList2000_all_smooth s hsL
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsok
      exact Finset.card_image_of_injective _ (fun m1 m2 h => Nat.eq_of_mul_eq_mul_right (by omega) h)
    rw [Finset.sum_congr rfl (fun s hs => hsum_list s (List.mem_toFinset.mp hs)),
      List.sum_toFinset _ hnd]
  · intro s1 hs1 s2 hs2 hne
    change Disjoint _ _
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [fiber, Finset.mem_image, Finset.mem_filter] at hx1 hx2
    obtain ⟨m1, ⟨_, hp1⟩, rfl⟩ := hx1
    obtain ⟨m2, ⟨_, hp2⟩, hEq⟩ := hx2
    have hsm : ∀ s ∈ smoothList2000, isSmooth3 s = true := by
      intro s hs
      have h := List.all_eq_true.mp smoothList2000_all_smooth s hs
      simp only [Bool.and_eq_true] at h
      exact isSmooth3_of_fast h.2
    have hs1m := hsm s1 (List.mem_toFinset.mp hs1)
    have hs2m := hsm s2 (List.mem_toFinset.mp hs2)
    have ho1 := oddPart23_mul_smooth hp1 hs1m
    have ho2 := oddPart23_mul_smooth hp2 hs2m
    rw [hEq] at ho2
    have hm12 : m1 = m2 := ho1.symm.trans ho2
    subst hm12
    exact hne (Nat.eq_of_mul_eq_mul_left (p6_pos hp1) hEq.symm)

private lemma lower_bound_eventually :
    ∀ᶠ n in atTop, (0.6725 : ℝ) * n ≤ (Erdos1062.f n : ℝ) := by
  rw [Filter.eventually_atTop]
  refine ⟨2000000000, fun n hn => ?_⟩
  classical
  have hle_f : (lowerSet n).card ≤ Erdos1062.f n := by
    have hcard_le_n : (lowerSet n).card ≤ n := by
      calc (lowerSet n).card ≤ (Finset.Icc 1 n).card := Finset.card_filter_le _ _
        _ = n := by simp
    refine Nat.le_findGreatest hcard_le_n ⟨(lowerSet n : Set ℕ), ?_, lowerSet_forkFree n, ?_⟩
    · intro x hx
      rw [Finset.mem_coe, mem_lowerSet_iff] at hx
      exact ⟨hx.1, hx.2.1⟩
    · exact Set.ncard_coe_finset (lowerSet n)
  let B0 := (Finset.Icc 1 n).filter (fun x => n < 3 * x)
  let Ubody := (Finset.Icc 1 n).filter (fun x => n / oddPart23 x < 2001 ∧ n < 3 * x)
  let Ltail := (lowerSet n).filter (fun x => 2001 ≤ n / oddPart23 x)
  let Lbody := (lowerSet n).filter (fun x => n / oddPart23 x < 2001)
  have hLtail_eq : Ltail = (Finset.Icc 1 n).filter (fun x => 2001 ≤ n / oddPart23 x ∧ n < 3 * x) := by
    ext x
    simp only [Ltail, Finset.mem_filter, Finset.mem_Icc, mem_lowerSet_iff]
    constructor
    · rintro ⟨⟨hx1, hxn, hin⟩, hK⟩
      unfold inLowerSet at hin; dsimp only at hin
      rw [if_pos hK, decide_eq_true_eq] at hin
      exact ⟨⟨hx1, hxn⟩, hK, hin⟩
    · rintro ⟨⟨hx1, hxn⟩, hK, h3⟩
      refine ⟨⟨hx1, hxn, ?_⟩, hK⟩
      unfold inLowerSet; dsimp only
      rw [if_pos hK, decide_eq_true_eq]; exact h3
  have hB0_split : B0.card = Ltail.card + Ubody.card := by
    rw [hLtail_eq]
    have h : B0 = (Finset.Icc 1 n).filter (fun x => 2001 ≤ n / oddPart23 x ∧ n < 3 * x) ∪ Ubody := by
      ext x
      simp only [B0, Ubody, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hx, h3⟩
        rcases le_or_gt 2001 (n / oddPart23 x) with hge | hlt
        · left; exact ⟨hx, hge, h3⟩
        · right; exact ⟨hx, hlt, h3⟩
      · rintro (⟨hx, _, h3⟩ | ⟨hx, _, h3⟩) <;> exact ⟨hx, h3⟩
    have hd : Disjoint ((Finset.Icc 1 n).filter (fun x => 2001 ≤ n / oddPart23 x ∧ n < 3 * x)) Ubody := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [Ubody, Finset.mem_filter] at h1 h2; omega
    rw [h, Finset.card_union_of_disjoint hd]
  have hB0_card : B0.card = n - n / 3 := by
    have h : B0 = Finset.Icc (n / 3 + 1) n := by
      ext x; simp only [B0, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [h, Nat.card_Icc]; omega
  have hL_split : (lowerSet n).card = Ltail.card + Lbody.card := by
    have hLb : Lbody = (lowerSet n).filter (fun x => ¬ 2001 ≤ n / oddPart23 x) := by
      ext x; simp only [Lbody, Finset.mem_filter, not_le]
    rw [hLb]
    exact (Finset.card_filter_add_card_filter_not (s := lowerSet n) (p := fun x => 2001 ≤ n / oddPart23 x)).symm
  let L0 := (lowerSet n).filter (fun x => n / oddPart23 x < 2001 ∧ pTier0 (oddPart23 x) = true)
  let L1 := (lowerSet n).filter (fun x => n / oddPart23 x < 2001 ∧ pTier1 (oddPart23 x) = true)
  let L2 := (lowerSet n).filter (fun x => n / oddPart23 x < 2001 ∧ pTier2 (oddPart23 x) = true)
  have hLbody_split : Lbody.card = L0.card + L1.card + L2.card := by
    have hun : Lbody = (L0 ∪ L1) ∪ L2 := by
      ext x; simp only [Lbody, L0, L1, L2, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hx, hK⟩
        have hx1 : 0 < x := (mem_lowerSet_iff.mp hx).1
        have hp6 := oddPart23_p6 hx1
        by_cases h5 : oddPart23 x % 5 ≠ 0
        · left; left; refine ⟨hx, hK, ?_⟩; simp [pTier0, hp6, h5]
        · push Not at h5
          by_cases h25 : oddPart23 x % 25 ≠ 0
          · left; right; refine ⟨hx, hK, ?_⟩; simp [pTier1, hp6, h5, h25]
          · push Not at h25
            right; refine ⟨hx, hK, ?_⟩; simp [pTier2, hp6, h25]
      · rintro ((⟨hx, hK, _⟩ | ⟨hx, hK, _⟩) | ⟨hx, hK, _⟩) <;> exact ⟨hx, hK⟩
    have hd01 : Disjoint L0 L1 := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [L0, L1, Finset.mem_filter, pTier0, pTier1, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h1 h2
      exact h1.2.2.2 h2.2.2.1.2
    have hd012 : Disjoint (L0 ∪ L1) L2 := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [L0, L1, L2, Finset.mem_union, Finset.mem_filter, pTier0, pTier1, pTier2,
        Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h1 h2
      rcases h1 with h0 | h1
      · exact h0.2.2.2 (by omega)
      · exact h1.2.2.2 h2.2.2.2
    rw [hun, Finset.card_union_of_disjoint hd012, Finset.card_union_of_disjoint hd01]
  have hL0 := card_tier_body n pTier0 tbl0 ⟨7, tbl0_valid⟩
    (fun m hm => (Bool.and_eq_true _ _ |>.mp hm).1)
    (fun m K hm _ _ => by
      simp only [pTier0, Bool.and_eq_true, bne_iff_ne] at hm
      unfold lookupTier; simp [hm.2])
  have hL1 := card_tier_body n pTier1 tbl1 ⟨7, tbl1_valid⟩
    (fun m hm => (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hm).1).1)
    (fun m K hm _ _ => by
      simp only [pTier1, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hm
      unfold lookupTier; simp [hm.1.2, hm.2])
  have hL2 := card_tier_body n pTier2 tbl2 ⟨5, tbl2_valid⟩
    (fun m hm => (Bool.and_eq_true _ _ |>.mp hm).1)
    (fun m K hm _ _ => by
      simp only [pTier2, Bool.and_eq_true, beq_iff_eq] at hm
      have h5 : m % 5 = 0 := by omega
      unfold lookupTier; simp [h5, hm.2])
  have hU := card_U_body n
  have htier_lb : ∀ (pT : ℕ → Bool) (M : ℕ) (hM : 0 < M) (hper : ∀ x, pT (x + M) = pT x)
      (tbl : List (ℕ × ℕ × List ℕ)) (hok : ∀ e ∈ tbl, 1 ≤ e.1 ∧ e.1 < e.2.1),
      (tbl.map (fun e => ((cntPeriod pT M : ℝ) / M) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum * n -
        (((tbl.map (fun e => (3 * cntPeriod pT M + 1) * e.2.2.length)).sum : ℕ) : ℝ) ≤
      (((tbl.map (fun e => e.2.2.length * ((Finset.Icc (n / e.2.1 + 1) (n / e.1)).filter (fun m => pT m)).card)).sum : ℕ) : ℝ) := by
    intro pT M hM hper tbl
    induction tbl with
    | nil => intro _; simp
    | cons e l ih =>
      intro hok
      have he := hok e (List.mem_cons_self ..)
      have hih := ih (fun e' he' => hok e' (List.mem_cons_of_mem _ he'))
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul]
      have hint := (cntP_interval_real_bounds pT M hM hper n e.1 e.2.1 (by omega) (le_of_lt he.2)).1
      have hmul := mul_le_mul_of_nonneg_left hint (Nat.cast_nonneg e.2.2.length)
      have hre : (e.2.2.length : ℝ) * (((cntPeriod pT M : ℝ) / M) * ((1 : ℝ) / e.1 - 1 / e.2.1) * n -
          (3 * (cntPeriod pT M : ℝ) + 1)) =
          ((cntPeriod pT M : ℝ) / M) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1) * n -
          ((3 * cntPeriod pT M + 1 : ℕ) : ℝ) * e.2.2.length := by
        push_cast; ring
      rw [hre] at hmul
      push_cast at hmul hih ⊢
      linarith
  have htbl_ok : ∀ multB tbl, tblValid multB tbl = true → ∀ e ∈ tbl, 1 ≤ e.1 ∧ e.1 < e.2.1 := by
    intro multB tbl hv e he
    have hb := (tblContig_unique (Bool.and_eq_true _ _ |>.mp hv).1).1 e he
    exact ⟨hb.1, hb.2.1⟩
  have h0lb := htier_lb pTier0 30 (by omega) pTier0_periodic tbl0 (htbl_ok 7 tbl0 tbl0_valid)
  have h1lb := htier_lb pTier1 150 (by omega) pTier1_periodic tbl1 (htbl_ok 7 tbl1 tbl1_valid)
  have h2lb := htier_lb pTier2 150 (by omega) pTier2_periodic tbl2 (htbl_ok 5 tbl2 tbl2_valid)
  rw [cntPeriod_pTier0] at h0lb
  rw [cntPeriod_pTier1] at h1lb
  rw [cntPeriod_pTier2] at h2lb
  have hU_ub :
      (((smoothList2000.map (fun s =>
        ((Finset.Icc (n / (min 2001 (3 * s)) + 1) (n / s)).filter (fun m => p6 m)).card)).sum : ℕ) : ℝ) ≤
      (smoothList2000.map (fun s => (1 : ℝ) / 3 * ((1 : ℝ) / s - 1 / (min 2001 (3 * s) : ℕ)))).sum * n + 1000 := by
    have hgen : ∀ l : List ℕ, (∀ s ∈ l, 1 ≤ s ∧ s ≤ 2000) →
        (((l.map (fun s =>
          ((Finset.Icc (n / (min 2001 (3 * s)) + 1) (n / s)).filter (fun m => p6 m)).card)).sum : ℕ) : ℝ) ≤
        (l.map (fun s => (1 : ℝ) / 3 * ((1 : ℝ) / s - 1 / (min 2001 (3 * s) : ℕ)))).sum * n + 7 * l.length := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons s l ih =>
        intro hok
        have hs := hok s (List.mem_cons_self ..)
        have hih := ih (fun s' hs' => hok s' (List.mem_cons_of_mem _ hs'))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        have hint := (cntP_interval_real_bounds p6 6 (by omega) p6_periodic n s (min 2001 (3 * s))
          (by omega) (by omega)).2
        rw [cntPeriod_p6] at hint
        have hre : ((2 : ℕ) : ℝ) / (6 : ℕ) * ((1 : ℝ) / s - 1 / (min 2001 (3 * s) : ℕ)) * n + (3 * ((2 : ℕ) : ℝ) + 1) =
            (1 : ℝ) / 3 * ((1 : ℝ) / s - 1 / (min 2001 (3 * s) : ℕ)) * n + 7 := by
          push_cast; ring
        rw [hre] at hint
        linarith
    have hok : ∀ s ∈ smoothList2000, 1 ≤ s ∧ s ≤ 2000 := by
      intro s hs
      have h1 := List.all_eq_true.mp smoothList2000_all_smooth s hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      exact h1.1
    have h1 := hgen smoothList2000 hok
    have hlen : (smoothList2000.length : ℝ) ≤ 100 := by
      have : smoothList2000.length ≤ 100 := by decide
      exact_mod_cast this
    linarith
  have herr0 : (((tbl0.map (fun e => (3 * 8 + 1) * e.2.2.length)).sum : ℕ) : ℝ) ≤ 20000 := by
    have : (tbl0.map (fun e => (3 * 8 + 1) * e.2.2.length)).sum ≤ 20000 := by decide
    exact_mod_cast this
  have herr1 : (((tbl1.map (fun e => (3 * 8 + 1) * e.2.2.length)).sum : ℕ) : ℝ) ≤ 20000 := by
    have : (tbl1.map (fun e => (3 * 8 + 1) * e.2.2.length)).sum ≤ 20000 := by decide
    exact_mod_cast this
  have herr2 : (((tbl2.map (fun e => (3 * 2 + 1) * e.2.2.length)).sum : ℕ) : ℝ) ≤ 20000 := by
    have : (tbl2.map (fun e => (3 * 2 + 1) * e.2.2.length)).sum ≤ 20000 := by decide
    exact_mod_cast this
  have heq0 : (tbl0.map (fun e => (((8 : ℕ) : ℝ) / (30 : ℕ)) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum =
      (tbl0.map (fun e => (((20 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum := by
    congr 1; apply List.map_congr_left; intro e _; push_cast; ring
  have heq1 : (tbl1.map (fun e => (((8 : ℕ) : ℝ) / (150 : ℕ)) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum =
      (tbl1.map (fun e => (((4 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum := by
    congr 1; apply List.map_congr_left; intro e _; push_cast; ring
  have heq2 : (tbl2.map (fun e => (((2 : ℕ) : ℝ) / (150 : ℕ)) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum =
      (tbl2.map (fun e => (((1 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum := by
    congr 1; apply List.map_congr_left; intro e _; push_cast; ring
  rw [heq0] at h0lb; rw [heq1] at h1lb; rw [heq2] at h2lb
  have hd0 := lb_tbl_real_sum 20 tbl0 (htbl_ok 7 tbl0 tbl0_valid)
  have hd1 := lb_tbl_real_sum 4 tbl1 (htbl_ok 7 tbl1 tbl1_valid)
  have hd2 := lb_tbl_real_sum 1 tbl2 (htbl_ok 5 tbl2 tbl2_valid)
  have hdU := lb_U_real_sum
  have hsc : (672550000 : ℝ) + lbUCeil ≤
      666666666 + lbTblFloor 20 tbl0 + lbTblFloor 4 tbl1 + lbTblFloor 1 tbl2 := by
    exact_mod_cast lb_scaled_ok
  have hdens : (0.67255 : ℝ) ≤
      (2 : ℝ) / 3 +
      (tbl0.map (fun e => (((20 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum +
      (tbl1.map (fun e => (((4 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum +
      (tbl2.map (fun e => (((1 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum -
      (smoothList2000.map (fun s => (1 : ℝ) / 3 * ((1 : ℝ) / s - 1 / (min 2001 (3 * s) : ℕ)))).sum := by
    linarith
  have hB0_lb : (2 : ℝ) / 3 * n ≤ (B0.card : ℝ) := by
    rw [hB0_card, Nat.cast_sub (Nat.div_le_self n 3)]
    have : ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := Nat.cast_div_le
    linarith
  have hcard_id : ((lowerSet n).card : ℝ) + (Ubody.card : ℝ) =
      (B0.card : ℝ) + (L0.card : ℝ) + (L1.card : ℝ) + (L2.card : ℝ) := by
    have : (lowerSet n).card + Ubody.card = B0.card + L0.card + L1.card + L2.card := by omega
    exact_mod_cast this
  have hle_fr : ((lowerSet n).card : ℝ) ≤ (Erdos1062.f n : ℝ) := by exact_mod_cast hle_f
  have hn_big : (2000000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul_dens := mul_le_mul_of_nonneg_right hdens (by positivity : (0 : ℝ) ≤ n)
  have hdist :
      ((2 : ℝ) / 3 +
        (tbl0.map (fun e => (((20 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum +
        (tbl1.map (fun e => (((4 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum +
        (tbl2.map (fun e => (((1 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum -
        (smoothList2000.map (fun s => (1 : ℝ) / 3 * ((1 : ℝ) / s - 1 / (min 2001 (3 * s) : ℕ)))).sum) * n =
      (2 : ℝ) / 3 * n +
        (tbl0.map (fun e => (((20 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum * n +
        (tbl1.map (fun e => (((4 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum * n +
        (tbl2.map (fun e => (((1 : ℕ) : ℝ) / 75) * e.2.2.length * ((1 : ℝ) / e.1 - 1 / e.2.1))).sum * n -
        (smoothList2000.map (fun s => (1 : ℝ) / 3 * ((1 : ℝ) / s - 1 / (min 2001 (3 * s) : ℕ)))).sum * n := by
    ring
  rw [hdist] at hmul_dens
  rw [hL0] at hcard_id; rw [hL1] at hcard_id; rw [hL2] at hcard_id; rw [hU] at hcard_id
  linarith

end Erdos1062Proof

theorem OMA.solution : type_of% @Erdos1062.erdos_1062.variants.lebensold_bounds := by
  exact Erdos1062Proof.lower_bound_eventually.and Erdos1062Proof.upper_bound_eventually
