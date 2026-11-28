import FormalConjectures.GreensOpenProblems.«93»

-- Reduction Green93.green_93.variants.bskk_large.R2 of Ben Green's Open Problem 93 — bskk large
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Proved here: polynomials with an integer root (a monic degree-1 factor) form a fraction
-- at most 5/sqrt n of the eligible ones, uniformly for M >= 34 and (log M)^3 <= n
-- (root r >= 0 impossible, r <= -2 by k-adic digit counting, r = -1 by an anti-concentration
-- bound for alternating sums). Remaining: monic factors of degree d >= 2, split at d^10 = n.

open Polynomial

namespace OMA.R_Green93_green_93_variants_bskk_large_R2


/-- Constant coefficient of `monicPoly a` for positive degree. -/
lemma monicPoly_coeff_zero {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℕ) :
    (Green93.monicPoly a).coeff 0 = (a ⟨0, hn⟩ : ℤ) := by
  unfold Green93.monicPoly
  rw [coeff_add, coeff_X_pow, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  have h0 : (0 : ℕ) ≠ n := by omega
  rw [if_neg h0, zero_add]
  rw [Finset.sum_eq_single ⟨0, hn⟩]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
    rw [if_neg (Ne.symm this)]
  · simp

/-- Coefficient of `monicPoly a` at any index `i < n`. -/
lemma monicPoly_coeff_lt {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    (Green93.monicPoly a).coeff (i : ℕ) = (a i : ℤ) := by
  unfold Green93.monicPoly
  rw [coeff_add, coeff_X_pow, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [if_neg i.isLt.ne, zero_add]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
    rw [if_neg this]
  · simp

/-- `monicPoly a` is monic of degree `n`. -/
lemma monicPoly_isMonicOfDegree {n : ℕ} (a : Fin n → ℕ) :
    IsMonicOfDegree (Green93.monicPoly a) n := by
  cases n with
  | zero => simp [Green93.monicPoly]
  | succ m =>
    unfold Green93.monicPoly
    apply (isMonicOfDegree_X_pow ℤ (m + 1)).add_right
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ ?_) (Nat.lt_succ_self m)
    intro i _
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ i.isLt)

lemma monicPoly_monic {n : ℕ} (a : Fin n → ℕ) : (Green93.monicPoly a).Monic :=
  (monicPoly_isMonicOfDegree a).monic

lemma monicPoly_natDegree {n : ℕ} (a : Fin n → ℕ) : (Green93.monicPoly a).natDegree = n :=
  (monicPoly_isMonicOfDegree a).natDegree_eq

/-- Evaluation formula for `monicPoly a`. -/
lemma monicPoly_eval {n : ℕ} (a : Fin n → ℕ) (r : ℤ) :
    (Green93.monicPoly a).eval r = r ^ n + ∑ j : Fin n, (a j : ℤ) * r ^ (j : ℕ) := by
  unfold Green93.monicPoly
  simp [eval_add, eval_pow, eval_finsetSum, eval_mul, eval_X]

/-- The conditioning set is nonempty. -/
lemma eligible_nonempty (M n : ℕ) (hM : 1 ≤ M) :
    (Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).Nonempty := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨default, ?_⟩
    simp [Green93.monicPoly]; exact Subsingleton.elim _ _
  · refine ⟨fun _ => ⟨1, by omega⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [monicPoly_coeff_zero hn]
    simp

/-- Exact cardinality of the eligible set for `n ≥ 1`. -/
lemma card_eligible (M n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card = M * (M + 1) ^ (n - 1) := by
  classical
  let s : Fin n → Finset (Fin (M + 1)) := fun i =>
    if i = ⟨0, hn⟩ then Finset.univ.erase (0 : Fin (M + 1)) else Finset.univ
  have hEq : (Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0) = Fintype.piFinset s := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, s]
    rw [monicPoly_coeff_zero hn]
    constructor
    · intro h i
      by_cases hi : i = ⟨0, hn⟩
      · subst hi
        simp only [↓reduceIte, Finset.mem_erase, Finset.mem_univ, and_true]
        intro h0
        apply h
        simp [h0]
      · simp [hi]
    · intro h
      have h0 := h ⟨0, hn⟩
      simp only [↓reduceIte, Finset.mem_erase, Finset.mem_univ, and_true] at h0
      intro hval
      apply h0
      have hvalN : (a ⟨0, hn⟩ : ℕ) = 0 := by exact_mod_cast hval
      exact Fin.ext hvalN
  rw [hEq, Fintype.card_piFinset]
  have hprod : (∏ i : Fin n, (s i).card) =
      (s ⟨0, hn⟩).card * ∏ i ∈ Finset.univ.erase ⟨0, hn⟩, (s i).card := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (s i).card) (Finset.mem_univ ⟨0, hn⟩)]
  rw [hprod]
  have h0 : (s ⟨0, hn⟩).card = M := by
    simp [s, Finset.card_erase_of_mem]
  have hrest : (∏ i ∈ Finset.univ.erase ⟨0, hn⟩, (s i).card) = (M + 1) ^ (n - 1) := by
    have hconst : ∀ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), (s i).card = M + 1 := by
      intro i hi
      have hne : i ≠ ⟨0, hn⟩ := (Finset.mem_erase.mp hi).1
      simp [s, hne]
    rw [Finset.prod_congr rfl hconst, Finset.prod_const]
    simp
  rw [h0, hrest]

/-- A reducible monic integer polynomial of positive degree has a monic divisor of degree in `[1, n/2]`. -/
lemma exists_monic_dvd_of_not_irreducible {f : ℤ[X]} (hm : f.Monic) (hn : 1 ≤ f.natDegree)
    (hred : ¬ Irreducible f) :
    ∃ g : ℤ[X], g.Monic ∧ g ∣ f ∧ 1 ≤ g.natDegree ∧ 2 * g.natDegree ≤ f.natDegree := by
  classical
  have hf1 : f ≠ 1 := by
    intro h
    simp [h] at hn
  rw [hm.irreducible_iff_lt_natDegree_lt hf1] at hred
  push Not at hred
  obtain ⟨g, -, hg, hdvd⟩ := hred
  rw [Finset.mem_Ioc] at hg
  have hlc : g.leadingCoeff ∣ (1 : ℤ) := by
    obtain ⟨q, hq⟩ := hdvd
    have hmul : (g * q).leadingCoeff = 1 := by rw [← hq, hm.leadingCoeff]
    rw [leadingCoeff_mul] at hmul
    exact ⟨q.leadingCoeff, hmul.symm⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hlc) with hpos | hneg
  · exact ⟨g, hpos, hdvd, Nat.succ_le_of_lt hg.1, by omega⟩
  · refine ⟨-g, ?_, neg_dvd.mpr hdvd, ?_, ?_⟩
    · rw [Monic, leadingCoeff_neg, hneg, neg_neg]
    · simpa [natDegree_neg] using Nat.succ_le_of_lt hg.1
    · simpa [natDegree_neg] using (by omega : 2 * g.natDegree ≤ f.natDegree)

/-- A monic degree-1 divisor yields an integer root. -/
lemma exists_int_root_of_monic_deg_one {f g : ℤ[X]} (hg : g.Monic) (hdeg : g.natDegree = 1)
    (hdvd : g ∣ f) : ∃ r : ℤ, f.eval r = 0 := by
  have hg_eq : g = X + C (g.coeff 0) := by
    ext k
    rcases k with _ | _ | k
    · simp
    · have h1 : g.coeff 1 = 1 := by
        rw [← hdeg]
        exact hg.leadingCoeff
      rw [coeff_add, coeff_X_one, coeff_C]
      simp [h1]
    · have hk : g.natDegree < k + 2 := by omega
      rw [coeff_eq_zero_of_natDegree_lt hk, coeff_add, coeff_X, coeff_C]
      simp
  refine ⟨-g.coeff 0, ?_⟩
  obtain ⟨q, rfl⟩ := hdvd
  rw [eval_mul, hg_eq]
  simp

/-- Eligible polynomials have no nonnegative integer roots. -/
lemma monicPoly_eval_pos_of_nonneg {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℕ)
    (ha0 : a ⟨0, hn⟩ ≠ 0) {r : ℤ} (hr : 0 ≤ r) :
    0 < (Green93.monicPoly a).eval r := by
  rw [monicPoly_eval]
  have hpow : 0 ≤ r ^ n := pow_nonneg hr n
  have hsum : (a ⟨0, hn⟩ : ℤ) ≤ ∑ j : Fin n, (a j : ℤ) * r ^ (j : ℕ) := by
    have hmem : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ≠ ⟨0, hn⟩ →
        0 ≤ (a j : ℤ) * r ^ (j : ℕ) := by
      intro j _ _
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _)
    have hle := Finset.single_le_sum (f := fun j : Fin n => (a j : ℤ) * r ^ (j : ℕ))
      (fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _)) hmem
    simpa using hle
  have ha0pos : (0 : ℤ) < (a ⟨0, hn⟩ : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero ha0
  linarith

/-- Any negative root `-k` of an eligible `monicPoly` divides `a 0`, hence `k ≤ M`. -/
lemma neg_root_le_M {M n k : ℕ} (hn : 1 ≤ n) (a : Fin n → Fin (M + 1))
    (ha0 : (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0)
    (heval : (Green93.monicPoly fun j ↦ (a j : ℕ)).eval (-(k : ℤ)) = 0) :
    k ≤ M := by
  rw [monicPoly_coeff_zero hn] at ha0
  have ha0pos : 0 < (a ⟨0, hn⟩ : ℕ) := by
    have : (a ⟨0, hn⟩ : ℕ) ≠ 0 := fun h => ha0 (by exact_mod_cast h)
    exact Nat.pos_of_ne_zero this
  have hdvdZ : (k : ℤ) ∣ ((a ⟨0, hn⟩ : ℕ) : ℤ) := by
    rw [monicPoly_eval] at heval
    have hsplit : ∑ j : Fin n, ((a j : ℕ) : ℤ) * (-(k : ℤ)) ^ (j : ℕ) =
        ((a ⟨0, hn⟩ : ℕ) : ℤ) +
          ∑ j ∈ Finset.univ.erase ⟨0, hn⟩, ((a j : ℕ) : ℤ) * (-(k : ℤ)) ^ (j : ℕ) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ⟨0, hn⟩)]
      simp
    have h1 : (k : ℤ) ∣ (-(k : ℤ)) ^ n := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ]
      exact dvd_mul_of_dvd_right (dvd_neg.mpr dvd_rfl) _
    have h2 : (k : ℤ) ∣ ∑ j ∈ Finset.univ.erase ⟨0, hn⟩,
        ((a j : ℕ) : ℤ) * (-(k : ℤ)) ^ (j : ℕ) := by
      apply Finset.dvd_sum
      intro j hj
      have hj0 : 0 < (j : ℕ) := by
        have hne : j ≠ ⟨0, hn⟩ := (Finset.mem_erase.mp hj).1
        have : (j : ℕ) ≠ 0 := fun h => hne (Fin.ext h)
        omega
      obtain ⟨m, hm⟩ : ∃ m, (j : ℕ) = m + 1 := ⟨(j : ℕ) - 1, by omega⟩
      rw [hm, pow_succ]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_neg.mpr dvd_rfl) _) _
    have hsum : ((a ⟨0, hn⟩ : ℕ) : ℤ) =
        -((-(k : ℤ)) ^ n + ∑ j ∈ Finset.univ.erase ⟨0, hn⟩,
          ((a j : ℕ) : ℤ) * (-(k : ℤ)) ^ (j : ℕ)) := by
      linarith
    rw [hsum]
    exact dvd_neg.mpr (dvd_add h1 h2)
  have hdvdN : k ∣ (a ⟨0, hn⟩ : ℕ) := Int.ofNat_dvd.mp hdvdZ
  have hle : k ≤ (a ⟨0, hn⟩ : ℕ) := Nat.le_of_dvd ha0pos hdvdN
  exact hle.trans (Nat.le_of_lt_succ (a ⟨0, hn⟩).isLt)

/-- At most `M / k + 1` elements of `Fin (M + 1)` lie in any single residue class mod `k`. -/
lemma card_mod_eq_le (M k r : ℕ) (_hk : 0 < k) :
    ((Finset.univ : Finset (Fin (M + 1))).filter fun x => x.val % k = r).card ≤ M / k + 1 := by
  let f : Fin (M + 1) → Fin (M / k + 1) := fun x =>
    ⟨x.val / k, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ x.isLt))⟩
  have hinj : Set.InjOn f ((Finset.univ : Finset (Fin (M + 1))).filter fun x => x.val % k = r) := by
    intro x hx y hy hxy
    have hxm : x.val % k = r := (Finset.mem_filter.mp hx).2
    have hym : y.val % k = r := (Finset.mem_filter.mp hy).2
    have hdiv : x.val / k = y.val / k := congrArg Fin.val hxy
    apply Fin.ext
    rw [← Nat.div_add_mod x.val k, ← Nat.div_add_mod y.val k, hdiv, hxm, hym]
  calc ((Finset.univ : Finset (Fin (M + 1))).filter fun x => x.val % k = r).card
      ≤ (Finset.univ : Finset (Fin (M / k + 1))).card :=
        Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
    _ = M / k + 1 := by simp

/-- Each prefix step adds at most `M / k + 1` valid extensions. -/
lemma card_prefixGood_le (M k m : ℕ) (hk : 0 < k) :
    ((Finset.univ.filter fun a : Fin m → Fin (M + 1) => ((k : ℤ) ^ m) ∣ ∑ i : Fin m, ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ))).card ≤ (M / k + 1) ^ m := by
  induction m with
  | zero =>
    calc ((Finset.univ.filter fun a : Fin 0 → Fin (M + 1) => ((k : ℤ) ^ 0) ∣ ∑ i : Fin 0, ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ))).card ≤ (Finset.univ : Finset (Fin 0 → Fin (M + 1))).card :=
          Finset.card_le_univ _
      _ = 1 := by simp
      _ = (M / k + 1) ^ 0 := by simp
  | succ m ih =>
    have hmap : ∀ a ∈ (Finset.univ.filter fun a : Fin (m + 1) → Fin (M + 1) => ((k : ℤ) ^ (m + 1)) ∣ ∑ i : Fin (m + 1), ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ)), Fin.init a ∈ (Finset.univ.filter fun a : Fin m → Fin (M + 1) => ((k : ℤ) ^ m) ∣ ∑ i : Fin m, ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ)) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [Fin.sum_univ_castSucc] at ha
      have h1 : (k : ℤ) ^ m ∣ (k : ℤ) ^ (m + 1) := pow_dvd_pow (k : ℤ) (Nat.le_succ m)
      have h2 : (k : ℤ) ^ m ∣ ((a (Fin.last m) : ℕ) : ℤ) * (-(k : ℤ)) ^ m := by
        rw [neg_pow]
        exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right dvd_rfl _) _
      have h3 : (k : ℤ) ^ m ∣ (∑ i : Fin m, ((a i.castSucc : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ)) +
          ((a (Fin.last m) : ℕ) : ℤ) * (-(k : ℤ)) ^ m := h1.trans ha
      have h4 := (dvd_add_left h2).mp h3
      simpa [Fin.init] using h4
    have hfiber : ∀ b ∈ (Finset.univ.filter fun a : Fin m → Fin (M + 1) => ((k : ℤ) ^ m) ∣ ∑ i : Fin m, ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ)),
        (((Finset.univ.filter fun a : Fin (m + 1) → Fin (M + 1) => ((k : ℤ) ^ (m + 1)) ∣ ∑ i : Fin (m + 1), ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ))).filter fun a => Fin.init a = b).card ≤ M / k + 1 := by
      intro b _
      set F := ((Finset.univ.filter fun a : Fin (m + 1) → Fin (M + 1) => ((k : ℤ) ^ (m + 1)) ∣ ∑ i : Fin (m + 1), ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ))).filter fun a => Fin.init a = b
      by_cases hne : F.Nonempty
      · obtain ⟨a₀, ha₀⟩ := hne
        have ha₀_mem : a₀ ∈ (Finset.univ.filter fun a : Fin (m + 1) → Fin (M + 1) => ((k : ℤ) ^ (m + 1)) ∣ ∑ i : Fin (m + 1), ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ)) := (Finset.mem_filter.mp ha₀).1
        have ha₀_init : Fin.init a₀ = b := (Finset.mem_filter.mp ha₀).2
        let r : ℕ := (a₀ (Fin.last m)).val % k
        let g : (Fin (m + 1) → Fin (M + 1)) → Fin (M + 1) := fun a => a (Fin.last m)
        have hmaps : ∀ a ∈ F, g a ∈ (Finset.univ : Finset (Fin (M + 1))).filter
            fun x => x.val % k = r := by
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have ha_mem : a ∈ (Finset.univ.filter fun a : Fin (m + 1) → Fin (M + 1) => ((k : ℤ) ^ (m + 1)) ∣ ∑ i : Fin (m + 1), ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ)) := (Finset.mem_filter.mp ha).1
          have ha_init : Fin.init a = b := (Finset.mem_filter.mp ha).2
          have hd1 : (k : ℤ) ^ (m + 1) ∣ ∑ i : Fin (m + 1),
              ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ) := (Finset.mem_filter.mp ha_mem).2
          have hd0 : (k : ℤ) ^ (m + 1) ∣ ∑ i : Fin (m + 1),
              ((a₀ i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ) := (Finset.mem_filter.mp ha₀_mem).2
          rw [Fin.sum_univ_castSucc] at hd1 hd0
          simp only [Fin.val_castSucc, Fin.val_last] at hd1 hd0
          have hsame : (∑ i : Fin m, ((a i.castSucc : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ)) =
              ∑ i : Fin m, ((a₀ i.castSucc : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ) := by
            apply Finset.sum_congr rfl
            intro i _
            have hi : a i.castSucc = a₀ i.castSucc := by
              change Fin.init a i = Fin.init a₀ i
              rw [ha_init, ha₀_init]
            rw [hi]
          have hsub := dvd_sub hd1 hd0
          rw [hsame] at hsub
          have hdiff : ((a (Fin.last m) : ℕ) : ℤ) * (-(k : ℤ)) ^ m -
              ((a₀ (Fin.last m) : ℕ) : ℤ) * (-(k : ℤ)) ^ m =
              (((a (Fin.last m) : ℕ) : ℤ) - ((a₀ (Fin.last m) : ℕ) : ℤ)) * (-(k : ℤ)) ^ m := by
            ring
          have hsub' : (k : ℤ) ^ (m + 1) ∣
              (((a (Fin.last m) : ℕ) : ℤ) - ((a₀ (Fin.last m) : ℕ) : ℤ)) * (-(k : ℤ)) ^ m := by
            simpa [add_sub_add_left_eq_sub, hdiff] using hsub
          rw [pow_succ, neg_pow] at hsub'
          have hsub'' : (k : ℤ) ^ m * (k : ℤ) ∣
              ((((-1 : ℤ) ^ m) * (((a (Fin.last m) : ℕ) : ℤ) - ((a₀ (Fin.last m) : ℕ) : ℤ))) *
                (k : ℤ) ^ m) := by
            convert hsub' using 1
            ring
          have hkm_ne : (k : ℤ) ^ m ≠ 0 := pow_ne_zero m (by exact_mod_cast hk.ne')
          rw [mul_comm ((k : ℤ) ^ m) (k : ℤ)] at hsub''
          have hkdvd : (k : ℤ) ∣
              ((-1 : ℤ) ^ m) * (((a (Fin.last m) : ℕ) : ℤ) - ((a₀ (Fin.last m) : ℕ) : ℤ)) :=
            (mul_dvd_mul_iff_right hkm_ne).mp hsub''
          have hkdvd' : (k : ℤ) ∣
              (((a (Fin.last m) : ℕ) : ℤ) - ((a₀ (Fin.last m) : ℕ) : ℤ)) := by
            have hu : IsUnit ((-1 : ℤ) ^ m) := isUnit_one.neg.pow m
            exact (hu.dvd_mul_left).mp hkdvd
          have hmodZ : (((a (Fin.last m) : ℕ) : ℤ) % (k : ℤ)) =
              (((a₀ (Fin.last m) : ℕ) : ℤ) % (k : ℤ)) :=
            Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hkdvd')
          exact_mod_cast hmodZ
        have hinj : Set.InjOn g F := by
          intro a₁ ha₁ a₂ ha₂ heq
          have hi1 : Fin.init a₁ = b := (Finset.mem_filter.mp ha₁).2
          have hi2 : Fin.init a₂ = b := (Finset.mem_filter.mp ha₂).2
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · exact heq
          · change Fin.init a₁ j = Fin.init a₂ j
            rw [hi1, hi2]
        exact (Finset.card_le_card_of_injOn g hmaps hinj).trans (card_mod_eq_le M k r hk)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp
    calc ((Finset.univ.filter fun a : Fin (m + 1) → Fin (M + 1) => ((k : ℤ) ^ (m + 1)) ∣ ∑ i : Fin (m + 1), ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ))).card
        = ∑ b ∈ (Finset.univ.filter fun a : Fin m → Fin (M + 1) => ((k : ℤ) ^ m) ∣ ∑ i : Fin m, ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ)), (((Finset.univ.filter fun a : Fin (m + 1) → Fin (M + 1) => ((k : ℤ) ^ (m + 1)) ∣ ∑ i : Fin (m + 1), ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ))).filter fun a => Fin.init a = b).card :=
          Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ _b ∈ (Finset.univ.filter fun a : Fin m → Fin (M + 1) => ((k : ℤ) ^ m) ∣ ∑ i : Fin m, ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ)), (M / k + 1) := Finset.sum_le_sum hfiber
      _ = ((Finset.univ.filter fun a : Fin m → Fin (M + 1) => ((k : ℤ) ^ m) ∣ ∑ i : Fin m, ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ))).card * (M / k + 1) := by simp
      _ ≤ (M / k + 1) ^ m * (M / k + 1) := Nat.mul_le_mul_right _ ih
      _ = (M / k + 1) ^ (m + 1) := by rw [pow_succ]

/-- Count of coefficient vectors with a fixed root `-k` (`k ≥ 2`). -/
lemma card_eval_neg_le (M n k : ℕ) (hk : 0 < k) :
    ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      (Green93.monicPoly fun j => (a j : ℕ)).eval (-(k : ℤ)) = 0).card ≤ (M / k + 1) ^ n := by
  refine (Finset.card_le_card ?_).trans (card_prefixGood_le M k n hk)
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  rw [monicPoly_eval] at ha
  have hsum : (∑ i : Fin n, ((a i : ℕ) : ℤ) * (-(k : ℤ)) ^ (i : ℕ)) = -(-(k : ℤ)) ^ n := by
    linarith
  rw [hsum, neg_pow]
  exact dvd_neg.mpr (dvd_mul_of_dvd_right dvd_rfl _)

/-- Elementary bound `1 / 3 ≤ log (5 / 3)` via `add_one_le_exp (-1/3)`. -/
lemma one_third_le_log_five_thirds : (1 / 3 : ℝ) ≤ Real.log (5 / 3 : ℝ) := by
  have h1 : (2 / 3 : ℝ) ≤ Real.exp (-1 / 3 : ℝ) := by
    have := Real.add_one_le_exp (-1 / 3 : ℝ)
    linarith
  have h2 : Real.exp (1 / 3 : ℝ) ≤ 3 / 2 := by
    have hpos : 0 < Real.exp (1 / 3 : ℝ) := Real.exp_pos _
    have hinv : Real.exp (-1 / 3 : ℝ) = (Real.exp (1 / 3 : ℝ))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [hinv] at h1
    rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 2 / 3) hpos] at h1
    linarith
  have h3 : Real.exp (1 / 3 : ℝ) ≤ 5 / 3 := by linarith
  exact (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 5 / 3)).mpr h3

open scoped Classical in
/-- Exponential bound for all negative integer roots `r ≤ -2`. -/
lemma card_roots_le_neg_two_bound {M n : ℕ} (hM : 34 ≤ M) (hn : 288 ≤ n)
    (hlog : (Real.log (M : ℝ)) ^ 3 ≤ n) :
    (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) =>
        ∃ r : ℤ, r ≤ -2 ∧ (Green93.monicPoly fun j => (a j : ℕ)).eval r = 0).card : ℝ) ≤
      (1 / (n : ℝ)) *
        ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
          (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ) := by
  classical
  set E := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
  have hn1 : 1 ≤ n := by omega
  have hsub : (E.filter fun a =>
      ∃ r : ℤ, r ≤ -2 ∧ (Green93.monicPoly fun j => (a j : ℕ)).eval r = 0) ⊆
      (Finset.Icc 2 M).biUnion fun k =>
        (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
          (Green93.monicPoly fun j => (a j : ℕ)).eval (-(k : ℤ)) = 0 := by
    intro a ha
    obtain ⟨haE, r, hr, heval⟩ := Finset.mem_filter.mp ha
    have ha0 : (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 := (Finset.mem_filter.mp haE).2
    let k : ℕ := (-r).toNat
    have hrk : r = -(k : ℤ) := by omega
    rw [hrk] at heval
    have hk2 : 2 ≤ k := by omega
    have hkM : k ≤ M := neg_root_le_M hn1 a ha0 heval
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk2, hkM⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, heval⟩⟩
  have hcardN : ((E.filter fun a =>
      ∃ r : ℤ, r ≤ -2 ∧ (Green93.monicPoly fun j => (a j : ℕ)).eval r = 0).card : ℝ) ≤
      (M : ℝ) * (((3 / 5 : ℝ) * (M + 1 : ℝ)) ^ n) := by
    have h1 : (E.filter fun a =>
        ∃ r : ℤ, r ≤ -2 ∧ (Green93.monicPoly fun j => (a j : ℕ)).eval r = 0).card ≤
        ∑ k ∈ Finset.Icc 2 M,
          ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
            (Green93.monicPoly fun j => (a j : ℕ)).eval (-(k : ℤ)) = 0).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : (∑ k ∈ Finset.Icc 2 M,
        (((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
          (Green93.monicPoly fun j => (a j : ℕ)).eval (-(k : ℤ)) = 0).card : ℝ)) ≤
        ∑ _k ∈ Finset.Icc 2 M, (((3 / 5 : ℝ) * (M + 1 : ℝ)) ^ n) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have h3 : ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
          (Green93.monicPoly fun j => (a j : ℕ)).eval (-(k : ℤ)) = 0).card ≤ (M / k + 1) ^ n :=
        card_eval_neg_le M n k (by omega)
      have hdiv : M / k + 1 ≤ M / 2 + 1 := Nat.add_le_add_right (Nat.div_le_div_left hk2 (by omega)) 1
      have h53 : 5 * (M / k + 1) ≤ 3 * (M + 1) := by omega
      have hreal : ((M / k + 1 : ℕ) : ℝ) ≤ (3 / 5 : ℝ) * (M + 1 : ℝ) := by
        have h53' : (5 : ℝ) * ((M / k + 1 : ℕ) : ℝ) ≤ (3 : ℝ) * ((M + 1 : ℕ) : ℝ) := by
          exact_mod_cast h53
        push_cast at h53' ⊢
        linarith
      calc (((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
              (Green93.monicPoly fun j => (a j : ℕ)).eval (-(k : ℤ)) = 0).card : ℝ)
          ≤ (((M / k + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast h3
        _ = ((M / k + 1 : ℕ) : ℝ) ^ n := Nat.cast_pow (M / k + 1) n
        _ ≤ ((3 / 5 : ℝ) * (M + 1 : ℝ)) ^ n :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hreal n
    have hcardIcc : ((Finset.Icc 2 M).card : ℝ) ≤ (M : ℝ) := by
      have : (Finset.Icc 2 M).card ≤ M := by simp
      exact_mod_cast this
    calc ((E.filter fun a =>
            ∃ r : ℤ, r ≤ -2 ∧ (Green93.monicPoly fun j => (a j : ℕ)).eval r = 0).card : ℝ)
        ≤ ∑ k ∈ Finset.Icc 2 M,
            (((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
              (Green93.monicPoly fun j => (a j : ℕ)).eval (-(k : ℤ)) = 0).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ ∑ _k ∈ Finset.Icc 2 M, (((3 / 5 : ℝ) * (M + 1 : ℝ)) ^ n) := h2
      _ = ((Finset.Icc 2 M).card : ℝ) * (((3 / 5 : ℝ) * (M + 1 : ℝ)) ^ n) := by simp
      _ ≤ (M : ℝ) * (((3 / 5 : ℝ) * (M + 1 : ℝ)) ^ n) :=
          mul_le_mul_of_nonneg_right hcardIcc (by positivity)
  have hEcard : (E.card : ℝ) = (M : ℝ) * (M + 1 : ℝ) ^ (n - 1) := by
    have := card_eligible M n hn1
    change E.card = M * (M + 1) ^ (n - 1) at this
    exact_mod_cast this
  have hfactor : (M : ℝ) * (((3 / 5 : ℝ) * (M + 1 : ℝ)) ^ n) =
      ((M + 1 : ℝ) * (3 / 5 : ℝ) ^ n) * (E.card : ℝ) := by
    rw [hEcard, mul_pow]
    have hpow : (M + 1 : ℝ) ^ n = (M + 1 : ℝ) * (M + 1 : ℝ) ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn1, pow_succ']
    rw [hpow]
    ring
  have hdecay : (M + 1 : ℝ) * (3 / 5 : ℝ) ^ n ≤ 1 / (n : ℝ) := by
    have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
    have hlog_nonneg : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
    have hnR : (288 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog_le : Real.log (M : ℝ) ≤ (n : ℝ) / 6 := by
      by_contra hgt
      push Not at hgt
      have hcube : ((n : ℝ) / 6) ^ 3 < (Real.log (M : ℝ)) ^ 3 :=
        pow_lt_pow_left₀ hgt (by positivity) (by norm_num)
      have hn2 : (216 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have hge : (n : ℝ) ≤ ((n : ℝ) / 6) ^ 3 := by nlinarith
      linarith
    have hM_le : (M : ℝ) ≤ Real.exp ((n : ℝ) / 6) := by
      rw [← Real.exp_log hMpos]
      exact Real.exp_le_exp.mpr hlog_le
    have hM1_le : (M + 1 : ℝ) ≤ 2 * Real.exp ((n : ℝ) / 6) := by
      have : (1 : ℝ) ≤ Real.exp ((n : ℝ) / 6) := Real.one_le_exp (by positivity)
      linarith
    have h35_le : (3 / 5 : ℝ) ^ n ≤ Real.exp (-(n : ℝ) / 3) := by
      have hbase : (3 / 5 : ℝ) ≤ Real.exp (-1 / 3 : ℝ) := by
        have hlt := one_third_le_log_five_thirds
        have hexp : Real.exp (1 / 3 : ℝ) ≤ 5 / 3 :=
          (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 5 / 3)).mp hlt
        have hinv : Real.exp (-1 / 3 : ℝ) = (Real.exp (1 / 3 : ℝ))⁻¹ := by
          rw [← Real.exp_neg]; ring_nf
        rw [hinv]
        rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 3 / 5) (Real.exp_pos _)]
        linarith
      calc (3 / 5 : ℝ) ^ n ≤ (Real.exp (-1 / 3 : ℝ)) ^ n :=
            pow_le_pow_left₀ (by norm_num) hbase n
        _ = Real.exp ((n : ℝ) * (-1 / 3 : ℝ)) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (-(n : ℝ) / 3) := by congr 1; ring
    have hexp_sq : (2 : ℝ) * (n : ℝ) ≤ Real.exp ((n : ℝ) / 6) := by
      have hhalf : (1 : ℝ) + (n : ℝ) / 12 ≤ Real.exp ((n : ℝ) / 12) := by
        linarith [Real.add_one_le_exp ((n : ℝ) / 12)]
      have hsq : ((1 : ℝ) + (n : ℝ) / 12) ^ 2 ≤ (Real.exp ((n : ℝ) / 12)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hhalf 2
      have heq : (Real.exp ((n : ℝ) / 12)) ^ 2 = Real.exp ((n : ℝ) / 6) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      rw [heq] at hsq
      nlinarith
    have hprod_exp : 2 * Real.exp ((n : ℝ) / 6) * Real.exp (-(n : ℝ) / 3) =
        2 * (Real.exp ((n : ℝ) / 6))⁻¹ := by
      rw [mul_assoc, ← Real.exp_add, ← Real.exp_neg]
      congr 2
      ring
    calc (M + 1 : ℝ) * (3 / 5 : ℝ) ^ n
        ≤ (2 * Real.exp ((n : ℝ) / 6)) * Real.exp (-(n : ℝ) / 3) :=
          mul_le_mul hM1_le h35_le (by positivity) (by positivity)
      _ = 2 * (Real.exp ((n : ℝ) / 6))⁻¹ := hprod_exp
      _ ≤ 2 * (2 * (n : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hexp_sq) (by norm_num)
      _ = 1 / (n : ℝ) := by field_simp
  calc ((E.filter fun a =>
          ∃ r : ℤ, r ≤ -2 ∧ (Green93.monicPoly fun j => (a j : ℕ)).eval r = 0).card : ℝ)
      ≤ (M : ℝ) * (((3 / 5 : ℝ) * (M + 1 : ℝ)) ^ n) := hcardN
    _ = ((M + 1 : ℝ) * (3 / 5 : ℝ) ^ n) * (E.card : ℝ) := hfactor
    _ ≤ (1 / (n : ℝ)) * (E.card : ℝ) :=
        mul_le_mul_of_nonneg_right hdecay (Nat.cast_nonneg _)

/-- Central binomial inequality `(2m choose m)^2 * (2m + 1) ≤ 4^(2m)`. -/
lemma choose_even_sq_mul_le (m : ℕ) :
    ((2 * m).choose m) ^ 2 * (2 * m + 1) ≤ 4 ^ (2 * m) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
      have h := Nat.choose_symm (by omega : m ≤ 2 * m + 1)
      have heq : 2 * m + 1 - m = m + 1 := by omega
      rw [heq] at h
      exact h
    have hstep1 : (m + 1) * (2 * m + 1).choose m = (2 * m + 1) * (2 * m).choose m := by
      have h := Nat.add_one_mul_choose_eq (2 * m) m
      rw [hsymm] at h
      linarith
    have hstep2 : (2 * m + 2).choose (m + 1) = 2 * (2 * m + 1).choose m := by
      have h := Nat.add_one_mul_choose_eq (2 * m + 1) m
      have h' : (m + 1) * (2 * m + 2).choose (m + 1) = (m + 1) * (2 * (2 * m + 1).choose m) := by
        linarith
      exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) h'
    have hrel : (m + 1) * (2 * m + 2).choose (m + 1) = 2 * (2 * m + 1) * (2 * m).choose m := by
      rw [hstep2]
      linarith
    have hmul : (m + 1) ^ 2 * (((2 * (m + 1)).choose (m + 1)) ^ 2 * (2 * (m + 1) + 1)) ≤
        (m + 1) ^ 2 * 4 ^ (2 * (m + 1)) := by
      have h1 : (m + 1) ^ 2 * (((2 * m + 2).choose (m + 1)) ^ 2 * (2 * m + 3)) =
          4 * (2 * m + 1) * (2 * m + 3) * (((2 * m).choose m) ^ 2 * (2 * m + 1)) := by
        have hsq : ((m + 1) * (2 * m + 2).choose (m + 1)) ^ 2 =
            (2 * (2 * m + 1) * (2 * m).choose m) ^ 2 := congrArg (· ^ 2) hrel
        nlinarith
      have h2 : 4 * (2 * m + 1) * (2 * m + 3) ≤ 16 * (m + 1) ^ 2 := by nlinarith
      have h3 : 4 * (2 * m + 1) * (2 * m + 3) * (((2 * m).choose m) ^ 2 * (2 * m + 1)) ≤
          16 * (m + 1) ^ 2 * 4 ^ (2 * m) :=
        Nat.mul_le_mul h2 ih
      have h4 : 16 * (m + 1) ^ 2 * 4 ^ (2 * m) = (m + 1) ^ 2 * 4 ^ (2 * (m + 1)) := by
        rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
        norm_num
        ring
      have heq2 : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
      have heq1 : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [heq2, heq1, h1]
      exact h3.trans_eq (by rw [← heq1]; exact h4)
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- Central binomial inequality `(k choose (k/2))^2 * (k + 1) ≤ 4^k` for all `k`. -/
lemma choose_middle_sq_mul_le (k : ℕ) :
    (k.choose (k / 2)) ^ 2 * (k + 1) ≤ 4 ^ k := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hdiv : (2 * m) / 2 = m := by omega
    rw [show m + m = 2 * m by omega, hdiv]
    exact choose_even_sq_mul_le m
  · have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
    have hstep2 : (2 * m + 2).choose (m + 1) = 2 * (2 * m + 1).choose m := by
      have h := Nat.add_one_mul_choose_eq (2 * m + 1) m
      have h' : (m + 1) * (2 * m + 2).choose (m + 1) = (m + 1) * (2 * (2 * m + 1).choose m) := by
        linarith
      exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) h'
    have heven := choose_even_sq_mul_le (m + 1)
    have hmul : 4 * (((2 * m + 1).choose m) ^ 2 * (2 * m + 2)) ≤ 4 * 4 ^ (2 * m + 1) := by
      calc 4 * (((2 * m + 1).choose m) ^ 2 * (2 * m + 2))
          = (2 * (2 * m + 1).choose m) ^ 2 * (2 * m + 2) := by ring
        _ = ((2 * m + 2).choose (m + 1)) ^ 2 * (2 * m + 2) := by rw [← hstep2]
        _ ≤ ((2 * (m + 1)).choose (m + 1)) ^ 2 * (2 * (m + 1) + 1) := by
            have : 2 * m + 2 ≤ 2 * (m + 1) + 1 := by omega
            simpa [show 2 * (m + 1) = 2 * m + 2 by omega] using
              Nat.mul_le_mul_left (((2 * m + 2).choose (m + 1)) ^ 2) this
        _ ≤ 4 ^ (2 * (m + 1)) := heven
        _ = 4 * 4 ^ (2 * m + 1) := by
            rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, pow_succ']
    exact Nat.le_of_mul_le_mul_left hmul (by norm_num)

/-- Real form: `choose k r * sqrt(k + 1) ≤ 2^k`. -/
lemma choose_mul_sqrt_le (k r : ℕ) :
    (k.choose r : ℝ) * Real.sqrt ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k := by
  have hmid : k.choose r ≤ k.choose (k / 2) := Nat.choose_le_middle r k
  have hsq : ((k.choose (k / 2) : ℝ) * Real.sqrt ((k : ℝ) + 1)) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm k 2, pow_mul]
    have hnat := choose_middle_sq_mul_le k
    have hreal : ((k.choose (k / 2) : ℝ) ^ 2) * ((k : ℝ) + 1) ≤ (4 : ℝ) ^ k := by
      exact_mod_cast hnat
    simpa [show (2 : ℝ) ^ 2 = 4 by norm_num] using hreal
  have hle : (k.choose (k / 2) : ℝ) * Real.sqrt ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k := by
    nlinarith [sq_nonneg ((k.choose (k / 2) : ℝ) * Real.sqrt ((k : ℝ) + 1) - (2 : ℝ) ^ k),
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k,
      mul_nonneg (Nat.cast_nonneg (k.choose (k / 2))) (Real.sqrt_nonneg ((k : ℝ) + 1))]
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hmid) (Real.sqrt_nonneg _)).trans hle

/-- Count of vectors with fewer than `m / 2` active coordinates is at most `(M + 1)^m / 2^m`. -/
lemma card_few_active_le (M m : ℕ) (hM : 15 ≤ M) :
    2 ^ m * ((Finset.univ : Finset (Fin m → Fin (M + 1))).filter
      fun b => ¬ (m ≤ 2 * ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2))).card)).card ≤ (M + 1) ^ m := by
  classical
  set H := (M + 1) / 2
  set Bad := (Finset.univ : Finset (Fin m → Fin (M + 1))).filter
    fun b => ¬ (m ≤ 2 * ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2))).card)
  set BigSets := (Finset.univ : Finset (Finset (Fin m))).filter fun S => m ≤ 2 * S.card
  have hmap : ∀ b ∈ Bad, ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)))ᶜ ∈ BigSets := by
    intro b hb
    simp only [Bad, BigSets, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    have hcomp : ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2))).card + ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)))ᶜ.card = m := by
      rw [Finset.card_add_card_compl, Fintype.card_fin]
    omega
  have hfiber : ∀ S ∈ BigSets,
      (Bad.filter fun b => ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)))ᶜ = S).card ≤ (M + 1) ^ (m - S.card) := by
    intro S _
    let restrict : (Fin m → Fin (M + 1)) → (↥(Sᶜ : Finset (Fin m)) → Fin (M + 1)) :=
      fun b i => b i.1
    have hinj : Set.InjOn restrict (Bad.filter fun b => ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)))ᶜ = S) := by
      intro b₁ hb₁ b₂ hb₂ heq
      have hS1 : ((Finset.univ.filter fun i => (b₁ i).val < 2 * ((M + 1) / 2)))ᶜ = S := (Finset.mem_filter.mp hb₁).2
      have hS2 : ((Finset.univ.filter fun i => (b₂ i).val < 2 * ((M + 1) / 2)))ᶜ = S := (Finset.mem_filter.mp hb₂).2
      funext i
      by_cases hi : i ∈ S
      · have hi1 : i ∉ (Finset.univ.filter fun i => (b₁ i).val < 2 * ((M + 1) / 2)) := by
          rw [← hS1] at hi; exact Finset.mem_compl.mp hi
        have hi2 : i ∉ (Finset.univ.filter fun i => (b₂ i).val < 2 * ((M + 1) / 2)) := by
          rw [← hS2] at hi; exact Finset.mem_compl.mp hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi1 hi2
        have hlt1 : (b₁ i).val < M + 1 := (b₁ i).isLt
        have hlt2 : (b₂ i).val < M + 1 := (b₂ i).isLt
        exact Fin.ext (by omega)
      · have hi' : i ∈ Sᶜ := Finset.mem_compl.mpr hi
        exact congrFun heq ⟨i, hi'⟩
    calc (Bad.filter fun b => ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)))ᶜ = S).card
        ≤ (Finset.univ : Finset (↥(Sᶜ : Finset (Fin m)) → Fin (M + 1))).card :=
          Finset.card_le_card_of_injOn restrict (fun _ _ => Finset.mem_univ _) hinj
      _ = (M + 1) ^ (m - S.card) := by simp
  have h4 : 4 ^ m * Bad.card ≤ 2 ^ m * (M + 1) ^ m := by
    calc 4 ^ m * Bad.card
        = 4 ^ m * ∑ S ∈ BigSets, (Bad.filter fun b => ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)))ᶜ = S).card := by
          rw [Finset.card_eq_sum_card_fiberwise hmap]
      _ = ∑ S ∈ BigSets, 4 ^ m * (Bad.filter fun b => ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)))ᶜ = S).card := by
          rw [Finset.mul_sum]
      _ ≤ ∑ S ∈ BigSets, (M + 1) ^ m := by
          apply Finset.sum_le_sum
          intro S hS
          have hSm : m ≤ 2 * S.card := (Finset.mem_filter.mp hS).2
          have hS_le : S.card ≤ m := by
            have := Finset.card_le_univ S
            simpa using this
          have hpow1 : 4 ^ m ≤ (M + 1) ^ S.card := by
            calc 4 ^ m ≤ 4 ^ (2 * S.card) := Nat.pow_le_pow_right (by norm_num) hSm
              _ = 16 ^ S.card := by rw [pow_mul]; norm_num
              _ ≤ (M + 1) ^ S.card := Nat.pow_le_pow_left (by omega) _
          calc 4 ^ m * (Bad.filter fun b => ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)))ᶜ = S).card
              ≤ (M + 1) ^ S.card * (M + 1) ^ (m - S.card) :=
                Nat.mul_le_mul hpow1 (hfiber S hS)
            _ = (M + 1) ^ (S.card + (m - S.card)) := by rw [← pow_add]
            _ = (M + 1) ^ m := by rw [Nat.add_sub_of_le hS_le]
      _ = BigSets.card * (M + 1) ^ m := by simp
      _ ≤ 2 ^ m * (M + 1) ^ m := by
          apply Nat.mul_le_mul_right
          calc BigSets.card ≤ (Finset.univ : Finset (Finset (Fin m))).card := Finset.card_le_univ _
            _ = 2 ^ m := by simp
  have h4eq : 4 ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  rw [h4eq, mul_assoc] at h4
  exact Nat.le_of_mul_le_mul_left h4 (by positivity)

/-- Anti-concentration for plain sums of `m` uniform `{0, ..., M}` variables (`M ≥ 15`, `m ≥ 1`). -/
lemma card_sum_eq_le (M m : ℕ) (hM : 15 ≤ M) (hm : 1 ≤ m) (t : ℤ) :
    (((Finset.univ : Finset (Fin m → Fin (M + 1))).filter
      fun b => ∑ i : Fin m, ((b i : ℕ) : ℤ) = t).card : ℝ) ≤
      (3 / Real.sqrt (m : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ m := by
  classical
  set H := (M + 1) / 2
  set T := (Finset.univ : Finset (Fin m → Fin (M + 1))).filter
    fun b => ∑ i : Fin m, ((b i : ℕ) : ℤ) = t
  set Good := T.filter fun b => m ≤ 2 * ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2))).card
  set Bad := T.filter fun b => ¬ (m ≤ 2 * ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2))).card)
  have hsplit : T.card = Good.card + Bad.card :=
    (Finset.card_filter_add_card_filter_not (s := T)
      (p := fun b => m ≤ 2 * ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2))).card)).symm
  let q : (Fin m → Fin (M + 1)) → (Fin m → ℕ) := fun b i => (b i).val / 2
  set Img := Good.image q
  have hGood_le : (Good.card : ℝ) * Real.sqrt ((m : ℝ) / 2) ≤ ((M + 1 : ℕ) : ℝ) ^ m := by
    have hfiber_le : ∀ f ∈ Img,
        ((Good.filter fun b => q b = f).card : ℝ) * Real.sqrt ((m : ℝ) / 2) ≤
          (((Finset.univ : Finset (Fin m → Fin (M + 1))).filter fun b => q b = f).card : ℝ) := by
      intro f hf
      obtain ⟨b₀, hb₀G, rfl⟩ := Finset.mem_image.mp hf
      set A := (Finset.univ.filter fun i => (b₀ i).val < 2 * ((M + 1) / 2))
      have hAm : m ≤ 2 * A.card := (Finset.mem_filter.mp hb₀G).2
      have hactive_eq : ∀ b : Fin m → Fin (M + 1), q b = q b₀ → (Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)) = A := by
        intro b hqb
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A]
        have hi : (b i).val / 2 = (b₀ i).val / 2 := congrFun hqb i
        omega
      -- Upper bound on Good fiber: inject into powersetCard r of A
      set s₀ : ℤ := ∑ i : Fin m, (2 * ((b₀ i).val / 2) : ℤ)
      set r : ℕ := (t - s₀).toNat
      have hS_le : (Good.filter fun b => q b = q b₀).card ≤ A.card.choose r := by
        let bits : (Fin m → Fin (M + 1)) → Finset (Fin m) :=
          fun b => A.filter fun i => (b i).val % 2 = 1
        have hmaps : ∀ b ∈ Good.filter fun b => q b = q b₀, bits b ∈ A.powersetCard r := by
          intro b hb
          have hbG : b ∈ Good := (Finset.mem_filter.mp hb).1
          have hqb : q b = q b₀ := (Finset.mem_filter.mp hb).2
          have hbT : ∑ i : Fin m, ((b i : ℕ) : ℤ) = t :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hbG).1).2
          have hAeq : (Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)) = A := hactive_eq b hqb
          have hsum_eq : ∑ i : Fin m, ((b i : ℕ) : ℤ) = s₀ + ((bits b).card : ℤ) := by
            have hterm : ∀ i : Fin m, ((b i : ℕ) : ℤ) =
                (2 * ((b₀ i).val / 2) : ℤ) + (if i ∈ bits b then (1 : ℤ) else 0) := by
              intro i
              have hqi : (b i).val / 2 = (b₀ i).val / 2 := congrFun hqb i
              have hdm : (b i).val = 2 * ((b i).val / 2) + (b i).val % 2 :=
                (Nat.div_add_mod (b i).val 2).symm
              by_cases hi : i ∈ A
              · by_cases hmod : (b i).val % 2 = 1
                · have hmem : i ∈ bits b := Finset.mem_filter.mpr ⟨hi, hmod⟩
                  simp only [hmem, ↓reduceIte]
                  omega
                · have hmod0 : (b i).val % 2 = 0 := by omega
                  have hmem : i ∉ bits b := fun h => hmod (Finset.mem_filter.mp h).2
                  simp only [hmem, ↓reduceIte]
                  omega
              · have hmem : i ∉ bits b := fun h => hi (Finset.mem_filter.mp h).1
                have hi' : i ∉ (Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2)) := by rwa [hAeq]
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi'
                have hlt : (b i).val < M + 1 := (b i).isLt
                have hmod0 : (b i).val % 2 = 0 := by omega
                simp only [hmem, ↓reduceIte]
                omega
            calc ∑ i : Fin m, ((b i : ℕ) : ℤ)
                = ∑ i : Fin m, ((2 * ((b₀ i).val / 2) : ℤ) +
                    (if i ∈ bits b then (1 : ℤ) else 0)) :=
                  Finset.sum_congr rfl (fun i _ => hterm i)
              _ = s₀ + ∑ i : Fin m, (if i ∈ bits b then (1 : ℤ) else 0) := by
                  rw [Finset.sum_add_distrib]
              _ = s₀ + ((bits b).card : ℤ) := by
                  congr 1
                  simp
          have hcard : (bits b).card = r := by
            have : ((bits b).card : ℤ) = t - s₀ := by linarith
            omega
          exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ A, hcard⟩
        have hinj : Set.InjOn bits (Good.filter fun b => q b = q b₀) := by
          intro b₁ hb₁ b₂ hb₂ heq
          have hq1 : q b₁ = q b₀ := (Finset.mem_filter.mp hb₁).2
          have hq2 : q b₂ = q b₀ := (Finset.mem_filter.mp hb₂).2
          have hA1 : (Finset.univ.filter fun i => (b₁ i).val < 2 * ((M + 1) / 2)) = A := hactive_eq b₁ hq1
          have hA2 : (Finset.univ.filter fun i => (b₂ i).val < 2 * ((M + 1) / 2)) = A := hactive_eq b₂ hq2
          funext i
          have hdiv : (b₁ i).val / 2 = (b₂ i).val / 2 := by
            change q b₁ i = q b₂ i
            rw [hq1, hq2]
          by_cases hi : i ∈ A
          · have hiff : (b₁ i).val % 2 = 1 ↔ (b₂ i).val % 2 = 1 := by
              have h1 : i ∈ bits b₁ ↔ (b₁ i).val % 2 = 1 := by simp [bits, hi]
              have h2 : i ∈ bits b₂ ↔ (b₂ i).val % 2 = 1 := by simp [bits, hi]
              rw [← h1, ← h2, heq]
            have hmod : (b₁ i).val % 2 = (b₂ i).val % 2 := by omega
            exact Fin.ext (by omega)
          · have hi1 : i ∉ (Finset.univ.filter fun i => (b₁ i).val < 2 * ((M + 1) / 2)) := by rwa [hA1]
            have hi2 : i ∉ (Finset.univ.filter fun i => (b₂ i).val < 2 * ((M + 1) / 2)) := by rwa [hA2]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi1 hi2
            have hlt1 : (b₁ i).val < M + 1 := (b₁ i).isLt
            have hlt2 : (b₂ i).val < M + 1 := (b₂ i).isLt
            exact Fin.ext (by omega)
        calc (Good.filter fun b => q b = q b₀).card
            ≤ (A.powersetCard r).card := Finset.card_le_card_of_injOn bits hmaps hinj
          _ = A.card.choose r := Finset.card_powersetCard r A
      -- Lower bound on full fiber: inject A.powerset into full fiber
      have hF_ge : 2 ^ A.card ≤
          ((Finset.univ : Finset (Fin m → Fin (M + 1))).filter fun b => q b = q b₀).card := by
        let φ : Finset (Fin m) → (Fin m → Fin (M + 1)) := fun S i =>
          if hi : i ∈ A then
            ⟨2 * ((b₀ i).val / 2) + (if i ∈ S then 1 else 0), by
              have hlt : (b₀ i).val < 2 * ((M + 1) / 2) := (Finset.mem_filter.mp hi).2
              split_ifs <;> omega⟩
          else b₀ i
        have hmaps : ∀ S ∈ A.powerset,
            φ S ∈ (Finset.univ : Finset (Fin m → Fin (M + 1))).filter fun b => q b = q b₀ := by
          intro S _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          funext i
          simp only [q, φ]
          by_cases hi : i ∈ A
          · simp only [hi, ↓reduceDIte]
            split_ifs <;> omega
          · simp [hi]
        have hinj : Set.InjOn φ A.powerset := by
          intro S₁ hS₁ S₂ hS₂ heq
          have hsub1 : S₁ ⊆ A := Finset.mem_powerset.mp hS₁
          have hsub2 : S₂ ⊆ A := Finset.mem_powerset.mp hS₂
          ext i
          by_cases hi : i ∈ A
          · have hi_eq := congrArg Fin.val (congrFun heq i)
            simp only [φ, hi, ↓reduceDIte] at hi_eq
            by_cases h1 : i ∈ S₁ <;> by_cases h2 : i ∈ S₂
            · exact ⟨fun _ => h2, fun _ => h1⟩
            · simp only [h1, h2, ↓reduceIte] at hi_eq; omega
            · simp only [h1, h2, ↓reduceIte] at hi_eq; omega
            · exact ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩
          · exact ⟨fun h => (hi (hsub1 h)).elim, fun h => (hi (hsub2 h)).elim⟩
        calc 2 ^ A.card = A.powerset.card := (Finset.card_powerset A).symm
          _ ≤ ((Finset.univ : Finset (Fin m → Fin (M + 1))).filter fun b => q b = q b₀).card :=
            Finset.card_le_card_of_injOn φ hmaps hinj
      have hsqrt_le : Real.sqrt ((m : ℝ) / 2) ≤ Real.sqrt ((A.card : ℝ) + 1) := by
        apply Real.sqrt_le_sqrt
        have hAmR : (m : ℝ) ≤ 2 * (A.card : ℝ) := by exact_mod_cast hAm
        linarith
      calc ((Good.filter fun b => q b = q b₀).card : ℝ) * Real.sqrt ((m : ℝ) / 2)
          ≤ (A.card.choose r : ℝ) * Real.sqrt ((A.card : ℝ) + 1) :=
            mul_le_mul (by exact_mod_cast hS_le) hsqrt_le (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
        _ ≤ (2 : ℝ) ^ A.card := choose_mul_sqrt_le A.card r
        _ ≤ (((Finset.univ : Finset (Fin m → Fin (M + 1))).filter
              fun b => q b = q b₀).card : ℝ) := by exact_mod_cast hF_ge
    have hsum_F : ∑ f ∈ Img,
        ((Finset.univ : Finset (Fin m → Fin (M + 1))).filter fun b => q b = f).card ≤
        (M + 1) ^ m := by
      have hdisj : Set.PairwiseDisjoint (Img : Set (Fin m → ℕ))
          (fun f => (Finset.univ : Finset (Fin m → Fin (M + 1))).filter fun b => q b = f) := by
        intro f₁ _ f₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro b hb1 hb2
        exact hne ((Finset.mem_filter.mp hb1).2.symm.trans (Finset.mem_filter.mp hb2).2)
      rw [← Finset.card_biUnion hdisj]
      calc (Img.biUnion fun f =>
              (Finset.univ : Finset (Fin m → Fin (M + 1))).filter fun b => q b = f).card
          ≤ (Finset.univ : Finset (Fin m → Fin (M + 1))).card := Finset.card_le_univ _
        _ = (M + 1) ^ m := by simp
    calc (Good.card : ℝ) * Real.sqrt ((m : ℝ) / 2)
        = (∑ f ∈ Img, ((Good.filter fun b => q b = f).card : ℝ)) * Real.sqrt ((m : ℝ) / 2) := by
          have hfib : Good.card = ∑ f ∈ Img, (Good.filter fun b => q b = f).card :=
            Finset.card_eq_sum_card_fiberwise (fun b hb => Finset.mem_image_of_mem q hb)
          rw [hfib, Nat.cast_sum]
      _ = ∑ f ∈ Img, ((Good.filter fun b => q b = f).card : ℝ) * Real.sqrt ((m : ℝ) / 2) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ f ∈ Img,
            (((Finset.univ : Finset (Fin m → Fin (M + 1))).filter fun b => q b = f).card : ℝ) :=
          Finset.sum_le_sum hfiber_le
      _ ≤ ((M + 1 : ℕ) : ℝ) ^ m := by exact_mod_cast hsum_F
  have hBad_le : (Bad.card : ℝ) * Real.sqrt ((m : ℝ) / 2) ≤ ((M + 1 : ℕ) : ℝ) ^ m := by
    have hBad_sub : Bad.card ≤ ((Finset.univ : Finset (Fin m → Fin (M + 1))).filter
        fun b => ¬ (m ≤ 2 * ((Finset.univ.filter fun i => (b i).val < 2 * ((M + 1) / 2))).card)).card := by
      apply Finset.card_le_card
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
    have hBadN : 2 ^ m * Bad.card ≤ (M + 1) ^ m :=
      (Nat.mul_le_mul_left (2 ^ m) hBad_sub).trans (card_few_active_le M m hM)
    have hsqrt_pow : Real.sqrt ((m : ℝ) / 2) ≤ (2 : ℝ) ^ m := by
      have hm_le : (m : ℝ) ≤ (2 : ℝ) ^ m := by
        exact_mod_cast Nat.lt_two_pow_self.le
      have hsq : (m : ℝ) / 2 ≤ ((2 : ℝ) ^ m) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
        nlinarith
      calc Real.sqrt ((m : ℝ) / 2) ≤ Real.sqrt (((2 : ℝ) ^ m) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = (2 : ℝ) ^ m := Real.sqrt_sq (by positivity)
    calc (Bad.card : ℝ) * Real.sqrt ((m : ℝ) / 2)
        ≤ (Bad.card : ℝ) * (2 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_left hsqrt_pow (Nat.cast_nonneg _)
      _ = (2 : ℝ) ^ m * (Bad.card : ℝ) := by ring
      _ ≤ ((M + 1 : ℕ) : ℝ) ^ m := by exact_mod_cast hBadN
  have hT : (T.card : ℝ) * Real.sqrt ((m : ℝ) / 2) ≤ 2 * ((M + 1 : ℕ) : ℝ) ^ m := by
    have hsplitR : (T.card : ℝ) = (Good.card : ℝ) + (Bad.card : ℝ) := by exact_mod_cast hsplit
    rw [hsplitR, add_mul]
    linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsqrt_pos : 0 < Real.sqrt ((m : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  have h2sqrt2 : 2 * Real.sqrt 2 ≤ 3 := by
    have hsq : (2 * Real.sqrt 2) ^ 2 ≤ (3 : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [sq_nonneg (2 * Real.sqrt 2 - 3), Real.sqrt_nonneg 2]
  have hdiv : (T.card : ℝ) ≤ (2 / Real.sqrt ((m : ℝ) / 2)) * ((M + 1 : ℕ) : ℝ) ^ m := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsqrt_pos]
    exact hT
  have hratio : 2 / Real.sqrt ((m : ℝ) / 2) ≤ 3 / Real.sqrt (m : ℝ) := by
    rw [Real.sqrt_div (by positivity), div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right h2sqrt2 (Real.sqrt_nonneg _)
  exact hdiv.trans (mul_le_mul_of_nonneg_right hratio (by positivity))

/-- Anti-concentration bound for the root `r = -1`. -/
lemma card_root_neg_one_bound {M n : ℕ} (hM : 34 ≤ M) (hn : 3 ≤ n) :
    (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a =>
        (Green93.monicPoly fun j => (a j : ℕ)).eval (-1) = 0).card : ℝ) ≤
      (4 / Real.sqrt (n : ℝ)) *
        ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
          (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ) := by
  classical
  set E := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
  set S := E.filter fun a => (Green93.monicPoly fun j => (a j : ℕ)).eval (-1) = 0
  have hn1 : 1 ≤ n := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  -- Fiber over a 0 ∈ Finset.univ.erase 0
  have hmap : ∀ a ∈ S, a 0 ∈ (Finset.univ : Finset (Fin (M + 1))).erase 0 := by
    intro a ha
    have ha0 : (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    rw [monicPoly_coeff_zero hn1] at ha0
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h0
    apply ha0
    change ((a 0 : ℕ) : ℤ) = 0
    simp [h0]
  have hfiber : ∀ c ∈ (Finset.univ : Finset (Fin (M + 1))).erase 0,
      ((S.filter fun a => a 0 = c).card : ℝ) ≤
        (3 / Real.sqrt (m : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ m := by
    intro c _
    -- Flip odd-indexed coordinates of tail so alternating sum becomes plain sum
    let flip : (Fin (m + 1) → Fin (M + 1)) → (Fin m → Fin (M + 1)) := fun a i =>
      if (i.val + 1) % 2 = 0 then a i.succ else ⟨M - (a i.succ).val, by omega⟩
    let oddCount : ℤ := ∑ i : Fin m, if (i.val + 1) % 2 = 0 then (0 : ℤ) else (M : ℤ)
    let t : ℤ := oddCount - (-1 : ℤ) ^ (m + 1) - (c.val : ℤ)
    have hmaps : ∀ a ∈ S.filter fun a => a 0 = c,
        flip a ∈ (Finset.univ : Finset (Fin m → Fin (M + 1))).filter
          fun b => ∑ i : Fin m, ((b i : ℕ) : ℤ) = t := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have haS : a ∈ S := (Finset.mem_filter.mp ha).1
      have ha0 : a 0 = c := (Finset.mem_filter.mp ha).2
      have heval : (Green93.monicPoly fun j => (a j : ℕ)).eval (-1) = 0 :=
        (Finset.mem_filter.mp haS).2
      rw [monicPoly_eval, Fin.sum_univ_succ] at heval
      simp only [Fin.val_zero, pow_zero, mul_one, ha0] at heval
      have hterm : ∀ i : Fin m,
          ((flip a i : ℕ) : ℤ) =
            (if (i.val + 1) % 2 = 0 then (0 : ℤ) else (M : ℤ)) +
              ((a i.succ : ℕ) : ℤ) * (-1 : ℤ) ^ (i.succ : ℕ) := by
        intro i
        simp only [flip, Fin.val_succ]
        by_cases hev : (i.val + 1) % 2 = 0
        · have hpow : (-1 : ℤ) ^ (i.val + 1) = 1 := by
            obtain ⟨q, hq⟩ : ∃ q, i.val + 1 = 2 * q := ⟨(i.val + 1) / 2, by omega⟩
            rw [hq, pow_mul]; norm_num
          simp [hev, hpow]
        · have hpow : (-1 : ℤ) ^ (i.val + 1) = -1 := by
            obtain ⟨q, hq⟩ : ∃ q, i.val + 1 = 2 * q + 1 := ⟨(i.val + 1) / 2, by omega⟩
            rw [hq, pow_succ, pow_mul]; norm_num
          have hle : (a i.succ).val ≤ M := Nat.le_of_lt_succ (a i.succ).isLt
          simp only [hev, ↓reduceIte, hpow, mul_neg_one]
          omega
      calc ∑ i : Fin m, ((flip a i : ℕ) : ℤ)
          = ∑ i : Fin m, ((if (i.val + 1) % 2 = 0 then (0 : ℤ) else (M : ℤ)) +
              ((a i.succ : ℕ) : ℤ) * (-1 : ℤ) ^ (i.succ : ℕ)) :=
            Finset.sum_congr rfl (fun i _ => hterm i)
        _ = oddCount + ∑ i : Fin m, ((a i.succ : ℕ) : ℤ) * (-1 : ℤ) ^ (i.succ : ℕ) := by
            rw [Finset.sum_add_distrib]
        _ = t := by linarith
    have hinj : Set.InjOn flip (S.filter fun a => a 0 = c) := by
      intro a₁ ha₁ a₂ ha₂ heq
      have h01 : a₁ 0 = c := (Finset.mem_filter.mp ha₁).2
      have h02 : a₂ 0 = c := (Finset.mem_filter.mp ha₂).2
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [h01, h02]
      · have hi := congrArg Fin.val (congrFun heq i)
        simp only [flip] at hi
        split_ifs at hi
        · exact Fin.ext hi
        · simp only at hi
          have h1 : (a₁ i.succ).val ≤ M := Nat.le_of_lt_succ (a₁ i.succ).isLt
          have h2 : (a₂ i.succ).val ≤ M := Nat.le_of_lt_succ (a₂ i.succ).isLt
          exact Fin.ext (by omega)
    have hcard : (S.filter fun a => a 0 = c).card ≤
        ((Finset.univ : Finset (Fin m → Fin (M + 1))).filter
          fun b => ∑ i : Fin m, ((b i : ℕ) : ℤ) = t).card :=
      Finset.card_le_card_of_injOn flip hmaps hinj
    exact (Nat.cast_le.mpr hcard).trans (card_sum_eq_le M m (by omega) hm1 t)
  have hS : (S.card : ℝ) ≤ (M : ℝ) * ((3 / Real.sqrt (m : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ m) := by
    have hfib : S.card = ∑ c ∈ (Finset.univ : Finset (Fin (M + 1))).erase 0,
        (S.filter fun a => a 0 = c).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    calc (S.card : ℝ)
        = ∑ c ∈ (Finset.univ : Finset (Fin (M + 1))).erase 0,
            ((S.filter fun a => a 0 = c).card : ℝ) := by rw [hfib, Nat.cast_sum]
      _ ≤ ∑ _c ∈ (Finset.univ : Finset (Fin (M + 1))).erase 0,
            ((3 / Real.sqrt (m : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ m) :=
          Finset.sum_le_sum hfiber
      _ = (((Finset.univ : Finset (Fin (M + 1))).erase 0).card : ℝ) *
            ((3 / Real.sqrt (m : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ m) := by simp
      _ = (M : ℝ) * ((3 / Real.sqrt (m : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ m) := by
          simp [Finset.card_erase_of_mem]
  have hEcard : (E.card : ℝ) = (M : ℝ) * ((M + 1 : ℕ) : ℝ) ^ m := by
    have := card_eligible M (m + 1) hn1
    change E.card = M * (M + 1) ^ m at this
    exact_mod_cast this
  have hratio : 3 / Real.sqrt (m : ℝ) ≤ 4 / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))]
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
    have hsq : (3 * Real.sqrt ((m + 1 : ℕ) : ℝ)) ^ 2 ≤ (4 * Real.sqrt (m : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      push_cast
      nlinarith
    nlinarith [sq_nonneg (3 * Real.sqrt ((m + 1 : ℕ) : ℝ) - 4 * Real.sqrt (m : ℝ)),
      Real.sqrt_nonneg ((m + 1 : ℕ) : ℝ), Real.sqrt_nonneg (m : ℝ)]
  calc (S.card : ℝ)
      ≤ (M : ℝ) * ((3 / Real.sqrt (m : ℝ)) * ((M + 1 : ℕ) : ℝ) ^ m) := hS
    _ = (3 / Real.sqrt (m : ℝ)) * (E.card : ℝ) := by rw [hEcard]; ring
    _ ≤ (4 / Real.sqrt ((m + 1 : ℕ) : ℝ)) * (E.card : ℝ) :=
        mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)

open scoped Classical in
/-- Combined bound for all eligible polynomials having a monic degree-1 divisor. -/
lemma card_deg_one_divisor_bound {M n : ℕ} (hM : 34 ≤ M) (hn : 288 ≤ n)
    (hlog : (Real.log (M : ℝ)) ^ 3 ≤ n) :
    (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) =>
        ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
          g.natDegree = 1).card : ℝ) ≤
      (5 / Real.sqrt (n : ℝ)) *
        ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
          (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ) := by
  classical
  set E := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
  set D1 := E.filter fun a =>
    ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧ g.natDegree = 1
  set Rneg1 := E.filter fun a => (Green93.monicPoly fun j => (a j : ℕ)).eval (-1) = 0
  set Rneg2 := E.filter fun a =>
    ∃ r : ℤ, r ≤ -2 ∧ (Green93.monicPoly fun j => (a j : ℕ)).eval r = 0
  have hn1 : 1 ≤ n := by omega
  have hsub : D1 ⊆ Rneg1 ∪ Rneg2 := by
    intro a ha
    obtain ⟨haE, g, hgM, hdvd, hdeg⟩ := Finset.mem_filter.mp ha
    obtain ⟨r, hr⟩ := exists_int_root_of_monic_deg_one hgM hdeg hdvd
    have ha0 : (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 := (Finset.mem_filter.mp haE).2
    have ha0' : (a ⟨0, hn1⟩ : ℕ) ≠ 0 := by
      rw [monicPoly_coeff_zero hn1] at ha0
      exact fun h => ha0 (by exact_mod_cast h)
    by_cases hnonneg : 0 ≤ r
    · exact absurd hr (monicPoly_eval_pos_of_nonneg hn1 (fun j => (a j : ℕ)) ha0' hnonneg).ne'
    · by_cases hm1 : r = -1
      · subst hm1
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haE, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haE, r, by omega, hr⟩)
  have hcard : (D1.card : ℝ) ≤ (Rneg1.card : ℝ) + (Rneg2.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le Rneg1 Rneg2)
  have h1 := card_root_neg_one_bound (M := M) (n := n) hM (by omega)
  have h2 := card_roots_le_neg_two_bound (M := M) (n := n) hM hn hlog
  have hinv_le : 1 / (n : ℝ) ≤ 1 / Real.sqrt (n : ℝ) := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hsq : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      have : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      simpa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ n)] using this
    exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr (by positivity)) hsq
  have hE0 : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
  have h1' : (Rneg1.card : ℝ) ≤ (4 / Real.sqrt (n : ℝ)) * (E.card : ℝ) := by
    convert h1 using 3
  have h2_aligned : (Rneg2.card : ℝ) ≤ (1 / (n : ℝ)) * (E.card : ℝ) := by
    convert h2 using 3
  have h2' : (Rneg2.card : ℝ) ≤ (1 / Real.sqrt (n : ℝ)) * (E.card : ℝ) :=
    h2_aligned.trans (mul_le_mul_of_nonneg_right hinv_le hE0)
  have hsum5 : (4 / Real.sqrt (n : ℝ)) * (E.card : ℝ) + (1 / Real.sqrt (n : ℝ)) * (E.card : ℝ) =
      (5 / Real.sqrt (n : ℝ)) * (E.card : ℝ) := by ring
  linarith

open scoped Classical in
lemma deg2_of (hA : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n → (Real.log (M : ℝ)) ^ 3 ≤ n →
      (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) ↦
          ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) ∧
            2 ≤ g.natDegree ∧ g.natDegree ^ 10 ≤ n).card : ℝ) ≤
      ((n : ℝ) ^ (-c) / 4) * ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ))
    (hB : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n → (Real.log (M : ℝ)) ^ 3 ≤ n →
      (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) ↦
          ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) ∧
            n < g.natDegree ^ 10 ∧ 2 * g.natDegree ≤ n).card : ℝ) ≤
      ((n : ℝ) ^ (-c) / 4) * ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n → (Real.log (M : ℝ)) ^ 3 ≤ n →
      (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) ↦
          ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) ∧
            2 ≤ g.natDegree ∧ 2 * g.natDegree ≤ n).card : ℝ) ≤
      ((n : ℝ) ^ (-c) / 2) * ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ) := by
  obtain ⟨c₁, hc₁, n₁, h₁⟩ := hA
  obtain ⟨c₂, hc₂, n₂, h₂⟩ := hB
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max (max n₁ n₂) 1, fun M n hM hn hlog => ?_⟩
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : n₂ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn0 : 1 ≤ n := (le_max_right _ _).trans hn
  set E := (Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0)
  set D := E.filter fun a : Fin n → Fin (M + 1) ↦
          ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) ∧
            2 ≤ g.natDegree ∧ 2 * g.natDegree ≤ n
  set A := E.filter fun a : Fin n → Fin (M + 1) ↦
          ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) ∧
            2 ≤ g.natDegree ∧ g.natDegree ^ 10 ≤ n
  set B := E.filter fun a : Fin n → Fin (M + 1) ↦
          ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) ∧
            n < g.natDegree ^ 10 ∧ 2 * g.natDegree ≤ n
  have hsub : D ⊆ A ∪ B := by
    intro a ha
    obtain ⟨haE, g, hgM, hdvd, h2d, hhalf⟩ := Finset.mem_filter.mp ha
    by_cases hs : g.natDegree ^ 10 ≤ n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haE, g, hgM, hdvd, h2d, hs⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haE, g, hgM, hdvd, by omega, hhalf⟩)
  have hcard : (D.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  have hA' : (A.card : ℝ) ≤ ((n : ℝ) ^ (-c₁) / 4) * (E.card : ℝ) := by
    convert h₁ M n hM hn1 hlog using 3
  have hB' : (B.card : ℝ) ≤ ((n : ℝ) ^ (-c₂) / 4) * (E.card : ℝ) := by
    convert h₂ M n hM hn2 hlog using 3
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have hp1 : (n : ℝ) ^ (-c₁) ≤ (n : ℝ) ^ (-min c₁ c₂) :=
    Real.rpow_le_rpow_of_exponent_le hnR (neg_le_neg (min_le_left c₁ c₂))
  have hp2 : (n : ℝ) ^ (-c₂) ≤ (n : ℝ) ^ (-min c₁ c₂) :=
    Real.rpow_le_rpow_of_exponent_le hnR (neg_le_neg (min_le_right c₁ c₂))
  have hE0 : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_right hp1 hE0
  have := mul_le_mul_of_nonneg_right hp2 hE0
  show (D.card : ℝ) ≤ ((n : ℝ) ^ (-min c₁ c₂) / 2) * (E.card : ℝ)
  nlinarith

open scoped Classical in
lemma core_of (hdeg2 : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n → (Real.log (M : ℝ)) ^ 3 ≤ n →
      (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) ↦
          ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) ∧
            2 ≤ g.natDegree ∧ 2 * g.natDegree ≤ n).card : ℝ) ≤
      ((n : ℝ) ^ (-c) / 2) * ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n → (Real.log (M : ℝ)) ^ 3 ≤ n →
      (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) ↦
          ¬ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))).card : ℝ) ≤
      (n : ℝ) ^ (-c) * ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ) := by
  obtain ⟨c₂, hc₂, n₂, h₂⟩ := hdeg2
  refine ⟨min c₂ (1 / 4), lt_min hc₂ (by norm_num), max 4477456 n₂, fun M n hM hn hlog => ?_⟩
  set E := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
  set Bad := E.filter fun a => ¬ Irreducible (Green93.monicPoly fun j => (a j : ℕ))
  set D1 := E.filter fun a =>
    ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧ g.natDegree = 1
  set D2 := E.filter fun a =>
    ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
      2 ≤ g.natDegree ∧ 2 * g.natDegree ≤ n
  have hnBig : 4477456 ≤ n := (le_max_left 4477456 n₂).trans hn
  have hn2 : n₂ ≤ n := (le_max_right 4477456 n₂).trans hn
  have hsub : Bad ⊆ D1 ∪ D2 := by
    intro a ha
    obtain ⟨haE, hred⟩ := Finset.mem_filter.mp ha
    have hm : (Green93.monicPoly fun j => (a j : ℕ)).Monic := monicPoly_monic _
    have hd : (Green93.monicPoly fun j => (a j : ℕ)).natDegree = n := monicPoly_natDegree _
    obtain ⟨g, hgM, hdvd, hge1, hhalf⟩ :=
      exists_monic_dvd_of_not_irreducible hm (by omega) hred
    rw [hd] at hhalf
    by_cases h1 : g.natDegree = 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haE, g, hgM, hdvd, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haE, g, hgM, hdvd, by omega, hhalf⟩)
  have hbad : (Bad.card : ℝ) ≤ (D1.card : ℝ) + (D2.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le D1 D2)
  have hd1 := card_deg_one_divisor_bound (M := M) (n := n) hM (by omega) hlog
  have hd2 := h₂ M n hM hn2 hlog
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnBigR : (4477456 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnBig
  have h23_le : 23 / Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) / 2 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hsqrt_eq : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (n : ℝ)
    have hq : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hnpos]; norm_num
    have h46 : (46 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
      have h46pow : (46 : ℝ) ^ (4 : ℝ) ≤ (n : ℝ) := by norm_num; linarith
      calc (46 : ℝ) = ((46 : ℝ) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) h46pow (by norm_num)
    have hrpow_pos : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hnpos _
    have hneg : (n : ℝ) ^ (-(1 / 4 : ℝ)) = ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ := Real.rpow_neg hnpos.le _
    rw [hsqrt_eq, hneg, ← hq]
    have hkey : 23 / ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ)) ≤
        ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      field_simp
      linarith
    exact hkey
  have hpow1 : (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (n : ℝ) ^ (-min c₂ (1 / 4)) :=
    Real.rpow_le_rpow_of_exponent_le hnR (neg_le_neg (min_le_right c₂ (1 / 4)))
  have hpow2 : (n : ℝ) ^ (-c₂) ≤ (n : ℝ) ^ (-min c₂ (1 / 4)) :=
    Real.rpow_le_rpow_of_exponent_le hnR (neg_le_neg (min_le_left c₂ (1 / 4)))
  have hE0 : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
  have hd1_aligned : (D1.card : ℝ) ≤ (5 / Real.sqrt (n : ℝ)) * (E.card : ℝ) := by
    convert hd1 using 3
  have h5le : 5 / Real.sqrt (n : ℝ) ≤ 23 / Real.sqrt (n : ℝ) :=
    div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
  have hd1' : (D1.card : ℝ) ≤ ((n : ℝ) ^ (-min c₂ (1 / 4)) / 2) * (E.card : ℝ) :=
    hd1_aligned.trans (mul_le_mul_of_nonneg_right
      (h5le.trans (h23_le.trans (div_le_div_of_nonneg_right hpow1 (by norm_num)))) hE0)
  have hd2_aligned : (D2.card : ℝ) ≤ ((n : ℝ) ^ (-c₂) / 2) * (E.card : ℝ) := by
    convert hd2 using 3
  have hd2' : (D2.card : ℝ) ≤ ((n : ℝ) ^ (-min c₂ (1 / 4)) / 2) * (E.card : ℝ) :=
    hd2_aligned.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hpow2 (by norm_num)) hE0)
  linarith


open scoped Classical in
lemma solution_of (hcore : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n → (Real.log (M : ℝ)) ^ 3 ≤ n →
      (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) ↦
          ¬ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))).card : ℝ) ≤
      (n : ℝ) ^ (-c) * ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ)) :
    type_of% @Green93.green_93.variants.bskk_large := by
  classical
  obtain ⟨c, hc, n₀, h⟩ := hcore
  refine ⟨c, hc, n₀, fun M n hM hn hlog => ?_⟩
  have hb := h M n hM hn hlog
  set E := (Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0) with hE
  have hEpos : (0 : ℝ) < E.card := by
    exact_mod_cast (eligible_nonempty M n (by omega)).card_pos
  have hsplit := Finset.card_filter_add_card_filter_not (s := E)
    (p := fun a ↦ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ)))
  have hI : (Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
      (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0 ∧
        Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))) =
      E.filter (fun a ↦ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))) := by
    rw [hE, Finset.filter_filter]
  unfold Green93.irreducibleProb
  rw [hI, ← hE, le_div_iff₀ hEpos]
  have hcast : ((E.filter fun a ↦ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))).card : ℝ)
      + ((E.filter fun a ↦ ¬ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))).card : ℝ)
      = E.card := by exact_mod_cast hsplit
  have hb' : ((E.filter fun a ↦ ¬ Irreducible (Green93.monicPoly fun j ↦ (a j : ℕ))).card : ℝ)
      ≤ (n : ℝ) ^ (-c) * (E.card : ℝ) := by
    convert hb using 4
  nlinarith

open scoped Classical in
/-- Small-degree factors: a monic factor of degree `2 ≤ d` with `d ^ 10 ≤ n`
(BSKK23 Sections 2.1-2.2: Mahler measure and anti-concentration regime). -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n → (Real.log (M : ℝ)) ^ 3 ≤ n →
      (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) ↦
          ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) ∧
            2 ≤ g.natDegree ∧ g.natDegree ^ 10 ≤ n).card : ℝ) ≤
      ((n : ℝ) ^ (-c) / 4) * ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ)

open scoped Classical in
/-- Large-degree factors: a monic factor of degree `d` with `n < d ^ 10` and `2 d ≤ n`
(BSKK23 Sections 3-8: equidistribution modulo primes and factorization anatomy). -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₀ ≤ n → (Real.log (M : ℝ)) ^ 3 ≤ n →
      (((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).filter fun a : Fin n → Fin (M + 1) ↦
          ∃ g : ℤ[X], g.Monic ∧ g ∣ Green93.monicPoly (fun j ↦ (a j : ℕ)) ∧
            n < g.natDegree ^ 10 ∧ 2 * g.natDegree ≤ n).card : ℝ) ≤
      ((n : ℝ) ^ (-c) / 4) * ((Finset.univ.filter fun a : Fin n → Fin (M + 1) ↦
        (Green93.monicPoly fun j ↦ (a j : ℕ)).coeff 0 ≠ 0).card : ℝ)

theorem main : H1 → H2 → type_of% @Green93.green_93.variants.bskk_large := by
  intro h1 h2
  exact solution_of (core_of (deg2_of h1 h2))

end OMA.R_Green93_green_93_variants_bskk_large_R2
