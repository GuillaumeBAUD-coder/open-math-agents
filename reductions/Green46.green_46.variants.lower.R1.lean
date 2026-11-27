import FormalConjectures.GreensOpenProblems.«46»

-- Reduction Green46.green_46.variants.lower.R1 of Ben Green's Open Problem 46 — lower
-- Credit: @chris01-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
The deduction of the lower bound from the sieving theorem of Ford, Green, Konyagin, Maynard
and Tao, Long gaps between primes, J. Amer. Math. Soc. 31 (2018), Section 3.

Write y = c x log x log_3 x / log_2 x and z = x ^ (log_3 x / (4 log_2 x)).
H1 is Theorem 2 of that paper (sieving primes): residue classes for the primes in
(log^20 x, z] and in (x/2, x] can be chosen so that only O(x / log x) primes of (x, y] survive.
H2 is the smooth number estimate used there: at most x / log x integers up to x log x have
all their prime factors at most z.

The proof of main is the rest of Section 3: the primes up to log^20 x and in (z, x/2] take the
class 0, so a survivor in (x, y] is z-smooth or a prime; the O(x / log x) survivors are then
matched with distinct primes of (x, C x] (Chebyshev), which covers (x, y], and a shift and a
change of variable give the bound for the function of the problem.
-/

namespace OMA.R_Green46_green_46_variants_lower_R1

open Real Filter

-- Theorem 2 (sieving primes) of Ford, Green, Konyagin, Maynard, Tao: one residue class a p for
-- each prime p in (log^20 x, z] or (x/2, x] leaves O(x / log x) primes q in (x, y].
def H1 : Prop := ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ᶠ x : ℕ in atTop, ∃ a : ℕ → ℕ,
    ({q : ℕ | q.Prime ∧ x < q ∧
        (q : ℝ) ≤ c * (x : ℝ) * Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) /
          Real.log (Real.log (x : ℝ)) ∧
        ∀ p : ℕ, p.Prime →
          (Real.log (x : ℝ) ^ 20 < (p : ℝ) ∧
              (p : ℝ) ≤ (x : ℝ) ^
                (Real.log (Real.log (Real.log (x : ℝ))) / (4 * Real.log (Real.log (x : ℝ)))) ∨
            x < 2 * p ∧ p ≤ x) →
          ¬ q ≡ a p [MOD p]}.ncard : ℝ) ≤ K * (x : ℝ) / Real.log (x : ℝ)

-- Smooth numbers: at most x / log x positive integers up to x log x have all their prime
-- factors at most z = x ^ (log_3 x / (4 log_2 x)).
def H2 : Prop := ∀ᶠ x : ℕ in atTop,
    ({n : ℕ | 0 < n ∧ (n : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) ∧
        ∀ p : ℕ, p.Prime → p ∣ n →
          (p : ℝ) ≤ (x : ℝ) ^
            (Real.log (Real.log (Real.log (x : ℝ))) / (4 * Real.log (Real.log (x : ℝ))))}.ncard : ℝ)
      ≤ (x : ℝ) / Real.log (x : ℝ)

lemma log_le_two_sqrt (t : ℝ) (ht : 0 < t) : log t ≤ 2 * √t := by
  have h1 : log (√t) = log t / 2 := Real.log_sqrt ht.le
  have h2 : log (√t) ≤ √t - 1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht)
  linarith

lemma mul_log_le (A t : ℝ) (hA : 0 < A) (ht : (2 * A) ^ 2 ≤ t) : A * log t ≤ t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hs : 2 * A ≤ √t := Real.le_sqrt_of_sq_le ht
  have h1 := log_le_two_sqrt t ht0
  have h2 : √t * √t = t := Real.mul_self_sqrt ht0.le
  have h3 : 0 ≤ √t := Real.sqrt_nonneg t
  nlinarith

lemma covered_mono {x x' y : ℕ} (h : Green46.IsCoveredByResidues x y) (hx : x ≤ x') :
    Green46.IsCoveredByResidues x' y := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun m hm => ?_⟩
  obtain ⟨p, hp, h1, h2⟩ := ha m hm
  exact ⟨p, hp.trans hx, h1, h2⟩

lemma covered_bdd (x : ℕ) : BddAbove {y | Green46.IsCoveredByResidues x y} := by
  classical
  set s : Finset ℕ := (Finset.range (x + 1)).filter Nat.Prime with hs
  refine ⟨2 * ∏ p ∈ s, p, ?_⟩
  rintro y ⟨a, ha⟩
  by_contra hcon
  push Not at hcon
  have hpos : 0 < ∏ p ∈ s, p :=
    Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
  have hcop : Set.Pairwise (s : Set ℕ) (Function.onFun Nat.Coprime (fun p : ℕ => p)) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).mpr hpq
  have hne : ∀ p ∈ s, (fun p : ℕ => p) p ≠ 0 := fun p hp => (Finset.mem_filter.mp hp).2.ne_zero
  have hklt := Nat.chineseRemainderOfFinset_lt_prod (fun p : ℕ => a p + 1) (fun p : ℕ => p) hne hcop
  have hk := (Nat.chineseRemainderOfFinset (fun p : ℕ => a p + 1) (fun p : ℕ => p) s hne hcop).2
  set k : ℕ := (Nat.chineseRemainderOfFinset (fun p : ℕ => a p + 1) (fun p : ℕ => p) s hne hcop : ℕ)
    with hkdef
  have hm : k + ∏ p ∈ s, p ∈ Finset.Icc 1 y := by
    rw [Finset.mem_Icc]
    constructor
    · omega
    · have : k < ∏ p ∈ s, p := hklt
      omega
  obtain ⟨p, hpx, hp, hmod⟩ := ha _ hm
  have hps : p ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
  have h1 : k ≡ a p + 1 [MOD p] := hk p hps
  have h2 : k + ∏ p ∈ s, p ≡ k [MOD p] := by
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem (fun p : ℕ => p) hps
    rw [ht]
    exact Nat.add_mul_mod_self_left _ _ _
  have h3 : a p ≡ a p + 1 [MOD p] := (hmod.symm.trans h2).trans h1
  have h4 : p ∣ a p + 1 - a p := (Nat.modEq_iff_dvd' (Nat.le_succ (a p))).mp h3
  have h5 : p ∣ 1 := by simpa using h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h5)

lemma le_maxY (x y : ℕ) (h : Green46.IsCoveredByResidues x y) : (y : ℝ) ≤ Green46.maxY x := by
  unfold Green46.maxY
  exact_mod_cast le_csSup (covered_bdd x) h

lemma cover_step (x C : ℕ) (hC : 1 ≤ C) (y y' z B : ℝ) (a : ℕ → ℕ)
    (hy0 : 0 ≤ y) (hyy : y ≤ y') (hz : z ≤ x)
    (hM : ∀ m : ℕ, (m : ℝ) * x < 2 * y → (m : ℝ) ≤ B ∧ 2 * m ≤ x)
    (hcard : {q : ℕ | q.Prime ∧ x < q ∧ (q : ℝ) ≤ y ∧
        ∀ p : ℕ, p.Prime → (B < (p : ℝ) ∧ (p : ℝ) ≤ z ∨ x < 2 * p ∧ p ≤ x) →
          ¬ q ≡ a p [MOD p]}.ncard +
      {n : ℕ | 0 < n ∧ (n : ℝ) ≤ y' ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ z}.ncard
        ≤ ((Finset.Ioc x (C * x)).filter Nat.Prime).card) :
    Green46.IsCoveredByResidues (C * x) (⌊y⌋₊ - x) := by
  classical
  set Q : Set ℕ := {q : ℕ | q.Prime ∧ x < q ∧ (q : ℝ) ≤ y ∧
        ∀ p : ℕ, p.Prime → (B < (p : ℝ) ∧ (p : ℝ) ≤ z ∨ x < 2 * p ∧ p ≤ x) →
          ¬ q ≡ a p [MOD p]} with hQ
  set R : Set ℕ := {n : ℕ | 0 < n ∧ (n : ℝ) ≤ y' ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ z}
    with hR
  set a' : ℕ → ℕ := fun p =>
    if (B < (p : ℝ) ∧ (p : ℝ) ≤ z) ∨ (x < 2 * p ∧ p ≤ x) then a p else 0 with ha'
  set T : Set ℕ := {n : ℕ | x < n ∧ (n : ℝ) ≤ y ∧
    ∀ p : ℕ, p ≤ x → p.Prime → ¬ n ≡ a' p [MOD p]} with hT
  have hQfin : Q.Finite := (Set.finite_Iic ⌊y⌋₊).subset (fun q hq => Nat.le_floor hq.2.2.1)
  have hRfin : R.Finite := (Set.finite_Iic ⌊y'⌋₊).subset (fun n hn => Nat.le_floor hn.2.1)
  have hzero : ∀ n r : ℕ, n ∈ T → r.Prime → r ∣ n → r ≤ x →
      ¬ ((B < (r : ℝ) ∧ (r : ℝ) ≤ z) ∨ (x < 2 * r ∧ r ≤ x)) → False := by
    intro n r hn hr hrn hrx hcond
    have h1 := hn.2.2 r hrx hr
    have h2 : a' r = 0 := if_neg hcond
    rw [h2] at h1
    exact h1 ((Nat.modEq_zero_iff_dvd).mpr hrn)
  have hTsub : T ⊆ R ∪ Q := by
    intro n hn
    by_cases hsm : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ z
    · left
      exact ⟨by have := hn.1; omega, hn.2.1.trans hyy, hsm⟩
    · right
      push Not at hsm
      obtain ⟨q, hq, hqn, hzq⟩ := hsm
      have hxq : x < 2 * q := by
        by_contra hcon
        push Not at hcon
        refine hzero n q hn hq hqn (by omega) ?_
        rintro (⟨_, h2⟩ | ⟨h1, _⟩)
        · exact absurd h2 (not_le.mpr hzq)
        · omega
      obtain ⟨m, rfl⟩ := hqn
      have hnpos : 0 < q * m := by have := hn.1; omega
      have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hnpos)
      have hmx : (m : ℝ) * x < 2 * y := by
        have h1 : ((q * m : ℕ) : ℝ) ≤ y := hn.2.1
        have h2 : (x : ℝ) < 2 * q := by exact_mod_cast hxq
        have h3 : (0 : ℝ) < m := by exact_mod_cast hmpos
        push_cast at h1
        nlinarith
      obtain ⟨hmB, hm2⟩ := hM m hmx
      have hm1 : m = 1 := by
        by_contra hne
        have hr := Nat.minFac_prime hne
        have hrm := Nat.minFac_le hmpos
        have hrd : m.minFac ∣ q * m := Dvd.dvd.mul_left (Nat.minFac_dvd m) q
        refine hzero _ m.minFac hn hr hrd (by omega) ?_
        rintro (⟨h1, _⟩ | ⟨h1, _⟩)
        · have : (m.minFac : ℝ) ≤ m := by exact_mod_cast hrm
          linarith
        · omega
      subst hm1
      rw [mul_one] at hn ⊢
      refine ⟨hq, hn.1, hn.2.1, ?_⟩
      intro p hp hcond
      have hpx : p ≤ x := by
        rcases hcond with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact_mod_cast h2.trans hz
        · exact h2
      have h7 := hn.2.2 p hpx hp
      rwa [show a' p = a p from if_pos hcond] at h7
  have hTfin : T.Finite := (hRfin.union hQfin).subset hTsub
  set Pr : Finset ℕ := (Finset.Ioc x (C * x)).filter Nat.Prime with hPr
  have hTcard : T.ncard ≤ Pr.card := by
    calc T.ncard ≤ (R ∪ Q).ncard := Set.ncard_le_ncard hTsub (hRfin.union hQfin)
      _ ≤ R.ncard + Q.ncard := Set.ncard_union_le R Q
      _ ≤ Pr.card := by omega
  obtain ⟨f, hfmaps, hfinj⟩ : ∃ f : ℕ → ℕ, T ⊆ f ⁻¹' (Pr : Set ℕ) ∧ Set.InjOn f T := by
    apply hTfin.exists_injOn_of_encard_le
    rw [← hTfin.cast_ncard_eq, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hTcard
  set g : ℕ → ℕ := fun p => if p ≤ x then a' p else
      (if h : ∃ n, n ∈ T ∧ f n = p then Classical.choose h else 0) with hg
  unfold Green46.IsCoveredByResidues
  refine ⟨fun p => g p + (p - 1) * x, ?_⟩
  intro m hm
  rw [Finset.mem_Icc] at hm
  have key : ∃ p ≤ C * x, p.Prime ∧ m + x ≡ g p [MOD p] := by
    by_cases hmT : m + x ∈ T
    · have hp : f (m + x) ∈ Pr := hfmaps hmT
      rw [hPr, Finset.mem_filter, Finset.mem_Ioc] at hp
      refine ⟨f (m + x), hp.1.2, hp.2, ?_⟩
      have hex : ∃ n, n ∈ T ∧ f n = f (m + x) := ⟨m + x, hmT, rfl⟩
      have hgp : g (f (m + x)) = m + x := by
        have hspec := Classical.choose_spec hex
        have hnle : ¬ f (m + x) ≤ x := by omega
        simp only [hg]
        rw [if_neg hnle, dif_pos hex]
        exact hfinj hspec.1 hmT hspec.2
      rw [hgp]
    · have hxn : x < m + x := by omega
      have hny : ((m + x : ℕ) : ℝ) ≤ y := by
        have h8 : m + x ≤ ⌊y⌋₊ := by omega
        exact (Nat.le_floor_iff hy0).mp h8
      have h9 : ¬ ∀ p : ℕ, p ≤ x → p.Prime → ¬ m + x ≡ a' p [MOD p] :=
        fun h => hmT ⟨hxn, hny, h⟩
      push Not at h9
      obtain ⟨p, hpx, hp, hmod⟩ := h9
      refine ⟨p, hpx.trans (Nat.le_mul_of_pos_left x (by omega)), hp, ?_⟩
      rw [show g p = a' p from if_pos hpx]
      exact hmod
  obtain ⟨p, hpC, hp, hmod⟩ := key
  refine ⟨p, hpC, hp, ?_⟩
  have h2 : g p + (p - 1) * x + x = g p + p * x := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.one_le; omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have h3 : m + x ≡ g p + (p - 1) * x + x [MOD p] := by
    rw [h2]
    have h4 : (g p + p * x) % p = g p % p := Nat.add_mul_mod_self_left _ _ _
    exact hmod.trans h4.symm
  exact Nat.ModEq.add_right_cancel' x h3

lemma card_primes_Ioc (x n : ℕ) (h : x ≤ n) :
    ((Finset.Ioc x n).filter Nat.Prime).card + Nat.primeCounting x = Nat.primeCounting n := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_eq_filter_Ioc_zero, Nat.primesLE_eq_filter_Ioc_zero,
    ← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le x) h, Finset.filter_union, add_comm]
  refine (Finset.card_union_of_disjoint ?_).symm
  rw [Finset.disjoint_left]
  intro p hp hp'
  have h1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp').1).1
  omega

lemma exists_many_primes (K : ℝ) : ∃ C : ℕ, 1 ≤ C ∧ ∀ᶠ x : ℕ in atTop,
    K * (x : ℝ) / log (x : ℝ) ≤ (((Finset.Ioc x (C * x)).filter Nat.Prime).card : ℝ) := by
  set C : ℕ := ⌈6 * (|K| + 3)⌉₊ + 1 with hCdef
  have hC6 : 6 * (|K| + 3) ≤ (C : ℝ) := by
    have h := Nat.le_ceil (6 * (|K| + 3))
    rw [hCdef]
    push_cast
    linarith
  have hC1 : 1 ≤ C := by omega
  refine ⟨C, hC1, ?_⟩
  have hup := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  filter_upwards [hup, eventually_ge_atTop (max C 64)] with x hx hxge
  have hxC : C ≤ x := (le_max_left _ _).trans hxge
  have hx64 : 64 ≤ x := (le_max_right _ _).trans hxge
  rw [Nat.floor_natCast] at hx
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx64
  have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC1
  have hCx : (C : ℝ) ≤ x := by exact_mod_cast hxC
  have hlogx : 0 < log (x : ℝ) := Real.log_pos (by linarith)
  set u : ℝ := (x : ℝ) / log (x : ℝ) with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hlogx.le
  have hul : u * log (x : ℝ) = x := div_mul_cancel₀ _ hlogx.ne'
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  -- upper bound for the primes up to x
  have hpix : (Nat.primeCounting x : ℝ) ≤ 2.4 * u := by
    have h1 : (log 4 + 1) * (x : ℝ) / log (x : ℝ) = (log 4 + 1) * u := by
      rw [hu, mul_div_assoc]
    rw [h1] at hx
    have h2 : (log 4 + 1) * u ≤ 2.4 * u := by
      apply mul_le_mul_of_nonneg_right _ hu0
      rw [hlog4]
      linarith
    linarith
  -- lower bound for the primes up to C x
  have hn : ((C * x : ℕ) : ℝ) = (C : ℝ) * x := by push_cast; ring
  have hnge : (64 : ℝ) ≤ (C : ℝ) * x := by nlinarith
  have hlogn : 0 < log ((C : ℝ) * x) := Real.log_pos (by linarith)
  have hlogn2 : log ((C : ℝ) * x) ≤ 2 * log (x : ℝ) := by
    rw [Real.log_mul (by linarith) (by linarith)]
    have := Real.log_le_log (by linarith) hCx
    linarith
  have hlog1 : log ((C : ℝ) * x + 1) ≤ ((C : ℝ) * x + 1) / 4 := by
    have := mul_log_le 4 ((C : ℝ) * x + 1) (by norm_num) (by norm_num; linarith)
    linarith
  have hpin : 0.17 * (C : ℝ) * u ≤ (Nat.primeCounting (C * x) : ℝ) := by
    have h1 := Chebyshev.pi_ge (C * x)
    rw [hn] at h1
    refine le_trans ?_ h1
    rw [le_div_iff₀ hlogn]
    have h2 : 0.17 * (C : ℝ) * u * log ((C : ℝ) * x) ≤ 0.17 * (C : ℝ) * u * (2 * log (x : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogn2 (by positivity)
    have h3 : 0.17 * (C : ℝ) * u * (2 * log (x : ℝ)) = 0.34 * ((C : ℝ) * (u * log (x : ℝ))) := by
      ring
    rw [hul] at h3
    nlinarith
  have hcardeq := card_primes_Ioc x (C * x) (Nat.le_mul_of_pos_left x (by omega))
  have hcardR : (((Finset.Ioc x (C * x)).filter Nat.Prime).card : ℝ) =
      (Nat.primeCounting (C * x) : ℝ) - (Nat.primeCounting x : ℝ) := by
    have : (((Finset.Ioc x (C * x)).filter Nat.Prime).card : ℝ) + (Nat.primeCounting x : ℝ) =
        (Nat.primeCounting (C * x) : ℝ) := by exact_mod_cast hcardeq
    linarith
  rw [hcardR, mul_div_assoc, ← hu]
  have hK : K ≤ |K| := le_abs_self K
  have h5 : (K + 2.4) * u ≤ 0.17 * (C : ℝ) * u := by
    apply mul_le_mul_of_nonneg_right _ hu0
    have : 0 ≤ |K| := abs_nonneg K
    linarith
  linarith

lemma ev_log (B : ℝ) : ∀ᶠ x : ℕ in atTop, B ≤ log (x : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B

lemma ev_log2 (B : ℝ) : ∀ᶠ x : ℕ in atTop, B ≤ log (log (x : ℝ)) :=
  (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop B

lemma ev_log3 (B : ℝ) : ∀ᶠ x : ℕ in atTop, B ≤ log (log (log (x : ℝ))) :=
  (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually_ge_atTop B

lemma f_compare (x X D : ℝ) (hD : 1 ≤ D) (hxX : x ≤ X) (hXD : X ≤ D * x) (hx0 : 0 < x)
    (hL : 2 ≤ log x) (hLD : log D ≤ log x) (hL3 : 1 ≤ log (log (log x))) :
    0 ≤ X * log X * log (log (log X)) / log (log X) ∧
    X * log X * log (log (log X)) / log (log X) ≤
      4 * D * (x * log x * log (log (log x)) / log (log x)) := by
  have hX0 : 0 < X := hx0.trans_le hxX
  have h1 : log x ≤ log X := Real.log_le_log hx0 hxX
  have h2 : log X ≤ 2 * log x := by
    calc log X ≤ log (D * x) := Real.log_le_log hX0 hXD
      _ = log D + log x := Real.log_mul (by linarith) hx0.ne'
      _ ≤ 2 * log x := by linarith
  have hlx : 0 < log x := by linarith
  have h3 : log (log x) ≤ log (log X) := Real.log_le_log hlx h1
  have hl2 : log 2 ≤ log (log x) := Real.log_le_log (by norm_num) hL
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have h4 : log (log X) ≤ 2 * log (log x) := by
    calc log (log X) ≤ log (2 * log x) := Real.log_le_log (by linarith) h2
      _ = log 2 + log (log x) := Real.log_mul (by norm_num) hlx.ne'
      _ ≤ 2 * log (log x) := by linarith
  have hl2x : 0 < log (log x) := by linarith
  have h5 : log (log (log x)) ≤ log (log (log X)) := Real.log_le_log hl2x h3
  have hlog2' : log (2 : ℝ) ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have h6 : log (log (log X)) ≤ 2 * log (log (log x)) := by
    calc log (log (log X)) ≤ log (2 * log (log x)) := Real.log_le_log (by linarith) h4
      _ = log 2 + log (log (log x)) := Real.log_mul (by norm_num) hl2x.ne'
      _ ≤ 2 * log (log (log x)) := by linarith
  have hl2X : 0 < log (log X) := by linarith
  have hnum : 0 ≤ X * log X * log (log (log X)) :=
    mul_nonneg (mul_nonneg hX0.le (by linarith)) (by linarith)
  refine ⟨div_nonneg hnum hl2X.le, ?_⟩
  rw [div_le_iff₀ hl2X]
  have a1 : X * log X ≤ (D * x) * (2 * log x) :=
    mul_le_mul hXD h2 (by linarith) (mul_nonneg (by linarith) hx0.le)
  have a2 : X * log X * log (log (log X)) ≤ (D * x) * (2 * log x) * (2 * log (log (log x))) :=
    mul_le_mul a1 h6 (by linarith) (mul_nonneg (mul_nonneg (by linarith) hx0.le) (by linarith))
  have a3 : (D * x) * (2 * log x) * (2 * log (log (log x))) =
      4 * D * (x * log x * log (log (log x)) / log (log x)) * log (log x) := by
    field_simp
    ring
  have a4 : 0 ≤ 4 * D * (x * log x * log (log (log x)) / log (log x)) :=
    mul_nonneg (by linarith)
      (div_nonneg (mul_nonneg (mul_nonneg hx0.le hlx.le) (by linarith)) hl2x.le)
  have a5 := mul_le_mul_of_nonneg_left h3 a4
  linarith

theorem main : H1 → H2 → type_of% @Green46.green_46.variants.lower := by
  rintro ⟨c, hc, K, hH1⟩ hH2
  obtain ⟨C, hC, hPr⟩ := exists_many_primes (K + 1)
  have hcov : ∀ᶠ x : ℕ in atTop, Green46.IsCoveredByResidues (C * x)
      (⌊c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ))⌋₊ - x) := by
    filter_upwards [hH1, hH2, hPr, ev_log 2, ev_log2 (max 1 ((2 * c) ^ 2)), ev_log3 0,
      eventually_ge_atTop 100] with x h1 h2 h3 hL hL2 hL3 hx100
    obtain ⟨a, ha⟩ := h1
    have hxR : (100 : ℝ) ≤ x := by exact_mod_cast hx100
    have hxpos : (0 : ℝ) < x := by linarith
    have hL2pos : 0 < log (log (x : ℝ)) := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hL2)
    have hcL3 : c * log (log (log (x : ℝ))) ≤ log (log (x : ℝ)) :=
      mul_log_le c _ hc ((le_max_right _ _).trans hL2)
    have hxL : 0 ≤ (x : ℝ) * log (x : ℝ) := mul_nonneg hxpos.le (by linarith)
    have hy : c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ)) ≤
        (x : ℝ) * log (x : ℝ) := by
      rw [div_le_iff₀ hL2pos]
      have := mul_le_mul_of_nonneg_left hcL3 hxL
      nlinarith
    have hy0 : 0 ≤ c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ)) :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc.le hxpos.le) (by linarith)) hL3)
        hL2pos.le
    have hL3le : log (log (log (x : ℝ))) ≤ 4 * log (log (x : ℝ)) := by
      have := Real.log_le_sub_one_of_pos hL2pos
      linarith
    have hz : (x : ℝ) ^ (log (log (log (x : ℝ))) / (4 * log (log (x : ℝ)))) ≤ x := by
      calc (x : ℝ) ^ (log (log (log (x : ℝ))) / (4 * log (log (x : ℝ))))
          ≤ (x : ℝ) ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by linarith)
            rw [div_le_one (by linarith)]
            exact hL3le
        _ = x := Real.rpow_one _
    have h4log : 4 * log (x : ℝ) < x := by
      have := mul_log_le 5 (x : ℝ) (by norm_num) (by norm_num; linarith)
      linarith
    have hM : ∀ m : ℕ, (m : ℝ) * x <
        2 * (c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ))) →
        (m : ℝ) ≤ log (x : ℝ) ^ 20 ∧ 2 * m ≤ x := by
      intro m hm
      have hm2 : (m : ℝ) < 2 * log (x : ℝ) := by
        have h5 : (m : ℝ) * x < 2 * log (x : ℝ) * x := by nlinarith
        exact lt_of_mul_lt_mul_right h5 hxpos.le
      constructor
      · have h6 : log (x : ℝ) ^ 2 ≤ log (x : ℝ) ^ 20 :=
          pow_le_pow_right₀ (by linarith) (by norm_num)
        nlinarith
      · have h7 : (2 * m : ℝ) < x := by linarith
        exact_mod_cast h7.le
    refine cover_step x C hC _ _ _ _ a hy0 hy hz hM ?_
    have h8 : ((K + 1) * (x : ℝ) / log (x : ℝ)) =
        K * (x : ℝ) / log (x : ℝ) + (x : ℝ) / log (x : ℝ) := by ring
    rw [h8] at h3
    have h9 := (add_le_add ha h2).trans h3
    exact_mod_cast h9
  have hfin : ∀ᶠ x : ℕ in atTop, Green46.IsCoveredByResidues (C * x)
      (⌊c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ))⌋₊ - x) ∧
      1 ≤ x ∧ 2 ≤ log (x : ℝ) ∧ log (2 * (C : ℝ)) ≤ log (x : ℝ) ∧
      1 ≤ log (log (log (x : ℝ))) ∧ 4 / c * log (log (x : ℝ)) ≤ log (x : ℝ) := by
    filter_upwards [hcov, eventually_ge_atTop 1,
      ev_log (max 2 (max (log (2 * (C : ℝ))) ((2 * (4 / c)) ^ 2))), ev_log3 1]
      with x h1 h2 h3 h4
    refine ⟨h1, h2, (le_max_left _ _).trans h3,
      ((le_max_left _ _).trans (le_max_right _ _)).trans h3, h4, ?_⟩
    exact mul_log_le (4 / c) _ (by positivity)
      (((le_max_right _ _).trans (le_max_right _ _)).trans h3)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfin
  refine Asymptotics.IsBigO.of_bound (16 * C / c) ?_
  filter_upwards [eventually_ge_atTop (N * C)] with X hX
  have hxN : N ≤ X / C := (Nat.le_div_iff_mul_le hC).mpr hX
  obtain ⟨hcv, hx1, hL, hLD, hL3, hLL2⟩ := hN (X / C) hxN
  set x : ℕ := X / C with hxdef
  have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hmax := le_maxY _ _ (covered_mono hcv (Nat.mul_div_le X C))
  have hXle : X ≤ 2 * C * x := by
    have h1 : X < C * (X / C + 1) := Nat.lt_mul_div_succ X hC
    have h2 : C ≤ C * x := Nat.le_mul_of_pos_right C hx1
    rw [← hxdef, Nat.mul_succ] at h1
    nlinarith
  have hXleR : (X : ℝ) ≤ 2 * C * x := by exact_mod_cast hXle
  have hxX : (x : ℝ) ≤ X := by
    have : x ≤ X := Nat.div_le_self X C
    exact_mod_cast this
  obtain ⟨hf0, hfle⟩ := f_compare (x : ℝ) (X : ℝ) (2 * C) (by linarith) hxX hXleR (by linarith)
    hL hLD hL3
  have hlx : 0 < log (x : ℝ) := by linarith
  have hl2x : 0 < log (log (x : ℝ)) := by
    have h1 : log (2 : ℝ) ≤ log (log (x : ℝ)) := Real.log_le_log (by norm_num) hL
    have h2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
    linarith
  -- c f(x) is at least 4 x
  have hcf : 4 * (x : ℝ) ≤
      c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ)) := by
    rw [le_div_iff₀ hl2x]
    have h1 : 4 * log (log (x : ℝ)) ≤ c * log (x : ℝ) := by
      have := mul_le_mul_of_nonneg_left hLL2 hc.le
      rw [← mul_assoc, mul_div_cancel₀ _ hc.ne'] at this
      exact this
    have h2 : c * (x : ℝ) * log (x : ℝ) ≤ c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) :=
      le_mul_of_one_le_right (by positivity) hL3
    nlinarith
  have hfloor : c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ)) - 1 - x ≤
      Green46.maxY X := by
    refine le_trans ?_ hmax
    have h1 := Nat.lt_floor_add_one
      (c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ)))
    have h2 : ⌊c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ))⌋₊ ≤
        ⌊c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ))⌋₊ - x + x := by
      omega
    have h3 : ((⌊c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ))⌋₊ : ℕ) : ℝ)
        ≤ ((⌊c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ))⌋₊ - x : ℕ) : ℝ)
          + x := by exact_mod_cast h2
    linarith
  have hmaxnn : 0 ≤ Green46.maxY X := by
    unfold Green46.maxY
    exact Nat.cast_nonneg _
  have hbl : Green46.bestLower X =
      (X : ℝ) * log (X : ℝ) * log (log (log (X : ℝ))) / log (log (X : ℝ)) := rfl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hmaxnn, hbl, abs_of_nonneg hf0]
  -- with F = f(x): f(X) ≤ 8 C F and c F - 1 - x ≤ maxY X and 4 x ≤ c F
  have hF : c * (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ)) =
      c * ((x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ))) := by ring
  rw [hF] at hcf hfloor
  set F : ℝ := (x : ℝ) * log (x : ℝ) * log (log (log (x : ℝ))) / log (log (x : ℝ)) with hFdef
  have h10 : c * F / 2 ≤ Green46.maxY X := by linarith
  have h11 : 4 * (2 * (C : ℝ)) * F ≤ 16 * C / c * Green46.maxY X := by
    have h12 : 16 * (C : ℝ) / c * (c * F / 2) ≤ 16 * C / c * Green46.maxY X :=
      mul_le_mul_of_nonneg_left h10 (by positivity)
    have h13 : 16 * (C : ℝ) / c * (c * F / 2) = 4 * (2 * (C : ℝ)) * F := by
      field_simp
      ring
    linarith
  linarith

end OMA.R_Green46_green_46_variants_lower_R1
