import FormalConjectures.ErdosProblems.«32»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # A lower bound for additive complements to the primes -/
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/32.lean:99 (declaration Erdos32.erdos_32.variants.ruzsa)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)

open Filter Topology

namespace OMA32R

/-- One prime per survivor: if there are at least as many moduli as survivors, every survivor
gets its own modulus. -/
lemma one_by_one (S : Finset ℕ) : ∀ T : Finset ℕ, S.card ≤ T.card →
    ∃ a : ℕ → ℕ, ∀ j ∈ S, ∃ p ∈ T, j % p = a p := by
  classical
  induction S using Finset.induction_on with
  | empty => intro T _; exact ⟨fun _ => 0, by simp⟩
  | insert j S' hj ih =>
    intro T hT
    rw [Finset.card_insert_of_notMem hj] at hT
    obtain ⟨p, hp⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := ih (T.erase p) (by rw [Finset.card_erase_of_mem hp]; omega)
    refine ⟨Function.update a p (j % p), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with h | hi'
    · subst h
      exact ⟨p, hp, by simp⟩
    · obtain ⟨p', hp', h'⟩ := ha i hi'
      refine ⟨p', Finset.mem_of_mem_erase hp', ?_⟩
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hp')]
      exact h'

/-- Greedy stage: each modulus removes at least its fair share of the survivors. -/
lemma greedy (S : Finset ℕ) (T : Finset ℕ) (hT : ∀ p ∈ T, 0 < p) :
    ∃ a : ℕ → ℕ, ((S.filter (fun j => ∀ p ∈ T, j % p ≠ a p)).card : ℝ) ≤
      (∏ p ∈ T, (1 - 1 / (p : ℝ))) * S.card := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert q T' hq ih =>
    obtain ⟨a, ha⟩ := ih (fun p hp => hT p (Finset.mem_insert_of_mem hp))
    have hqpos : 0 < q := hT q (Finset.mem_insert_self q T')
    have hq0 : (0:ℝ) < q := by exact_mod_cast hqpos
    obtain ⟨r, hr, hfib⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      (s := S.filter (fun j => ∀ p ∈ T', j % p ≠ a p)) (t := Finset.range q)
      (f := fun j => j % q)
      (b := ((S.filter (fun j => ∀ p ∈ T', j % p ≠ a p)).card : ℝ) / q)
      (fun j _ => Finset.mem_range.mpr (Nat.mod_lt j hqpos))
      ⟨0, Finset.mem_range.mpr hqpos⟩
      (by rw [Finset.card_range, nsmul_eq_mul]; exact le_of_eq (by field_simp))
    refine ⟨Function.update a q r, ?_⟩
    obtain ⟨S1, hS1⟩ : ∃ S1, S1 = S.filter (fun j => ∀ p ∈ T', j % p ≠ a p) := ⟨_, rfl⟩
    obtain ⟨F, hF⟩ : ∃ F, F = S1.filter (fun j => j % q = r) := ⟨_, rfl⟩
    obtain ⟨S2, hS2⟩ : ∃ S2, S2 = S.filter
      (fun j => ∀ p ∈ insert q T', j % p ≠ Function.update a q r p) := ⟨_, rfl⟩
    rw [← hS1] at ha hfib
    have hfib' : (S1.card : ℝ) / q ≤ F.card := by rw [hF]; exact hfib
    rw [← hS2]
    have hsub : S2 ∪ F ⊆ S1 := by
      intro j hj
      rcases Finset.mem_union.mp hj with h | h
      · rw [hS2] at h
        obtain ⟨hjS, hjP⟩ := Finset.mem_filter.mp h
        rw [hS1]
        refine Finset.mem_filter.mpr ⟨hjS, fun p hp => ?_⟩
        have h3 := hjP p (Finset.mem_insert_of_mem hp)
        have hne : p ≠ q := by rintro rfl; exact hq hp
        rwa [Function.update_of_ne hne] at h3
      · rw [hF] at h
        exact (Finset.mem_filter.mp h).1
    have hdisj : Disjoint S2 F := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      rw [hS2] at h1
      rw [hF] at h2
      have h3 := (Finset.mem_filter.mp h1).2 q (Finset.mem_insert_self q T')
      rw [Function.update_self] at h3
      exact h3 (Finset.mem_filter.mp h2).2
    have hcard : S2.card + F.card ≤ S1.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hsub
    have hcardR : (S2.card : ℝ) + F.card ≤ S1.card := by exact_mod_cast hcard
    have h1 : (S2.card : ℝ) ≤ (1 - 1 / q) * S1.card := by
      have e : (1 - 1 / (q:ℝ)) * S1.card = S1.card - S1.card / q := by ring
      rw [e]; linarith
    have hfactor : 0 ≤ (1 - 1 / (q : ℝ)) := by
      have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
      exact sub_nonneg.mpr ((div_le_iff₀ hq0).mpr (by simpa using hqone))
    rw [Finset.prod_insert hq, mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_left ha hfactor)

/-- A residue cover of the truncated complement forces a large CRT modulus. -/
lemma cover_modulus_gt (A : Set ℕ) [DecidablePred (· ∈ A)] (N K : ℕ)
    (hA : ∀ n ≥ K, ∃ p, p.Prime ∧ ∃ a ∈ A, n = p + a)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (b : ℕ → ℕ)
    (hcover : ∀ a ∈ (Finset.Icc 0 N).filter (· ∈ A), ∃ p ∈ T, a % p = b p) :
    N < (K + ((Finset.Icc 0 N).filter (· ∈ A)).card + 1) * ∏ p ∈ T, p := by
  classical
  by_contra! hN
  let S := (Finset.Icc 0 N).filter (· ∈ A)
  let M := ∏ p ∈ T, p
  have hM : 0 < M := Finset.prod_pos fun p hp => (hT p hp).pos
  have pp : Set.Pairwise (T : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (hT p hp) (hT q hq)).mpr hne
  obtain ⟨r, hr⟩ := Nat.chineseRemainderOfFinset b id T (fun p hp => (hT p hp).ne_zero) pp
  choose q hq hqa using hcover
  let bad := S.attach.image (fun a => a.val + q a.val a.property)
  let x := fun i : ℕ => r % M + (K + i) * M
  have hinj : Function.Injective x := by
    intro i j hij
    have hmul := Nat.add_left_cancel hij
    have := (mul_left_inj' (Nat.ne_of_gt hM)).mp hmul
    omega
  have hbad : bad.card ≤ S.card :=
    Finset.card_image_le.trans_eq Finset.card_attach
  have hcards : bad.card < ((Finset.range (S.card + 1)).image x).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    omega
  obtain ⟨n, hn, hn_bad⟩ := Finset.exists_mem_notMem_of_card_lt_card hcards
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  have hKn : K ≤ x i := by
    have : K + i ≤ (K + i) * M := Nat.le_mul_of_pos_right _ hM
    dsimp [x]
    omega
  have hxN : x i ≤ N := by
    have hi' : K + i + 1 ≤ K + S.card + 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hlt : x i < (K + i + 1) * M := by
      have := Nat.mod_lt r hM
      dsimp [x]
      rw [Nat.add_mul (K + i) 1 M, one_mul]
      omega
    exact (hlt.le.trans (Nat.mul_le_mul_right M hi')).trans hN
  obtain ⟨p, hp, a, ha, hpa⟩ := hA (x i) hKn
  have haS : a ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, ha⟩
  have hqM : q a haS ∣ M := Finset.dvd_prod_of_mem id (hq a haS)
  have hxr : x i ≡ r [MOD M] := by
    exact (Nat.modEq_add_mul_modulus_iff.mpr (Nat.mod_modEq r M).symm).symm
  have hba : b (q a haS) ≡ a [MOD q a haS] := by
    rw [← hqa a haS]
    exact Nat.mod_modEq _ _
  have hxa : x i ≡ a [MOD q a haS] :=
    ((hxr.of_dvd hqM).trans (hr (q a haS) (hq a haS))).trans hba
  rw [hpa, add_comm] at hxa
  have hd : q a haS ∣ p := Nat.modEq_zero_iff_dvd.mp
    ((Nat.ModEq.add_left_cancel' a) (show a + p ≡ a + 0 [MOD q a haS] by simpa using hxa))
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact (hT _ (hq a haS)).ne_one h
  · apply hn_bad
    exact Finset.mem_image.mpr ⟨⟨a, haS⟩, Finset.mem_attach _ _, by simpa [h, add_comm] using hpa.symm⟩

/-- The fraction left by the greedy sieve with all primes up to y. -/
noncomputable def primeSurvival (y : ℕ) : ℝ :=
  ∏ p ∈ y.primesLE, (1 - 1 / (p : ℝ))

lemma primeSurvival_nonneg (y : ℕ) : 0 ≤ primeSurvival y := by
  apply Finset.prod_nonneg
  intro p hp
  have h : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
  exact sub_nonneg.mpr ((div_le_iff₀ (by linarith : (0 : ℝ) < p)).mpr (by simpa using h))

/-- The two stages of the sieve bound the logarithm of N by their logarithmic modulus cost. -/
lemma sieve_log_bound (A : Set ℕ) [DecidablePred (· ∈ A)] {N K : ℕ} (hN : 0 < N)
    (hA : ∀ n ≥ K, ∃ p, p.Prime ∧ ∃ a ∈ A, n = p + a) (y z : ℕ)
    (hs : primeSurvival y * ((Finset.Icc 0 N).filter (· ∈ A)).card ≤
      ((z.primesLE \ y.primesLE).card : ℝ)) :
    Real.log N < Real.log (K + ((Finset.Icc 0 N).filter (· ∈ A)).card + 1 : ℕ) +
      Real.log 4 * y + primeSurvival y * ((Finset.Icc 0 N).filter (· ∈ A)).card * Real.log z := by
  classical
  let S := (Finset.Icc 0 N).filter (· ∈ A)
  let P := y.primesLE
  let Q := z.primesLE \ P
  obtain ⟨b, hb⟩ := greedy S P (fun p hp => (Nat.prime_of_mem_primesLE hp).pos)
  let R := S.filter (fun j => ∀ p ∈ P, j % p ≠ b p)
  change (R.card : ℝ) ≤ primeSurvival y * S.card at hb
  have hs' : R.card ≤ Q.card := by exact_mod_cast hb.trans hs
  obtain ⟨U, hU, hUc⟩ := Finset.exists_subset_card_eq hs'
  obtain ⟨d, hd⟩ := one_by_one R U hUc.ge
  have hUprime : ∀ p ∈ U, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp (hU hp)).1
  have hPU : Disjoint P U := by
    rw [Finset.disjoint_left]
    exact fun p hp hu => (Finset.mem_sdiff.mp (hU hu)).2 hp
  have hprime : ∀ p ∈ P ∪ U, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primesLE hp
    · exact hUprime p hp
  let f := fun p => if p ∈ P then b p else d p
  have hcov : ∀ a ∈ S, ∃ p ∈ P ∪ U, a % p = f p := by
    intro a ha
    by_cases h : ∃ p ∈ P, a % p = b p
    · obtain ⟨p, hp, heq⟩ := h
      exact ⟨p, Finset.mem_union_left _ hp, by simpa [f, hp] using heq⟩
    · have har : a ∈ R := Finset.mem_filter.mpr ⟨ha, fun p hp heq => h ⟨p, hp, heq⟩⟩
      obtain ⟨p, hp, heq⟩ := hd a har
      have hp' : p ∉ P := (Finset.mem_sdiff.mp (hU hp)).2
      exact ⟨p, Finset.mem_union_right _ hp, by simpa [f, hp'] using heq⟩
  have hlt := cover_modulus_gt A N K hA (P ∪ U) hprime f hcov
  change N < (K + S.card + 1) * ∏ p ∈ P ∪ U, p at hlt
  rw [Finset.prod_union hPU, ← primorial_eq_prod_primesLE y, ← mul_assoc] at hlt
  have hprimorial : Real.log (primorial y : ℕ) ≤ Real.log 4 * y := by
    have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg y)
    simpa [Chebyshev.theta_eq_log_primorial] using h
  have hUlog : Real.log ((∏ p ∈ U, p : ℕ) : ℝ) ≤ (R.card : ℝ) * Real.log z := by
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hUprime p hp).ne_zero)]
    calc
      _ ≤ ∑ _p ∈ U, Real.log z := Finset.sum_le_sum fun p hp =>
        Real.log_le_log (by exact_mod_cast (hUprime p hp).pos)
          (by exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp (hU hp)).1).1)
      _ = _ := by simp [hUc, nsmul_eq_mul]
  have hUpos : 0 < (∏ p ∈ U, p : ℕ) := Finset.prod_pos fun p hp => (hUprime p hp).pos
  have hltR : (N : ℝ) < ((K + S.card + 1 : ℕ) : ℝ) *
      (primorial y : ℝ) * ((∏ p ∈ U, p : ℕ) : ℝ) := by exact_mod_cast hlt
  have hlog := Real.log_lt_log (by exact_mod_cast hN) hltR
  have hbase : ((K + S.card + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show K + S.card + 1 ≠ 0 by omega)
  have hprim : (primorial y : ℝ) ≠ 0 := by exact_mod_cast (primorial_pos y).ne'
  rw [Real.log_mul (mul_ne_zero hbase hprim) (by exact_mod_cast hUpos.ne'),
    Real.log_mul hbase hprim] at hlog
  have hcost := mul_le_mul_of_nonneg_right hb (Real.log_natCast_nonneg z)
  change Real.log N < Real.log (K + S.card + 1 : ℕ) + _ + primeSurvival y * S.card * _
  linarith

open scoped Asymptotics in
lemma eventually_theta_ge_half : ∀ᶠ x : ℝ in atTop, x / 2 ≤ Chebyshev.theta x := by
  have hsqrt : Real.sqrt =o[atTop] (id : ℝ → ℝ) := by
    refine Asymptotics.isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [eventually_ge_atTop ((1 / ε) ^ 2)] with x hx
    have hx0 : 0 ≤ x := (sq_nonneg _).trans hx
    have hh : 1 / ε ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
    have he : 1 ≤ ε * Real.sqrt x := by
      rw [div_le_iff₀ hε] at hh
      simpa [mul_comm] using hh
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0,
      abs_of_nonneg (Real.sqrt_nonneg x)]
    calc
      Real.sqrt x = 1 * Real.sqrt x := (one_mul _).symm
      _ ≤ (ε * Real.sqrt x) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg x)
      _ = ε * x := by rw [mul_assoc, Real.mul_self_sqrt hx0]
  have herr := (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt).bound
    (show (0 : ℝ) < 1 / 16 by norm_num)
  have hlog := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 32 by norm_num)
  filter_upwards [herr, hlog, eventually_ge_atTop (32 : ℝ)] with x he hl hx
  have hx0 : 0 ≤ x := by linarith
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] at he hl
  have hl' := (le_abs_self (Real.log x)).trans hl
  have hlogadd : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hpsi := Chebyshev.psi_ge' hx0
  have hdiff := (le_abs_self (Chebyshev.psi x - Chebyshev.theta x)).trans he
  have hprod := mul_le_mul_of_nonneg_left
    (show (2 / 3 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) (show 0 ≤ x - 1 by linarith)
  linarith [Real.log_two_lt_d9]

private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have heq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

/-- For large x, the primes in (δx, 8x] can pay a logarithmic cost of at least x. -/
lemma eventually_prime_cutoff_supply {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ x : ℝ in atTop,
      x ≤ (((⌊8 * x⌋₊ : ℕ).primesLE \ (⌊δ * x⌋₊ : ℕ).primesLE).card : ℝ) *
        Real.log (8 * x) := by
  have h8 : Tendsto (fun x : ℝ => 8 * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [h8.eventually eventually_theta_ge_half, eventually_ge_atTop (1 : ℝ)]
    with x hθ hx
  let y := ⌊δ * x⌋₊
  let z := ⌊8 * x⌋₊
  have hδx : 0 ≤ δ * x := mul_nonneg hδ (by linarith)
  have hyz : y ≤ z := Nat.floor_mono (by nlinarith)
  have hθy := Chebyshev.theta_le_log4_mul_x hδx
  have hθy' : Chebyshev.theta (δ * x) ≤ 2 * x := calc
    _ ≤ Real.log 4 * (δ * x) := hθy
    _ ≤ 2 * (δ * x) := mul_le_mul_of_nonneg_right log_four_le_two hδx
    _ ≤ 2 * x := by nlinarith
  have hsum :
      Chebyshev.theta (8 * x) - Chebyshev.theta (δ * x) =
        ∑ p ∈ z.primesLE \ y.primesLE, Real.log (p : ℝ) := by
    rw [Chebyshev.theta_eq_theta_coe_floor (8 * x),
      Chebyshev.theta_eq_theta_coe_floor (δ * x)]
    change Chebyshev.theta z - Chebyshev.theta y = _
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
      Finset.sum_sdiff_eq_sub (Nat.primesLE_mono hyz)]
  have hc :
      (∑ p ∈ z.primesLE \ y.primesLE, Real.log (p : ℝ)) ≤
        ((z.primesLE \ y.primesLE).card : ℝ) * Real.log (8 * x) := calc
    _ ≤ ∑ _p ∈ z.primesLE \ y.primesLE, Real.log (8 * x) := by
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨hpz, hpp⟩ := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
      exact Real.log_le_log (by exact_mod_cast hpp.pos)
        ((by exact_mod_cast hpz : (p : ℝ) ≤ z).trans (Nat.floor_le (by positivity)))
    _ = _ := by simp [nsmul_eq_mul]
  change x ≤ ((z.primesLE \ y.primesLE).card : ℝ) * Real.log (8 * x)
  linarith

/- `log n!` as a sum over the primes `≤ n` (Legendre). -/
lemma log_factorial_eq_sum_primesLE (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((n.factorial).factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    rw [Nat.mem_primesLE]
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact ⟨(hpp.dvd_factorial).mp (Nat.dvd_of_mem_primeFactors hp), hpp⟩
  · intro p _ hp
    rw [Finsupp.notMem_support_iff] at hp
    simp [hp]

/- `⌊n/p⌋ ≤ v_p(n!)`. -/
lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (b := n + 1) (Nat.lt_succ_of_le (Nat.log_le_self p n))]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : 1 ∈ Finset.Ico 1 (n + 1) := by
      rw [Finset.mem_Ico]; omega
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) h1
    simpa using this

/- Mertens' first theorem, upper bound, explicit constant `log 4`. -/
theorem mertens_first_upper_explicit (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log
    · exact_mod_cast Nat.factorial_pos n
    · exact_mod_cast Nat.factorial_le_pow n
  have h2 : ∑ p ∈ Nat.primesLE n, ((n : ℝ) / p - 1) * Real.log p
      ≤ Real.log (n.factorial : ℝ) := by
    rw [log_factorial_eq_sum_primesLE]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have h3 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial).factorization p : ℝ) := by
      exact_mod_cast div_le_factorization_factorial hpp n
    have h4 : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by
      exact_mod_cast Nat.lt_div_mul_add hpp.pos
    have h5 : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hp0]; linarith
    linarith
  have h6 : ∑ p ∈ Nat.primesLE n, ((n : ℝ) / p - 1) * Real.log p
      = n * ∑ p ∈ Nat.primesLE n, Real.log p / p - ∑ p ∈ Nat.primesLE n, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have h7 : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have h8 : n * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left h8 hn0

lemma mertens_log_succ_le (x : ℝ) (hx : 0 < x) : Real.log (x + 1) ≤ Real.log x + 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at h
  have h' : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

lemma mertens_tail_step (x : ℝ) (hx : 1 < x) :
    Real.log x / (x * (x - 1)) + (Real.log (x + 1) + 1) / x ≤ (Real.log x + 1) / (x - 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h1 : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have := mertens_log_succ_le x hx0; linarith
  have h2 : (x - 1) * (Real.log (x + 1) - Real.log x) ≤ (x - 1) * (1 / x) :=
    mul_le_mul_of_nonneg_left h1 hx1.le
  have h3 : (x - 1) * (1 / x) ≤ 1 := by
    rw [mul_one_div, div_le_one hx0]; linarith
  have key : (Real.log x + 1) / (x - 1) - Real.log x / (x * (x - 1))
      - (Real.log (x + 1) + 1) / x
      = (1 - (x - 1) * (Real.log (x + 1) - Real.log x)) / (x * (x - 1)) := by
    field_simp
    ring
  have h4 : 0 ≤ (1 - (x - 1) * (Real.log (x + 1) - Real.log x)) / (x * (x - 1)) := by
    apply div_nonneg
    · linarith
    · positivity
  linarith

/- `∑_{m=2}^{n+1} log m / (m (m-1)) ≤ log 2 + 1` (telescoping majorant). -/
lemma mertens_tail_bound (n : ℕ) :
    ∑ m ∈ Finset.Icc 2 (n + 1), Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))
      + (Real.log ((n : ℝ) + 2) + 1) / ((n : ℝ) + 1) ≤ Real.log 2 + 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h := mertens_tail_step ((k : ℝ) + 2) (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    have e0 : ((k + 1 + 1 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    have e1 : (k : ℝ) + 2 - 1 = k + 1 := by ring
    have e2 : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 2 + 1 := by push_cast; ring
    have e3 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [e0, e2, e3]
    rw [e1] at h ⊢
    linarith

/- Mertens' first theorem, lower bound, explicit constant `2 + log 2`. -/
theorem mertens_first_lower_explicit (n : ℕ) (hn : 1 ≤ n) :
    Real.log n - (2 + Real.log 2) ≤ ∑ p ∈ Nat.primesLE n, Real.log p / p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : n * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn0.le n
    rw [div_le_iff₀ hf] at h
    have h' := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h'
    linarith
  have h2 : Real.log (n.factorial : ℝ)
      ≤ ∑ p ∈ Nat.primesLE n, (n : ℝ) / ((p : ℝ) - 1) * Real.log p := by
    rw [log_factorial_eq_sum_primesLE]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    apply mul_le_mul_of_nonneg_right _ hlog
    have h3 : ((n.factorial).factorization p : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp n
    have h4 : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_sub hpp.one_le, Nat.cast_one] at h4
    linarith
  have h5 : ∑ p ∈ Nat.primesLE n, (n : ℝ) / ((p : ℝ) - 1) * Real.log p
      = n * ∑ p ∈ Nat.primesLE n, Real.log p / p
        + n * ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      linarith
    field_simp
    ring
  have h6 : ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ Real.log 2 + 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hsub : Nat.primesLE (k + 1) ⊆ Finset.Icc 2 (k + 1) := by
      rw [Nat.primesLE_eq_filter_Icc_two]; exact Finset.filter_subset _ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun m : ℕ => Real.log (m : ℝ) / ((m : ℝ) * ((m : ℝ) - 1))) (fun m hm _ => by
        rw [Finset.mem_Icc] at hm
        have h2m : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
        apply div_nonneg (Real.log_nonneg (by linarith))
        apply mul_nonneg <;> linarith)
    have hb := mertens_tail_bound k
    have hpos : 0 ≤ (Real.log ((k : ℝ) + 2) + 1) / ((k : ℝ) + 1) := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      apply div_nonneg
      · have := Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 2 by linarith)
        linarith
      · linarith
    linarith
  have h7 : n * (Real.log n - (2 + Real.log 2))
      ≤ n * ∑ p ∈ Nat.primesLE n, Real.log p / p := by
    have := mul_le_mul_of_nonneg_left h6 hn0.le
    nlinarith
  exact le_of_mul_le_mul_left h7 hn0

/- Mertens' first theorem with an explicit constant. -/
theorem mertens_first_explicit (n : ℕ) (hn : 1 ≤ n) :
    |∑ p ∈ Nat.primesLE n, Real.log p / p - Real.log n| ≤ 2 + Real.log 2 := by
  rw [abs_le]
  have h1 := mertens_first_upper_explicit n hn
  have h2 := mertens_first_lower_explicit n hn
  have h3 : Real.log 4 ≤ 2 + Real.log 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  constructor <;> linarith

lemma primesLE_sum_succ (f : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ Nat.primesLE (n + 1), f p
      = ∑ p ∈ Nat.primesLE n, f p + if (n + 1).Prime then f (n + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert (Nat.notMem_primesLE n)]; ring
  · simp

/- Summation by parts: `∑_{p ≤ n} 1/p = S(n)/log n + ∑_{2 ≤ m < n} S(m) (1/log m - 1/log (m+1))`
   where `S(m) = ∑_{p ≤ m} log p / p`. -/
lemma mertens_sum_by_parts (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ Nat.primesLE n, (1 : ℝ) / p
      = (∑ p ∈ Nat.primesLE n, Real.log p / p) * (1 / Real.log (n : ℝ))
        + ∑ m ∈ Finset.Ico 2 n, (∑ p ∈ Nat.primesLE m, Real.log p / p)
            * (1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h2 : Nat.primesLE 2 = {2} := by decide
    have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    simp [h2]
    field_simp
  | succ n hn ih =>
    rw [primesLE_sum_succ, primesLE_sum_succ, Finset.sum_Ico_succ_top hn, ih]
    have hx : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hl : Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 := by
      have h1 : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n + 1)
      exact (Real.log_pos h1).ne'
    split_ifs with hp
    · have e : (∑ p ∈ Nat.primesLE n, Real.log p / p
            + Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) * (1 / Real.log ((n + 1 : ℕ) : ℝ))
          = (∑ p ∈ Nat.primesLE n, Real.log p / p) * (1 / Real.log ((n + 1 : ℕ) : ℝ))
            + 1 / ((n + 1 : ℕ) : ℝ) := by
        field_simp
      rw [e]; ring
    · ring

lemma mertens_loglog_step (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ u + 1 / 2) :
    u * (1 / u - 1 / v) ≤ Real.log v - Real.log u
      ∧ Real.log v - Real.log u ≤ (u + 1 / 2) * (1 / u - 1 / v) := by
  have hv0 : 0 < v := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < v / u by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show 0 < v / u by positivity)
  rw [Real.log_div hv0.ne' hu.ne'] at h1 h2
  constructor
  · have e : u * (1 / u - 1 / v) = 1 - (v / u)⁻¹ := by field_simp
    linarith
  · have e : (u + 1 / 2) * (1 / u - 1 / v) - (v / u - 1)
        = (v - u) * (u + 1 / 2 - v) / (u * v) := by
      field_simp
    have h3 : 0 ≤ (v - u) * (u + 1 / 2 - v) / (u * v) := by
      apply div_nonneg
      · apply mul_nonneg <;> linarith
      · positivity
    linarith

private noncomputable def primeLogWeight (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, Real.log p / p

private noncomputable def logStep (n : ℕ) : ℝ :=
  1 / Real.log (n + 2 : ℕ) - 1 / Real.log (n + 1 + 2 : ℕ)

private lemma logStep_nonneg (n : ℕ) : 0 ≤ logStep n := by
  unfold logStep
  apply sub_nonneg.mpr
  refine one_div_le_one_div_of_le (Real.log_pos (by norm_cast; omega)) ?_
  exact Real.log_le_log (by positivity) (by norm_cast; omega)

private lemma summable_logStep : Summable logStep := by
  refine summable_of_sum_range_le logStep_nonneg (c := 1 / Real.log 2) fun n => ?_
  simp only [logStep]
  rw [Finset.sum_range_sub']
  have h : 0 ≤ 1 / Real.log (n + 2 : ℕ) :=
    div_nonneg zero_le_one (Real.log_natCast_nonneg _)
  simp only [zero_add, Nat.cast_ofNat]
  linarith

private noncomputable def mertensIncrement (n : ℕ) : ℝ :=
  primeLogWeight (n + 2) * logStep n -
    (Real.log (Real.log (n + 1 + 2 : ℕ)) - Real.log (Real.log (n + 2 : ℕ)))

private lemma norm_mertensIncrement_le (n : ℕ) :
    ‖mertensIncrement n‖ ≤ (2 + Real.log 2 + 1 / 2) * logStep n := by
  let k := n + 2
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by dsimp [k]; omega)
  let u := Real.log (k : ℝ)
  let v := Real.log ((k + 1 : ℕ) : ℝ)
  have hu : 0 < u := Real.log_pos (by linarith)
  have huv : u ≤ v := Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ k)
  have hv : v ≤ u + 1 / 2 := by
    dsimp [u, v]
    push_cast
    have h₁ := mertens_log_succ_le (k : ℝ) (by linarith)
    have h₂ := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hk
    linarith
  have hw : 1 / u - 1 / v = logStep n := by
    have h : n + 1 + 2 = k + 1 := rfl
    simp [logStep, u, v, k, h]
  obtain ⟨hlo, hhi⟩ := mertens_loglog_step u v hu huv hv
  rw [hw] at hlo hhi
  have hs : |primeLogWeight k - u| ≤ 2 + Real.log 2 :=
    mertens_first_explicit k (by dsimp [k]; omega)
  rw [abs_le] at hs
  have hsw₁ := mul_le_mul_of_nonneg_right hs.1 (logStep_nonneg n)
  have hsw₂ := mul_le_mul_of_nonneg_right hs.2 (logStep_nonneg n)
  have hstep : n + 1 + 2 = k + 1 := rfl
  unfold mertensIncrement
  rw [hstep, Real.norm_eq_abs, abs_le]
  change -( (2 + Real.log 2 + 1 / 2) * logStep n) ≤
      primeLogWeight k * logStep n - (Real.log v - Real.log u) ∧ _
  constructor <;> linarith

private lemma tendsto_primeLogWeight_div :
    Tendsto (fun n : ℕ => primeLogWeight n / Real.log n) atTop (𝓝 1) := by
  let C := 2 + Real.log 2
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC : Tendsto (fun n : ℕ => C / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hl : Tendsto (fun n : ℕ => 1 - C / Real.log n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hC
  have hh : Tendsto (fun n : ℕ => 1 + C / Real.log n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hC
  apply hl.squeeze' hh
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have h : |primeLogWeight n - Real.log n| ≤ C := mertens_first_explicit n (by omega)
    rw [abs_le] at h
    rw [le_div_iff₀ hpos, sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
    linarith [h.1]
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have h : |primeLogWeight n - Real.log n| ≤ C := mertens_first_explicit n (by omega)
    rw [abs_le] at h
    rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
    linarith [h.2]

/-- Mertens' second theorem with existence of the limiting constant. -/
lemma exists_prime_reciprocal_limit :
    ∃ B : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ n.primesLE, (1 : ℝ) / p) -
      Real.log (Real.log n)) atTop (𝓝 B) := by
  have hs : Summable mertensIncrement :=
    (summable_logStep.mul_left (2 + Real.log 2 + 1 / 2)).of_norm_bounded norm_mertensIncrement_le
  let B := 1 - Real.log (Real.log 2) + ∑' k, mertensIncrement k
  refine ⟨B, (tendsto_add_atTop_iff_nat 2).mp ?_⟩
  have hf (n : ℕ) :
      (∑ p ∈ (n + 2).primesLE, (1 : ℝ) / p) - Real.log (Real.log (n + 2 : ℕ)) =
        (primeLogWeight (n + 2) / Real.log (n + 2 : ℕ) - Real.log (Real.log 2)) +
          ∑ k ∈ Finset.range n, mertensIncrement k := by
    rw [mertens_sum_by_parts _ (by omega), Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, mertensIncrement]
    rw [Finset.sum_sub_distrib]
    have hn : (∑ k ∈ Finset.range n, (Real.log (Real.log (k + 1 + 2 : ℕ)) -
        Real.log (Real.log (k + 2 : ℕ)))) =
        Real.log (Real.log (n + 2 : ℕ)) - Real.log (Real.log 2) := by
      rw [Finset.sum_range_sub (fun k : ℕ => Real.log (Real.log (k + 2 : ℕ))) n]
      rfl
    rw [hn]
    have heq (k : ℕ) : k + 2 + 1 = k + 1 + 2 := by omega
    simp only [primeLogWeight, logStep, Nat.add_comm 2, heq, div_eq_mul_inv, one_mul]
    ring
  simp_rw [hf]
  have h := (tendsto_add_atTop_iff_nat 2).mpr tendsto_primeLogWeight_div
  exact (h.sub tendsto_const_nhds).add hs.hasSum.tendsto_sum_nat

private lemma neg_log_one_sub_sub_bounds {u : ℝ} (hu' : u ≤ 1 / 2) :
    0 ≤ -Real.log (1 - u) - u ∧ -Real.log (1 - u) - u ≤ 2 * u ^ 2 := by
  have hpos : 0 < 1 - u := by linarith
  have hl := Real.log_le_sub_one_of_pos hpos
  have hh := Real.one_sub_inv_le_log_of_pos hpos
  have hf : (1 - u)⁻¹ - 1 - u = u ^ 2 / (1 - u) := by
    field_simp
    ring
  have hq : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ hpos]
    have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * (1 - u) by linarith)
      (sq_nonneg u)
    linarith
  exact ⟨by linarith, by linarith⟩

private noncomputable def primeLogCorrection (n : ℕ) : ℝ :=
  if n.Prime then -Real.log (1 - 1 / (n : ℝ)) - 1 / n else 0

private lemma summable_primeLogCorrection : Summable primeLogCorrection := by
  have hbase := (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ))).mul_left (2 : ℝ)
  refine hbase.of_norm_bounded ?_
  intro n
  unfold primeLogCorrection
  split_ifs with hn
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hhalf : (1 : ℝ) / n ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
    obtain ⟨hlo, hhi⟩ := neg_log_one_sub_sub_bounds hhalf
    simp only [Real.norm_eq_abs, abs_of_nonneg hlo]
    simpa [one_div, inv_pow] using hhi
  · simp

/-- The logarithmic survival product has an asymptotic constant. -/
lemma exists_prime_log_product_limit :
    ∃ B : ℝ, Tendsto (fun n : ℕ =>
      (∑ p ∈ n.primesLE, -Real.log (1 - 1 / (p : ℝ))) - Real.log (Real.log n))
      atTop (𝓝 B) := by
  obtain ⟨b, hb⟩ := exists_prime_reciprocal_limit
  have hc := summable_primeLogCorrection.hasSum.tendsto_sum_nat
  refine ⟨b + ∑' n, primeLogCorrection n, ?_⟩
  have hcc := (tendsto_add_atTop_iff_nat 1).mpr hc
  refine (hb.add hcc).congr fun n => ?_
  rw [show (∑ i ∈ Finset.range (n + 1), primeLogCorrection i) =
      ∑ p ∈ n.primesLE, (-Real.log (1 - 1 / (p : ℝ)) - 1 / p) by
    simp only [primeLogCorrection, Nat.primesLE, Nat.primesBelow, Finset.sum_filter]]
  rw [Finset.sum_sub_distrib]
  ring

private noncomputable def expCutoff (n : ℕ) : ℕ := ⌊Real.exp (n : ℝ)⌋₊

private lemma tendsto_expCutoff : Tendsto expCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop)

private lemma expCutoff_mono : Monotone expCutoff := fun i j hij =>
  Nat.floor_mono (Real.exp_le_exp.mpr (by exact_mod_cast hij))

private lemma tendsto_loglog_expCutoff :
    Tendsto (fun n : ℕ => Real.log (Real.log (expCutoff n : ℝ)) - Real.log n) atTop (𝓝 0) := by
  have hl := (Real.tendsto_log_comp_add_sub_log (-Real.log 2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hl.squeeze' tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlarge : (2 : ℝ) ≤ Real.exp (n : ℝ) := by linarith [Real.add_one_le_exp (n : ℝ)]
    have hf : Real.exp (n : ℝ) / 2 ≤ expCutoff n := by
      have h := Nat.sub_one_lt_floor (Real.exp (n : ℝ))
      unfold expCutoff
      linarith
    have hlog := Real.log_le_log (by positivity) hf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_exp] at hlog
    have hpos : 0 < (n : ℝ) - Real.log 2 := by linarith [Real.log_two_lt_d9]
    exact sub_le_sub_right (Real.log_le_log hpos hlog) _
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlarge : (2 : ℝ) ≤ Real.exp (n : ℝ) := by linarith [Real.add_one_le_exp (n : ℝ)]
    have hpos : 0 < (expCutoff n : ℝ) := by
      have h := Nat.sub_one_lt_floor (Real.exp (n : ℝ))
      unfold expCutoff
      linarith
    have hlog := Real.log_le_log hpos (Nat.floor_le (Real.exp_pos (n : ℝ)).le)
    rw [Real.log_exp] at hlog
    have hlogpos : 0 < Real.log (expCutoff n : ℝ) := by
      apply Real.log_pos
      have h := Nat.sub_one_lt_floor (Real.exp (n : ℝ))
      unfold expCutoff
      linarith [Real.add_one_le_exp (n : ℝ)]
    exact sub_nonpos.mpr (Real.log_le_log hlogpos hlog)

private noncomputable def primeBlockSum (n : ℕ) : ℝ :=
  ∑ p ∈ (expCutoff n).primesLE, -Real.log (1 - 1 / (p : ℝ))

private lemma primeBlockSum_zero : primeBlockSum 0 = 0 := by
  simp [primeBlockSum, expCutoff]

private noncomputable def primeBlockIncrement (n : ℕ) : ℝ :=
  primeBlockSum (n + 1) - primeBlockSum n

private lemma prime_block_partial_limit {B : ℝ} (hB : Tendsto (fun n : ℕ =>
    (∑ p ∈ n.primesLE, -Real.log (1 - 1 / (p : ℝ))) - Real.log (Real.log n)) atTop (𝓝 B)) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (primeBlockIncrement k - 1 / (k + 1 : ℕ)))
      atTop (𝓝 (B - Real.eulerMascheroniConstant)) := by
  have h' : Tendsto (fun n : ℕ => primeBlockSum n - Real.log n) atTop (𝓝 B) := by
    have h := (hB.comp tendsto_expCutoff).add tendsto_loglog_expCutoff
    rw [add_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, primeBlockSum]
    ring
  have h'' := h'.sub Real.tendsto_harmonic_sub_log
  refine h''.congr fun n => ?_
  simp only [primeBlockIncrement, Finset.sum_sub_distrib,
    Finset.sum_range_sub primeBlockSum, primeBlockSum_zero, sub_zero]
  unfold harmonic
  push_cast
  simp [one_div]

private lemma scaled_neg_log_le {u t : ℝ} (hu : u < 1) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    -Real.log (1 - u * t) ≤ t * (-Real.log (1 - u)) := by
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (show 1 - u ∈ Set.Ioi 0 from sub_pos.mpr hu)
    (sub_nonneg.mpr ht') ht (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hc
  rw [show 1 - t + t * (1 - u) = 1 - u * t by ring] at hc
  linarith

private lemma euler_log_le_prime_block_weight {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) (n : ℕ) :
    (∑ p ∈ (expCutoff n).primesLE, -Real.log (1 - (p : ℝ) ^ (-(1 - Real.log r)))) ≤
      ∑ k ∈ Finset.range n, primeBlockIncrement k * r ^ k := by
  induction n with
  | zero => simp [expCutoff]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hsub := Nat.primesLE_mono (expCutoff_mono (Nat.le_succ n))
    have hstep :
        ∑ p ∈ (expCutoff (n + 1)).primesLE \ (expCutoff n).primesLE,
          -Real.log (1 - (p : ℝ) ^ (-(1 - Real.log r))) ≤ primeBlockIncrement n * r ^ n := by
      unfold primeBlockIncrement primeBlockSum
      rw [← Finset.sum_sdiff_eq_sub hsub, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro p hp
      have hpp := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
      have hp' : expCutoff n < p := by
        by_contra! h
        exact (Finset.mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨h, hpp⟩)
      have hp₀ : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hp₁ : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have hpLog : (n : ℝ) ≤ Real.log p := by
        have h := Real.log_le_log (Real.exp_pos _) (Nat.lt_of_floor_lt hp').le
        simpa using h
      have hrLog := Real.log_neg hr₀ hr₁
      have hw : (p : ℝ) ^ Real.log r ≤ r ^ n := by
        have hpow : r ^ n = Real.exp (Real.log r * n) := by
          rw [mul_comm, Real.exp_nat_mul, Real.exp_log hr₀]
        rw [Real.rpow_def_of_pos hp₀, hpow, Real.exp_le_exp]
        simpa only [mul_comm (Real.log r) (n : ℝ)] using mul_le_mul_of_nonpos_right hpLog hrLog.le
      have hsplit : (p : ℝ) ^ (-(1 - Real.log r)) = 1 / p * (p : ℝ) ^ Real.log r := by
        rw [show -(1 - Real.log r) = -1 + Real.log r by ring,
          Real.rpow_add hp₀, Real.rpow_neg_one, one_div]
      have hu : (1 : ℝ) / p < 1 := (div_lt_one hp₀).mpr hp₁
      have hsign : 0 ≤ -Real.log (1 - 1 / (p : ℝ)) :=
        neg_nonneg.mpr (Real.log_nonpos (by linarith) (sub_le_self _ (by positivity)))
      rw [hsplit]
      apply (scaled_neg_log_le hu (by positivity) (hw.trans (pow_le_one₀ hr₀.le hr₁.le))).trans
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hw hsign
    rw [Finset.sum_sdiff_eq_sub hsub] at hstep
    linarith

private noncomputable def realZeta (s : ℝ) : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ s

private lemma ofReal_realZeta {s : ℝ} (hs : 1 < s) :
    (realZeta s : ℂ) = riemannZeta (s : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hs)]
  simp only [realZeta, Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]

private lemma tendsto_realEuler_log {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n : ℕ => ∑ p ∈ n.primesLE, -Real.log (1 - (p : ℝ) ^ (-s))) atTop
      (𝓝 (Real.log (realZeta s))) := by
  let f := fun p : ℕ => (1 - (p : ℝ) ^ (-s))⁻¹
  have ht : Tendsto (fun n : ℕ => ∏ p ∈ n.primesLE, f p) atTop (𝓝 (realZeta s)) := by
    have hc := riemannZeta_eulerProduct (s := (s : ℂ)) (by simpa using hs)
    rw [← ofReal_realZeta hs] at hc
    rw [← tendsto_ofReal_iff]
    have hshift := (tendsto_add_atTop_iff_nat 1).mpr hc
    refine hshift.congr fun n => ?_
    simp only [Nat.primesLE, f, Complex.ofReal_prod, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast,
      Complex.ofReal_neg]
  have hpos (p : ℕ) (hp : p.Prime) : 0 < 1 - (p : ℝ) ^ (-s) := by
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith))
  have hζ : 1 ≤ realZeta s :=
    ge_of_tendsto ht (Eventually.of_forall fun (n : ℕ) =>
      Finset.one_le_prod fun p hp =>
        (one_le_inv₀ (hpos p (Nat.prime_of_mem_primesLE hp))).mpr
          (sub_le_self _ (by positivity)))
  have ht' := (Real.continuousAt_log (show realZeta s ≠ 0 by linarith)).tendsto.comp ht
  refine ht'.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [Real.log_prod (fun p hp => inv_ne_zero (hpos p (Nat.prime_of_mem_primesLE hp)).ne')]
  simp only [Real.log_inv]

private lemma eventually_pos_lt_one : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r ∧ r < 1 := by
  filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds zero_lt_one), eventually_mem_nhdsWithin]
    with r hr hlt
  exact ⟨hr, hlt⟩

private lemma tendsto_zeta_scaled :
    Tendsto (fun r : ℝ => (1 - r) * realZeta (1 - Real.log r)) (𝓝[<] 1) (𝓝 1) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hlog : Tendsto Real.log (𝓝[<] 1) (𝓝 0) := by
    simpa using (Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun r : ℝ => 1 - Real.log r) (𝓝[<] 1) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using tendsto_const_nhds.sub hlog
    · filter_upwards [eventually_pos_lt_one] with r hr
      exact Set.mem_Ioi.mpr (by linarith [Real.log_neg hr.1 hr.2])
  have hζ := tendsto_sub_mul_tsum_nat_rpow.comp hs
  have hratio : Tendsto (fun r : ℝ => (1 - r) / (-Real.log r)) (𝓝[<] 1) (𝓝 1) := by
    apply hr.squeeze' tendsto_const_nhds
    · filter_upwards [eventually_pos_lt_one] with r hr
      have hl := Real.one_sub_inv_le_log_of_pos hr.1
      have hp := Real.log_neg hr.1 hr.2
      rw [le_div_iff₀ (neg_pos.mpr hp)]
      have h := mul_le_mul_of_nonneg_left hl hr.1.le
      rw [mul_sub, mul_one, mul_inv_cancel₀ hr.1.ne'] at h
      linarith
    · filter_upwards [eventually_pos_lt_one] with r hr
      rw [div_le_iff₀ (neg_pos.mpr (Real.log_neg hr.1 hr.2)), one_mul]
      linarith [Real.log_le_sub_one_of_pos hr.1]
  have h := hratio.mul hζ
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_pos_lt_one] with r hr
  have hne := (Real.log_neg hr.1 hr.2).ne
  change (1 - r) / (-Real.log r) * ((1 - Real.log r - 1) * realZeta _) = _
  field_simp
  ring

private lemma tendsto_zeta_log_normalized :
    Tendsto (fun r : ℝ => r * Real.log (realZeta (1 - Real.log r)) + Real.log (1 - r))
      (𝓝[<] 1) (𝓝 0) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have h₁ : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hr
  have h₂ : Tendsto (fun r : ℝ => Real.log ((1 - r) * realZeta (1 - Real.log r)))
      (𝓝[<] 1) (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp tendsto_zeta_scaled
  have hsign : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < (1 - r) * realZeta (1 - Real.log r) :=
    tendsto_zeta_scaled.eventually (eventually_gt_nhds zero_lt_one)
  have h₃ := (Real.continuous_mul_log.continuousAt (x := 0)).tendsto.comp h₁
  have h := (hr.mul h₂).add h₃
  simp only [Real.log_zero, mul_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_pos_lt_one, hsign] with r hr hsign
  have hz : realZeta (1 - Real.log r) ≠ 0 := by
    intro he
    rw [he, mul_zero] at hsign
    exact (lt_irrefl _ hsign)
  change r * Real.log ((1 - r) * realZeta (1 - Real.log r)) +
    (1 - r) * Real.log (1 - r) = _
  rw [Real.log_mul (sub_ne_zero.mpr hr.2.ne') hz]
  ring

private lemma gamma_le_log_product_limit {B : ℝ} (hB : Tendsto (fun n : ℕ =>
    (∑ p ∈ n.primesLE, -Real.log (1 - 1 / (p : ℝ))) - Real.log (Real.log n)) atTop (𝓝 B)) :
    Real.eulerMascheroniConstant ≤ B := by
  have hpart := prime_block_partial_limit hB
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hpart
  have hr : Tendsto (fun r : ℝ => r) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hab' := hr.mul hab
  rw [one_mul] at hab'
  have hcmp : 0 ≤ B - Real.eulerMascheroniConstant := by
    apply le_of_tendsto_of_tendsto tendsto_zeta_log_normalized hab'
    filter_upwards [eventually_pos_lt_one] with r hr
    have hnr : |r| < 1 := by simpa [abs_of_pos hr.1] using hr.2
    have hgeom := (Real.hasSum_pow_div_log_of_abs_lt_one hnr).tendsto_sum_nat
    have hser := (summable_powerSeries_of_norm_lt_one hpart.cauchySeq
      (by simpa [Real.norm_eq_abs] using hnr)).hasSum.tendsto_sum_nat
    have hs : 1 < 1 - Real.log r := by linarith [Real.log_neg hr.1 hr.2]
    have hlog := (tendsto_realEuler_log hs).comp tendsto_expCutoff
    have hscaled := (hlog.const_mul r).sub hgeom
    rw [sub_neg_eq_add] at hscaled
    refine le_of_tendsto_of_tendsto hscaled (hser.const_mul r) (Eventually.of_forall fun n => ?_)
    have hh := mul_le_mul_of_nonneg_left (euler_log_le_prime_block_weight hr.1 hr.2 n) hr.1.le
    calc
      _ ≤ r * (∑ k ∈ Finset.range n, primeBlockIncrement k * r ^ k) -
        ∑ k ∈ Finset.range n, r ^ (k + 1) / ((k : ℝ) + 1) := sub_le_sub_right hh _
      _ = _ := by
        change _ = r * ∑ k ∈ Finset.range n, (primeBlockIncrement k - 1 / (k + 1 : ℕ)) * r ^ k
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        rw [pow_succ]
        ring
  linarith

/-- The upper bound from Mertens' third theorem, with its exact limiting constant. -/
lemma mertens_product_upper (m : ℝ) (hm : (Real.exp Real.eulerMascheroniConstant)⁻¹ < m) :
    ∀ᶠ y : ℕ in atTop, primeSurvival y * Real.log y ≤ m := by
  obtain ⟨B, hB⟩ := exists_prime_log_product_limit
  have hγ := gamma_le_log_product_limit hB
  have hlim : Tendsto (fun y : ℕ => primeSurvival y * Real.log y) atTop (𝓝 (Real.exp (-B))) := by
    refine ((Real.continuous_exp.tendsto _).comp hB.neg).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with y hy
    change Real.exp (-((∑ p ∈ y.primesLE, -Real.log (1 - 1 / (p : ℝ))) -
      Real.log (Real.log y))) = _
    have hlog : 0 < Real.log y := Real.log_pos (by exact_mod_cast hy)
    rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hlog, ← Finset.sum_neg_distrib,
      Real.exp_sum, mul_comm]
    unfold primeSurvival
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [neg_neg, Real.exp_log]
    have hp₁ : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith : (0 : ℝ) < p)).mpr hp₁)
  have hlt : Real.exp (-B) < m := by
    apply lt_of_le_of_lt (Real.exp_le_exp.mpr (neg_le_neg hγ))
    rwa [Real.exp_neg]
  exact (hlim.eventually (eventually_lt_nhds hlt)).mono fun _ h => h.le

lemma eventually_cutoff_log_le {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      Real.log (8 * x) ≤ (1 + ε) * Real.log (⌊δ * x⌋₊ : ℕ) := by
  have hδt : Tendsto (fun x : ℝ => δ * x) atTop atTop :=
    tendsto_id.const_mul_atTop hδ
  filter_upwards [hδt.eventually_ge_atTop 2, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop
      ((Real.log 8 - (1 + ε) * Real.log (δ / 2)) / ε)] with x hxδ hx hlog
  have hfloor : (δ / 2) * x ≤ (⌊δ * x⌋₊ : ℕ) := by
    have h := Nat.sub_one_lt_floor (δ * x)
    linarith
  have hx0 : 0 < x := by linarith
  have hlow := Real.log_le_log (mul_pos (half_pos hδ) hx0) hfloor
  rw [Real.log_mul (by positivity) hx0.ne'] at hlow
  rw [Real.log_mul (by norm_num) hx0.ne']
  have hlog' := (div_le_iff₀ hε).mp hlog
  calc
    _ ≤ (1 + ε) * (Real.log (δ / 2) + Real.log x) := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by linarith)

lemma eventually_cutoff_survival_le {δ m : ℝ} (hδ : 0 < δ)
    (hm : (Real.exp Real.eulerMascheroniConstant)⁻¹ < m) :
    ∀ᶠ x : ℝ in atTop,
      primeSurvival ⌊δ * x⌋₊ * Real.log (8 * x) ≤ m := by
  let m₀ := ((Real.exp Real.eulerMascheroniConstant)⁻¹ + m) / 2
  have hm₀ : (Real.exp Real.eulerMascheroniConstant)⁻¹ < m₀ := by dsimp [m₀]; linarith
  have hm₀0 : 0 < m₀ := lt_trans (by positivity) hm₀
  have hm₀m : m₀ < m := by dsimp [m₀]; linarith
  let ε := m / m₀ - 1
  have hε : 0 < ε := sub_pos.mpr ((lt_div_iff₀ hm₀0).mpr (by simpa using hm₀m))
  have ht : Tendsto (fun x : ℝ => ⌊δ * x⌋₊) atTop atTop :=
    (tendsto_nat_floor_atTop (α := ℝ)).comp (tendsto_id.const_mul_atTop hδ)
  filter_upwards [ht.eventually (mertens_product_upper m₀ hm₀),
    eventually_cutoff_log_le hδ hε] with x hx hlog
  calc
    _ ≤ primeSurvival ⌊δ * x⌋₊ * ((1 + ε) * Real.log (⌊δ * x⌋₊ : ℕ)) :=
      mul_le_mul_of_nonneg_left hlog (primeSurvival_nonneg _)
    _ = (1 + ε) * (primeSurvival ⌊δ * x⌋₊ * Real.log (⌊δ * x⌋₊ : ℕ)) := by ring
    _ ≤ (1 + ε) * m₀ := mul_le_mul_of_nonneg_left hx (by linarith)
    _ = m := by
      dsimp [ε]
      field_simp
      ring

lemma card_Icc_zero_le (A : Set ℕ) [DecidablePred (· ∈ A)] (N : ℕ) :
    ((Finset.Icc 0 N).filter (· ∈ A)).card ≤ ((Finset.Icc 1 N).filter (· ∈ A)).card + 1 := by
  have hs : (Finset.Icc 0 N).filter (· ∈ A) ⊆ insert 0 ((Finset.Icc 1 N).filter (· ∈ A)) := by
    intro a ha
    obtain ⟨hi, ha⟩ := Finset.mem_filter.mp ha
    have hN := (Finset.mem_Icc.mp hi).2
    rcases Nat.eq_zero_or_pos a with rfl | hp
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp, hN⟩, ha⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

lemma eventually_log_affine_le {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log (a * x + b) ≤ ε * x := by
  have hlog := Real.isLittleO_log_id_atTop.bound (half_pos hε)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (Real.log (a + b) / (ε / 2))] with x hl hx hb'
  have hx0 : 0 < x := by linarith
  simp only [id_eq, Real.norm_eq_abs, abs_of_pos hx0] at hl
  have hl' := (le_abs_self (Real.log x)).trans hl
  have hc := (div_le_iff₀ (half_pos hε)).mp hb'
  have hmul : b ≤ b * x := by nlinarith
  calc
    _ ≤ Real.log ((a + b) * x) := Real.log_le_log (by positivity) (by linarith)
    _ = Real.log (a + b) + Real.log x := Real.log_mul (by positivity) hx0.ne'
    _ ≤ _ := by linarith

/-- Real-valued lower bound for the counting function of an additive complement. -/
lemma core (A : Set ℕ) [DecidablePred (· ∈ A)] (hA : Erdos32.IsAdditiveComplementToPrimes A)
    (c : ℝ) (hc : c < Real.exp Real.eulerMascheroniConstant) :
    ∀ᶠ N : ℕ in atTop, c * Real.log N ≤ (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) := by
  by_cases hc0 : c ≤ 0
  · exact Eventually.of_forall fun N =>
      (mul_nonpos_of_nonpos_of_nonneg hc0 (Real.log_natCast_nonneg N)).trans (Nat.cast_nonneg _)
  have hcpos : 0 < c := lt_of_not_ge hc0
  rw [Erdos32.IsAdditiveComplementToPrimes, eventually_atTop] at hA
  obtain ⟨K, hK⟩ := hA
  let L := Real.exp Real.eulerMascheroniConstant
  let d := (c + L) / 2
  have hcd : c < d := by dsimp [d, L]; linarith
  have hd : 0 < d := hcpos.trans hcd
  have hdL : d < L := by dsimp [d, L]; linarith
  let m := (L⁻¹ + d⁻¹) / 2
  have hinv : L⁻¹ < d⁻¹ := (inv_lt_inv₀ (hd.trans hdL) hd).mpr hdL
  have hm : L⁻¹ < m := by dsimp [m]; linarith
  have hm0 : 0 < m := lt_trans (by dsimp [L]; positivity) hm
  have hdm : d * m < 1 := by
    have ht : m < d⁻¹ := by dsimp [m]; linarith
    simpa [hd.ne'] using mul_lt_mul_of_pos_left ht hd
  let δ := (1 - d * m) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith [mul_pos hd hm0]
  have ht : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, ht.eventually_ge_atTop 1,
    ht.eventually_ge_atTop (1 / (d - c)),
    ht.eventually (eventually_prime_cutoff_supply hδ.le hδ1),
    ht.eventually (eventually_cutoff_survival_le hδ hm),
    ht.eventually (eventually_log_affine_le hd (show 0 < (K : ℝ) + 1 by positivity)
      (show 0 < 2 * δ by positivity))] with N hN hx hgap hs hmert hover
  by_contra! hsmall
  let x := Real.log N
  let S := (Finset.Icc 0 N).filter (· ∈ A)
  let y := ⌊δ * x⌋₊
  let z := ⌊8 * x⌋₊
  have hx0 : 0 < x := by change 1 ≤ x at hx; linarith
  have hcard₀ : (S.card : ℝ) ≤ ((Finset.Icc 1 N).filter (· ∈ A)).card + 1 := by
    exact_mod_cast card_Icc_zero_le A N
  have hcS : (S.card : ℝ) ≤ d * x := by
    have hh := (div_le_iff₀ (sub_pos.mpr hcd)).mp hgap
    change 1 ≤ x * (d - c) at hh
    change (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) < c * x at hsmall
    linarith
  have hzlog : 0 < Real.log (8 * x) := Real.log_pos (by change 1 ≤ x at hx; linarith)
  have hcost : primeSurvival y * S.card * Real.log (8 * x) ≤ (d * m) * x := calc
    _ = (primeSurvival y * Real.log (8 * x)) * S.card := by ring
    _ ≤ m * S.card := mul_le_mul_of_nonneg_right hmert (Nat.cast_nonneg _)
    _ ≤ m * (d * x) := mul_le_mul_of_nonneg_left hcS hm0.le
    _ = _ := by ring
  have hdmx : (d * m) * x < x := by nlinarith [mul_lt_mul_of_pos_right hdm hx0]
  have hs' : primeSurvival y * S.card ≤ ((z.primesLE \ y.primesLE).card : ℝ) :=
    (mul_le_mul_iff_left₀ hzlog).mp (hcost.trans (hdmx.le.trans hs))
  have hfin := sieve_log_bound A (show 0 < N by omega) hK y z hs'
  change x < Real.log (K + S.card + 1 : ℕ) + Real.log 4 * y +
    primeSurvival y * S.card * Real.log z at hfin
  have hover' : Real.log (K + S.card + 1 : ℕ) ≤ 2 * δ * x := by
    refine (Real.log_le_log (by positivity) ?_).trans hover
    push_cast
    linarith
  have hprim : Real.log 4 * y ≤ 2 * δ * x := calc
    _ ≤ 2 * (y : ℝ) := mul_le_mul_of_nonneg_right log_four_le_two (Nat.cast_nonneg _)
    _ ≤ 2 * (δ * x) := mul_le_mul_of_nonneg_left
      (Nat.floor_le (mul_nonneg hδ.le hx0.le)) (by norm_num)
    _ = _ := by ring
  have hzlog' : Real.log z ≤ Real.log (8 * x) := by
    by_cases hz : z = 0
    · simpa [hz] using hzlog.le
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
        (Nat.floor_le (by positivity))
  have hcost' := (mul_le_mul_of_nonneg_left hzlog'
    (mul_nonneg (primeSurvival_nonneg y) (Nat.cast_nonneg S.card))).trans hcost
  have hsum : 2 * δ * x + 2 * δ * x + (d * m) * x = x := by dsimp [δ]; ring
  linarith

/-- Glue: an eventual real lower bound for every c below x gives x below the EReal liminf. -/
lemma ereal_le_liminf_of_eventually (x : ℝ) (a : ℕ → ℕ)
    (h : ∀ c : ℝ, c < x → ∀ᶠ N : ℕ in atTop, c * Real.log N ≤ (a N : ℝ)) :
    (x : EReal) ≤ liminf (fun N => ((a N : EReal) / (Real.log N : EReal))) atTop := by
  apply le_of_forall_lt_imp_le_of_dense
  intro y hy
  obtain ⟨c, hyc, hcx⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  have hcx' : c < x := by exact_mod_cast hcx
  refine le_trans hyc.le (le_liminf_of_le (by isBoundedDefault) ?_)
  filter_upwards [h c hcx', eventually_ge_atTop 2] with N hN hN2
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hcast : (a N : EReal) = ((a N : ℝ) : EReal) := rfl
  rw [hcast, ← EReal.coe_div, EReal.coe_le_coe_iff, le_div_iff₀ hlog]
  exact hN

end OMA32R

theorem OMA.solution : type_of% @Erdos32.erdos_32.variants.ruzsa := by
  intro A hA
  classical
  exact OMA32R.ereal_le_liminf_of_eventually _ _ (fun c hc => OMA32R.core A hA c hc)
