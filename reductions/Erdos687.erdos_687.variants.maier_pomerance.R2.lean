import FormalConjectures.ErdosProblems.«687»

/-!
# A disjoint residue packing reduction of the Maier–Pomerance bound

After sifting the length-`y` interval by primes up to `min x ⌊√y⌋`, each
remaining prime can be assigned to any one survivor. To cover more, some
primes must each cover a group of at least two survivors. Assign each survivor
to only one prime so the groups are disjoint. Two distinct positions can
share a class for at most one prime above `√y`, since the product of two
such primes exceeds their difference.

The two hypotheses rule out covering exclusively by singleton assignments
and covering by a mixture of groups and singleton assignments. The finite
equivalence also shows that every violation of either bound gives a cover.
-/

namespace OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2

open Asymptotics Filter Finset

/-- Above the square root of the interval length, a pair has at most one prime label. -/
theorem prime_label_unique {x y i j p q : ℕ} (hij : i < j) (hjy : j ≤ y)
    (hp : p ∈ (Finset.Ioc (min x y.sqrt) x).filter Nat.Prime)
    (hq : q ∈ (Finset.Ioc (min x y.sqrt) x).filter Nat.Prime)
    (hpmod : i ≡ j [MOD p]) (hqmod : i ≡ j [MOD q]) : p = q := by
  obtain ⟨hpRange, hpPrime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqRange, hqPrime⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpLower, hpUpper⟩ := Finset.mem_Ioc.mp hpRange
  obtain ⟨hqLower, hqUpper⟩ := Finset.mem_Ioc.mp hqRange
  have hpBig : y.sqrt.succ ≤ p := by omega
  have hqBig : y.sqrt.succ ≤ q := by omega
  have hbig : y < p * q := (Nat.lt_succ_sqrt y).trans_le (Nat.mul_le_mul hpBig hqBig)
  by_contra hne
  have hd := Nat.Prime.dvd_mul_of_dvd_ne hne hpPrime hqPrime
    ((Nat.modEq_iff_dvd' hij.le).mp hpmod) ((Nat.modEq_iff_dvd' hij.le).mp hqmod)
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hd
  omega

/-- Complete a partial assignment by giving each unassigned survivor a distinct unused prime. -/
private theorem cover_of_packing_budget {x y z : ℕ} (hzx : z ≤ x) (a : ℕ → ℕ)
    (U : Finset ℕ) (f : ℕ → ℕ)
    (hU : U ⊆ (Icc 1 y).filter
      (fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])))
    (hImage : U.image f ⊆ (Ioc z x).filter Nat.Prime)
    (hClasses : ∀ m ∈ U, ∀ n ∈ U, f m = f n → m ≡ n [MOD f m])
    (hBudget : ((Icc 1 y).filter
      (fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p]))).card ≤
      U.card + (((Ioc z x).filter Nat.Prime) \ U.image f).card) :
    Green46.IsCoveredByResidues x y := by
  let survivors := (Icc 1 y).filter fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])
  let primes := (Ioc z x).filter Nat.Prime
  let remaining := survivors \ U
  let unused := primes \ U.image f
  have hRemaining : remaining.card ≤ unused.card := by
    have hCard := card_sdiff_add_card_eq_card hU
    change remaining.card + U.card = survivors.card at hCard
    change survivors.card ≤ U.card + unused.card at hBudget
    omega
  have hCard : Fintype.card ↥remaining ≤ unused.card := by
    simpa only [Fintype.card_coe] using hRemaining
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hCard
  have hChoose : ∀ p : ℕ, ∃ b : ℕ,
      (∀ m ∈ U, f m = p → m ≡ b [MOD p]) ∧
      (∀ m : ↥remaining, e m = p → (m : ℕ) ≡ b [MOD p]) := by
    intro p
    by_cases hp : p ∈ U.image f
    · obtain ⟨n, hn, hnp⟩ := mem_image.mp hp
      refine ⟨n, ?_, ?_⟩
      · intro m hm hmp
        simpa only [hmp] using hClasses m hm n hn (hmp.trans hnp.symm)
      · intro m hm
        have hu : e m ∈ unused := he ⟨m, rfl⟩
        rw [hm] at hu
        exact ((mem_sdiff.mp hu).2 hp).elim
    · by_cases hex : ∃ m : ↥remaining, e m = p
      · obtain ⟨n, hn⟩ := hex
        refine ⟨n, ?_, ?_⟩
        · intro m hm hmp
          exact (hp (mem_image.mpr ⟨m, hm, hmp⟩)).elim
        · intro m hm
          rw [e.injective (hm.trans hn.symm)]
      · refine ⟨0, ?_, ?_⟩
        · intro m hm hmp
          exact (hp (mem_image.mpr ⟨m, hm, hmp⟩)).elim
        · intro m hm
          exact (hex ⟨m, hm⟩).elim
  choose b hb using hChoose
  refine ⟨fun p => if p ≤ z then a p else b p, fun m hm => ?_⟩
  by_cases hs : m ∈ survivors
  · by_cases hmU : m ∈ U
    · obtain ⟨hp, hpPrime⟩ := mem_filter.mp (hImage (mem_image.mpr ⟨m, hmU, rfl⟩))
      obtain ⟨hpLower, hpUpper⟩ := mem_Ioc.mp hp
      exact ⟨f m, hpUpper, hpPrime, by
        simpa only [if_neg (not_le_of_gt hpLower)] using (hb (f m)).1 m hmU rfl⟩
    · let r : ↥remaining := ⟨m, mem_sdiff.mpr ⟨hs, hmU⟩⟩
      have hp : e r ∈ unused := he ⟨r, rfl⟩
      obtain ⟨hp, hpPrime⟩ := mem_filter.mp (mem_sdiff.mp hp).1
      obtain ⟨hpLower, hpUpper⟩ := mem_Ioc.mp hp
      exact ⟨e r, hpUpper, hpPrime, by
        simpa only [if_neg (not_le_of_gt hpLower)] using (hb (e r)).2 r rfl⟩
  · have hmHit : ¬ ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p]) :=
      fun hAvoid => hs (mem_filter.mpr ⟨hm, hAvoid⟩)
    push Not at hmHit
    obtain ⟨p, hp, hpPrime, hCongr⟩ := hmHit
    exact ⟨p, hp.trans hzx, hpPrime, by simpa only [if_pos hp] using hCongr⟩

/--
A cover exists exactly when some initial sieve leaves few enough survivors for
singleton assignments, or admits a nonempty partial packing whose remaining
survivors can be covered using distinct unused primes. The image of `f` is the
set of primes used by the packing. Every fiber of `f` on `U` has size at least two
and lies in a single congruence class.
-/
theorem cover_iff_packing_budget {x y z : ℕ} (hzx : z ≤ x) :
    Green46.IsCoveredByResidues x y ↔
      ∃ a : ℕ → ℕ,
        let survivors := (Icc 1 y).filter fun m =>
          ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])
        let primes := (Ioc z x).filter Nat.Prime
        survivors.card ≤ primes.card ∨
          ∃ (U : Finset ℕ) (f : ℕ → ℕ), U.Nonempty ∧ U ⊆ survivors ∧ U.image f ⊆ primes ∧
            (∀ m ∈ U, ∃ n ∈ U, n ≠ m ∧ f n = f m) ∧
            (∀ m ∈ U, ∀ n ∈ U, f m = f n → m ≡ n [MOD f m]) ∧
            survivors.card ≤ U.card + (primes \ U.image f).card := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    let survivors := (Icc 1 y).filter fun m =>
      ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])
    let primes := (Ioc z x).filter Nat.Prime
    have hChoose : ∀ m : ℕ, ∃ p : ℕ,
        m ∉ survivors ∨ (p ∈ primes ∧ m ≡ a p [MOD p]) := by
      intro m
      by_cases hm : m ∈ survivors
      · obtain ⟨hmInterval, hmAvoid⟩ := mem_filter.mp hm
        obtain ⟨p, hpUpper, hpPrime, hpCongr⟩ := ha m hmInterval
        have hpLower : z < p := lt_of_not_ge fun hp => hmAvoid p hp hpPrime hpCongr
        exact ⟨p, Or.inr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpLower, hpUpper⟩, hpPrime⟩, hpCongr⟩⟩
      · exact ⟨0, Or.inl hm⟩
    choose f hf' using hChoose
    have hf : ∀ m ∈ survivors, f m ∈ primes ∧ m ≡ a (f m) [MOD f m] := by
      intro m hm
      exact (hf' m).resolve_left (fun h => h hm)
    let U := survivors.filter fun m => ∃ n ∈ survivors, n ≠ m ∧ f n = f m
    have hU : U ⊆ survivors := filter_subset _ _
    have hImage : U.image f ⊆ primes := by
      intro p hp
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
      exact (hf m (hU hm)).1
    have hInjective : Set.InjOn f (↑(survivors \ U) : Set ℕ) := by
      intro m hm n hn heq
      obtain ⟨hmS, hmU⟩ := mem_sdiff.mp hm
      by_contra hmn
      exact hmU (mem_filter.mpr ⟨hmS, n, (mem_sdiff.mp hn).1, Ne.symm hmn, heq.symm⟩)
    have hRemainingImage : (survivors \ U).image f ⊆ primes \ U.image f := by
      intro p hp
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hp
      obtain ⟨hmS, hmU⟩ := mem_sdiff.mp hm
      refine mem_sdiff.mpr ⟨(hf m hmS).1, ?_⟩
      intro hmImage
      obtain ⟨n, hnU, heq⟩ := mem_image.mp hmImage
      have hnm : n ≠ m := fun h => hmU (h ▸ hnU)
      exact hmU (mem_filter.mpr ⟨hmS, n, hU hnU, hnm, heq⟩)
    have hRemaining : (survivors \ U).card ≤ (primes \ U.image f).card := by
      rw [← card_image_of_injOn hInjective]
      exact card_le_card hRemainingImage
    have hBudget : survivors.card ≤ U.card + (primes \ U.image f).card := by
      have hCard := card_sdiff_add_card_eq_card hU
      omega
    by_cases hNonempty : U.Nonempty
    · right
      refine ⟨U, f, hNonempty, hU, hImage, ?_, ?_, hBudget⟩
      · intro m hm
        obtain ⟨hmS, n, hnS, hnm, heq⟩ := mem_filter.mp hm
        exact ⟨n, mem_filter.mpr ⟨hnS, m, hmS, Ne.symm hnm, heq.symm⟩, hnm, heq⟩
      · intro m hm n hn hEq
        have hmCongr := (hf m (hU hm)).2
        have hnCongr := (hf n (hU hn)).2
        rw [← hEq] at hnCongr
        exact hmCongr.trans hnCongr.symm
    · left
      have hEmpty : U = ∅ := not_nonempty_iff_eq_empty.mp hNonempty
      simpa only [hEmpty, card_empty, image_empty, sdiff_empty, zero_add] using hBudget
  · rintro ⟨a, h⟩
    dsimp only at h
    rcases h with h | ⟨U, f, _, hU, hImage, _, hClasses, hBudget⟩
    · apply cover_of_packing_budget hzx a ∅ (fun _ => 0)
      · exact empty_subset _
      · simp
      · simp
      · simpa using h
    · exact cover_of_packing_budget hzx a U f hU hImage hClasses hBudget

private theorem Y_le_of_not_coverable_succ {x y : ℕ}
    (h : ¬ Green46.IsCoveredByResidues x (y + 1)) : Erdos687.Y x ≤ y := by
  rw [Erdos687.Y]
  refine csSup_le ⟨0, ⟨fun _ => 0, by simp⟩⟩ ?_
  rintro k ⟨a, ha⟩
  by_contra hk
  have hle : y + 1 ≤ k := by omega
  exact h ⟨a, fun m hm => ha m <| mem_Icc.mpr
    ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans hle⟩⟩

/-- The initial sieve leaves more survivors than primes remain.
OpenAI's Theorem 1.2 in *A quadratic bound for Jacobsthal's function*,
applied at `√y * log y / 4` to a prefix of asymptotic length `y / 4`, gives
at least a constant times `y * log log y / (log y)^2` survivors. At the
specified length that quantity grows faster than `x`. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ x : ℕ in atTop, ∀ a : ℕ → ℕ,
      let y := ⌊(x : ℝ) * Real.log x ^ (2 + ε)⌋₊ + 1
      let z := min x y.sqrt
      let survivors := (Icc 1 y).filter fun m =>
        ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])
      let primes := (Ioc z x).filter Nat.Prime
      primes.card < survivors.card

/-- A partial assignment to groups of at least two survivors leaves more
unassigned survivors than unused primes. The function `f` labels each survivor
in `U` by its assigned prime, counting each position once. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ x : ℕ in atTop, ∀ a : ℕ → ℕ,
      let y := ⌊(x : ℝ) * Real.log x ^ (2 + ε)⌋₊ + 1
      let z := min x y.sqrt
      let survivors := (Icc 1 y).filter fun m =>
        ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])
      let primes := (Ioc z x).filter Nat.Prime
      ∀ (U : Finset ℕ) (f : ℕ → ℕ), U.Nonempty → U ⊆ survivors → U.image f ⊆ primes →
        (∀ m ∈ U, ∃ n ∈ U, n ≠ m ∧ f n = f m) →
        (∀ m ∈ U, ∀ n ∈ U, f m = f n → m ≡ n [MOD f m]) →
        U.card + (primes \ U.image f).card < survivors.card

theorem main : H1 → H2 → type_of% @Erdos687.erdos_687.variants.maier_pomerance := by
  intro hSingleton hPacking ε hε
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [hSingleton ε hε, hPacking ε hε] with x hSingletonX hPackingX
  let scale : ℝ := (x : ℝ) * Real.log x ^ (2 + ε)
  have hscale : 0 ≤ scale :=
    mul_nonneg (Nat.cast_nonneg x) (Real.rpow_nonneg (Real.log_natCast_nonneg x) _)
  have hY : Erdos687.Y x ≤ ⌊scale⌋₊ := by
    apply Y_le_of_not_coverable_succ
    intro hCover
    obtain ⟨a, h⟩ := (cover_iff_packing_budget (min_le_left x (⌊scale⌋₊ + 1).sqrt)).mp hCover
    dsimp only [scale] at h
    rcases h with h | ⟨U, f, hNonempty, hU, hImage, hMulti, hClasses, hBudget⟩
    · exact (not_le_of_gt (hSingletonX a)) h
    · exact (not_le_of_gt (hPackingX a U f hNonempty hU hImage hMulti hClasses)) hBudget
  have hYReal : (Erdos687.Y x : ℝ) ≤ scale :=
    (Nat.cast_le.mpr hY).trans (Nat.floor_le hscale)
  change ‖(Erdos687.Y x : ℝ)‖ ≤ 1 * ‖scale‖
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg hscale, one_mul]

private theorem eventually_not_covered
    (hmp : type_of% @Erdos687.erdos_687.variants.maier_pomerance)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      ¬ Green46.IsCoveredByResidues x (⌊(x : ℝ) * Real.log x ^ (2 + ε)⌋₊ + 1) := by
  have he : 0 < ε / 2 := half_pos hε
  obtain ⟨C, hbound⟩ := isBigO_iff.mp (hmp (ε / 2) he)
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrowth : Tendsto (fun x : ℕ => Real.log (x : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop he).comp hlog
  filter_upwards [hbound, hgrowth.eventually_ge_atTop C, hlog.eventually_gt_atTop 0]
    with x hY hC hlogx
  have hsmall : 0 ≤ (x : ℝ) * Real.log x ^ (2 + ε / 2) := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (Erdos687.Y x)),
    abs_of_nonneg hsmall] at hY
  have hub : (Erdos687.Y x : ℝ) ≤ (x : ℝ) * Real.log x ^ (2 + ε) := calc
    _ ≤ C * ((x : ℝ) * Real.log x ^ (2 + ε / 2)) := hY
    _ ≤ Real.log x ^ (ε / 2) * ((x : ℝ) * Real.log x ^ (2 + ε / 2)) :=
      mul_le_mul_of_nonneg_right hC hsmall
    _ = (x : ℝ) * (Real.log x ^ (2 + ε / 2) * Real.log x ^ (ε / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add hlogx, show (2 + ε / 2) + ε / 2 = 2 + ε by ring]
  intro hCover
  have hCoveredLe : _ ≤ Erdos687.Y x :=
    le_csSup ⟨primorial x, fun _ hh => (Erdos687.lt_primorial_of_isCoveredByResidues hh).le⟩ hCover
  exact (Nat.not_succ_le_self _) (hCoveredLe.trans (Nat.le_floor hub))

/-- Every bound in the conjecture implies both packing hypotheses. Passing from
`ε / 2` to `ε` absorbs the Big-O constant at the specified interval length. -/
theorem hypotheses_of_maier_pomerance
    (hmp : type_of% @Erdos687.erdos_687.variants.maier_pomerance) : H1 ∧ H2 := by
  constructor
  · intro ε hε
    filter_upwards [eventually_not_covered hmp ε hε] with x hx
    intro a
    apply lt_of_not_ge
    intro h
    let y := ⌊(x : ℝ) * Real.log x ^ (2 + ε)⌋₊ + 1
    exact hx ((cover_iff_packing_budget (y := y) (min_le_left x y.sqrt)).mpr ⟨a, Or.inl h⟩)
  · intro ε hε
    filter_upwards [eventually_not_covered hmp ε hε] with x hx
    intro a
    dsimp only
    intro U f hNonempty hU hImage hMulti hClasses
    apply lt_of_not_ge
    intro h
    let y := ⌊(x : ℝ) * Real.log x ^ (2 + ε)⌋₊ + 1
    exact hx ((cover_iff_packing_budget (y := y) (min_le_left x y.sqrt)).mpr
      ⟨a, Or.inr ⟨U, f, hNonempty, hU, hImage, hMulti, hClasses, h⟩⟩)

end OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2
