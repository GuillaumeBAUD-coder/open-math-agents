import OMAStatements.S_oeis_a278415

-- Problem: A278415: a(n) = Sum_{k=0..n} binomial(n, 2k)*binomial(n-k, k)*(-1)^k.
-- Upstream: formal-conjectures statements/oeis-a278415.lean:0 (declaration OMA.S_oeis_a278415.main)
-- Credit: Daniel Whorlow (@draonbioetl)

namespace OMA_A278415

open Finset PowerSeries

private abbrev a_seq := OMA.S_oeis_a278415.a

/-! ### Section 1: p-adic integrality predicates on ℚ and PowerSeries ℚ -/

private def IsPInt (p : ℕ) (q : ℚ) : Prop := ¬ p ∣ q.den

private lemma isPInt_zero (p : ℕ) (hp : p.Prime) : IsPInt p 0 := by
  unfold IsPInt
  simp [hp.not_dvd_one]

private lemma isPInt_one (p : ℕ) (hp : p.Prime) : IsPInt p 1 := by
  unfold IsPInt
  simp [hp.not_dvd_one]

private lemma isPInt_intCast (p : ℕ) (hp : p.Prime) (z : ℤ) : IsPInt p (z : ℚ) := by
  unfold IsPInt
  simp [hp.not_dvd_one]

private lemma isPInt_natCast (p : ℕ) (hp : p.Prime) (n : ℕ) : IsPInt p (n : ℚ) := by
  unfold IsPInt
  simp [hp.not_dvd_one]

private lemma isPInt_div_nat {p : ℕ} (hp : p.Prime) (z : ℤ) {m : ℕ} (hm : ¬ p ∣ m) :
    IsPInt p ((z : ℚ) / (m : ℚ)) := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hden : (((z : ℚ) / (m : ℚ)).den) ∣ m := by
    have hq : (z : ℚ) / (m : ℚ) = Rat.divInt z m := by
      rw [Rat.divInt_eq_div]; push_cast; rfl
    rw [hq]
    exact Int.ofNat_dvd.mp (Rat.den_dvd z m)
  exact fun hd => hm (dvd_trans hd hden)

private lemma isPInt_neg {p : ℕ} {q : ℚ} (hq : IsPInt p q) : IsPInt p (-q) := by
  unfold IsPInt at *
  simpa using hq

private lemma isPInt_add {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : IsPInt p x) (hy : IsPInt p y) : IsPInt p (x + y) := by
  have hden : (x + y).den ∣ x.den * y.den := by
    have heq : x + y = Rat.divInt (x.num * y.den + y.num * x.den) (x.den * y.den) := by
      rw [Rat.divInt_eq_div]
      push_cast
      have hx0 : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
      have hy0 : (y.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr y.den_nz
      field_simp [hx0, hy0]
      calc (x + y) * (y.den : ℚ) * (x.den : ℚ)
          = (x * (x.den : ℚ)) * (y.den : ℚ) + (y * (y.den : ℚ)) * (x.den : ℚ) := by ring
        _ = (x.num : ℚ) * (y.den : ℚ) + (y.num : ℚ) * (x.den : ℚ) := by
            rw [Rat.mul_den_eq_num, Rat.mul_den_eq_num]
    rw [heq]
    exact Int.ofNat_dvd.mp (by simpa using Rat.den_dvd (x.num * y.den + y.num * x.den) (x.den * y.den))
  intro hd
  have hmul : p ∣ x.den * y.den := dvd_trans hd hden
  rcases hp.dvd_mul.mp hmul with h1 | h2
  · exact hx h1
  · exact hy h2

private lemma isPInt_sub {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : IsPInt p x) (hy : IsPInt p y) : IsPInt p (x - y) := by
  rw [sub_eq_add_neg]
  exact isPInt_add hp hx (isPInt_neg hy)

private lemma isPInt_mul {p : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : IsPInt p x) (hy : IsPInt p y) : IsPInt p (x * y) := by
  have hden : (x * y).den ∣ x.den * y.den := by
    have heq : x * y = Rat.divInt (x.num * y.num) (x.den * y.den) := by
      rw [Rat.divInt_eq_div]
      push_cast
      have hx0 : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
      have hy0 : (y.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr y.den_nz
      field_simp [hx0, hy0]
      calc x * y * (x.den : ℚ) * (y.den : ℚ)
          = (x * (x.den : ℚ)) * (y * (y.den : ℚ)) := by ring
        _ = (x.num : ℚ) * (y.num : ℚ) := by rw [Rat.mul_den_eq_num, Rat.mul_den_eq_num]
    rw [heq]
    exact Int.ofNat_dvd.mp (by simpa using Rat.den_dvd (x.num * y.num) (x.den * y.den))
  intro hd
  have hmul : p ∣ x.den * y.den := dvd_trans hd hden
  rcases hp.dvd_mul.mp hmul with h1 | h2
  · exact hx h1
  · exact hy h2

private lemma isPInt_pow {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : IsPInt p x) :
    ∀ k : ℕ, IsPInt p (x ^ k)
  | 0 => by simpa using isPInt_one p hp
  | k + 1 => by rw [pow_succ]; exact isPInt_mul hp (isPInt_pow hp hx k) hx

private lemma isPInt_sum {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsPInt p (f i)) : IsPInt p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPInt_zero p hp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isPInt_add hp (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private def HasPVal (p : ℕ) (k : ℕ) (q : ℚ) : Prop :=
  IsPInt p (q / (p : ℚ) ^ k)

private lemma hasPVal_zero_iff {p : ℕ} (q : ℚ) : HasPVal p 0 q ↔ IsPInt p q := by
  simp [HasPVal]

private lemma hasPVal_mono {p a b : ℕ} (hp : p.Prime) (hab : a ≤ b) {q : ℚ}
    (hq : HasPVal p b q) : HasPVal p a q := by
  unfold HasPVal at *
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have heq : q / (p : ℚ) ^ a = (q / (p : ℚ) ^ b) * (p : ℚ) ^ (b - a) := by
    rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hp0)]
    rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hp0)]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hab]
  rw [heq]
  exact isPInt_mul hp hq (isPInt_pow hp (isPInt_natCast p hp p) (b - a))

private lemma hasPVal_add {p k : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : HasPVal p k x) (hy : HasPVal p k y) : HasPVal p k (x + y) := by
  unfold HasPVal at *
  rw [add_div]
  exact isPInt_add hp hx hy

private lemma hasPVal_mul {p a b : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : HasPVal p a x) (hy : HasPVal p b y) : HasPVal p (a + b) (x * y) := by
  unfold HasPVal at *
  rw [pow_add, ← div_mul_div_comm]
  exact isPInt_mul hp hx hy

private lemma hasPVal_sum {ι : Type*} {p k : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, HasPVal p k (f i)) : HasPVal p k (∑ i ∈ s, f i) := by
  unfold HasPVal at *
  rw [Finset.sum_div]
  exact isPInt_sum hp s _ hf

private lemma hasPVal_natCast_of_dvd {p k n : ℕ} (hp : p.Prime) (hd : p ^ k ∣ n) :
    HasPVal p k (n : ℚ) := by
  rcases hd with ⟨m, rfl⟩
  unfold HasPVal
  have hp0 : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  push_cast
  rw [mul_div_cancel_left₀ _ hp0]
  exact isPInt_natCast p hp m

private lemma hasPVal_div_nat {p k : ℕ} (hp : p.Prime) {q : ℚ} {m : ℕ}
    (hm : m ≠ 0) (hq : HasPVal p (k + padicValNat p m) q) :
    HasPVal p k (q / (m : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set v := padicValNat p m
  have hdvd : p ^ v ∣ m := pow_padicValNat_dvd
  rcases hdvd with ⟨u, hu⟩
  have hu_ndvd : ¬ p ∣ u := by
    intro hpu
    have h1 : p ^ (v + 1) ∣ m := by
      rw [hu, pow_succ]
      exact mul_dvd_mul_left (p ^ v) hpu
    have h2 : v + 1 ≤ padicValNat p m := (padicValNat_dvd_iff_le hm).mp h1
    omega
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  unfold HasPVal at *
  have heq : (q / (m : ℚ)) / (p : ℚ) ^ k = (q / (p : ℚ) ^ (k + v)) * ((1 : ℤ) / (u : ℚ)) := by
    rw [hu]
    push_cast
    rw [pow_add]
    have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hu_ndvd (h ▸ dvd_zero p))
    field_simp [hp0, hu0]
  rw [heq]
  exact isPInt_mul hp hq (isPInt_div_nat hp 1 hu_ndvd)

private lemma isPInt_div_of_hasPVal {p n : ℕ} (hp : p.Prime) (hn : 0 < n) {q : ℚ}
    (hq : HasPVal p (2 * padicValNat p (p * n)) q) :
    IsPInt p (q / ((p : ℚ) * (n : ℚ)) ^ 2) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpn0 : p * n ≠ 0 := mul_ne_zero hp.ne_zero hn.ne'
  have hsq0 : (p * n) ^ 2 ≠ 0 := pow_ne_zero 2 hpn0
  have hv : padicValNat p ((p * n) ^ 2) = 2 * padicValNat p (p * n) := by
    rw [sq, padicValNat.mul hpn0 hpn0, two_mul]
  have h1 : HasPVal p (0 + padicValNat p ((p * n) ^ 2)) q := by
    rw [zero_add, hv]; exact hq
  have h2 := hasPVal_div_nat hp hsq0 h1
  rw [hasPVal_zero_iff] at h2
  simpa [Nat.cast_pow, Nat.cast_mul] using h2

private def SeriesPInt (p : ℕ) (F : PowerSeries ℚ) : Prop :=
  ∀ k : ℕ, IsPInt p (PowerSeries.coeff k F)

private lemma seriesPInt_zero {p : ℕ} (hp : p.Prime) : SeriesPInt p 0 := fun _ => by
  simp [isPInt_zero p hp]

private lemma seriesPInt_one {p : ℕ} (hp : p.Prime) : SeriesPInt p 1 := fun k => by
  by_cases hk : k = 0
  · subst hk; simp [isPInt_one p hp]
  · simp [PowerSeries.coeff_one, hk, isPInt_zero p hp]

private lemma seriesPInt_X {p : ℕ} (hp : p.Prime) : SeriesPInt p PowerSeries.X := fun k => by
  by_cases hk : k = 1
  · subst hk; simp [isPInt_one p hp]
  · simp [PowerSeries.coeff_X, hk, isPInt_zero p hp]

private lemma seriesPInt_add {p : ℕ} (hp : p.Prime) {F G : PowerSeries ℚ}
    (hF : SeriesPInt p F) (hG : SeriesPInt p G) : SeriesPInt p (F + G) := fun k => by
  rw [map_add]
  exact isPInt_add hp (hF k) (hG k)

private lemma seriesPInt_mul {p : ℕ} (hp : p.Prime) {F G : PowerSeries ℚ}
    (hF : SeriesPInt p F) (hG : SeriesPInt p G) : SeriesPInt p (F * G) := fun k => by
  rw [PowerSeries.coeff_mul]
  exact isPInt_sum hp _ _ fun x _ => isPInt_mul hp (hF x.1) (hG x.2)

private lemma seriesPInt_pow {p : ℕ} (hp : p.Prime) {F : PowerSeries ℚ}
    (hF : SeriesPInt p F) : ∀ n : ℕ, SeriesPInt p (F ^ n)
  | 0 => by simpa using seriesPInt_one hp
  | n + 1 => by rw [pow_succ]; exact seriesPInt_mul hp (seriesPInt_pow hp hF n) hF

/-! ### Section 2: Power Series Operators (psDeriv, psExpand, psCartier, psExp0) -/

private noncomputable def psDeriv (F : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => ((k + 1 : ℕ) : ℚ) * PowerSeries.coeff (k + 1) F

@[simp]
private lemma coeff_psDeriv (F : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k (psDeriv F) = ((k + 1 : ℕ) : ℚ) * PowerSeries.coeff (k + 1) F := by
  simp [psDeriv]

private lemma psDeriv_add (F G : PowerSeries ℚ) :
    psDeriv (F + G) = psDeriv F + psDeriv G := by
  ext k; simp [mul_add]

private lemma psDeriv_sub (F G : PowerSeries ℚ) :
    psDeriv (F - G) = psDeriv F - psDeriv G := by
  ext k; simp [mul_sub]

private lemma psDeriv_smul (c : ℚ) (F : PowerSeries ℚ) :
    psDeriv (c • F) = c • psDeriv F := by
  ext k; simp; ring

private lemma psDeriv_C (c : ℚ) : psDeriv (PowerSeries.C c) = 0 := by
  ext k; simp

private lemma psDeriv_one : psDeriv (1 : PowerSeries ℚ) = 0 := by
  ext k; simp [PowerSeries.coeff_one]

private lemma psDeriv_X : psDeriv (PowerSeries.X : PowerSeries ℚ) = 1 := by
  ext k
  by_cases hk : k = 0
  · subst hk; simp
  · simp [PowerSeries.coeff_X, PowerSeries.coeff_one, hk]

private lemma psDeriv_mul (F G : PowerSeries ℚ) :
    psDeriv (F * G) = psDeriv F * G + F * psDeriv G := by
  ext k
  rw [coeff_psDeriv, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i F * coeff j G) (k + 1)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (psDeriv F) * coeff j G) k]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i F * coeff j (psDeriv G)) k]
  simp only [coeff_psDeriv]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_cancel, Nat.sub_zero]
  have hsplit :
      ((k + 1 : ℕ) : ℚ) * (∑ x ∈ Finset.range (k + 1), coeff (x + 1) F * coeff (k + 1 - (x + 1)) G +
        coeff 0 F * coeff (k + 1) G) =
      ∑ x ∈ Finset.range (k + 1), ((x + 1 : ℕ) : ℚ) * coeff (x + 1) F * coeff (k - x) G +
      (∑ x ∈ Finset.range (k + 1), ((k - x : ℕ) : ℚ) * coeff (x + 1) F * coeff (k - x) G +
        ((k + 1 : ℕ) : ℚ) * coeff 0 F * coeff (k + 1) G) := by
    rw [mul_add, Finset.mul_sum]
    have hsum : ∑ x ∈ Finset.range (k + 1), ((k + 1 : ℕ) : ℚ) * (coeff (x + 1) F * coeff (k + 1 - (x + 1)) G) =
        ∑ x ∈ Finset.range (k + 1), (((x + 1 : ℕ) : ℚ) * coeff (x + 1) F * coeff (k - x) G +
          ((k - x : ℕ) : ℚ) * coeff (x + 1) F * coeff (k - x) G) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxk : x ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      have hsub : k + 1 - (x + 1) = k - x := by omega
      have hadd : ((k + 1 : ℕ) : ℚ) = ((x + 1 : ℕ) : ℚ) + ((k - x : ℕ) : ℚ) := by
        exact_mod_cast (show k + 1 = (x + 1) + (k - x) by omega)
      rw [hsub, hadd]
      ring
    rw [hsum, Finset.sum_add_distrib]
    ring
  rw [hsplit]
  congr 1
  -- Show second sum matches ∑_{x=0}^k coeff x F * (k - x + 1) * coeff (k - x + 1) G
  have h2 : ∑ x ∈ Finset.range (k + 1), coeff x F * (((k - x + 1 : ℕ) : ℚ) * coeff (k - x + 1) G) =
      ∑ x ∈ Finset.range (k + 1), ((k - x : ℕ) : ℚ) * coeff (x + 1) F * coeff (k - x) G +
        ((k + 1 : ℕ) : ℚ) * coeff 0 F * coeff (k + 1) G := by
    rw [Finset.sum_range_succ', Nat.sub_zero]
    congr 1
    · rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxk : x < k := Finset.mem_range.mp hx
      have hsub : k - (x + 1) + 1 = k - x := by omega
      rw [hsub]
      ring
    · ring
  rw [h2]

private lemma psDeriv_pow (F : PowerSeries ℚ) :
    ∀ n : ℕ, psDeriv (F ^ n) = (n : ℚ) • (F ^ (n - 1) * psDeriv F)
  | 0 => by simp [psDeriv_one]
  | 1 => by simp
  | n + 2 => by
    rw [pow_succ, psDeriv_mul, psDeriv_pow F (n + 1), Nat.add_sub_cancel, show n + 2 - 1 = n + 1 by omega]
    have h1 : ((n + 1 : ℕ) : ℚ) • (F ^ n * psDeriv F) * F =
        ((n + 1 : ℕ) : ℚ) • (F ^ (n + 1) * psDeriv F) := by
      rw [smul_mul_assoc]; congr 1; rw [pow_succ]; ring
    rw [h1]
    ext k
    simp only [map_add, map_smul, smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

private lemma seriesPInt_psDeriv {p : ℕ} (hp : p.Prime) {F : PowerSeries ℚ}
    (hF : SeriesPInt p F) : SeriesPInt p (psDeriv F) := fun k => by
  rw [coeff_psDeriv]
  exact isPInt_mul hp (isPInt_natCast p hp (k + 1)) (hF (k + 1))

private lemma coeff_X_mul_psDeriv (F : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X * psDeriv F) = (n : ℚ) * PowerSeries.coeff n F := by
  cases n with
  | zero => simp
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, coeff_psDeriv]

private lemma eq_of_ode_unique {A Y₁ Y₂ : PowerSeries ℚ}
    (h0 : PowerSeries.coeff 0 Y₁ = PowerSeries.coeff 0 Y₂)
    (h1 : psDeriv Y₁ = A * Y₁) (h2 : psDeriv Y₂ = A * Y₂) : Y₁ = Y₂ := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => exact h0
    | succ k =>
      have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      apply mul_left_cancel₀ hk
      rw [← coeff_psDeriv Y₁ k, ← coeff_psDeriv Y₂ k, h1, h2]
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j Y₁) k,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j Y₂) k]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : k - i < k + 1 := by omega
      rw [ih (k - i) hik]

private noncomputable def psExpand (p : ℕ) (F : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => if p ∣ k then PowerSeries.coeff (k / p) F else 0

private lemma coeff_psExpand (p : ℕ) (F : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k (psExpand p F) = if p ∣ k then PowerSeries.coeff (k / p) F else 0 := by
  simp [psExpand]

private lemma psExpand_one (p : ℕ) (hp : 0 < p) : psExpand p 1 = 1 := by
  ext k
  rw [coeff_psExpand]
  by_cases hk : k = 0
  · subst hk; simp
  · by_cases hd : p ∣ k
    · rcases hd with ⟨m, rfl⟩
      have hm : m ≠ 0 := fun h => hk (by simp [h])
      simp [Nat.mul_div_cancel_left m hp, PowerSeries.coeff_one, hk, hm]
    · simp [hd, PowerSeries.coeff_one, hk]

private lemma psExpand_mul (p : ℕ) (hp : 0 < p) (F G : PowerSeries ℚ) :
    psExpand p (F * G) = psExpand p F * psExpand p G := by
  ext k
  rw [coeff_psExpand]
  by_cases hd : p ∣ k
  · rcases hd with ⟨m, rfl⟩
    simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left m hp, PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i F * coeff j G) m]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (psExpand p F) * coeff j (psExpand p G)) (p * m)]
    symm
    refine Finset.sum_bij_ne_zero (fun i _ _ => i / p) ?_ ?_ ?_ ?_
    · intro i hi hne
      rw [coeff_psExpand] at hne
      have hpi : p ∣ i := by by_contra h; simp [h] at hne
      have him : i ≤ p * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rcases hpi with ⟨q, rfl⟩
      rw [Nat.mul_div_cancel_left q hp, Finset.mem_range]
      have : q ≤ m := Nat.le_of_mul_le_mul_left him hp
      omega
    · intro i₁ _ hne₁ i₂ _ hne₂ heq
      rw [coeff_psExpand] at hne₁ hne₂
      have h1 : p ∣ i₁ := by by_contra h; simp [h] at hne₁
      have h2 : p ∣ i₂ := by by_contra h; simp [h] at hne₂
      rcases h1 with ⟨q₁, rfl⟩
      rcases h2 with ⟨q₂, rfl⟩
      rw [Nat.mul_div_cancel_left q₁ hp, Nat.mul_div_cancel_left q₂ hp] at heq
      rw [heq]
    · intro q hq hne
      have hqm : q ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
      refine ⟨p * q, Finset.mem_range.mpr (by nlinarith), ?_, Nat.mul_div_cancel_left q hp⟩
      rw [coeff_psExpand, coeff_psExpand]
      have hsub : p * m - p * q = p * (m - q) := (Nat.mul_sub_left_distrib p m q).symm
      rw [hsub]
      simp [Nat.mul_div_cancel_left _ hp, hne]
    · intro i _ hne
      rw [coeff_psExpand] at hne
      have hpi : p ∣ i := by by_contra h; simp [h] at hne
      rcases hpi with ⟨q, rfl⟩
      have hsub : p * m - p * q = p * (m - q) := (Nat.mul_sub_left_distrib p m q).symm
      rw [coeff_psExpand, coeff_psExpand, hsub]
      simp [Nat.mul_div_cancel_left _ hp]
  · simp only [hd, ↓reduceIte]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (psExpand p F) * coeff j (psExpand p G)) k]
    symm
    refine Finset.sum_eq_zero fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [coeff_psExpand, coeff_psExpand]
    by_cases h1 : p ∣ i
    · have h2 : ¬ p ∣ k - i := fun h2 => hd (by rw [← Nat.add_sub_of_le hik]; exact dvd_add h1 h2)
      simp [h1, h2]
    · simp [h1]

private lemma psExpand_pow (p : ℕ) (hp : 0 < p) (F : PowerSeries ℚ) :
    ∀ n : ℕ, psExpand p (F ^ n) = (psExpand p F) ^ n
  | 0 => by simp [psExpand_one p hp]
  | n + 1 => by rw [pow_succ, pow_succ, psExpand_mul p hp, psExpand_pow p hp F n]

private lemma psDeriv_psExpand (p : ℕ) (hp : 0 < p) (F : PowerSeries ℚ) :
    psDeriv (psExpand p F) = (p : ℚ) • (PowerSeries.X ^ (p - 1) * psExpand p (psDeriv F)) := by
  ext k
  rw [coeff_psDeriv, coeff_psExpand, map_smul, smul_eq_mul]
  by_cases hd : p ∣ k + 1
  · rcases hd with ⟨m, hm⟩
    have hm_pos : 0 < m := by
      by_contra h0
      have : m = 0 := by omega
      subst this; omega
    have hk_ge : p - 1 ≤ k := by have : p ≤ p * m := Nat.le_mul_of_pos_right p hm_pos; omega
    have hsub : k - (p - 1) = p * (m - 1) := by
      have : p * m = p * (m - 1) + p := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega, mul_add, mul_one]
      omega
    rw [if_pos ⟨m, hm⟩, hm, Nat.mul_div_cancel_left m hp]
    rw [PowerSeries.coeff_X_pow_mul']
    rw [if_pos hk_ge, hsub, coeff_psExpand, if_pos (dvd_mul_right p (m - 1))]
    rw [Nat.mul_div_cancel_left (m - 1) hp, coeff_psDeriv]
    rw [show m - 1 + 1 = m by omega]
    push_cast; ring
  · rw [if_neg hd, mul_zero]
    rw [PowerSeries.coeff_X_pow_mul']
    by_cases hk_ge : p - 1 ≤ k
    · rw [if_pos hk_ge, coeff_psExpand]
      have hnd : ¬ p ∣ k - (p - 1) := by
        intro ⟨m, hm⟩
        apply hd
        refine ⟨m + 1, ?_⟩
        rw [mul_add, mul_one]; omega
      rw [if_neg hnd, mul_zero]
    · rw [if_neg hk_ge, mul_zero]

private noncomputable def psCartier (p : ℕ) (F : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => PowerSeries.coeff (p * k) F

@[simp]
private lemma coeff_psCartier (p : ℕ) (F : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k (psCartier p F) = PowerSeries.coeff (p * k) F := by
  simp [psCartier]

private lemma seriesPInt_psCartier {p : ℕ} {F : PowerSeries ℚ} (hF : SeriesPInt p F) :
    SeriesPInt p (psCartier p F) := fun k => by
  rw [coeff_psCartier]; exact hF (p * k)

private lemma psCartier_expand_mul (p : ℕ) (hp : 0 < p) (A B : PowerSeries ℚ) :
    psCartier p (psExpand p A * B) = A * psCartier p B := by
  ext n
  rw [coeff_psCartier, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (psExpand p A) * coeff j B) (p * n)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j (psCartier p B)) n]
  refine Finset.sum_bij_ne_zero (fun i _ _ => i / p) ?_ ?_ ?_ ?_
  · intro i hi hne
    rw [coeff_psExpand] at hne
    have hpi : p ∣ i := by by_contra h; simp [h] at hne
    rcases hpi with ⟨q, rfl⟩
    have hqn : q ≤ n := Nat.le_of_mul_le_mul_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp
    rw [Nat.mul_div_cancel_left q hp, Finset.mem_range]; omega
  · intro i₁ _ hne₁ i₂ _ hne₂ heq
    rw [coeff_psExpand] at hne₁ hne₂
    have h1 : p ∣ i₁ := by by_contra h; simp [h] at hne₁
    have h2 : p ∣ i₂ := by by_contra h; simp [h] at hne₂
    rcases h1 with ⟨q₁, rfl⟩
    rcases h2 with ⟨q₂, rfl⟩
    rw [Nat.mul_div_cancel_left q₁ hp, Nat.mul_div_cancel_left q₂ hp] at heq
    rw [heq]
  · intro q hq hne
    have hqn : q ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    refine ⟨p * q, Finset.mem_range.mpr (by nlinarith), ?_, Nat.mul_div_cancel_left q hp⟩
    rw [coeff_psExpand]
    have hsub : p * n - p * q = p * (n - q) := (Nat.mul_sub_left_distrib p n q).symm
    rw [hsub, if_pos (dvd_mul_right p q), Nat.mul_div_cancel_left q hp]
    simpa [coeff_psCartier] using hne
  · intro i _ hne
    rw [coeff_psExpand] at hne
    have hpi : p ∣ i := by by_contra h; simp [h] at hne
    rcases hpi with ⟨q, rfl⟩
    have hsub : p * n - p * q = p * (n - q) := (Nat.mul_sub_left_distrib p n q).symm
    rw [coeff_psExpand, if_pos (dvd_mul_right p q), Nat.mul_div_cancel_left q hp, hsub, coeff_psCartier]

/-! ### Section 3: Formal Exponential of a Zero-Constant-Term Power Series -/

private lemma coeff_pow_eq_zero_of_lt {S : PowerSeries ℚ} (hS0 : PowerSeries.coeff 0 S = 0) :
    ∀ {k m : ℕ}, m < k → PowerSeries.coeff m (S ^ k) = 0
  | 0, _, h => by omega
  | k + 1, m, h => by
    rw [pow_succ, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (S ^ k) * coeff j S) m]
    refine Finset.sum_eq_zero fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hmi : m - i = 0
    · rw [hmi, hS0, mul_zero]
    · have hi_lt : i < k := by omega
      rw [coeff_pow_eq_zero_of_lt hS0 hi_lt, zero_mul]

private noncomputable def psExp0 (S : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff m (S ^ k) / (k.factorial : ℚ)

private lemma coeff_psExp0 (S : PowerSeries ℚ) (m : ℕ) :
    PowerSeries.coeff m (psExp0 S) =
      ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff m (S ^ k) / (k.factorial : ℚ) := by
  simp [psExp0]

private lemma coeff_psExp0_eq_sum_ge {S : PowerSeries ℚ} (hS0 : PowerSeries.coeff 0 S = 0)
    {m N : ℕ} (hmN : m ≤ N) :
    PowerSeries.coeff m (psExp0 S) =
      ∑ k ∈ Finset.range (N + 1), PowerSeries.coeff m (S ^ k) / (k.factorial : ℚ) := by
  rw [coeff_psExp0]
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmN)) fun k _ hk => ?_
  have hmk : m < k := by rw [Finset.mem_range] at hk; omega
  rw [coeff_pow_eq_zero_of_lt hS0 hmk, zero_div]

private lemma coeff_zero_psExp0 (S : PowerSeries ℚ) :
    PowerSeries.coeff 0 (psExp0 S) = 1 := by
  simp [coeff_psExp0]

private lemma psDeriv_psExp0 {S : PowerSeries ℚ} (hS0 : PowerSeries.coeff 0 S = 0) :
    psDeriv (psExp0 S) = psDeriv S * psExp0 S := by
  ext m
  rw [coeff_psDeriv, coeff_psExp0, Finset.mul_sum]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_div, mul_zero,
    add_zero]
  have h1 : ∑ k ∈ Finset.range (m + 1),
      ((m + 1 : ℕ) : ℚ) * (coeff (m + 1) (S ^ (k + 1)) / ((k + 1).factorial : ℚ)) =
      ∑ k ∈ Finset.range (m + 1), coeff m (psDeriv S * S ^ k) / (k.factorial : ℚ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hdp := psDeriv_pow S (k + 1)
    have hcoeff : ((m + 1 : ℕ) : ℚ) * coeff (m + 1) (S ^ (k + 1)) =
        ((k + 1 : ℕ) : ℚ) * coeff m (S ^ k * psDeriv S) := by
      rw [← coeff_psDeriv, hdp, Nat.add_sub_cancel, map_smul, smul_eq_mul]
    rw [mul_div_assoc', hcoeff, Nat.factorial_succ, mul_comm (S ^ k) (psDeriv S)]
    push_cast
    have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
    field_simp [hk1]
  rw [h1]
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (psDeriv S) * coeff j (psExp0 S)) m]
  have h2 : ∑ i ∈ Finset.range (m + 1), coeff i (psDeriv S) * coeff (m - i) (psExp0 S) =
      ∑ i ∈ Finset.range (m + 1),
        ∑ k ∈ Finset.range (m + 1), coeff i (psDeriv S) * (coeff (m - i) (S ^ k) / (k.factorial : ℚ)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : m - i ≤ m := Nat.sub_le m i
    rw [coeff_psExp0_eq_sum_ge hS0 him, Finset.mul_sum]
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (psDeriv S) * coeff j (S ^ k)) m,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma psExp0_add {S T : PowerSeries ℚ}
    (hS0 : PowerSeries.coeff 0 S = 0) (hT0 : PowerSeries.coeff 0 T = 0) :
    psExp0 (S + T) = psExp0 S * psExp0 T := by
  have hST0 : PowerSeries.coeff 0 (S + T) = 0 := by rw [map_add, hS0, hT0, add_zero]
  refine eq_of_ode_unique (A := psDeriv (S + T)) ?_ ?_ ?_
  · rw [coeff_zero_psExp0, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_psExp0, coeff_zero_psExp0, mul_one]
  · exact psDeriv_psExp0 hST0
  · rw [psDeriv_mul, psDeriv_psExp0 hS0, psDeriv_psExp0 hT0, psDeriv_add]
    ring

private lemma psExp0_nsmul {S : PowerSeries ℚ} (hS0 : PowerSeries.coeff 0 S = 0) :
    ∀ n : ℕ, psExp0 ((n : ℚ) • S) = (psExp0 S) ^ n
  | 0 => by
    ext k
    simp only [Nat.cast_zero, zero_smul, pow_zero, coeff_psExp0, PowerSeries.coeff_one]
    cases k with
    | zero => simp
    | succ m =>
      rw [Finset.sum_range_succ']
      simp [zero_pow]
  | n + 1 => by
    have hns0 : PowerSeries.coeff 0 ((n : ℚ) • S) = 0 := by simp [hS0]
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul, psExp0_add hns0 hS0,
      psExp0_nsmul hS0 n, pow_succ]

/-! ### Section 4: Generating Function Identity a(n) = [X^n] (f^n * h) -/

private noncomputable def h_ps : PowerSeries ℚ :=
  PowerSeries.mk fun k => if k % 2 = 0 then (-1 : ℚ) ^ (k / 2) else 0

private noncomputable def f_ps : PowerSeries ℚ :=
  1 + PowerSeries.X * h_ps

private lemma coeff_h_ps (k : ℕ) :
    PowerSeries.coeff k h_ps = if k % 2 = 0 then (-1 : ℚ) ^ (k / 2) else 0 := by
  simp [h_ps]

private lemma seriesPInt_h_ps {p : ℕ} (hp : p.Prime) : SeriesPInt p h_ps := fun k => by
  rw [coeff_h_ps]
  split_ifs
  · exact isPInt_pow hp (isPInt_neg (isPInt_one p hp)) _
  · exact isPInt_zero p hp

private lemma seriesPInt_f_ps {p : ℕ} (hp : p.Prime) : SeriesPInt p f_ps :=
  seriesPInt_add hp (seriesPInt_one hp) (seriesPInt_mul hp (seriesPInt_X hp) (seriesPInt_h_ps hp))

private lemma one_add_X_sq_mul_h_ps :
    (1 + PowerSeries.X ^ 2) * h_ps = 1 := by
  ext k
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_X_pow_mul']
  cases k with
  | zero => simp [coeff_h_ps]
  | succ k1 =>
    cases k1 with
    | zero => simp [coeff_h_ps]
    | succ m =>
      have hge : 2 ≤ m + 1 + 1 := by omega
      rw [if_pos hge, show m + 1 + 1 - 2 = m by omega, coeff_h_ps, coeff_h_ps]
      have hmod : (m + 1 + 1) % 2 = m % 2 := by omega
      rw [hmod, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero _)]
      split_ifs with h
      · rw [show (m + 1 + 1) / 2 = m / 2 + 1 by omega, pow_succ]
        ring
      · ring

private lemma one_add_X_sq_mul_f_ps :
    (1 + PowerSeries.X ^ 2) * f_ps = 1 + PowerSeries.X + PowerSeries.X ^ 2 := by
  unfold f_ps
  calc
    (1 + PowerSeries.X ^ 2) * (1 + PowerSeries.X * h_ps)
      = (1 + PowerSeries.X ^ 2) + PowerSeries.X * ((1 + PowerSeries.X ^ 2) * h_ps) := by ring
    _ = (1 + PowerSeries.X ^ 2) + PowerSeries.X * 1 := by rw [one_add_X_sq_mul_h_ps]
    _ = 1 + PowerSeries.X + PowerSeries.X ^ 2 := by ring

private lemma coeff_h_ps_pow (j : ℕ) :
    ∀ m : ℕ, PowerSeries.coeff m (h_ps ^ (j + 1)) =
      if m % 2 = 0 then (-1 : ℚ) ^ (m / 2) * ((j + m / 2).choose (m / 2) : ℚ) else 0 := by
  induction j with
  | zero =>
    intro m
    simp [coeff_h_ps]
  | succ j ih =>
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      have hrel : (1 + PowerSeries.X ^ 2) * h_ps ^ (j + 2) = h_ps ^ (j + 1) := by
        calc
          (1 + PowerSeries.X ^ 2) * h_ps ^ (j + 2)
            = ((1 + PowerSeries.X ^ 2) * h_ps) * h_ps ^ (j + 1) := by rw [pow_succ]; ring
          _ = 1 * h_ps ^ (j + 1) := by rw [one_add_X_sq_mul_h_ps]
          _ = h_ps ^ (j + 1) := one_mul _
      have hcoeff := congrArg (PowerSeries.coeff m) hrel
      rw [add_mul, one_mul, map_add, PowerSeries.coeff_X_pow_mul'] at hcoeff
      cases m with
      | zero =>
        simp only [show ¬(2 ≤ 0) by omega, ↓reduceIte, add_zero] at hcoeff
        rw [hcoeff, ih 0]; simp
      | succ m1 =>
        cases m1 with
        | zero =>
          simp only [show ¬(2 ≤ 1) by omega, ↓reduceIte, add_zero] at hcoeff
          rw [hcoeff, ih 1]; simp
        | succ r =>
          have hge : 2 ≤ r + 2 := by omega
          rw [if_pos hge, show r + 1 + 1 - 2 = r by omega] at hcoeff
          have hr_ih := ihm r (by omega)
          have hgoal : coeff (r + 2) (h_ps ^ (j + 2)) =
              coeff (r + 2) (h_ps ^ (j + 1)) - coeff r (h_ps ^ (j + 2)) := by linarith
          rw [hgoal, ih (r + 2), hr_ih]
          have hmod : (r + 2) % 2 = r % 2 := by omega
          rw [hmod]
          split_ifs with h
          · set s := r / 2
            have hs : (r + 2) / 2 = s + 1 := by omega
            rw [hs, pow_succ]
            have hpas : ((j + 1 + (s + 1)).choose (s + 1) : ℚ) =
                ((j + (s + 1)).choose (s + 1) : ℚ) + ((j + (s + 1)).choose s : ℚ) := by
              have h1 : j + 1 + (s + 1) = (j + (s + 1)) + 1 := by omega
              rw [h1, Nat.choose_succ_succ]
              push_cast; ring
            have h2 : j + (s + 1) = j + 1 + s := by omega
            rw [hpas, h2]
            ring
          · ring

private lemma a_seq_eq_coeff (n : ℕ) :
    (a_seq n : ℚ) = PowerSeries.coeff n (f_ps ^ n * h_ps) := by
  have hexp : f_ps ^ n * h_ps =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℚ) • (PowerSeries.X ^ j * h_ps ^ (j + 1)) := by
    unfold f_ps
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, mul_pow, pow_succ, PowerSeries.smul_eq_C_mul,
      PowerSeries.C_eq_algebraMap, map_natCast]
    ring
  rw [hexp, map_sum]
  unfold a_seq OMA.S_oeis_a278415.a
  push_cast
  symm
  -- Match terms: j = n - 2*k (where 2*k ≤ n)
  refine Finset.sum_bij_ne_zero (fun j _ _ => (n - j) / 2) ?_ ?_ ?_ ?_
  · intro j hj _
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Finset.mem_range]; omega
  · intro j₁ hj₁ hne₁ j₂ hj₂ hne₂ heq
    have h1 : j₁ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₁)
    have h2 : j₂ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₂)
    simp only [map_smul, smul_eq_mul, PowerSeries.coeff_X_pow_mul', h1, h2, ↓reduceIte,
      coeff_h_ps_pow] at hne₁ hne₂
    have hev₁ : (n - j₁) % 2 = 0 := by by_contra h; simp [h] at hne₁
    have hev₂ : (n - j₂) % 2 = 0 := by by_contra h; simp [h] at hne₂
    omega
  · intro k hk hne
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h2k : 2 * k ≤ n := by
      by_contra h
      have : n.choose (2 * k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [this] at hne
    refine ⟨n - 2 * k, Finset.mem_range.mpr (by omega), ?_, by omega⟩
    simp only [map_smul, smul_eq_mul, PowerSeries.coeff_X_pow_mul', show n - 2 * k ≤ n by omega,
      ↓reduceIte, coeff_h_ps_pow, show n - (n - 2 * k) = 2 * k by omega,
      show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega,
      show n - 2 * k + k = n - k by omega]
    rw [Nat.choose_symm h2k]
    intro h0
    apply hne
    linarith
  · intro j hj hne
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [map_smul, smul_eq_mul, PowerSeries.coeff_X_pow_mul', hjn, ↓reduceIte,
      coeff_h_ps_pow] at hne ⊢
    have hev : (n - j) % 2 = 0 := by by_contra h; simp [h] at hne
    rw [if_pos hev]
    set k := (n - j) / 2
    have h2k : 2 * k = n - j := by omega
    have h2k_le : 2 * k ≤ n := by omega
    have hj_eq : j = n - 2 * k := by omega
    have hjk : j + k = n - k := by omega
    rw [hj_eq, Nat.choose_symm h2k_le, show n - 2 * k + k = n - k by omega]
    ring

private lemma psCartier_h_ps {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    psCartier p h_ps = h_ps := by
  have hp_odd : p % 2 = 1 := by
    have := hp.eq_two_or_odd; omega
  ext k
  rw [coeff_psCartier, coeff_h_ps, coeff_h_ps]
  have hmod : (p * k) % 2 = k % 2 := by
    rw [Nat.mul_mod, hp_odd, one_mul, Nat.mod_mod]
  rw [hmod]
  split_ifs with hk
  · have hdiv : (p * k) / 2 = p * (k / 2) := by
      have : k = 2 * (k / 2) := by omega
      conv_lhs => rw [this, ← mul_assoc, mul_comm p 2, mul_assoc]
      exact Nat.mul_div_cancel_left _ (by omega)
    rw [hdiv, pow_mul]
    have hpow : ((-1 : ℚ) ^ p) = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hp_odd)
    rw [hpow]
  · rfl

/-! ### Section 5: Explicit Logarithmic Derivative and psi_ps -/

private def c_seq (N : ℕ) : ℤ :=
  1 - (if 3 ∣ N then 3 else 0) - (if 2 ∣ N then 2 * (-1 : ℤ) ^ (N / 2 - 1) else 0)

private lemma c_seq_mul_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (M : ℕ) (hM : 0 < M) :
    c_seq (p * M) = c_seq M := by
  have hp2 : p % 2 = 1 := by have := hp.eq_two_or_odd; omega
  have hp3 : ¬ 3 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by decide) hp).mp h
    omega
  have h3 : (3 ∣ p * M) ↔ (3 ∣ M) := by
    constructor
    · intro hd
      exact ((Nat.Prime.dvd_mul (by decide)).mp hd).resolve_left hp3
    · exact fun hd => dvd_mul_of_dvd_right hd p
  have h2 : (2 ∣ p * M) ↔ (2 ∣ M) := by
    constructor
    · intro hd
      have hp2' : ¬ 2 ∣ p := by omega
      exact ((Nat.Prime.dvd_mul (by decide)).mp hd).resolve_left hp2'
    · exact fun hd => dvd_mul_of_dvd_right hd p
  unfold c_seq
  rw [if_congr h3 rfl rfl, if_congr h2 rfl rfl]
  congr 1
  split_ifs with hm2
  · rcases hm2 with ⟨q, rfl⟩
    have hq0 : 0 < q := by omega
    have hdiv1 : (p * (2 * q)) / 2 = p * q := by
      rw [← mul_assoc, mul_comm p 2, mul_assoc]
      exact Nat.mul_div_cancel_left _ (by omega)
    have hdiv2 : (2 * q) / 2 = q := Nat.mul_div_cancel_left q (by omega)
    rw [hdiv1, hdiv2]
    have hpar : (p * q - 1) % 2 = (q - 1) % 2 := by
      have : (p * q) % 2 = q % 2 := by rw [Nat.mul_mod, hp2, one_mul, Nat.mod_mod]
      have hpq : 1 ≤ p * q := by nlinarith
      omega
    have heq : (-1 : ℤ) ^ (p * q - 1) = (-1 : ℤ) ^ (q - 1) := by
      rw [← Nat.div_add_mod (p * q - 1) 2, ← Nat.div_add_mod (q - 1) 2, hpar]
      simp [pow_add, pow_mul]
    rw [heq]
  · rfl

private noncomputable def L1_ps : PowerSeries ℚ :=
  PowerSeries.mk fun k => if 3 ∣ (k + 1) then (-2 : ℚ) else 1

private noncomputable def L2_ps : PowerSeries ℚ :=
  PowerSeries.mk fun k => if 2 ∣ (k + 1) then -(2 : ℚ) * (-1 : ℚ) ^ ((k + 1) / 2 - 1) else 0

private noncomputable def Lprime_ps : PowerSeries ℚ :=
  PowerSeries.mk fun k => (c_seq (k + 1) : ℚ)

private lemma Lprime_eq_add : Lprime_ps = L1_ps + L2_ps := by
  ext k
  simp only [Lprime_ps, L1_ps, L2_ps, map_add, coeff_mk, c_seq]
  split_ifs <;> push_cast <;> ring

private lemma poly1_mul_L1 :
    (1 + PowerSeries.X + PowerSeries.X ^ 2) * L1_ps = 1 + (2 : ℚ) • PowerSeries.X := by
  ext k
  have hmul : (1 + PowerSeries.X + PowerSeries.X ^ 2) * L1_ps =
      L1_ps + PowerSeries.X * L1_ps + PowerSeries.X ^ 2 * L1_ps := by ring
  rw [hmul, map_add, map_add]
  cases k with
  | zero =>
    simp [L1_ps]
  | succ k1 =>
    cases k1 with
    | zero =>
      simp [L1_ps, PowerSeries.coeff_X_pow_mul']
      norm_num
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega : 2 ≤ m + 2),
        show m + 1 + 1 - 2 = m by omega]
      simp only [L1_ps, coeff_mk, map_add, map_smul, PowerSeries.coeff_one, PowerSeries.coeff_X,
        show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega, ↓reduceIte, smul_eq_mul, mul_zero,
        add_zero]
      have hmod : (m + 1) % 3 = 0 ∨ (m + 1) % 3 = 1 ∨ (m + 1) % 3 = 2 := by omega
      rcases hmod with h | h | h
      · have h1 : ¬ 3 ∣ (m + 2 + 1) := by omega
        have h2 : ¬ 3 ∣ (m + 1 + 1) := by omega
        have h3 : 3 ∣ (m + 1) := by omega
        simp [h1, h2, h3]; ring
      · have h1 : 3 ∣ (m + 2 + 1) := by omega
        have h2 : ¬ 3 ∣ (m + 1 + 1) := by omega
        have h3 : ¬ 3 ∣ (m + 1) := by omega
        simp [h1, h2, h3]; ring
      · have h1 : ¬ 3 ∣ (m + 2 + 1) := by omega
        have h2 : 3 ∣ (m + 1 + 1) := by omega
        have h3 : ¬ 3 ∣ (m + 1) := by omega
        simp [h1, h2, h3]; ring

private lemma poly2_mul_L2 :
    (1 + PowerSeries.X ^ 2) * L2_ps = -((2 : ℚ) • PowerSeries.X) := by
  ext k
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_X_pow_mul']
  cases k with
  | zero =>
    simp [L2_ps]
  | succ k1 =>
    cases k1 with
    | zero =>
      simp [L2_ps]
    | succ m =>
      rw [if_pos (by omega : 2 ≤ m + 2), show m + 1 + 1 - 2 = m by omega]
      simp only [L2_ps, coeff_mk, map_neg, map_smul, PowerSeries.coeff_X, show m + 2 ≠ 1 by omega,
        ↓reduceIte, smul_eq_mul, mul_zero, neg_zero]
      have hiff : (2 ∣ m + 2 + 1) ↔ (2 ∣ m + 1) := by omega
      rw [if_congr hiff rfl rfl]
      split_ifs with h
      · have hdiv : (m + 2 + 1) / 2 - 1 = ((m + 1) / 2 - 1) + 1 := by omega
        rw [hdiv, pow_succ]
        ring
      · ring

private lemma psDeriv_f_ps : psDeriv f_ps = f_ps * Lprime_ps := by
  -- Prove (1 + X^2)^2 * psDeriv f_ps = (1 + X^2)^2 * (f_ps * Lprime_ps) and cancel (1 + X^2)^2
  have h1 : (1 + PowerSeries.X ^ 2) * psDeriv f_ps + ((2 : ℚ) • PowerSeries.X) * f_ps =
      1 + (2 : ℚ) • PowerSeries.X := by
    have hd := congrArg psDeriv one_add_X_sq_mul_f_ps
    rw [psDeriv_mul, psDeriv_add, psDeriv_one, psDeriv_pow, psDeriv_X] at hd
    rw [psDeriv_add, psDeriv_add, psDeriv_one, psDeriv_X, psDeriv_pow, psDeriv_X] at hd
    rw [add_comm] at hd
    simpa [pow_one, mul_one, zero_add, smul_mul_assoc] using hd
  have h2 : (1 + PowerSeries.X + PowerSeries.X ^ 2) * (1 + PowerSeries.X ^ 2) * Lprime_ps =
      (1 + (2 : ℚ) • PowerSeries.X) * (1 + PowerSeries.X ^ 2) -
        ((2 : ℚ) • PowerSeries.X) * (1 + PowerSeries.X + PowerSeries.X ^ 2) := by
    rw [Lprime_eq_add, mul_add]
    have ha : (1 + PowerSeries.X + PowerSeries.X ^ 2) * (1 + PowerSeries.X ^ 2) * L1_ps =
        ((1 + PowerSeries.X + PowerSeries.X ^ 2) * L1_ps) * (1 + PowerSeries.X ^ 2) := by ring
    have hb : (1 + PowerSeries.X + PowerSeries.X ^ 2) * (1 + PowerSeries.X ^ 2) * L2_ps =
        (1 + PowerSeries.X + PowerSeries.X ^ 2) * ((1 + PowerSeries.X ^ 2) * L2_ps) := by ring
    rw [ha, hb, poly1_mul_L1, poly2_mul_L2]
    ring
  have h3 : (1 + PowerSeries.X ^ 2) ^ 2 * psDeriv f_ps =
      (1 + PowerSeries.X ^ 2) ^ 2 * (f_ps * Lprime_ps) := by
    have hlhs : (1 + PowerSeries.X ^ 2) ^ 2 * psDeriv f_ps =
        (1 + PowerSeries.X ^ 2) * ((1 + PowerSeries.X ^ 2) * psDeriv f_ps) := by ring
    have hsub : (1 + PowerSeries.X ^ 2) * psDeriv f_ps =
        (1 + (2 : ℚ) • PowerSeries.X) - ((2 : ℚ) • PowerSeries.X) * f_ps := by
      exact eq_sub_of_add_eq h1
    rw [hlhs, hsub, mul_sub]
    have hrhs : (1 + PowerSeries.X ^ 2) ^ 2 * (f_ps * Lprime_ps) =
        ((1 + PowerSeries.X ^ 2) * f_ps) * (1 + PowerSeries.X ^ 2) * Lprime_ps := by ring
    rw [hrhs, one_add_X_sq_mul_f_ps, h2]
    have hmul : (1 + PowerSeries.X ^ 2) * (((2 : ℚ) • PowerSeries.X) * f_ps) =
        ((2 : ℚ) • PowerSeries.X) * ((1 + PowerSeries.X ^ 2) * f_ps) := by ring
    rw [hmul, one_add_X_sq_mul_f_ps]
    ring
  -- Multiply both sides by h_ps ^ 2 (since (1 + X^2) * h_ps = 1)
  have h4 := congrArg (fun x => h_ps ^ 2 * x) h3
  have hinv : h_ps ^ 2 * (1 + PowerSeries.X ^ 2) ^ 2 = 1 := by
    rw [← mul_pow, mul_comm, one_add_X_sq_mul_h_ps, one_pow]
  simpa [← mul_assoc, hinv] using h4

private noncomputable def psi_ps (p : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun N => if N = 0 ∨ p ∣ N then 0 else (c_seq N : ℚ) / (N : ℚ)

private lemma coeff_psi_ps (p N : ℕ) :
    PowerSeries.coeff N (psi_ps p) = if N = 0 ∨ p ∣ N then 0 else (c_seq N : ℚ) / (N : ℚ) := by
  simp [psi_ps]

private lemma coeff_zero_psi_ps (p : ℕ) : PowerSeries.coeff 0 (psi_ps p) = 0 := by
  simp [coeff_psi_ps]

private lemma seriesPInt_psi_ps {p : ℕ} (hp : p.Prime) : SeriesPInt p (psi_ps p) := fun N => by
  rw [coeff_psi_ps]
  split_ifs with h
  · exact isPInt_zero p hp
  · push Not at h
    exact isPInt_div_nat hp (c_seq N) h.2

private lemma psDeriv_psi_ps {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    psDeriv (psi_ps p) = Lprime_ps - PowerSeries.X ^ (p - 1) * psExpand p Lprime_ps := by
  have hp0 : 0 < p := hp.pos
  ext k
  rw [coeff_psDeriv, coeff_psi_ps, map_sub, PowerSeries.coeff_X_pow_mul']
  by_cases hd : p ∣ k + 1
  · rw [if_pos (Or.inr hd), mul_zero]
    rcases hd with ⟨m, hm⟩
    have hm_pos : 0 < m := by
      by_contra h0; have : m = 0 := by omega
      subst this; omega
    have hk_ge : p - 1 ≤ k := by have : p ≤ p * m := Nat.le_mul_of_pos_right p hm_pos; omega
    have hsub : k - (p - 1) = p * (m - 1) := by
      have : p * m = p * (m - 1) + p := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega, mul_add, mul_one]
      omega
    rw [if_pos hk_ge, hsub, coeff_psExpand, if_pos (dvd_mul_right p (m - 1)),
      Nat.mul_div_cancel_left (m - 1) hp0]
    simp only [Lprime_ps, coeff_mk, show m - 1 + 1 = m by omega, hm]
    rw [c_seq_mul_prime hp hp5 m hm_pos, sub_self]
  · rw [if_neg (by push Not; exact ⟨Nat.succ_ne_zero k, hd⟩)]
    have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    rw [mul_div_cancel₀ _ hk1]
    by_cases hk_ge : p - 1 ≤ k
    · rw [if_pos hk_ge, coeff_psExpand]
      have hnd : ¬ p ∣ k - (p - 1) := by
        intro ⟨m, hm⟩; apply hd; refine ⟨m + 1, ?_⟩; rw [mul_add, mul_one]; omega
      rw [if_neg hnd, sub_zero]
      simp [Lprime_ps]
    · rw [if_neg hk_ge, sub_zero]
      simp [Lprime_ps]

private lemma f_ps_pow_p_eq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    f_ps ^ p = psExpand p f_ps * psExp0 ((p : ℚ) • psi_ps p) := by
  have hp0 : 0 < p := hp.pos
  have hpsi0 : PowerSeries.coeff 0 ((p : ℚ) • psi_ps p) = 0 := by simp [coeff_zero_psi_ps]
  refine eq_of_ode_unique (A := (p : ℚ) • Lprime_ps) ?_ ?_ ?_
  · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_psExpand, if_pos (dvd_zero p),
      Nat.zero_div, coeff_zero_psExp0, mul_one]
    have hf0 : coeff 0 f_ps = 1 := by simp [f_ps]
    rw [hf0, one_pow]
  · rw [psDeriv_pow, psDeriv_f_ps]
    have : f_ps ^ (p - 1) * (f_ps * Lprime_ps) = Lprime_ps * f_ps ^ p := by
      have hp1 : p = (p - 1) + 1 := by omega
      conv_rhs => rw [hp1, pow_succ]
      ring
    rw [this, smul_mul_assoc]
  · rw [psDeriv_mul, psDeriv_psExpand p hp0 f_ps, psDeriv_f_ps, psExpand_mul p hp0,
      psDeriv_psExp0 hpsi0, psDeriv_smul, psDeriv_psi_ps hp hp5]
    ext k
    simp only [map_add, map_sub, map_smul, smul_eq_mul]
    have h1 : coeff k (((p : ℚ) • (X ^ (p - 1) * (psExpand p f_ps * psExpand p Lprime_ps))) *
          psExp0 ((p : ℚ) • psi_ps p) +
        psExpand p f_ps * (((p : ℚ) • (Lprime_ps - X ^ (p - 1) * psExpand p Lprime_ps)) *
          psExp0 ((p : ℚ) • psi_ps p))) =
        coeff k ((p : ℚ) • Lprime_ps * (psExpand p f_ps * psExp0 ((p : ℚ) • psi_ps p))) := by
      congr 1
      rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, ← smul_add, smul_mul_assoc]
      congr 1
      ring
    simpa [map_add, map_smul] using h1

private lemma f_ps_pow_pn_eq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (n : ℕ) :
    f_ps ^ (p * n) = psExpand p (f_ps ^ n) * psExp0 (((p * n : ℕ) : ℚ) • psi_ps p) := by
  rw [pow_mul, f_ps_pow_p_eq hp hp5, mul_pow, ← psExpand_pow p hp.pos f_ps n,
    ← psExp0_nsmul (by simp [coeff_zero_psi_ps] : coeff 0 ((p : ℚ) • psi_ps p) = 0) n]
  congr 2
  rw [smul_smul, Nat.cast_mul, mul_comm]

/-! ### Section 6: Harmonic Sums in ZMod (p^v) and Key Lemma for W_k -/

private def Hsum (p v M d : ℕ) : ZMod (p ^ v) :=
  ∑ j ∈ (Finset.range M).filter (fun j => 0 < j ∧ d * j < M ∧ ¬ p ∣ j), (j : ZMod (p ^ v))⁻¹

private lemma zmod_inv_unit_mul {p v a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    (a : ZMod (p ^ v)) * (a : ZMod (p ^ v))⁻¹ = 1 := by
  have hcop : Nat.Coprime a (p ^ v) :=
    (hp.coprime_iff_not_dvd.mpr ha).symm.pow_right v
  have h := ZMod.mul_inv_eq_gcd (a : ZMod (p ^ v))
  have hgcd : (a : ZMod (p ^ v)).val.gcd (p ^ v) = 1 := by
    rw [ZMod.val_natCast, ← Nat.gcd_rec, Nat.gcd_comm]
    exact hcop.gcd_eq_one
  rw [hgcd, Nat.cast_one] at h
  exact h

private lemma zmod_inv_mul_unit {p v a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) :
    (a : ZMod (p ^ v))⁻¹ * (a : ZMod (p ^ v)) = 1 := by
  rw [mul_comm]; exact zmod_inv_unit_mul hp ha

private lemma zmod_two_mul_inv {p v : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) :
    (2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹ = 1 := by
  simpa using zmod_inv_unit_mul (p := p) (v := v) (a := 2) hp hp2

private lemma zmod_three_mul_inv {p v : ℕ} (hp : p.Prime) (hp3 : ¬ p ∣ 3) :
    (3 : ZMod (p ^ v)) * (3 : ZMod (p ^ v))⁻¹ = 1 := by
  simpa using zmod_inv_unit_mul (p := p) (v := v) (a := 3) hp hp3

private lemma zmod_inv_sub {p v M j : ℕ} (hp : p.Prime) (hv : 1 ≤ v) (hM : p ^ v ∣ M) (hjM : j < M)
    (hj : ¬ p ∣ j) :
    ((M - j : ℕ) : ZMod (p ^ v))⁻¹ = -(j : ZMod (p ^ v))⁻¹ := by
  have hpM : p ∣ M := dvd_trans (dvd_pow_self p (by omega)) hM
  have hMj : ¬ p ∣ (M - j) := by
    intro h
    have : p ∣ j := by
      have := Nat.dvd_sub hpM h
      rwa [Nat.sub_sub_self hjM.le] at this
    exact hj this
  have hM0 : (M : ZMod (p ^ v)) = 0 := (ZMod.natCast_eq_zero_iff M (p ^ v)).mpr hM
  have hsub : ((M - j : ℕ) : ZMod (p ^ v)) = -(j : ZMod (p ^ v)) := by
    rw [Nat.cast_sub hjM.le, hM0, zero_sub]
  have h1 : (j : ZMod (p ^ v)) * ((M - j : ℕ) : ZMod (p ^ v))⁻¹ =
      (j : ZMod (p ^ v)) * (-(j : ZMod (p ^ v))⁻¹) := by
    have hl : -((M - j : ℕ) : ZMod (p ^ v)) * ((M - j : ℕ) : ZMod (p ^ v))⁻¹ = -1 := by
      rw [neg_mul, zmod_inv_unit_mul hp hMj]
    have hl2 : (j : ZMod (p ^ v)) * ((M - j : ℕ) : ZMod (p ^ v))⁻¹ = -1 := by
      simpa [hsub] using hl
    rw [hl2, mul_neg, zmod_inv_unit_mul hp hj]
  have h2 := congrArg (fun x => (j : ZMod (p ^ v))⁻¹ * x) h1
  simpa [← mul_assoc, zmod_inv_mul_unit hp hj] using h2

private lemma zmod_inv_mul_nat {p v a b : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    ((a * b : ℕ) : ZMod (p ^ v))⁻¹ = (a : ZMod (p ^ v))⁻¹ * (b : ZMod (p ^ v))⁻¹ := by
  have hab : ¬ p ∣ a * b := fun h => (hp.dvd_mul.mp h).elim ha hb
  have h1 : ((a * b : ℕ) : ZMod (p ^ v)) * ((a * b : ℕ) : ZMod (p ^ v))⁻¹ =
      ((a * b : ℕ) : ZMod (p ^ v)) * ((a : ZMod (p ^ v))⁻¹ * (b : ZMod (p ^ v))⁻¹) := by
    rw [zmod_inv_unit_mul hp hab, Nat.cast_mul]
    calc
      (1 : ZMod (p ^ v)) = ((a : ZMod (p ^ v)) * (a : ZMod (p ^ v))⁻¹) *
          ((b : ZMod (p ^ v)) * (b : ZMod (p ^ v))⁻¹) := by
        rw [zmod_inv_unit_mul hp ha, zmod_inv_unit_mul hp hb, mul_one]
      _ = (a : ZMod (p ^ v)) * (b : ZMod (p ^ v)) *
          ((a : ZMod (p ^ v))⁻¹ * (b : ZMod (p ^ v))⁻¹) := by ring
  have h2 := congrArg (fun x => ((a * b : ℕ) : ZMod (p ^ v))⁻¹ * x) h1
  rw [← mul_assoc, ← mul_assoc, zmod_inv_mul_unit hp hab, one_mul, one_mul] at h2
  exact h2

private lemma zmod_inv_two_mul {p v b : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) (hb : ¬ p ∣ b) :
    ((2 * b : ℕ) : ZMod (p ^ v))⁻¹ = (2 : ZMod (p ^ v))⁻¹ * (b : ZMod (p ^ v))⁻¹ := by
  simpa using zmod_inv_mul_nat (p := p) (v := v) (a := 2) (b := b) hp hp2 hb

private lemma zmod_inv_three_mul {p v b : ℕ} (hp : p.Prime) (hp3 : ¬ p ∣ 3) (hb : ¬ p ∣ b) :
    ((3 * b : ℕ) : ZMod (p ^ v))⁻¹ = (3 : ZMod (p ^ v))⁻¹ * (b : ZMod (p ^ v))⁻¹ := by
  simpa using zmod_inv_mul_nat (p := p) (v := v) (a := 3) (b := b) hp hp3 hb

private lemma zmod_cancel_nat {p v a : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a)
    {x y : ZMod (p ^ v)} (h : (a : ZMod (p ^ v)) * x = (a : ZMod (p ^ v)) * y) : x = y := by
  have h2 := congrArg (fun z => (a : ZMod (p ^ v))⁻¹ * z) h
  simpa [← mul_assoc, zmod_inv_mul_unit hp ha] using h2

private lemma Hsum_one_eq_zero {p v M : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2)
    (hv : 1 ≤ v) (hM : p ^ v ∣ M) : Hsum p v M 1 = 0 := by
  have hpM : p ∣ M := dvd_trans (dvd_pow_self p (by omega)) hM
  have hS : Hsum p v M 1 = -Hsum p v M 1 := by
    unfold Hsum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun j _ => M - j) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, one_mul] at hj ⊢
      refine ⟨by omega, by omega, by omega, ?_⟩
      intro hdiv
      have : p ∣ j := by
        have := Nat.dvd_sub hpM hdiv
        rwa [Nat.sub_sub_self hj.1.le] at this
      exact hj.2.2.2 this
    · intro j₁ hj₁ j₂ hj₂ heq
      simp only [Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, one_mul] at hj
      refine ⟨M - j, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range, one_mul]
      refine ⟨by omega, by omega, by omega, ?_⟩
      intro hdiv
      have : p ∣ j := by
        have := Nat.dvd_sub hpM hdiv
        rwa [Nat.sub_sub_self hj.1.le] at this
      exact hj.2.2.2 this
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      rw [zmod_inv_sub hp hv hM hj.1 hj.2.2.2, neg_neg]
  apply zmod_cancel_nat hp hp2 (a := 2)
  rw [Nat.cast_ofNat, mul_zero]
  have : (2 : ZMod (p ^ v)) * Hsum p v M 1 = Hsum p v M 1 + Hsum p v M 1 := by ring
  rw [this]
  conv_lhs => rhs; rw [hS]
  ring

private lemma Hsum_two_mul {p v K d : ℕ} (hd : 1 ≤ d) :
    Hsum p v (2 * K) (2 * d) = Hsum p v K d := by
  unfold Hsum
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h1, h2, h3⟩; exact ⟨by nlinarith, h1, by nlinarith, h3⟩
  · rintro ⟨_, h1, h2, h3⟩; exact ⟨by nlinarith, h1, by nlinarith, h3⟩

private lemma Hsum_three_mul {p v K d : ℕ} (hd : 1 ≤ d) :
    Hsum p v (3 * K) (3 * d) = Hsum p v K d := by
  unfold Hsum
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h1, h2, h3⟩; exact ⟨by nlinarith, h1, by nlinarith, h3⟩
  · rintro ⟨_, h1, h2, h3⟩; exact ⟨by nlinarith, h1, by nlinarith, h3⟩

-- Helper: split a filtered sum into even and odd indices
private lemma sum_filter_even_odd {α : Type*} [AddCommMonoid α] (S : Finset ℕ) (f : ℕ → α) :
    ∑ j ∈ S, f j = ∑ j ∈ S.filter (fun j => 2 ∣ j), f j +
      ∑ j ∈ S.filter (fun j => ¬ 2 ∣ j), f j := by
  exact (Finset.sum_filter_add_sum_filter_not S (fun j => 2 ∣ j) f).symm

-- Helper: sum of j⁻¹ over j ∈ (0, M/d) even, p ∤ j equals 2⁻¹ * Hsum p v M (2*d)
private lemma sum_even_Hsum {p v M d : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) (hd : 1 ≤ d) :
    ∑ j ∈ ((Finset.range M).filter (fun j => 0 < j ∧ d * j < M ∧ ¬ p ∣ j)).filter (fun j => 2 ∣ j),
      (j : ZMod (p ^ v))⁻¹ =
    (2 : ZMod (p ^ v))⁻¹ * Hsum p v M (2 * d) := by
  unfold Hsum
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun j _ => j / 2) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    rcases hj.2 with ⟨t, rfl⟩
    have hpt : ¬ p ∣ t := fun h => hj.1.2.2.2 (dvd_mul_of_dvd_right h 2)
    rw [Nat.mul_div_cancel_left t (by omega)]
    exact ⟨by omega, by omega, by linarith, hpt⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.mem_filter] at hj₁ hj₂
    rcases hj₁.2 with ⟨t₁, rfl⟩
    rcases hj₂.2 with ⟨t₂, rfl⟩
    rw [Nat.mul_div_cancel_left t₁ (by omega), Nat.mul_div_cancel_left t₂ (by omega)] at heq
    rw [heq]
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    refine ⟨2 * t, ?_, Nat.mul_div_cancel_left t (by omega)⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    have h2t : ¬ p ∣ 2 * t := fun h => (hp.dvd_mul.mp h).elim hp2 ht.2.2.2
    exact ⟨⟨by nlinarith, by omega, by nlinarith, h2t⟩, ⟨t, rfl⟩⟩
  · intro j hj
    simp only [Finset.mem_filter] at hj
    rcases hj.2 with ⟨t, rfl⟩
    have hpt : ¬ p ∣ t := fun h => hj.1.2.2.2 (dvd_mul_of_dvd_right h 2)
    rw [Nat.mul_div_cancel_left t (by omega), zmod_inv_two_mul hp hp2 hpt]

-- Lemma: for odd M with p^v | M, 2 * Hsum p v M 4 = 3 * Hsum p v M 2
private lemma Hsum_odd_four {p v M : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2)
    (hv : 1 ≤ v) (hM : p ^ v ∣ M) (hModd : M % 2 = 1) :
    (2 : ZMod (p ^ v)) * Hsum p v M 4 = (3 : ZMod (p ^ v)) * Hsum p v M 2 := by
  have hpM : p ∣ M := dvd_trans (dvd_pow_self p (by omega)) hM
  -- Split Hsum M 1 = 0 into even and odd
  have hfull := Hsum_one_eq_zero hp hp2 hv hM
  have hsplit_full := sum_filter_even_odd
    ((Finset.range M).filter (fun j => 0 < j ∧ 1 * j < M ∧ ¬ p ∣ j))
    (fun j => (j : ZMod (p ^ v))⁻¹)
  have hev_full := sum_even_Hsum (p := p) (v := v) (M := M) (d := 1) hp hp2 (by omega)
  rw [mul_one] at hev_full
  have hodd_full :
      ∑ j ∈ ((Finset.range M).filter (fun j => 0 < j ∧ 1 * j < M ∧ ¬ p ∣ j)).filter (fun j => ¬ 2 ∣ j),
        (j : ZMod (p ^ v))⁻¹ = -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 2) := by
    have : Hsum p v M 1 = (2 : ZMod (p ^ v))⁻¹ * Hsum p v M 2 +
        ∑ j ∈ ((Finset.range M).filter (fun j => 0 < j ∧ 1 * j < M ∧ ¬ p ∣ j)).filter (fun j => ¬ 2 ∣ j),
          (j : ZMod (p ^ v))⁻¹ := by
      conv_lhs => unfold Hsum
      rw [hsplit_full, hev_full]
    rw [hfull] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  -- Split odd j < M into 2*j < M and 2*j > M (cannot have 2*j = M since M odd)
  set Sodd := ((Finset.range M).filter (fun j => 0 < j ∧ 1 * j < M ∧ ¬ p ∣ j)).filter (fun j => ¬ 2 ∣ j)
  have hsplit_half : ∑ j ∈ Sodd, (j : ZMod (p ^ v))⁻¹ =
      ∑ j ∈ Sodd.filter (fun j => 2 * j < M), (j : ZMod (p ^ v))⁻¹ +
      ∑ j ∈ Sodd.filter (fun j => ¬ 2 * j < M), (j : ZMod (p ^ v))⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not Sodd (fun j => 2 * j < M) _).symm
  -- First half of odd j < M equals Hsum M 2 - 2⁻¹ * Hsum M 4
  have hlo : ∑ j ∈ Sodd.filter (fun j => 2 * j < M), (j : ZMod (p ^ v))⁻¹ =
      Hsum p v M 2 - (2 : ZMod (p ^ v))⁻¹ * Hsum p v M 4 := by
    have hsp := sum_filter_even_odd
      ((Finset.range M).filter (fun j => 0 < j ∧ 2 * j < M ∧ ¬ p ∣ j))
      (fun j => (j : ZMod (p ^ v))⁻¹)
    have hev2 := sum_even_Hsum (p := p) (v := v) (M := M) (d := 2) hp hp2 (by omega)
    have hset : Sodd.filter (fun j => 2 * j < M) =
        ((Finset.range M).filter (fun j => 0 < j ∧ 2 * j < M ∧ ¬ p ∣ j)).filter (fun j => ¬ 2 ∣ j) := by
      ext j; simp only [Sodd, Finset.mem_filter, Finset.mem_range]; omega
    rw [hset]
    have : Hsum p v M 2 = (2 : ZMod (p ^ v))⁻¹ * Hsum p v M 4 +
        ∑ j ∈ ((Finset.range M).filter (fun j => 0 < j ∧ 2 * j < M ∧ ¬ p ∣ j)).filter (fun j => ¬ 2 ∣ j),
          (j : ZMod (p ^ v))⁻¹ := by
      conv_lhs => unfold Hsum
      rw [hsp, hev2]
    exact eq_sub_of_add_eq' this.symm
  -- Second half of odd j < M (M/2 < j < M, j odd): M - j = 2*t with 4*t < M
  have hhi : ∑ j ∈ Sodd.filter (fun j => ¬ 2 * j < M), (j : ZMod (p ^ v))⁻¹ =
      -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 4) := by
    unfold Hsum
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun j _ => (M - j) / 2) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Sodd, Finset.mem_filter, Finset.mem_range, one_mul] at hj ⊢
      have hMj_ev : (M - j) % 2 = 0 := by omega
      have hpt : ¬ p ∣ (M - j) / 2 := by
        intro h
        have h1 : p ∣ M - j := by
          rw [show M - j = 2 * ((M - j) / 2) by omega]
          exact dvd_mul_of_dvd_right h 2
        have : p ∣ j := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hj.1.1.1.le] at this
        exact hj.1.1.2.2.2 this
      exact ⟨by omega, by omega, by omega, hpt⟩
    · intro j₁ hj₁ j₂ hj₂ heq
      simp only [Sodd, Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
      omega
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      refine ⟨M - 2 * t, ?_, by omega⟩
      simp only [Sodd, Finset.mem_filter, Finset.mem_range, one_mul]
      have hnd : ¬ p ∣ M - 2 * t := by
        intro h
        have h1 : p ∣ 2 * t := by
          have := Nat.dvd_sub hpM h
          rwa [Nat.sub_sub_self (by omega : 2 * t ≤ M)] at this
        exact (hp.dvd_mul.mp h1).elim hp2 ht.2.2.2
      exact ⟨⟨⟨by omega, by omega, by omega, hnd⟩, by omega⟩, by omega⟩
    · intro j hj
      simp only [Sodd, Finset.mem_filter, Finset.mem_range, one_mul] at hj
      set t := (M - j) / 2
      have hMj : M - j = 2 * t := by omega
      have hj_eq : j = M - 2 * t := by omega
      have hpt : ¬ p ∣ t := by
        intro h
        have h1 : p ∣ M - j := hMj ▸ dvd_mul_of_dvd_right h 2
        have : p ∣ j := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hj.1.1.1.le] at this
        exact hj.1.1.2.2.2 this
      have h2t : ¬ p ∣ 2 * t := fun h => (hp.dvd_mul.mp h).elim hp2 hpt
      rw [hj_eq, zmod_inv_sub hp hv hM (by omega : 2 * t < M) h2t, zmod_inv_two_mul hp hp2 hpt]
  have heq_all : -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 2) =
      (Hsum p v M 2 - (2 : ZMod (p ^ v))⁻¹ * Hsum p v M 4) +
      (-((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 4)) := by
    rw [← hodd_full, hsplit_half, hlo, hhi]
  have hmul2 := congrArg (fun x => (2 : ZMod (p ^ v)) * x) heq_all
  have h2inv : (2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹ = 1 := zmod_two_mul_inv hp hp2
  have hstep : -Hsum p v M 2 = (2 : ZMod (p ^ v)) * Hsum p v M 2 - (2 : ZMod (p ^ v)) * Hsum p v M 4 := by
    calc
      -Hsum p v M 2
        = (2 : ZMod (p ^ v)) * -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 2) := by
          rw [mul_neg, ← mul_assoc, h2inv, one_mul]
      _ = (2 : ZMod (p ^ v)) * ((Hsum p v M 2 - (2 : ZMod (p ^ v))⁻¹ * Hsum p v M 4) +
          -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 4)) := hmul2
      _ = (2 : ZMod (p ^ v)) * Hsum p v M 2 -
          ((2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹) * Hsum p v M 4 -
          ((2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹) * Hsum p v M 4 := by ring
      _ = (2 : ZMod (p ^ v)) * Hsum p v M 2 - (2 : ZMod (p ^ v)) * Hsum p v M 4 := by
          rw [h2inv]; ring
  calc
    (2 : ZMod (p ^ v)) * Hsum p v M 4
      = (2 : ZMod (p ^ v)) * Hsum p v M 2 - (-Hsum p v M 2) := by rw [hstep]; ring
    _ = (3 : ZMod (p ^ v)) * Hsum p v M 2 := by ring

-- Lemma: for odd M with p^v | M and ¬ p ∣ 3, Hsum p v M 6 - Hsum p v M 3 = Hsum p v M 2
private lemma Hsum_odd_six {p v M : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3)
    (hv : 1 ≤ v) (hM : p ^ v ∣ M) (hModd : M % 2 = 1) :
    Hsum p v M 6 - Hsum p v M 3 = Hsum p v M 2 := by
  have hpM : p ∣ M := dvd_trans (dvd_pow_self p (by omega)) hM
  have hfull := Hsum_one_eq_zero hp hp2 hv hM
  have hsplit_full := sum_filter_even_odd
    ((Finset.range M).filter (fun j => 0 < j ∧ 1 * j < M ∧ ¬ p ∣ j))
    (fun j => (j : ZMod (p ^ v))⁻¹)
  have hev_full := sum_even_Hsum (p := p) (v := v) (M := M) (d := 1) hp hp2 (by omega)
  rw [mul_one] at hev_full
  set Sodd := ((Finset.range M).filter (fun j => 0 < j ∧ 1 * j < M ∧ ¬ p ∣ j)).filter (fun j => ¬ 2 ∣ j)
  have hodd_full : ∑ j ∈ Sodd, (j : ZMod (p ^ v))⁻¹ = -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 2) := by
    have : Hsum p v M 1 = (2 : ZMod (p ^ v))⁻¹ * Hsum p v M 2 + ∑ j ∈ Sodd, (j : ZMod (p ^ v))⁻¹ := by
      conv_lhs => unfold Hsum
      rw [hsplit_full, hev_full]
    rw [hfull] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  -- No j with ¬ p ∣ j can satisfy 3*j = M or 3*j = 2*M
  have hne_M : ∀ j, ¬ p ∣ j → 3 * j ≠ M := fun j hj h =>
    hj ((hp.dvd_mul.mp (h ▸ hpM)).resolve_left hp3)
  have hne_2M : ∀ j, ¬ p ∣ j → 3 * j ≠ 2 * M := fun j hj h =>
    hj ((hp.dvd_mul.mp (h ▸ dvd_mul_of_dvd_right hpM 2)).resolve_left hp3)
  -- Split Sodd into: (I1) 3*j < M, (I2) M < 3*j ∧ 3*j < 2*M, (I3) 2*M < 3*j
  have hsp1 : ∑ j ∈ Sodd, (j : ZMod (p ^ v))⁻¹ =
      ∑ j ∈ Sodd.filter (fun j => 3 * j < M), (j : ZMod (p ^ v))⁻¹ +
      ∑ j ∈ Sodd.filter (fun j => ¬ 3 * j < M), (j : ZMod (p ^ v))⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not Sodd (fun j => 3 * j < M) _).symm
  have hsp2 : ∑ j ∈ Sodd.filter (fun j => ¬ 3 * j < M), (j : ZMod (p ^ v))⁻¹ =
      ∑ j ∈ (Sodd.filter (fun j => ¬ 3 * j < M)).filter (fun j => 3 * j < 2 * M), (j : ZMod (p ^ v))⁻¹ +
      ∑ j ∈ (Sodd.filter (fun j => ¬ 3 * j < M)).filter (fun j => ¬ 3 * j < 2 * M), (j : ZMod (p ^ v))⁻¹ :=
    (Finset.sum_filter_add_sum_filter_not _ (fun j => 3 * j < 2 * M) _).symm
  -- I1 = Hsum M 3 - 2⁻¹ * Hsum M 6
  have hI1 : ∑ j ∈ Sodd.filter (fun j => 3 * j < M), (j : ZMod (p ^ v))⁻¹ =
      Hsum p v M 3 - (2 : ZMod (p ^ v))⁻¹ * Hsum p v M 6 := by
    have hsp := sum_filter_even_odd
      ((Finset.range M).filter (fun j => 0 < j ∧ 3 * j < M ∧ ¬ p ∣ j))
      (fun j => (j : ZMod (p ^ v))⁻¹)
    have hev3 := sum_even_Hsum (p := p) (v := v) (M := M) (d := 3) hp hp2 (by omega)
    have hset : Sodd.filter (fun j => 3 * j < M) =
        ((Finset.range M).filter (fun j => 0 < j ∧ 3 * j < M ∧ ¬ p ∣ j)).filter (fun j => ¬ 2 ∣ j) := by
      ext j; simp only [Sodd, Finset.mem_filter, Finset.mem_range]; omega
    rw [hset]
    have : Hsum p v M 3 = (2 : ZMod (p ^ v))⁻¹ * Hsum p v M 6 +
        ∑ j ∈ ((Finset.range M).filter (fun j => 0 < j ∧ 3 * j < M ∧ ¬ p ∣ j)).filter (fun j => ¬ 2 ∣ j),
          (j : ZMod (p ^ v))⁻¹ := by
      conv_lhs => unfold Hsum
      rw [hsp, hev3]
    exact eq_sub_of_add_eq' this.symm
  -- I3 = -2⁻¹ * Hsum M 6 (via j ↦ (M - j) / 2)
  have hI3 : ∑ j ∈ (Sodd.filter (fun j => ¬ 3 * j < M)).filter (fun j => ¬ 3 * j < 2 * M),
      (j : ZMod (p ^ v))⁻¹ = -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 6) := by
    unfold Hsum
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun j _ => (M - j) / 2) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Sodd, Finset.mem_filter, Finset.mem_range, one_mul] at hj ⊢
      have hne := hne_2M j hj.1.1.1.2.2.2
      have hpt : ¬ p ∣ (M - j) / 2 := by
        intro h
        have h1 : p ∣ M - j := by
          rw [show M - j = 2 * ((M - j) / 2) by omega]
          exact dvd_mul_of_dvd_right h 2
        have : p ∣ j := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hj.1.1.1.1.le] at this
        exact hj.1.1.1.2.2.2 this
      exact ⟨by omega, by omega, by omega, hpt⟩
    · intro j₁ hj₁ j₂ hj₂ heq
      simp only [Sodd, Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
      omega
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      refine ⟨M - 2 * t, ?_, by omega⟩
      simp only [Sodd, Finset.mem_filter, Finset.mem_range, one_mul]
      have hnd : ¬ p ∣ M - 2 * t := by
        intro h
        have h1 : p ∣ 2 * t := by
          have := Nat.dvd_sub hpM h
          rwa [Nat.sub_sub_self (by omega : 2 * t ≤ M)] at this
        exact (hp.dvd_mul.mp h1).elim hp2 ht.2.2.2
      exact ⟨⟨⟨⟨by omega, by omega, by omega, hnd⟩, by omega⟩, by omega⟩, by omega⟩
    · intro j hj
      simp only [Sodd, Finset.mem_filter, Finset.mem_range, one_mul] at hj
      set t := (M - j) / 2
      have hMj : M - j = 2 * t := by omega
      have hj_eq : j = M - 2 * t := by omega
      have hpt : ¬ p ∣ t := by
        intro h
        have h1 : p ∣ M - j := hMj ▸ dvd_mul_of_dvd_right h 2
        have : p ∣ j := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hj.1.1.1.1.le] at this
        exact hj.1.1.1.2.2.2 this
      have h2t : ¬ p ∣ 2 * t := fun h => (hp.dvd_mul.mp h).elim hp2 hpt
      rw [hj_eq, zmod_inv_sub hp hv hM (by omega : 2 * t < M) h2t, zmod_inv_two_mul hp hp2 hpt]
  -- I2 = -2⁻¹ * (Hsum M 3 - Hsum M 6) (via j ↦ (M - j) / 2, landing in 3*t < M ∧ ¬ 6*t < M)
  have hI2 : ∑ j ∈ (Sodd.filter (fun j => ¬ 3 * j < M)).filter (fun j => 3 * j < 2 * M),
      (j : ZMod (p ^ v))⁻¹ = -((2 : ZMod (p ^ v))⁻¹ * (Hsum p v M 3 - Hsum p v M 6)) := by
    set T3 := (Finset.range M).filter (fun t => 0 < t ∧ 3 * t < M ∧ ¬ p ∣ t)
    have hdiff : Hsum p v M 3 - Hsum p v M 6 =
        ∑ t ∈ T3.filter (fun t => ¬ 6 * t < M), (t : ZMod (p ^ v))⁻¹ := by
      have hsp := (Finset.sum_filter_add_sum_filter_not T3 (fun t => 6 * t < M)
        (fun t => (t : ZMod (p ^ v))⁻¹)).symm
      have hsub : T3.filter (fun t => 6 * t < M) =
          (Finset.range M).filter (fun t => 0 < t ∧ 6 * t < M ∧ ¬ p ∣ t) := by
        ext t; simp only [T3, Finset.mem_filter, Finset.mem_range]; omega
      have : Hsum p v M 3 = Hsum p v M 6 + ∑ t ∈ T3.filter (fun t => ¬ 6 * t < M), (t : ZMod (p ^ v))⁻¹ := by
        unfold Hsum; rw [← hsub]; exact hsp
      exact (eq_sub_of_add_eq' this.symm).symm
    rw [hdiff, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun j _ => (M - j) / 2) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Sodd, T3, Finset.mem_filter, Finset.mem_range, one_mul] at hj ⊢
      have hne := hne_M j hj.1.1.1.2.2.2
      have hpt : ¬ p ∣ (M - j) / 2 := by
        intro h
        have h1 : p ∣ M - j := by
          rw [show M - j = 2 * ((M - j) / 2) by omega]
          exact dvd_mul_of_dvd_right h 2
        have : p ∣ j := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hj.1.1.1.1.le] at this
        exact hj.1.1.1.2.2.2 this
      exact ⟨⟨by omega, by omega, by omega, hpt⟩, by omega⟩
    · intro j₁ hj₁ j₂ hj₂ heq
      simp only [Sodd, Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
      omega
    · intro t ht
      simp only [T3, Finset.mem_filter, Finset.mem_range] at ht
      have hne6 : 6 * t ≠ M := by
        intro h
        have h1 : p ∣ 6 * t := h ▸ hpM
        have h2 : ¬ p ∣ 6 := by
          intro h6
          rw [show (6 : ℕ) = 2 * 3 by norm_num] at h6
          exact (hp.dvd_mul.mp h6).elim hp2 hp3
        exact (hp.dvd_mul.mp h1).elim h2 ht.1.2.2.2
      refine ⟨M - 2 * t, ?_, by omega⟩
      simp only [Sodd, Finset.mem_filter, Finset.mem_range, one_mul]
      have hnd : ¬ p ∣ M - 2 * t := by
        intro h
        have h1 : p ∣ 2 * t := by
          have := Nat.dvd_sub hpM h
          rwa [Nat.sub_sub_self (by omega : 2 * t ≤ M)] at this
        exact (hp.dvd_mul.mp h1).elim hp2 ht.1.2.2.2
      exact ⟨⟨⟨⟨by omega, by omega, by omega, hnd⟩, by omega⟩, by omega⟩, by omega⟩
    · intro j hj
      simp only [Sodd, Finset.mem_filter, Finset.mem_range, one_mul] at hj
      set t := (M - j) / 2
      have hMj : M - j = 2 * t := by omega
      have hj_eq : j = M - 2 * t := by omega
      have hpt : ¬ p ∣ t := by
        intro h
        have h1 : p ∣ M - j := hMj ▸ dvd_mul_of_dvd_right h 2
        have : p ∣ j := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hj.1.1.1.1.le] at this
        exact hj.1.1.1.2.2.2 this
      have h2t : ¬ p ∣ 2 * t := fun h => (hp.dvd_mul.mp h).elim hp2 hpt
      rw [hj_eq, zmod_inv_sub hp hv hM (by omega : 2 * t < M) h2t, zmod_inv_two_mul hp hp2 hpt]
  have hall : -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 2) =
      (Hsum p v M 3 - (2 : ZMod (p ^ v))⁻¹ * Hsum p v M 6) +
      (-((2 : ZMod (p ^ v))⁻¹ * (Hsum p v M 3 - Hsum p v M 6)) +
       -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 6)) := by
    rw [← hodd_full, hsp1, hsp2, hI1, hI2, hI3]
  have h2inv : (2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹ = 1 := zmod_two_mul_inv hp hp2
  have hmul := congrArg (fun x => (2 : ZMod (p ^ v)) * x) hall
  have hsimp : -Hsum p v M 2 = Hsum p v M 3 - Hsum p v M 6 := by
    calc
      -Hsum p v M 2
        = (2 : ZMod (p ^ v)) * -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 2) := by
          rw [mul_neg, ← mul_assoc, h2inv, one_mul]
      _ = (2 : ZMod (p ^ v)) * ((Hsum p v M 3 - (2 : ZMod (p ^ v))⁻¹ * Hsum p v M 6) +
          (-((2 : ZMod (p ^ v))⁻¹ * (Hsum p v M 3 - Hsum p v M 6)) +
           -((2 : ZMod (p ^ v))⁻¹ * Hsum p v M 6))) := hmul
      _ = (2 : ZMod (p ^ v)) * Hsum p v M 3 -
          ((2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹) * Hsum p v M 6 -
          ((2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹) * (Hsum p v M 3 - Hsum p v M 6) -
          ((2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹) * Hsum p v M 6 := by ring
      _ = Hsum p v M 3 - Hsum p v M 6 := by rw [h2inv]; ring
  calc
    Hsum p v M 6 - Hsum p v M 3 = -(Hsum p v M 3 - Hsum p v M 6) := by ring
    _ = -(-Hsum p v M 2) := by rw [← hsimp]
    _ = Hsum p v M 2 := neg_neg _

-- Lemma: for even M = 2*L with p^v | 2*L and ¬ p ∣ 2, ¬ p ∣ 3, Hsum (2*L) 6 = Hsum (2*L) 3
private lemma Hsum_even_six {p v L : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3)
    (hv : 1 ≤ v) (hL : p ^ v ∣ 2 * L) :
    Hsum p v (2 * L) 6 = Hsum p v (2 * L) 3 := by
  have hpvL : p ^ v ∣ L := by
    have hcop : Nat.Coprime (p ^ v) 2 := (hp.coprime_iff_not_dvd.mpr hp2).pow_left v
    exact hcop.dvd_of_dvd_mul_left hL
  have hpL : p ∣ L := dvd_trans (dvd_pow_self p (by omega)) hpvL
  set T := (Finset.range (2 * L)).filter (fun j => 0 < j ∧ 3 * j < 2 * L ∧ ¬ p ∣ j)
  have hsp := (Finset.sum_filter_add_sum_filter_not T (fun j => 3 * j < L)
    (fun j => (j : ZMod (p ^ v))⁻¹)).symm
  have hlo : T.filter (fun j => 3 * j < L) =
      (Finset.range (2 * L)).filter (fun j => 0 < j ∧ 6 * j < 2 * L ∧ ¬ p ∣ j) := by
    ext j; simp only [T, Finset.mem_filter, Finset.mem_range]; omega
  -- Show the mid sum (L ≤ 3*j < 2*L) is 0 by pairing j ↔ L - j
  set Mset := T.filter (fun j => ¬ 3 * j < L)
  have hmid : ∑ j ∈ Mset, (j : ZMod (p ^ v))⁻¹ = 0 := by
    have hneg : ∑ j ∈ Mset, (j : ZMod (p ^ v))⁻¹ = -∑ j ∈ Mset, (j : ZMod (p ^ v))⁻¹ := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_bij (fun j _ => L - j) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Mset, T, Finset.mem_filter, Finset.mem_range] at hj ⊢
        have hne : 3 * j ≠ L := fun h => hj.1.2.2.2 ((hp.dvd_mul.mp (h ▸ hpL)).resolve_left hp3)
        have hnd : ¬ p ∣ L - j := by
          intro h
          have : p ∣ j := by
            have := Nat.dvd_sub hpL h
            rwa [Nat.sub_sub_self (by omega : j ≤ L)] at this
          exact hj.1.2.2.2 this
        exact ⟨⟨by omega, by omega, by omega, hnd⟩, by omega⟩
      · intro j₁ hj₁ j₂ hj₂ heq
        simp only [Mset, T, Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
        omega
      · intro j hj
        simp only [Mset, T, Finset.mem_filter, Finset.mem_range] at hj
        have hne : 3 * j ≠ L := fun h => hj.1.2.2.2 ((hp.dvd_mul.mp (h ▸ hpL)).resolve_left hp3)
        have hnd : ¬ p ∣ L - j := by
          intro h
          have : p ∣ j := by
            have := Nat.dvd_sub hpL h
            rwa [Nat.sub_sub_self (by omega : j ≤ L)] at this
          exact hj.1.2.2.2 this
        refine ⟨L - j, ?_, by omega⟩
        simp only [Mset, T, Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨by omega, by omega, by omega, hnd⟩, by omega⟩
      · intro j hj
        simp only [Mset, T, Finset.mem_filter, Finset.mem_range] at hj
        rw [zmod_inv_sub hp hv hpvL (by omega : j < L) hj.1.2.2.2, neg_neg]
    apply zmod_cancel_nat hp hp2 (a := 2)
    rw [Nat.cast_ofNat, mul_zero]
    have : (2 : ZMod (p ^ v)) * ∑ j ∈ Mset, (j : ZMod (p ^ v))⁻¹ =
        ∑ j ∈ Mset, (j : ZMod (p ^ v))⁻¹ + ∑ j ∈ Mset, (j : ZMod (p ^ v))⁻¹ := by ring
    rw [this]
    conv_lhs => rhs; rw [hneg]
    ring
  have heq : Hsum p v (2 * L) 3 = Hsum p v (2 * L) 6 + ∑ j ∈ Mset, (j : ZMod (p ^ v))⁻¹ := by
    unfold Hsum; rw [← hlo]; exact hsp
  rw [heq, hmid, add_zero]

private def chi4 (p v n : ℕ) : ZMod (p ^ v) :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

private lemma neg_one_pow_half_sub {p v M N : ℕ} (hM : M % 2 = 1) (hN : N % 2 = 1) (hNM : N ≤ M) :
    ((-1 : ZMod (p ^ v)) ^ ((M - N) / 2)) = chi4 p v M * chi4 p v N := by
  unfold chi4
  have hM4 : M % 4 = 1 ∨ M % 4 = 3 := by omega
  have hN4 : N % 4 = 1 ∨ N % 4 = 3 := by omega
  rcases hM4 with hm | hm <;> rcases hN4 with hn | hn
  · have hpar : ((M - N) / 2) % 2 = 0 := by omega
    rw [if_pos hm, if_pos hn, mul_one, ← Nat.div_add_mod ((M - N) / 2) 2, hpar]
    simp [pow_add, pow_mul]
  · have hpar : ((M - N) / 2) % 2 = 1 := by omega
    rw [if_pos hm, if_neg (by omega), if_pos hn, one_mul, ← Nat.div_add_mod ((M - N) / 2) 2, hpar]
    simp [pow_add, pow_mul]
  · have hpar : ((M - N) / 2) % 2 = 1 := by omega
    rw [if_neg (by omega), if_pos hm, if_pos hn, mul_one, ← Nat.div_add_mod ((M - N) / 2) 2, hpar]
    simp [pow_add, pow_mul]
  · have hpar : ((M - N) / 2) % 2 = 0 := by omega
    rw [if_neg (by omega), if_pos hm, if_neg (by omega), if_pos hn, neg_one_mul, neg_neg,
      ← Nat.div_add_mod ((M - N) / 2) 2, hpar]
    simp [pow_add, pow_mul]

private lemma chi4_sub_two_mul {p v M t : ℕ} (hM : M % 2 = 1) (h2t : 2 * t ≤ M) :
    chi4 p v (M - 2 * t) = chi4 p v M * (-1 : ZMod (p ^ v)) ^ t := by
  unfold chi4
  have hM4 : M % 4 = 1 ∨ M % 4 = 3 := by omega
  have ht2 : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases hM4 with hm | hm <;> rcases ht2 with ht | ht
  · have h1 : (M - 2 * t) % 4 = 1 := by omega
    rw [if_pos h1, if_pos hm, ← Nat.div_add_mod t 2, ht]; simp [pow_add, pow_mul]
  · have h1 : (M - 2 * t) % 4 = 3 := by omega
    rw [if_neg (by omega), if_pos h1, if_pos hm, ← Nat.div_add_mod t 2, ht]; simp [pow_add, pow_mul]
  · have h1 : (M - 2 * t) % 4 = 3 := by omega
    rw [if_neg (by omega), if_pos h1, if_neg (by omega), if_pos hm, ← Nat.div_add_mod t 2, ht]
    simp [pow_add, pow_mul]
  · have h1 : (M - 2 * t) % 4 = 1 := by omega
    rw [if_pos h1, if_neg (by omega), if_pos hm, ← Nat.div_add_mod t 2, ht]
    simp [pow_add, pow_mul]

private lemma chi4_three_mul {p v q : ℕ} (hq : q % 2 = 1) :
    chi4 p v (3 * q) = -chi4 p v q := by
  unfold chi4
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rcases hq4 with h | h
  · rw [if_neg (by omega), if_pos (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg (by omega), if_pos h, neg_neg]

private lemma sum_alt_Hsum {p v M d : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) (hd : 1 ≤ d) :
    ∑ t ∈ (Finset.range M).filter (fun t => 0 < t ∧ d * t < M ∧ ¬ p ∣ t),
      (-1 : ZMod (p ^ v)) ^ t * (t : ZMod (p ^ v))⁻¹ =
    Hsum p v M (2 * d) - Hsum p v M d := by
  set S := (Finset.range M).filter (fun t => 0 < t ∧ d * t < M ∧ ¬ p ∣ t)
  have hsp := sum_filter_even_odd S (fun t => (-1 : ZMod (p ^ v)) ^ t * (t : ZMod (p ^ v))⁻¹)
  have hsp2 := sum_filter_even_odd S (fun t => (t : ZMod (p ^ v))⁻¹)
  have hev1 : ∑ t ∈ S.filter (fun t => 2 ∣ t), (-1 : ZMod (p ^ v)) ^ t * (t : ZMod (p ^ v))⁻¹ =
      ∑ t ∈ S.filter (fun t => 2 ∣ t), (t : ZMod (p ^ v))⁻¹ := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rcases (Finset.mem_filter.mp ht).2 with ⟨q, rfl⟩
    simp [pow_mul]
  have hodd1 : ∑ t ∈ S.filter (fun t => ¬ 2 ∣ t), (-1 : ZMod (p ^ v)) ^ t * (t : ZMod (p ^ v))⁻¹ =
      -∑ t ∈ S.filter (fun t => ¬ 2 ∣ t), (t : ZMod (p ^ v))⁻¹ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hpar : t % 2 = 1 := by have := (Finset.mem_filter.mp ht).2; omega
    rw [← Nat.div_add_mod t 2, hpar]; simp [pow_add, pow_mul]
  have hev_val := sum_even_Hsum (p := p) (v := v) (M := M) (d := d) hp hp2 hd
  have h2inv : (2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹ = 1 := zmod_two_mul_inv hp hp2
  have hS_eq : ∑ t ∈ S, (t : ZMod (p ^ v))⁻¹ = Hsum p v M d := rfl
  rw [hsp, hev1, hodd1]
  have hodd_val : ∑ t ∈ S.filter (fun t => ¬ 2 ∣ t), (t : ZMod (p ^ v))⁻¹ =
      Hsum p v M d - (2 : ZMod (p ^ v))⁻¹ * Hsum p v M (2 * d) := by
    have : Hsum p v M d = (2 : ZMod (p ^ v))⁻¹ * Hsum p v M (2 * d) +
        ∑ t ∈ S.filter (fun t => ¬ 2 ∣ t), (t : ZMod (p ^ v))⁻¹ := by
      rw [← hS_eq, hsp2, hev_val]
    exact eq_sub_of_add_eq' this.symm
  rw [hev_val, hodd_val]
  calc
    (2 : ZMod (p ^ v))⁻¹ * Hsum p v M (2 * d) +
        -(Hsum p v M d - (2 : ZMod (p ^ v))⁻¹ * Hsum p v M (2 * d))
      = ((2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹) * Hsum p v M (2 * d) - Hsum p v M d := by ring
    _ = Hsum p v M (2 * d) - Hsum p v M d := by rw [h2inv, one_mul]

-- s1(M) for odd M: 4 * s1(M) = -chi4(M) * Hsum M 2
private lemma s1_odd_eq {p v M : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2)
    (hv : 1 ≤ v) (hM : p ^ v ∣ M) (hModd : M % 2 = 1) :
    (4 : ZMod (p ^ v)) *
      ∑ N ∈ (Finset.range M).filter (fun N => 0 < N ∧ N % 2 = 1 ∧ ¬ p ∣ N),
        chi4 p v N * (N : ZMod (p ^ v))⁻¹ =
    -chi4 p v M * Hsum p v M 2 := by
  have hpM : p ∣ M := dvd_trans (dvd_pow_self p (by omega)) hM
  have hbij :
      ∑ N ∈ (Finset.range M).filter (fun N => 0 < N ∧ N % 2 = 1 ∧ ¬ p ∣ N),
        chi4 p v N * (N : ZMod (p ^ v))⁻¹ =
      -(chi4 p v M * (2 : ZMod (p ^ v))⁻¹) *
        ∑ t ∈ (Finset.range M).filter (fun t => 0 < t ∧ 2 * t < M ∧ ¬ p ∣ t),
          (-1 : ZMod (p ^ v)) ^ t * (t : ZMod (p ^ v))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun N _ => (M - N) / 2) ?_ ?_ ?_ ?_
    · intro N hN
      simp only [Finset.mem_filter, Finset.mem_range] at hN ⊢
      have hpt : ¬ p ∣ (M - N) / 2 := by
        intro h
        have h1 : p ∣ M - N := by
          rw [show M - N = 2 * ((M - N) / 2) by omega]
          exact dvd_mul_of_dvd_right h 2
        have : p ∣ N := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hN.1.le] at this
        exact hN.2.2.2 this
      exact ⟨by omega, by omega, by omega, hpt⟩
    · intro N₁ h₁ N₂ h₂ heq
      simp only [Finset.mem_filter, Finset.mem_range] at h₁ h₂
      omega
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      have hnd : ¬ p ∣ M - 2 * t := by
        intro h
        have h1 : p ∣ 2 * t := by
          have := Nat.dvd_sub hpM h
          rwa [Nat.sub_sub_self (by omega : 2 * t ≤ M)] at this
        exact (hp.dvd_mul.mp h1).elim hp2 ht.2.2.2
      refine ⟨M - 2 * t, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, by omega, hnd⟩
    · intro N hN
      simp only [Finset.mem_filter, Finset.mem_range] at hN
      set t := (M - N) / 2
      have hN_eq : N = M - 2 * t := by omega
      have hpt : ¬ p ∣ t := by
        intro h
        have h1 : p ∣ M - N := by
          rw [show M - N = 2 * t by omega]
          exact dvd_mul_of_dvd_right h 2
        have : p ∣ N := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hN.1.le] at this
        exact hN.2.2.2 this
      have h2t : ¬ p ∣ 2 * t := fun h => (hp.dvd_mul.mp h).elim hp2 hpt
      rw [hN_eq, chi4_sub_two_mul hModd (by omega), zmod_inv_sub hp hv hM (by omega) h2t,
        zmod_inv_two_mul hp hp2 hpt]
      ring
  rw [hbij, sum_alt_Hsum hp hp2 (by omega)]
  have h2inv : (2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹ = 1 := zmod_two_mul_inv hp hp2
  have h4 := Hsum_odd_four hp hp2 hv hM hModd
  calc
    (4 : ZMod (p ^ v)) * (-(chi4 p v M * (2 : ZMod (p ^ v))⁻¹) * (Hsum p v M 4 - Hsum p v M 2))
      = -chi4 p v M * ((2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹) *
          ((2 : ZMod (p ^ v)) * Hsum p v M 4 - (2 : ZMod (p ^ v)) * Hsum p v M 2) := by ring
    _ = -chi4 p v M * ((3 : ZMod (p ^ v)) * Hsum p v M 2 - (2 : ZMod (p ^ v)) * Hsum p v M 2) := by
          rw [h2inv, mul_one, h4]
    _ = -chi4 p v M * Hsum p v M 2 := by ring

-- Helper for s2(M) when 3 ∤ M: 3 * SM = Hsum M 2
private lemma SM_odd_not_dvd3 {p v M : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3)
    (hv : 1 ≤ v) (hM : p ^ v ∣ M) (hModd : M % 2 = 1) (hM3 : ¬ 3 ∣ M) :
    (3 : ZMod (p ^ v)) *
      ∑ u ∈ (Finset.range M).filter (fun u => 0 < u ∧ 2 * u < M ∧ u % 3 = M % 3 ∧ ¬ p ∣ u),
        (u : ZMod (p ^ v))⁻¹ = Hsum p v M 2 := by
  have hpM : p ∣ M := dvd_trans (dvd_pow_self p (by omega)) hM
  set Sfull := (Finset.range M).filter (fun u => 0 < u ∧ u % 3 = M % 3 ∧ ¬ p ∣ u)
  have hsp := (Finset.sum_filter_add_sum_filter_not Sfull (fun u => 2 * u < M)
    (fun u => (u : ZMod (p ^ v))⁻¹)).symm
  -- Sfull = -3⁻¹ * Hsum M 3 (via u ↦ (M - u) / 3)
  have hfull_eq : ∑ u ∈ Sfull, (u : ZMod (p ^ v))⁻¹ =
      -((3 : ZMod (p ^ v))⁻¹ * Hsum p v M 3) := by
    unfold Hsum
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun u _ => (M - u) / 3) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Sfull, Finset.mem_filter, Finset.mem_range] at hu ⊢
      have hpz : ¬ p ∣ (M - u) / 3 := by
        intro h
        have h1 : p ∣ M - u := by
          rw [show M - u = 3 * ((M - u) / 3) by omega]
          exact dvd_mul_of_dvd_right h 3
        have : p ∣ u := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hu.1.le] at this
        exact hu.2.2.2 this
      exact ⟨by omega, by omega, by omega, hpz⟩
    · intro u₁ h₁ u₂ h₂ heq
      simp only [Sfull, Finset.mem_filter, Finset.mem_range] at h₁ h₂
      omega
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_range] at hz
      have hnd : ¬ p ∣ M - 3 * z := by
        intro h
        have h1 : p ∣ 3 * z := by
          have := Nat.dvd_sub hpM h
          rwa [Nat.sub_sub_self (by omega : 3 * z ≤ M)] at this
        exact (hp.dvd_mul.mp h1).elim hp3 hz.2.2.2
      refine ⟨M - 3 * z, ?_, by omega⟩
      simp only [Sfull, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, by omega, hnd⟩
    · intro u hu
      simp only [Sfull, Finset.mem_filter, Finset.mem_range] at hu
      set z := (M - u) / 3
      have hu_eq : u = M - 3 * z := by omega
      have hpz : ¬ p ∣ z := by
        intro h
        have h1 : p ∣ M - u := by
          rw [show M - u = 3 * z by omega]
          exact dvd_mul_of_dvd_right h 3
        have : p ∣ u := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hu.1.le] at this
        exact hu.2.2.2 this
      have h3z : ¬ p ∣ 3 * z := fun h => (hp.dvd_mul.mp h).elim hp3 hpz
      rw [hu_eq, zmod_inv_sub hp hv hM (by omega) h3z, zmod_inv_three_mul hp hp3 hpz]
  -- Upper half of Sfull (2*u > M) = -3⁻¹ * Hsum M 6 (via u ↦ (M - u) / 3)
  have hhi_eq : ∑ u ∈ Sfull.filter (fun u => ¬ 2 * u < M), (u : ZMod (p ^ v))⁻¹ =
      -((3 : ZMod (p ^ v))⁻¹ * Hsum p v M 6) := by
    unfold Hsum
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun u _ => (M - u) / 3) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Sfull, Finset.mem_filter, Finset.mem_range] at hu ⊢
      have hpz : ¬ p ∣ (M - u) / 3 := by
        intro h
        have h1 : p ∣ M - u := by
          rw [show M - u = 3 * ((M - u) / 3) by omega]
          exact dvd_mul_of_dvd_right h 3
        have : p ∣ u := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hu.1.1.le] at this
        exact hu.1.2.2.2 this
      exact ⟨by omega, by omega, by omega, hpz⟩
    · intro u₁ h₁ u₂ h₂ heq
      simp only [Sfull, Finset.mem_filter, Finset.mem_range] at h₁ h₂
      omega
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_range] at hz
      have hnd : ¬ p ∣ M - 3 * z := by
        intro h
        have h1 : p ∣ 3 * z := by
          have := Nat.dvd_sub hpM h
          rwa [Nat.sub_sub_self (by omega : 3 * z ≤ M)] at this
        exact (hp.dvd_mul.mp h1).elim hp3 hz.2.2.2
      refine ⟨M - 3 * z, ?_, by omega⟩
      simp only [Sfull, Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨by omega, by omega, by omega, hnd⟩, by omega⟩
    · intro u hu
      simp only [Sfull, Finset.mem_filter, Finset.mem_range] at hu
      set z := (M - u) / 3
      have hu_eq : u = M - 3 * z := by omega
      have hpz : ¬ p ∣ z := by
        intro h
        have h1 : p ∣ M - u := by
          rw [show M - u = 3 * z by omega]
          exact dvd_mul_of_dvd_right h 3
        have : p ∣ u := by
          have := Nat.dvd_sub hpM h1
          rwa [Nat.sub_sub_self hu.1.1.le] at this
        exact hu.1.2.2.2 this
      have h3z : ¬ p ∣ 3 * z := fun h => (hp.dvd_mul.mp h).elim hp3 hpz
      rw [hu_eq, zmod_inv_sub hp hv hM (by omega) h3z, zmod_inv_three_mul hp hp3 hpz]
  have hlo_set : Sfull.filter (fun u => 2 * u < M) =
      (Finset.range M).filter (fun u => 0 < u ∧ 2 * u < M ∧ u % 3 = M % 3 ∧ ¬ p ∣ u) := by
    ext u; simp only [Sfull, Finset.mem_filter, Finset.mem_range]; tauto
  have h3inv : (3 : ZMod (p ^ v)) * (3 : ZMod (p ^ v))⁻¹ = 1 := zmod_three_mul_inv hp hp3
  have hcomb : -((3 : ZMod (p ^ v))⁻¹ * Hsum p v M 3) =
      ∑ u ∈ (Finset.range M).filter (fun u => 0 < u ∧ 2 * u < M ∧ u % 3 = M % 3 ∧ ¬ p ∣ u),
        (u : ZMod (p ^ v))⁻¹ +
      -((3 : ZMod (p ^ v))⁻¹ * Hsum p v M 6) := by
    rw [← hfull_eq, hsp, hlo_set, hhi_eq]
  have hmul3 := congrArg (fun x => (3 : ZMod (p ^ v)) * x) hcomb
  have hstep : -Hsum p v M 3 =
      (3 : ZMod (p ^ v)) *
        ∑ u ∈ (Finset.range M).filter (fun u => 0 < u ∧ 2 * u < M ∧ u % 3 = M % 3 ∧ ¬ p ∣ u),
          (u : ZMod (p ^ v))⁻¹ - Hsum p v M 6 := by
    calc
      -Hsum p v M 3
        = (3 : ZMod (p ^ v)) * -((3 : ZMod (p ^ v))⁻¹ * Hsum p v M 3) := by
          rw [mul_neg, ← mul_assoc, h3inv, one_mul]
      _ = (3 : ZMod (p ^ v)) * (
          ∑ u ∈ (Finset.range M).filter (fun u => 0 < u ∧ 2 * u < M ∧ u % 3 = M % 3 ∧ ¬ p ∣ u),
            (u : ZMod (p ^ v))⁻¹ +
          -((3 : ZMod (p ^ v))⁻¹ * Hsum p v M 6)) := hmul3
      _ = (3 : ZMod (p ^ v)) *
          ∑ u ∈ (Finset.range M).filter (fun u => 0 < u ∧ 2 * u < M ∧ u % 3 = M % 3 ∧ ¬ p ∣ u),
            (u : ZMod (p ^ v))⁻¹ -
          ((3 : ZMod (p ^ v)) * (3 : ZMod (p ^ v))⁻¹) * Hsum p v M 6 := by ring
      _ = _ := by rw [h3inv, one_mul]
  calc
    (3 : ZMod (p ^ v)) *
        ∑ u ∈ (Finset.range M).filter (fun u => 0 < u ∧ 2 * u < M ∧ u % 3 = M % 3 ∧ ¬ p ∣ u),
          (u : ZMod (p ^ v))⁻¹
      = Hsum p v M 6 - Hsum p v M 3 := by
        have := congrArg (fun x => x + Hsum p v M 6) hstep
        calc (3 : ZMod (p ^ v)) * ∑ u ∈ (Finset.range M).filter (fun u => 0 < u ∧ 2 * u < M ∧ u % 3 = M % 3 ∧ ¬ p ∣ u), (u : ZMod (p ^ v))⁻¹
          = -Hsum p v M 3 + Hsum p v M 6 := by simpa [sub_add_cancel] using this.symm
          _ = Hsum p v M 6 - Hsum p v M 3 := by ring
    _ = Hsum p v M 2 := Hsum_odd_six hp hp2 hp3 hv hM hModd

-- s2(M) for odd M: 4 * s2(M) = chi4(M) * Hsum M 2
private lemma s2_odd_eq {p v M : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 2) (hp3 : ¬ p ∣ 3)
    (hv : 1 ≤ v) (hM : p ^ v ∣ M) (hModd : M % 2 = 1) :
    (4 : ZMod (p ^ v)) *
      ∑ q ∈ (Finset.range M).filter (fun q => 0 < q ∧ 3 * q < M ∧ q % 2 = 1 ∧ ¬ p ∣ q),
        chi4 p v q * (q : ZMod (p ^ v))⁻¹ =
    chi4 p v M * Hsum p v M 2 := by
  have hpM : p ∣ M := dvd_trans (dvd_pow_self p (by omega)) hM
  by_cases hM3 : 3 ∣ M
  · -- Case 3 | M: M = 3*K, s2(M) = s1(K)
    rcases hM3 with ⟨K, rfl⟩
    have hKodd : K % 2 = 1 := by omega
    have hcop : Nat.Coprime (p ^ v) 3 := (hp.coprime_iff_not_dvd.mpr hp3).pow_left v
    have hpvK : p ^ v ∣ K := hcop.dvd_of_dvd_mul_left hM
    have hset : (Finset.range (3 * K)).filter (fun q => 0 < q ∧ 3 * q < 3 * K ∧ q % 2 = 1 ∧ ¬ p ∣ q) =
        (Finset.range K).filter (fun q => 0 < q ∧ q % 2 = 1 ∧ ¬ p ∣ q) := by
      ext q; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hset, s1_odd_eq hp hp2 hv hpvK hKodd, chi4_three_mul hKodd, neg_mul]
    have hH6 : Hsum p v K 2 = Hsum p v (3 * K) 6 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, Hsum_three_mul (by omega)]
    have hH3 : Hsum p v (3 * K) 3 = 0 := by
      rw [show (3 : ℕ) = 3 * 1 by norm_num, Hsum_three_mul (by omega)]
      exact Hsum_one_eq_zero hp hp2 hv hpvK
    have h6 := Hsum_odd_six hp hp2 hp3 hv hM hModd
    rw [hH3, sub_zero] at h6
    rw [hH6, h6]; ring
  · -- Case 3 ∤ M: reduce s2 -> Tm -> SM -> Hsum M 2
    set Tm := ∑ t ∈ (Finset.range M).filter (fun t => 0 < t ∧ 2 * t < M ∧ t % 3 = (2 * M) % 3 ∧ ¬ p ∣ t),
      (-1 : ZMod (p ^ v)) ^ t * (t : ZMod (p ^ v))⁻¹
    have hs2_Tm :
        ∑ q ∈ (Finset.range M).filter (fun q => 0 < q ∧ 3 * q < M ∧ q % 2 = 1 ∧ ¬ p ∣ q),
          chi4 p v q * (q : ZMod (p ^ v))⁻¹ =
        (3 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹ * chi4 p v M * Tm := by
      dsimp only [Tm]
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun q _ => (M - 3 * q) / 2) ?_ ?_ ?_ ?_
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
        have hpt : ¬ p ∣ (M - 3 * q) / 2 := by
          intro h
          have h1 : p ∣ M - 3 * q := by
            rw [show M - 3 * q = 2 * ((M - 3 * q) / 2) by omega]
            exact dvd_mul_of_dvd_right h 2
          have h2 : p ∣ 3 * q := by
            have := Nat.dvd_sub hpM h1
            rwa [Nat.sub_sub_self hq.2.2.1.le] at this
          exact (hp.dvd_mul.mp h2).elim hp3 hq.2.2.2.2
        exact ⟨by omega, by omega, by omega, by omega, hpt⟩
      · intro q₁ h₁ q₂ h₂ heq
        simp only [Finset.mem_filter, Finset.mem_range] at h₁ h₂
        omega
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_range] at ht
        have h3dvd : 3 ∣ M - 2 * t := by omega
        have hpq : ¬ p ∣ (M - 2 * t) / 3 := by
          intro h
          have h1 : p ∣ M - 2 * t := by
            rw [show M - 2 * t = 3 * ((M - 2 * t) / 3) by omega]
            exact dvd_mul_of_dvd_right h 3
          have h2 : p ∣ 2 * t := by
            have := Nat.dvd_sub hpM h1
            rwa [Nat.sub_sub_self ht.2.2.1.le] at this
          exact (hp.dvd_mul.mp h2).elim hp2 ht.2.2.2.2
        refine ⟨(M - 2 * t) / 3, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by omega, by omega, by omega, hpq⟩
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_range] at hq
        set t := (M - 3 * q) / 2
        have h3q : 3 * q = M - 2 * t := by omega
        have hpt : ¬ p ∣ t := by
          intro h
          have h1 : p ∣ M - 3 * q := by
            rw [show M - 3 * q = 2 * t by omega]
            exact dvd_mul_of_dvd_right h 2
          have h2 : p ∣ 3 * q := by
            have := Nat.dvd_sub hpM h1
            rwa [Nat.sub_sub_self hq.2.2.1.le] at this
          exact (hp.dvd_mul.mp h2).elim hp3 hq.2.2.2.2
        have h2t : ¬ p ∣ 2 * t := fun h => (hp.dvd_mul.mp h).elim hp2 hpt
        have hchi : chi4 p v q = -(chi4 p v M * (-1 : ZMod (p ^ v)) ^ t) := by
          have := chi4_three_mul (p := p) (v := v) hq.2.2.2.1
          rw [h3q, chi4_sub_two_mul hModd (by omega)] at this
          rw [← neg_neg (chi4 p v q), ← this]
        have hqinv : (q : ZMod (p ^ v))⁻¹ =
            -((3 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹ * (t : ZMod (p ^ v))⁻¹) := by
          have h3inv := zmod_inv_three_mul (p := p) (v := v) hp hp3 hq.2.2.2.2
          rw [h3q, zmod_inv_sub hp hv hM (by omega) h2t, zmod_inv_two_mul hp hp2 hpt] at h3inv
          have hm := congrArg (fun x => (3 : ZMod (p ^ v)) * x) h3inv
          have h3u := zmod_three_mul_inv (p := p) (v := v) hp hp3
          calc
            (q : ZMod (p ^ v))⁻¹
              = ((3 : ZMod (p ^ v)) * (3 : ZMod (p ^ v))⁻¹) * (q : ZMod (p ^ v))⁻¹ := by
                rw [h3u, one_mul]
            _ = (3 : ZMod (p ^ v)) * ((3 : ZMod (p ^ v))⁻¹ * (q : ZMod (p ^ v))⁻¹) := by ring
            _ = (3 : ZMod (p ^ v)) * -((2 : ZMod (p ^ v))⁻¹ * (t : ZMod (p ^ v))⁻¹) := hm.symm
            _ = -((3 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹ * (t : ZMod (p ^ v))⁻¹) := by ring
        rw [hchi, hqinv]
        ring
    -- Now prove Tm = 2⁻¹ * SM by splitting Tm into even and odd t!
    set SMset := (Finset.range M).filter (fun u => 0 < u ∧ 2 * u < M ∧ u % 3 = M % 3 ∧ ¬ p ∣ u)
    have hTm_SM : Tm = (2 : ZMod (p ^ v))⁻¹ * ∑ u ∈ SMset, (u : ZMod (p ^ v))⁻¹ := by
      set Tset := (Finset.range M).filter (fun t => 0 < t ∧ 2 * t < M ∧ t % 3 = (2 * M) % 3 ∧ ¬ p ∣ t)
      have hsp := sum_filter_even_odd Tset (fun t => (-1 : ZMod (p ^ v)) ^ t * (t : ZMod (p ^ v))⁻¹)
      have hspSM := (Finset.sum_filter_add_sum_filter_not SMset (fun u => 4 * u < M)
        (fun u => (u : ZMod (p ^ v))⁻¹)).symm
      -- Even t = 2*u gives 2⁻¹ * ∑_{u ∈ SMset, 4*u < M} u⁻¹
      have hev : ∑ t ∈ Tset.filter (fun t => 2 ∣ t), (-1 : ZMod (p ^ v)) ^ t * (t : ZMod (p ^ v))⁻¹ =
          (2 : ZMod (p ^ v))⁻¹ * ∑ u ∈ SMset.filter (fun u => 4 * u < M), (u : ZMod (p ^ v))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun t _ => t / 2) ?_ ?_ ?_ ?_
        · intro t ht
          simp only [Tset, SMset, Finset.mem_filter, Finset.mem_range] at ht ⊢
          rcases ht.2 with ⟨u, rfl⟩
          have hpu : ¬ p ∣ u := fun h => ht.1.2.2.2.2 (dvd_mul_of_dvd_right h 2)
          rw [Nat.mul_div_cancel_left u (by omega)]
          exact ⟨⟨by omega, by omega, by omega, by omega, hpu⟩, by omega⟩
        · intro t₁ h₁ t₂ h₂ heq
          simp only [Finset.mem_filter] at h₁ h₂
          rcases h₁.2 with ⟨u₁, rfl⟩; rcases h₂.2 with ⟨u₂, rfl⟩
          rw [Nat.mul_div_cancel_left u₁ (by omega), Nat.mul_div_cancel_left u₂ (by omega)] at heq
          rw [heq]
        · intro u hu
          simp only [SMset, Tset, Finset.mem_filter, Finset.mem_range] at hu
          have h2u : ¬ p ∣ 2 * u := fun h => (hp.dvd_mul.mp h).elim hp2 hu.1.2.2.2.2
          refine ⟨2 * u, ?_, Nat.mul_div_cancel_left u (by omega)⟩
          simp only [Tset, Finset.mem_filter, Finset.mem_range]
          exact ⟨⟨by omega, by omega, by omega, by omega, h2u⟩, ⟨u, rfl⟩⟩
        · intro t ht
          simp only [Tset, Finset.mem_filter] at ht
          rcases ht.2 with ⟨u, rfl⟩
          have hpu : ¬ p ∣ u := fun h => ht.1.2.2.2.2 (dvd_mul_of_dvd_right h 2)
          rw [Nat.mul_div_cancel_left u (by omega), pow_mul, neg_one_sq, one_pow, one_mul,
            zmod_inv_two_mul hp hp2 hpu]
      -- Odd t: M - t = 2*u gives 2⁻¹ * ∑_{u ∈ SMset, ¬ 4*u < M} u⁻¹
      have hodd : ∑ t ∈ Tset.filter (fun t => ¬ 2 ∣ t), (-1 : ZMod (p ^ v)) ^ t * (t : ZMod (p ^ v))⁻¹ =
          (2 : ZMod (p ^ v))⁻¹ * ∑ u ∈ SMset.filter (fun u => ¬ 4 * u < M), (u : ZMod (p ^ v))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun t _ => (M - t) / 2) ?_ ?_ ?_ ?_
        · intro t ht
          simp only [Tset, SMset, Finset.mem_filter, Finset.mem_range] at ht ⊢
          have hpu : ¬ p ∣ (M - t) / 2 := by
            intro h
            have h1 : p ∣ M - t := by
              rw [show M - t = 2 * ((M - t) / 2) by omega]
              exact dvd_mul_of_dvd_right h 2
            have : p ∣ t := by
              have := Nat.dvd_sub hpM h1
              rwa [Nat.sub_sub_self ht.1.1.le] at this
            exact ht.1.2.2.2.2 this
          exact ⟨⟨by omega, by omega, by omega, by omega, hpu⟩, by omega⟩
        · intro t₁ h₁ t₂ h₂ heq
          simp only [Tset, Finset.mem_filter, Finset.mem_range] at h₁ h₂
          omega
        · intro u hu
          simp only [SMset, Tset, Finset.mem_filter, Finset.mem_range] at hu
          have hnd : ¬ p ∣ M - 2 * u := by
            intro h
            have h1 : p ∣ 2 * u := by
              have := Nat.dvd_sub hpM h
              rwa [Nat.sub_sub_self hu.1.2.2.1.le] at this
            exact (hp.dvd_mul.mp h1).elim hp2 hu.1.2.2.2.2
          refine ⟨M - 2 * u, ?_, by omega⟩
          simp only [Tset, Finset.mem_filter, Finset.mem_range]
          exact ⟨⟨by omega, by omega, by omega, by omega, hnd⟩, by omega⟩
        · intro t ht
          simp only [Tset, Finset.mem_filter, Finset.mem_range] at ht
          set u := (M - t) / 2
          have ht_eq : t = M - 2 * u := by omega
          have hpu : ¬ p ∣ u := by
            intro h
            have h1 : p ∣ M - t := by
              rw [show M - t = 2 * u by omega]
              exact dvd_mul_of_dvd_right h 2
            have : p ∣ t := by
              have := Nat.dvd_sub hpM h1
              rwa [Nat.sub_sub_self ht.1.1.le] at this
            exact ht.1.2.2.2.2 this
          have h2u : ¬ p ∣ 2 * u := fun h => (hp.dvd_mul.mp h).elim hp2 hpu
          have hpar : t % 2 = 1 := by omega
          have hneg1 : (-1 : ZMod (p ^ v)) ^ t = -1 := by
            rw [← Nat.div_add_mod t 2, hpar]; simp [pow_add, pow_mul]
          rw [hneg1, ht_eq, zmod_inv_sub hp hv hM (by omega) h2u, zmod_inv_two_mul hp hp2 hpu]
          ring
      dsimp only [Tm]
      rw [hsp, hev, hodd, ← mul_add, ← hspSM]
    have h2inv : (2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹ = 1 := zmod_two_mul_inv hp hp2
    have hSM := SM_odd_not_dvd3 hp hp2 hp3 hv hM hModd hM3
    rw [hs2_Tm, hTm_SM]
    calc
      (4 : ZMod (p ^ v)) * ((3 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹ * chi4 p v M *
          ((2 : ZMod (p ^ v))⁻¹ * ∑ u ∈ SMset, (u : ZMod (p ^ v))⁻¹))
        = ((2 : ZMod (p ^ v)) * (2 : ZMod (p ^ v))⁻¹) ^ 2 * chi4 p v M *
            ((3 : ZMod (p ^ v)) * ∑ u ∈ SMset, (u : ZMod (p ^ v))⁻¹) := by ring
      _ = chi4 p v M * Hsum p v M 2 := by rw [h2inv, one_pow, one_mul, hSM]

-- Key Harmonic Theorem in ZMod (p^v): W_k = 0 in ZMod (p^v) whenever p^v | M = p*k
private lemma W_sum_zmod_zero {p v M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hv : 1 ≤ v) (hM : p ^ v ∣ M) :
    ∑ N ∈ (Finset.range M).filter (fun N => 0 < N ∧ (M - N) % 2 = 0 ∧ ¬ p ∣ N),
      ((-1 : ZMod (p ^ v)) ^ ((M - N) / 2)) * (c_seq N : ZMod (p ^ v)) * (N : ZMod (p ^ v))⁻¹ = 0 := by
  have hp2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hp3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hpM : p ∣ M := dvd_trans (dvd_pow_self p (by omega)) hM
  by_cases hMev : M % 2 = 0
  · -- Case M = 2*K even
    obtain ⟨K, rfl⟩ : ∃ K, M = 2 * K := ⟨M / 2, by omega⟩
    have hcop2 : Nat.Coprime (p ^ v) 2 := (hp.coprime_iff_not_dvd.mpr hp2).pow_left v
    have hpvK : p ^ v ∣ K := hcop2.dvd_of_dvd_mul_left hM
    -- Reindex N = 2*m, 1 ≤ m < K, ¬ p ∣ m
    have hreindex :
        ∑ N ∈ (Finset.range (2 * K)).filter (fun N => 0 < N ∧ (2 * K - N) % 2 = 0 ∧ ¬ p ∣ N),
          ((-1 : ZMod (p ^ v)) ^ ((2 * K - N) / 2)) * (c_seq N : ZMod (p ^ v)) * (N : ZMod (p ^ v))⁻¹ =
        (-1 : ZMod (p ^ v)) ^ K * (2 : ZMod (p ^ v))⁻¹ *
          ∑ m ∈ (Finset.range K).filter (fun m => 0 < m ∧ ¬ p ∣ m),
            ((-1 : ZMod (p ^ v)) ^ m * (1 - (if 3 ∣ m then (3 : ZMod (p ^ v)) else 0)) + 2) *
              (m : ZMod (p ^ v))⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun N _ => N / 2) ?_ ?_ ?_ ?_
      · intro N hN
        simp only [Finset.mem_filter, Finset.mem_range] at hN ⊢
        have hpm : ¬ p ∣ N / 2 := fun h => hN.2.2.2 (by rw [show N = 2 * (N / 2) by omega]; exact dvd_mul_of_dvd_right h 2)
        exact ⟨by omega, by omega, hpm⟩
      · intro N₁ h₁ N₂ h₂ heq
        simp only [Finset.mem_filter, Finset.mem_range] at h₁ h₂
        omega
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_range] at hm
        have h2m : ¬ p ∣ 2 * m := fun h => (hp.dvd_mul.mp h).elim hp2 hm.2.2
        refine ⟨2 * m, ?_, Nat.mul_div_cancel_left m (by omega)⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by omega, by omega, h2m⟩
      · intro N hN
        simp only [Finset.mem_filter, Finset.mem_range] at hN
        set m := N / 2
        have hN_eq : N = 2 * m := by omega
        have hm0 : 0 < m := by omega
        have hpm : ¬ p ∣ m := fun h => hN.2.2.2 (hN_eq ▸ dvd_mul_of_dvd_right h 2)
        rw [hN_eq]
        have hdiv1 : (2 * K - 2 * m) / 2 = K - m := by omega
        have hdiv2 : (2 * m) / 2 = m := Nat.mul_div_cancel_left m (by omega)
        have h3iff : (3 ∣ 2 * m) ↔ (3 ∣ m) := by
          constructor
          · intro h; exact ((Nat.Prime.dvd_mul (by decide)).mp h).resolve_left (by decide)
          · exact fun h => dvd_mul_of_dvd_right h 2
        have hc : (c_seq (2 * m) : ZMod (p ^ v)) =
            1 - (if 3 ∣ m then (3 : ZMod (p ^ v)) else 0) + 2 * (-1 : ZMod (p ^ v)) ^ m := by
          unfold c_seq
          rw [if_congr h3iff rfl rfl, if_pos (dvd_mul_right 2 m), hdiv2]
          have hpow : (-1 : ZMod (p ^ v)) ^ (m - 1) = -((-1 : ZMod (p ^ v)) ^ m) := by
            have hm1 : m = (m - 1) + 1 := by omega
            conv_rhs => rw [hm1, pow_succ]
            ring
          push_cast
          split_ifs <;> rw [hpow] <;> ring
        have hpowKm : (-1 : ZMod (p ^ v)) ^ (K - m) = (-1 : ZMod (p ^ v)) ^ K * (-1 : ZMod (p ^ v)) ^ m := by
          have : (-1 : ZMod (p ^ v)) ^ (K - m) * (-1 : ZMod (p ^ v)) ^ m = (-1 : ZMod (p ^ v)) ^ K := by
            rw [← pow_add, Nat.sub_add_cancel (by omega)]
          calc
            (-1 : ZMod (p ^ v)) ^ (K - m)
              = ((-1 : ZMod (p ^ v)) ^ (K - m) * (-1 : ZMod (p ^ v)) ^ m) * (-1 : ZMod (p ^ v)) ^ m := by
                rw [mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
            _ = (-1 : ZMod (p ^ v)) ^ K * (-1 : ZMod (p ^ v)) ^ m := by rw [this]
        have hpow_m2 : (-1 : ZMod (p ^ v)) ^ m * (-1 : ZMod (p ^ v)) ^ m = 1 := by
          rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
        rw [hdiv1, hc, hpowKm, zmod_inv_two_mul hp hp2 hpm]
        calc
          (-1 : ZMod (p ^ v)) ^ K * (-1 : ZMod (p ^ v)) ^ m *
              (1 - (if 3 ∣ m then (3 : ZMod (p ^ v)) else 0) + 2 * (-1 : ZMod (p ^ v)) ^ m) *
              ((2 : ZMod (p ^ v))⁻¹ * (m : ZMod (p ^ v))⁻¹)
            = (-1 : ZMod (p ^ v)) ^ K * (2 : ZMod (p ^ v))⁻¹ *
                ((-1 : ZMod (p ^ v)) ^ m * (1 - (if 3 ∣ m then (3 : ZMod (p ^ v)) else 0)) +
                  2 * ((-1 : ZMod (p ^ v)) ^ m * (-1 : ZMod (p ^ v)) ^ m)) * (m : ZMod (p ^ v))⁻¹ := by ring
          _ = (-1 : ZMod (p ^ v)) ^ K * (2 : ZMod (p ^ v))⁻¹ *
                (((-1 : ZMod (p ^ v)) ^ m * (1 - (if 3 ∣ m then (3 : ZMod (p ^ v)) else 0)) + 2) *
                  (m : ZMod (p ^ v))⁻¹) := by rw [hpow_m2]; ring
    rw [hreindex]
    -- Split the inner sum into 3 pieces:
    -- (1) ∑ (-1)^m m⁻¹ = Hsum K 2 - Hsum K 1 = Hsum K 2
    -- (2) -∑_{3|m} (-1)^m * 3 * m⁻¹ = -∑_{3q < K} (-1)^q q⁻¹ = -(Hsum K 6 - Hsum K 3)
    -- (3) 2 * ∑ m⁻¹ = 2 * Hsum K 1 = 0
    set Sk := (Finset.range K).filter (fun m => 0 < m ∧ ¬ p ∣ m)
    have hsplit_inner :
        ∑ m ∈ Sk, ((-1 : ZMod (p ^ v)) ^ m * (1 - (if 3 ∣ m then (3 : ZMod (p ^ v)) else 0)) + 2) *
            (m : ZMod (p ^ v))⁻¹ =
        ∑ m ∈ Sk, (-1 : ZMod (p ^ v)) ^ m * (m : ZMod (p ^ v))⁻¹ -
        ∑ m ∈ Sk.filter (fun m => 3 ∣ m), (-1 : ZMod (p ^ v)) ^ m * (3 : ZMod (p ^ v)) * (m : ZMod (p ^ v))⁻¹ +
        2 * ∑ m ∈ Sk, (m : ZMod (p ^ v))⁻¹ := by
      have h3f : ∑ m ∈ Sk, (if 3 ∣ m then (-1 : ZMod (p ^ v)) ^ m * (3 : ZMod (p ^ v)) * (m : ZMod (p ^ v))⁻¹ else 0) =
          ∑ m ∈ Sk.filter (fun m => 3 ∣ m), (-1 : ZMod (p ^ v)) ^ m * (3 : ZMod (p ^ v)) * (m : ZMod (p ^ v))⁻¹ :=
        (Finset.sum_filter (s := Sk) (p := fun m => 3 ∣ m) (f := fun m => (-1 : ZMod (p ^ v)) ^ m * (3 : ZMod (p ^ v)) * (m : ZMod (p ^ v))⁻¹)).symm
      rw [← h3f, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> ring
    have hp1 : ∑ m ∈ Sk, (-1 : ZMod (p ^ v)) ^ m * (m : ZMod (p ^ v))⁻¹ = Hsum p v K 2 := by
      have hset : Sk = (Finset.range K).filter (fun m => 0 < m ∧ 1 * m < K ∧ ¬ p ∣ m) := by
        ext m; simp only [Sk, Finset.mem_filter, Finset.mem_range]; omega
      rw [hset, sum_alt_Hsum hp hp2 (by omega), mul_one, Hsum_one_eq_zero hp hp2 hv hpvK, sub_zero]
    have hp3_sum : ∑ m ∈ Sk, (m : ZMod (p ^ v))⁻¹ = 0 := by
      have hset : Sk = (Finset.range K).filter (fun m => 0 < m ∧ 1 * m < K ∧ ¬ p ∣ m) := by
        ext m; simp only [Sk, Finset.mem_filter, Finset.mem_range]; omega
      rw [hset]; exact Hsum_one_eq_zero hp hp2 hv hpvK
    have hp2_sum :
        ∑ m ∈ Sk.filter (fun m => 3 ∣ m), (-1 : ZMod (p ^ v)) ^ m * (3 : ZMod (p ^ v)) * (m : ZMod (p ^ v))⁻¹ =
        Hsum p v K 6 - Hsum p v K 3 := by
      have hbij3 :
          ∑ m ∈ Sk.filter (fun m => 3 ∣ m), (-1 : ZMod (p ^ v)) ^ m * (3 : ZMod (p ^ v)) * (m : ZMod (p ^ v))⁻¹ =
          ∑ q ∈ (Finset.range K).filter (fun q => 0 < q ∧ 3 * q < K ∧ ¬ p ∣ q),
            (-1 : ZMod (p ^ v)) ^ q * (q : ZMod (p ^ v))⁻¹ := by
        refine Finset.sum_bij (fun m _ => m / 3) ?_ ?_ ?_ ?_
        · intro m hm
          simp only [Sk, Finset.mem_filter, Finset.mem_range] at hm ⊢
          rcases hm.2 with ⟨q, rfl⟩
          have hpq : ¬ p ∣ q := fun h => hm.1.2.2 (dvd_mul_of_dvd_right h 3)
          rw [Nat.mul_div_cancel_left q (by omega)]
          exact ⟨by omega, by omega, by omega, hpq⟩
        · intro m₁ h₁ m₂ h₂ heq
          simp only [Finset.mem_filter] at h₁ h₂
          rcases h₁.2 with ⟨q₁, rfl⟩; rcases h₂.2 with ⟨q₂, rfl⟩
          rw [Nat.mul_div_cancel_left q₁ (by omega), Nat.mul_div_cancel_left q₂ (by omega)] at heq
          rw [heq]
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_range] at hq
          have h3q : ¬ p ∣ 3 * q := fun h => (hp.dvd_mul.mp h).elim hp3 hq.2.2.2
          refine ⟨3 * q, ?_, Nat.mul_div_cancel_left q (by omega)⟩
          simp only [Sk, Finset.mem_filter, Finset.mem_range]
          exact ⟨⟨by omega, by omega, h3q⟩, ⟨q, rfl⟩⟩
        · intro m hm
          simp only [Sk, Finset.mem_filter] at hm
          rcases hm.2 with ⟨q, rfl⟩
          have hpq : ¬ p ∣ q := fun h => hm.1.2.2 (dvd_mul_of_dvd_right h 3)
          rw [Nat.mul_div_cancel_left q (by omega), zmod_inv_three_mul hp hp3 hpq]
          have hpow3 : (-1 : ZMod (p ^ v)) ^ (3 * q) = (-1 : ZMod (p ^ v)) ^ q := by
            rw [pow_mul]; norm_num
          have h3u := zmod_three_mul_inv (p := p) (v := v) hp hp3
          rw [hpow3]
          calc
            (-1 : ZMod (p ^ v)) ^ q * (3 : ZMod (p ^ v)) * ((3 : ZMod (p ^ v))⁻¹ * (q : ZMod (p ^ v))⁻¹)
              = (-1 : ZMod (p ^ v)) ^ q * ((3 : ZMod (p ^ v)) * (3 : ZMod (p ^ v))⁻¹) * (q : ZMod (p ^ v))⁻¹ := by ring
            _ = (-1 : ZMod (p ^ v)) ^ q * (q : ZMod (p ^ v))⁻¹ := by rw [h3u, mul_one]
      rw [hbij3, sum_alt_Hsum hp hp2 (by omega)]
    rw [hsplit_inner, hp1, hp2_sum, hp3_sum, mul_zero, add_zero]
    -- Show Hsum K 2 - (Hsum K 6 - Hsum K 3) = 0 for both K odd and K even!
    have hK_zero : Hsum p v K 2 - (Hsum p v K 6 - Hsum p v K 3) = 0 := by
      by_cases hKev : K % 2 = 0
      · obtain ⟨L, rfl⟩ : ∃ L, K = 2 * L := ⟨K / 2, by omega⟩
        have hcop2' : Nat.Coprime (p ^ v) 2 := (hp.coprime_iff_not_dvd.mpr hp2).pow_left v
        have hpvL : p ^ v ∣ L := hcop2'.dvd_of_dvd_mul_left hpvK
        have h2 : Hsum p v (2 * L) 2 = 0 := by
          rw [show (2 : ℕ) = 2 * 1 by norm_num, Hsum_two_mul (by omega)]
          exact Hsum_one_eq_zero hp hp2 hv hpvL
        have h63 := Hsum_even_six hp hp2 hp3 hv hpvK
        rw [h2, h63, sub_self, sub_self]
      · have hKodd : K % 2 = 1 := by omega
        rw [Hsum_odd_six hp hp2 hp3 hv hpvK hKodd, sub_self]
    rw [hK_zero, mul_zero]
  · -- Case M odd: rewrite as chi4(M) * (s1(M) + s2(M)) = 0
    have hModd : M % 2 = 1 := by omega
    set S1 := (Finset.range M).filter (fun N => 0 < N ∧ N % 2 = 1 ∧ ¬ p ∣ N)
    have hset : (Finset.range M).filter (fun N => 0 < N ∧ (M - N) % 2 = 0 ∧ ¬ p ∣ N) = S1 := by
      ext N; simp only [S1, Finset.mem_filter, Finset.mem_range]; omega
    rw [hset]
    have hsplit :
        ∑ N ∈ S1, ((-1 : ZMod (p ^ v)) ^ ((M - N) / 2)) * (c_seq N : ZMod (p ^ v)) * (N : ZMod (p ^ v))⁻¹ =
        chi4 p v M * (
          ∑ N ∈ S1, chi4 p v N * (N : ZMod (p ^ v))⁻¹ +
          ∑ q ∈ (Finset.range M).filter (fun q => 0 < q ∧ 3 * q < M ∧ q % 2 = 1 ∧ ¬ p ∣ q),
            chi4 p v q * (q : ZMod (p ^ v))⁻¹) := by
      have hterm : ∀ N ∈ S1,
          ((-1 : ZMod (p ^ v)) ^ ((M - N) / 2)) * (c_seq N : ZMod (p ^ v)) * (N : ZMod (p ^ v))⁻¹ =
          chi4 p v M * (chi4 p v N * (N : ZMod (p ^ v))⁻¹ -
            if 3 ∣ N then 3 * chi4 p v N * (N : ZMod (p ^ v))⁻¹ else 0) := by
        intro N hN
        simp only [S1, Finset.mem_filter, Finset.mem_range] at hN
        rw [neg_one_pow_half_sub hModd hN.2.2.1 hN.1.le]
        have hcN : (c_seq N : ZMod (p ^ v)) = 1 - (if 3 ∣ N then (3 : ZMod (p ^ v)) else 0) := by
          unfold c_seq
          have hnd2 : ¬ 2 ∣ N := by omega
          rw [if_neg hnd2, sub_zero]
          split_ifs <;> push_cast <;> ring
        rw [hcN]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib]
      have h3f : ∑ N ∈ S1, (if 3 ∣ N then (3 : ZMod (p ^ v)) * chi4 p v N * (N : ZMod (p ^ v))⁻¹ else 0) =
          ∑ N ∈ S1.filter (fun N => 3 ∣ N), (3 : ZMod (p ^ v)) * chi4 p v N * (N : ZMod (p ^ v))⁻¹ :=
        (Finset.sum_filter (s := S1) (p := fun N => 3 ∣ N) (f := fun N => (3 : ZMod (p ^ v)) * chi4 p v N * (N : ZMod (p ^ v))⁻¹)).symm
      rw [h3f]
      congr 1
      have h3bij :
          -(∑ N ∈ S1.filter (fun N => 3 ∣ N), (3 : ZMod (p ^ v)) * chi4 p v N * (N : ZMod (p ^ v))⁻¹) =
          ∑ q ∈ (Finset.range M).filter (fun q => 0 < q ∧ 3 * q < M ∧ q % 2 = 1 ∧ ¬ p ∣ q),
            chi4 p v q * (q : ZMod (p ^ v))⁻¹ := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_bij (fun N _ => N / 3) ?_ ?_ ?_ ?_
        · intro N hN
          simp only [S1, Finset.mem_filter, Finset.mem_range] at hN ⊢
          rcases hN.2 with ⟨q, rfl⟩
          have hpq : ¬ p ∣ q := fun h => hN.1.2.2.2 (dvd_mul_of_dvd_right h 3)
          rw [Nat.mul_div_cancel_left q (by omega)]
          exact ⟨by omega, by omega, by omega, by omega, hpq⟩
        · intro N₁ h₁ N₂ h₂ heq
          simp only [Finset.mem_filter] at h₁ h₂
          rcases h₁.2 with ⟨q₁, rfl⟩; rcases h₂.2 with ⟨q₂, rfl⟩
          rw [Nat.mul_div_cancel_left q₁ (by omega), Nat.mul_div_cancel_left q₂ (by omega)] at heq
          rw [heq]
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_range] at hq
          have h3q : ¬ p ∣ 3 * q := fun h => (hp.dvd_mul.mp h).elim hp3 hq.2.2.2.2
          refine ⟨3 * q, ?_, Nat.mul_div_cancel_left q (by omega)⟩
          simp only [S1, Finset.mem_filter, Finset.mem_range]
          exact ⟨⟨by omega, by omega, by omega, h3q⟩, ⟨q, rfl⟩⟩
        · intro N hN
          simp only [S1, Finset.mem_filter] at hN
          rcases hN.2 with ⟨q, rfl⟩
          have hqodd : q % 2 = 1 := by omega
          have hpq : ¬ p ∣ q := fun h => hN.1.2.2.2 (dvd_mul_of_dvd_right h 3)
          rw [Nat.mul_div_cancel_left q (by omega), chi4_three_mul hqodd,
            zmod_inv_three_mul hp hp3 hpq]
          have h3u := zmod_three_mul_inv (p := p) (v := v) hp hp3
          calc
            -((3 : ZMod (p ^ v)) * -chi4 p v q * ((3 : ZMod (p ^ v))⁻¹ * (q : ZMod (p ^ v))⁻¹))
              = ((3 : ZMod (p ^ v)) * (3 : ZMod (p ^ v))⁻¹) * (chi4 p v q * (q : ZMod (p ^ v))⁻¹) := by ring
            _ = chi4 p v q * (q : ZMod (p ^ v))⁻¹ := by rw [h3u, one_mul]
      rw [sub_eq_add_neg, h3bij]
    rw [hsplit]
    have h4ndvd : ¬ p ∣ 4 := by
      intro h; rw [show (4 : ℕ) = 2 * 2 by norm_num] at h
      exact (hp.dvd_mul.mp h).elim hp2 hp2
    have hsum0 :
        ∑ N ∈ S1, chi4 p v N * (N : ZMod (p ^ v))⁻¹ +
        ∑ q ∈ (Finset.range M).filter (fun q => 0 < q ∧ 3 * q < M ∧ q % 2 = 1 ∧ ¬ p ∣ q),
          chi4 p v q * (q : ZMod (p ^ v))⁻¹ = 0 := by
      apply zmod_cancel_nat hp h4ndvd (a := 4)
      rw [Nat.cast_ofNat, mul_add, mul_zero]
      have hs1 := s1_odd_eq hp hp2 hv hM hModd
      have hs2 := s2_odd_eq hp hp2 hp3 hv hM hModd
      dsimp only [S1]
      rw [hs1, hs2]
      ring
    rw [hsum0, mul_zero]

/-! ### Section 7: Bridge from ZMod to HasPVal and Main Theorem -/

private lemma hasPVal_of_zmod_sum_zero {ι : Type*} {p v : ℕ} (hp : p.Prime)
    (s : Finset ι) (num : ι → ℤ) (den : ι → ℕ)
    (hden : ∀ i ∈ s, ¬ p ∣ den i)
    (hzero : ∑ i ∈ s, (num i : ZMod (p ^ v)) * (den i : ZMod (p ^ v))⁻¹ = 0) :
    HasPVal p v (∑ i ∈ s, (num i : ℚ) / (den i : ℚ)) := by
  classical
  set D : ℕ := ∏ i ∈ s, den i
  have hD_ndvd : ¬ p ∣ D := by
    dsimp only [D]
    clear hzero
    induction s using Finset.induction_on with
    | empty => simpa using hp.not_dvd_one
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro hd
      rcases hp.dvd_mul.mp hd with h1 | h2
      · exact hden a (Finset.mem_insert_self a s) h1
      · exact ih (fun i hi => hden i (Finset.mem_insert_of_mem hi)) h2
  have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hD_ndvd (h ▸ dvd_zero p))
  set Z : ℤ := ∑ i ∈ s, num i * ((D / den i : ℕ) : ℤ)
  have hsum_eq : ∑ i ∈ s, (num i : ℚ) / (den i : ℚ) = (Z : ℚ) / (D : ℚ) := by
    rw [eq_div_iff hD0, Finset.sum_mul]
    simp only [Z, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hdvd : den i ∣ D := Finset.dvd_prod_of_mem den hi
    have hdi0 : (den i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h => hden i hi (h ▸ dvd_zero p))
    have hDeq : (D : ℚ) = (den i : ℚ) * ((D / den i : ℕ) : ℚ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
    rw [hDeq, div_mul_eq_mul_div, ← mul_assoc, mul_comm (num i : ℚ) (den i : ℚ),
      mul_assoc, mul_div_cancel_left₀ _ hdi0]
  have hZ_zmod : (Z : ZMod (p ^ v)) = 0 := by
    simp only [Z, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    have hterm : ∀ i ∈ s,
        (num i : ZMod (p ^ v)) * ((D / den i : ℕ) : ZMod (p ^ v)) =
        (D : ZMod (p ^ v)) * ((num i : ZMod (p ^ v)) * (den i : ZMod (p ^ v))⁻¹) := by
      intro i hi
      have hdvd : den i ∣ D := Finset.dvd_prod_of_mem den hi
      have hDeq : (D : ZMod (p ^ v)) = (den i : ZMod (p ^ v)) * ((D / den i : ℕ) : ZMod (p ^ v)) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      rw [hDeq]
      have hu := zmod_inv_unit_mul (p := p) (v := v) hp (hden i hi)
      calc
        (num i : ZMod (p ^ v)) * ((D / den i : ℕ) : ZMod (p ^ v))
          = ((den i : ZMod (p ^ v)) * (den i : ZMod (p ^ v))⁻¹) *
              ((num i : ZMod (p ^ v)) * ((D / den i : ℕ) : ZMod (p ^ v))) := by rw [hu, one_mul]
        _ = (den i : ZMod (p ^ v)) * ((D / den i : ℕ) : ZMod (p ^ v)) *
              ((num i : ZMod (p ^ v)) * (den i : ZMod (p ^ v))⁻¹) := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hzero, mul_zero]
  have hpvZ : ((p ^ v : ℕ) : ℤ) ∣ Z := (ZMod.intCast_zmod_eq_zero_iff_dvd Z (p ^ v)).mp hZ_zmod
  rcases hpvZ with ⟨q, hq⟩
  rw [hsum_eq, hq]
  unfold HasPVal
  have hpv0 : (p : ℚ) ^ v ≠ 0 := pow_ne_zero v (Nat.cast_ne_zero.mpr hp.ne_zero)
  push_cast
  rw [div_div, mul_comm (D : ℚ) ((p : ℚ) ^ v), ← div_div, mul_div_cancel_left₀ _ hpv0]
  exact isPInt_div_nat hp q hD_ndvd

private lemma coeff_W_hasPVal {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    HasPVal p (padicValNat p (p * k))
      (PowerSeries.coeff k (psCartier p (psi_ps p * h_ps))) := by
  have : Fact p.Prime := ⟨hp⟩
  set M := p * k
  set v := padicValNat p M
  have hv : 1 ≤ v := by
    have hM0 : M ≠ 0 := mul_ne_zero hp.ne_zero (by omega)
    exact (padicValNat_dvd_iff_le hM0).mp (by rw [pow_one]; exact dvd_mul_right p k)
  have hM_dvd : p ^ v ∣ M := pow_padicValNat_dvd
  -- Express coeff k (psCartier p (psi_ps p * h_ps)) as the finite sum over N
  have hexpr : PowerSeries.coeff k (psCartier p (psi_ps p * h_ps)) =
      ∑ N ∈ (Finset.range M).filter (fun N => 0 < N ∧ (M - N) % 2 = 0 ∧ ¬ p ∣ N),
        (((-1 : ℤ) ^ ((M - N) / 2) * c_seq N : ℤ) : ℚ) / (N : ℚ) := by
    rw [coeff_psCartier, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (psi_ps p) * coeff j h_ps) M]
    rw [Finset.sum_range_succ]
    have hM_psi : coeff M (psi_ps p) = 0 := by
      rw [coeff_psi_ps, if_pos (Or.inr (dvd_mul_right p k))]
    rw [hM_psi, zero_mul, add_zero]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [coeff_psi_ps, coeff_h_ps]
    by_cases h1 : N = 0 ∨ p ∣ N
    · rw [if_pos h1, zero_mul, if_neg (by omega)]
    · push Not at h1
      rw [if_neg (by push Not; exact h1)]
      by_cases h2 : (M - N) % 2 = 0
      · rw [if_pos h2, if_pos ⟨by omega, h2, h1.2⟩]
        push_cast; ring
      · rw [if_neg h2, mul_zero, if_neg (by omega)]
  rw [hexpr]
  refine hasPVal_of_zmod_sum_zero hp _
    (fun N => (-1 : ℤ) ^ ((M - N) / 2) * c_seq N) (fun N => N) ?_ ?_
  · intro N hN; exact (Finset.mem_filter.mp hN).2.2.2
  · have hz := W_sum_zmod_zero hp hp5 hv hM_dvd
    convert hz using 2 with N _
    push_cast; ring

-- Legendre step: padicValNat p n! = n / p + padicValNat p (n / p)!
private lemma padicValNat_factorial_step {p : ℕ} (hp : p.Prime) :
    ∀ n : ℕ, padicValNat p n.factorial = n / p + padicValNat p (n / p).factorial := by
  have : Fact p.Prime := ⟨hp⟩
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero m) (Nat.factorial_ne_zero m), ih]
    by_cases hd : p ∣ m + 1
    · rcases hd with ⟨q, hq⟩
      have hq_pos : 0 < q := by
        by_contra h0; have : q = 0 := by omega
        subst this; omega
      have hdiv1 : (m + 1) / p = q := by rw [hq, Nat.mul_div_cancel_left q hp.pos]
      have hdiv2 : m / p = q - 1 := by
        have hp1 : 0 < p := hp.pos
        have hm_eq : m = p * (q - 1) + (p - 1) := by
          have : p * q = p * (q - 1) + p := by
            conv_lhs => rw [show q = (q - 1) + 1 by omega, mul_add, mul_one]
          omega
        rw [hm_eq, Nat.mul_add_div hp1, Nat.div_eq_of_lt (by omega : p - 1 < p), add_zero]
      have hv1 : padicValNat p (m + 1) = 1 + padicValNat p q := by
        rw [hq, padicValNat.mul hp.ne_zero hq_pos.ne', padicValNat.self hp.one_lt]
      have hfac : padicValNat p q.factorial = padicValNat p q + padicValNat p (q - 1).factorial := by
        have hq1 : q = (q - 1) + 1 := by omega
        conv_lhs => rw [hq1, Nat.factorial_succ]
        rw [padicValNat.mul (by omega) (Nat.factorial_ne_zero _), ← hq1]
      rw [hdiv1, hdiv2, hv1, hfac]
      omega
    · have hv0 : padicValNat p (m + 1) = 0 := padicValNat.eq_zero_of_not_dvd hd
      have hdiv : (m + 1) / p = m / p := by
        have hrem : (m + 1) % p ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
        have hm_lt : m % p + 1 < p := by
          have h1 := Nat.mod_lt m hp.pos
          by_contra hge
          have heq : m % p + 1 = p := by omega
          have : (m + 1) % p = 0 := by
            rw [Nat.add_mod, show (1 : ℕ) % p = 1 from Nat.mod_eq_of_lt hp.one_lt, heq, Nat.mod_self]
          exact hrem this
        have hm_eq : m = p * (m / p) + m % p := (Nat.div_add_mod m p).symm
        have hm1_eq : m + 1 = p * (m / p) + (m % p + 1) := by omega
        rw [hm1_eq, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hm_lt, add_zero]
      rw [hv0, hdiv, zero_add]

-- Direct bound: for p ≥ 5, r ≥ 1, k ≥ 2, 2 * r + padicValNat p (k!) ≤ k * r
private lemma factorial_val_le {p r k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (hk : 2 ≤ k) :
    2 * r + padicValNat p k.factorial ≤ k * r := by
  have : Fact p.Prime := ⟨hp⟩
  have hleg : ∀ n : ℕ, (p - 1) * padicValNat p n.factorial ≤ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < p
      · have h0 : padicValNat p n.factorial = 0 := by
          rw [padicValNat_factorial_step hp n, Nat.div_eq_of_lt hn]; simp
        rw [h0, mul_zero]; exact Nat.zero_le n
      · have hdiv : n / p < n := Nat.div_lt_self (by omega) hp.one_lt
        have ih' := ih (n / p) hdiv
        rw [padicValNat_factorial_step hp n, mul_add]
        have hmul : p * (n / p) ≤ n := Nat.mul_div_le n p
        have : (p - 1) * (n / p) + n / p = p * (n / p) := by
          have hp1 : (p - 1) + 1 = p := by omega
          calc (p - 1) * (n / p) + n / p = ((p - 1) + 1) * (n / p) := by ring
            _ = p * (n / p) := by rw [hp1]
        omega
  have h1 := hleg k
  -- From 4 * padicValNat p k! ≤ (p - 1) * padicValNat p k! ≤ k:
  -- Need 2 * r + v ≤ k * r, i.e., v ≤ (k - 2) * r.
  -- If k = 2: k < p so v = 0, holds!
  -- If k = 3: k < p so v = 0, holds!
  -- If k = 4: k < p so v = 0, holds!
  -- If k ≥ 5: 4 * v ≤ k ≤ 4 * (k - 2) ≤ 4 * (k - 2) * r, done!
  by_cases hk5 : k < 5
  · have h0 : padicValNat p k.factorial = 0 := by
      rw [padicValNat_factorial_step hp k, Nat.div_eq_of_lt (by omega : k < p)]; simp
    rw [h0, add_zero]
    exact Nat.mul_le_mul_right r hk
  · have h4v : 4 * padicValNat p k.factorial ≤ k :=
      le_trans (Nat.mul_le_mul_right _ (by omega : 4 ≤ p - 1)) h1
    have h4k : k ≤ 4 * (k - 2) := by omega
    have hv_le : padicValNat p k.factorial ≤ k - 2 := by omega
    have hkr : 2 * r + (k - 2) * r = k * r := by
      rw [← add_mul, Nat.add_sub_of_le hk]
    have hle1 : k - 2 ≤ (k - 2) * r := Nat.le_mul_of_pos_right _ hr
    omega

theorem main_theorem :
    ∀ p n : ℕ, p.Prime → 3 < p → 0 < n →
      ¬ p ∣ (((a_seq (p * n) : ℚ) - (a_seq n : ℚ)) / ((p : ℚ) * (n : ℚ)) ^ 2).den := by
  intro p n hp hp3 hn
  have hp5 : 5 ≤ p := by
    have := hp.eq_two_or_odd
    have hp4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
    omega
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  set r := padicValNat p (p * n)
  have hpn0 : p * n ≠ 0 := mul_ne_zero hp.ne_zero hn.ne'
  have hr : 1 ≤ r := (padicValNat_dvd_iff_le hpn0).mp (by simpa using dvd_mul_right p n)
  apply isPInt_div_of_hasPVal hp hn
  -- Rewrite a(p*n) - a(n) using f_ps^(p*n) * h_ps = psExpand p (f_ps^n) * (psExp0 ((pn)•psi) * h_ps)
  rw [a_seq_eq_coeff (p * n), a_seq_eq_coeff n, f_ps_pow_pn_eq hp hp5 n]
  have hcoeff_pn : PowerSeries.coeff (p * n) (psExpand p (f_ps ^ n) * psExp0 (((p * n : ℕ) : ℚ) • psi_ps p) * h_ps) =
      PowerSeries.coeff n (f_ps ^ n * psCartier p (psExp0 (((p * n : ℕ) : ℚ) • psi_ps p) * h_ps)) := by
    rw [mul_assoc, ← coeff_psCartier, psCartier_expand_mul p hp.pos]
  rw [hcoeff_pn]
  -- Expand coeff n (f^n * C_p(exp0((pn)•psi) * h)) as ∑_{k=0}^{p*n} ((pn)^k / k!) * coeff n (f^n * C_p(psi^k * h))
  have hpsi0 : PowerSeries.coeff 0 (psi_ps p) = 0 := coeff_zero_psi_ps p
  have hpn_psi0 : PowerSeries.coeff 0 (((p * n : ℕ) : ℚ) • psi_ps p) = 0 := by simp [hpsi0]
  have hexpand_sum :
      PowerSeries.coeff n (f_ps ^ n * psCartier p (psExp0 (((p * n : ℕ) : ℚ) • psi_ps p) * h_ps)) =
      ∑ k ∈ Finset.range (p * n + 1),
        (((p * n : ℕ) : ℚ) ^ k / (k.factorial : ℚ)) *
          PowerSeries.coeff n (f_ps ^ n * psCartier p (psi_ps p ^ k * h_ps)) := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (f_ps ^ n) * coeff j (psCartier p (psExp0 (((p * n : ℕ) : ℚ) • psi_ps p) * h_ps))) n]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        coeff i (f_ps ^ n) * coeff (n - i) (psCartier p (psExp0 (((p * n : ℕ) : ℚ) • psi_ps p) * h_ps)) =
        ∑ k ∈ Finset.range (p * n + 1),
          (((p * n : ℕ) : ℚ) ^ k / (k.factorial : ℚ)) *
            (coeff i (f_ps ^ n) * coeff (n - i) (psCartier p (psi_ps p ^ k * h_ps))) := by
      intro i hi
      have hni : n - i ≤ n := Nat.sub_le n i
      rw [coeff_psCartier, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a b => coeff a (psExp0 (((p * n : ℕ) : ℚ) • psi_ps p)) * coeff b h_ps) (p * (n - i)),
        Finset.mul_sum]
      have hinner : ∀ a ∈ Finset.range (p * (n - i) + 1),
          coeff i (f_ps ^ n) * (coeff a (psExp0 (((p * n : ℕ) : ℚ) • psi_ps p)) * coeff (p * (n - i) - a) h_ps) =
          ∑ k ∈ Finset.range (p * n + 1),
            (((p * n : ℕ) : ℚ) ^ k / (k.factorial : ℚ)) *
              (coeff i (f_ps ^ n) * (coeff a (psi_ps p ^ k) * coeff (p * (n - i) - a) h_ps)) := by
        intro a ha
        have ha1 : a ≤ p * n := by
          have ha' : a ≤ p * (n - i) := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          exact le_trans ha' (Nat.mul_le_mul_left p hni)
        rw [coeff_psExp0_eq_sum_ge hpn_psi0 ha1, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_pow, map_smul, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_psCartier, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun a b => coeff a (psi_ps p ^ k) * coeff b h_ps) (p * (n - i)),
        Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (f_ps ^ n) * coeff j (psCartier p (psi_ps p ^ k * h_ps))) n,
      Finset.mul_sum]
  rw [hexpand_sum]
  -- Peel off k = 0 term (= coeff n (f^n * h)) and k = 1 term
  have hpn_ge2 : 2 ≤ p * n + 1 := by nlinarith
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, psCartier_h_ps hp hp2]
  rw [add_sub_cancel_right]
  -- Remaining sum is over k' ∈ range (p * n), corresponding to k = k' + 1
  have hrange : Finset.range (p * n) = Finset.range ((p * n - 1) + 1) := by congr 1; omega
  rw [hrange, Finset.sum_range_succ']
  simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  -- Sum of (k ≥ 2 terms) + (k = 1 term)
  apply hasPVal_add hp
  · -- k = k' + 2 ≥ 2 terms
    apply hasPVal_sum hp
    intro k' _
    set k := k' + 2
    have hk2 : 2 ≤ k := by omega
    have hpn_val : HasPVal p (k * r) (((p * n : ℕ) : ℚ) ^ k) := by
      have hd : p ^ (k * r) ∣ (p * n) ^ k := by
        rw [mul_comm, pow_mul]
        exact pow_dvd_pow_of_dvd pow_padicValNat_dvd k
      simpa [Nat.cast_pow] using hasPVal_natCast_of_dvd hp hd
    have hfac_le : 2 * r + padicValNat p k.factorial ≤ k * r := factorial_val_le hp hp5 hr hk2
    have hcoeff_val : HasPVal p (2 * r) (((p * n : ℕ) : ℚ) ^ k / (k.factorial : ℚ)) :=
      hasPVal_div_nat hp (Nat.factorial_ne_zero k) (hasPVal_mono hp hfac_le hpn_val)
    have hser_int : IsPInt p (PowerSeries.coeff n (f_ps ^ n * psCartier p (psi_ps p ^ k * h_ps))) :=
      (seriesPInt_mul hp (seriesPInt_pow hp (seriesPInt_f_ps hp) n)
        (seriesPInt_psCartier (seriesPInt_mul hp (seriesPInt_pow hp (seriesPInt_psi_ps hp) k)
          (seriesPInt_h_ps hp)))) n
    simpa [add_zero] using hasPVal_mul hp hcoeff_val ((hasPVal_zero_iff _).mpr hser_int)
  · -- k = 1 term: (p * n) * coeff n (f^n * W)
    set W := psCartier p (psi_ps p * h_ps)
    set U : PowerSeries ℚ := PowerSeries.mk fun m =>
      if m = 0 then 0 else PowerSeries.coeff m W / (((p * m : ℕ) : ℚ))
    have hU_int : SeriesPInt p U := by
      intro m
      simp only [U, coeff_mk]
      by_cases hm : m = 0
      · rw [if_pos hm]; exact isPInt_zero p hp
      · rw [if_neg hm]
        have hm1 : 1 ≤ m := by omega
        have hpm0 : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm
        have hW := coeff_W_hasPVal hp hp5 hm1
        have hdiv := hasPVal_div_nat (k := 0) hp hpm0 (by rw [zero_add]; exact hW)
        exact (hasPVal_zero_iff _).mp hdiv
    have hW_eq : W = (p : ℚ) • (PowerSeries.X * psDeriv U) := by
      ext m
      rw [map_smul, smul_eq_mul, coeff_X_mul_psDeriv]
      cases m with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, mul_zero, W, coeff_psCartier, mul_zero]
        rw [PowerSeries.coeff_mul]
        simp [coeff_zero_psi_ps]
      | succ k =>
        simp only [U, coeff_mk, Nat.succ_ne_zero, ↓reduceIte, Nat.cast_mul]
        have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
        have hk0 : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
        field_simp [hp0, hk0]
    -- Integration by parts: coeff n (f^n * (X * psDeriv U)) = n * (coeff n (f^n * U) - coeff n (X * psDeriv f * f^(n-1) * U))
    have hibp : PowerSeries.coeff n (f_ps ^ n * (PowerSeries.X * psDeriv U)) =
        (n : ℚ) * (PowerSeries.coeff n (f_ps ^ n * U) -
          PowerSeries.coeff n (PowerSeries.X * psDeriv f_ps * f_ps ^ (n - 1) * U)) := by
      have h1 := coeff_X_mul_psDeriv (f_ps ^ n * U) n
      rw [psDeriv_mul, psDeriv_pow, mul_add] at h1
      have h2 : PowerSeries.X * ((n : ℚ) • (f_ps ^ (n - 1) * psDeriv f_ps) * U) =
          (n : ℚ) • (PowerSeries.X * psDeriv f_ps * f_ps ^ (n - 1) * U) := by
        rw [smul_mul_assoc, mul_smul_comm]
        congr 1; ring
      have h3 : PowerSeries.X * (f_ps ^ n * psDeriv U) = f_ps ^ n * (PowerSeries.X * psDeriv U) := by ring
      rw [h2, h3, map_add, map_smul, smul_eq_mul] at h1
      linarith
    have hk1_eq : (((p * n : ℕ) : ℚ)) * PowerSeries.coeff n (f_ps ^ n * W) =
        (((p * n : ℕ) : ℚ) ^ 2) * (PowerSeries.coeff n (f_ps ^ n * U) -
          PowerSeries.coeff n (PowerSeries.X * psDeriv f_ps * f_ps ^ (n - 1) * U)) := by
      rw [hW_eq, mul_smul_comm, map_smul, smul_eq_mul, hibp]
      push_cast; ring
    rw [hk1_eq]
    have hpn2_val : HasPVal p (2 * r) (((p * n : ℕ) : ℚ) ^ 2) := by
      have hd : p ^ (2 * r) ∣ (p * n) ^ 2 := by
        rw [mul_comm, pow_mul]
        exact pow_dvd_pow_of_dvd pow_padicValNat_dvd 2
      simpa [Nat.cast_pow] using hasPVal_natCast_of_dvd hp hd
    have hdiff_int : IsPInt p (PowerSeries.coeff n (f_ps ^ n * U) -
        PowerSeries.coeff n (PowerSeries.X * psDeriv f_ps * f_ps ^ (n - 1) * U)) :=
      isPInt_sub hp
        ((seriesPInt_mul hp (seriesPInt_pow hp (seriesPInt_f_ps hp) n) hU_int) n)
        ((seriesPInt_mul hp
          (seriesPInt_mul hp (seriesPInt_mul hp (seriesPInt_X hp) (seriesPInt_psDeriv hp (seriesPInt_f_ps hp)))
            (seriesPInt_pow hp (seriesPInt_f_ps hp) (n - 1)))
          hU_int) n)
    simpa [add_zero] using hasPVal_mul hp hpn2_val ((hasPVal_zero_iff _).mpr hdiff_int)

end OMA_A278415

theorem OMA.solution : type_of% @OMA.S_oeis_a278415.main :=
  OMA_A278415.main_theorem
