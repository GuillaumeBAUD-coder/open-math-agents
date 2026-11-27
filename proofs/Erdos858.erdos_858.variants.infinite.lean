import FormalConjectures.ErdosProblems.«858»

/-! Proof of Erdos858.erdos_858.variants.infinite via Alexander-ESS primorial sieve and Mertens bound. -/

open Filter Real

namespace OMA.Erdos858Inf

private def primesLE (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

private lemma mem_primesLE {p n : ℕ} : p ∈ primesLE n ↔ p.Prime ∧ p ≤ n := by
  simp [primesLE, and_comm]

private lemma primorial_pos (n : ℕ) : 0 < primorial n := by
  unfold primorial
  exact Finset.prod_pos fun p hp => (mem_primesLE.mp hp).1.pos

private lemma dvd_primorial_of_prime {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    p ∣ primorial n := by
  unfold primorial
  exact Finset.dvd_prod_of_mem _ (mem_primesLE.mpr ⟨hp, hpn⟩)

private lemma primorial_dvd_primorial {a b : ℕ} (hab : a ≤ b) :
    primorial a ∣ primorial b := by
  unfold primorial
  refine Finset.prod_dvd_prod_of_subset _ _ id ?_
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

private lemma coprime_of_dvd_primorial_coprime {a P : ℕ}
    (hcop : ∀ p : ℕ, p.Prime → p ∣ a → p ∣ P) {t : ℕ} (ht : Nat.Coprime t P) :
    Nat.Coprime a t := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  have hmin : (Nat.gcd a t).minFac.Prime := Nat.minFac_prime hne
  have hdvd_gcd : (Nat.gcd a t).minFac ∣ Nat.gcd a t := Nat.minFac_dvd _
  have hdvd_a : (Nat.gcd a t).minFac ∣ a := hdvd_gcd.trans (Nat.gcd_dvd_left a t)
  have hdvd_t : (Nat.gcd a t).minFac ∣ t := hdvd_gcd.trans (Nat.gcd_dvd_right a t)
  have hdvd_P : (Nat.gcd a t).minFac ∣ P := hcop _ hmin hdvd_a
  have h1 : (Nat.gcd a t).minFac ∣ 1 := by
    rw [← ht.gcd_eq_one]
    exact Nat.dvd_gcd hdvd_t hdvd_P
  exact hmin.not_dvd_one h1

private lemma totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have ha : a.Prime := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq' : q.Prime := hs' q hq
      have hne : a ≠ q := fun h => has (h ▸ hq)
      exact (ha.coprime_iff_not_dvd).mpr fun hd =>
        hne ((Nat.prime_dvd_prime_iff_eq ha hq').mp hd)
    rw [Finset.prod_insert has, Finset.prod_insert has, Nat.totient_mul hcop,
      Nat.totient_prime ha, ih hs']

private lemma totient_primorial_div (n : ℕ) :
    (Nat.totient (primorial n) : ℝ) / primorial n =
      ∏ p ∈ primesLE n, (1 - (1 : ℝ) / p) := by
  have hprim : primorial n = ∏ p ∈ primesLE n, p := by
    unfold primorial
    rfl
  have hs : ∀ p ∈ primesLE n, p.Prime := fun p hp => (mem_primesLE.mp hp).1
  rw [hprim, totient_prod_primes (primesLE n) hs]
  push_cast
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp1 : 1 ≤ p := (hs p hp).one_le
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hs p hp).ne_zero
  rw [Nat.cast_sub hp1]
  field_simp [hp0]
  norm_num

private lemma coprime_mod_iff (t P : ℕ) : Nat.Coprime (t % P) P ↔ Nat.Coprime t P := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one]
  have hg : Nat.gcd (t % P) P = Nat.gcd t P := by
    rw [Nat.gcd_comm t P, ← Nat.gcd_rec P t]
  rw [hg]

private lemma card_coprime_Icc_one (P : ℕ) (hP : 0 < P) :
    ((Finset.Icc 1 P).filter (fun t => Nat.Coprime t P)).card = Nat.totient P := by
  rw [Nat.totient_eq_card_coprime]
  refine Finset.card_bij (fun t _ => t % P) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter, Finset.mem_Icc] at ht
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt t hP, ((coprime_mod_iff t P).mpr ht.2).symm⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
    by_cases haP : a = P <;> by_cases hbP : b = P
    · rw [haP, hbP]
    · have hb_lt : b < P := lt_of_le_of_ne hb.1.2 hbP
      rw [haP, Nat.mod_self, Nat.mod_eq_of_lt hb_lt] at hab
      omega
    · have ha_lt : a < P := lt_of_le_of_ne ha.1.2 haP
      rw [hbP, Nat.mod_self, Nat.mod_eq_of_lt ha_lt] at hab
      omega
    · have ha_lt : a < P := lt_of_le_of_ne ha.1.2 haP
      have hb_lt : b < P := lt_of_le_of_ne hb.1.2 hbP
      rwa [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hab
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    by_cases hr0 : r = 0
    · refine ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hP, le_rfl⟩, ?_⟩, ?_⟩
      · rw [← coprime_mod_iff, Nat.mod_self, ← hr0]
        exact hr.2.symm
      · rw [Nat.mod_self, hr0]
    · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
      refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr1, hr.1.le⟩, hr.2.symm⟩, ?_⟩
      exact Nat.mod_eq_of_lt hr.1

private lemma coprime_add_mul_iff (P k r : ℕ) :
    Nat.Coprime (k * P + r) P ↔ Nat.Coprime r P := by
  rw [mul_comm k P, ← coprime_mod_iff, Nat.mul_add_mod_self_left, coprime_mod_iff]

private lemma card_coprime_Icc_mul (P k : ℕ) (hP : 0 < P) :
    ((Finset.Icc 1 (k * P)).filter (fun t => Nat.Coprime t P)).card = k * Nat.totient P := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : Finset.Icc 1 ((k + 1) * P) =
        Finset.Icc 1 (k * P) ∪ Finset.Icc (k * P + 1) ((k + 1) * P) := by
      ext t
      simp only [Finset.mem_union, Finset.mem_Icc]
      have hmul : (k + 1) * P = k * P + P := Nat.succ_mul k P
      omega
    have hdisj : Disjoint ((Finset.Icc 1 (k * P)).filter (fun t => Nat.Coprime t P))
        ((Finset.Icc (k * P + 1) ((k + 1) * P)).filter (fun t => Nat.Coprime t P)) := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [Finset.mem_filter, Finset.mem_Icc] at ht1 ht2
      omega
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj, ih]
    have hshift : ((Finset.Icc (k * P + 1) ((k + 1) * P)).filter (fun t => Nat.Coprime t P)).card =
        ((Finset.Icc 1 P).filter (fun r => Nat.Coprime r P)).card := by
      refine Finset.card_bij (fun t _ => t - k * P) ?_ ?_ ?_
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢
        have hmul : (k + 1) * P = k * P + P := Nat.succ_mul k P
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        have hteq : t = k * P + (t - k * P) := by omega
        rw [hteq, coprime_add_mul_iff] at ht
        exact ht.2
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
        omega
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_Icc] at hr ⊢
        have hmul : (k + 1) * P = k * P + P := Nat.succ_mul k P
        refine ⟨k * P + r, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
        exact (coprime_add_mul_iff P k r).mpr hr.2
    rw [hshift, card_coprime_Icc_one P hP, Nat.succ_mul]

private lemma sum_inv_mul_prod_le_one (A : Set ℕ)
    (hadm : ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, a * t = b → t.minFac ≤ a)
    (F : Finset ℕ) (hF : ∀ a ∈ F, a ∈ A ∧ 2 ≤ a) :
    ∑ a ∈ F, (1 : ℝ) / a * ∏ p ∈ primesLE a, (1 - (1 : ℝ) / p) ≤ 1 := by
  let M : ℕ := F.sup id
  let X : ℕ := (∏ a ∈ F, a) * primorial M
  have hprod_pos : 0 < ∏ a ∈ F, a := Finset.prod_pos fun a ha => by have := (hF a ha).2; omega
  have hX_pos : 0 < X := Nat.mul_pos hprod_pos (primorial_pos M)
  let S : ℕ → Finset ℕ := fun a =>
    ((Finset.Icc 1 (X / a)).filter (fun t => Nat.Coprime t (primorial a))).image
      (fun t => a * t)
  have hS_sub : ∀ a ∈ F, S a ⊆ Finset.Icc 1 X := by
    intro a ha n hn
    rcases Finset.mem_image.mp hn with ⟨t, ht, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at ht
    have ha2 : 2 ≤ a := (hF a ha).2
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · exact Nat.mul_pos (by omega) ht.1.1
    · exact (Nat.mul_le_mul_left a ht.1.2).trans (Nat.mul_div_le X a)
  have hS_disj : (F : Set ℕ).PairwiseDisjoint S := by
    intro a₁ ha₁ a₂ ha₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn₁ hn₂
    rcases Finset.mem_image.mp hn₁ with ⟨t₁, ht₁, hEq₁⟩
    rcases Finset.mem_image.mp hn₂ with ⟨t₂, ht₂, hEq₂⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at ht₁ ht₂
    have hEq : a₁ * t₁ = a₂ * t₂ := hEq₁.trans hEq₂.symm
    suffices key : ∀ x ∈ F, ∀ y ∈ F, x < y →
        ∀ u v : ℕ, Nat.Coprime u (primorial x) → Nat.Coprime v (primorial y) →
        x * u = y * v → False by
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact key a₁ ha₁ a₂ ha₂ hlt t₁ t₂ ht₁.2 ht₂.2 hEq
      · exact key a₂ ha₂ a₁ ha₁ hlt t₂ t₁ ht₂.2 ht₁.2 hEq.symm
    intro x hx y hy hxy u v hu hv huv
    have hcop_xv : Nat.Coprime x v := by
      refine coprime_of_dvd_primorial_coprime (fun p hp hpx => ?_) hv
      exact dvd_primorial_of_prime hp ((Nat.le_of_dvd (by have := (hF x hx).2; omega) hpx).trans hxy.le)
    have hxdvd : x ∣ y := hcop_xv.dvd_of_dvd_mul_right ⟨u, huv.symm⟩
    rcases hxdvd with ⟨d, rfl⟩
    have hx_pos : 0 < x := by have := (hF x hx).2; omega
    have hd_gt1 : 1 < d := by
      by_contra hd1
      have : x * d ≤ x * 1 := Nat.mul_le_mul_left x (by omega)
      omega
    have huv' : u = d * v := by
      have : x * u = x * (d * v) := by rw [← mul_assoc]; exact huv
      exact Nat.eq_of_mul_eq_mul_left hx_pos this
    have hp_prime : d.minFac.Prime := Nat.minFac_prime (by omega)
    have hp_u : d.minFac ∣ u := (Nat.minFac_dvd d).trans ⟨v, huv'⟩
    have hp_le : d.minFac ≤ x := hadm x (hF x hx).1 (x * d) (hF (x * d) hy).1 d rfl
    have hp_prim : d.minFac ∣ primorial x := dvd_primorial_of_prime hp_prime hp_le
    have hp_one : d.minFac ∣ 1 := by
      rw [← hu.gcd_eq_one]
      exact Nat.dvd_gcd hp_u hp_prim
    exact hp_prime.not_dvd_one hp_one
  have hcard_S : ∀ a ∈ F, (S a).card * (a * primorial a) =
      X * Nat.totient (primorial a) := by
    intro a ha
    have ha_pos : 0 < a := by have := (hF a ha).2; omega
    have hprim_a_pos : 0 < primorial a := primorial_pos a
    have haM : a ≤ M := Finset.le_sup (f := id) ha
    have ha_dvd_prod : a ∣ ∏ b ∈ F, b := Finset.dvd_prod_of_mem _ ha
    have hprim_dvd : primorial a ∣ primorial M := primorial_dvd_primorial haM
    have hap_dvd_X : a * primorial a ∣ X := Nat.mul_dvd_mul ha_dvd_prod hprim_dvd
    rcases hap_dvd_X with ⟨k, hk⟩
    have hXa : X / a = k * primorial a := by
      have hX_eq : X = a * (k * primorial a) := by rw [hk]; ring
      rw [hX_eq, Nat.mul_div_right _ ha_pos]
    have hinj : Function.Injective (fun t => a * t) := fun t₁ t₂ h =>
      Nat.eq_of_mul_eq_mul_left ha_pos h
    have hcard : (S a).card = k * Nat.totient (primorial a) := by
      dsimp [S]
      rw [Finset.card_image_of_injective _ hinj, hXa]
      exact card_coprime_Icc_mul (primorial a) k hprim_a_pos
    rw [hcard, hk]
    ring
  have hsum_card : ∑ a ∈ F, (S a).card ≤ X := by
    rw [← Finset.card_biUnion hS_disj]
    have hbi_sub : F.biUnion S ⊆ Finset.Icc 1 X :=
      Finset.biUnion_subset.mpr hS_sub
    exact (Finset.card_le_card hbi_sub).trans (by simp)
  have hsum_real : ∑ a ∈ F, ((S a).card : ℝ) / X ≤ 1 := by
    rw [← Finset.sum_div]
    have hX_real_pos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
    exact (div_le_one hX_real_pos).mpr (by exact_mod_cast hsum_card)
  refine le_trans ?_ hsum_real
  refine le_of_eq (Finset.sum_congr rfl fun a ha => ?_)
  have ha_pos : (0 : ℝ) < a := Nat.cast_pos.mpr (by have := (hF a ha).2; omega)
  have hprim_pos : (0 : ℝ) < primorial a := Nat.cast_pos.mpr (primorial_pos a)
  have hX_real_pos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
  rw [← totient_primorial_div a]
  have heq : ((S a).card : ℝ) * (a * primorial a) =
      (X : ℝ) * Nat.totient (primorial a) := by
    exact_mod_cast hcard_S a ha
  field_simp [ha_pos.ne', hprim_pos.ne', hX_real_pos.ne']
  linarith [heq]

private lemma prod_dvd_of_pairwise_coprime {s : Finset ℕ} {f : ℕ → ℕ} {N : ℕ}
    (hcop : (s : Set ℕ).Pairwise fun p q => Nat.Coprime (f p) (f q))
    (hdvd : ∀ p ∈ s, f p ∣ N) :
    (∏ p ∈ s, f p) ∣ N := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.prod_insert has]
    have hcop_a : Nat.Coprime (f a) (∏ p ∈ s, f p) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hq) (fun h => has (h ▸ hq))
    exact hcop_a.mul_dvd_of_dvd_of_dvd
      (hdvd a (Finset.mem_insert_self a s))
      (ih (hcop.mono (Finset.subset_insert a s)) fun p hp => hdvd p (Finset.mem_insert_of_mem hp))

private lemma prod_prime_pow_div_dvd_factorial (n : ℕ) :
    (∏ p ∈ primesLE n, p ^ (n / p)) ∣ Nat.factorial n := by
  refine prod_dvd_of_pairwise_coprime ?_ ?_
  · intro p hp q hq hpq
    have hp' : p.Prime := (mem_primesLE.mp hp).1
    have hq' : q.Prime := (mem_primesLE.mp hq).1
    exact ((hp'.coprime_iff_not_dvd).mpr fun hd =>
      hpq ((Nat.prime_dvd_prime_iff_eq hp' hq').mp hd)).pow _ _
  · intro p hp
    have hp' : p.Prime := (mem_primesLE.mp hp).1
    let : Fact p.Prime := ⟨hp'⟩
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hlog_lt : Nat.log p n < n + 1 :=
        lt_of_le_of_lt (Nat.log_le_self p n) (Nat.lt_succ_self n)
      have hpadic : n / p ≤ padicValNat p (Nat.factorial n) := by
        rw [padicValNat_factorial hlog_lt]
        have h1mem : 1 ∈ Finset.Ico 1 (n + 1) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
        simpa using Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1mem
      exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mpr hpadic

private lemma factorial_le_pow_self (n : ℕ) : Nat.factorial n ≤ n ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, pow_succ']
    exact Nat.mul_le_mul_left (n + 1) (ih.trans (Nat.pow_le_pow_left (Nat.le_succ n) n))

private noncomputable def Lsum (n : ℕ) : ℝ :=
  ∑ p ∈ primesLE n, Real.log p / p

private lemma Lsum_nonneg (n : ℕ) : 0 ≤ Lsum n := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_primesLE.mp hp).1.one_le
  exact div_nonneg (Real.log_nonneg hp1) (by positivity)

private lemma Lsum_one : Lsum 1 = 0 := by
  have h1 : primesLE 1 = ∅ := by
    ext p
    rw [mem_primesLE]
    constructor
    · rintro ⟨hp, hp1⟩
      exact absurd hp1 (not_le_of_gt hp.one_lt)
    · simp
  simp [Lsum, h1]

private lemma Lsum_sub (k : ℕ) (hk : 1 ≤ k) :
    Lsum k - Lsum (k - 1) = if k.Prime then Real.log k / k else 0 := by
  have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hsplit : primesLE k =
      if k.Prime then insert k (primesLE (k - 1)) else primesLE (k - 1) := by
    ext p
    rw [mem_primesLE]
    split_ifs with hkp
    · rw [Finset.mem_insert, mem_primesLE]
      constructor
      · rintro ⟨hp, hpk⟩
        rcases eq_or_lt_of_le hpk with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨hp, by omega⟩
      · rintro (rfl | ⟨hp, hpk⟩)
        · exact ⟨hkp, le_rfl⟩
        · exact ⟨hp, by omega⟩
    · rw [mem_primesLE]
      constructor
      · rintro ⟨hp, hpk⟩
        refine ⟨hp, ?_⟩
        have hne : p ≠ k := fun h => hkp (h ▸ hp)
        omega
      · rintro ⟨hp, hpk⟩
        exact ⟨hp, by omega⟩
  have hnotmem : k ∉ primesLE (k - 1) := by
    rw [mem_primesLE]
    intro h
    omega
  rw [Lsum, Lsum, hsplit]
  split_ifs with hkp
  · rw [Finset.sum_insert hnotmem, add_sub_cancel_right]
  · rw [sub_self]

private lemma sum_log_div_prime_le (n : ℕ) (hn : 1 ≤ n) :
    Lsum n ≤ Real.log n + Real.log 4 := by
  have hdvd : ∏ p ∈ primesLE n, p ^ (n / p) ∣ Nat.factorial n := prod_prime_pow_div_dvd_factorial n
  have hle_nat : ∏ p ∈ primesLE n, p ^ (n / p) ≤ n ^ n :=
    (Nat.le_of_dvd (Nat.factorial_pos n) hdvd).trans (factorial_le_pow_self n)
  have hpos_prod : (0 : ℝ) < ∏ p ∈ primesLE n, ((p : ℝ) ^ (n / p)) := by
    refine Finset.prod_pos fun p hp => ?_
    exact pow_pos (Nat.cast_pos.mpr (mem_primesLE.mp hp).1.pos) _
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ n := pow_pos (Nat.cast_pos.mpr hn) n
  have hle_real : ∏ p ∈ primesLE n, ((p : ℝ) ^ (n / p)) ≤ (n : ℝ) ^ n := by
    exact_mod_cast hle_nat
  have hlog_le : Real.log (∏ p ∈ primesLE n, ((p : ℝ) ^ (n / p))) ≤ Real.log ((n : ℝ) ^ n) :=
    Real.log_le_log hpos_prod hle_real
  rw [Real.log_prod fun p hp => pow_ne_zero _ (Nat.cast_ne_zero.mpr (mem_primesLE.mp hp).1.ne_zero),
    Real.log_pow] at hlog_le
  have hlog_sum : ∑ p ∈ primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ n * Real.log n := by
    simpa [Real.log_pow] using hlog_le
  have hterm : ∀ p ∈ primesLE n,
      (n : ℝ) * (Real.log p / p) ≤ ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hp_pos_nat : 0 < p := (mem_primesLE.mp hp).1.pos
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_pos_nat
    have hlogp_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (mem_primesLE.mp hp).1.one_le)
    have hdiv_lt : n < p * (n / p) + p := by
      have h1 : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
      have h2 : n % p < p := Nat.mod_lt n hp_pos_nat
      omega
    have hdiv_real : (n : ℝ) ≤ (p : ℝ) * (n / p : ℕ) + p := by
      exact_mod_cast hdiv_lt.le
    have hquot : (n : ℝ) / p ≤ (n / p : ℕ) + 1 := by
      rw [div_le_iff₀ hp_pos]
      linarith
    have hmul : (n : ℝ) / p * Real.log p ≤ ((n / p : ℕ) + 1) * Real.log p :=
      mul_le_mul_of_nonneg_right hquot hlogp_nn
    have heq1 : (n : ℝ) * (Real.log p / p) = (n : ℝ) / p * Real.log p := by ring
    linarith
  have hprim_bound : ∑ p ∈ primesLE n, Real.log p ≤ n * Real.log 4 := by
    have hprim_pos : (0 : ℝ) < primorial n := Nat.cast_pos.mpr (primorial_pos n)
    have h4_le : (primorial n : ℝ) ≤ (4 : ℝ) ^ n := by
      exact_mod_cast primorial_le_four_pow n
    have hlog4 := Real.log_le_log hprim_pos h4_le
    rw [Real.log_pow] at hlog4
    have hprim_eq : (primorial n : ℝ) = ∏ p ∈ primesLE n, (p : ℝ) := by
      unfold primorial
      push_cast
      rfl
    rw [hprim_eq, Real.log_prod fun p hp => Nat.cast_ne_zero.mpr (mem_primesLE.mp hp).1.ne_zero] at hlog4
    exact hlog4
  have hsum_ineq : (n : ℝ) * Lsum n ≤ (n : ℝ) * (Real.log n + Real.log 4) := by
    calc (n : ℝ) * Lsum n
        = ∑ p ∈ primesLE n, (n : ℝ) * (Real.log p / p) := by rw [Lsum, Finset.mul_sum]
      _ ≤ ∑ p ∈ primesLE n, (((n / p : ℕ) : ℝ) * Real.log p + Real.log p) :=
          Finset.sum_le_sum hterm
      _ = ∑ p ∈ primesLE n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ primesLE n, Real.log p :=
          Finset.sum_add_distrib
      _ ≤ (n : ℝ) * Real.log n + (n : ℝ) * Real.log 4 := add_le_add hlog_sum hprim_bound
      _ = (n : ℝ) * (Real.log n + Real.log 4) := by ring
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact le_of_mul_le_mul_left hsum_ineq hn_pos

private lemma abel_identity (a : ℕ) (ha : 2 ≤ a) :
    ∑ k ∈ Finset.Icc 2 a, (Lsum k - Lsum (k - 1)) / Real.log k =
      Lsum a / Real.log a +
        ∑ k ∈ Finset.Ico 2 a, Lsum k * (1 / Real.log k - 1 / Real.log (k + 1)) := by
  induction a, ha using Nat.le_induction with
  | base =>
    simp [Lsum_one]
  | succ a ha ih =>
    have hIcc : Finset.Icc 2 (a + 1) = insert (a + 1) (Finset.Icc 2 a) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot_Icc : a + 1 ∉ Finset.Icc 2 a := by simp
    have hIco : Finset.Ico 2 (a + 1) = insert a (Finset.Ico 2 a) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnot_Ico : a ∉ Finset.Ico 2 a := by simp
    rw [hIcc, Finset.sum_insert hnot_Icc, ih, hIco, Finset.sum_insert hnot_Ico]
    have hsub : a + 1 - 1 = a := Nat.add_sub_cancel a 1
    rw [hsub]
    push_cast
    ring

private lemma telescope_sub {f : ℕ → ℝ} (a : ℕ) (ha : 2 ≤ a) :
    ∑ k ∈ Finset.Ico 2 a, (f k - f (k + 1)) = f 2 - f a := by
  induction a, ha using Nat.le_induction with
  | base => simp
  | succ a ha ih =>
    have hIco : Finset.Ico 2 (a + 1) = insert a (Finset.Ico 2 a) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hIco, Finset.sum_insert (by simp), ih]
    ring

private lemma sum_inv_prime_le (a : ℕ) (ha : 2 ≤ a) :
    ∑ p ∈ primesLE a, (1 : ℝ) / p ≤
      Real.log (Real.log a) + (1 + 2 * Real.log 4 / Real.log 2 - Real.log (Real.log 2)) := by
  have hfilter_eq : primesLE a = (Finset.Icc 2 a).filter Nat.Prime := by
    ext p
    rw [mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp, hpa⟩
      exact ⟨⟨hp.two_le, hpa⟩, hp⟩
    · rintro ⟨⟨_, hpa⟩, hp⟩
      exact ⟨hp, hpa⟩
  have hsum_Icc : ∑ p ∈ primesLE a, (1 : ℝ) / p =
      ∑ k ∈ Finset.Icc 2 a, (Lsum k - Lsum (k - 1)) / Real.log k := by
    rw [hfilter_eq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    rw [Lsum_sub k (by omega)]
    split_ifs with hkp
    · have hlogk : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
      field_simp [hlogk.ne']
    · simp
  rw [hsum_Icc, abel_identity a ha]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloga_ge : Real.log 2 ≤ Real.log a :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ha)
  have hloga_pos : 0 < Real.log a := lt_of_lt_of_le hlog2_pos hloga_ge
  have hhead : Lsum a / Real.log a ≤ 1 + Real.log 4 / Real.log 2 := by
    have hL := sum_log_div_prime_le a (by omega)
    have h1 : Lsum a / Real.log a ≤ (Real.log a + Real.log 4) / Real.log a :=
      div_le_div_of_nonneg_right hL hloga_pos.le
    have h2 : (Real.log a + Real.log 4) / Real.log a = 1 + Real.log 4 / Real.log a := by
      field_simp [hloga_pos.ne']
    have h3 : Real.log 4 / Real.log a ≤ Real.log 4 / Real.log 2 :=
      div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) hlog2_pos hloga_ge
    linarith
  have htail_bound : ∑ k ∈ Finset.Ico 2 a, Lsum k * (1 / Real.log k - 1 / Real.log (k + 1)) ≤
      ∑ k ∈ Finset.Ico 2 a, (Real.log k + Real.log 4) * (1 / Real.log k - 1 / Real.log (k + 1)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hk_ge2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hlogk_pos : 0 < Real.log k := Real.log_pos (by linarith)
    have hlogk_le : Real.log k ≤ Real.log ((k : ℕ) + 1) :=
      Real.log_le_log (by linarith) (by exact_mod_cast Nat.le_succ k)
    have hdiff_nn : 0 ≤ 1 / Real.log k - 1 / Real.log ((k : ℕ) + 1) := by
      have : 1 / Real.log ((k : ℕ) + 1) ≤ 1 / Real.log k :=
        one_div_le_one_div_of_le hlogk_pos hlogk_le
      linarith
    have hLk := sum_log_div_prime_le k (by omega)
    simpa [Nat.cast_add, Nat.cast_one] using mul_le_mul_of_nonneg_right hLk hdiff_nn
  have hsplit_tail :
      ∑ k ∈ Finset.Ico 2 a, (Real.log k + Real.log 4) * (1 / Real.log k - 1 / Real.log (k + 1)) =
      ∑ k ∈ Finset.Ico 2 a, (1 - Real.log k / Real.log (k + 1)) +
        Real.log 4 * ∑ k ∈ Finset.Ico 2 a, (1 / Real.log k - 1 / Real.log (k + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hlogk_pos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    field_simp [hlogk_pos.ne']
  have hpart1 : ∑ k ∈ Finset.Ico 2 a, (1 - Real.log k / Real.log (k + 1)) ≤
      Real.log (Real.log a) - Real.log (Real.log 2) := by
    have hterm : ∑ k ∈ Finset.Ico 2 a, (1 - Real.log k / Real.log (k + 1)) ≤
        ∑ k ∈ Finset.Ico 2 a, (Real.log (Real.log (k + 1)) - Real.log (Real.log k)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      have hk1 : 1 < k := by omega
      have hlogk_pos : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk1)
      have hlogk1_pos : 0 < Real.log ((k : ℕ) + 1) :=
        Real.log_pos (by exact_mod_cast (show 1 < k + 1 by omega))
      have hy_pos : 0 < Real.log k / Real.log ((k : ℕ) + 1) := div_pos hlogk_pos hlogk1_pos
      have hlog_y := Real.log_le_sub_one_of_pos hy_pos
      rw [Real.log_div hlogk_pos.ne' hlogk1_pos.ne'] at hlog_y
      linarith
    have htel : ∑ k ∈ Finset.Ico 2 a, (Real.log (Real.log (k + 1)) - Real.log (Real.log k)) =
        Real.log (Real.log a) - Real.log (Real.log 2) := by
      have := telescope_sub (f := fun k : ℕ => -Real.log (Real.log k)) a ha
      push_cast at this
      simpa [sub_eq_add_neg, add_comm] using this
    linarith
  have hpart2 : Real.log 4 * ∑ k ∈ Finset.Ico 2 a, (1 / Real.log k - 1 / Real.log (k + 1)) ≤
      Real.log 4 / Real.log 2 := by
    have htel := telescope_sub (f := fun k : ℕ => 1 / Real.log k) a ha
    push_cast at htel
    rw [htel]
    have hsub : (1 : ℝ) / Real.log 2 - 1 / Real.log a ≤ 1 / Real.log 2 := by
      have : 0 ≤ 1 / Real.log a := div_nonneg zero_le_one hloga_pos.le
      linarith
    have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    calc Real.log 4 * (1 / Real.log (2 : ℕ) - 1 / Real.log a)
        ≤ Real.log 4 * (1 / Real.log 2) := by
          simpa using mul_le_mul_of_nonneg_left hsub hlog4_nn
      _ = Real.log 4 / Real.log 2 := by ring
  have h2ratio : 2 * Real.log 4 / Real.log 2 = Real.log 4 / Real.log 2 + Real.log 4 / Real.log 2 := by ring
  linarith

private noncomputable def mertensConst : ℝ :=
  Real.exp (-(2 + 2 * Real.log 4 / Real.log 2 - Real.log (Real.log 2)))

private lemma mertensConst_pos : 0 < mertensConst := Real.exp_pos _

private lemma sum_inv_sub_mul_le (a : ℕ) (ha : 2 ≤ a) :
    ∑ p ∈ primesLE a, (1 : ℝ) / (p * (p - 1)) ≤ 1 := by
  have hsub : primesLE a ⊆ Finset.Icc 2 a := by
    intro p hp
    rw [mem_primesLE] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.1.two_le, hp.2⟩
  have hle1 : ∑ p ∈ primesLE a, (1 : ℝ) / (p * (p - 1)) ≤
      ∑ k ∈ Finset.Icc 2 a, (1 : ℝ) / (k * (k - 1)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => ?_
    rw [Finset.mem_Icc] at hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hmul_pos : (0 : ℝ) < k * (k - 1) := mul_pos (by linarith) (by linarith)
    exact (div_pos one_pos hmul_pos).le
  clear hsub
  have htel : ∑ k ∈ Finset.Icc 2 a, (1 : ℝ) / (k * (k - 1)) = 1 - 1 / (a : ℝ) := by
    clear hle1
    induction a, ha using Nat.le_induction with
    | base => norm_num
    | succ a ha ih =>
      have hIcc : Finset.Icc 2 (a + 1) = insert (a + 1) (Finset.Icc 2 a) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.sum_insert (by simp), ih]
      have ha1 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have ha2 : (a : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp [ha1, ha2]
      ring
  have ha_nn : 0 ≤ (1 : ℝ) / a := by positivity
  linarith

private lemma prod_one_sub_inv_prime_ge (a : ℕ) (ha : 2 ≤ a) :
    mertensConst / Real.log a ≤ ∏ p ∈ primesLE a, (1 - (1 : ℝ) / p) := by
  have hfac_pos : ∀ p ∈ primesLE a, (0 : ℝ) < 1 - 1 / p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLE.mp hp).1.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hprod_pos : 0 < ∏ p ∈ primesLE a, (1 - (1 : ℝ) / p) := Finset.prod_pos hfac_pos
  have hterm : ∀ p ∈ primesLE a,
      (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp (1 / p + 1 / (p * (p - 1))) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLE.mp hp).1.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have heq : (1 - (1 : ℝ) / p)⁻¹ = (1 / p + 1 / (p * (p - 1))) + 1 := by
      field_simp [hp0, hp1]
      ring
    rw [heq]
    exact Real.add_one_le_exp _
  have hinv_le : (∏ p ∈ primesLE a, (1 - (1 : ℝ) / p))⁻¹ ≤
      Real.exp (Real.log (Real.log a) + (2 + 2 * Real.log 4 / Real.log 2 - Real.log (Real.log 2))) := by
    calc (∏ p ∈ primesLE a, (1 - (1 : ℝ) / p))⁻¹
        = ∏ p ∈ primesLE a, (1 - (1 : ℝ) / p)⁻¹ := by rw [Finset.prod_inv_distrib]
      _ ≤ ∏ p ∈ primesLE a, Real.exp (1 / p + 1 / (p * (p - 1))) := by
          refine Finset.prod_le_prod (fun p hp => (inv_pos.mpr (hfac_pos p hp)).le) hterm
      _ = Real.exp (∑ p ∈ primesLE a, (1 / p + 1 / (p * (p - 1)))) := by
          rw [Real.exp_sum]
      _ = Real.exp (∑ p ∈ primesLE a, (1 : ℝ) / p + ∑ p ∈ primesLE a, (1 : ℝ) / (p * (p - 1))) := by
          rw [Finset.sum_add_distrib]
      _ ≤ Real.exp (Real.log (Real.log a) + (2 + 2 * Real.log 4 / Real.log 2 - Real.log (Real.log 2))) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 := sum_inv_prime_le a ha
          have h2 := sum_inv_sub_mul_le a ha
          linarith
  have hloga_pos : 0 < Real.log a := Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  rw [Real.exp_add, Real.exp_log hloga_pos] at hinv_le
  have hc_pos : 0 < Real.exp (2 + 2 * Real.log 4 / Real.log 2 - Real.log (Real.log 2)) :=
    Real.exp_pos _
  have hprod_ge : (Real.log a * Real.exp (2 + 2 * Real.log 4 / Real.log 2 - Real.log (Real.log 2)))⁻¹ ≤
      ∏ p ∈ primesLE a, (1 - (1 : ℝ) / p) := by
    have hmul_pos : 0 < Real.log a * Real.exp (2 + 2 * Real.log 4 / Real.log 2 - Real.log (Real.log 2)) :=
      mul_pos hloga_pos hc_pos
    exact (inv_le_of_inv_le₀ hprod_pos hinv_le).trans_eq rfl
  refine le_trans (le_of_eq ?_) hprod_ge
  rw [mertensConst, Real.exp_neg, mul_inv, mul_comm, div_eq_mul_inv]
  ring

section
open scoped Classical

private noncomputable def fA (A : Set ℕ) (n : ℕ) : ℝ :=
  if n ∈ A ∧ 2 ≤ n then (1 : ℝ) / (n * Real.log n) else 0

private lemma fA_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ fA A n := by
  dsimp [fA]
  split_ifs with h
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h.2
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    positivity
  · exact le_rfl

private lemma summable_fA (A : Set ℕ)
    (hadm : ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, a * t = b → t.minFac ≤ a) :
    Summable (fA A) := by
  refine summable_of_sum_range_le (fA_nonneg A) (c := 1 / mertensConst) fun N => ?_
  let F : Finset ℕ := (Finset.range N).filter (fun n => n ∈ A ∧ 2 ≤ n)
  have hsum_eq : ∑ i ∈ Finset.range N, fA A i = ∑ a ∈ F, (1 : ℝ) / (a * Real.log a) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [hsum_eq]
  have hF : ∀ a ∈ F, a ∈ A ∧ 2 ≤ a := fun a ha => (Finset.mem_filter.mp ha).2
  have hbound := sum_inv_mul_prod_le_one A hadm F hF
  have hmul_le : mertensConst * ∑ a ∈ F, (1 : ℝ) / (a * Real.log a) ≤ 1 := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun a ha => ?_) hbound
    have ha2 : 2 ≤ a := (hF a ha).2
    have ha_pos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    have hloga_pos : 0 < Real.log a := Real.log_pos (by exact_mod_cast (by omega : 1 < a))
    have hprod_ge := prod_one_sub_inv_prime_ge a ha2
    have hmul1 : mertensConst * ((1 : ℝ) / (a * Real.log a)) =
        (1 : ℝ) / a * (mertensConst / Real.log a) := by
      field_simp [ha_pos.ne', hloga_pos.ne']
    rw [hmul1]
    exact mul_le_mul_of_nonneg_left hprod_ge (by positivity)
  exact (le_div_iff₀' mertensConst_pos).mpr hmul_le

theorem erdos_858_infinite_proof (A : Set ℕ) (_hA : A.Infinite) (_h0 : 0 ∉ A)
    (hadm : ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, a * t = b → t.minFac ≤ a) :
    (fun N : ℕ ↦ ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / n) =o[atTop]
      fun N : ℕ ↦ log N := by
  have hsumm : Summable (fA A) := summable_fA A hadm
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hsumm.hasSum.tendsto_sum_nat (c / 2) (by positivity)
  let M : ℕ := max K 2
  have hMK : K ≤ M := le_max_left K 2
  have hM2 : 2 ≤ M := le_max_right K 2
  have hM_dist : dist (∑ i ∈ Finset.range M, fA A i) (∑' i, fA A i) < c / 2 := hK M hMK
  rw [Real.dist_eq] at hM_dist
  have hM_tail : (∑' i, fA A i) - ∑ i ∈ Finset.range M, fA A i < c / 2 :=
    (le_abs_self _).trans_lt (by simpa [abs_sub_comm] using hM_dist)
  let B : ℝ := ∑ n ∈ (Finset.Icc 1 (M - 1)).filter (· ∈ A), (1 : ℝ) / n
  have hB_nn : 0 ≤ B := Finset.sum_nonneg fun n _ => by positivity
  have hlog_top : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_ev1 : ∀ᶠ N : ℕ in atTop, max 1 (2 * B / c) ≤ Real.log N :=
    hlog_top.eventually_ge_atTop (max 1 (2 * B / c))
  have h_ev2 : ∀ᶠ N : ℕ in atTop, M ≤ N := eventually_ge_atTop M
  filter_upwards [h_ev1, h_ev2] with N hlogN_ge hMN
  have hlogN_ge1 : 1 ≤ Real.log N := (le_max_left 1 _).trans hlogN_ge
  have hlogN_pos : 0 < Real.log N := by linarith
  have hsum_nn : 0 ≤ ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / n :=
    Finset.sum_nonneg fun n _ => by positivity
  rw [Real.norm_of_nonneg hsum_nn, Real.norm_of_nonneg hlogN_pos.le]
  have hsub_union : (Finset.Icc 1 N).filter (· ∈ A) ⊆
      (Finset.Icc 1 (M - 1)).filter (· ∈ A) ∪ (Finset.Ico M (N + 1)).filter (· ∈ A) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    by_cases hnM : n < M
    · exact Or.inl ⟨⟨hn.1.1, by omega⟩, hn.2⟩
    · exact Or.inr ⟨⟨by omega, by omega⟩, hn.2⟩
  have hsplit_le : ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / n ≤
      B + ∑ n ∈ (Finset.Ico M (N + 1)).filter (· ∈ A), (1 : ℝ) / n := by
    have h1 : ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / n ≤
        ∑ n ∈ (Finset.Icc 1 (M - 1)).filter (· ∈ A) ∪ (Finset.Ico M (N + 1)).filter (· ∈ A),
          (1 : ℝ) / n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub_union fun n _ _ => by positivity
    have hdisj : Disjoint ((Finset.Icc 1 (M - 1)).filter (· ∈ A))
        ((Finset.Ico M (N + 1)).filter (· ∈ A)) := by
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico] at hn1 hn2
      omega
    have h2 : ∑ n ∈ (Finset.Icc 1 (M - 1)).filter (· ∈ A) ∪ (Finset.Ico M (N + 1)).filter (· ∈ A),
        (1 : ℝ) / n = B + ∑ n ∈ (Finset.Ico M (N + 1)).filter (· ∈ A), (1 : ℝ) / n :=
      Finset.sum_union hdisj
    exact h1.trans h2.le
  have hB_le : B ≤ (c / 2) * Real.log N := by
    have h2Bc : 2 * B / c ≤ Real.log N := (le_max_right 1 _).trans hlogN_ge
    have hc2 : 2 * B ≤ Real.log N * c := (div_le_iff₀ hc).mp h2Bc
    linarith
  have htail_le : ∑ n ∈ (Finset.Ico M (N + 1)).filter (· ∈ A), (1 : ℝ) / n ≤
      (c / 2) * Real.log N := by
    have hterm : ∑ n ∈ (Finset.Ico M (N + 1)).filter (· ∈ A), (1 : ℝ) / n ≤
        ∑ n ∈ (Finset.Ico M (N + 1)).filter (· ∈ A), fA A n * Real.log N := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [Finset.mem_filter, Finset.mem_Ico] at hn
      have hn2 : 2 ≤ n := hM2.trans hn.1.1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hlogn_le : Real.log n ≤ Real.log N := Real.log_le_log hn_pos hnN
      have hfA_eq : fA A n = (1 : ℝ) / (n * Real.log n) := by
        dsimp [fA]
        rw [if_pos ⟨hn.2, hn2⟩]
      have h1_eq : (1 : ℝ) / n = fA A n * Real.log n := by
        rw [hfA_eq]
        field_simp [hn_pos.ne', hlogn_pos.ne']
      rw [h1_eq]
      exact mul_le_mul_of_nonneg_left hlogn_le (fA_nonneg A n)
    have hfilt_sub : (Finset.Ico M (N + 1)).filter (· ∈ A) ⊆ Finset.Ico M (N + 1) :=
      Finset.filter_subset _ _
    have hsum_sub : ∑ n ∈ (Finset.Ico M (N + 1)).filter (· ∈ A), fA A n * Real.log N ≤
        (∑ n ∈ Finset.Ico M (N + 1), fA A n) * Real.log N := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum_of_subset_of_nonneg hfilt_sub fun n _ _ =>
        mul_nonneg (fA_nonneg A n) hlogN_pos.le
    have hIco_bound : ∑ n ∈ Finset.Ico M (N + 1), fA A n ≤ c / 2 := by
      rw [Finset.sum_Ico_eq_sub _ (by omega)]
      have hle_tsum : ∑ i ∈ Finset.range (N + 1), fA A i ≤ ∑' i, fA A i :=
        hsumm.sum_le_tsum (Finset.range (N + 1)) fun i _ => fA_nonneg A i
      linarith
    exact hterm.trans (hsum_sub.trans (mul_le_mul_of_nonneg_right hIco_bound hlogN_pos.le))
  linarith

end

end OMA.Erdos858Inf

theorem OMA.solution : type_of% @Erdos858.erdos_858.variants.infinite :=
  OMA.Erdos858Inf.erdos_858_infinite_proof
