import OMAStatements.S_oeis_a363418
import Mathlib

namespace OeisA363418Proof

open PowerSeries
open scoped BigOperators

/-! ### Part 1: Elementary `p`-adic divisibility on `ℚ` -/

/-- `pDiv p k q` means `q = p^k * a / b` for some `a : ℤ`, `b : ℕ` with `b ≠ 0` and `¬ (p ∣ b)`. -/
private def pDiv (p k : ℕ) (q : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), b ≠ 0 ∧ ¬ (p ∣ b) ∧ q = (p : ℚ) ^ k * (a : ℚ) / (b : ℚ)

private lemma pDiv_zero (p k : ℕ) (hp : p.Prime) : pDiv p k 0 := by
  refine ⟨0, 1, one_ne_zero, ?_, by simp⟩
  exact mt Nat.dvd_one.mp hp.ne_one

private lemma pDiv_of_int (p : ℕ) (hp : p.Prime) (z : ℤ) : pDiv p 0 (z : ℚ) := by
  refine ⟨z, 1, one_ne_zero, ?_, by simp⟩
  exact mt Nat.dvd_one.mp hp.ne_one

private lemma pDiv_of_int_dvd (p k : ℕ) (hp : p.Prime) (z : ℤ) (h : (p : ℤ) ^ k ∣ z) :
    pDiv p k (z : ℚ) := by
  rcases h with ⟨a, rfl⟩
  refine ⟨a, 1, one_ne_zero, mt Nat.dvd_one.mp hp.ne_one, ?_⟩
  push_cast
  simp

private lemma pDiv_mono {p k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) {q : ℚ} (hq : pDiv p k₂ q) :
    pDiv p k₁ q := by
  rcases hq with ⟨a, b, hb0, hpb, rfl⟩
  refine ⟨a * (p : ℤ) ^ (k₂ - k₁), b, hb0, hpb, ?_⟩
  push_cast
  have hpow : (p : ℚ) ^ k₂ = (p : ℚ) ^ k₁ * (p : ℚ) ^ (k₂ - k₁) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  rw [hpow]
  ring

private lemma pDiv_add {p k : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h₁ : pDiv p k q₁) (h₂ : pDiv p k q₂) : pDiv p k (q₁ + q₂) := by
  rcases h₁ with ⟨a₁, b₁, hb₁, hpb₁, rfl⟩
  rcases h₂ with ⟨a₂, b₂, hb₂, hpb₂, rfl⟩
  refine ⟨a₁ * (b₂ : ℤ) + a₂ * (b₁ : ℤ), b₁ * b₂, mul_ne_zero hb₁ hb₂,
    fun h => (hp.dvd_mul.mp h).elim hpb₁ hpb₂, ?_⟩
  have h1 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb₁
  have h2 : (b₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb₂
  push_cast
  field_simp

private lemma pDiv_sub {p k : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h₁ : pDiv p k q₁) (h₂ : pDiv p k q₂) : pDiv p k (q₁ - q₂) := by
  rw [sub_eq_add_neg]
  refine pDiv_add hp h₁ ?_
  rcases h₂ with ⟨a, b, hb, hpb, rfl⟩
  refine ⟨-a, b, hb, hpb, ?_⟩
  push_cast
  ring

private lemma pDiv_sum {ι : Type*} {p k : ℕ} (hp : p.Prime) (s : Finset ι) (g : ι → ℚ)
    (hg : ∀ i ∈ s, pDiv p k (g i)) : pDiv p k (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using pDiv_zero p k hp
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact pDiv_add hp (hg x (Finset.mem_insert_self x s))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

private lemma pDiv_mul {p k₁ k₂ : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h₁ : pDiv p k₁ q₁) (h₂ : pDiv p k₂ q₂) : pDiv p (k₁ + k₂) (q₁ * q₂) := by
  rcases h₁ with ⟨a₁, b₁, hb₁, hpb₁, rfl⟩
  rcases h₂ with ⟨a₂, b₂, hb₂, hpb₂, rfl⟩
  refine ⟨a₁ * a₂, b₁ * b₂, mul_ne_zero hb₁ hb₂,
    fun h => (hp.dvd_mul.mp h).elim hpb₁ hpb₂, ?_⟩
  push_cast
  rw [pow_add]
  ring

private lemma pDiv_pow {p k : ℕ} (hp : p.Prime) {q : ℚ} (hq : pDiv p k q) :
    ∀ j : ℕ, pDiv p (j * k) (q ^ j) := by
  intro j
  induction j with
  | zero =>
    simpa using pDiv_of_int p hp 1
  | succ j ih =>
    rw [pow_succ, Nat.succ_mul]
    exact pDiv_mul hp ih hq

private lemma pDiv_int_dvd {p k : ℕ} (hp : p.Prime) (z : ℤ) (hz : pDiv p k (z : ℚ)) :
    (p : ℤ) ^ k ∣ z := by
  rcases hz with ⟨a, b, hb0, hpb, heq⟩
  have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
  have hq : (z : ℚ) * (b : ℚ) = (p : ℚ) ^ k * (a : ℚ) := by
    rw [heq]; field_simp
  have hz_eq : z * (b : ℤ) = (p : ℤ) ^ k * a := by exact_mod_cast hq
  have hcop : IsCoprime ((p : ℤ) ^ k) (b : ℤ) := by
    have hc : Nat.Coprime p b := hp.coprime_iff_not_dvd.mpr hpb
    have hc' : Nat.Coprime (p ^ k) b := hc.pow_left k
    exact_mod_cast hc'.isCoprime
  have hdvd : (p : ℤ) ^ k ∣ z * (b : ℤ) := ⟨a, hz_eq⟩
  exact hcop.dvd_of_dvd_mul_right hdvd

private lemma pDiv_div_nat {p k n : ℕ} (hp : p.Prime) (hn : n ≠ 0) {q : ℚ}
    (hq : pDiv p k q) (hv : padicValNat p n ≤ k) :
    pDiv p (k - padicValNat p n) (q / (n : ℚ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s := padicValNat p n
  have hs_dvd : p ^ s ∣ n := pow_padicValNat_dvd
  rcases hs_dvd with ⟨u, hu⟩
  have hu0 : u ≠ 0 := by
    intro h; rw [h, mul_zero] at hu; exact hn hu
  have hpu : ¬ (p ∣ u) := by
    intro hdiv
    rcases hdiv with ⟨w, rfl⟩
    have hdvd1 : p ^ (s + 1) ∣ n := ⟨w, by rw [hu, pow_succ]; ring⟩
    have hle : s + 1 ≤ padicValNat p n :=
      (padicValNat_dvd_iff_le hn).mp hdvd1
    omega
  rcases hq with ⟨a, b, hb0, hpb, rfl⟩
  refine ⟨a, b * u, mul_ne_zero hb0 hu0,
    fun h => (hp.dvd_mul.mp h).elim hpb hpu, ?_⟩
  have hpow : (p : ℚ) ^ k = (p : ℚ) ^ (k - s) * (p : ℚ) ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hv]
  have hnq : (n : ℚ) = (p : ℚ) ^ s * (u : ℚ) := by exact_mod_cast hu
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hb0q : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
  have hu0q : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hu0
  rw [hpow, hnq]
  push_cast
  field_simp

private lemma padicValNat_factorial_bound {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) :
    4 * padicValNat p j.factorial ≤ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  let b := Nat.log p j + 1
  rw [padicValNat_factorial (Nat.lt_succ_self (Nat.log p j))]
  have hle_p : (p - 1) * ∑ i ∈ Finset.Ico 1 b, j / p ^ i ≤ j := by
    have haux : ∀ k : ℕ, (p - 1) * ∑ i ∈ Finset.Ico 1 (k + 1), j / p ^ i + j / p ^ k ≤ j := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hIco : Finset.Ico 1 (k + 2) = insert (k + 1) (Finset.Ico 1 (k + 1)) := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        rw [hIco, Finset.sum_insert (by simp)]
        have hstep : p * (j / p ^ (k + 1)) ≤ j / p ^ k := by
          rw [pow_succ, ← Nat.div_div_eq_div_mul]
          exact Nat.mul_div_le (j / p ^ k) p
        have hmul : (p - 1) * (j / p ^ (k + 1)) + j / p ^ (k + 1) = p * (j / p ^ (k + 1)) := by
          cases p with
          | zero => omega
          | succ p' => simp [Nat.succ_mul]
        have hdist : (p - 1) * (j / p ^ (k + 1) + ∑ i ∈ Finset.Ico 1 (k + 1), j / p ^ i) +
            j / p ^ (k + 1) =
            (p - 1) * ∑ i ∈ Finset.Ico 1 (k + 1), j / p ^ i + p * (j / p ^ (k + 1)) := by
          rw [mul_add]; linarith
        omega
    have h1 := haux (Nat.log p j)
    exact le_trans (Nat.le_add_right _ _) h1
  have h4 : 4 ≤ p - 1 := by omega
  exact le_trans (Nat.mul_le_mul_right _ h4) hle_p

private lemma pDiv_pow_div_factorial {p r j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) (hj : 3 ≤ j) (m : ℕ) :
    pDiv p (3 * r) (((m : ℚ) * (p : ℚ) ^ r) ^ j / (j.factorial : ℚ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hval : padicValNat p j.factorial ≤ j * r - 3 * r := by
    by_cases hj3 : j = 3
    · subst hj3
      have hndvd : ¬ (p ∣ (3 : ℕ).factorial) := by
        have : (3 : ℕ).factorial = 6 := by decide
        rw [this]
        intro h
        have hle := Nat.le_of_dvd (by norm_num) h
        have : p = 5 ∨ p = 6 := by omega
        rcases this with rfl | rfl
        · norm_num at h
        · exact absurd hp (by decide)
      rw [padicValNat.eq_zero_of_not_dvd hndvd]
      omega
    · by_cases hj4 : j = 4
      · subst hj4
        have hndvd : ¬ (p ∣ (4 : ℕ).factorial) := by
          have h24 : (4 : ℕ).factorial = 2 * 2 * 2 * 3 := by decide
          rw [h24]
          intro h
          have h1 := hp.dvd_mul.mp h
          rcases h1 with h2 | h3
          · have h2' := hp.dvd_mul.mp h2
            rcases h2' with h2'' | h2'''
            · have h2'''' := hp.dvd_mul.mp h2''
              rcases h2'''' with ha | ha <;> exact absurd (Nat.le_of_dvd (by norm_num) ha) (by omega)
            · exact absurd (Nat.le_of_dvd (by norm_num) h2''') (by omega)
          · exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
        rw [padicValNat.eq_zero_of_not_dvd hndvd]
        omega
      · have hj5 : 5 ≤ j := by omega
        have hb := padicValNat_factorial_bound hp hp5 j
        have hsub : (j - 3) * r = j * r - 3 * r := Nat.sub_mul j 3 r
        have hjr : j - 3 ≤ j * r - 3 * r := by
          have : (j - 3) * 1 ≤ (j - 3) * r := Nat.mul_le_mul_left _ hr
          omega
        omega
  have hnum : pDiv p (j * r) (((m : ℚ) * (p : ℚ) ^ r) ^ j) := by
    have hbase : pDiv p r ((m : ℚ) * (p : ℚ) ^ r) := by
      refine ⟨m, 1, one_ne_zero, mt Nat.dvd_one.mp hp.ne_one, ?_⟩
      simp [mul_comm]
    exact pDiv_pow hp hbase j
  have h3j : 3 * r ≤ j * r := Nat.mul_le_mul_right r hj
  have hdiv := pDiv_div_nat hp (Nat.factorial_ne_zero j) hnum (by omega)
  exact pDiv_mono (by omega) hdiv

/-! ### Part 2: Wolstenholme-type sum `∑_{a=1, p∤a}^{pt-1} 1/(a(pt-a)) ≡ 0 (mod p^(s+1))` -/

private lemma zmod_sum_inv_sq_zero {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (he : 1 ≤ e) :
    let P := p ^ e
    ∑ r ∈ (Finset.range P).filter (fun r => ¬ p ∣ r), (((r : ZMod P)⁻¹) ^ 2) = 0 := by
  intro P
  have hP_pos : 0 < P := pow_pos hp.pos e
  have hcop2 : Nat.Coprime 2 P := by
    have h2 : Nat.Coprime 2 p := hp.coprime_iff_not_dvd.mpr (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega) |>.symm
    exact h2.pow_right e
  have hcop3 : Nat.Coprime 3 P := by
    have h3 : Nat.Coprime 3 p := hp.coprime_iff_not_dvd.mpr (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega) |>.symm
    exact h3.pow_right e
  let S := (Finset.range P).filter (fun r => ¬ p ∣ r)
  let T : ZMod P := ∑ r ∈ S, (((r : ZMod P)⁻¹) ^ 2)
  have h2_unit : IsUnit (2 : ZMod P) := (ZMod.isUnit_iff_coprime 2 P).mpr hcop2
  have h3_unit : IsUnit (3 : ZMod P) := (ZMod.isUnit_iff_coprime 3 P).mpr hcop3
  have hbij : T = ∑ r ∈ S, ((((2 * r) % P : ℕ) : ZMod P)⁻¹) ^ 2 := by
    symm
    refine Finset.sum_bij (fun r _ => (2 * r) % P) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro r hr
      simp only [S, Finset.mem_filter, Finset.mem_range] at hr ⊢
      refine ⟨Nat.mod_lt _ hP_pos, ?_⟩
      intro hdiv
      have hpP : p ∣ P := dvd_pow_self p (by omega)
      have h2r : p ∣ 2 * r := (Nat.dvd_mod_iff hpP).mp hdiv
      rcases hp.dvd_mul.mp h2r with h2 | hr'
      · have := Nat.le_of_dvd (by norm_num) h2; omega
      · exact hr.2 hr'
    · intro a ha b hb heq
      simp only [S, Finset.mem_filter, Finset.mem_range] at ha hb
      have hcast : ((2 * a : ℕ) : ZMod P) = ((2 * b : ℕ) : ZMod P) := by
        have h1 : (((2 * a) % P : ℕ) : ZMod P) = ((2 * a : ℕ) : ZMod P) := by
          rw [ZMod.natCast_mod]
        have h2 : (((2 * b) % P : ℕ) : ZMod P) = ((2 * b : ℕ) : ZMod P) := by
          rw [ZMod.natCast_mod]
        rw [← h1, ← h2, heq]
      push_cast at hcast
      have hab : (a : ZMod P) = (b : ZMod P) := h2_unit.mul_left_cancel hcast
      have hval := congrArg ZMod.val hab
      haveI : NeZero P := ⟨Nat.ne_of_gt hP_pos⟩
      rw [ZMod.val_natCast_of_lt ha.1, ZMod.val_natCast_of_lt hb.1] at hval
      exact hval
    · intro y hy
      simp only [S, Finset.mem_filter, Finset.mem_range] at hy
      haveI : NeZero P := ⟨Nat.ne_of_gt hP_pos⟩
      let x : ℕ := ((2 : ZMod P)⁻¹ * (y : ZMod P)).val
      have hx_lt : x < P := ZMod.val_lt _
      have h2x_mod : (2 * x) % P = y := by
        have h2x_z : ((2 * x : ℕ) : ZMod P) = (y : ZMod P) := by
          push_cast
          simp only [x, ZMod.natCast_zmod_val, ← mul_assoc]
          have h2inv : (2 : ZMod P) * (2 : ZMod P)⁻¹ = 1 :=
            ZMod.mul_inv_of_unit (2 : ZMod P) h2_unit
          rw [h2inv, one_mul]
        have hval := congrArg ZMod.val h2x_z
        rw [ZMod.val_natCast, ZMod.val_natCast_of_lt hy.1] at hval
        exact hval
      refine ⟨x, ?_, h2x_mod⟩
      simp only [S, Finset.mem_filter, Finset.mem_range]
      refine ⟨hx_lt, ?_⟩
      intro hpx
      have hpP : p ∣ P := dvd_pow_self p (by omega)
      have h2x : p ∣ 2 * x := dvd_mul_of_dvd_right hpx 2
      have hpy : p ∣ y := by rw [← h2x_mod]; exact (Nat.dvd_mod_iff hpP).mpr h2x
      exact hy.2 hpy
  have h4T : (4 : ZMod P) * T = T := by
    calc (4 : ZMod P) * T
        = (4 : ZMod P) * ∑ r ∈ S, ((((2 * r) % P : ℕ) : ZMod P)⁻¹) ^ 2 := by rw [← hbij]
      _ = ∑ r ∈ S, (4 : ZMod P) * ((((2 * r) % P : ℕ) : ZMod P)⁻¹) ^ 2 := Finset.mul_sum _ _ _
      _ = ∑ r ∈ S, (((r : ZMod P)⁻¹) ^ 2) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hpr : ¬ p ∣ r := (Finset.mem_filter.mp hr).2
        have hcop_r : Nat.Coprime r P := (hp.coprime_iff_not_dvd.mpr hpr).symm.pow_right e
        have hr_unit : IsUnit (r : ZMod P) := (ZMod.isUnit_iff_coprime r P).mpr hcop_r
        have h2r_unit : IsUnit ((2 : ZMod P) * (r : ZMod P)) := h2_unit.mul hr_unit
        have hmod : (((2 * r) % P : ℕ) : ZMod P) = (2 : ZMod P) * (r : ZMod P) := by
          rw [ZMod.natCast_mod]; push_cast; rfl
        rw [hmod]
        have hinv : ((2 : ZMod P) * (r : ZMod P))⁻¹ = (2 : ZMod P)⁻¹ * (r : ZMod P)⁻¹ := by
          have hmul : ((2 : ZMod P) * (r : ZMod P)) * ((2 : ZMod P)⁻¹ * (r : ZMod P)⁻¹) = 1 := by
            calc ((2 : ZMod P) * (r : ZMod P)) * ((2 : ZMod P)⁻¹ * (r : ZMod P)⁻¹)
                = ((2 : ZMod P) * (2 : ZMod P)⁻¹) * ((r : ZMod P) * (r : ZMod P)⁻¹) := by ring
              _ = 1 * 1 := by
                rw [ZMod.mul_inv_of_unit (2 : ZMod P) h2_unit, ZMod.mul_inv_of_unit (r : ZMod P) hr_unit]
              _ = 1 := one_mul 1
          have hmul2 : ((2 : ZMod P) * (r : ZMod P)) * ((2 : ZMod P) * (r : ZMod P))⁻¹ = 1 :=
            ZMod.mul_inv_of_unit ((2 : ZMod P) * (r : ZMod P)) h2r_unit
          exact h2r_unit.mul_left_cancel (hmul2.trans hmul.symm)
        rw [hinv, mul_pow]
        have h4inv : (4 : ZMod P) * ((2 : ZMod P)⁻¹) ^ 2 = 1 := by
          have h2i : (2 : ZMod P) * (2 : ZMod P)⁻¹ = 1 := ZMod.mul_inv_of_unit 2 h2_unit
          calc (4 : ZMod P) * ((2 : ZMod P)⁻¹) ^ 2
              = ((2 : ZMod P) * (2 : ZMod P)⁻¹) * ((2 : ZMod P) * (2 : ZMod P)⁻¹) := by ring
            _ = 1 := by rw [h2i, one_mul]
        calc (4 : ZMod P) * (((2 : ZMod P)⁻¹) ^ 2 * ((r : ZMod P)⁻¹) ^ 2)
            = ((4 : ZMod P) * ((2 : ZMod P)⁻¹) ^ 2) * ((r : ZMod P)⁻¹) ^ 2 := by ring
          _ = ((r : ZMod P)⁻¹) ^ 2 := by rw [h4inv, one_mul]
  have h3T : (3 : ZMod P) * T = 0 := by
    have hsub : (4 : ZMod P) * T - T = 0 := sub_eq_zero.mpr h4T
    have h3 : (4 : ZMod P) * T - T = (3 : ZMod P) * T := by ring
    rw [← h3]; exact hsub
  have h30 : (3 : ZMod P) * T = (3 : ZMod P) * 0 := by rw [h3T, mul_zero]
  exact h3_unit.mul_left_cancel h30

private lemma pDiv_sum_inv_mul {p t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ht : 1 ≤ t) :
    pDiv p (padicValNat p t + 1)
      (∑ a ∈ (Finset.Ico 1 (p * t)).filter (fun a => ¬ p ∣ a),
        (1 : ℚ) / ((a : ℚ) * ((p * t - a : ℕ) : ℚ))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set s := padicValNat p t
  let P : ℕ := p ^ (s + 1)
  let M : ℕ := p * t
  have hPM : P ∣ M := by
    have hs : p ^ s ∣ t := pow_padicValNat_dvd
    rcases hs with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    simp only [P, M, pow_succ']
    rw [hu]; ring
  rcases hPM with ⟨u, huM⟩
  let S := (Finset.Ico 1 M).filter (fun a => ¬ p ∣ a)
  let D : ℕ := ∏ a ∈ S, a
  have hD_pos : D ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro a ha
    have := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).1
    omega
  have hpD : ¬ p ∣ D := by
    intro hdvd
    rcases hp.prime.dvd_finset_prod_iff _ |>.mp hdvd with ⟨a, ha, hpa⟩
    exact (Finset.mem_filter.mp ha).2 hpa
  have hmem_sub : ∀ a ∈ S, M - a ∈ S := by
    intro a ha
    simp only [S, Finset.mem_filter, Finset.mem_Ico] at ha ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro hsub
    have hMp : p ∣ M := dvd_mul_right p t
    have ha_eq : a + (M - a) = M := Nat.add_sub_of_le (le_of_lt ha.1.2)
    have : p ∣ a := (Nat.dvd_add_left hsub).mp (by rw [ha_eq]; exact hMp)
    exact ha.2 this
  let N : ℕ := ∑ a ∈ S, (D / a) * (D / (M - a))
  have hrat : ∑ a ∈ S, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ)) =
      (N : ℚ) / ((D * D : ℕ) : ℚ) := by
    simp only [N, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha_dvd : a ∣ D := Finset.dvd_prod_of_mem _ ha
    have hma_dvd : (M - a) ∣ D := Finset.dvd_prod_of_mem _ (hmem_sub a ha)
    have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by
      have := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).1; omega)
    have hma0 : ((M - a : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by
      have := (Finset.mem_Ico.mp (Finset.mem_filter.mp (hmem_sub a ha)).1).1; omega)
    have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD_pos
    have h1 : ((D / a : ℕ) : ℚ) * (a : ℚ) = (D : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel ha_dvd
    have h2 : ((D / (M - a) : ℕ) : ℚ) * ((M - a : ℕ) : ℚ) = (D : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hma_dvd
    have hDsq : (D : ℚ) ^ 2 =
        (((D / a : ℕ) : ℚ) * (a : ℚ)) * (((D / (M - a) : ℕ) : ℚ) * ((M - a : ℕ) : ℚ)) := by
      rw [h1, h2, sq]
    push_cast
    field_simp
    rw [hDsq]
    ring
  have hPN : P ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff]
    simp only [N, Nat.cast_sum, Nat.cast_mul]
    have hterm : ∀ a ∈ S,
        ((D / a : ℕ) : ZMod P) * ((D / (M - a) : ℕ) : ZMod P) =
        -((D : ZMod P) ^ 2 * (((a : ZMod P)⁻¹) ^ 2)) := by
      intro a ha
      have hpa : ¬ p ∣ a := (Finset.mem_filter.mp ha).2
      have hcop_a : Nat.Coprime a P := (hp.coprime_iff_not_dvd.mpr hpa).symm.pow_right (s + 1)
      have ha_unit : IsUnit (a : ZMod P) := (ZMod.isUnit_iff_coprime a P).mpr hcop_a
      have hma_in := hmem_sub a ha
      have hcop_ma : Nat.Coprime (M - a) P :=
        (hp.coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hma_in).2).symm.pow_right (s + 1)
      have hma_unit : IsUnit ((M - a : ℕ) : ZMod P) :=
        (ZMod.isUnit_iff_coprime (M - a) P).mpr hcop_ma
      have hda : ((D / a : ℕ) : ZMod P) = (D : ZMod P) * (a : ZMod P)⁻¹ := by
        have hmul : ((D / a : ℕ) : ZMod P) * (a : ZMod P) = (D : ZMod P) := by
          rw [← Nat.cast_mul, Nat.div_mul_cancel (Finset.dvd_prod_of_mem _ ha)]
        calc ((D / a : ℕ) : ZMod P)
            = ((D / a : ℕ) : ZMod P) * ((a : ZMod P) * (a : ZMod P)⁻¹) := by
              rw [ZMod.mul_inv_of_unit (a : ZMod P) ha_unit, mul_one]
          _ = (((D / a : ℕ) : ZMod P) * (a : ZMod P)) * (a : ZMod P)⁻¹ := by ring
          _ = (D : ZMod P) * (a : ZMod P)⁻¹ := by rw [hmul]
      have hdma : ((D / (M - a) : ℕ) : ZMod P) = (D : ZMod P) * ((M - a : ℕ) : ZMod P)⁻¹ := by
        have hmul : ((D / (M - a) : ℕ) : ZMod P) * ((M - a : ℕ) : ZMod P) = (D : ZMod P) := by
          rw [← Nat.cast_mul, Nat.div_mul_cancel (Finset.dvd_prod_of_mem _ hma_in)]
        calc ((D / (M - a) : ℕ) : ZMod P)
            = ((D / (M - a) : ℕ) : ZMod P) * (((M - a : ℕ) : ZMod P) * ((M - a : ℕ) : ZMod P)⁻¹) := by
              rw [ZMod.mul_inv_of_unit ((M - a : ℕ) : ZMod P) hma_unit, mul_one]
          _ = (((D / (M - a) : ℕ) : ZMod P) * ((M - a : ℕ) : ZMod P)) * ((M - a : ℕ) : ZMod P)⁻¹ := by ring
          _ = (D : ZMod P) * ((M - a : ℕ) : ZMod P)⁻¹ := by rw [hmul]
      have hma_neg : ((M - a : ℕ) : ZMod P) = -(a : ZMod P) := by
        have hadd : (a : ZMod P) + ((M - a : ℕ) : ZMod P) = (M : ZMod P) := by
          rw [← Nat.cast_add, Nat.add_sub_of_le (le_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2)]
        have hM0 : (M : ZMod P) = 0 := (ZMod.natCast_eq_zero_iff M P).mpr ⟨u, huM⟩
        rw [hM0] at hadd
        exact eq_neg_of_add_eq_zero_right hadd
      have hinv_neg : ((M - a : ℕ) : ZMod P)⁻¹ = -(a : ZMod P)⁻¹ := by
        have h1 : (-(a : ZMod P)) * (-(a : ZMod P)⁻¹) = 1 := by
          rw [neg_mul_neg]; exact ZMod.mul_inv_of_unit (a : ZMod P) ha_unit
        have h2 : (-(a : ZMod P)) * ((M - a : ℕ) : ZMod P)⁻¹ = 1 := by
          rw [← hma_neg]; exact ZMod.mul_inv_of_unit ((M - a : ℕ) : ZMod P) hma_unit
        have hneg_unit : IsUnit (-(a : ZMod P)) := ha_unit.neg
        exact hneg_unit.mul_left_cancel (h2.trans h1.symm)
      rw [hda, hdma, hinv_neg]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.mul_sum]
    have hblocks : ∑ a ∈ S, (((a : ZMod P)⁻¹) ^ 2) =
        ∑ _q ∈ Finset.range u,
          ∑ r ∈ (Finset.range P).filter (fun r => ¬ p ∣ r), (((r : ZMod P)⁻¹) ^ 2) := by
      have hP_pos : 0 < P := pow_pos hp.pos (s + 1)
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun a _ => (a / P, a % P)) ?_ ?_ ?_ ?_
      · intro a ha
        simp only [S, Finset.mem_filter, Finset.mem_Ico] at ha
        simp only [Finset.mem_product, Finset.mem_range, Finset.mem_filter]
        refine ⟨?_, Nat.mod_lt a hP_pos, ?_⟩
        · rw [Nat.div_lt_iff_lt_mul hP_pos, mul_comm, ← huM]
          exact ha.1.2
        · intro hdiv
          have hpP : p ∣ P := dvd_pow_self p (Nat.succ_ne_zero s)
          exact ha.2 ((Nat.dvd_mod_iff hpP).mp hdiv)
      · intro a₁ _ a₂ _ heq
        simp only [Prod.mk.injEq] at heq
        have h1 := Nat.div_add_mod a₁ P
        have h2 := Nat.div_add_mod a₂ P
        rw [← h1, ← h2, heq.1, heq.2]
      · rintro ⟨q, r⟩ hqr
        simp only [Finset.mem_product, Finset.mem_range, Finset.mem_filter] at hqr
        refine ⟨q * P + r, ?_, ?_⟩
        · simp only [S, Finset.mem_filter, Finset.mem_Ico]
          have hr_pos : 1 ≤ r := by
            by_contra h0
            have hr0 : r = 0 := by omega
            subst hr0; exact hqr.2.2 (dvd_zero p)
          have hltM : q * P + r < M := by
            have hq1 : (q + 1) * P ≤ u * P := Nat.mul_le_mul_right P hqr.1
            rw [Nat.add_mul, one_mul] at hq1
            rw [huM, mul_comm P u]; omega
          refine ⟨⟨by omega, hltM⟩, ?_⟩
          intro hdiv
          have hpP : p ∣ P := dvd_pow_self p (Nat.succ_ne_zero s)
          have hqp : p ∣ q * P := dvd_mul_of_dvd_right hpP q
          exact hqr.2.2 ((Nat.dvd_add_right hqp).mp hdiv)
        · simp only [Prod.mk.injEq]
          rw [mul_comm q P, Nat.mul_add_div hP_pos, Nat.div_eq_of_lt hqr.2.1, add_zero,
            Nat.mul_add_mod, Nat.mod_eq_of_lt hqr.2.1]
          exact ⟨rfl, rfl⟩
      · intro a _
        have hmod : ((a % P : ℕ) : ZMod P) = (a : ZMod P) := ZMod.natCast_mod a P
        rw [hmod]
    rw [hblocks]
    have hz := zmod_sum_inv_sq_zero hp hp5 (Nat.succ_pos s)
    simp [P, hz]
  rcases hPN with ⟨w, hw⟩
  rw [hrat, hw]
  refine ⟨w, D * D, mul_ne_zero hD_pos hD_pos, fun h => (hp.dvd_mul.mp h).elim hpD hpD, ?_⟩
  simp only [P]
  push_cast
  rfl

/-! ### Part 3: Power-series `p`-expansion `f(X^p)` and finite exponential `E_N` -/

private noncomputable def expandP (p : ℕ) (g : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => if p ∣ k then PowerSeries.coeff (k / p) g else 0

private lemma coeff_expandP (p : ℕ) (g : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k (expandP p g) = if p ∣ k then PowerSeries.coeff (k / p) g else 0 := by
  simp [expandP]

private lemma expandP_mul (p : ℕ) (hp : 0 < p) (g h : PowerSeries ℚ) :
    expandP p (g * h) = expandP p g * expandP p h := by
  ext n
  rw [coeff_expandP]
  by_cases hpn : p ∣ n
  · rw [if_pos hpn, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    rcases hpn with ⟨q, rfl⟩
    rw [Nat.mul_div_cancel_left q hp]
    have hfilt :
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (p * q),
          PowerSeries.coeff x.1 (expandP p g) * PowerSeries.coeff x.2 (expandP p h) =
        ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (p * q)).filter (fun x => p ∣ x.1 ∧ p ∣ x.2),
          PowerSeries.coeff x.1 (expandP p g) * PowerSeries.coeff x.2 (expandP p h) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro x hx hxnot
      rw [Finset.mem_filter, not_and] at hxnot
      have hnot : ¬ (p ∣ x.1 ∧ p ∣ x.2) := hxnot hx
      rw [coeff_expandP, coeff_expandP]
      by_cases h1 : p ∣ x.1
      · have h2 : ¬ p ∣ x.2 := fun h2 => hnot ⟨h1, h2⟩
        simp [h2]
      · simp [h1]
    rw [hfilt]
    symm
    refine Finset.sum_bij (fun x _ => (x.1 / p, x.2 / p)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hx ⊢
      rcases hx.2.1 with ⟨a, ha⟩
      rcases hx.2.2 with ⟨b, hb⟩
      rw [ha, hb, Nat.mul_div_cancel_left a hp, Nat.mul_div_cancel_left b hp]
      have hmul : p * (a + b) = p * q := by rw [mul_add, ← ha, ← hb, hx.1]
      exact Nat.eq_of_mul_eq_mul_left hp hmul
    · intro x hx y hy heq
      simp only [Finset.mem_filter] at hx hy
      simp only [Prod.mk.injEq] at heq
      have hx1 := Nat.mul_div_cancel' hx.2.1
      have hx2 := Nat.mul_div_cancel' hx.2.2
      have hy1 := Nat.mul_div_cancel' hy.2.1
      have hy2 := Nat.mul_div_cancel' hy.2.2
      exact Prod.ext (by rw [← hx1, ← hy1, heq.1]) (by rw [← hx2, ← hy2, heq.2])
    · intro y hy
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
      refine ⟨(p * y.1, p * y.2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
        exact ⟨by rw [← mul_add, hy], dvd_mul_right p y.1, dvd_mul_right p y.2⟩
      · simp [Nat.mul_div_cancel_left _ hp]
    · intro x hx
      have h1 := (Finset.mem_filter.mp hx).2.1
      have h2 := (Finset.mem_filter.mp hx).2.2
      simp [coeff_expandP, h1, h2]
  · rw [if_neg hpn, PowerSeries.coeff_mul]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_expandP, coeff_expandP]
    by_cases h1 : p ∣ x.1
    · have h2 : ¬ p ∣ x.2 := fun h2 => hpn (by rw [← hx]; exact dvd_add h1 h2)
      simp [h2]
    · simp [h1]

private lemma expandP_one (p : ℕ) (hp : 0 < p) : expandP p 1 = 1 := by
  ext n
  rw [coeff_expandP]
  cases n with
  | zero => simp
  | succ n =>
    have hrhs : PowerSeries.coeff (n + 1) (1 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]
    rw [hrhs]
    split_ifs with h
    · rw [PowerSeries.coeff_one, if_neg]
      rcases h with ⟨q, hq⟩
      intro h0
      rw [hq, Nat.mul_div_cancel_left q hp] at h0
      rw [h0, mul_zero] at hq
      omega
    · rfl

private lemma expandP_pow (p : ℕ) (hp : 0 < p) (g : PowerSeries ℚ) (k : ℕ) :
    expandP p (g ^ k) = (expandP p g) ^ k := by
  induction k with
  | zero => simp [expandP_one p hp]
  | succ k ih => rw [pow_succ, pow_succ, expandP_mul p hp, ih]

private lemma derivative_expandP (p : ℕ) (hp : 0 < p) (g : PowerSeries ℚ) :
    PowerSeries.derivative ℚ (expandP p g) =
      PowerSeries.C (p : ℚ) * PowerSeries.X ^ (p - 1) * expandP p (PowerSeries.derivative ℚ g) := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_expandP]
  have hrhs : PowerSeries.coeff n
      (PowerSeries.C (p : ℚ) * PowerSeries.X ^ (p - 1) * expandP p (PowerSeries.derivative ℚ g)) =
      if p - 1 ≤ n then
        (p : ℚ) * PowerSeries.coeff (n - (p - 1)) (expandP p (PowerSeries.derivative ℚ g))
      else 0 := by
    rw [mul_assoc, PowerSeries.coeff_C_mul]
    by_cases hle : p - 1 ≤ n
    · rw [if_pos hle]
      congr 1
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
      rw [PowerSeries.coeff_X_pow_mul, Nat.add_sub_cancel]
    · rw [if_neg hle]
      have hlt : n < p - 1 := by omega
      have h0 : PowerSeries.coeff n (PowerSeries.X ^ (p - 1) * expandP p (PowerSeries.derivative ℚ g)) = 0 := by
        rw [PowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [PowerSeries.coeff_X_pow]
        have hne : x.1 ≠ p - 1 := by omega
        simp [hne]
      rw [h0, mul_zero]
  rw [hrhs]
  by_cases hdvd : p ∣ n + 1
  · rw [if_pos hdvd]
    rcases hdvd with ⟨q, hq⟩
    have hq_pos : 1 ≤ q := by
      by_contra h0
      have : q = 0 := by omega
      rw [this, mul_zero] at hq; omega
    have hle : p - 1 ≤ n := by
      have : p * 1 ≤ p * q := Nat.mul_le_mul_left p hq_pos
      omega
    rw [if_pos hle, coeff_expandP]
    have hsub : n - (p - 1) = p * (q - 1) := by
      cases q with
      | zero => omega
      | succ q' => simp only [Nat.add_sub_cancel]; rw [mul_add, mul_one] at hq; omega
    rw [hsub, if_pos (dvd_mul_right p (q - 1)), Nat.mul_div_cancel_left (q - 1) hp,
      PowerSeries.coeff_derivative]
    have hq_div : (n + 1) / p = q := by rw [hq, Nat.mul_div_cancel_left q hp]
    have hq1 : q - 1 + 1 = q := by omega
    rw [hq_div, hq1]
    have hnq : ((n : ℚ) + 1) = (p : ℚ) * (q : ℚ) := by
      have : (n + 1 : ℕ) = p * q := hq
      exact_mod_cast this
    have hqm : (((q - 1 : ℕ) : ℚ) + 1) = (q : ℚ) := by
      exact_mod_cast hq1
    rw [hnq, hqm]
    ring
  · rw [if_neg hdvd, zero_mul]
    by_cases hle : p - 1 ≤ n
    · rw [if_pos hle, coeff_expandP]
      have hndvd : ¬ p ∣ n - (p - 1) := by
        intro h
        apply hdvd
        have heq : n + 1 = (n - (p - 1)) + p := by omega
        rw [heq]
        exact dvd_add h (dvd_refl p)
      rw [if_neg hndvd, mul_zero]
    · rw [if_neg hle]

private lemma coeff_pow_eq_zero_of_lt {g : PowerSeries ℚ} (hg0 : PowerSeries.constantCoeff g = 0) :
    ∀ (j k : ℕ), k < j → PowerSeries.coeff k (g ^ j) = 0 := by
  intro j
  induction j with
  | zero => intro k hk; omega
  | succ j ih =>
    intro k hk
    rw [pow_succ, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hx2 : x.2 = 0
    · rw [hx2, PowerSeries.coeff_zero_eq_constantCoeff, hg0, mul_zero]
    · have hlt : x.1 < j := by omega
      rw [ih x.1 hlt, zero_mul]

private lemma coeff_expPoly_deriv {g : PowerSeries ℚ} (hg0 : PowerSeries.constantCoeff g = 0)
    (N : ℕ) :
    let E : PowerSeries ℚ :=
      ∑ j ∈ Finset.range (N + 1), PowerSeries.C (1 / (j.factorial : ℚ)) * g ^ j
    ∀ k : ℕ, k < N →
      PowerSeries.coeff k (PowerSeries.derivative ℚ E) =
        PowerSeries.coeff k (E * PowerSeries.derivative ℚ g) := by
  intro E k hk
  have hderivE : PowerSeries.derivative ℚ E =
      (∑ j ∈ Finset.range N, PowerSeries.C (1 / (j.factorial : ℚ)) * g ^ j) *
        PowerSeries.derivative ℚ g := by
    simp only [E, map_sum, Finset.sum_mul]
    rw [Finset.sum_range_succ']
    have h0 : PowerSeries.derivative ℚ (PowerSeries.C (1 / ((0 : ℕ).factorial : ℚ)) * g ^ 0) = 0 := by
      simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hC : PowerSeries.derivative ℚ (PowerSeries.C (1 / ((j + 1).factorial : ℚ))) = 0 := by
      simp
    rw [Derivation.leibniz, hC, smul_zero, add_zero, smul_eq_mul, PowerSeries.derivative_pow]
    simp only [Nat.add_sub_cancel]
    have hfac : (((j + 1).factorial : ℕ) : ℚ) = ((j + 1 : ℕ) : ℚ) * (j.factorial : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hcoeff_eq : PowerSeries.C (1 / (((j + 1).factorial : ℕ) : ℚ)) * (((j + 1 : ℕ) : PowerSeries ℚ)) =
        PowerSeries.C (1 / (j.factorial : ℚ)) := by
      rw [← map_natCast PowerSeries.C (j + 1), ← map_mul]
      congr 1
      rw [hfac]
      have hj1 : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hjf : (j.factorial : ℚ) ≠ 0 := by positivity
      field_simp
    calc PowerSeries.C (1 / (((j + 1).factorial : ℕ) : ℚ)) *
            (((j + 1 : ℕ) : PowerSeries ℚ) * g ^ j * PowerSeries.derivative ℚ g)
        = (PowerSeries.C (1 / (((j + 1).factorial : ℕ) : ℚ)) * ((j + 1 : ℕ) : PowerSeries ℚ)) *
            g ^ j * PowerSeries.derivative ℚ g := by ring
      _ = PowerSeries.C (1 / (j.factorial : ℚ)) * g ^ j * PowerSeries.derivative ℚ g := by
            rw [hcoeff_eq]
  rw [hderivE]
  have hdiff : E = (∑ j ∈ Finset.range N, PowerSeries.C (1 / (j.factorial : ℚ)) * g ^ j) +
      PowerSeries.C (1 / (N.factorial : ℚ)) * g ^ N := Finset.sum_range_succ _ N
  rw [hdiff, add_mul, map_add]
  have hlast : PowerSeries.coeff k
      (PowerSeries.C (1 / (N.factorial : ℚ)) * g ^ N * PowerSeries.derivative ℚ g) = 0 := by
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul]
    have hsum0 : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k,
        PowerSeries.coeff x.1 (g ^ N) * PowerSeries.coeff x.2 (PowerSeries.derivative ℚ g) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [coeff_pow_eq_zero_of_lt hg0 N x.1 (by omega), zero_mul]
    rw [hsum0, mul_zero]
  rw [hlast, add_zero]

/-! ### Part 4: Master supercongruence theorem for `(1 - x)^A (1 + x)^B` -/

private lemma pDiv_coeff_pow_of_int {p : ℕ} (hp : p.Prime) (f : PowerSeries ℤ)
    (K N : ℕ) (hN : 1 ≤ N) (s : ℕ) (hK : p ^ s ∣ K) :
    pDiv p (s - padicValNat p N) (PowerSeries.coeff N ((PowerSeries.map (Int.castRingHom ℚ) f) ^ K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmap : PowerSeries.coeff N ((PowerSeries.map (Int.castRingHom ℚ) f) ^ K) =
      ((PowerSeries.coeff N (f ^ K) : ℤ) : ℚ) := by
    rw [← map_pow, PowerSeries.coeff_map]; rfl
  rw [hmap]
  by_cases hs : padicValNat p N ≤ s
  · have hderiv : PowerSeries.coeff (N - 1) (PowerSeries.derivative ℤ (f ^ K)) =
        (N : ℤ) * PowerSeries.coeff N (f ^ K) := by
      rw [PowerSeries.coeff_derivative]
      have hN1 : N - 1 + 1 = N := by omega
      rw [hN1]
      have hcast : (((N - 1 : ℕ) : ℤ) + 1) = (N : ℤ) := by exact_mod_cast hN1
      rw [hcast, mul_comm]
    have hderiv2 : PowerSeries.derivative ℤ (f ^ K) =
        (K : PowerSeries ℤ) * f ^ (K - 1) * PowerSeries.derivative ℤ f :=
      PowerSeries.derivative_pow f K
    have hdvd_prod : (p : ℤ) ^ s ∣ (N : ℤ) * PowerSeries.coeff N (f ^ K) := by
      rw [← hderiv, hderiv2, mul_assoc, ← map_natCast PowerSeries.C K, PowerSeries.coeff_C_mul]
      rcases hK with ⟨u, hu⟩
      refine ⟨(u : ℤ) * PowerSeries.coeff (N - 1) (f ^ (K - 1) * PowerSeries.derivative ℤ f), ?_⟩
      have hK_z : (K : ℤ) = (p : ℤ) ^ s * (u : ℤ) := by exact_mod_cast hu
      rw [hK_z]; ring
    have hq_div : pDiv p s (((N : ℤ) * PowerSeries.coeff N (f ^ K) : ℤ) : ℚ) :=
      pDiv_of_int_dvd p s hp _ hdvd_prod
    have hdiv := pDiv_div_nat hp (by omega : N ≠ 0) hq_div hs
    have hsimp : (((N : ℤ) * PowerSeries.coeff N (f ^ K) : ℤ) : ℚ) / (N : ℚ) =
        ((PowerSeries.coeff N (f ^ K) : ℤ) : ℚ) := by
      push_cast
      have hN0 : (N : ℚ) ≠ 0 := by positivity
      field_simp
    rw [hsimp] at hdiv
    exact hdiv
  · have h0 : s - padicValNat p N = 0 := by omega
    rw [h0]
    exact pDiv_of_int p hp _

private lemma pDiv_psi_sq_coeff (A B : ℤ) {p t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ht : 1 ≤ t) :
    let q : ℕ → ℤ := fun k => -(A + B * (-1 : ℤ) ^ (k + 1))
    let Ψ : PowerSeries ℚ :=
      PowerSeries.mk fun k => if k = 0 ∨ p ∣ k then 0 else (q (k - 1) : ℚ) / (k : ℚ)
    pDiv p (padicValNat p t + 1) (PowerSeries.coeff (p * t) (Ψ ^ 2)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro q Ψ
  set s := padicValNat p t
  let M : ℕ := p * t
  let S := (Finset.Ico 1 M).filter (fun a => ¬ p ∣ a)
  have hcoeff : PowerSeries.coeff M (Ψ ^ 2) =
      ∑ a ∈ S, ((q (a - 1) * q (M - a - 1) : ℤ) : ℚ) *
        ((1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ))) := by
    rw [sq, PowerSeries.coeff_mul]
    have hfilt :
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal M,
          PowerSeries.coeff x.1 Ψ * PowerSeries.coeff x.2 Ψ =
        ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal M).filter (fun x => x.1 ∈ S),
          PowerSeries.coeff x.1 Ψ * PowerSeries.coeff x.2 Ψ := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro x hx hxnot
      rw [Finset.mem_filter, not_and] at hxnot
      have hnotS : x.1 ∉ S := hxnot hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      simp only [S, Finset.mem_filter, Finset.mem_Ico, not_and, not_not] at hnotS
      by_cases h1 : x.1 = 0
      · simp [Ψ, h1]
      · by_cases h2 : x.1 < M
        · have hp1 : p ∣ x.1 := hnotS ⟨by omega, h2⟩
          simp [Ψ, hp1]
        · have hx2 : x.2 = 0 := by omega
          simp [Ψ, hx2]
    rw [hfilt]
    refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy heq
      have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.mp hx).1
      have h2 := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.mp hy).1
      exact Prod.ext heq (by omega)
    · intro a ha
      have ha_lt : a < M := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).2
      refine ⟨(a, M - a), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
      exact ⟨by omega, ha⟩
    · intro x hx
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.mp hx).1
      have haS := (Finset.mem_filter.mp hx).2
      have hax : x.2 = M - x.1 := by omega
      rw [hax]
      simp only [S, Finset.mem_filter, Finset.mem_Ico] at haS
      have hne1 : x.1 ≠ 0 := by omega
      have hne2 : M - x.1 ≠ 0 := by omega
      have hndvd2 : ¬ p ∣ M - x.1 := by
        intro hdiv
        have hMp : p ∣ M := dvd_mul_right p t
        have : p ∣ x.1 := (Nat.dvd_add_left hdiv).mp (by rw [Nat.add_sub_of_le (le_of_lt haS.1.2)]; exact hMp)
        exact haS.2 this
      simp only [Ψ, PowerSeries.coeff_mk, hne1, haS.2, hne2, hndvd2, or_self, ↓reduceIte]
      push_cast
      ring
  rw [hcoeff]
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  let cE : ℤ := -(A + B)
  let cO : ℤ := -(A - B)
  have hq_val : ∀ k : ℕ, 1 ≤ k → q (k - 1) = if Even k then cE else cO := by
    intro k hk
    have hk1 : k - 1 + 1 = k := by omega
    simp only [q, hk1, cE, cO]
    split_ifs with he
    · rw [Even.neg_one_pow he]; ring
    · rw [Odd.neg_one_pow (Nat.not_even_iff_odd.mp he)]; ring
  rcases Nat.even_or_odd t with ⟨t', ht'⟩ | ht_odd
  · -- t = 2 * t' is even: split S into even a and odd a!
    have ht'1 : 1 ≤ t' := by omega
    have hM2 : M = 2 * (p * t') := by simp only [M, ht']; ring
    have hs_eq : padicValNat p t' = s := by
      have h2t : t = 2 * t' := by omega
      have hndvd2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
      have h2ne : (2 : ℕ) ≠ 0 := by norm_num
      have ht'ne : t' ≠ 0 := by omega
      have hmul : padicValNat p (2 * t') = padicValNat p 2 + padicValNat p t' :=
        padicValNat.mul h2ne ht'ne
      rw [padicValNat.eq_zero_of_not_dvd hndvd2, zero_add] at hmul
      simp only [s, h2t, hmul]
    let Seven := S.filter (fun a => Even a)
    let Sodd := S.filter (fun a => ¬ Even a)
    have hsplit :
        ∑ a ∈ S, ((q (a - 1) * q (M - a - 1) : ℤ) : ℚ) *
          ((1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ))) =
        ((cE * cE : ℤ) : ℚ) *
          (∑ a ∈ Seven, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ))) +
        ((cO * cO : ℤ) : ℚ) *
          (∑ a ∈ Sodd, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ))) := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun a => Even a), Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun a ha => ?_
        have haS := (Finset.mem_filter.mp ha).1
        have haE : Even a := (Finset.mem_filter.mp ha).2
        have ha_b := Finset.mem_Ico.mp (Finset.mem_filter.mp haS).1
        have hmaE : Even (M - a) := by
          rcases haE with ⟨r, hr⟩
          refine ⟨p * t' - r, ?_⟩
          omega
        rw [hq_val a ha_b.1, hq_val (M - a) (by omega), if_pos haE, if_pos hmaE]
      · refine Finset.sum_congr rfl fun a ha => ?_
        have haS := (Finset.mem_filter.mp ha).1
        have haO : ¬ Even a := (Finset.mem_filter.mp ha).2
        have ha_b := Finset.mem_Ico.mp (Finset.mem_filter.mp haS).1
        have hmaO : ¬ Even (M - a) := by
          intro hmaE
          rcases hmaE with ⟨r, hr⟩
          apply haO
          refine ⟨p * t' - r, ?_⟩
          omega
        rw [hq_val a ha_b.1, hq_val (M - a) (by omega), if_neg haO, if_neg hmaO]
    rw [hsplit]
    have heven_eq :
        ∑ a ∈ Seven, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ)) =
        (1 / 4 : ℚ) *
          ∑ a' ∈ (Finset.Ico 1 (p * t')).filter (fun a' => ¬ p ∣ a'),
            (1 : ℚ) / ((a' : ℚ) * ((p * t' - a' : ℕ) : ℚ)) := by
      rw [Finset.mul_sum]
      symm
      refine Finset.sum_bij (fun a' _ => 2 * a') ?_ ?_ ?_ ?_
      · intro a' ha'
        simp only [Finset.mem_filter, Finset.mem_Ico] at ha'
        simp only [Seven, S, Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, ⟨a', by omega⟩⟩
        intro hdiv
        rcases hp.dvd_mul.mp hdiv with h2 | ha''
        · have := Nat.le_of_dvd (by norm_num) h2; omega
        · exact ha'.2 ha''
      · intro a₁ _ a₂ _ heq; omega
      · intro a ha
        simp only [Seven, S, Finset.mem_filter, Finset.mem_Ico] at ha
        rcases ha.2 with ⟨a', rfl⟩
        refine ⟨a', ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        intro hdiv
        have h2a : p ∣ a' + a' := by rw [show a' + a' = 2 * a' by omega]; exact dvd_mul_of_dvd_right hdiv 2
        exact ha.1.2 h2a
      · intro a' ha'
        have ha'_lt : a' < p * t' := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha').1).2
        have hsub : M - 2 * a' = 2 * (p * t' - a') := by omega
        rw [hsub]
        push_cast
        ring
    have hdiv_all : pDiv p (s + 1) (∑ a ∈ S, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ))) :=
      pDiv_sum_inv_mul hp hp5 ht
    have hdiv_even : pDiv p (s + 1) (∑ a ∈ Seven, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ))) := by
      rw [heven_eq]
      have hbase := pDiv_sum_inv_mul hp hp5 ht'1
      rw [hs_eq] at hbase
      have hquarter : pDiv p 0 (1 / 4 : ℚ) := by
        refine ⟨1, 4, by norm_num, ?_, by norm_num⟩
        intro h
        have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using pDiv_mul hp hquarter hbase
    have hodd_eq :
        ∑ a ∈ Sodd, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ)) =
        (∑ a ∈ S, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ))) -
        (∑ a ∈ Seven, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ))) := by
      have htot := Finset.sum_filter_add_sum_filter_not S (fun a => Even a)
        (f := fun a => (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ)))
      linarith
    have hdiv_odd : pDiv p (s + 1) (∑ a ∈ Sodd, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ))) := by
      rw [hodd_eq]
      exact pDiv_sub hp hdiv_all hdiv_even
    exact pDiv_add hp
      (by simpa using pDiv_mul hp (pDiv_of_int p hp (cE * cE)) hdiv_even)
      (by simpa using pDiv_mul hp (pDiv_of_int p hp (cO * cO)) hdiv_odd)
  · -- t is odd: M = p * t is odd, so q(a-1) * q(M-a-1) = cE * cO for every a ∈ S!
    have hM_odd : Odd M := hp_odd.mul ht_odd
    have hconst :
        ∑ a ∈ S, ((q (a - 1) * q (M - a - 1) : ℤ) : ℚ) *
          ((1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ))) =
        ((cE * cO : ℤ) : ℚ) *
          ∑ a ∈ S, (1 : ℚ) / ((a : ℚ) * ((M - a : ℕ) : ℚ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha_b := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
      rw [hq_val a ha_b.1, hq_val (M - a) (by omega)]
      by_cases haE : Even a
      · have hmaO : ¬ Even (M - a) := by
          intro hmaE
          have hME : Even M := by
            rw [← Nat.add_sub_of_le (le_of_lt ha_b.2)]
            exact haE.add hmaE
          exact (Nat.not_even_iff_odd.mpr hM_odd) hME
        rw [if_pos haE, if_neg hmaO]
      · have hmaE : Even (M - a) := by
          rcases Nat.not_even_iff_odd.mp haE with ⟨r, hr⟩
          rcases hM_odd with ⟨u, hu⟩
          exact ⟨u - r, by omega⟩
        rw [if_neg haE, if_pos hmaE]
        push_cast; ring
    rw [hconst]
    simpa using pDiv_mul hp (pDiv_of_int p hp (cE * cO)) (pDiv_sum_inv_mul hp hp5 ht)

theorem supercongruence_1sub_1add
    (A B : ℤ) (D : ℕ) (hD : 1 ≤ D)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (f : PowerSeries ℤ)
    (hf0 : PowerSeries.constantCoeff f = 1)
    (hf_log : PowerSeries.derivative ℚ (PowerSeries.map (Int.castRingHom ℚ) f) *
      (1 - PowerSeries.X ^ 2) =
      PowerSeries.map (Int.castRingHom ℚ) f *
      (PowerSeries.C (B - A : ℚ) - PowerSeries.C (A + B : ℚ) * PowerSeries.X)) :
    ((p : ℤ) ^ (3 * r) ∣
      PowerSeries.coeff (D * (m * p ^ r)) (f ^ (m * p ^ r)) -
      PowerSeries.coeff (D * (m * p ^ (r - 1))) (f ^ (m * p ^ (r - 1)))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let fq : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) f
  let q : ℕ → ℤ := fun k => -(A + B * (-1 : ℤ) ^ (k + 1))
  let Q : PowerSeries ℚ := PowerSeries.mk fun k => (q k : ℚ)
  let Ψ : PowerSeries ℚ :=
    PowerSeries.mk fun k => if k = 0 ∨ p ∣ k then 0 else (q (k - 1) : ℚ) / (k : ℚ)
  have hQ_mul : Q * (1 - PowerSeries.X ^ 2) =
      PowerSeries.C (B - A : ℚ) - PowerSeries.C (A + B : ℚ) * PowerSeries.X := by
    ext k
    rw [mul_sub, mul_one, map_sub, map_sub, PowerSeries.coeff_C, PowerSeries.coeff_C_mul]
    cases k with
    | zero =>
      simp [Q, q]
      ring
    | succ k' =>
      cases k' with
      | zero =>
        have h0 : PowerSeries.coeff 1 (Q * PowerSeries.X ^ 2) = 0 := by
          rw [mul_comm, PowerSeries.coeff_mul]
          refine Finset.sum_eq_zero fun x hx => ?_
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
          rw [PowerSeries.coeff_X_pow]
          have : x.1 ≠ 2 := by omega
          simp [this]
        rw [h0]
        simp [Q, q]
      | succ k'' =>
        have h2 : PowerSeries.coeff (k'' + 1 + 1) (Q * PowerSeries.X ^ 2) = PowerSeries.coeff k'' Q := by
          rw [show k'' + 1 + 1 = k'' + 2 by rfl, mul_comm, PowerSeries.coeff_X_pow_mul]
        have hX0 : PowerSeries.coeff (k'' + 1 + 1) (PowerSeries.X : PowerSeries ℚ) = 0 := by
          rw [PowerSeries.coeff_X]
          split_ifs with h
          · omega
          · rfl
        rw [h2, hX0, mul_zero, if_neg (by omega), sub_zero]
        simp only [Q, PowerSeries.coeff_mk, q]
        have hpow : (-1 : ℤ) ^ (k'' + 1 + 1 + 1) = (-1 : ℤ) ^ (k'' + 1) := by
          rw [show k'' + 1 + 1 + 1 = (k'' + 1) + 2 by omega, pow_add]; ring
        rw [hpow]; ring
  have hunit_1subX2 : IsUnit (1 - PowerSeries.X ^ 2 : PowerSeries ℚ) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)
  have hfq_deriv : PowerSeries.derivative ℚ fq = fq * Q := by
    have h1 : PowerSeries.derivative ℚ fq * (1 - PowerSeries.X ^ 2) =
        (fq * Q) * (1 - PowerSeries.X ^ 2) := by
      rw [mul_assoc, hQ_mul]
      exact hf_log
    exact hunit_1subX2.mul_right_cancel h1
  -- Key decomposition: Q = X^(p-1) * expandP p Q + derivative ℚ Ψ
  have hQ_decomp : Q = PowerSeries.X ^ (p - 1) * expandP p Q + PowerSeries.derivative ℚ Ψ := by
    ext k
    rw [map_add, PowerSeries.coeff_derivative]
    have hxp : PowerSeries.coeff k (PowerSeries.X ^ (p - 1) * expandP p Q) =
        if p - 1 ≤ k then PowerSeries.coeff (k - (p - 1)) (expandP p Q) else 0 := by
      by_cases hle : p - 1 ≤ k
      · rw [if_pos hle]
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
        rw [PowerSeries.coeff_X_pow_mul, Nat.add_sub_cancel]
      · rw [if_neg hle, PowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [PowerSeries.coeff_X_pow]
        have : x.1 ≠ p - 1 := by omega
        simp [this]
    rw [hxp]
    have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
    by_cases hdvd : p ∣ k + 1
    · have hpsi0 : PowerSeries.coeff (k + 1) Ψ = 0 := by simp [Ψ, hdvd]
      rw [hpsi0, zero_mul, add_zero]
      rcases hdvd with ⟨u, hu⟩
      have hu1 : 1 ≤ u := by
        by_contra h0
        have : u = 0 := by omega
        rw [this, mul_zero] at hu; omega
      have hle : p - 1 ≤ k := by
        have : p * 1 ≤ p * u := Nat.mul_le_mul_left p hu1
        omega
      rw [if_pos hle, coeff_expandP]
      have hsub : k - (p - 1) = p * (u - 1) := by
        cases u with
        | zero => omega
        | succ u' => simp only [Nat.add_sub_cancel]; rw [mul_add, mul_one] at hu; omega
      rw [hsub, if_pos (dvd_mul_right p (u - 1)), Nat.mul_div_cancel_left (u - 1) hp.pos]
      simp only [Q, PowerSeries.coeff_mk, q]
      have hpow : (-1 : ℤ) ^ (k + 1) = (-1 : ℤ) ^ (u - 1 + 1) := by
        have hu' : u - 1 + 1 = u := by omega
        rw [hu, hu', pow_mul, Odd.neg_one_pow hp_odd]
      rw [hpow]
    · have hxp0 : (if p - 1 ≤ k then PowerSeries.coeff (k - (p - 1)) (expandP p Q) else 0) = 0 := by
        split_ifs with hle
        · rw [coeff_expandP, if_neg]
          intro h
          apply hdvd
          have : k + 1 = (k - (p - 1)) + p := by omega
          rw [this]; exact dvd_add h (dvd_refl p)
        · rfl
      rw [hxp0, zero_add]
      have hne : k + 1 ≠ 0 := Nat.succ_ne_zero k
      simp only [Ψ, Q, PowerSeries.coeff_mk, hne, hdvd, or_self, ↓reduceIte, Nat.add_sub_cancel]
      have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
  -- Set up U = fq^(m * p^r) and V = (expandP p fq)^(m * p^(r-1)) * E_N
  let K : ℕ := m * p ^ r
  let K' : ℕ := m * p ^ (r - 1)
  have hK_eq : K = K' * p := by
    simp only [K, K']
    have hr1 : r = (r - 1) + 1 := by omega
    conv_lhs => rw [hr1, pow_succ]
    ring
  let N : ℕ := D * K
  let g : PowerSeries ℚ := PowerSeries.C (K : ℚ) * Ψ
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [g, Ψ]
  let E : PowerSeries ℚ :=
    ∑ j ∈ Finset.range (N + 1), PowerSeries.C (1 / (j.factorial : ℚ)) * g ^ j
  let U : PowerSeries ℚ := fq ^ K
  let V : PowerSeries ℚ := (expandP p fq) ^ K' * E
  have hU_deriv : PowerSeries.derivative ℚ U = PowerSeries.C (K : ℚ) * Q * U := by
    simp only [U]
    rw [PowerSeries.derivative_pow, hfq_deriv]
    have hKpos : 1 ≤ K := Nat.mul_pos hm (pow_pos hp.pos r)
    have hpow : fq ^ (K - 1) * fq = fq ^ K := by
      rw [← pow_succ, Nat.sub_add_cancel hKpos]
    rw [← map_natCast PowerSeries.C K]
    calc PowerSeries.C (K : ℚ) * fq ^ (K - 1) * (fq * Q)
        = PowerSeries.C (K : ℚ) * Q * (fq ^ (K - 1) * fq) := by ring
      _ = PowerSeries.C (K : ℚ) * Q * fq ^ K := by rw [hpow]
  have hV_deriv : ∀ k : ℕ, k < N →
      PowerSeries.coeff k (PowerSeries.derivative ℚ V) =
        PowerSeries.coeff k (PowerSeries.C (K : ℚ) * Q * V) := by
    intro k hk
    have hfp_deriv : PowerSeries.derivative ℚ ((expandP p fq) ^ K') =
        PowerSeries.C (K : ℚ) * (PowerSeries.X ^ (p - 1) * expandP p Q) * (expandP p fq) ^ K' := by
      rw [PowerSeries.derivative_pow, derivative_expandP p hp.pos fq, hfq_deriv,
        expandP_mul p hp.pos]
      have hK'pos : 1 ≤ K' := Nat.mul_pos hm (pow_pos hp.pos (r - 1))
      have hpow : (expandP p fq) ^ (K' - 1) * expandP p fq = (expandP p fq) ^ K' := by
        rw [← pow_succ, Nat.sub_add_cancel hK'pos]
      have hCK : PowerSeries.C (K : ℚ) = (K' : PowerSeries ℚ) * PowerSeries.C (p : ℚ) := by
        rw [← map_natCast PowerSeries.C K', ← map_mul]
        congr 1
        exact_mod_cast hK_eq
      rw [hCK]
      calc (K' : PowerSeries ℚ) * (expandP p fq) ^ (K' - 1) *
            (PowerSeries.C (p : ℚ) * PowerSeries.X ^ (p - 1) * (expandP p fq * expandP p Q))
          = (K' : PowerSeries ℚ) * PowerSeries.C (p : ℚ) *
              (PowerSeries.X ^ (p - 1) * expandP p Q) *
              ((expandP p fq) ^ (K' - 1) * expandP p fq) := by ring
        _ = (K' : PowerSeries ℚ) * PowerSeries.C (p : ℚ) *
              (PowerSeries.X ^ (p - 1) * expandP p Q) * (expandP p fq) ^ K' := by rw [hpow]
    have hV_leib : PowerSeries.derivative ℚ V =
        (expandP p fq) ^ K' * PowerSeries.derivative ℚ E +
        E * PowerSeries.derivative ℚ ((expandP p fq) ^ K') := by
      simp only [V, Derivation.leibniz, smul_eq_mul]
    rw [hV_leib, map_add]
    have hterm1 : PowerSeries.coeff k ((expandP p fq) ^ K' * PowerSeries.derivative ℚ E) =
        PowerSeries.coeff k ((expandP p fq) ^ K' * (E * PowerSeries.derivative ℚ g)) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [coeff_expPoly_deriv hg0 N x.2 (by omega)]
    rw [hterm1, hfp_deriv]
    have hdg : PowerSeries.derivative ℚ g = PowerSeries.C (K : ℚ) * PowerSeries.derivative ℚ Ψ := by
      simp only [g, Derivation.leibniz, smul_eq_mul]
      have hC0 : PowerSeries.derivative ℚ (PowerSeries.C (K : ℚ)) = 0 := by simp
      rw [hC0, mul_zero, add_zero]
    rw [hdg, ← map_add]
    congr 1
    have hcomb : (expandP p fq) ^ K' * (E * (PowerSeries.C (K : ℚ) * PowerSeries.derivative ℚ Ψ)) +
        E * (PowerSeries.C (K : ℚ) * (PowerSeries.X ^ (p - 1) * expandP p Q) * (expandP p fq) ^ K') =
        PowerSeries.C (K : ℚ) * (PowerSeries.X ^ (p - 1) * expandP p Q + PowerSeries.derivative ℚ Ψ) * V := by
      simp only [V]; ring
    rw [hcomb, ← hQ_decomp]
  -- Prove coeff k U = coeff k V for all k ≤ N by strong induction!
  have hU_eq_V : ∀ k : ℕ, k ≤ N → PowerSeries.coeff k U = PowerSeries.coeff k V := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      cases k with
      | zero =>
        have hfq0 : PowerSeries.coeff 0 fq = 1 := by
          rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, hf0, map_one]
        have hfp0 : PowerSeries.coeff 0 (expandP p fq) = 1 := by
          rw [coeff_expandP, if_pos (dvd_zero p), Nat.zero_div, hfq0]
        have hE0 : PowerSeries.coeff 0 E = 1 := by
          simp only [E, map_sum, PowerSeries.coeff_C_mul]
          rw [Finset.sum_eq_single 0]
          · simp
          · intro j _ hj0
            rw [coeff_pow_eq_zero_of_lt hg0 j 0 (Nat.pos_of_ne_zero hj0), mul_zero]
          · intro h0; simp at h0
        have hU0 : PowerSeries.coeff 0 U = 1 := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff]
          simp only [U, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, hfq0, one_pow]
        have hV0 : PowerSeries.coeff 0 V = 1 := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff]
          simp only [V, map_mul, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
            hfp0, one_pow, one_mul, hE0]
        rw [hU0, hV0]
      | succ k' =>
        have hmul_eq : PowerSeries.coeff (k' + 1) U * ((k' : ℚ) + 1) =
            PowerSeries.coeff (k' + 1) V * ((k' : ℚ) + 1) := by
          rw [← PowerSeries.coeff_derivative, ← PowerSeries.coeff_derivative,
            hU_deriv, hV_deriv k' (by omega), PowerSeries.coeff_mul, PowerSeries.coeff_mul]
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
          rw [ih x.2 (by omega) (by omega)]
        have hk1 : ((k' : ℚ) + 1) ≠ 0 := by positivity
        exact mul_right_cancel₀ hk1 hmul_eq
  -- Extract coefficient at N = D * K and split j = 0, 1, 2, ≥ 3!
  have hcoeff_N : PowerSeries.coeff N U =
      ∑ j ∈ Finset.range (N + 1),
        (((K : ℚ) ^ j) / (j.factorial : ℚ)) *
          PowerSeries.coeff N ((expandP p fq) ^ K' * Ψ ^ j) := by
    rw [hU_eq_V N (le_refl N)]
    simp only [V, E, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hgj : g ^ j = PowerSeries.C ((K : ℚ) ^ j) * Ψ ^ j := by
      simp only [g, mul_pow, map_pow]
    rw [hgj]
    have hrearr : (expandP p fq) ^ K' * (PowerSeries.C (1 / (j.factorial : ℚ)) *
        (PowerSeries.C ((K : ℚ) ^ j) * Ψ ^ j)) =
        PowerSeries.C ((K : ℚ) ^ j / (j.factorial : ℚ)) * ((expandP p fq) ^ K' * Ψ ^ j) := by
      rw [← mul_assoc (PowerSeries.C (1 / (j.factorial : ℚ))), ← map_mul]
      have hc : (1 / (j.factorial : ℚ)) * (K : ℚ) ^ j = (K : ℚ) ^ j / (j.factorial : ℚ) := by ring
      rw [hc]; ring
    rw [hrearr, PowerSeries.coeff_C_mul]
  -- Evaluate j = 0 term = a(K')!
  have hterm0 : PowerSeries.coeff N ((expandP p fq) ^ K' * Ψ ^ 0) =
      ((PowerSeries.coeff (D * K') (f ^ K') : ℤ) : ℚ) := by
    rw [pow_zero, mul_one, ← expandP_pow p hp.pos fq K', coeff_expandP]
    have hN_eq : N = p * (D * K') := by simp only [N, hK_eq]; ring
    rw [hN_eq, if_pos (dvd_mul_right p (D * K')), Nat.mul_div_cancel_left (D * K') hp.pos]
    simp only [fq, ← map_pow, PowerSeries.coeff_map]; rfl
  -- Evaluate j = 1 term = 0!
  have hterm1 : PowerSeries.coeff N ((expandP p fq) ^ K' * Ψ ^ 1) = 0 := by
    rw [pow_one, ← expandP_pow p hp.pos fq K', PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_expandP]
    by_cases h1 : p ∣ x.1
    · have hN_dvd : p ∣ N := by
        have : N = p * (D * K') := by simp only [N, hK_eq]; ring
        rw [this]; exact dvd_mul_right p _
      have h2 : p ∣ x.2 := (Nat.dvd_add_right h1).mp (by rw [hx]; exact hN_dvd)
      have hpsi : PowerSeries.coeff x.2 Ψ = 0 := by simp [Ψ, h2]
      rw [hpsi, mul_zero]
    · simp [h1]
  -- Evaluate j = 2 term has pDiv p (3 * r)!
  have hterm2 : pDiv p (3 * r)
      ((((K : ℚ) ^ 2) / ((2 : ℕ).factorial : ℚ)) *
        PowerSeries.coeff N ((expandP p fq) ^ K' * Ψ ^ 2)) := by
    have hK2 : pDiv p (2 * r) (((K : ℚ) ^ 2) / ((2 : ℕ).factorial : ℚ)) := by
      have h2f : ((2 : ℕ).factorial : ℚ) = 2 := by norm_num
      rw [h2f]
      refine ⟨(m : ℤ) ^ 2, 2, by norm_num, fun h => by have := Nat.le_of_dvd (by norm_num) h; omega, ?_⟩
      simp only [K]
      push_cast
      rw [mul_pow, ← pow_mul]
      ring
    have hcoeff2 : pDiv p r (PowerSeries.coeff N ((expandP p fq) ^ K' * Ψ ^ 2)) := by
      rw [← expandP_pow p hp.pos fq K', PowerSeries.coeff_mul]
      refine pDiv_sum hp _ _ fun x hx => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [coeff_expandP]
      by_cases h1 : p ∣ x.1
      · rw [if_pos h1]
        have hN_eq : N = p * (D * K') := by simp only [N, hK_eq]; ring
        have h2 : p ∣ x.2 := (Nat.dvd_add_right h1).mp (by rw [hx, hN_eq]; exact dvd_mul_right p _)
        rcases h2 with ⟨t, ht⟩
        by_cases ht0 : t = 0
        · rw [ht, ht0, mul_zero]
          have h0 : PowerSeries.coeff 0 (Ψ ^ 2) = 0 :=
            coeff_pow_eq_zero_of_lt (by rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [Ψ]) 2 0 (by omega)
          rw [h0, mul_zero]
          exact pDiv_zero p r hp
        · have ht1 : 1 ≤ t := Nat.pos_of_ne_zero ht0
          rw [ht]
          have hpsi2 : pDiv p (padicValNat p t + 1) (PowerSeries.coeff (p * t) (Ψ ^ 2)) :=
            pDiv_psi_sq_coeff A B hp hp5 ht1
          set s := padicValNat p t
          by_cases hsr : r - 1 ≤ s
          · have h1int : pDiv p 0 (PowerSeries.coeff (x.1 / p) (fq ^ K')) := by
              have : PowerSeries.coeff (x.1 / p) (fq ^ K') = ((PowerSeries.coeff (x.1 / p) (f ^ K') : ℤ) : ℚ) := by
                simp only [fq, ← map_pow, PowerSeries.coeff_map]; rfl
              rw [this]; exact pDiv_of_int p hp _
            have hmul := pDiv_mul hp h1int hpsi2
            exact pDiv_mono (by omega) hmul
          · have hs_lt : s < r - 1 := by omega
            have hx1_div : x.1 / p = D * K' - t := by
              rcases h1 with ⟨a, ha⟩
              rw [ha, Nat.mul_div_cancel_left a hp.pos]
              have hmul : p * (a + t) = p * (D * K') := by
                rw [mul_add, ← ha, ← ht, hx, hN_eq]
              have := Nat.eq_of_mul_eq_mul_left hp.pos hmul
              omega
            have hx1_pos : 1 ≤ x.1 / p := by
              rw [hx1_div]
              by_contra h0
              have hle : D * K' ≤ t := by omega
              have hlt : t ≤ D * K' := by
                have : p * t ≤ p * (D * K') := by omega
                exact Nat.le_of_mul_le_mul_left this hp.pos
              have heq : t = D * K' := le_antisymm hlt hle
              have hdvd_t : p ^ (r - 1) ∣ t := by
                rw [heq]; exact dvd_mul_of_dvd_right (dvd_mul_left (p ^ (r - 1)) m) D
              have hge : r - 1 ≤ s := (padicValNat_dvd_iff_le ht0).mp hdvd_t
              omega
            have hval_x1 : padicValNat p (x.1 / p) ≤ s := by
              by_contra hgt
              have hge : s + 1 ≤ padicValNat p (x.1 / p) := by omega
              have hdvd1 : p ^ (s + 1) ∣ x.1 / p :=
                (padicValNat_dvd_iff_le (by omega)).mpr hge
              have hdvd_DK : p ^ (s + 1) ∣ D * K' := by
                have hle : s + 1 ≤ r - 1 := by omega
                have hpow_dvd : p ^ (s + 1) ∣ p ^ (r - 1) := pow_dvd_pow p hle
                exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpow_dvd m) D
              have hsum_eq : x.1 / p + t = D * K' := by omega
              have hdvd_t : p ^ (s + 1) ∣ t :=
                (Nat.dvd_add_right hdvd1).mp (by rw [hsum_eq]; exact hdvd_DK)
              have hle_s : s + 1 ≤ s := (padicValNat_dvd_iff_le ht0).mp hdvd_t
              omega
            have hdiv_f := pDiv_coeff_pow_of_int hp f K' (x.1 / p) hx1_pos (r - 1)
              (dvd_mul_left (p ^ (r - 1)) m)
            have hmul := pDiv_mul hp hdiv_f hpsi2
            exact pDiv_mono (by omega) hmul
      · rw [if_neg h1, zero_mul]
        exact pDiv_zero p r hp
    have hmul := pDiv_mul hp hK2 hcoeff2
    exact pDiv_mono (by omega) hmul
  -- Evaluate j ≥ 3 terms all have pDiv p (3 * r)!
  have hpsi_int : ∀ k : ℕ, pDiv p 0 (PowerSeries.coeff k Ψ) := by
    intro k
    simp only [Ψ, PowerSeries.coeff_mk]
    split_ifs with h
    · exact pDiv_zero p 0 hp
    · push_neg at h
      refine ⟨q (k - 1), k, h.1, h.2, by simp⟩
  have hpsi_pow_int : ∀ (j k : ℕ), pDiv p 0 (PowerSeries.coeff k (Ψ ^ j)) := by
    intro j
    induction j with
    | zero =>
      intro k
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs
      · exact pDiv_of_int p hp 1
      · exact pDiv_zero p 0 hp
    | succ j ih =>
      intro k
      rw [pow_succ, PowerSeries.coeff_mul]
      refine pDiv_sum hp _ _ fun x _ => ?_
      simpa using pDiv_mul hp (ih x.1) (hpsi_int x.2)
  have hterm_ge3 : ∀ j ∈ Finset.range (N + 1), 3 ≤ j →
      pDiv p (3 * r)
        ((((K : ℚ) ^ j) / (j.factorial : ℚ)) *
          PowerSeries.coeff N ((expandP p fq) ^ K' * Ψ ^ j)) := by
    intro j _ hj
    have hcoeff_int : pDiv p 0 (PowerSeries.coeff N ((expandP p fq) ^ K' * Ψ ^ j)) := by
      rw [← expandP_pow p hp.pos fq K', PowerSeries.coeff_mul]
      refine pDiv_sum hp _ _ fun x _ => ?_
      rw [coeff_expandP]
      have h1 : pDiv p 0 (if p ∣ x.1 then PowerSeries.coeff (x.1 / p) (fq ^ K') else 0) := by
        split_ifs
        · have : PowerSeries.coeff (x.1 / p) (fq ^ K') = ((PowerSeries.coeff (x.1 / p) (f ^ K') : ℤ) : ℚ) := by
            simp only [fq, ← map_pow, PowerSeries.coeff_map]; rfl
          rw [this]; exact pDiv_of_int p hp _
        · exact pDiv_zero p 0 hp
      simpa using pDiv_mul hp h1 (hpsi_pow_int j x.2)
    have hfac := pDiv_pow_div_factorial hp hp5 hr hj m
    have hK_cast : (K : ℚ) = (m : ℚ) * (p : ℚ) ^ r := by simp [K]
    rw [hK_cast]
    simpa using pDiv_mul hp hfac hcoeff_int
  -- Combine all j = 0, 1, 2, ≥ 3!
  have hN_ge3 : 3 ≤ N := by
    have h1 : 1 * (1 * 5) ≤ D * (m * p ^ r) := by
      have hp1 : 5 ≤ p ^ r := le_trans hp5 (Nat.le_self_pow (by omega) p)
      exact Nat.mul_le_mul hD (Nat.mul_le_mul hm hp1)
    dsimp only [N, K]
    omega
  have hdiff_q : ((PowerSeries.coeff (D * K) (f ^ K) - PowerSeries.coeff (D * K') (f ^ K') : ℤ) : ℚ) =
      ∑ j ∈ Finset.Icc 2 N,
        (((K : ℚ) ^ j) / (j.factorial : ℚ)) *
          PowerSeries.coeff N ((expandP p fq) ^ K' * Ψ ^ j) := by
    have hU_int : PowerSeries.coeff N U = ((PowerSeries.coeff (D * K) (f ^ K) : ℤ) : ℚ) := by
      simp only [U, N, fq, ← map_pow, PowerSeries.coeff_map]; rfl
    have hrange : Finset.range (N + 1) = insert 0 (insert 1 (Finset.Icc 2 N)) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hU_int, hrange, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      hterm0, hterm1] at hcoeff_N
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
      mul_zero, zero_add] at hcoeff_N
    push_cast
    linarith
  have hpdiv_diff : pDiv p (3 * r)
      ((PowerSeries.coeff (D * K) (f ^ K) - PowerSeries.coeff (D * K') (f ^ K') : ℤ) : ℚ) := by
    rw [hdiff_q]
    refine pDiv_sum hp _ _ fun j hj => ?_
    have hj_b := Finset.mem_Icc.mp hj
    by_cases hj2 : j = 2
    · subst hj2; exact hterm2
    · exact hterm_ge3 j (Finset.mem_range.mpr (by omega)) (by omega)
  exact pDiv_int_dvd hp _ hpdiv_diff

/-! ### Part 5: Instantiation to OEIS A363418 -/

theorem main_proof :
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ m r : ℕ, 1 ≤ m → 1 ≤ r →
      ((p : ℤ) ^ (3 * r) ∣
        OMA.S_oeis_a363418.T n (m * p ^ r) - OMA.S_oeis_a363418.T n (m * p ^ (r - 1))) := by
  intro n hn p hp hp5 m r hm hr
  let f : PowerSeries ℤ := (1 + PowerSeries.X) * PowerSeries.mk 1
  have hf0 : PowerSeries.constantCoeff f = 1 := by
    simp [f]
  have h1sub : (1 - PowerSeries.X : PowerSeries ℚ) *
      PowerSeries.map (Int.castRingHom ℚ) f = 1 + PowerSeries.X := by
    have hmk : PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk (1 : ℕ → ℤ)) =
        PowerSeries.mk (1 : ℕ → ℚ) := by
      ext j; simp
    simp only [f, map_mul, map_add, map_one, PowerSeries.map_X, hmk]
    have hgeom : (1 - PowerSeries.X : PowerSeries ℚ) * PowerSeries.mk (1 : ℕ → ℚ) = 1 := by
      ext j
      rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_one]
      cases j with
      | zero => simp
      | succ j' => simp [PowerSeries.coeff_succ_X_mul]
    have hrearr : (1 - PowerSeries.X : PowerSeries ℚ) *
        ((1 + PowerSeries.X) * PowerSeries.mk (1 : ℕ → ℚ)) =
        (1 + PowerSeries.X) * ((1 - PowerSeries.X) * PowerSeries.mk (1 : ℕ → ℚ)) := by ring
    rw [hrearr, hgeom, mul_one]
  have hf_log : PowerSeries.derivative ℚ (PowerSeries.map (Int.castRingHom ℚ) f) *
      (1 - PowerSeries.X ^ 2) =
      PowerSeries.map (Int.castRingHom ℚ) f *
      (PowerSeries.C ((1 : ℤ) - (-1 : ℤ) : ℚ) - PowerSeries.C ((-1 : ℤ) + (1 : ℤ) : ℚ) * PowerSeries.X) := by
    set fq := PowerSeries.map (Int.castRingHom ℚ) f
    have hderiv := congrArg (PowerSeries.derivative ℚ) h1sub
    simp only [Derivation.leibniz, smul_eq_mul, map_sub, map_add, Derivation.map_one_eq_zero,
      PowerSeries.derivative_X, zero_sub, mul_neg, mul_one, zero_add] at hderiv
    have hmul := congrArg (· * (1 + PowerSeries.X)) hderiv
    have h1 : ((1 - PowerSeries.X) * PowerSeries.derivative ℚ fq + -fq) * (1 + PowerSeries.X) =
        PowerSeries.derivative ℚ fq * (1 - PowerSeries.X ^ 2) - fq * (1 + PowerSeries.X) := by ring
    rw [h1, one_mul] at hmul
    have h2 : PowerSeries.derivative ℚ fq * (1 - PowerSeries.X ^ 2) =
        fq * (1 + PowerSeries.X) + (1 - PowerSeries.X) * fq := by
      have h3 := congrArg (· + fq * (1 + PowerSeries.X)) hmul
      simp only [sub_add_cancel] at h3
      calc PowerSeries.derivative ℚ fq * (1 - PowerSeries.X ^ 2)
          = (1 + PowerSeries.X) + fq * (1 + PowerSeries.X) := h3
        _ = (1 - PowerSeries.X) * fq + fq * (1 + PowerSeries.X) :=
            congrArg (· + fq * (1 + PowerSeries.X)) h1sub.symm
        _ = fq * (1 + PowerSeries.X) + (1 - PowerSeries.X) * fq := by ring
    rw [h2]
    have hc : PowerSeries.C ((1 : ℤ) - (-1 : ℤ) : ℚ) -
        PowerSeries.C ((-1 : ℤ) + (1 : ℤ) : ℚ) * PowerSeries.X = (2 : PowerSeries ℚ) := by
      simp
      ring
    rw [hc]
    ring
  exact supercongruence_1sub_1add (-1) 1 n hn p hp hp5 m r hm hr f hf0 hf_log

end OeisA363418Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a363418.main :=
  OeisA363418Proof.main_proof

