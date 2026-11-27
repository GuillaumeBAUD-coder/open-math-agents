import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
For `p ≡ 1 (mod 4)`, `-1` is a square modulo `p ^ e` for every `e`. Evaluating the Gaussian
product `∏_{k ≤ n} (1 + k i)` at both square roots `±r` modulo `p ^ v_p(n!)` gives
`p ^ v_p(n!) ∣ a(n)`.
-/

namespace OMA.Moll105751

open Finset

private def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((P n).1 - (n + 1 : ℤ) * (P n).2, (P n).2 + (n + 1 : ℤ) * (P n).1)

private lemma prod_eq_P (n : ℕ) :
    (Finset.range (n + 1)).prod (fun k : ℕ => (1 : ℂ) + (k : ℂ) * Complex.I) =
      ((P n).1 : ℂ) + ((P n).2 : ℂ) * Complex.I := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    simp only [P, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add,
      Nat.cast_one]
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination ((P n).2 : ℂ) * ((n : ℂ) + 1) * hI2

private lemma a_eq_P (n : ℕ) : OeisA105751.a n = (P n).2 := by
  unfold OeisA105751.a
  rw [prod_eq_P]
  simp [Int.floor_intCast]

private lemma exists_sq_neg_one_mod (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) (e : ℕ) :
    ∃ r : ℤ, (r ^ 2 + 1) ≡ 0 [ZMOD (p ^ e : ℕ)] := by
  induction e with
  | zero => exact ⟨0, by simp [Int.ModEq]⟩
  | succ e ih =>
    cases e with
    | zero =>
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨x, hx⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by right; exact hmod)
      refine ⟨(x.val : ℤ), ?_⟩
      rw [Int.ModEq, Int.zero_emod]
      have h0 : ((x.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
        push_cast
        rw [ZMod.natCast_zmod_val, hx]
        ring
      have hd : p ∣ x.val ^ 2 + 1 := (ZMod.natCast_eq_zero_iff _ p).mp h0
      exact_mod_cast Int.emod_eq_zero_of_dvd (by exact_mod_cast hd)
    | succ e =>
      obtain ⟨r, hr⟩ := ih
      have hdvd : ((p : ℤ) ^ (e + 1)) ∣ (r ^ 2 + 1) := Int.modEq_zero_iff_dvd.mp hr
      obtain ⟨q, hq⟩ := hdvd
      have hp_ndvd_r : ¬ (p : ℤ) ∣ r := by
        intro hpr
        have hp_dvd1 : (p : ℤ) ∣ r ^ 2 + 1 :=
          dvd_trans (dvd_pow_self (p : ℤ) (by omega)) (⟨q, hq⟩)
        have hp_dvd_sq : (p : ℤ) ∣ r ^ 2 := dvd_trans hpr (dvd_pow_self r (by omega))
        have hp_dvd_one : (p : ℤ) ∣ 1 := (Int.dvd_add_right hp_dvd_sq).mp hp_dvd1
        have hp1 : p = 1 := by
          have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hp_dvd_one
          omega
        exact hp.ne_one hp1
      have hp_ne2 : p ≠ 2 := by omega
      have hcop : IsCoprime (2 * r) (p : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have hp_primeZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
        by_contra hne
        have hd : (p : ℤ) ∣ 2 * r := by
          have h1 : (Nat.gcd (2 * r).natAbs p : ℕ) ∣ p := Nat.gcd_dvd_right _ _
          rcases hp.eq_one_or_self_of_dvd _ h1 with h | h
          · exact absurd h hne
          · have h2 : (p : ℕ) ∣ (2 * r).natAbs := h ▸ Nat.gcd_dvd_left _ _
            exact Int.natCast_dvd.mpr h2
        rcases hp_primeZ.dvd_or_dvd hd with h2 | hr2
        · have : p ∣ 2 := by exact_mod_cast h2
          rcases hp.eq_one_or_self_of_dvd 2 this with h | h <;> omega
        · exact hp_ndvd_r hr2
      obtain ⟨u, v, huv⟩ := hcop
      let t : ℤ := -q * u
      refine ⟨r + (p : ℤ) ^ (e + 1) * t, ?_⟩
      rw [Int.modEq_zero_iff_dvd]
      have hqt : q + 2 * r * t = (p : ℤ) * (q * v) := by
        calc q + 2 * r * t = q * (1 - 2 * r * u) := by dsimp [t]; ring
          _ = q * ((p : ℤ) * v) := by rw [show 1 - 2 * r * u = (p : ℤ) * v by linear_combination huv]
          _ = (p : ℤ) * (q * v) := by ring
      have hexp : (r + (p : ℤ) ^ (e + 1) * t) ^ 2 + 1 =
          (p : ℤ) ^ (e + 1) * (q + 2 * r * t) + (p : ℤ) ^ (2 * e + 2) * t ^ 2 := by
        calc (r + (p : ℤ) ^ (e + 1) * t) ^ 2 + 1
            = (r ^ 2 + 1) + 2 * r * (p : ℤ) ^ (e + 1) * t + ((p : ℤ) ^ (e + 1)) ^ 2 * t ^ 2 := by ring
          _ = (p : ℤ) ^ (e + 1) * q + 2 * r * (p : ℤ) ^ (e + 1) * t + (p : ℤ) ^ (2 * e + 2) * t ^ 2 := by
              rw [hq, ← pow_mul, show (e + 1) * 2 = 2 * e + 2 by ring]
          _ = _ := by ring
      rw [hexp, hqt]
      refine dvd_add ?_ ?_
      · refine ⟨q * v, ?_⟩
        push_cast
        rw [show e + 1 + 1 = (e + 1) + 1 by rfl, pow_succ]
        ring
      · refine ⟨(p : ℤ) ^ e * t ^ 2, ?_⟩
        push_cast
        rw [← mul_assoc, ← pow_add, show e + 1 + 1 + e = 2 * e + 2 by omega]

private lemma P_eval_mod (m : ℤ) (r : ℤ) (hr : r ^ 2 + 1 ≡ 0 [ZMOD m]) (n : ℕ) :
    (P n).1 + (P n).2 * r ≡ ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r) [ZMOD m] := by
  induction n with
  | zero => simp [P, Int.ModEq]
  | succ n ih =>
    rw [Finset.prod_range_succ]
    simp only [P]
    have hr2 : r ^ 2 ≡ -1 [ZMOD m] := by
      have : r ^ 2 + 1 - 1 ≡ 0 - 1 [ZMOD m] := hr.sub_right 1
      simpa using this
    have hstep : ((P n).1 - (n + 1 : ℤ) * (P n).2) + ((P n).2 + (n + 1 : ℤ) * (P n).1) * r ≡
        ((P n).1 + (P n).2 * r) * (1 + (n + 1 : ℤ) * r) [ZMOD m] := by
      have h1 : ((P n).1 + (P n).2 * r) * (1 + (n + 1 : ℤ) * r) =
          (P n).1 + (P n).2 * r + (n + 1 : ℤ) * (P n).1 * r + (n + 1 : ℤ) * (P n).2 * r ^ 2 := by ring
      rw [h1]
      have h2 := hr2.mul_left ((n + 1 : ℤ) * (P n).2)
      have h3 := h2.add_left ((P n).1 + (P n).2 * r + (n + 1 : ℤ) * (P n).1 * r)
      rw [show ((P n).1 - (n + 1 : ℤ) * (P n).2) + ((P n).2 + (n + 1 : ℤ) * (P n).1) * r =
          (P n).1 + (P n).2 * r + (n + 1 : ℤ) * (P n).1 * r + (n + 1 : ℤ) * (P n).2 * (-1) by ring]
      exact h3.symm
    exact hstep.trans (ih.mul_right _)

private lemma card_filter_dvd_ge (p : ℕ) (hp : p.Prime) (r : ℤ) (hpr : ¬ (p : ℤ) ∣ r)
    (n j : ℕ) (hj : 1 ≤ j) :
    n / p ^ j ≤ ((Finset.Icc (1 : ℕ) n).filter (fun k : ℕ => (p : ℤ) ^ j ∣ 1 + (k : ℤ) * r)).card := by
  haveI : NeZero (p ^ j) := ⟨pow_ne_zero j hp.ne_zero⟩
  have hr_unit : IsUnit (r : ZMod (p ^ j)) := by
    have hcop : Nat.Coprime r.natAbs (p ^ j) := by
      refine Nat.Coprime.pow_right j ?_
      refine (hp.coprime_iff_not_dvd.mpr ?_).symm
      intro hd
      exact hpr (Int.natCast_dvd.mpr hd)
    have : IsUnit ((r.natAbs : ℕ) : ZMod (p ^ j)) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
    rcases Int.natAbs_eq r with hr_eq | hr_eq
    · simpa [← hr_eq] using this
    · rw [hr_eq, Int.cast_neg]
      simpa using this.neg
  let u0 : ZMod (p ^ j) := -(r : ZMod (p ^ j))⁻¹
  have hu0_ne : u0 ≠ 0 := by
    intro h
    have h1 : (r : ZMod (p ^ j)) * u0 = -1 := by
      dsimp [u0]
      rw [mul_neg, ZMod.mul_inv_of_unit _ hr_unit]
    rw [h, mul_zero] at h1
    have h2 : (1 : ZMod (p ^ j)) = 0 := by linear_combination h1
    have hlt1 : 1 < p ^ j := one_lt_pow₀ hp.one_lt (by omega)
    haveI : Nontrivial (ZMod (p ^ j)) := ZMod.nontrivial_iff.mpr hlt1.ne'
    exact one_ne_zero h2
  let u : ℕ := u0.val
  have hu_pos : 0 < u := Nat.pos_of_ne_zero fun h =>
    hu0_ne (by rw [← ZMod.natCast_zmod_val u0, h]; rfl)
  have hu_lt : u < p ^ j := ZMod.val_lt u0
  have hu_mod : (1 + (u : ℤ) * r : ZMod (p ^ j)) = 0 := by
    push_cast
    dsimp [u]
    rw [ZMod.natCast_zmod_val]
    dsimp [u0]
    rw [neg_mul, mul_comm _ (r : ZMod (p ^ j)), ZMod.mul_inv_of_unit _ hr_unit]
    ring
  have hu_dvd : (p : ℤ) ^ j ∣ 1 + (u : ℤ) * r := by
    have : ((1 + (u : ℤ) * r : ℤ) : ZMod (p ^ j)) = 0 := by simpa using hu_mod
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  let f : ℕ → ℕ := fun m => m * p ^ j + u
  have hf_inj : Function.Injective f := by
    intro m₁ m₂ h
    dsimp [f] at h
    have := congrArg (· / p ^ j) h
    have hpj_pos : 0 < p ^ j := pow_pos hp.pos j
    rwa [add_comm (m₁ * p ^ j) u, add_comm (m₂ * p ^ j) u,
      Nat.add_mul_div_right _ _ hpj_pos, Nat.add_mul_div_right _ _ hpj_pos,
      Nat.div_eq_of_lt hu_lt, zero_add, zero_add] at this
  calc n / p ^ j = (Finset.range (n / p ^ j)).card := (Finset.card_range _).symm
    _ ≤ ((Finset.Icc (1 : ℕ) n).filter (fun k : ℕ => (p : ℤ) ^ j ∣ 1 + (k : ℤ) * r)).card := by
        refine Finset.card_le_card_of_injOn f ?_ (fun _ _ _ _ h => hf_inj h)
        intro m hm
        rw [Finset.mem_coe, Finset.mem_range] at hm
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by omega, ?_⟩, ?_⟩
        · have h1 : m + 1 ≤ n / p ^ j := hm
          have h2 : (m + 1) * p ^ j ≤ n :=
            (Nat.mul_le_mul_right (p ^ j) h1).trans (Nat.div_mul_le_self n (p ^ j))
          dsimp [f]
          rw [Nat.add_mul, one_mul] at h2
          omega
        · dsimp [f]
          push_cast
          have hsplit : 1 + ((m : ℤ) * (p : ℤ) ^ j + (u : ℤ)) * r =
              (1 + (u : ℤ) * r) + (p : ℤ) ^ j * ((m : ℤ) * r) := by ring
          rw [hsplit]
          exact dvd_add hu_dvd (dvd_mul_right _ _)

private lemma pow_padicVal_factorial_dvd_prod (p : ℕ) (hp : p.Prime) (r : ℤ) (hpr : ¬ (p : ℤ) ∣ r)
    (n : ℕ) :
    (p : ℤ) ^ padicValNat p n.factorial ∣ ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r) := by
  have hprod_eq : ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r) =
      ∏ k ∈ Finset.Icc 1 n, (1 + (k : ℤ) * r) := by
    have hsplit : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hsplit, Finset.prod_insert (by simp), Nat.cast_zero, zero_mul, add_zero, one_mul]
  rw [hprod_eq]
  by_cases hz : (∏ k ∈ Finset.Icc 1 n, (1 + (k : ℤ) * r)) = 0
  · rw [hz]
    exact dvd_zero _
  have hne : ∀ k ∈ Finset.Icc 1 n, (1 + (k : ℤ) * r) ≠ 0 := by
    intro k hk h0
    apply hz
    exact Finset.prod_eq_zero hk h0
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← padicValInt_dvd_iff (p := p)]
  right
  have hfact : padicValNat p n.factorial =
      ∑ j ∈ Finset.Ico 1 (Nat.log p n + 2), n / p ^ j := by
    rw [padicValNat_factorial (b := Nat.log p n + 2) (by omega)]
    rw [← Finset.sum_Ico_add' (fun j => n / p ^ (j + 1)) 0 _]
    simp only [add_zero]
    rw [Finset.Ico_succ_right_eq_Ioo]
    congr 1
    ext j
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  rw [hfact]
  calc ∑ j ∈ Finset.Ico 1 (Nat.log p n + 2), n / p ^ j
      ≤ ∑ j ∈ Finset.Ico 1 (Nat.log p n + 2),
          ((Finset.Icc 1 n).filter (fun k => (p : ℤ) ^ j ∣ 1 + (k : ℤ) * r)).card := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact card_filter_dvd_ge p hp r hpr n j (Finset.mem_Ico.mp hj).1
    _ = ∑ k ∈ Finset.Icc 1 n,
          ∑ j ∈ Finset.Ico 1 (Nat.log p n + 2),
            (if (p : ℤ) ^ j ∣ 1 + (k : ℤ) * r then 1 else 0) := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.Icc 1 n, padicValInt p (1 + (k : ℤ) * r) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hfk := hne k hk
        have hsub : (Finset.Ico 1 (Nat.log p n + 2)).filter
            (fun j => (p : ℤ) ^ j ∣ 1 + (k : ℤ) * r) ⊆
            Finset.Icc 1 (padicValInt p (1 + (k : ℤ) * r)) := by
          intro j hj
          rw [Finset.mem_filter, Finset.mem_Ico] at hj
          rw [Finset.mem_Icc]
          refine ⟨hj.1.1, ?_⟩
          rcases (padicValInt_dvd_iff _ hfk).1 hj.2 with h | h
          · exact absurd h hfk
          · exact h
        calc ∑ j ∈ Finset.Ico 1 (Nat.log p n + 2),
                (if (p : ℤ) ^ j ∣ 1 + (k : ℤ) * r then 1 else 0)
            = ((Finset.Ico 1 (Nat.log p n + 2)).filter
                (fun j => (p : ℤ) ^ j ∣ 1 + (k : ℤ) * r)).card := by simp [Finset.card_filter]
          _ ≤ (Finset.Icc 1 (padicValInt p (1 + (k : ℤ) * r))).card := Finset.card_le_card hsub
          _ = padicValInt p (1 + (k : ℤ) * r) := by simp
    _ = padicValInt p (∏ k ∈ Finset.Icc 1 n, (1 + (k : ℤ) * r)) :=
        (padicValInt.prod hne).symm

theorem moll_h1 : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 := by
  intro p hp hmod n
  rw [a_eq_P]
  let e := padicValNat p n.factorial
  by_cases he : e = 0
  · simp [e, he]
  obtain ⟨r, hr⟩ := exists_sq_neg_one_mod p hp hmod e
  have hpr : ¬ (p : ℤ) ∣ r := by
    intro h
    have hp_dvd : (p : ℤ) ∣ r ^ 2 + 1 :=
      dvd_trans (dvd_pow_self (p : ℤ) he) (Int.modEq_zero_iff_dvd.mp hr)
    have hp_dvd1 : (p : ℤ) ∣ 1 := (Int.dvd_add_right (dvd_trans h (dvd_pow_self r (by omega)))).mp hp_dvd
    have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hp_dvd1
    exact absurd (by omega : p ≤ 1) (not_le_of_gt hp.one_lt)
  have hnr : ¬ (p : ℤ) ∣ -r := fun h => hpr (dvd_neg.mp h)
  have hr_neg : (-r) ^ 2 + 1 ≡ 0 [ZMOD ((p : ℕ) ^ e : ℕ)] := by simpa using hr
  have h1 : ((p : ℤ) ^ e) ∣ (P n).1 + (P n).2 * r := by
    have hev := P_eval_mod ((p : ℕ) ^ e : ℕ) r hr n
    have hd := pow_padicVal_factorial_dvd_prod p hp r hpr n
    exact Int.dvd_trans (by simpa [e] using hd) (Int.modEq_zero_iff_dvd.mp (hev.trans (Int.modEq_zero_iff_dvd.mpr (by simpa [e] using hd))))
  have h2 : ((p : ℤ) ^ e) ∣ (P n).1 + (P n).2 * (-r) := by
    have hev := P_eval_mod ((p : ℕ) ^ e : ℕ) (-r) hr_neg n
    have hd := pow_padicVal_factorial_dvd_prod p hp (-r) hnr n
    exact Int.dvd_trans (by simpa [e] using hd) (Int.modEq_zero_iff_dvd.mp (hev.trans (Int.modEq_zero_iff_dvd.mpr (by simpa [e] using hd))))
  have hdiff : ((p : ℤ) ^ e) ∣ 2 * r * (P n).2 := by
    have : 2 * r * (P n).2 = ((P n).1 + (P n).2 * r) - ((P n).1 + (P n).2 * (-r)) := by ring
    rw [this]
    exact dvd_sub h1 h2
  have hcop : IsCoprime (2 * r) ((p : ℤ) ^ e) := by
    refine IsCoprime.pow_right ?_
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    have h1g : (Nat.gcd (2 * r).natAbs p : ℕ) ∣ p := Nat.gcd_dvd_right _ _
    rcases hp.eq_one_or_self_of_dvd _ h1g with h | h
    · exact hne h
    · have h2g : p ∣ (2 * r).natAbs := h ▸ Nat.gcd_dvd_left _ _
      have h2z : (p : ℤ) ∣ 2 * r := Int.natCast_dvd.mpr h2g
      rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h2z with hp2 | hpr2
      · have : p ∣ 2 := by exact_mod_cast hp2
        rcases (Nat.dvd_prime Nat.prime_two).mp this with h' | h' <;> omega
      · exact hpr hpr2
  exact hcop.symm.dvd_of_dvd_mul_left hdiff

end OMA.Moll105751

theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 :=
  OMA.Moll105751.moll_h1
