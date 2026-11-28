import OMAStatements.S_arxiv_2610_05514
import Mathlib

namespace OMA.P_arxiv_2610_05514

open OMA.S_arxiv_2610_05514
open scoped Classical

/-! ### Part 1: General finite-field quadratic extension infrastructure -/

section QuadExt

private lemma mem_spreadLine_none {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (p : K × K) : p ∈ spreadLine F K none ↔ p.1 = 0 :=
  Iff.rfl

private lemma mem_spreadLine_some {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (c : K) (p : K × K) : p ∈ spreadLine F K (some c) ↔ p.2 = c * p.1 :=
  Iff.rfl

private lemma card_F_ge_three {F : Type} [Field F] [Fintype F] (hq : Odd (Fintype.card F)) :
    3 ≤ Fintype.card F := by
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  obtain ⟨k, hk⟩ := hq
  omega

private lemma two_ne_zero_of_odd_card {F : Type} [Field F] [Fintype F]
    (hq : Odd (Fintype.card F)) : (2 : F) ≠ 0 := by
  intro h2
  obtain ⟨n, hprime, hcard⟩ := FiniteField.card F (ringChar F)
  have hd : ringChar F ∣ 2 := (ringChar.spec F 2).mp (by simpa using h2)
  have hc : ringChar F = 2 := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hd
  rw [hc] at hcard
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have heven : Even (Fintype.card F) := by
    rw [hcard]
    refine ⟨2 ^ ((n : ℕ) - 1), ?_⟩
    have hsplit : (n : ℕ) = ((n : ℕ) - 1) + 1 := (Nat.sub_add_cancel hn1).symm
    conv_lhs => rw [hsplit, pow_succ]
    ring
  exact Nat.not_even_iff_odd.mpr hq heven

private lemma two_ne_zero_K {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (hq : Odd (Fintype.card F)) : (2 : K) ≠ 0 := by
  intro h2
  apply two_ne_zero_of_odd_card (F := F) hq
  apply (algebraMap F K).injective
  rw [map_ofNat, map_zero]
  exact h2

private lemma frob_add {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (x y : K) :
    (x + y) ^ Fintype.card F = x ^ Fintype.card F + y ^ Fintype.card F := by
  set p := ringChar F
  have hcard := FiniteField.card F p
  have _ : Fact p.Prime := ⟨hcard.choose_spec.1⟩
  have _ : CharP K p := ⟨fun n => by
    rw [← map_natCast (algebraMap F K),
      map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective,
      CharP.cast_eq_zero_iff F p]⟩
  rw [hcard.choose_spec.2]
  induction (hcard.choose : ℕ) with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih, add_pow_char (p := p)]

private lemma frob_neg {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (x : K) :
    (-x) ^ Fintype.card F = -(x ^ Fintype.card F) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← frob_add (F := F), neg_add_cancel, zero_pow Fintype.card_ne_zero]

private lemma frob_sub {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (x y : K) :
    (x - y) ^ Fintype.card F = x ^ Fintype.card F - y ^ Fintype.card F := by
  rw [sub_eq_add_neg, frob_add (F := F), frob_neg (F := F), ← sub_eq_add_neg]

private lemma frob_mul {F K : Type} [Fintype F] [CommSemiring K] (x y : K) :
    (x * y) ^ Fintype.card F = x ^ Fintype.card F * y ^ Fintype.card F :=
  mul_pow x y _

private lemma frob_algebraMap {F K : Type} [Field F] [Fintype F] [Field K] [Algebra F K] (a : F) :
    (algebraMap F K a) ^ Fintype.card F = algebraMap F K a := by
  rw [← map_pow, FiniteField.pow_card]

private lemma frob_frob {F K : Type} [Fintype F] [Field K] [Fintype K]
    (hcardK : Fintype.card K = Fintype.card F ^ 2) (x : K) :
    (x ^ Fintype.card F) ^ Fintype.card F = x := by
  rw [← pow_mul, ← sq, ← hcardK, FiniteField.pow_card]

private lemma frob_eq_self_iff {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (x : K) :
    x ^ Fintype.card F = x ↔ ∃ a : F, algebraMap F K a = x := by
  constructor
  · intro hx
    set q := Fintype.card F
    set S : Finset K := Finset.univ.image (algebraMap F K)
    set R : Finset K := Finset.univ.filter (fun y : K => y ^ q = y)
    have hSR : S ⊆ R := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨a, _, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, frob_algebraMap a⟩
    have hScard : S.card = q := by
      rw [Finset.card_image_of_injective _ (algebraMap F K).injective, Finset.card_univ]
    have hRcard : R.card ≤ q := by
      let f : Polynomial K := Polynomial.X ^ q - Polynomial.X
      have hf_ne : f ≠ 0 := by
        intro h0
        have hdeg := congrArg (fun p : Polynomial K => p.coeff q) h0
        have hq1 : 1 < q := Fintype.one_lt_card
        have h1ne : (1 : ℕ) ≠ q := by omega
        simp [f, Polynomial.coeff_X_pow, Polynomial.coeff_X, h1ne] at hdeg
      have hdeg : f.natDegree ≤ q := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X, max_le_iff, le_refl, true_and]
        exact Fintype.card_pos
      have hsub : R.val ⊆ f.roots := by
        intro y hy
        have hy' : y ^ q = y := (Finset.mem_filter.mp hy).2
        rw [Polynomial.mem_roots hf_ne, Polynomial.IsRoot.def]
        simp [f, hy']
      calc R.card = Multiset.card R.val := rfl
        _ ≤ Multiset.card f.roots := Multiset.card_le_card ((Multiset.le_iff_subset R.nodup).mpr hsub)
        _ ≤ f.natDegree := Polynomial.card_roots' f
        _ ≤ q := hdeg
    have hEq : S = R := Finset.eq_of_subset_of_card_le hSR (by omega)
    have hxR : x ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    rw [← hEq] at hxR
    rcases Finset.mem_image.mp hxR with ⟨a, _, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact frob_algebraMap a

private lemma norm_mem_F {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (hcardK : Fintype.card K = Fintype.card F ^ 2) (x : K) :
    ∃ a : F, algebraMap F K a = x * x ^ Fintype.card F := by
  rw [← frob_eq_self_iff]
  rw [frob_mul (F := F), frob_frob (F := F) hcardK, mul_comm]

private lemma trace_mem_F {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (hcardK : Fintype.card K = Fintype.card F ^ 2) (x : K) :
    ∃ a : F, algebraMap F K a = x + x ^ Fintype.card F := by
  rw [← frob_eq_self_iff]
  rw [frob_add (F := F), frob_frob (F := F) hcardK, add_comm]

private lemma finrank_K_eq_two {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hcardK : Fintype.card K = Fintype.card F ^ 2) :
    Module.finrank F K = 2 := by
  have hcard : Fintype.card K = Fintype.card F ^ Module.finrank F K := Module.card_eq_pow_finrank
  rw [hcardK] at hcard
  exact Nat.pow_right_injective Fintype.one_lt_card hcard.symm

private lemma finrank_map_of_inj {F V W : Type} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (f : V →ₗ[F] W) (hf : Function.Injective f) (L : Submodule F V) :
    Module.finrank F (L.map f) = Module.finrank F L :=
  (Submodule.equivMapOfInjective f hf L).finrank_eq.symm

private lemma orderOf_primitive_unit {F K : Type} [Fintype F] [Field K] [Fintype K]
    (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (β : Kˣ) (hβ : ∀ x : Kˣ, x ∈ Subgroup.zpowers β) :
    orderOf β = Fintype.card F ^ 2 - 1 := by
  have htop : Subgroup.zpowers β = ⊤ := eq_top_iff.mpr (fun x _ => hβ x)
  have h1 : orderOf β = Nat.card (Subgroup.zpowers β) := (Nat.card_zpowers β).symm
  rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units, hcardK] at h1
  exact h1

private lemma beta_pow_q_add_one_mem_F {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hcardK : Fintype.card K = Fintype.card F ^ 2) (β : Kˣ) :
    ∃ g : Fˣ, algebraMap F K (g : F) = (β : K) ^ (Fintype.card F + 1) := by
  have hmem : ∃ a : F, algebraMap F K a = (β : K) ^ (Fintype.card F + 1) := by
    rw [pow_succ']
    exact norm_mem_F hcardK (β : K)
  obtain ⟨a, ha⟩ := hmem
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha
    exact pow_ne_zero _ β.ne_zero ha.symm
  exact ⟨Units.mk0 a ha0, ha⟩

private lemma beta_pow_q_add_one_gen_F {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (β : Kˣ) (hβ : ∀ x : Kˣ, x ∈ Subgroup.zpowers β)
    (g : Fˣ) (hg : algebraMap F K (g : F) = (β : K) ^ (Fintype.card F + 1)) :
    orderOf g = Fintype.card F - 1 ∧ ∀ d : Fˣ, d ∈ Subgroup.zpowers g := by
  set q := Fintype.card F
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hordβ : orderOf β = q ^ 2 - 1 := orderOf_primitive_unit (F := F) hcardK β hβ
  have hord_pow : orderOf (β ^ (q + 1)) = q - 1 := by
    rw [orderOf_pow, hordβ]
    have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]
      ring
    rw [hfac, Nat.gcd_comm, Nat.gcd_eq_left (dvd_mul_right (q + 1) (q - 1)),
      Nat.mul_div_cancel_left _ (by omega)]
  have hordg : orderOf g = q - 1 := by
    let φ : Fˣ →* Kˣ := Units.map (algebraMap F K).toMonoidHom
    have hφ_inj : Function.Injective φ := by
      intro x y hxy
      ext
      exact (algebraMap F K).injective (congrArg Units.val hxy)
    have hφg : φ g = β ^ (q + 1) := by
      ext
      simpa [φ] using hg
    rw [← orderOf_injective φ hφ_inj g, hφg, hord_pow]
  refine ⟨hordg, ?_⟩
  have hcard : Nat.card (Subgroup.zpowers g) = Fintype.card Fˣ := by
    rw [Nat.card_zpowers, hordg, Fintype.card_units]
  have htop : Subgroup.zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by simpa [Nat.card_eq_fintype_card] using hcard)
  intro d
  rw [htop]
  trivial

private lemma norm_surjective {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hcardK : Fintype.card K = Fintype.card F ^ 2) (a : F) (ha : a ≠ 0) :
    ∃ r : K, r ≠ 0 ∧ r * r ^ Fintype.card F = algebraMap F K a := by
  obtain ⟨β, hβ⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨g, hg⟩ := beta_pow_q_add_one_mem_F (F := F) hcardK β
  obtain ⟨_, hgen⟩ := beta_pow_q_add_one_gen_F hcardK β hβ g hg
  obtain ⟨n, hn⟩ := hgen (Units.mk0 a ha)
  dsimp only at hn
  refine ⟨((β ^ n : Kˣ) : K), (β ^ n).ne_zero, ?_⟩
  have h1 : (((β ^ n : Kˣ) : K)) * (((β ^ n : Kˣ) : K)) ^ Fintype.card F =
      (((β ^ (Fintype.card F + 1)) ^ n : Kˣ) : K) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 1
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    push_cast
    ring
  rw [h1]
  have h2 : (((β ^ (Fintype.card F + 1)) ^ n : Kˣ) : K) =
      algebraMap F K (((g ^ n : Fˣ) : F)) := by
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, hg,
      Units.val_pow_eq_pow_val]
  rw [h2, hn]
  rfl

private lemma card_unit_circle {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    (hcardK : Fintype.card K = Fintype.card F ^ 2) :
    (Finset.univ.filter (fun u : K => u * u ^ Fintype.card F = 1)).card = Fintype.card F + 1 := by
  set q := Fintype.card F
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hq2_gt : 1 < q ^ 2 := by nlinarith
  obtain ⟨β, hβ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hordβ : orderOf β = q ^ 2 - 1 := orderOf_primitive_unit (F := F) hcardK β hβ
  have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]; ring
  let f : Fin (q + 1) → K := fun j => (β : K) ^ (j.1 * (q - 1))
  have hf_inj : Function.Injective f := by
    intro i j hij
    dsimp only [f] at hij
    by_contra hne
    have hne' : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
    have hlt_case : ∀ a b : Fin (q + 1), a.1 < b.1 →
        (β : K) ^ (a.1 * (q - 1)) = (β : K) ^ (b.1 * (q - 1)) → False := by
      intro a b hlt hab
      have hpow : β ^ ((b.1 - a.1) * (q - 1)) = 1 := by
        apply Units.ext
        have h1 : (β : K) ^ (b.1 * (q - 1)) =
            (β : K) ^ (a.1 * (q - 1)) * (β : K) ^ ((b.1 - a.1) * (q - 1)) := by
          rw [← pow_add, ← add_mul, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
        have h3 : (β : K) ^ (a.1 * (q - 1)) * 1 =
            (β : K) ^ (a.1 * (q - 1)) * (β : K) ^ ((b.1 - a.1) * (q - 1)) := by
          rw [mul_one, ← h1]; exact hab
        simpa using (mul_left_cancel₀ (pow_ne_zero _ β.ne_zero) h3).symm
      have hdvd : orderOf β ∣ (b.1 - a.1) * (q - 1) := orderOf_dvd_of_pow_eq_one hpow
      rw [hordβ, hfac] at hdvd
      have hle : (q + 1) * (q - 1) ≤ (b.1 - a.1) * (q - 1) :=
        Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd
      have : q + 1 ≤ b.1 - a.1 := Nat.le_of_mul_le_mul_right hle (by omega)
      omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · exact hlt_case i j hlt hij
    · exact hlt_case j i hgt hij.symm
  have himg : Finset.univ.image f = Finset.univ.filter (fun u : K => u * u ^ q = 1) := by
    ext u
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j, rfl⟩
      dsimp only [f]
      rw [← pow_succ', ← pow_mul]
      have hmul : j.1 * (q - 1) * (q + 1) = j.1 * (q ^ 2 - 1) := by
        rw [mul_assoc, mul_comm (q - 1), ← hfac]
      rw [hmul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← hordβ, pow_orderOf_eq_one,
        Units.val_one, one_pow]
    · intro hu
      have hu0 : u ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hu; exact zero_ne_one hu
      obtain ⟨k, hk⟩ := hβ (Units.mk0 u hu0)
      dsimp only at hk
      have hord_pos : 0 < orderOf β := by omega
      let m : ℕ := (k % (orderOf β : ℤ)).toNat
      have hm_lt : m < q ^ 2 - 1 := by
        have hnonneg : 0 ≤ k % (orderOf β : ℤ) := Int.emod_nonneg k (by omega)
        have hlt : k % (orderOf β : ℤ) < (orderOf β : ℤ) := Int.emod_lt_of_pos k (by omega)
        omega
      have hbm : β ^ m = Units.mk0 u hu0 := by
        rw [← hk]
        have h1 : (m : ℤ) = k % (orderOf β : ℤ) :=
          Int.toNat_of_nonneg (Int.emod_nonneg k (by omega))
        rw [← zpow_natCast, h1, zpow_mod_orderOf]
      have hpow1 : β ^ (m * (q + 1)) = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul, ← Units.val_pow_eq_pow_val, hbm]
        simpa [pow_succ'] using hu
      have hdvd : (q + 1) * (q - 1) ∣ m * (q + 1) := by
        rw [← hfac, ← hordβ]
        exact orderOf_dvd_of_pow_eq_one hpow1
      have hdvd' : q - 1 ∣ m := by
        rw [mul_comm m (q + 1)] at hdvd
        exact (Nat.mul_dvd_mul_iff_left (by omega)).mp hdvd
      obtain ⟨r, hr⟩ := hdvd'
      have hr_lt : r < q + 1 := by
        rw [hr, hfac, mul_comm (q + 1)] at hm_lt
        exact Nat.lt_of_mul_lt_mul_left hm_lt
      refine ⟨⟨r, hr_lt⟩, ?_⟩
      dsimp only [f]
      rw [mul_comm r (q - 1), ← hr, ← Units.val_pow_eq_pow_val, hbm]
      rfl
  rw [← himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]

private lemma exists_pow_q_sub_one_eq {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (u : K) (hu : u * u ^ Fintype.card F = 1) :
    ∃ x : K, x ≠ 0 ∧ x ^ Fintype.card F = u * x := by
  set q := Fintype.card F
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hq2_gt : 1 < q ^ 2 := by nlinarith
  obtain ⟨β, hβ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hordβ : orderOf β = q ^ 2 - 1 := orderOf_primitive_unit (F := F) hcardK β hβ
  have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]; ring
  have hu0 : u ≠ 0 := by intro h0; rw [h0, zero_mul] at hu; exact zero_ne_one hu
  obtain ⟨k, hk⟩ := hβ (Units.mk0 u hu0)
  dsimp only at hk
  let m : ℕ := (k % (orderOf β : ℤ)).toNat
  have hbm : β ^ m = Units.mk0 u hu0 := by
    rw [← hk]
    have h1 : (m : ℤ) = k % (orderOf β : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg k (by omega))
    rw [← zpow_natCast, h1, zpow_mod_orderOf]
  have hpow1 : β ^ (m * (q + 1)) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul, ← Units.val_pow_eq_pow_val, hbm]
    simpa [pow_succ'] using hu
  have hdvd : (q + 1) * (q - 1) ∣ m * (q + 1) := by
    rw [← hfac, ← hordβ]; exact orderOf_dvd_of_pow_eq_one hpow1
  have hdvd' : q - 1 ∣ m := by
    rw [mul_comm m (q + 1)] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (by omega)).mp hdvd
  obtain ⟨r, hr⟩ := hdvd'
  refine ⟨(β : K) ^ r, pow_ne_zero _ β.ne_zero, ?_⟩
  have hbm_val : (β : K) ^ m = u := congrArg Units.val hbm
  rw [← hbm_val, hr, ← pow_mul, ← pow_add]
  congr 1
  have : r * q = (q - 1) * r + r := by
    zify [show 1 ≤ q by omega]; ring
  exact this

private lemma card_miquelianCircle_of_b_ne_zero {F K : Type} [Field F] [Fintype F] [Field K]
    [Fintype K] [Algebra F K] (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (lam : K) (a b : F) (hb : b ≠ 0)
    (hnd : lam * lam ^ Fintype.card F + algebraMap F K (a * b) ≠ 0) :
    (miquelianCircle F K lam a b).card = Fintype.card F + 1 := by
  set q := Fintype.card F
  have hbK : algebraMap F K b ≠ 0 :=
    (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr hb
  have hnorm_mem : ∃ R : F, algebraMap F K R =
      (lam * lam ^ q + algebraMap F K (a * b)) / (algebraMap F K b ^ 2) := by
    obtain ⟨nlam, hnlam⟩ := norm_mem_F hcardK lam
    refine ⟨(nlam + a * b) / b ^ 2, ?_⟩
    rw [map_div₀, map_add, map_pow, hnlam]
  obtain ⟨R, hR⟩ := hnorm_mem
  have hR0 : R ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hR
    exact hnd (div_eq_zero_iff.mp hR.symm |>.resolve_right (pow_ne_zero 2 hbK))
  obtain ⟨r, hr0, hr_norm⟩ := norm_surjective hcardK R hR0
  let c : K := lam / algebraMap F K b
  let U : Finset K := Finset.univ.filter (fun u : K => u * u ^ q = 1)
  have hUcard : U.card = q + 1 := card_unit_circle (F := F) hcardK
  let f : K → Option K := fun u => some (c + r * u)
  have hf_inj : Function.Injective f := by
    intro u₁ u₂ h
    have h' : c + r * u₁ = c + r * u₂ := Option.some.inj h
    exact mul_left_cancel₀ hr0 (add_left_cancel h')
  have himg : U.image f = miquelianCircle F K lam a b := by
    ext k
    simp only [Finset.mem_image, U, Finset.mem_filter, Finset.mem_univ, true_and,
      miquelianCircle, f]
    cases k with
    | none => simp [hb]
    | some x =>
      simp only [Option.some.injEq]
      have hbc : algebraMap F K b * c = lam := mul_div_cancel₀ lam hbK
      have hcq : c ^ q = lam ^ q / algebraMap F K b := by
        simp only [c, div_pow]
        rw [frob_algebraMap]
      have hbcq : algebraMap F K b * c ^ q = lam ^ q := by
        rw [hcq, mul_div_cancel₀ _ hbK]
      have hrr : algebraMap F K b * (r * r ^ q) =
          (lam * lam ^ q + algebraMap F K (a * b)) / algebraMap F K b := by
        rw [hr_norm, hR, sq, div_mul_eq_div_div, mul_div_cancel₀ _ hbK]
      have hrr' : algebraMap F K b * (r * r ^ q) * algebraMap F K b =
          lam * lam ^ q + algebraMap F K (a * b) := by
        rw [hrr, div_mul_cancel₀ _ hbK]
      constructor
      · rintro ⟨u, hu, rfl⟩
        have h1 : (c + r * u) * (c + r * u) ^ q =
            c * c ^ q + c * (r ^ q * u ^ q) + r * u * c ^ q + (r * r ^ q) * (u * u ^ q) := by
          rw [frob_add (F := F), frob_mul (F := F)]; ring
        rw [h1, hu, mul_one, frob_add (F := F), frob_mul (F := F)]
        apply mul_right_cancel₀ hbK
        rw [zero_mul]
        have h2 : (algebraMap F K b * (c * c ^ q + c * (r ^ q * u ^ q) + r * u * c ^ q + r * r ^ q) -
            lam ^ q * (c + r * u) - lam * (c ^ q + r ^ q * u ^ q) - algebraMap F K a) * algebraMap F K b =
            (algebraMap F K b * c) * (algebraMap F K b * c ^ q) +
            (algebraMap F K b * c) * (algebraMap F K b * r ^ q * u ^ q) +
            (algebraMap F K b * c ^ q) * (algebraMap F K b * r * u) +
            (algebraMap F K b * (r * r ^ q) * algebraMap F K b) -
            lam ^ q * (algebraMap F K b * c + algebraMap F K b * r * u) -
            lam * (algebraMap F K b * c ^ q + algebraMap F K b * r ^ q * u ^ q) -
            algebraMap F K (a * b) := by
          rw [map_mul]; ring
        rw [h2, hbc, hbcq, hrr']
        ring
      · intro hx
        refine ⟨(x - c) / r, ?_, by rw [mul_div_cancel₀ _ hr0, add_sub_cancel]⟩
        rw [div_pow, div_mul_div_comm]
        rw [div_eq_one_iff_eq (mul_ne_zero hr0 (pow_ne_zero q hr0))]
        have hmul : algebraMap F K b * ((x - c) * (x - c) ^ q) * algebraMap F K b =
            algebraMap F K b * (r * r ^ q) * algebraMap F K b := by
          rw [frob_sub (F := F), hrr']
          have h3 : algebraMap F K b * ((x - c) * (x ^ q - c ^ q)) * algebraMap F K b =
              (algebraMap F K b * (x * x ^ q) - lam ^ q * x - lam * x ^ q - algebraMap F K a) *
                algebraMap F K b +
              (lam * lam ^ q + algebraMap F K (a * b)) +
              (algebraMap F K b * c - lam) * (algebraMap F K b * c ^ q - algebraMap F K b * x ^ q) +
              (algebraMap F K b * c ^ q - lam ^ q) * (lam - algebraMap F K b * x) := by
            rw [map_mul]; ring
          rw [h3, hx, zero_mul, zero_add, hbc, hbcq]
          ring
        exact mul_left_cancel₀ hbK (mul_right_cancel₀ hbK hmul)
  rw [← himg, Finset.card_image_of_injective _ hf_inj, hUcard]

private lemma quad_roots_count {F : Type} [Field F] [Fintype F]
    (hq : Odd (Fintype.card F)) (A B C : F) (hA : A ≠ 0) (hΔ : B ^ 2 - 4 * A * C ≠ 0) :
    (Finset.univ.filter (fun u : F => A * u ^ 2 + B * u + C = 0)).card =
      if IsSquare (B ^ 2 - 4 * A * C) then 2 else 0 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hq
  have h2A : 2 * A ≠ 0 := mul_ne_zero h2 hA
  have h4A : 4 * A ≠ 0 := by
    have : (4 : F) * A = 2 * (2 * A) := by ring
    rw [this]; exact mul_ne_zero h2 h2A
  have hiff : ∀ u : F, A * u ^ 2 + B * u + C = 0 ↔ (2 * A * u + B) ^ 2 = B ^ 2 - 4 * A * C := by
    intro u
    constructor
    · intro h
      calc (2 * A * u + B) ^ 2 = 4 * A * (A * u ^ 2 + B * u + C) + (B ^ 2 - 4 * A * C) := by ring
        _ = B ^ 2 - 4 * A * C := by rw [h, mul_zero, zero_add]
    · intro h
      have h1 : 4 * A * (A * u ^ 2 + B * u + C) = 0 := by
        calc 4 * A * (A * u ^ 2 + B * u + C) = (2 * A * u + B) ^ 2 - (B ^ 2 - 4 * A * C) := by ring
          _ = 0 := sub_eq_zero.mpr h
      exact (mul_eq_zero.mp h1).resolve_left h4A
  split_ifs with hsq
  · rcases hsq with ⟨s, hs⟩
    have hs0 : s ≠ 0 := by intro h0; rw [h0, mul_zero] at hs; exact hΔ hs
    have hset : Finset.univ.filter (fun u : F => A * u ^ 2 + B * u + C = 0) =
        {(-B + s) / (2 * A), (-B - s) / (2 * A)} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, hiff, hs, ← sq, sq_eq_sq_iff_eq_or_eq_neg]
      constructor
      · rintro (h | h)
        · left
          rw [eq_div_iff h2A]
          calc u * (2 * A) = (2 * A * u + B) - B := by ring
            _ = s - B := by rw [h]
            _ = -B + s := by ring
        · right
          rw [eq_div_iff h2A]
          calc u * (2 * A) = (2 * A * u + B) - B := by ring
            _ = -s - B := by rw [h]
            _ = -B - s := by ring
      · rintro (rfl | rfl)
        · left; field_simp [h2A]; ring
        · right; field_simp [h2A]; ring
    rw [hset, Finset.card_pair]
    intro heq
    have hnum : -B + s = -B - s := by
      have := congrArg (· * (2 * A)) heq
      rwa [div_mul_cancel₀ _ h2A, div_mul_cancel₀ _ h2A] at this
    have h2s : 2 * s = 0 := by
      calc 2 * s = (-B + s) - (-B - s) := by ring
        _ = 0 := sub_eq_zero.mpr hnum
    exact mul_ne_zero h2 hs0 h2s
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u _ h
    exact hsq ⟨2 * A * u + B, by rw [← sq]; exact ((hiff u).mp h).symm⟩

private lemma poly_deg2_card_le_two {K : Type} [Field K] [Fintype K] (p q r : K) (hp : p ≠ 0) :
    (Finset.univ.filter (fun x : K => p * x ^ 2 + q * x + r = 0)).card ≤ 2 := by
  let f : Polynomial K :=
    Polynomial.C p * Polynomial.X ^ 2 + Polynomial.C q * Polynomial.X + Polynomial.C r
  have hf_ne : f ≠ 0 := by
    intro h0
    have hc := congrArg (fun g : Polynomial K => g.coeff 2) h0
    simp [f, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc
    exact hp hc
  have hdeg : f.natDegree ≤ 2 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp only [Polynomial.natDegree_C, max_le_iff, Nat.zero_le, and_true]
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp only [max_le_iff]
    constructor
    · refine le_trans (Polynomial.natDegree_mul_le) ?_; simp
    · refine le_trans (Polynomial.natDegree_mul_le) ?_; simp
  set S := Finset.univ.filter (fun x : K => p * x ^ 2 + q * x + r = 0)
  have hsub : S.val ⊆ f.roots := by
    intro x hx
    have hx' : p * x ^ 2 + q * x + r = 0 := (Finset.mem_filter.mp hx).2
    rw [Polynomial.mem_roots hf_ne, Polynomial.IsRoot.def]
    simp [f, hx']
  calc S.card = Multiset.card S.val := rfl
    _ ≤ Multiset.card f.roots := Multiset.card_le_card ((Multiset.le_iff_subset S.nodup).mpr hsub)
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ ≤ 2 := hdeg

/-! ### Part 2: Baker–Ebert `(q-1)`-nest refinement (Theorems 6.2 & 6.3) -/

private lemma scale_miquelianCircle_11b {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (d : Fˣ) (b : F) :
    (miquelianCircle F K 1 1 b).image (scaleOption F K d) =
      miquelianCircle F K (algebraMap F K (d : F)) ((d : F) ^ 2) b := by
  set q := Fintype.card F
  have hdK : algebraMap F K (d : F) ≠ 0 :=
    (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr d.ne_zero
  ext k
  simp only [Finset.mem_image, miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and]
  cases k with
  | none =>
    constructor
    · rintro ⟨w, hw, hsw⟩
      cases w with
      | none => exact hw
      | some x => simp [scaleOption] at hsw
    · intro hb0
      exact ⟨none, hb0, rfl⟩
  | some y =>
    dsimp only
    constructor
    · rintro ⟨w, hw, hsw⟩
      cases w with
      | none => simp [scaleOption] at hsw
      | some x =>
        dsimp only at hw
        have hy : algebraMap F K (d : F) * x = y := Option.some.inj hsw
        rw [← hy, frob_mul (F := F), frob_algebraMap, map_pow]
        rw [one_pow, one_mul, one_mul, map_one] at hw
        calc algebraMap F K b * (algebraMap F K (d : F) * x * (algebraMap F K (d : F) * x ^ q)) -
              algebraMap F K (d : F) * (algebraMap F K (d : F) * x) -
              algebraMap F K (d : F) * (algebraMap F K (d : F) * x ^ q) -
              algebraMap F K (d : F) ^ 2
            = algebraMap F K (d : F) ^ 2 *
                (algebraMap F K b * (x * x ^ Fintype.card F) - x - x ^ Fintype.card F - 1) := by
              simp only [q]; ring
          _ = 0 := by rw [hw, mul_zero]
    · intro hy
      refine ⟨some (algebraMap F K (d : F)⁻¹ * y), ?_, ?_⟩
      · dsimp only
        rw [frob_mul (F := F), frob_algebraMap, one_pow, one_mul, one_mul, map_one]
        rw [frob_algebraMap, map_pow] at hy
        apply mul_left_cancel₀ (pow_ne_zero 2 hdK)
        rw [mul_zero]
        have hdi : algebraMap F K (d : F) * algebraMap F K (d : F)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel₀ d.ne_zero, map_one]
        calc algebraMap F K (d : F) ^ 2 *
              (algebraMap F K b * (algebraMap F K (d : F)⁻¹ * y * (algebraMap F K (d : F)⁻¹ * y ^ Fintype.card F)) -
                algebraMap F K (d : F)⁻¹ * y - algebraMap F K (d : F)⁻¹ * y ^ Fintype.card F - 1)
            = algebraMap F K b * ((algebraMap F K (d : F) * algebraMap F K (d : F)⁻¹) ^ 2 * (y * y ^ Fintype.card F)) -
              algebraMap F K (d : F) * ((algebraMap F K (d : F) * algebraMap F K (d : F)⁻¹) * y) -
              algebraMap F K (d : F) * ((algebraMap F K (d : F) * algebraMap F K (d : F)⁻¹) * y ^ Fintype.card F) -
              algebraMap F K (d : F) ^ 2 := by ring
          _ = algebraMap F K b * (y * y ^ Fintype.card F) - algebraMap F K (d : F) * y -
              algebraMap F K (d : F) * y ^ Fintype.card F - algebraMap F K (d : F) ^ 2 := by
            rw [hdi, one_pow, one_mul, one_mul, one_mul]
          _ = 0 := hy
      · simp only [scaleOption, ← mul_assoc, ← map_mul, mul_inv_cancel₀ d.ne_zero, map_one, one_mul]

private lemma disc_ne_zero_of_b_sq {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hq : Odd (Fintype.card F)) (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (b : F) (hb_sq : IsSquare (b * (b + 1))) (hb_ne : b * (b + 1) ≠ 0)
    (y : K) (hy : y ≠ 0) :
    (y + y ^ Fintype.card F) ^ 2 + 4 * algebraMap F K b * (y * y ^ Fintype.card F) ≠ 0 := by
  set q := Fintype.card F
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hb_ne
  have hb1 : b + 1 ≠ 0 := right_ne_zero_of_mul hb_ne
  have h2K : (2 : K) ≠ 0 := two_ne_zero_K (F := F) hq
  have h4K : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2K h2K
  intro hzero
  set v : K := y ^ q / y
  have hv_eq : v ^ 2 + (4 * algebraMap F K b + 2) * v + 1 = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hy)
    rw [mul_zero]
    have : y ^ 2 * (v ^ 2 + (4 * algebraMap F K b + 2) * v + 1) =
        (y + y ^ q) ^ 2 + 4 * algebraMap F K b * (y * y ^ q) := by
      simp only [v]; field_simp [hy]; ring
    rw [this, hzero]
  rcases hb_sq with ⟨s, hs⟩
  have hquad : (v + (2 * algebraMap F K b + 1)) ^ 2 = (2 * algebraMap F K s) ^ 2 := by
    have hsk : algebraMap F K s * algebraMap F K s = algebraMap F K b * (algebraMap F K b + 1) := by
      rw [← map_mul, ← hs, map_mul, map_add, map_one]
    calc (v + (2 * algebraMap F K b + 1)) ^ 2
        = (v ^ 2 + (4 * algebraMap F K b + 2) * v + 1) +
            4 * (algebraMap F K b * (algebraMap F K b + 1)) := by ring
      _ = 4 * (algebraMap F K s * algebraMap F K s) := by rw [hv_eq, zero_add, hsk]
      _ = (2 * algebraMap F K s) ^ 2 := by ring
  have hv_in_F : v ^ q = v := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hquad with h | h
    · have hv_val : v = 2 * algebraMap F K s - (2 * algebraMap F K b + 1) := by
        calc v = (v + (2 * algebraMap F K b + 1)) - (2 * algebraMap F K b + 1) := by ring
          _ = 2 * algebraMap F K s - (2 * algebraMap F K b + 1) := by rw [h]
      have : ∃ c : F, algebraMap F K c = v :=
        ⟨2 * s - (2 * b + 1), by simp only [map_sub, map_add, map_mul, map_ofNat, map_one, hv_val]⟩
      exact (frob_eq_self_iff v).mpr this
    · have hv_val : v = -(2 * algebraMap F K s) - (2 * algebraMap F K b + 1) := by
        calc v = (v + (2 * algebraMap F K b + 1)) - (2 * algebraMap F K b + 1) := by ring
          _ = -(2 * algebraMap F K s) - (2 * algebraMap F K b + 1) := by rw [h]
      have : ∃ c : F, algebraMap F K c = v :=
        ⟨-(2 * s) - (2 * b + 1), by simp only [map_sub, map_add, map_mul, map_ofNat, map_one, map_neg, hv_val]⟩
      exact (frob_eq_self_iff v).mpr this
  have hv_sq : v ^ 2 = 1 := by
    calc v ^ 2 = v * v := sq v
      _ = v * v ^ q := by rw [hv_in_F]
      _ = (y ^ q / y) * ((y ^ q) ^ q / y ^ q) := by rw [div_pow]
      _ = (y ^ q / y) * (y / y ^ q) := by rw [frob_frob (F := F) hcardK]
      _ = 1 := by field_simp [hy, pow_ne_zero q hy]
  rcases sq_eq_one_iff.mp hv_sq with hv1 | hvm1
  · rw [hv1] at hv_eq
    have h4b1 : 4 * (algebraMap F K (b + 1)) = 0 := by
      rw [map_add, map_one]; linear_combination hv_eq
    have : algebraMap F K (b + 1) = 0 := (mul_eq_zero.mp h4b1).resolve_left h4K
    exact hb1 ((map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective).mp this)
  · rw [hvm1] at hv_eq
    have h4b : 4 * algebraMap F K b = 0 := by linear_combination -hv_eq
    have : algebraMap F K b = 0 := (mul_eq_zero.mp h4b).resolve_left h4K
    exact hb0 ((map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective).mp this)

private lemma bakerEbert_isNest {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hq : Odd (Fintype.card F)) (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (b : F) (hb_sq : IsSquare (b * (b + 1))) (hb_ne : b * (b + 1) ≠ 0) :
    IsNest F K (Fintype.card F - 1) (bundleOrbit F K (miquelianCircle F K 1 1 b)) := by
  set q := Fintype.card F
  have hq3 : 3 ≤ q := card_F_ge_three hq
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hb_ne
  have hb1 : b + 1 ≠ 0 := right_ne_zero_of_mul hb_ne
  have hbK : algebraMap F K b ≠ 0 :=
    (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr hb0
  have hnd1 : (1 : K) * (1 : K) ^ q + algebraMap F K (1 * b) ≠ 0 := by
    rw [one_pow, one_mul, one_mul, ← map_one (algebraMap F K), ← map_add, add_comm]
    exact (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr hb1
  set D := miquelianCircle F K 1 1 b
  have hDcard : D.card = q + 1 := card_miquelianCircle_of_b_ne_zero hcardK 1 1 b hb0 hnd1
  have horb_inj : Function.Injective (fun d : Fˣ => D.image (scaleOption F K d)) := by
    intro d₁ d₂ hEq
    dsimp only at hEq
    by_contra hne
    set d : Fˣ := d₁ * d₂⁻¹
    have hd_ne1 : (d : F) ≠ 1 := by
      intro h1
      apply hne
      apply Units.ext
      have h1' : (d₁ : F) * (d₂ : F)⁻¹ = 1 := by simpa [d] using h1
      calc (d₁ : F) = (d₁ : F) * (d₂ : F)⁻¹ * (d₂ : F) := by
            rw [mul_assoc, inv_mul_cancel₀ d₂.ne_zero, mul_one]
        _ = (d₂ : F) := by rw [h1', one_mul]
    have hdd : D.image (scaleOption F K d) = D := by
      have h1 : D.image (scaleOption F K d) =
          (D.image (scaleOption F K d₁)).image (scaleOption F K d₂⁻¹) := by
        ext k
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨w, hw, rfl⟩
          refine ⟨scaleOption F K d₁ w, ⟨w, hw, rfl⟩, ?_⟩
          cases w with
          | none => rfl
          | some x =>
            simp only [scaleOption, Option.some.injEq, d, Units.val_mul, map_mul]
            ring
        · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
          refine ⟨w, hw, ?_⟩
          cases w with
          | none => rfl
          | some x =>
            simp only [scaleOption, Option.some.injEq, d, Units.val_mul, map_mul]
            ring
      rw [h1, hEq]
      ext k
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        cases w with
        | none => exact hw
        | some x =>
          have : scaleOption F K d₂⁻¹ (scaleOption F K d₂ (some x)) = some x := by
            simp only [scaleOption, Units.val_inv_eq_inv_val, ← mul_assoc,
              ← map_mul, inv_mul_cancel₀ d₂.ne_zero, map_one, one_mul]
          rwa [this]
      · intro hk
        refine ⟨scaleOption F K d₂ k, ⟨k, hk, rfl⟩, ?_⟩
        cases k with
        | none => rfl
        | some x =>
          simp only [scaleOption, Units.val_inv_eq_inv_val, ← mul_assoc,
            ← map_mul, inv_mul_cancel₀ d₂.ne_zero, map_one, one_mul]
    have hd1K : algebraMap F K (d : F) - 1 ≠ 0 := by
      intro h0
      exact hd_ne1 ((algebraMap F K).injective (by simpa using sub_eq_zero.mp h0))
    have hD_le_two : D.card ≤ 2 := by
      have hsub' : D ⊆ (Finset.univ.filter (fun x : K =>
          1 * x ^ 2 + (algebraMap F K (d : F) + 1) * x +
            (-(algebraMap F K (d : F) / algebraMap F K b)) = 0)).image some := by
        intro k hk
        cases k with
        | none => simp [D, miquelianCircle, hb0] at hk
        | some x =>
          rw [Finset.mem_image]
          refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          have hx1 : algebraMap F K b * (x * x ^ q) - x - x ^ q - 1 = 0 := by
            simpa [D, miquelianCircle] using hk
          have hx2 : some x ∈ D.image (scaleOption F K d) := by rwa [hdd]
          rw [scale_miquelianCircle_11b] at hx2
          have hx2' : algebraMap F K b * (x * x ^ q) - algebraMap F K (d : F) * x -
              algebraMap F K (d : F) * x ^ q - algebraMap F K (d : F) ^ 2 = 0 := by
            simpa [miquelianCircle, frob_algebraMap, map_pow] using hx2
          have hnorm : algebraMap F K b * (x * x ^ q) = -algebraMap F K (d : F) := by
            have hdiff : (algebraMap F K (d : F) - 1) *
                (algebraMap F K b * (x * x ^ q) + algebraMap F K (d : F)) = 0 := by
              linear_combination algebraMap F K (d : F) * hx1 - hx2'
            linear_combination (mul_eq_zero.mp hdiff).resolve_left hd1K
          have htrace : x + x ^ q = -(algebraMap F K (d : F) + 1) := by
            linear_combination -hx1 + hnorm
          have hprod : x * x ^ q = -(algebraMap F K (d : F) / algebraMap F K b) := by
            apply mul_left_cancel₀ hbK
            rw [mul_neg, mul_div_cancel₀ _ hbK, hnorm]
          linear_combination x * htrace - hprod
      calc D.card ≤ ((Finset.univ.filter (fun x : K =>
            1 * x ^ 2 + (algebraMap F K (d : F) + 1) * x +
              (-(algebraMap F K (d : F) / algebraMap F K b)) = 0)).image some).card :=
          Finset.card_le_card hsub'
        _ ≤ (Finset.univ.filter (fun x : K =>
            1 * x ^ 2 + (algebraMap F K (d : F) + 1) * x +
              (-(algebraMap F K (d : F) / algebraMap F K b)) = 0)).card :=
          Finset.card_image_le
        _ ≤ 2 := poly_deg2_card_le_two 1 _ _ one_ne_zero
    omega
  refine ⟨?_, ?_, ?_⟩
  · unfold bundleOrbit
    rw [Finset.card_image_of_injective _ horb_inj, Finset.card_univ, Fintype.card_units]
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨d, _, rfl⟩
    rw [scale_miquelianCircle_11b]
    refine ⟨algebraMap F K (d : F), (d : F) ^ 2, b, ?_, rfl⟩
    rw [frob_algebraMap, map_mul, map_pow]
    have hfac : algebraMap F K (d : F) * algebraMap F K (d : F) +
        algebraMap F K (d : F) ^ 2 * algebraMap F K b =
        algebraMap F K ((d : F) ^ 2 * (b + 1)) := by
      rw [map_mul, map_pow, map_add, map_one]; ring
    rw [hfac]
    exact (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr
      (mul_ne_zero (pow_ne_zero 2 d.ne_zero) hb1)
  · intro k
    cases k with
    | none =>
      left
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro C hC hmem
      rcases Finset.mem_image.mp hC with ⟨d, _, rfl⟩
      rw [scale_miquelianCircle_11b] at hmem
      simp [miquelianCircle, hb0] at hmem
    | some y =>
      by_cases hy : y = 0
      · subst hy
        left
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro C hC hmem
        rcases Finset.mem_image.mp hC with ⟨d, _, rfl⟩
        rw [scale_miquelianCircle_11b] at hmem
        simp only [miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and,
          zero_pow Fintype.card_ne_zero, mul_zero, sub_zero, zero_sub, neg_eq_zero] at hmem
        exact pow_ne_zero 2 d.ne_zero
          ((map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective).mp hmem)
      · obtain ⟨Ny, hNy⟩ := norm_mem_F hcardK y
        obtain ⟨Ty, hTy⟩ := trace_mem_F hcardK y
        have hNy0 : Ny ≠ 0 := by
          intro h0; rw [h0, map_zero] at hNy
          exact mul_ne_zero hy (pow_ne_zero q hy) hNy.symm
        have hΔ0 : (-Ty) ^ 2 - 4 * (b * Ny) * (-1) ≠ 0 := by
          intro h0
          apply disc_ne_zero_of_b_sq hq hcardK b hb_sq hb_ne y hy
          have h1 : algebraMap F K ((-Ty) ^ 2 - 4 * (b * Ny) * (-1)) = 0 := by rw [h0, map_zero]
          simp only [map_sub, map_pow, map_neg, map_mul, map_ofNat, map_one, hTy, hNy] at h1
          linear_combination h1
        have hcount : ((bundleOrbit F K D).filter (fun C => some y ∈ C)).card =
            (Finset.univ.filter (fun u : F => (b * Ny) * u ^ 2 + (-Ty) * u + (-1) = 0)).card := by
          have h1 : ((bundleOrbit F K D).filter (fun C => some y ∈ C)).card =
              (Finset.univ.filter (fun d : Fˣ => some y ∈ D.image (scaleOption F K d))).card := by
            unfold bundleOrbit
            rw [Finset.filter_image, Finset.card_image_of_injective _ horb_inj]
          rw [h1]
          let gmap : Fˣ → F := fun d => (d : F)⁻¹
          have hg_inj : Function.Injective gmap := by
            intro d₁ d₂ h; apply Units.ext; exact inv_injective h
          have hg_img :
              (Finset.univ.filter (fun d : Fˣ => some y ∈ D.image (scaleOption F K d))).image gmap =
              Finset.univ.filter (fun u : F => (b * Ny) * u ^ 2 + (-Ty) * u + (-1) = 0) := by
            ext u
            rw [Finset.mem_image]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, gmap]
            constructor
            · rintro ⟨d, hd, rfl⟩
              rw [scale_miquelianCircle_11b] at hd
              simp only [miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and,
                frob_algebraMap, map_pow] at hd
              apply (algebraMap F K).injective
              simp only [map_add, map_mul, map_pow, map_neg, map_one, map_inv₀, hNy, hTy, map_zero]
              have hdK : algebraMap F K (d : F) ≠ 0 :=
                (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr d.ne_zero
              apply mul_left_cancel₀ (pow_ne_zero 2 hdK)
              rw [mul_zero]
              field_simp [hdK]
              linear_combination hd
            · intro hu
              have hu0 : u ≠ 0 := by
                intro h0; rw [h0] at hu; norm_num at hu
              refine ⟨(Units.mk0 u hu0)⁻¹, ?_, by simp⟩
              rw [scale_miquelianCircle_11b]
              simp only [miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and,
                map_pow, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, inv_pow, frob_algebraMap]
              have huK : algebraMap F K u ≠ 0 :=
                (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr hu0
              have hu_eq : algebraMap F K ((b * Ny) * u ^ 2 + (-Ty) * u + (-1)) = 0 := by
                rw [hu, map_zero]
              simp only [map_add, map_mul, map_pow, map_neg, map_one, hNy, hTy] at hu_eq
              apply mul_left_cancel₀ (pow_ne_zero 2 huK)
              rw [mul_zero]
              field_simp [huK]
              linear_combination hu_eq
          rw [← hg_img, Finset.card_image_of_injective _ hg_inj]
        rw [hcount, quad_roots_count hq (b * Ny) (-Ty) (-1) (mul_ne_zero hb0 hNy0) hΔ0]
        split_ifs
        · right; rfl
        · left; rfl

/-- The `F`-linear map `T^n(x, y) = (β^n * x, β^(n*(q+2)) * y)` on `K × K`. -/
private def TLin (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (β : Kˣ) (n : ℕ) : (K × K) →ₗ[F] (K × K) where
  toFun p := ((β : K) ^ n * p.1, (β : K) ^ (n * (Fintype.card F + 2)) * p.2)
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' r p := by
    apply Prod.ext
    · change (β : K) ^ n * (r • p.1) = r • ((β : K) ^ n * p.1)
      rw [Algebra.smul_def, Algebra.smul_def]; ring
    · change (β : K) ^ (n * (Fintype.card F + 2)) * (r • p.2) =
        r • ((β : K) ^ (n * (Fintype.card F + 2)) * p.2)
      rw [Algebra.smul_def, Algebra.smul_def]; ring

private lemma TLin_injective {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (β : Kˣ) (n : ℕ) : Function.Injective (TLin F K β n) := by
  intro p q hpq
  have h1 := congrArg Prod.fst hpq
  have h2 := congrArg Prod.snd hpq
  dsimp [TLin] at h1 h2
  exact Prod.ext
    (mul_left_cancel₀ (pow_ne_zero _ β.ne_zero) h1)
    (mul_left_cancel₀ (pow_ne_zero _ β.ne_zero) h2)

private lemma TLin_comp {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (β : Kˣ) (m n : ℕ) :
    (TLin F K β m).comp (TLin F K β n) = TLin F K β (m + n) := by
  apply LinearMap.ext; intro p
  apply Prod.ext
  · simp only [LinearMap.comp_apply, TLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← mul_assoc, ← pow_add]
  · simp only [LinearMap.comp_apply, TLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← mul_assoc, ← pow_add, ← add_mul]

/-- The opposite-regulus line `L₀ = {(x, c * x + r * x^q) : x ∈ K}`. -/
private def oppLineMap (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (c r : K) : K →ₗ[F] (K × K) where
  toFun x := (x, c * x + r * x ^ Fintype.card F)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · dsimp; rw [frob_add (F := F)]; ring
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · change c * (a • x) + r * (a • x) ^ Fintype.card F = a • (c * x + r * x ^ Fintype.card F)
      rw [Algebra.smul_def, Algebra.smul_def, frob_mul (F := F), frob_algebraMap]
      ring

private lemma oppLineMap_injective {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (c r : K) : Function.Injective (oppLineMap F K c r) := by
  intro x y h
  exact congrArg Prod.fst h

private lemma finrank_oppLine {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hcardK : Fintype.card K = Fintype.card F ^ 2) (c r : K) :
    Module.finrank F (LinearMap.range (oppLineMap F K c r)) = 2 := by
  rw [LinearMap.finrank_range_of_inj (oppLineMap_injective c r), finrank_K_eq_two hcardK]

private lemma oppLine_isOpposite_11b {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (b : F) (hb0 : b ≠ 0) (r : K) (hr0 : r ≠ 0)
    (hr_norm : r * r ^ Fintype.card F = algebraMap F K ((b + 1) / b ^ 2)) :
    IsOppositeLine F K (miquelianCircle F K 1 1 b)
      (LinearMap.range (oppLineMap F K (algebraMap F K b)⁻¹ r)) := by
  set q := Fintype.card F
  have hbK : algebraMap F K b ≠ 0 :=
    (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr hb0
  refine ⟨finrank_oppLine hcardK _ r, ?_⟩
  intro k hk
  cases k with
  | none =>
    simp [miquelianCircle, hb0] at hk
  | some y =>
    have hy : algebraMap F K b * (y * y ^ q) - y - y ^ q - 1 = 0 := by
      simpa [miquelianCircle] using hk
    set u : K := (y - (algebraMap F K b)⁻¹) / r
    have hu_norm : u * u ^ q = 1 := by
      simp only [u, div_pow, div_mul_div_comm]
      rw [div_eq_one_iff_eq (mul_ne_zero hr0 (pow_ne_zero q hr0))]
      have h1 : (algebraMap F K b) ^ 2 * ((y - (algebraMap F K b)⁻¹) * (y - (algebraMap F K b)⁻¹) ^ q) =
          (algebraMap F K b) ^ 2 * (r * r ^ q) := by
        rw [frob_sub (F := F), inv_pow, frob_algebraMap, hr_norm, map_div₀, map_add, map_one, map_pow,
          mul_div_cancel₀ _ (pow_ne_zero 2 hbK)]
        have : (algebraMap F K b) ^ 2 * ((y - (algebraMap F K b)⁻¹) * (y ^ q - (algebraMap F K b)⁻¹)) =
            algebraMap F K b * (algebraMap F K b * (y * y ^ q) - y - y ^ q - 1) +
            (algebraMap F K b + 1) := by
          field_simp [hbK]; ring
        rw [this, hy, mul_zero, zero_add]
      exact mul_left_cancel₀ (pow_ne_zero 2 hbK) h1
    obtain ⟨x, hx0, hxq⟩ := exists_pow_q_sub_one_eq (F := F) hcardK u hu_norm
    have hmem_L : (x, (algebraMap F K b)⁻¹ * x + r * x ^ q) ∈
        LinearMap.range (oppLineMap F K (algebraMap F K b)⁻¹ r) := ⟨x, rfl⟩
    have hmem_S : (x, (algebraMap F K b)⁻¹ * x + r * x ^ q) ∈ spreadLine F K (some y) := by
      rw [mem_spreadLine_some]
      dsimp only
      rw [hxq]
      simp only [u]
      rw [← mul_assoc, mul_div_cancel₀ _ hr0]
      ring
    intro hbot
    have h0 : (x, (algebraMap F K b)⁻¹ * x + r * x ^ q) = (0, 0) := by
      have : (x, (algebraMap F K b)⁻¹ * x + r * x ^ q) ∈ (⊥ : Submodule F (K × K)) := by
        rw [← hbot]; exact ⟨hmem_L, hmem_S⟩
      exact (Submodule.mem_bot F).mp this
    exact hx0 (congrArg Prod.fst h0)

private lemma TLin_preserves_oppLine {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (β : Kˣ) (g : Fˣ) (hg : algebraMap F K (g : F) = (β : K) ^ (Fintype.card F + 1))
    (D : Finset (Option K)) (L : Submodule F (K × K)) (hL : IsOppositeLine F K D L) (n : ℕ) :
    IsOppositeLine F K (D.image (scaleOption F K (g ^ n))) (L.map (TLin F K β n)) := by
  set q := Fintype.card F
  refine ⟨?_, ?_⟩
  · rw [finrank_map_of_inj (TLin F K β n) (TLin_injective β n) L, hL.1]
  · intro k hk
    rcases Finset.mem_image.mp hk with ⟨w, hw, rfl⟩
    have hne := hL.2 w hw
    rw [Submodule.ne_bot_iff] at hne ⊢
    obtain ⟨p, ⟨hpL, hpS⟩, hp0⟩ := hne
    refine ⟨TLin F K β n p, ⟨Submodule.mem_map_of_mem hpL, ?_⟩, ?_⟩
    · cases w with
      | none =>
        rw [SetLike.mem_coe, mem_spreadLine_none] at hpS
        change ((β : K) ^ n * p.1) = 0
        rw [hpS, mul_zero]
      | some c =>
        rw [SetLike.mem_coe, mem_spreadLine_some] at hpS
        change (β : K) ^ (n * (q + 2)) * p.2 =
          algebraMap F K ((g ^ n : Fˣ) : F) * c * ((β : K) ^ n * p.1)
        rw [hpS, Units.val_pow_eq_pow_val, map_pow, hg, ← pow_mul]
        have hexp : n * (q + 2) = (q + 1) * n + n := by ring
        rw [hexp, pow_add]
        ring
    · intro h0
      exact hp0 (TLin_injective β n (h0.trans (map_zero _).symm))

/-- Core disjointness lemma (Dover Theorem 6.3): `L₀` and `T^n(L₀)` are disjoint for all
`0 < n < (q^2 - 1) / 2`. -/
private lemma TLin_oppLine_disjoint {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hq : Odd (Fintype.card F)) (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (β : Kˣ) (hβ : ∀ x : Kˣ, x ∈ Subgroup.zpowers β)
    (b : F) (hb_sq : IsSquare (b * (b + 1))) (hb_ne : b * (b + 1) ≠ 0)
    (r : K) (hr0 : r ≠ 0)
    (hr_norm : r * r ^ Fintype.card F = algebraMap F K ((b + 1) / b ^ 2))
    (n : ℕ) (hn0 : 0 < n) (hn_lt : n < (Fintype.card F ^ 2 - 1) / 2) :
    let L₀ := LinearMap.range (oppLineMap F K (algebraMap F K b)⁻¹ r)
    L₀ ⊓ L₀.map (TLin F K β n) = ⊥ := by
  set q := Fintype.card F
  have hq3 : 3 ≤ q := card_F_ge_three hq
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hb_ne
  have hb1 : b + 1 ≠ 0 := right_ne_zero_of_mul hb_ne
  have hbK : algebraMap F K b ≠ 0 :=
    (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr hb0
  have hordβ : orderOf β = q ^ 2 - 1 := orderOf_primitive_unit (F := F) hcardK β hβ
  obtain ⟨m, hm⟩ := hq
  have hq2_eq : q ^ 2 - 1 = 2 * (2 * m * (m + 1)) := by
    zify [show 1 ≤ q ^ 2 by nlinarith]; rw [hm]; push_cast; ring
  have h2n_lt : 2 * n < q ^ 2 - 1 := by omega
  intro L₀
  rw [Submodule.eq_bot_iff]
  rintro p ⟨hp1, hp2⟩
  rcases hp1 with ⟨u, hu⟩
  rcases hp2 with ⟨_, ⟨z, rfl⟩, hz⟩
  by_contra hp0
  have hz0 : z ≠ 0 := by
    intro h0; subst h0
    apply hp0
    rw [← hz, map_zero, map_zero]
  have hu_eq : u = (β : K) ^ n * z := by
    have h1 := congrArg Prod.fst (hu.trans hz.symm)
    simpa [oppLineMap, TLin] using h1
  have hy_eq : (algebraMap F K b)⁻¹ * u + r * u ^ q =
      (β : K) ^ (n * (q + 2)) * ((algebraMap F K b)⁻¹ * z + r * z ^ q) := by
    have h2 := congrArg Prod.snd (hu.trans hz.symm)
    simpa [oppLineMap, TLin] using h2
  rw [hu_eq, frob_mul (F := F)] at hy_eq
  set t : K := (β : K) ^ (n * (q + 1))
  set s : K := (β : K) ^ (n * (q - 1))
  have hts_eq : (1 - t) * z = algebraMap F K b * r * (t - s) * z ^ q := by
    have hstep1 : (β : K) ^ n * ((algebraMap F K b)⁻¹ * z + r * s * z ^ q) =
        (β : K) ^ n * (t * ((algebraMap F K b)⁻¹ * z + r * z ^ q)) := by
      have hexp1 : ((β : K) ^ n) ^ q = (β : K) ^ n * s := by
        rw [← pow_mul, ← pow_add]
        congr 1; zify [show 1 ≤ q by omega]; ring
      have hexp2 : (β : K) ^ (n * (q + 2)) = (β : K) ^ n * t := by
        rw [← pow_add]; congr 1; ring
      rw [hexp1, hexp2] at hy_eq
      linear_combination hy_eq
    have hstep2 := mul_left_cancel₀ (pow_ne_zero n β.ne_zero) hstep1
    have hstep3 : algebraMap F K b * ((algebraMap F K b)⁻¹ * z + r * s * z ^ q) =
        algebraMap F K b * (t * ((algebraMap F K b)⁻¹ * z + r * z ^ q)) :=
      congrArg (algebraMap F K b * ·) hstep2
    field_simp [hbK] at hstep3
    linear_combination hstep3
  have hts_ne : t - s ≠ 0 := by
    intro h0
    have hts : t = s := sub_eq_zero.mp h0
    have hpow : β ^ (2 * n) = 1 := by
      apply Units.ext
      have hexp : n * (q + 1) = n * (q - 1) + 2 * n := by zify [show 1 ≤ q by omega]; ring
      have h1 : (β : K) ^ (n * (q - 1)) * (β : K) ^ (2 * n) = (β : K) ^ (n * (q - 1)) * 1 := by
        rw [← pow_add, ← hexp, mul_one]; exact hts
      simpa using mul_left_cancel₀ (pow_ne_zero _ β.ne_zero) h1
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [hordβ] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have ht_ne1 : t ≠ 1 := by
    intro ht1
    have hzero_rhs : algebraMap F K b * r * (t - s) * z ^ q = 0 := by
      rw [← hts_eq, ht1, sub_self, zero_mul]
    have hne_rhs : algebraMap F K b * r * (t - s) * z ^ q ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hbK hr0) hts_ne) (pow_ne_zero q hz0)
    exact hne_rhs hzero_rhs
  have ht_in_F : t ^ q = t := by
    obtain ⟨g, hg⟩ := beta_pow_q_add_one_mem_F (F := F) hcardK β
    have ht_eq : t = algebraMap F K ((g : F) ^ n) := by
      rw [map_pow, hg, ← pow_mul, mul_comm (q + 1) n]
    rw [ht_eq, frob_algebraMap]
  have hs_norm : s * s ^ q = 1 := by
    simp only [s]
    rw [← pow_succ', ← pow_mul]
    have hexp : n * (q - 1) * (q + 1) = (q ^ 2 - 1) * n := by
      zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]; ring
    rw [hexp, pow_mul, ← Units.val_pow_eq_pow_val, ← hordβ, pow_orderOf_eq_one,
      Units.val_one, one_pow]
  have hnorm_eq : (1 - t) ^ 2 = algebraMap F K (b + 1) * (t ^ 2 - (s + s ^ q) * t + 1) := by
    have hnorm_lhs : ((1 - t) * z) * ((1 - t) * z) ^ q = (1 - t) ^ 2 * (z * z ^ q) := by
      rw [frob_mul (F := F), frob_sub (F := F), one_pow, ht_in_F]; ring
    have hnorm_rhs : (algebraMap F K b * r * (t - s) * z ^ q) *
        (algebraMap F K b * r * (t - s) * z ^ q) ^ q =
        algebraMap F K (b + 1) * (t ^ 2 - (s + s ^ q) * t + 1) * (z * z ^ q) := by
      rw [frob_mul (F := F), frob_mul (F := F), frob_mul (F := F), frob_algebraMap,
        frob_sub (F := F), ht_in_F, frob_frob (F := F) hcardK]
      have hbr : algebraMap F K b ^ 2 * (r * r ^ q) = algebraMap F K (b + 1) := by
        rw [hr_norm, map_div₀, map_pow, mul_div_cancel₀ _ (pow_ne_zero 2 hbK)]
      calc algebraMap F K b * r * (t - s) * z ^ q *
            (algebraMap F K b * r ^ q * (t - s ^ q) * z)
          = (algebraMap F K b ^ 2 * (r * r ^ q)) * (t ^ 2 - (s + s ^ q) * t + s * s ^ q) *
              (z * z ^ q) := by ring
        _ = algebraMap F K (b + 1) * (t ^ 2 - (s + s ^ q) * t + 1) * (z * z ^ q) := by
          rw [hbr, hs_norm]
    have hzz : z * z ^ q ≠ 0 := mul_ne_zero hz0 (pow_ne_zero q hz0)
    have hEq := congrArg (fun w : K => w * w ^ q) hts_eq
    rw [hnorm_lhs, hnorm_rhs] at hEq
    exact mul_right_cancel₀ hzz hEq
  have htr_id : (s + s ^ q - 2) * (algebraMap F K (b + 1) ^ 2 * t) =
      algebraMap F K (b * (b + 1)) * (t - 1) ^ 2 := by
    rw [map_add, map_one] at hnorm_eq
    rw [map_mul, map_add, map_one]
    linear_combination (algebraMap F K b + 1) * hnorm_eq
  have hs_ne1 : s ≠ 1 := by
    intro hs1
    have htr0 : s + s ^ q - 2 = 0 := by rw [hs1, one_pow]; ring
    rw [htr0, zero_mul] at htr_id
    have hne0 : algebraMap F K (b * (b + 1)) * (t - 1) ^ 2 ≠ 0 :=
      mul_ne_zero ((map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr hb_ne)
        (pow_ne_zero 2 (sub_ne_zero.mpr ht_ne1))
    exact hne0 htr_id.symm
  have h2m : 2 * m = q - 1 := by omega
  have hpow_rhs : (algebraMap F K (b * (b + 1)) * (t - 1) ^ 2) ^ m = 1 := by
    rcases hb_sq with ⟨w, hw⟩
    have hw0 : w ≠ 0 := by intro h0; rw [h0, mul_zero] at hw; exact hb_ne hw
    have ht1_in_F : ∃ c : F, algebraMap F K c = t - 1 := by
      rw [← frob_eq_self_iff, frob_sub (F := F), ht_in_F, one_pow]
    obtain ⟨c, hc⟩ := ht1_in_F
    have hc0 : c ≠ 0 := by
      intro h0; rw [h0, map_zero] at hc; exact sub_ne_zero.mpr ht_ne1 hc.symm
    have hrew : algebraMap F K (b * (b + 1)) * (t - 1) ^ 2 = algebraMap F K ((w * c) ^ 2) := by
      rw [hw, map_pow, map_mul, map_mul, hc]; ring
    rw [hrew, ← map_pow, ← pow_mul, h2m, FiniteField.pow_card_sub_one_eq_one _ (mul_ne_zero hw0 hc0),
      map_one]
  have hpow_b1 : (algebraMap F K (b + 1) ^ 2) ^ m = 1 := by
    rw [← pow_mul, h2m, ← map_pow, FiniteField.pow_card_sub_one_eq_one _ hb1, map_one]
  have htr_fact : (s + s ^ q - 2) * s = (s - 1) ^ 2 := by
    have : s ^ q * s = 1 := by rw [mul_comm]; exact hs_norm
    linear_combination this
  have hpow_s_lhs : (s + s ^ q - 2) ^ m * s ^ (m + 1) = -1 := by
    have h1 : (s + s ^ q - 2) ^ m * s ^ m * (s - 1) = (s - 1) ^ q := by
      rw [← mul_pow, htr_fact, ← pow_mul, ← pow_succ]
      congr 1; omega
    have h2 : (s - 1) ^ q = s ^ q - 1 := by rw [frob_sub (F := F), one_pow]
    have h3 : (s ^ q - 1) * s = -(s - 1) := by
      have : s ^ q * s = 1 := by rw [mul_comm]; exact hs_norm
      linear_combination this
    have h4 : (s + s ^ q - 2) ^ m * s ^ (m + 1) * (s - 1) = (-1) * (s - 1) := by
      calc (s + s ^ q - 2) ^ m * s ^ (m + 1) * (s - 1)
          = ((s + s ^ q - 2) ^ m * s ^ m * (s - 1)) * s := by rw [pow_succ]; ring
        _ = (s ^ q - 1) * s := by rw [h1, h2]
        _ = (-1) * (s - 1) := by rw [h3]; ring
    exact mul_right_cancel₀ (sub_ne_zero.mpr hs_ne1) h4
  have ht_eq_s_char : t ^ m = s ^ (m + 1) := by
    simp only [t, s, ← pow_mul]
    congr 1
    have hq_sub : q - 1 = 2 * m := by omega
    rw [hq_sub, hm]; ring
  have hpow_id := congrArg (· ^ m) htr_id
  rw [mul_pow, mul_pow, hpow_b1, one_mul, hpow_rhs, ht_eq_s_char, hpow_s_lhs] at hpow_id
  have h2zero : (2 : K) = 0 := by linear_combination -hpow_id
  exact two_ne_zero_K (F := F) ⟨m, hm⟩ h2zero

private lemma bakerEbert_isBruckReplaceable {F K : Type} [Field F] [Fintype F] [Field K]
    [Fintype K] [Algebra F K] (hq : Odd (Fintype.card F))
    (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (b : F) (hb_sq : IsSquare (b * (b + 1))) (hb_ne : b * (b + 1) ≠ 0) :
    IsBruckReplaceable F K (bundleOrbit F K (miquelianCircle F K 1 1 b)) := by
  set q := Fintype.card F
  have hq3 : 3 ≤ q := card_F_ge_three hq
  obtain ⟨k0, hk0⟩ := hq
  have hq_sub : q - 1 = 2 * k0 := by omega
  have hq_add_half : (q + 1) / 2 = k0 + 1 := by omega
  have hq2_eq : q ^ 2 - 1 = 2 * (2 * k0 * (k0 + 1)) := by
    zify [show 1 ≤ q ^ 2 by nlinarith]; rw [hk0]; push_cast; ring
  have hhalf_eq : (q - 1) * ((q + 1) / 2) = (q ^ 2 - 1) / 2 := by
    rw [hq_sub, hq_add_half, hq2_eq, Nat.mul_div_cancel_left _ (by omega)]
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hb_ne
  have hb1 : b + 1 ≠ 0 := right_ne_zero_of_mul hb_ne
  obtain ⟨β, hβ⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨g, hg⟩ := beta_pow_q_add_one_mem_F (F := F) hcardK β
  obtain ⟨hordg, hg_gen⟩ := beta_pow_q_add_one_gen_F hcardK β hβ g hg
  have hordβ : orderOf β = q ^ 2 - 1 := orderOf_primitive_unit (F := F) hcardK β hβ
  obtain ⟨r, hr0, hr_norm⟩ := norm_surjective hcardK ((b + 1) / b ^ 2)
    (div_ne_zero hb1 (pow_ne_zero 2 hb0))
  set D := miquelianCircle F K 1 1 b
  set L₀ := LinearMap.range (oppLineMap F K (algebraMap F K b)⁻¹ r)
  have hL₀_opp : IsOppositeLine F K D L₀ := oppLine_isOpposite_11b hcardK b hb0 r hr0 hr_norm
  have hT_disj : ∀ m n : ℕ, m < (q ^ 2 - 1) / 2 → n < (q ^ 2 - 1) / 2 → m ≠ n →
      L₀.map (TLin F K β m) ⊓ L₀.map (TLin F K β n) = ⊥ := by
    intro m n hm hn hne
    have hlt_case : ∀ a c : ℕ, a < c → c < (q ^ 2 - 1) / 2 →
        L₀.map (TLin F K β a) ⊓ L₀.map (TLin F K β c) = ⊥ := by
      intro a c hlt hc
      rw [Submodule.eq_bot_iff]
      rintro p ⟨hp1, hp2⟩
      rcases hp1 with ⟨u, huL, rfl⟩
      rcases hp2 with ⟨v, hvL, hv_eq⟩
      have hdiff : TLin F K β c v = TLin F K β a (TLin F K β (c - a) v) := by
        rw [← LinearMap.comp_apply, TLin_comp, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
      rw [hdiff] at hv_eq
      have hu_eq : TLin F K β (c - a) v = u := TLin_injective β a hv_eq
      have hbot := TLin_oppLine_disjoint ⟨k0, hk0⟩ hcardK β hβ b hb_sq hb_ne r hr0 hr_norm
        (c - a) (by omega) (by change c - a < (q ^ 2 - 1) / 2; omega)
      have hu0 : u = 0 := by
        have hmem : u ∈ L₀ ⊓ L₀.map (TLin F K β (c - a)) := ⟨huL, ⟨v, hvL, hu_eq⟩⟩
        rw [hbot] at hmem
        exact (Submodule.mem_bot F).mp hmem
      rw [hu0, map_zero]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hlt_case m n hlt hn
    · rw [inf_comm]; exact hlt_case n m hgt hm
  have hT_bruck : ∀ k j : ℕ,
      L₀.map (TLin F K β (k + j * (q - 1))) =
        (L₀.map (TLin F K β k)).map (bruckKernelMap F K ((β : K) ^ (j * (q - 1)))) := by
    intro k j
    rw [← Submodule.map_comp]
    congr 1
    apply LinearMap.ext; intro p
    apply Prod.ext
    · simp only [LinearMap.comp_apply, TLin, bruckKernelMap, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← mul_assoc, ← pow_add, add_comm]
    · simp only [LinearMap.comp_apply, TLin, bruckKernelMap, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← mul_assoc, ← pow_add]
      congr 1
      have hpow_eq : (β : K) ^ (j * (q - 1) * (q + 1)) = 1 := by
        have : j * (q - 1) * (q + 1) = (q ^ 2 - 1) * j := by
          zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]; ring
        rw [this, pow_mul, ← Units.val_pow_eq_pow_val, ← hordβ, pow_orderOf_eq_one,
          Units.val_one, one_pow]
      have hexp : (k + j * (q - 1)) * (q + 2) =
          j * (q - 1) + k * (q + 2) + j * (q - 1) * (q + 1) := by ring
      rw [hexp, pow_add, hpow_eq, mul_one]
  have hL₀_bruck_q1 : ∀ M : Submodule F (K × K),
      M.map (bruckKernelMap F K ((β : K) ^ (q + 1))) = M := by
    intro M
    ext p
    simp only [Submodule.mem_map, bruckKernelMap, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have : ((β : K) ^ (q + 1) * v.1, (β : K) ^ (q + 1) * v.2) = (g : F) • v := by
        apply Prod.ext
        · change (β : K) ^ (q + 1) * v.1 = (g : F) • v.1
          rw [Algebra.smul_def, hg]
        · change (β : K) ^ (q + 1) * v.2 = (g : F) • v.2
          rw [Algebra.smul_def, hg]
      rw [this]
      exact M.smul_mem (g : F) hv
    · intro hp
      refine ⟨(g : F)⁻¹ • p, M.smul_mem _ hp, ?_⟩
      have hgi : algebraMap F K (g : F) * algebraMap F K (g : F)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ g.ne_zero, map_one]
      apply Prod.ext
      · change (β : K) ^ (q + 1) * ((g : F)⁻¹ • p.1) = p.1
        rw [Algebra.smul_def, ← hg, ← mul_assoc, hgi, one_mul]
      · change (β : K) ^ (q + 1) * ((g : F)⁻¹ • p.2) = p.2
        rw [Algebra.smul_def, ← hg, ← mul_assoc, hgi, one_mul]
  have hC_idx : ∀ C ∈ bundleOrbit F K D, ∃ k : ℕ, k < q - 1 ∧ C = D.image (scaleOption F K (g ^ k)) := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨d, _, rfl⟩
    obtain ⟨z, hz⟩ := hg_gen d
    dsimp only at hz
    let k : ℕ := (z % ((q - 1 : ℕ) : ℤ)).toNat
    have hk_lt : k < q - 1 := by
      have hpos : (0 : ℤ) < ((q - 1 : ℕ) : ℤ) := by omega
      have := Int.emod_nonneg z (ne_of_gt hpos)
      have := Int.emod_lt_of_pos z hpos
      omega
    have hgk : g ^ k = d := by
      rw [← hz]
      have h1 : (k : ℤ) = z % ((q - 1 : ℕ) : ℤ) :=
        Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))
      rw [← zpow_natCast, h1, ← hordg, zpow_mod_orderOf]
    exact ⟨k, hk_lt, by rw [hgk]⟩
  let idxOf : Finset (Option K) → ℕ := fun C =>
    if h : C ∈ bundleOrbit F K D then (hC_idx C h).choose else 0
  have hidx_spec : ∀ C (h : C ∈ bundleOrbit F K D),
      idxOf C < q - 1 ∧ C = D.image (scaleOption F K (g ^ idxOf C)) := by
    intro C h
    simp only [idxOf, dif_pos h]
    exact (hC_idx C h).choose_spec
  let H : Finset (Option K) → Finset (Submodule F (K × K)) := fun C =>
    (Finset.range ((q + 1) / 2)).image (fun j => L₀.map (TLin F K β (idxOf C + j * (q - 1))))
  refine ⟨β, hβ, H, ?_, ?_⟩
  · intro C hC
    obtain ⟨hk_lt, hC_eq⟩ := hidx_spec C hC
    have hlt_bound : ∀ j < (q + 1) / 2, idxOf C + j * (q - 1) < (q ^ 2 - 1) / 2 := by
      intro j hj
      rw [← hhalf_eq]
      calc idxOf C + j * (q - 1) < (q - 1) + j * (q - 1) := by omega
        _ = (j + 1) * (q - 1) := by ring
        _ ≤ ((q + 1) / 2) * (q - 1) := Nat.mul_le_mul_right _ hj
        _ = (q - 1) * ((q + 1) / 2) := mul_comm _ _
    have hH_inj : Set.InjOn (fun j => L₀.map (TLin F K β (idxOf C + j * (q - 1))))
        (Finset.range ((q + 1) / 2) : Set ℕ) := by
      intro j₁ hj₁ j₂ hj₂ heq
      dsimp only at heq
      by_contra hne
      have hj₁' : j₁ < (q + 1) / 2 := Finset.mem_range.mp hj₁
      have hj₂' : j₂ < (q + 1) / 2 := Finset.mem_range.mp hj₂
      have hne_idx : idxOf C + j₁ * (q - 1) ≠ idxOf C + j₂ * (q - 1) := by
        intro h; apply hne
        have h' : j₁ * (q - 1) = j₂ * (q - 1) := Nat.add_left_cancel h
        exact Nat.eq_of_mul_eq_mul_right (by omega) h'
      have hbot := hT_disj _ _ (hlt_bound j₁ hj₁') (hlt_bound j₂ hj₂') hne_idx
      rw [heq, inf_idem] at hbot
      have hfin := (TLin_preserves_oppLine β g hg D L₀ hL₀_opp (idxOf C + j₂ * (q - 1))).1
      rw [hbot, finrank_bot] at hfin
      omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [H]
      rw [Finset.card_image_of_injOn hH_inj, Finset.card_range]
    · intro L hL
      rcases Finset.mem_image.mp hL with ⟨j, _, rfl⟩
      have hopp := TLin_preserves_oppLine β g hg D L₀ hL₀_opp (idxOf C + j * (q - 1))
      have hpowg : g ^ (idxOf C + j * (q - 1)) = g ^ idxOf C := by
        rw [pow_add, pow_mul', ← hordg, pow_orderOf_eq_one, one_pow, mul_one]
      rw [hpowg, ← hC_eq] at hopp
      exact hopp
    · set M := L₀.map (TLin F K β (idxOf C))
      refine ⟨M, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp [M]⟩, ?_⟩
      intro L
      have hM_period : ∀ a c : ℕ, a % (q + 1) = c % (q + 1) →
          M.map (bruckKernelMap F K ((β : K) ^ a)) = M.map (bruckKernelMap F K ((β : K) ^ c)) := by
        have hstep : ∀ s : ℕ, M.map (bruckKernelMap F K ((β : K) ^ (s + (q + 1)))) =
            M.map (bruckKernelMap F K ((β : K) ^ s)) := by
          intro s
          have hcomp : bruckKernelMap F K ((β : K) ^ (s + (q + 1))) =
              (bruckKernelMap F K ((β : K) ^ s)).comp (bruckKernelMap F K ((β : K) ^ (q + 1))) := by
            apply LinearMap.ext; intro p
            apply Prod.ext <;> simp [bruckKernelMap, pow_add, mul_assoc]
          rw [hcomp, Submodule.map_comp, hL₀_bruck_q1 M]
        have hmod : ∀ s : ℕ, M.map (bruckKernelMap F K ((β : K) ^ s)) =
            M.map (bruckKernelMap F K ((β : K) ^ (s % (q + 1)))) := by
          intro s
          conv_lhs => rw [← Nat.mod_add_div s (q + 1)]
          induction (s / (q + 1)) with
          | zero => simp
          | succ t ih =>
            rw [Nat.mul_succ, ← add_assoc, hstep, ih]
        intro a c hac
        rw [hmod a, hmod c, hac]
      constructor
      · intro hL
        rcases Finset.mem_image.mp hL with ⟨j, _, rfl⟩
        rw [hT_bruck]
        refine ⟨j * k0, ?_⟩
        have : j * (q - 1) = 2 * (j * k0) := by rw [hq_sub]; ring
        rw [this]
      · rintro ⟨m, rfl⟩
        set h : ℕ := (q + 1) / 2
        have hh_pos : 0 < h := by omega
        have h2h : 2 * h = q + 1 := by omega
        let j : ℕ := (h - m % h) % h
        have hj_lt : j < h := Nat.mod_lt _ hh_pos
        refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj_lt, ?_⟩
        rw [hT_bruck]
        apply hM_period
        have hcong : (j * (q - 1) + 2 * j) % (2 * h) = (2 * m + 2 * j) % (2 * h) := by
          have hlhs : j * (q - 1) + 2 * j = j * (2 * h) := by
            have : q - 1 + 2 = 2 * h := by omega
            calc j * (q - 1) + 2 * j = j * (q - 1 + 2) := by ring
              _ = j * (2 * h) := by rw [this]
          have hrhs_div : h ∣ (m + j) := by
            have h1 : m % h + j = if m % h = 0 then 0 else h := by
              dsimp only [j]
              split_ifs with h0
              · rw [h0, Nat.sub_zero, Nat.mod_self, add_zero]
              · have hlt : m % h < h := Nat.mod_lt m hh_pos
                have hsub : h - m % h < h := by omega
                rw [Nat.mod_eq_of_lt hsub]
                omega
            have h2 : h ∣ m % h + j := by
              rw [h1]; split_ifs
              · exact dvd_zero h
              · exact dvd_refl h
            have h3 : m + j = h * (m / h) + (m % h + j) := by
              have := Nat.div_add_mod m h; omega
            rw [h3]
            exact dvd_add (dvd_mul_right h _) h2
          obtain ⟨t, ht⟩ := hrhs_div
          have hrhs : 2 * m + 2 * j = t * (2 * h) := by
            calc 2 * m + 2 * j = 2 * (m + j) := by ring
              _ = 2 * (h * t) := by rw [ht]
              _ = t * (2 * h) := by ring
          rw [hlhs, hrhs, Nat.mul_mod_left, Nat.mul_mod_left]
        rw [← h2h]
        have hcancel : ∀ a c e : ℕ, (a + e) % (2 * h) = (c + e) % (2 * h) → a % (2 * h) = c % (2 * h) := by
          intro a c e hae
          have hmod : (a + e : ℕ) ≡ (c + e : ℕ) [MOD (2 * h)] := hae
          exact Nat.ModEq.add_right_cancel' e hmod
        exact hcancel _ _ (2 * j) hcong
  · intro C₁ hC₁ L₁ hL₁ C₂ hC₂ L₂ hL₂ hne
    rcases Finset.mem_image.mp hL₁ with ⟨j₁, hj₁, rfl⟩
    rcases Finset.mem_image.mp hL₂ with ⟨j₂, hj₂, rfl⟩
    have hj₁' : j₁ < (q + 1) / 2 := Finset.mem_range.mp hj₁
    have hj₂' : j₂ < (q + 1) / 2 := Finset.mem_range.mp hj₂
    obtain ⟨hk₁, hC₁_eq⟩ := hidx_spec C₁ hC₁
    obtain ⟨hk₂, hC₂_eq⟩ := hidx_spec C₂ hC₂
    have hlt₁ : idxOf C₁ + j₁ * (q - 1) < (q ^ 2 - 1) / 2 := by
      rw [← hhalf_eq]
      calc idxOf C₁ + j₁ * (q - 1) < (q - 1) + j₁ * (q - 1) := by omega
        _ = (j₁ + 1) * (q - 1) := by ring
        _ ≤ ((q + 1) / 2) * (q - 1) := Nat.mul_le_mul_right _ hj₁'
        _ = (q - 1) * ((q + 1) / 2) := mul_comm _ _
    have hlt₂ : idxOf C₂ + j₂ * (q - 1) < (q ^ 2 - 1) / 2 := by
      rw [← hhalf_eq]
      calc idxOf C₂ + j₂ * (q - 1) < (q - 1) + j₂ * (q - 1) := by omega
        _ = (j₂ + 1) * (q - 1) := by ring
        _ ≤ ((q + 1) / 2) * (q - 1) := Nat.mul_le_mul_right _ hj₂'
        _ = (q - 1) * ((q + 1) / 2) := mul_comm _ _
    have hidx_ne : idxOf C₁ + j₁ * (q - 1) ≠ idxOf C₂ + j₂ * (q - 1) := by
      intro heq
      rcases hne with hCne | hLne
      · have hmod := congrArg (· % (q - 1)) heq
        rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt hk₁, Nat.mod_eq_of_lt hk₂] at hmod
        apply hCne
        rw [hC₁_eq, hC₂_eq, hmod]
      · exact hLne (by rw [heq])
    exact hT_disj _ _ hlt₁ hlt₂ hidx_ne

/-! ### Part 3: Companion disjoint `(q-1)`-nest (Theorem 6.4) -/

private lemma companion_nest_exists {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hq : Odd (Fintype.card F)) (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (b : F) (hb_sq : IsSquare (b * (b + 1))) (hb_ne : b * (b + 1) ≠ 0) :
    let q := Fintype.card F
    let D := miquelianCircle F K 1 1 b
    let N := bundleOrbit F K D
    ∃ D' : Finset (Option K),
      let N' := bundleOrbit F K D'
      IsNest F K (q - 1) N' ∧
      IsBruckReplaceable F K N' ∧
      (∀ C ∈ N, ∀ C' ∈ N', Disjoint C C') := by
  set q := Fintype.card F
  have hq3 : 3 ≤ q := card_F_ge_three hq
  obtain ⟨k0, hk0⟩ := hq
  have hk0_pos : 1 ≤ k0 := by omega
  have hq2_eq : q ^ 2 - 1 = 2 * (2 * k0 * (k0 + 1)) := by
    zify [show 1 ≤ q ^ 2 by nlinarith]; rw [hk0]; push_cast; ring
  have hq2_half : (q ^ 2 - 1) / 2 = 2 * k0 * (k0 + 1) := by
    rw [hq2_eq, Nat.mul_div_cancel_left _ (by omega)]
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hb_ne
  have hb1 : b + 1 ≠ 0 := right_ne_zero_of_mul hb_ne
  obtain ⟨β, hβ⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨g, hg⟩ := beta_pow_q_add_one_mem_F (F := F) hcardK β
  obtain ⟨hordg, _⟩ := beta_pow_q_add_one_gen_F hcardK β hβ g hg
  have hordβ : orderOf β = q ^ 2 - 1 := orderOf_primitive_unit (F := F) hcardK β hβ
  set ε : K := (β : K) ^ (k0 + 1)
  have hε0 : ε ≠ 0 := pow_ne_zero _ β.ne_zero
  have hε_sq : ε ^ 2 = algebraMap F K (g : F) := by
    simp only [ε, ← pow_mul, hg]
    congr 1; omega
  have hε_frob : ε ^ q = -ε := by
    have hpow : β ^ (2 * k0 * (k0 + 1)) = -1 := by
      have hsq : (β ^ (2 * k0 * (k0 + 1))) ^ 2 = 1 := by
        rw [← pow_mul]
        have h2 : 2 * k0 * (k0 + 1) * 2 = q ^ 2 - 1 := by rw [hq2_eq]; ring
        rw [h2, ← hordβ, pow_orderOf_eq_one]
      have hne1 : β ^ (2 * k0 * (k0 + 1)) ≠ 1 := by
        intro h1
        have hdvd := orderOf_dvd_of_pow_eq_one h1
        rw [hordβ, hq2_eq] at hdvd
        have hle := Nat.le_of_dvd (by nlinarith) hdvd
        nlinarith
      have hval : ((β ^ (2 * k0 * (k0 + 1)) : Kˣ) : K) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
      rcases sq_eq_one_iff.mp hval with h1 | hm1
      · exact absurd (Units.ext h1) hne1
      · exact Units.ext hm1
    have h1 : ε ^ q = ε * ((β ^ (2 * k0 * (k0 + 1)) : Kˣ) : K) := by
      simp only [ε, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_add]
      congr 1
      rw [hk0]; ring
    rw [h1, hpow, Units.val_neg, Units.val_one, mul_neg_one]
  have hg_nonsq : ¬ IsSquare (g : F) := by
    rintro ⟨u, hu⟩
    have hu0 : u ≠ 0 := by intro h0; rw [h0, mul_zero] at hu; exact g.ne_zero hu
    have hpow : g ^ k0 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, hu, ← sq, ← pow_mul]
      have : 2 * k0 = q - 1 := by omega
      rw [this, FiniteField.pow_card_sub_one_eq_one _ hu0]
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [hordg] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  let D' := miquelianCircle F K ε ((b + 1) * (g : F)) 1
  let E := miquelianCircle F K 1 1 (-1 - b)
  have hmb_ne : (-1 - b) * ((-1 - b) + 1) ≠ 0 := by
    have : (-1 - b) * ((-1 - b) + 1) = b * (b + 1) := by ring
    rwa [this]
  have hmb_sq : IsSquare ((-1 - b) * ((-1 - b) + 1)) := by
    have : (-1 - b) * ((-1 - b) + 1) = b * (b + 1) := by ring
    rwa [this]
  have hE_nest := bakerEbert_isNest ⟨k0, hk0⟩ hcardK (-1 - b) hmb_sq hmb_ne
  have hE_bruck := bakerEbert_isBruckReplaceable ⟨k0, hk0⟩ hcardK (-1 - b) hmb_sq hmb_ne
  let ν : (K × K) →ₗ[F] (K × K) :=
    { toFun := fun p => (p.2, -ε * p.1)
      map_add' := fun p q => by
        apply Prod.ext
        · rfl
        · change -ε * (p.1 + q.1) = -ε * p.1 + -ε * q.1; ring
      map_smul' := fun r p => by
        apply Prod.ext
        · rfl
        · change -ε * (r • p.1) = r • (-ε * p.1)
          rw [Algebra.smul_def, Algebra.smul_def]; ring }
  have hν_inj : Function.Injective ν := by
    intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp [ν] at h1 h2
    exact Prod.ext (mul_left_cancel₀ (neg_ne_zero.mpr hε0) h2) h1
  let νOpt : Option K → Option K
    | none => some 0
    | some z => if z = 0 then none else some (-ε / z)
  have hνOpt_invol : ∀ k : Option K, νOpt (νOpt k) = k := by
    intro k
    cases k with
    | none => simp [νOpt]
    | some z =>
      by_cases hz : z = 0
      · subst hz; simp [νOpt]
      · simp only [νOpt, if_neg hz, if_neg (div_ne_zero (neg_ne_zero.mpr hε0) hz),
          div_div_eq_mul_div, mul_div_cancel_left₀ _ (neg_ne_zero.mpr hε0)]
  have hνOpt_inj : Function.Injective νOpt := Function.LeftInverse.injective hνOpt_invol
  have hν_spread : ∀ k : Option K, (spreadLine F K k).map ν = spreadLine F K (νOpt k) := by
    intro k
    ext p
    simp only [Submodule.mem_map, ν, LinearMap.coe_mk, AddHom.coe_mk]
    cases k with
    | none =>
      simp only [νOpt, mem_spreadLine_none, mem_spreadLine_some, zero_mul]
      constructor
      · rintro ⟨⟨x, y⟩, hx, rfl⟩; dsimp at hx ⊢; rw [hx, mul_zero]
      · intro hp2; exact ⟨(0, p.1), rfl, by ext <;> simp [hp2]⟩
    | some z =>
      by_cases hz : z = 0
      · subst hz
        simp only [νOpt, ↓reduceIte, mem_spreadLine_none, mem_spreadLine_some, zero_mul]
        constructor
        · rintro ⟨⟨x, y⟩, hy, rfl⟩; exact hy
        · intro hp1; exact ⟨(-p.2 / ε, 0), rfl, by ext <;> [exact hp1.symm; field_simp [hε0]]⟩
      · simp only [νOpt, if_neg hz, mem_spreadLine_some]
        constructor
        · rintro ⟨⟨x, y⟩, hy, rfl⟩; dsimp at hy ⊢; rw [hy]; field_simp [hz]
        · intro hp; refine ⟨(p.1 / z, p.1), by dsimp; field_simp [hz], ?_⟩
          apply Prod.ext
          · rfl
          · dsimp; rw [hp]; field_simp [hz]
  have hνOpt_E : E.image νOpt = D' := by
    ext k
    simp only [Finset.mem_image]
    have hE_ne0 : ∀ w ∈ E, w ≠ none ∧ w ≠ some 0 := by
      intro w hw
      cases w with
      | none =>
        simp only [E, miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        exact absurd (by linear_combination -hw : b + 1 = 0) hb1
      | some z =>
        refine ⟨Option.some_ne_none _, ?_⟩
        intro h0
        have hz0 : z = 0 := Option.some.inj h0
        subst hz0
        simp [E, miquelianCircle] at hw
    have hD'_ne0 : ∀ w ∈ D', w ≠ none ∧ w ≠ some 0 := by
      intro w hw
      cases w with
      | none => simp [D', miquelianCircle] at hw
      | some z =>
        refine ⟨Option.some_ne_none _, ?_⟩
        intro h0
        have hz0 : z = 0 := Option.some.inj h0
        subst hz0
        simp only [D', miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and,
          zero_pow Fintype.card_ne_zero, mul_zero, sub_zero, zero_sub, neg_eq_zero] at hw
        exact mul_ne_zero hb1 g.ne_zero
          ((map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective).mp hw)
    have hε_frob' : ε ^ Fintype.card F = -ε := hε_frob
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hne := hE_ne0 w hw
      cases w with
      | none => exact absurd rfl hne.1
      | some z =>
        have hz0 : z ≠ 0 := fun h => hne.2 (congrArg some h)
        simp only [νOpt, if_neg hz0, D', miquelianCircle, Finset.mem_filter, Finset.mem_univ,
          true_and, map_one, one_mul, map_mul, ← hε_sq]
        simp only [E, miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and,
          one_pow, one_mul, map_one, map_sub, map_neg] at hw
        rw [div_pow, frob_neg (F := F), hε_frob', neg_neg, map_add, map_one]
        field_simp [hz0, pow_ne_zero q hz0]
        linear_combination ε ^ 2 * hw
    · intro hk
      have hne := hD'_ne0 k hk
      cases k with
      | none => exact absurd rfl hne.1
      | some x =>
        have hx0 : x ≠ 0 := fun h => hne.2 (congrArg some h)
        refine ⟨some (-ε / x), ?_, ?_⟩
        · simp only [E, miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and,
            one_pow, one_mul, map_one, map_sub, map_neg]
          simp only [D', miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and,
            map_one, one_mul, hε_frob', map_mul, map_add, map_one, ← hε_sq] at hk
          rw [div_pow, frob_neg (F := F), hε_frob', neg_neg]
          field_simp [hx0, pow_ne_zero q hx0]
          linear_combination -hk
        · simp only [νOpt, if_neg (div_ne_zero (neg_ne_zero.mpr hε0) hx0),
            div_div_eq_mul_div, mul_div_cancel_left₀ _ (neg_ne_zero.mpr hε0)]
  have hνOpt_scale : ∀ (d : Fˣ) (k : Option K),
      νOpt (scaleOption F K d k) = scaleOption F K d⁻¹ (νOpt k) := by
    intro d k
    cases k with
    | none => simp [scaleOption, νOpt]
    | some z =>
      by_cases hz : z = 0
      · subst hz; simp [scaleOption, νOpt]
      · have hdK : algebraMap F K (d : F) ≠ 0 :=
          (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr d.ne_zero
        simp only [scaleOption, νOpt, if_neg hz, if_neg (mul_ne_zero hdK hz),
          Units.val_inv_eq_inv_val, map_inv₀, Option.some.injEq]
        field_simp [hdK, hz]
  have horb_img : bundleOrbit F K D' = (bundleOrbit F K E).image (fun C => C.image νOpt) := by
    ext C
    simp only [bundleOrbit, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨E.image (scaleOption F K d⁻¹), ⟨d⁻¹, rfl⟩, ?_⟩
      rw [← hνOpt_E, Finset.image_image, Finset.image_image]
      refine Finset.image_congr (fun k _ => ?_)
      simp [Function.comp, hνOpt_scale]
    · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
      refine ⟨d⁻¹, ?_⟩
      rw [← hνOpt_E, Finset.image_image, Finset.image_image]
      refine Finset.image_congr (fun k _ => ?_)
      simp [Function.comp, hνOpt_scale]
  have hImg_inj : Function.Injective (fun C : Finset (Option K) => C.image νOpt) := by
    intro C₁ C₂ h
    ext k
    have := Finset.ext_iff.mp h (νOpt k)
    simp only [Finset.mem_image] at this
    constructor
    · intro hk
      obtain ⟨w, hw, hwk⟩ := this.mp ⟨k, hk, rfl⟩
      rwa [hνOpt_inj hwk] at hw
    · intro hk
      obtain ⟨w, hw, hwk⟩ := this.mpr ⟨k, hk, rfl⟩
      rwa [hνOpt_inj hwk] at hw
  have hinv_img : ∀ C₀ : Finset (Option K), (C₀.image νOpt).image νOpt = C₀ := by
    intro C₀
    rw [Finset.image_image]
    simpa only [Function.comp_def, hνOpt_invol] using Finset.image_id' (s := C₀)
  refine ⟨D', ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [horb_img, Finset.card_image_of_injective _ hImg_inj, hE_nest.1]
    · intro C hC
      rcases Finset.mem_image.mp hC with ⟨d, _, rfl⟩
      refine ⟨algebraMap F K (d : F) * ε, (d : F) ^ 2 * ((b + 1) * (g : F)), 1, ?_, ?_⟩
      · rw [frob_mul (F := F), frob_algebraMap, hε_frob, mul_one, map_mul, map_mul, map_pow, ← hε_sq]
        have hfac : algebraMap F K (d : F) * ε * (algebraMap F K (d : F) * -ε) +
            algebraMap F K (d : F) ^ 2 * (algebraMap F K (b + 1) * ε ^ 2) =
            algebraMap F K ((d : F) ^ 2 * b) * ε ^ 2 := by
          rw [map_mul, map_pow, map_add, map_one]; ring
        rw [hfac]
        exact mul_ne_zero
          ((map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr
            (mul_ne_zero (pow_ne_zero 2 d.ne_zero) hb0))
          (pow_ne_zero 2 hε0)
      · ext k
        simp only [Finset.mem_image, D', miquelianCircle, Finset.mem_filter, Finset.mem_univ,
          true_and, map_one, one_mul, one_ne_zero]
        cases k with
        | none =>
          constructor
          · rintro ⟨w, hw, hsw⟩
            cases w with
            | none => exact hw
            | some x => simp [scaleOption] at hsw
          · exact False.elim
        | some y =>
          dsimp only
          have hdK : algebraMap F K (d : F) ≠ 0 :=
            (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr d.ne_zero
          constructor
          · rintro ⟨w, hw, hsw⟩
            cases w with
            | none => simp [scaleOption] at hsw
            | some x =>
              dsimp only at hw
              have hy : algebraMap F K (d : F) * x = y := Option.some.inj hsw
              rw [← hy, frob_mul (F := F), frob_mul (F := F), frob_algebraMap, map_mul, map_pow]
              calc algebraMap F K (d : F) * x * (algebraMap F K (d : F) * x ^ q) -
                    algebraMap F K (d : F) * ε ^ q * (algebraMap F K (d : F) * x) -
                    algebraMap F K (d : F) * ε * (algebraMap F K (d : F) * x ^ q) -
                    algebraMap F K (d : F) ^ 2 * algebraMap F K ((b + 1) * (g : F))
                  = algebraMap F K (d : F) ^ 2 *
                      (x * x ^ q - ε ^ q * x - ε * x ^ q - algebraMap F K ((b + 1) * (g : F))) := by ring
                _ = 0 := by rw [hw, mul_zero]
          · intro hy
            refine ⟨some (algebraMap F K (d : F)⁻¹ * y), ?_, ?_⟩
            · dsimp only
              rw [frob_mul (F := F), frob_algebraMap]
              rw [frob_mul (F := F), frob_algebraMap, map_mul, map_pow] at hy
              apply mul_left_cancel₀ (pow_ne_zero 2 hdK)
              rw [mul_zero]
              have hdi : algebraMap F K (d : F) * algebraMap F K (d : F)⁻¹ = 1 := by
                rw [← map_mul, mul_inv_cancel₀ d.ne_zero, map_one]
              calc algebraMap F K (d : F) ^ 2 *
                    (algebraMap F K (d : F)⁻¹ * y * (algebraMap F K (d : F)⁻¹ * y ^ q) -
                      ε ^ q * (algebraMap F K (d : F)⁻¹ * y) -
                      ε * (algebraMap F K (d : F)⁻¹ * y ^ q) -
                      algebraMap F K ((b + 1) * (g : F)))
                  = (algebraMap F K (d : F) * algebraMap F K (d : F)⁻¹) ^ 2 * (y * y ^ Fintype.card F) -
                    algebraMap F K (d : F) * ε ^ Fintype.card F * ((algebraMap F K (d : F) * algebraMap F K (d : F)⁻¹) * y) -
                    algebraMap F K (d : F) * ε * ((algebraMap F K (d : F) * algebraMap F K (d : F)⁻¹) * y ^ Fintype.card F) -
                    algebraMap F K (d : F) ^ 2 * algebraMap F K ((b + 1) * (g : F)) := by simp only [q]; ring
                _ = 0 := by rw [hdi, one_pow, one_mul, one_mul, one_mul]; exact hy
            · simp only [scaleOption, ← mul_assoc, ← map_mul, mul_inv_cancel₀ d.ne_zero, map_one, one_mul]
    · intro k
      have hfilt : ((bundleOrbit F K D').filter (fun C => k ∈ C)).card =
          ((bundleOrbit F K E).filter (fun C => νOpt k ∈ C)).card := by
        rw [horb_img, Finset.filter_image, Finset.card_image_of_injective _ hImg_inj]
        congr 1
        ext C
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨hC, w, hw, hwk⟩
          refine ⟨hC, ?_⟩
          have : νOpt k = w := by rw [← hwk, hνOpt_invol]
          rwa [this]
        · rintro ⟨hC, hk'⟩
          exact ⟨hC, νOpt k, hk', hνOpt_invol k⟩
      rw [hfilt]
      exact hE_nest.2.2 (νOpt k)
  · rcases hE_bruck with ⟨β₀, hβ₀, HE, hHE_spec, hHE_disj⟩
    have hν_bruck : ∀ γ : K, ν.comp (bruckKernelMap F K γ) = (bruckKernelMap F K γ).comp ν := by
      intro γ; apply LinearMap.ext; intro p
      apply Prod.ext
      · simp [ν, bruckKernelMap]
      · simp [ν, bruckKernelMap]; ring
    have hν_map_inj : Function.Injective (fun L : Submodule F (K × K) => L.map ν) := by
      intro L₁ L₂ h
      ext p
      have := SetLike.ext_iff.mp h (ν p)
      simp only [Submodule.mem_map] at this
      constructor
      · intro hp
        obtain ⟨w, hw, hwp⟩ := this.mp ⟨p, hp, rfl⟩
        rwa [hν_inj hwp] at hw
      · intro hp
        obtain ⟨w, hw, hwp⟩ := this.mpr ⟨p, hp, rfl⟩
        rwa [hν_inj hwp] at hw
    let H' : Finset (Option K) → Finset (Submodule F (K × K)) :=
      fun C => (HE (C.image νOpt)).image (fun L => L.map ν)
    refine ⟨β₀, hβ₀, H', ?_, ?_⟩
    · intro C hC
      rw [horb_img] at hC
      rcases Finset.mem_image.mp hC with ⟨C₀, hC₀, rfl⟩
      obtain ⟨hcard, hopp, ⟨L₀, hL₀_mem, hL₀_orb⟩⟩ := hHE_spec C₀ hC₀
      refine ⟨?_, ?_, ?_⟩
      · simp only [H', hinv_img]
        rw [Finset.card_image_of_injective _ hν_map_inj, hcard]
      · intro L hL
        simp only [H', hinv_img] at hL
        rcases Finset.mem_image.mp hL with ⟨M, hM, rfl⟩
        have hM_opp := hopp M hM
        refine ⟨?_, ?_⟩
        · rw [finrank_map_of_inj ν hν_inj M, hM_opp.1]
        · intro k hk
          rcases Finset.mem_image.mp hk with ⟨w, hw, rfl⟩
          have hne := hM_opp.2 w hw
          rw [Submodule.ne_bot_iff] at hne ⊢
          obtain ⟨p, ⟨hpM, hpS⟩, hp0⟩ := hne
          refine ⟨ν p, ⟨Submodule.mem_map_of_mem hpM, ?_⟩, fun h0 => hp0 (hν_inj (h0.trans (map_zero _).symm))⟩
          rw [← hν_spread w]
          exact Submodule.mem_map_of_mem hpS
      · refine ⟨L₀.map ν, ?_, ?_⟩
        · simp only [H', hinv_img]; exact Finset.mem_image_of_mem _ hL₀_mem
        · intro L
          simp only [H', hinv_img, Finset.mem_image]
          constructor
          · rintro ⟨M, hM, rfl⟩
            obtain ⟨j, rfl⟩ := (hL₀_orb M).mp hM
            refine ⟨j, ?_⟩
            rw [← Submodule.map_comp, hν_bruck, Submodule.map_comp]
          · rintro ⟨j, rfl⟩
            refine ⟨L₀.map (bruckKernelMap F K ((β₀ : K) ^ (2 * j))), (hL₀_orb _).mpr ⟨j, rfl⟩, ?_⟩
            rw [← Submodule.map_comp, hν_bruck, Submodule.map_comp]
    · intro C₁ hC₁ L₁ hL₁ C₂ hC₂ L₂ hL₂ hne
      rw [horb_img] at hC₁ hC₂
      rcases Finset.mem_image.mp hC₁ with ⟨C₁₀, hC₁₀, rfl⟩
      rcases Finset.mem_image.mp hC₂ with ⟨C₂₀, hC₂₀, rfl⟩
      simp only [H', hinv_img, Finset.mem_image] at hL₁ hL₂
      rcases hL₁ with ⟨M₁, hM₁, rfl⟩
      rcases hL₂ with ⟨M₂, hM₂, rfl⟩
      have hne₀ : C₁₀ ≠ C₂₀ ∨ M₁ ≠ M₂ := by
        rcases hne with hC | hL
        · left; exact fun h => hC (by rw [h])
        · right; exact fun h => hL (by rw [h])
      have hbot := hHE_disj C₁₀ hC₁₀ M₁ hM₁ C₂₀ hC₂₀ M₂ hM₂ hne₀
      rw [Submodule.eq_bot_iff]
      rintro p ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
      have huv : u = v := hν_inj hvu.symm
      subst huv
      have hu0 : u = 0 := by
        have : u ∈ M₁ ⊓ M₂ := ⟨hu, hv⟩
        rw [hbot] at this
        exact (Submodule.mem_bot F).mp this
      rw [hu0, map_zero]
  · intro C hC C' hC'
    rw [Finset.disjoint_left]
    intro k hkC hkC'
    rcases Finset.mem_image.mp hC with ⟨d₁, _, rfl⟩
    rcases Finset.mem_image.mp hC' with ⟨d₂, _, rfl⟩
    cases k with
    | none =>
      rw [scale_miquelianCircle_11b] at hkC
      simp [miquelianCircle, hb0] at hkC
    | some y =>
      have hy0 : y ≠ 0 := by
        intro hy; subst hy
        rw [scale_miquelianCircle_11b] at hkC
        simp only [miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and,
          zero_pow Fintype.card_ne_zero, mul_zero, sub_zero, zero_sub, neg_eq_zero] at hkC
        exact pow_ne_zero 2 d₁.ne_zero
          ((map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective).mp hkC)
      rw [scale_miquelianCircle_11b] at hkC
      simp only [miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and,
        frob_algebraMap, map_pow] at hkC
      rcases Finset.mem_image.mp hkC' with ⟨w, hw, hsw⟩
      cases w with
      | none => simp [scaleOption] at hsw
      | some x =>
        have hxy : algebraMap F K (d₂ : F) * x = y := Option.some.inj hsw
        have hε_frob' : ε ^ Fintype.card F = -ε := hε_frob
        simp only [D', miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and,
          map_one, one_mul, hε_frob'] at hw
        obtain ⟨Ny, hNy⟩ := norm_mem_F hcardK y
        obtain ⟨Ty, hTy⟩ := trace_mem_F hcardK y
        have hUy_mem : ∃ Uy : F, algebraMap F K Uy = ε * (y - y ^ q) := by
          rw [← frob_eq_self_iff, frob_mul (F := F), frob_sub (F := F), hε_frob,
            frob_frob (F := F) hcardK]; ring
        obtain ⟨Uy, hUy⟩ := hUy_mem
        set Δ : F := Ty ^ 2 + 4 * b * Ny
        have hΔ_ne : Δ ≠ 0 := by
          intro h0
          apply disc_ne_zero_of_b_sq ⟨k0, hk0⟩ hcardK b hb_sq hb_ne y hy0
          have h1 : algebraMap F K Δ = 0 := by rw [h0, map_zero]
          simp only [Δ, map_add, map_pow, map_mul, map_ofNat, hTy, hNy] at h1
          exact h1
        have hΔ_sq : IsSquare Δ := by
          refine ⟨2 * b * Ny * (d₁ : F)⁻¹ - Ty, ?_⟩
          apply (algebraMap F K).injective
          simp only [Δ, map_add, map_sub, map_pow, map_mul, map_ofNat, map_inv₀, hTy, hNy]
          have hd1K : algebraMap F K (d₁ : F) ≠ 0 :=
            (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr d₁.ne_zero
          apply mul_left_cancel₀ (pow_ne_zero 2 hd1K)
          field_simp [hd1K]
          linear_combination -4 * algebraMap F K b * (y * y ^ q) * hkC
        have hgΔ_sq : IsSquare ((g : F) * Δ) := by
          refine ⟨2 * Ny * (d₂ : F)⁻¹ + Uy, ?_⟩
          apply (algebraMap F K).injective
          simp only [Δ, map_add, map_pow, map_mul, map_ofNat, map_inv₀, hTy, hNy, hUy, ← hε_sq]
          have hd2K : algebraMap F K (d₂ : F) ≠ 0 :=
            (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr d₂.ne_zero
          have hx_eq : x = (algebraMap F K (d₂ : F))⁻¹ * y := by
            rw [← hxy, ← mul_assoc, inv_mul_cancel₀ hd2K, one_mul]
          rw [hx_eq, frob_mul (F := F), inv_pow, frob_algebraMap, map_mul, map_add, map_one, ← hε_sq] at hw
          have hw' : y * y ^ Fintype.card F + algebraMap F K (d₂ : F) * ε * y -
              algebraMap F K (d₂ : F) * ε * y ^ Fintype.card F -
              algebraMap F K (d₂ : F) ^ 2 * ((algebraMap F K b + 1) * ε ^ 2) = 0 := by
            have h := congrArg (algebraMap F K (d₂ : F) ^ 2 * ·) hw
            rw [mul_zero] at h
            field_simp [hd2K] at h
            linear_combination h
          apply mul_left_cancel₀ (pow_ne_zero 2 hd2K)
          field_simp [hd2K]
          linear_combination -4 * (y * y ^ q) * hw'
        rcases hΔ_sq with ⟨u, hu⟩
        rcases hgΔ_sq with ⟨v, hv⟩
        have hu0 : u ≠ 0 := by intro h0; rw [h0, mul_zero] at hu; exact hΔ_ne hu
        apply hg_nonsq
        refine ⟨v / u, ?_⟩
        field_simp [hu0]
        calc (g : F) * u ^ 2 = (g : F) * Δ := by rw [hu, sq]
          _ = v ^ 2 := by rw [hv, sq]

end QuadExt

/-! ### Part 4: Concrete `PG(3, 9)` (`F9 ⊂ K81`) and explicit non-hemi-replaceable 9-nest -/

section Counterexample9

/-- Concrete `GF(9) = 𝔽₃[i] / (i² + 1)`. -/
private structure F9 where
  a : ZMod 3
  b : ZMod 3
  deriving DecidableEq

private lemma F9.ext {x y : F9} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; cases ha; cases hb; rfl

private instance : Fintype F9 :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun x => (x.a, x.b)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private lemma card_F9 : Fintype.card F9 = 9 := by
  decide

private instance : Zero F9 := ⟨⟨0, 0⟩⟩
private instance : One F9 := ⟨⟨1, 0⟩⟩
private instance : Add F9 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
private instance : Neg F9 := ⟨fun x => ⟨-x.a, -x.b⟩⟩
private instance : Mul F9 := ⟨fun x y => ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a⟩⟩

private def F9.norm (x : F9) : ZMod 3 := x.a * x.a + x.b * x.b
private def F9.inv (x : F9) : F9 :=
  let n := x.norm
  ⟨x.a * n, -x.b * n⟩

private instance : CommRing F9 where
  add_assoc x y z := F9.ext (add_assoc x.a y.a z.a) (add_assoc x.b y.b z.b)
  zero_add x := F9.ext (zero_add x.a) (zero_add x.b)
  add_zero x := F9.ext (add_zero x.a) (add_zero x.b)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel x := F9.ext (neg_add_cancel x.a) (neg_add_cancel x.b)
  add_comm x y := F9.ext (add_comm x.a y.a) (add_comm x.b y.b)
  mul_assoc x y z := F9.ext
    (by change (x.a * y.a - x.b * y.b) * z.a - (x.a * y.b + x.b * y.a) * z.b =
          x.a * (y.a * z.a - y.b * z.b) - x.b * (y.a * z.b + y.b * z.a); ring)
    (by change (x.a * y.a - x.b * y.b) * z.b + (x.a * y.b + x.b * y.a) * z.a =
          x.a * (y.a * z.b + y.b * z.a) + x.b * (y.a * z.a - y.b * z.b); ring)
  one_mul x := F9.ext (by change 1 * x.a - 0 * x.b = x.a; ring) (by change 1 * x.b + 0 * x.a = x.b; ring)
  mul_one x := F9.ext (by change x.a * 1 - x.b * 0 = x.a; ring) (by change x.a * 0 + x.b * 1 = x.b; ring)
  left_distrib x y z := F9.ext
    (by change x.a * (y.a + z.a) - x.b * (y.b + z.b) =
          (x.a * y.a - x.b * y.b) + (x.a * z.a - x.b * z.b); ring)
    (by change x.a * (y.b + z.b) + x.b * (y.a + z.a) =
          (x.a * y.b + x.b * y.a) + (x.a * z.b + x.b * z.a); ring)
  right_distrib x y z := F9.ext
    (by change (x.a + y.a) * z.a - (x.b + y.b) * z.b =
          (x.a * z.a - x.b * z.b) + (y.a * z.a - y.b * z.b); ring)
    (by change (x.a + y.a) * z.b + (x.b + y.b) * z.a =
          (x.a * z.b + x.b * z.a) + (y.a * z.b + y.b * z.a); ring)
  zero_mul x := F9.ext (by change 0 * x.a - 0 * x.b = 0; ring) (by change 0 * x.b + 0 * x.a = 0; ring)
  mul_zero x := F9.ext (by change x.a * 0 - x.b * 0 = 0; ring) (by change x.a * 0 + x.b * 0 = 0; ring)
  mul_comm x y := F9.ext
    (by change x.a * y.a - x.b * y.b = y.a * x.a - y.b * x.b; ring)
    (by change x.a * y.b + x.b * y.a = y.a * x.b + y.b * x.a; ring)

private lemma F9_mul_inv_cancel (x : F9) (hx : x ≠ 0) : x * x.inv = 1 := by
  have hall : ∀ y : F9, y ≠ 0 → y * y.inv = 1 := by decide
  exact hall x hx

private instance : Field F9 where
  inv := F9.inv
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := F9_mul_inv_cancel
  inv_zero := rfl
  nnqsmul := _
  qsmul := _

/-- Concrete `GF(81) = F9[ω] / (ω² - (1 + i))`. -/
private structure K81 where
  x : F9
  y : F9
  deriving DecidableEq

private lemma K81.ext {u v : K81} (hx : u.x = v.x) (hy : u.y = v.y) : u = v := by
  cases u; cases v; cases hx; cases hy; rfl

private instance : Fintype K81 :=
  Fintype.ofEquiv (F9 × F9)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun z => (z.x, z.y)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private lemma card_K81 : Fintype.card K81 = 81 := by
  decide

private def W2 : F9 := ⟨1, 1⟩

private instance : Zero K81 := ⟨⟨0, 0⟩⟩
private instance : One K81 := ⟨⟨1, 0⟩⟩
private instance : Add K81 := ⟨fun u v => ⟨u.x + v.x, u.y + v.y⟩⟩
private instance : Neg K81 := ⟨fun u => ⟨-u.x, -u.y⟩⟩
private instance : Mul K81 :=
  ⟨fun u v => ⟨u.x * v.x + W2 * (u.y * v.y), u.x * v.y + u.y * v.x⟩⟩

private def K81.norm (u : K81) : F9 := u.x * u.x - W2 * (u.y * u.y)
private def K81.inv (u : K81) : K81 :=
  let n := u.norm
  ⟨u.x * n.inv, -u.y * n.inv⟩

private instance : CommRing K81 where
  add_assoc u v w := K81.ext (add_assoc u.x v.x w.x) (add_assoc u.y v.y w.y)
  zero_add u := K81.ext (zero_add u.x) (zero_add u.y)
  add_zero u := K81.ext (add_zero u.x) (add_zero u.y)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel u := K81.ext (neg_add_cancel u.x) (neg_add_cancel u.y)
  add_comm u v := K81.ext (add_comm u.x v.x) (add_comm u.y v.y)
  mul_assoc u v w := K81.ext
    (by change (u.x * v.x + W2 * (u.y * v.y)) * w.x + W2 * ((u.x * v.y + u.y * v.x) * w.y) =
          u.x * (v.x * w.x + W2 * (v.y * w.y)) + W2 * (u.y * (v.x * w.y + v.y * w.x)); ring)
    (by change (u.x * v.x + W2 * (u.y * v.y)) * w.y + (u.x * v.y + u.y * v.x) * w.x =
          u.x * (v.x * w.y + v.y * w.x) + u.y * (v.x * w.x + W2 * (v.y * w.y)); ring)
  one_mul u := K81.ext (by change 1 * u.x + W2 * (0 * u.y) = u.x; ring)
    (by change 1 * u.y + 0 * u.x = u.y; ring)
  mul_one u := K81.ext (by change u.x * 1 + W2 * (u.y * 0) = u.x; ring)
    (by change u.x * 0 + u.y * 1 = u.y; ring)
  left_distrib u v w := K81.ext
    (by change u.x * (v.x + w.x) + W2 * (u.y * (v.y + w.y)) =
          (u.x * v.x + W2 * (u.y * v.y)) + (u.x * w.x + W2 * (u.y * w.y)); ring)
    (by change u.x * (v.y + w.y) + u.y * (v.x + w.x) =
          (u.x * v.y + u.y * v.x) + (u.x * w.y + u.y * w.x); ring)
  right_distrib u v w := K81.ext
    (by change (u.x + v.x) * w.x + W2 * ((u.y + v.y) * w.y) =
          (u.x * w.x + W2 * (u.y * w.y)) + (v.x * w.x + W2 * (v.y * w.y)); ring)
    (by change (u.x + v.x) * w.y + (u.y + v.y) * w.x =
          (u.x * w.y + u.y * w.x) + (v.x * w.y + v.y * w.x); ring)
  zero_mul u := K81.ext (by change 0 * u.x + W2 * (0 * u.y) = 0; ring)
    (by change 0 * u.y + 0 * u.x = 0; ring)
  mul_zero u := K81.ext (by change u.x * 0 + W2 * (u.y * 0) = 0; ring)
    (by change u.x * 0 + u.y * 0 = 0; ring)
  mul_comm u v := K81.ext
    (by change u.x * v.x + W2 * (u.y * v.y) = v.x * u.x + W2 * (v.y * u.y); ring)
    (by change u.x * v.y + u.y * v.x = v.x * u.y + v.y * u.x; ring)

private lemma K81_norm_ne_zero (u : K81) (hu : u ≠ 0) : u.norm ≠ 0 := by
  by_cases hy : u.y = 0
  · have hx : u.x ≠ 0 := fun h => hu (K81.ext h hy)
    simp only [K81.norm, hy, mul_zero, sub_zero]
    exact mul_ne_zero hx hx
  · intro h0
    have hsq : (u.x * u.y⁻¹) * (u.x * u.y⁻¹) = W2 := by
      have : u.x * u.x = W2 * (u.y * u.y) := sub_eq_zero.mp h0
      field_simp [hy]
      linear_combination this
    have hnsq : ∀ t : F9, t * t ≠ W2 := by decide
    exact hnsq (u.x * u.y⁻¹) hsq

private lemma K81_mul_inv_cancel (u : K81) (hu : u ≠ 0) : u * u.inv = 1 := by
  have hn := K81_norm_ne_zero u hu
  apply K81.ext
  · change u.x * (u.x * u.norm⁻¹) + W2 * (u.y * (-u.y * u.norm⁻¹)) = 1
    have : u.x * (u.x * u.norm⁻¹) + W2 * (u.y * (-u.y * u.norm⁻¹)) = u.norm * u.norm⁻¹ := by
      simp only [K81.norm]; ring
    rw [this, mul_inv_cancel₀ hn]
  · change u.x * (-u.y * u.norm⁻¹) + u.y * (u.x * u.norm⁻¹) = 0
    ring

private instance : Field K81 where
  inv := K81.inv
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := K81_mul_inv_cancel
  inv_zero := rfl
  nnqsmul := _
  qsmul := _

private def F9ToK81 : F9 →+* K81 where
  toFun a := ⟨a, 0⟩
  map_one' := rfl
  map_mul' a b := K81.ext (by change a * b = a * b + W2 * (0 * 0); ring)
    (by change 0 = a * 0 + 0 * b; ring)
  map_zero' := rfl
  map_add' a b := K81.ext rfl (by change 0 = 0 + 0; ring)

private instance : Algebra F9 K81 := F9ToK81.toAlgebra

private def K81.frob (u : K81) : K81 := ⟨u.x, -u.y⟩

private lemma K81_pow_nine (u : K81) : u ^ 9 = u.frob := by
  have h1 : ∀ a : F9, a ^ 9 = a := by decide
  have hw9 : (⟨0, 1⟩ : K81) ^ 9 = ⟨0, -1⟩ := by decide
  have hu : u = F9ToK81 u.x + F9ToK81 u.y * ⟨0, 1⟩ :=
    K81.ext (by change u.x = u.x + (u.y * 0 + W2 * (0 * 1)); ring)
      (by change u.y = 0 + (u.y * 1 + 0 * 0); ring)
  have hcharF9 : CharP F9 3 := by
    refine ⟨fun n => ?_⟩
    have hmod : (n : F9) = ⟨(n : ZMod 3), 0⟩ := by
      induction n with
      | zero => rfl
      | succ k ih =>
        rw [Nat.cast_succ, Nat.cast_succ, ih]
        exact F9.ext rfl (by change (0 : ZMod 3) + 0 = 0; ring)
    rw [hmod]
    constructor
    · intro h
      exact (ZMod.natCast_eq_zero_iff n 3).mp (congrArg F9.a h)
    · intro hd
      exact F9.ext ((ZMod.natCast_eq_zero_iff n 3).mpr hd) rfl
  have _ : CharP K81 3 := ⟨fun n => by
    rw [← map_natCast (algebraMap F9 K81),
      map_eq_zero_iff (algebraMap F9 K81) (algebraMap F9 K81).injective,
      CharP.cast_eq_zero_iff F9 3]⟩
  have _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hadd9 : ∀ a b : K81, (a + b) ^ 9 = a ^ 9 + b ^ 9 := by
    intro a b
    have h3 : ∀ c d : K81, (c + d) ^ 3 = c ^ 3 + d ^ 3 := fun c d => add_pow_char (p := 3) c d
    calc (a + b) ^ 9 = ((a + b) ^ 3) ^ 3 := by ring
      _ = (a ^ 3 + b ^ 3) ^ 3 := by rw [h3]
      _ = (a ^ 3) ^ 3 + (b ^ 3) ^ 3 := by rw [h3]
      _ = a ^ 9 + b ^ 9 := by ring
  conv_lhs => rw [hu]
  rw [hadd9, mul_pow, ← map_pow, ← map_pow, h1 u.x, h1 u.y, hw9]
  exact K81.ext (by change u.x + (u.y * 0 + W2 * (0 * -1)) = u.x; ring)
    (by change 0 + (u.y * -1 + 0 * 0) = -u.y; ring)

private lemma K81_norm_eq (u : K81) : u * u.frob = ⟨u.norm, 0⟩ :=
  K81.ext (by change u.x * u.x + W2 * (u.y * -u.y) = u.x * u.x - W2 * (u.y * u.y); ring)
    (by change u.x * -u.y + u.y * u.x = 0; ring)

private def f9 (a b : ZMod 3) : F9 := ⟨a, b⟩
private def k81 (a b c d : ZMod 3) : K81 := ⟨⟨a, b⟩, ⟨c, d⟩⟩

private def circlePred (lam : K81) (a b : F9) : Option K81 → Bool
  | none => decide (b = 0)
  | some x =>
    decide (⟨b, 0⟩ * (x * x.frob) - lam.frob * x - lam * x.frob - ⟨a, 0⟩ = (0 : K81))

private lemma mem_miquelianCircle_iff_circlePred (lam : K81) (a b : F9) (k : Option K81) :
    k ∈ miquelianCircle F9 K81 lam a b ↔ circlePred lam a b k = true := by
  simp only [miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and, card_F9, circlePred]
  cases k with
  | none => simp
  | some x =>
    change (⟨b, 0⟩ * (x * x ^ 9) - lam ^ 9 * x - lam * x ^ 9 - ⟨a, 0⟩ = (0 : K81)) ↔ _
    rw [K81_pow_nine x, K81_pow_nine lam, decide_eq_true_iff]

/-- The 9 explicit Miquelian circles of our non-hemi-replaceable 9-nest in `PG(3, 9)`. -/
private def nestParams : Fin 9 → K81 × F9 × F9
  | 0 => (k81 0 0 0 0, f9 1 0, f9 1 0)
  | 1 => (k81 1 0 0 0, f9 0 0, f9 0 0)
  | 2 => (k81 1 0 0 0, f9 0 0, f9 2 0)
  | 3 => (k81 1 0 2 0, f9 0 2, f9 1 0)
  | 4 => (k81 2 2 2 0, f9 1 0, f9 0 2)
  | 5 => (k81 0 0 0 1, f9 2 0, f9 1 0)
  | 6 => (k81 1 0 2 2, f9 1 0, f9 1 2)
  | 7 => (k81 1 0 2 2, f9 0 2, f9 0 0)
  | 8 => (k81 2 1 2 2, f9 0 1, f9 1 1)

private noncomputable def nestCircle (i : Fin 9) : Finset (Option K81) :=
  let p := nestParams i
  miquelianCircle F9 K81 p.1 p.2.1 p.2.2

private noncomputable def nest9 : Finset (Finset (Option K81)) :=
  Finset.univ.image nestCircle

private lemma nestCircle_nondeg (i : Fin 9) :
    let p := nestParams i
    p.1 * p.1 ^ Fintype.card F9 + algebraMap F9 K81 (p.2.1 * p.2.2) ≠ 0 := by
  have hall : ∀ j : Fin 9,
      let p := nestParams j
      p.1 * p.1.frob + ⟨p.2.1 * p.2.2, 0⟩ ≠ (0 : K81) := by decide
  dsimp only
  rw [card_F9, K81_pow_nine]
  exact hall i

private lemma nestCircle_inj : Function.Injective nestCircle := by
  have hdist : ∀ i j : Fin 9, i ≠ j →
      ∃ k : Option K81,
        circlePred (nestParams i).1 (nestParams i).2.1 (nestParams i).2.2 k ≠
        circlePred (nestParams j).1 (nestParams j).2.1 (nestParams j).2.2 k := by
    decide
  intro i j hij
  by_contra hne
  obtain ⟨k, hk⟩ := hdist i j hne
  have hm := Finset.ext_iff.mp hij k
  simp only [nestCircle, mem_miquelianCircle_iff_circlePred] at hm
  exact hk (Bool.eq_iff_iff.mpr hm)

private lemma nest9_isNest : IsNest F9 K81 9 nest9 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold nest9
    rw [Finset.card_image_of_injective _ nestCircle_inj, Finset.card_univ, Fintype.card_fin]
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨i, _, rfl⟩
    exact ⟨(nestParams i).1, (nestParams i).2.1, (nestParams i).2.2, nestCircle_nondeg i, rfl⟩
  · intro k
    have hcount : ∀ (inst : DecidablePred (fun C : Finset (Option K81) => k ∈ C)),
        (@Finset.filter _ (fun C => k ∈ C) inst nest9).card =
        (Finset.univ.filter (fun i : Fin 9 =>
          circlePred (nestParams i).1 (nestParams i).2.1 (nestParams i).2.2 k = true)).card := by
      intro inst
      unfold nest9
      rw [Finset.filter_image, Finset.card_image_of_injective _ nestCircle_inj]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, nestCircle,
        mem_miquelianCircle_iff_circlePred]
    rw [hcount _]
    have hall : ∀ x : Option K81,
        (Finset.univ.filter (fun i : Fin 9 =>
          circlePred (nestParams i).1 (nestParams i).2.1 (nestParams i).2.2 x = true)).card = 0 ∨
        (Finset.univ.filter (fun i : Fin 9 =>
          circlePred (nestParams i).1 (nestParams i).2.1 (nestParams i).2.2 x = true)).card = 2 := by
      decide
    exact hall k

/-- Polymorphic opposite-regulus line classification over any odd quadratic extension `F ⊂ K`
with anti-Frobenius element `ω` (`ω ^ q = -ω`, `ω ≠ 0`): kept abstract so Lean never unfolds
concrete `Fintype` lists during elaboration. -/
private lemma oppLine_classification_gen {F K : Type} [Field F] [Fintype F] [Field K] [Fintype K]
    [Algebra F K] (hq : Odd (Fintype.card F)) (hcardK : Fintype.card K = Fintype.card F ^ 2)
    (ω : K) (hω0 : ω ≠ 0) (hωf : ω ^ Fintype.card F = -ω)
    (lam : K) (a b : F) (hb : b ≠ 0)
    (hnd : lam * lam ^ Fintype.card F + algebraMap F K (a * b) ≠ 0)
    (L : Submodule F (K × K))
    (hL : IsOppositeLine F K (miquelianCircle F K lam a b) L) :
    ∃ B : K,
      B * B ^ Fintype.card F =
        (lam * lam ^ Fintype.card F + algebraMap F K (a * b)) / (algebraMap F K b) ^ 2 ∧
      L = LinearMap.range (oppLineMap F K (lam / algebraMap F K b) B) := by
  classical
  set q := Fintype.card F
  have hq3 : 3 ≤ q := card_F_ge_three hq
  have h2K : (2 : K) ≠ 0 := two_ne_zero_K (F := F) hq
  set C := miquelianCircle F K lam a b
  have hCcard : C.card = q + 1 := card_miquelianCircle_of_b_ne_zero hcardK lam a b hb hnd
  have hLcard : Fintype.card L = q ^ 2 := by
    have h := Module.card_eq_pow_finrank (K := F) (V := L)
    rw [hL.1] at h; exact h
  have hC_no_none : none ∉ C := by simp [C, miquelianCircle, hb]
  have hspread_disj : ∀ k₁ k₂ : Option K, k₁ ≠ k₂ →
      spreadLine F K k₁ ⊓ spreadLine F K k₂ = ⊥ := by
    intro k₁ k₂ hne
    rw [Submodule.eq_bot_iff]
    rintro ⟨x, y⟩ ⟨h1, h2⟩
    cases k₁ with
    | none =>
      cases k₂ with
      | none => exact absurd rfl hne
      | some c₂ =>
        rw [SetLike.mem_coe, mem_spreadLine_none] at h1
        rw [SetLike.mem_coe, mem_spreadLine_some] at h2
        dsimp only at h1 h2
        rw [h1, mul_zero] at h2
        exact Prod.ext h1 h2
    | some c₁ =>
      cases k₂ with
      | none =>
        rw [SetLike.mem_coe, mem_spreadLine_some] at h1
        rw [SetLike.mem_coe, mem_spreadLine_none] at h2
        dsimp only at h1 h2
        rw [h2, mul_zero] at h1
        exact Prod.ext h2 h1
      | some c₂ =>
        rw [SetLike.mem_coe, mem_spreadLine_some] at h1 h2
        dsimp only at h1 h2
        have hsub : (c₁ - c₂) * x = 0 := by rw [sub_mul, ← h1, ← h2, sub_self]
        have hcne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr (fun h => hne (congrArg some h))
        have hx0 : x = 0 := (mul_eq_zero.mp hsub).resolve_left hcne
        rw [hx0, mul_zero] at h1
        exact Prod.ext hx0 h1
  let nz : Finset L := Finset.univ.erase 0
  have hnz_card : nz.card = q ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hLcard]
  let fiber : Option K → Finset L := fun k =>
    nz.filter (fun v : L => (v : K × K) ∈ spreadLine F K k)
  have hsmul_nz : ∀ (s : F) (w : K × K), s ≠ 0 → w ≠ 0 → s • w ≠ 0 := by
    intro s w hs hw h0
    have hsK : algebraMap F K s ≠ 0 :=
      (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr hs
    have h1 : algebraMap F K s * w.1 = 0 := by
      have := congrArg Prod.fst h0; change s • w.1 = 0 at this; rwa [Algebra.smul_def] at this
    have h2 : algebraMap F K s * w.2 = 0 := by
      have := congrArg Prod.snd h0; change s • w.2 = 0 at this; rwa [Algebra.smul_def] at this
    exact hw (Prod.ext ((mul_eq_zero.mp h1).resolve_left hsK) ((mul_eq_zero.mp h2).resolve_left hsK))
  have hfib_card : ∀ k ∈ C, q - 1 ≤ (fiber k).card := by
    intro k hk
    have hne := hL.2 k hk
    rw [Submodule.ne_bot_iff] at hne
    obtain ⟨w, ⟨hwL, hwS⟩, hw0⟩ := hne
    let f : Fˣ → L := fun s => ⟨(s : F) • w, L.smul_mem _ hwL⟩
    have hf_inj : Function.Injective f := by
      intro s₁ s₂ h
      have h' : ((s₁ : F) - (s₂ : F)) • w = 0 := by
        have hv := congrArg Subtype.val h; dsimp [f] at hv; rw [sub_smul, hv, sub_self]
      by_contra hne'
      exact hsmul_nz _ w (sub_ne_zero.mpr (fun heq => hne' (Units.ext heq))) hw0 h'
    have hf_sub : Finset.univ.image f ⊆ fiber k := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨s, _, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
      · intro h0; exact hsmul_nz (s : F) w s.ne_zero hw0 (congrArg Subtype.val h0)
      · exact (spreadLine F K k).smul_mem (s : F) hwS
    calc q - 1 = Fintype.card Fˣ := (Fintype.card_units F).symm
      _ = (Finset.univ.image f).card := by rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ]
      _ ≤ (fiber k).card := Finset.card_le_card hf_sub
  have hfib_disj : Set.PairwiseDisjoint (C : Set (Option K)) fiber := by
    intro k₁ _ k₂ _ hne
    change Disjoint (fiber k₁) (fiber k₂)
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    have hv0 : (v : K × K) ≠ 0 := fun h =>
      (Finset.mem_erase.mp (Finset.mem_filter.mp hv₁).1).1 (Subtype.ext h)
    have hmem : (v : K × K) ∈ spreadLine F K k₁ ⊓ spreadLine F K k₂ :=
      ⟨(Finset.mem_filter.mp hv₁).2, (Finset.mem_filter.mp hv₂).2⟩
    rw [hspread_disj k₁ k₂ hne] at hmem
    exact hv0 ((Submodule.mem_bot F).mp hmem)
  have hbi_eq : C.biUnion fiber = nz := by
    refine Finset.eq_of_subset_of_card_le (by
      intro v hv
      rcases Finset.mem_biUnion.mp hv with ⟨_, _, hvk⟩
      exact (Finset.mem_filter.mp hvk).1) ?_
    rw [hnz_card, Finset.card_biUnion hfib_disj]
    have hmul_eq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]; ring
    calc q ^ 2 - 1 = ∑ _k ∈ C, (q - 1) := by rw [Finset.sum_const, hCcard, smul_eq_mul, hmul_eq]
      _ ≤ ∑ k ∈ C, (fiber k).card := Finset.sum_le_sum hfib_card
  have hno_inf : L ⊓ spreadLine F K none = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro p ⟨hpL, hpS⟩
    by_contra hp0
    have hmem_nz : (⟨p, hpL⟩ : L) ∈ nz :=
      Finset.mem_erase.mpr ⟨fun h => hp0 (congrArg Subtype.val h), Finset.mem_univ _⟩
    rw [← hbi_eq] at hmem_nz
    rcases Finset.mem_biUnion.mp hmem_nz with ⟨k, hkC, hvk⟩
    have hpSk : p ∈ spreadLine F K k := (Finset.mem_filter.mp hvk).2
    have hne : k ≠ none := fun h => hC_no_none (h ▸ hkC)
    have hbot : p ∈ spreadLine F K k ⊓ spreadLine F K none := ⟨hpSk, hpS⟩
    rw [hspread_disj k none hne] at hbot
    exact hp0 ((Submodule.mem_bot F).mp hbot)
  let fstL : L →ₗ[F] K := (LinearMap.fst F K K).comp L.subtype
  have hfst_inj : Function.Injective fstL := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hvS : (v : K × K) ∈ spreadLine F K none := hv
    have hmem : (v : K × K) ∈ L ⊓ spreadLine F K none := ⟨v.2, hvS⟩
    rw [hno_inf] at hmem
    exact Subtype.ext ((Submodule.mem_bot F).mp hmem)
  have hfst_bij : Function.Bijective fstL :=
    (Fintype.bijective_iff_injective_and_card fstL).mpr ⟨hfst_inj, by rw [hLcard, hcardK]⟩
  let e : K ≃ₗ[F] L := (LinearEquiv.ofBijective fstL hfst_bij).symm
  let g : K →ₗ[F] K := (LinearMap.snd F K K).comp (L.subtype.comp e.toLinearMap)
  have hL_graph : ∀ x : K, (x, g x) ∈ L := by
    intro x
    have h1 : (e x : K × K).1 = x := by
      change fstL (e x) = x
      exact (LinearEquiv.ofBijective fstL hfst_bij).apply_symm_apply x
    have h2 : (e x : K × K) = (x, g x) := Prod.ext h1 rfl
    rw [← h2]
    exact (e x).2
  have hL_eq_graph : L = LinearMap.range (LinearMap.prod LinearMap.id g) := by
    ext p
    simp only [LinearMap.mem_range, LinearMap.prod_apply]
    constructor
    · intro hp
      refine ⟨p.1, ?_⟩
      have h1 : e p.1 = ⟨p, hp⟩ := by
        apply hfst_inj
        change fstL (e p.1) = p.1
        exact (LinearEquiv.ofBijective fstL hfst_bij).apply_symm_apply p.1
      have h2 : g p.1 = p.2 := congrArg (fun v : L => (v : K × K).2) h1
      exact Prod.ext rfl h2
    · rintro ⟨x, rfl⟩
      exact hL_graph x
  let A : K := (g 1 + g ω / ω) / 2
  let B : K := (g 1 - g ω / ω) / 2
  have hg_form : ∀ x : K, g x = A * x + B * x ^ q := by
    intro x
    have hxa : ∃ c₁ : F, algebraMap F K c₁ = (x + x ^ q) / 2 := by
      rw [← frob_eq_self_iff, div_pow, frob_add (F := F), frob_frob (F := F) hcardK]
      have h2f : (2 : K) ^ Fintype.card F = 2 := by
        rw [← map_ofNat (algebraMap F K), frob_algebraMap]
      rw [h2f, add_comm]
    have hxb : ∃ c₂ : F, algebraMap F K c₂ = (x - x ^ q) / (2 * ω) := by
      rw [← frob_eq_self_iff, div_pow, frob_sub (F := F), frob_mul (F := F),
        frob_frob (F := F) hcardK, hωf]
      have h2f : (2 : K) ^ Fintype.card F = 2 := by
        rw [← map_ofNat (algebraMap F K), frob_algebraMap]
      rw [h2f]; field_simp [h2K, hω0]; ring
    obtain ⟨c₁, hc₁⟩ := hxa
    obtain ⟨c₂, hc₂⟩ := hxb
    have hx : x = c₁ • (1 : K) + c₂ • ω := by
      simp only [Algebra.smul_def, hc₁, hc₂]; field_simp [h2K, hω0]; ring
    have hxf : x ^ q = c₁ • (1 : K) - c₂ • ω := by
      simp only [Algebra.smul_def, hc₁, hc₂]; field_simp [h2K, hω0]; ring
    have hg1 : A + B = g 1 := by simp only [A, B]; field_simp [h2K]; ring
    have hgω : A * ω - B * ω = g ω := by simp only [A, B]; field_simp [h2K, hω0]; ring
    calc g x = g (c₁ • (1 : K) + c₂ • ω) := congrArg g hx
      _ = algebraMap F K c₁ * g 1 + algebraMap F K c₂ * g ω := by
        rw [map_add, map_smul, map_smul, Algebra.smul_def, Algebra.smul_def]
      _ = A * (algebraMap F K c₁ * 1 + algebraMap F K c₂ * ω) +
          B * (algebraMap F K c₁ * 1 - algebraMap F K c₂ * ω) := by
        linear_combination algebraMap F K c₁ * hg1.symm + algebraMap F K c₂ * hgω.symm
      _ = A * (c₁ • (1 : K) + c₂ • ω) + B * (c₁ • (1 : K) - c₂ • ω) := by
        simp only [Algebra.smul_def]
      _ = A * x + B * x ^ q := by rw [← hx, ← hxf]
  have hgx_in_C : ∀ x : K, x ≠ 0 → some (A + B * (x ^ q / x)) ∈ C := by
    intro x hx0
    have hmem_nz : (⟨(x, g x), hL_graph x⟩ : L) ∈ nz :=
      Finset.mem_erase.mpr ⟨fun h => hx0 (congrArg (fun v : L => (v : K × K).1) h), Finset.mem_univ _⟩
    rw [← hbi_eq] at hmem_nz
    rcases Finset.mem_biUnion.mp hmem_nz with ⟨k, hkC, hvk⟩
    have hkS : (x, g x) ∈ spreadLine F K k := (Finset.mem_filter.mp hvk).2
    cases k with
    | none => exact absurd hkC hC_no_none
    | some c =>
      have hc : g x = c * x := hkS
      have hce : c = A + B * (x ^ q / x) := by
        rw [hg_form x] at hc
        apply mul_right_cancel₀ hx0
        rw [← hc]
        field_simp [hx0]
      rwa [← hce]
  set c₀ : K := lam / algebraMap F K b
  set R : K := (lam * lam ^ q + algebraMap F K (a * b)) / (algebraMap F K b) ^ 2
  set D₀ : K := A - c₀
  have hbK : algebraMap F K b ≠ 0 :=
    (map_ne_zero_iff (algebraMap F K) (algebraMap F K).injective).mpr hb
  have hu_poly : ∀ u : K, u * u ^ q = 1 →
      (D₀ ^ q * B) * u ^ 2 + (D₀ * D₀ ^ q + B * B ^ q - R) * u + (D₀ * B ^ q) = 0 := by
    intro u hu
    obtain ⟨x, hx0, hxq⟩ := exists_pow_q_sub_one_eq (F := F) (K := K) hcardK u hu
    have hdiv : x ^ q / x = u := by rw [hxq, mul_div_cancel_right₀ _ hx0]
    have hmem := hgx_in_C x hx0
    rw [hdiv] at hmem
    simp only [C, miquelianCircle, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hA_eq : A + B * u = c₀ + (D₀ + B * u) := by simp only [D₀]; ring
    have hc_frob : c₀ ^ q = lam ^ q / algebraMap F K b := by
      simp only [c₀, div_pow, q, frob_algebraMap]
    have hD_norm : (D₀ + B * u) * (D₀ ^ q + B ^ q * u ^ q) = R := by
      have hmul : (algebraMap F K b) ^ 2 * ((D₀ + B * u) * (D₀ ^ q + B ^ q * u ^ q)) =
          (algebraMap F K b) ^ 2 * R := by
        simp only [R, mul_div_cancel₀ _ (pow_ne_zero 2 hbK)]
        have hAf : (A + B * u) ^ Fintype.card F = c₀ ^ q + (D₀ ^ q + B ^ q * u ^ q) := by
          rw [hA_eq, frob_add (F := F), frob_add (F := F), frob_mul (F := F)]
        rw [hAf, hA_eq] at hmem
        have hbc : algebraMap F K b * c₀ = lam := mul_div_cancel₀ lam hbK
        have hbcf : algebraMap F K b * c₀ ^ q = lam ^ q := by
          rw [hc_frob, mul_div_cancel₀ _ hbK]
        rw [map_mul]
        linear_combination algebraMap F K b * hmem -
          (algebraMap F K b * (D₀ ^ q + B ^ q * u ^ q) + algebraMap F K b * c₀ ^ q - lam ^ q) * hbc -
          (algebraMap F K b * (D₀ + B * u)) * hbcf
      exact mul_left_cancel₀ (pow_ne_zero 2 hbK) hmul
    calc (D₀ ^ q * B) * u ^ 2 + (D₀ * D₀ ^ q + B * B ^ q - R) * u + (D₀ * B ^ q)
        = ((D₀ + B * u) * (D₀ ^ q + B ^ q * u ^ q) - R) * u +
            (D₀ * B ^ q + B * B ^ q * u) * (1 - u * u ^ q) := by ring
      _ = 0 := by rw [hD_norm, sub_self, zero_mul, hu, sub_self, mul_zero, add_zero]
  have hU_card : (Finset.univ.filter (fun u : K => u * u ^ q = 1)).card = q + 1 :=
    card_unit_circle (F := F) (K := K) hcardK
  have hlead0 : D₀ ^ q * B = 0 := by
    by_contra hne
    have hsub : Finset.univ.filter (fun u : K => u * u ^ q = 1) ⊆
        Finset.univ.filter (fun u : K =>
          (D₀ ^ q * B) * u ^ 2 + (D₀ * D₀ ^ q + B * B ^ q - R) * u + (D₀ * B ^ q) = 0) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_poly u (Finset.mem_filter.mp hu).2⟩
    have hle := le_trans (Finset.card_le_card hsub) (poly_deg2_card_le_two _ _ _ hne)
    omega
  have hB0 : B ≠ 0 := by
    intro hB
    have hsub : L ≤ spreadLine F K (some A) := by
      intro p hp
      rw [hL_eq_graph] at hp
      rcases hp with ⟨x, rfl⟩
      rw [mem_spreadLine_some]
      change g x = A * x
      rw [hg_form x, hB, zero_mul, add_zero]
    have hex : ∃ k ∈ C, k ≠ some A := by
      by_contra hall; push Not at hall
      have hsubC : C ⊆ {some A} := fun k hk => Finset.mem_singleton.mpr (hall k hk)
      have := Finset.card_le_card hsubC
      rw [hCcard, Finset.card_singleton] at this
      omega
    obtain ⟨k, hkC, hkne⟩ := hex
    have hne := hL.2 k hkC
    rw [Submodule.ne_bot_iff] at hne
    obtain ⟨p, ⟨hpL, hpS⟩, hp0⟩ := hne
    have hpA : p ∈ spreadLine F K (some A) := hsub hpL
    cases k with
    | none => simp [C, miquelianCircle, hb] at hkC
    | some c =>
      have h1 : p.2 = c * p.1 := hpS
      have h2 : p.2 = A * p.1 := hpA
      have hsub' : (c - A) * p.1 = 0 := by rw [sub_mul, ← h1, ← h2, sub_self]
      have hx0 : p.1 = 0 :=
        (mul_eq_zero.mp hsub').resolve_left (sub_ne_zero.mpr (fun h => hkne (congrArg some h)))
      rw [hx0, mul_zero] at h1
      exact hp0 (Prod.ext hx0 h1)
  have hD₀0 : D₀ = 0 := by
    have hDf0 : D₀ ^ q = 0 := (mul_eq_zero.mp hlead0).resolve_right hB0
    have h1 : (D₀ ^ q) ^ q = 0 := by rw [hDf0, zero_pow Fintype.card_ne_zero]
    rwa [frob_frob (F := F) hcardK] at h1
  have hA_eq : A = c₀ := sub_eq_zero.mp hD₀0
  have hB_norm : B * B ^ q = R := by
    have h1 := hu_poly 1 (by simp)
    rw [hD₀0, zero_pow Fintype.card_ne_zero] at h1
    linear_combination h1
  refine ⟨B, hB_norm, ?_⟩
  rw [hL_eq_graph]
  congr 1
  apply LinearMap.ext; intro x
  apply Prod.ext
  · rfl
  · change g x = c₀ * x + B * x ^ Fintype.card F
    rw [hg_form x, hA_eq]

/-- Every opposite-regulus line `L` of a Miquelian circle `C(lam, a, b)` with `b ≠ 0` in `PG(3, 9)`
has the exact form `L = LinearMap.range (oppLineMap F9 K81 (lam / b) B)` with `B.norm = R`. -/
private lemma oppLine_classification_K81 (lam : K81) (a b : F9) (hb : b ≠ 0)
    (hnd : lam * lam ^ Fintype.card F9 + algebraMap F9 K81 (a * b) ≠ 0)
    (L : Submodule F9 (K81 × K81))
    (hL : IsOppositeLine F9 K81 (miquelianCircle F9 K81 lam a b) L) :
    ∃ B : K81,
      B * B.frob = (lam * lam.frob + algebraMap F9 K81 (a * b)) / (algebraMap F9 K81 b) ^ 2 ∧
      L = LinearMap.range (oppLineMap F9 K81 (lam / algebraMap F9 K81 b) B) := by
  have h := oppLine_classification_gen (F := F9) (K := K81)
    (by rw [card_F9]; exact ⟨4, rfl⟩) (by rw [card_F9, card_K81]; norm_num)
    ⟨0, 1⟩ (by decide) (by rw [card_F9]; decide) lam a b hb hnd L hL
  simpa only [card_F9, K81_pow_nine] using h

private lemma oppLine_inter_of_norm_eq (c₁ B₁ c₂ B₂ : K81)
    (hc : c₁ ≠ c₂) (hnorm : (B₂ - B₁).norm = (c₁ - c₂).norm) :
    LinearMap.range (oppLineMap F9 K81 c₁ B₁) ⊓ LinearMap.range (oppLineMap F9 K81 c₂ B₂) ≠ ⊥ := by
  have hBne : B₂ - B₁ ≠ 0 := by
    intro h0
    rw [h0] at hnorm
    have h0n : (0 : K81).norm = 0 := by decide
    rw [h0n] at hnorm
    exact K81_norm_ne_zero (c₁ - c₂) (sub_ne_zero.mpr hc) hnorm.symm
  set u : K81 := (c₁ - c₂) / (B₂ - B₁)
  have hu_norm : u * u ^ Fintype.card F9 = 1 := by
    rw [card_F9, K81_pow_nine]
    have huf : u.frob = (c₁ - c₂).frob / (B₂ - B₁).frob := by
      simp only [u, ← K81_pow_nine, div_pow]
    rw [huf, div_mul_div_comm, K81_norm_eq, K81_norm_eq, hnorm]
    exact div_self (by
      intro h0
      exact K81_norm_ne_zero (c₁ - c₂) (sub_ne_zero.mpr hc) (congrArg K81.x h0))
  obtain ⟨x, hx0, hxq⟩ := exists_pow_q_sub_one_eq (F := F9) (K := K81)
    (by rw [card_F9, card_K81]; norm_num) u hu_norm
  rw [Submodule.ne_bot_iff]
  refine ⟨oppLineMap F9 K81 c₁ B₁ x, ⟨⟨x, rfl⟩, ⟨x, ?_⟩⟩, ?_⟩
  · apply Prod.ext
    · rfl
    · simp only [oppLineMap, LinearMap.coe_mk, AddHom.coe_mk]
      have hmul : (B₂ - B₁) * x ^ Fintype.card F9 = (c₁ - c₂) * x := by
        rw [hxq]; simp only [u]; rw [← mul_assoc, mul_div_cancel₀ _ hBne]
      linear_combination hmul
  · intro h0
    exact hx0 (congrArg Prod.fst h0)

private lemma two_five_cycles_force {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) (hU : U.card = 10) (hV : V.card = 10)
    (O₀ O₁ : Finset α) (hO₀ : O₀.card = 5) (hO₁ : O₁.card = 5)
    (hU_part : O₀ ⊆ U ∧ O₁ ⊆ U ∧ Disjoint O₀ O₁)
    (step : α → α)
    (hstep_O₀ : ∀ x ∈ O₀, step x ∈ O₀)
    (_hstep_O₁ : ∀ x ∈ O₁, step x ∈ O₁)
    (hcyc_O₀ : ∀ x ∈ O₀, ∀ y ∈ O₀, ∃ k : ℕ, step^[k] x = y)
    (_hcyc_O₁ : ∀ x ∈ O₁, ∀ y ∈ O₁, ∃ k : ℕ, step^[k] x = y)
    (f : α → β) (hf_inj : Set.InjOn f U) (hf_maps : ∀ x ∈ U, f x ∈ V)
    (rel : α → β → Prop)
    (hrel_f : ∀ x ∈ U, rel x (f x))
    (hrel_step : ∀ x ∈ U, rel (step x) (f x))
    (S : Finset α) (T : Finset β)
    (hSU : S ⊆ U) (hTV : T ⊆ V) (hSc : S.card = 5) (hTc : T.card = 5)
    (havoid : ∀ x ∈ S, ∀ y ∈ T, ¬ rel x y) :
    (S = O₀ ∧ T = V \ O₀.image f) ∨ (S = O₁ ∧ T = V \ O₁.image f) := by
  have hS_img_sub : S.image f ⊆ V \ T := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxS, rfl⟩
    refine Finset.mem_sdiff.mpr
      ⟨hf_maps x (hSU hxS), fun hT => havoid x hxS (f x) hT (hrel_f x (hSU hxS))⟩
  have hVT_card : (V \ T).card = 5 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTV, hV, hTc]
  have hS_img_card : (S.image f).card = 5 := by
    rw [Finset.card_image_of_injOn (hf_inj.mono hSU), hSc]
  have hS_img_eq : S.image f = V \ T :=
    Finset.eq_of_subset_of_card_le hS_img_sub (by omega)
  have hstep_back : ∀ x ∈ U, step x ∈ S → x ∈ S := by
    intro x hxU hsx
    have hfx_notT : f x ∉ T := fun hT => havoid (step x) hsx (f x) hT (hrel_step x hxU)
    have hfx_VT : f x ∈ V \ T := Finset.mem_sdiff.mpr ⟨hf_maps x hxU, hfx_notT⟩
    rw [← hS_img_eq] at hfx_VT
    rcases Finset.mem_image.mp hfx_VT with ⟨x', hx'S, hfx'⟩
    have hxx' : x' = x := hf_inj (hSU hx'S) hxU hfx'
    rwa [← hxx']
  have hstep_iter_back : ∀ k : ℕ, ∀ x ∈ U, (∀ j ≤ k, step^[j] x ∈ U) → step^[k] x ∈ S → x ∈ S := by
    intro k
    induction k with
    | zero => intro x _ _ hx; exact hx
    | succ k ih =>
      intro x hxU hall hsk
      have h1 : step^[k] x ∈ S := by
        apply hstep_back (step^[k] x) (hall k (Nat.le_succ k))
        rwa [← Function.iterate_succ_apply' step k x]
      exact ih x hxU (fun j hj => hall j (Nat.le_succ_of_le hj)) h1
  have hO₀_dich : O₀ ⊆ S ∨ Disjoint O₀ S := by
    by_cases hex : ∃ y ∈ O₀, y ∈ S
    · left
      obtain ⟨y, hyO, hyS⟩ := hex
      intro x hxO
      obtain ⟨k, hk⟩ := hcyc_O₀ x hxO y hyO
      have hall : ∀ j : ℕ, step^[j] x ∈ O₀ := by
        intro j; induction j with
        | zero => exact hxO
        | succ j ih => rw [Function.iterate_succ_apply']; exact hstep_O₀ _ ih
      exact hstep_iter_back k x (hU_part.1 hxO) (fun j _ => hU_part.1 (hall j)) (hk ▸ hyS)
    · right
      rw [Finset.disjoint_left]
      intro x hxO hxS; exact hex ⟨x, hxO, hxS⟩
  have hU_eq : O₀ ∪ O₁ = U := by
    refine Finset.eq_of_subset_of_card_le (Finset.union_subset hU_part.1 hU_part.2.1) ?_
    rw [Finset.card_union_of_disjoint hU_part.2.2, hO₀, hO₁, hU]
  have hT_eq : T = V \ S.image f := by
    rw [hS_img_eq, Finset.sdiff_sdiff_eq_self hTV]
  rcases hO₀_dich with hsub | hdisj
  · left
    have hS0 : S = O₀ := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    exact ⟨hS0, by rw [hT_eq, hS0]⟩
  · right
    have hS_sub_O₁ : S ⊆ O₁ := by
      intro x hxS
      have hxU : x ∈ O₀ ∪ O₁ := by rw [hU_eq]; exact hSU hxS
      rcases Finset.mem_union.mp hxU with hx0 | hx1
      · exact absurd hxS (Finset.disjoint_left.mp hdisj hx0)
      · exact hx1
    have hS1 : S = O₁ := Finset.eq_of_subset_of_card_le hS_sub_O₁ (by omega)
    exact ⟨hS1, by rw [hT_eq, hS1]⟩

private lemma nest9_not_hemiReplaceable : ¬ IsHemiReplaceable F9 K81 nest9 := by
  rintro ⟨H, hH_spec, hH_disj⟩
  have h0_mem : nestCircle 0 ∈ nest9 := Finset.mem_image_of_mem _ (Finset.mem_univ 0)
  have h4_mem : nestCircle 4 ∈ nest9 := Finset.mem_image_of_mem _ (Finset.mem_univ 4)
  have h6_mem : nestCircle 6 ∈ nest9 := Finset.mem_image_of_mem _ (Finset.mem_univ 6)
  obtain ⟨hH0_card, hH0_opp⟩ := hH_spec _ h0_mem
  obtain ⟨hH4_card, hH4_opp⟩ := hH_spec _ h4_mem
  obtain ⟨hH6_card, hH6_opp⟩ := hH_spec _ h6_mem
  rw [card_F9] at hH0_card hH4_card hH6_card
  let c0 : K81 := k81 0 0 0 0
  let c4 : K81 := k81 1 2 0 2
  let c6 : K81 := k81 2 2 0 2
  let R0 : F9 := f9 1 0
  let R4 : F9 := f9 1 0
  let R6 : F9 := f9 0 2
  have hc0_eq : (nestParams 0).1 / algebraMap F9 K81 (nestParams 0).2.2 = c0 := by decide
  have hc4_eq : (nestParams 4).1 / algebraMap F9 K81 (nestParams 4).2.2 = c4 := by decide
  have hc6_eq : (nestParams 6).1 / algebraMap F9 K81 (nestParams 6).2.2 = c6 := by decide
  have hR0_eq : ((nestParams 0).1 * (nestParams 0).1.frob +
      algebraMap F9 K81 ((nestParams 0).2.1 * (nestParams 0).2.2)) /
      (algebraMap F9 K81 (nestParams 0).2.2) ^ 2 = ⟨R0, 0⟩ := by decide
  have hR4_eq : ((nestParams 4).1 * (nestParams 4).1.frob +
      algebraMap F9 K81 ((nestParams 4).2.1 * (nestParams 4).2.2)) /
      (algebraMap F9 K81 (nestParams 4).2.2) ^ 2 = ⟨R4, 0⟩ := by decide
  have hR6_eq : ((nestParams 6).1 * (nestParams 6).1.frob +
      algebraMap F9 K81 ((nestParams 6).2.1 * (nestParams 6).2.2)) /
      (algebraMap F9 K81 (nestParams 6).2.2) ^ 2 = ⟨R6, 0⟩ := by decide
  have hopp_inj : ∀ c : K81, Function.Injective (fun B : K81 => LinearMap.range (oppLineMap F9 K81 c B)) := by
    intro c B₁ B₂ heq
    dsimp only at heq
    have h1 : (1, c * 1 + B₁ * (1 : K81) ^ Fintype.card F9) ∈
        LinearMap.range (oppLineMap F9 K81 c B₂) := by
      rw [← heq]; exact ⟨1, rfl⟩
    rcases h1 with ⟨x, hx⟩
    have hx1 : x = 1 := congrArg Prod.fst hx
    subst hx1
    have h2 := congrArg Prod.snd hx
    simp only [oppLineMap, LinearMap.coe_mk, AddHom.coe_mk, mul_one, one_pow] at h2
    exact (add_left_cancel h2).symm
  let U0 : Finset K81 := Finset.univ.filter (fun B : K81 => B.norm = R0)
  let U4 : Finset K81 := Finset.univ.filter (fun B : K81 => B.norm = R4)
  let U6 : Finset K81 := Finset.univ.filter (fun B : K81 => B.norm = R6)
  let S0 : Finset K81 := U0.filter (fun B => LinearMap.range (oppLineMap F9 K81 c0 B) ∈ H (nestCircle 0))
  let S4 : Finset K81 := U4.filter (fun B => LinearMap.range (oppLineMap F9 K81 c4 B) ∈ H (nestCircle 4))
  let S6 : Finset K81 := U6.filter (fun B => LinearMap.range (oppLineMap F9 K81 c6 B) ∈ H (nestCircle 6))
  have hS0_img : S0.image (fun B => LinearMap.range (oppLineMap F9 K81 c0 B)) = H (nestCircle 0) := by
    ext L
    simp only [Finset.mem_image, S0, U0, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨B, ⟨_, hL⟩, rfl⟩; exact hL
    · intro hL
      obtain ⟨B, hBn, rfl⟩ := oppLine_classification_K81 _ _ _ (by decide) (nestCircle_nondeg 0) L (hH0_opp L hL)
      rw [hc0_eq] at hL ⊢
      rw [hR0_eq, K81_norm_eq] at hBn
      exact ⟨B, ⟨congrArg K81.x hBn, hL⟩, rfl⟩
  have hS4_img : S4.image (fun B => LinearMap.range (oppLineMap F9 K81 c4 B)) = H (nestCircle 4) := by
    ext L
    simp only [Finset.mem_image, S4, U4, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨B, ⟨_, hL⟩, rfl⟩; exact hL
    · intro hL
      obtain ⟨B, hBn, rfl⟩ := oppLine_classification_K81 _ _ _ (by decide) (nestCircle_nondeg 4) L (hH4_opp L hL)
      rw [hc4_eq] at hL ⊢
      rw [hR4_eq, K81_norm_eq] at hBn
      exact ⟨B, ⟨congrArg K81.x hBn, hL⟩, rfl⟩
  have hS6_img : S6.image (fun B => LinearMap.range (oppLineMap F9 K81 c6 B)) = H (nestCircle 6) := by
    ext L
    simp only [Finset.mem_image, S6, U6, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨B, ⟨_, hL⟩, rfl⟩; exact hL
    · intro hL
      obtain ⟨B, hBn, rfl⟩ := oppLine_classification_K81 _ _ _ (by decide) (nestCircle_nondeg 6) L (hH6_opp L hL)
      rw [hc6_eq] at hL ⊢
      rw [hR6_eq, K81_norm_eq] at hBn
      exact ⟨B, ⟨congrArg K81.x hBn, hL⟩, rfl⟩
  have hS0c : S0.card = 5 := by
    have := congrArg Finset.card hS0_img
    rw [Finset.card_image_of_injective _ (hopp_inj c0), hH0_card] at this; exact this
  have hS4c : S4.card = 5 := by
    have := congrArg Finset.card hS4_img
    rw [Finset.card_image_of_injective _ (hopp_inj c4), hH4_card] at this; exact this
  have hS6c : S6.card = 5 := by
    have := congrArg Finset.card hS6_img
    rw [Finset.card_image_of_injective _ (hopp_inj c6), hH6_card] at this; exact this
  have havoid04 : ∀ B0 ∈ S0, ∀ B4 ∈ S4, (B4 - B0).norm ≠ (c0 - c4).norm := by
    intro B0 hB0 B4 hB4 hnorm
    have hL0 : LinearMap.range (oppLineMap F9 K81 c0 B0) ∈ H (nestCircle 0) := (Finset.mem_filter.mp hB0).2
    have hL4 : LinearMap.range (oppLineMap F9 K81 c4 B4) ∈ H (nestCircle 4) := (Finset.mem_filter.mp hB4).2
    have hne : nestCircle 0 ≠ nestCircle 4 := fun h => absurd (nestCircle_inj h) (by decide)
    exact oppLine_inter_of_norm_eq c0 B0 c4 B4 (by decide) hnorm
      (hH_disj _ h0_mem _ hL0 _ h4_mem _ hL4 (Or.inl hne))
  have havoid06 : ∀ B0 ∈ S0, ∀ B6 ∈ S6, (B6 - B0).norm ≠ (c0 - c6).norm := by
    intro B0 hB0 B6 hB6 hnorm
    have hL0 : LinearMap.range (oppLineMap F9 K81 c0 B0) ∈ H (nestCircle 0) := (Finset.mem_filter.mp hB0).2
    have hL6 : LinearMap.range (oppLineMap F9 K81 c6 B6) ∈ H (nestCircle 6) := (Finset.mem_filter.mp hB6).2
    have hne : nestCircle 0 ≠ nestCircle 6 := fun h => absurd (nestCircle_inj h) (by decide)
    exact oppLine_inter_of_norm_eq c0 B0 c6 B6 (by decide) hnorm
      (hH_disj _ h0_mem _ hL0 _ h6_mem _ hL6 (Or.inl hne))
  have havoid46 : ∀ B4 ∈ S4, ∀ B6 ∈ S6, (B6 - B4).norm ≠ (c4 - c6).norm := by
    intro B4 hB4 B6 hB6 hnorm
    have hL4 : LinearMap.range (oppLineMap F9 K81 c4 B4) ∈ H (nestCircle 4) := (Finset.mem_filter.mp hB4).2
    have hL6 : LinearMap.range (oppLineMap F9 K81 c6 B6) ∈ H (nestCircle 6) := (Finset.mem_filter.mp hB6).2
    have hne : nestCircle 4 ≠ nestCircle 6 := fun h => absurd (nestCircle_inj h) (by decide)
    exact oppLine_inter_of_norm_eq c4 B4 c6 B6 (by decide) hnorm
      (hH_disj _ h4_mem _ hL4 _ h6_mem _ hL6 (Or.inl hne))
  let a0 := k81 1 0 0 0; let a1 := k81 2 1 2 1; let a2 := k81 2 2 0 2
  let a3 := k81 2 2 0 1; let a4 := k81 2 1 1 2
  let b0 := k81 1 1 0 1; let b1 := k81 1 2 1 2; let b2 := k81 2 0 0 0
  let b3 := k81 1 2 2 1; let b4 := k81 1 1 0 2
  let O0 : Finset K81 := {a0, a1, a2, a3, a4}
  let O1 : Finset K81 := {b0, b1, b2, b3, b4}
  let step0 : K81 → K81 := fun u =>
    if u = a0 then a1 else if u = a1 then a2 else if u = a2 then a3 else if u = a3 then a4
    else if u = a4 then a0 else if u = b0 then b1 else if u = b1 then b2 else if u = b2 then b3
    else if u = b3 then b4 else if u = b4 then b0 else u
  let f04 : K81 → K81 := fun u =>
    if u = a0 then k81 2 2 0 1 else if u = a1 then k81 2 1 1 2 else if u = a2 then k81 1 0 0 0
    else if u = a3 then k81 2 1 2 1 else if u = a4 then k81 2 2 0 2
    else if u = b0 then k81 1 2 2 1 else if u = b1 then k81 1 1 0 2 else if u = b2 then k81 1 1 0 1
    else if u = b3 then k81 1 2 1 2 else if u = b4 then k81 2 0 0 0 else u
  let f06 : K81 → K81 := fun u =>
    if u = a0 then k81 0 1 2 1 else if u = a1 then k81 1 0 2 0 else if u = a2 then k81 1 1 0 0
    else if u = a3 then k81 1 0 1 0 else if u = a4 then k81 0 1 1 2
    else if u = b0 then k81 2 0 1 0 else if u = b1 then k81 0 2 1 2 else if u = b2 then k81 0 2 2 1
    else if u = b3 then k81 2 0 2 0 else if u = b4 then k81 2 2 0 0 else u
  have hU0_eq : U0 = O0 ∪ O1 := by decide
  have hcyc0 : ∀ x ∈ O0, ∀ y ∈ O0, ∃ k : ℕ, step0^[k] x = y := by
    simp only [O0, Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl | rfl | rfl | rfl) y (rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | exact ⟨0, rfl⟩ | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩
      | exact ⟨3, by decide⟩ | exact ⟨4, by decide⟩
  have hcyc1 : ∀ x ∈ O1, ∀ y ∈ O1, ∃ k : ℕ, step0^[k] x = y := by
    simp only [O1, Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl | rfl | rfl | rfl) y (rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | exact ⟨0, rfl⟩ | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩
      | exact ⟨3, by decide⟩ | exact ⟨4, by decide⟩
  have hf04_inj : Set.InjOn f04 U0 := by
    intro x hx y hy hxy
    have hx' : x ∈ O0 ∪ O1 := hU0_eq ▸ hx
    have hy' : y ∈ O0 ∪ O1 := hU0_eq ▸ hy
    simp only [Finset.mem_union, O0, O1, Finset.mem_insert, Finset.mem_singleton] at hx' hy'
    rcases hx' with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;>
    rcases hy' with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;>
    first | rfl | (exfalso; revert hxy; decide)
  have hf06_inj : Set.InjOn f06 U0 := by
    intro x hx y hy hxy
    have hx' : x ∈ O0 ∪ O1 := hU0_eq ▸ hx
    have hy' : y ∈ O0 ∪ O1 := hU0_eq ▸ hy
    simp only [Finset.mem_union, O0, O1, Finset.mem_insert, Finset.mem_singleton] at hx' hy'
    rcases hx' with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;>
    rcases hy' with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;>
    first | rfl | (exfalso; revert hxy; decide)
  have h04 := two_five_cycles_force U0 U4 (by decide) (by decide) O0 O1 (by decide) (by decide)
    (by decide) step0 (by decide) (by decide) hcyc0 hcyc1 f04 hf04_inj
    (by decide)
    (fun x y => (y - x).norm = (c0 - c4).norm)
    (by decide) (by decide)
    S0 S4 (Finset.filter_subset _ _) (Finset.filter_subset _ _) hS0c hS4c havoid04
  have h06 := two_five_cycles_force U0 U6 (by decide) (by decide) O0 O1 (by decide) (by decide)
    (by decide) step0 (by decide) (by decide) hcyc0 hcyc1 f06 hf06_inj
    (by decide)
    (fun x y => (y - x).norm = (c0 - c6).norm)
    (by decide) (by decide)
    S0 S6 (Finset.filter_subset _ _) (Finset.filter_subset _ _) hS0c hS6c havoid06
  rcases h04 with ⟨hS0, hS4⟩ | ⟨hS0, hS4⟩
  · rcases h06 with ⟨_, hS6⟩ | ⟨hS0', _⟩
    · have hb4 : k81 2 0 0 0 ∈ S4 := by rw [hS4]; decide
      have hb6 : k81 0 2 1 2 ∈ S6 := by rw [hS6]; decide
      exact havoid46 _ hb4 _ hb6 (by decide)
    · have : O0 = O1 := hS0.symm.trans hS0'
      exact absurd this (by decide)
  · rcases h06 with ⟨hS0', _⟩ | ⟨_, hS6⟩
    · have : O1 = O0 := hS0.symm.trans hS0'
      exact absurd this (by decide)
    · have hb4 : k81 2 1 1 2 ∈ S4 := by rw [hS4]; decide
      have hb6 : k81 0 1 1 2 ∈ S6 := by rw [hS6]; decide
      exact havoid46 _ hb4 _ hb6 (by decide)

end Counterexample9

theorem main_proof :
    (∀ (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K],
      Odd (Fintype.card F) →
      Fintype.card K = Fintype.card F ^ 2 →
      ∀ b : F, IsSquare (b * (b + 1)) → b * (b + 1) ≠ 0 →
        let q := Fintype.card F
        let D := miquelianCircle F K 1 1 b
        let N := bundleOrbit F K D
        IsNest F K (q - 1) N ∧
        IsBruckReplaceable F K N ∧
        ∃ D' : Finset (Option K),
          let N' := bundleOrbit F K D'
          IsNest F K (q - 1) N' ∧
          IsBruckReplaceable F K N' ∧
          (∀ C ∈ N, ∀ C' ∈ N', Disjoint C C')) ∧
    (∃ (F K : Type) (_ : Field F) (_ : Fintype F) (_ : Field K) (_ : Fintype K)
      (_ : Algebra F K),
      Fintype.card F = 9 ∧
      Fintype.card K = 81 ∧
      ∃ (t : ℕ) (N : Finset (Finset (Option K))),
        t ≤ Fintype.card F ∧
        IsNest F K t N ∧
        ¬ IsHemiReplaceable F K N) := by
  refine ⟨?_, ?_⟩
  · intro F K _ _ _ _ _ hq hcardK b hb_sq hb_ne
    exact ⟨bakerEbert_isNest hq hcardK b hb_sq hb_ne,
      bakerEbert_isBruckReplaceable hq hcardK b hb_sq hb_ne,
      companion_nest_exists hq hcardK b hb_sq hb_ne⟩
  · exact ⟨F9, K81, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      card_F9, card_K81, 9, nest9, by rw [card_F9], nest9_isNest, nest9_not_hemiReplaceable⟩

end OMA.P_arxiv_2610_05514

theorem OMA.solution : type_of% @OMA.S_arxiv_2610_05514.main :=
  OMA.P_arxiv_2610_05514.main_proof
