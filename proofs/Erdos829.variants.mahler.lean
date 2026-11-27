import FormalConjectures.ErdosProblems.«829»

/-! Proof of Erdos829.variants.mahler. -/

namespace Erdos829Mahler

open WeierstrassCurve Affine

def W : WeierstrassCurve.Affine ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := -34992 }

lemma W_eq_iff (u v : ℚ) : W.Equation u v ↔ v ^ 2 = u ^ 3 - 34992 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [W]
  ring_nf

lemma W_negY (u v : ℚ) : W.negY u v = -v := by
  simp [WeierstrassCurve.Affine.negY, W]

lemma W_u_pos {u v : ℚ} (h : W.Equation u v) : 0 < u := by
  rw [W_eq_iff] at h
  have hu3 : 0 < u ^ 3 := by nlinarith [sq_nonneg v]
  by_contra hu
  push Not at hu
  have h1 : u ^ 3 ≤ 0 := by nlinarith [sq_nonneg u]
  linarith

lemma W_v_ne_zero {u v : ℚ} (h : W.Equation u v) : v ≠ 0 := by
  intro hv
  rw [W_eq_iff, hv] at h
  have hu3 : u ^ 3 = 34992 := by linarith
  have hq : (u.num : ℚ) ^ 3 = 34992 * (u.den : ℚ) ^ 3 := by
    have hd : (u.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr u.den_nz
    calc (u.num : ℚ) ^ 3 = ((u.num : ℚ) / u.den * u.den) ^ 3 := by rw [div_mul_cancel₀ _ hd]
      _ = (u * u.den) ^ 3 := by rw [u.num_div_den]
      _ = u ^ 3 * (u.den : ℚ) ^ 3 := by ring
      _ = 34992 * (u.den : ℚ) ^ 3 := by rw [hu3]
  have hz : u.num ^ 3 = 34992 * (u.den : ℤ) ^ 3 := by exact_mod_cast hq
  have ha_nonneg : 0 ≤ u.num := by
    have hup := W_u_pos ((W_eq_iff u 0).mpr (by linarith))
    have hrat := u.num_div_den
    have hd : (0 : ℚ) < u.den := Nat.cast_pos.mpr u.pos
    have hnum_pos : (0 : ℚ) < u.num := by rw [← hrat] at hup; exact (div_pos_iff_of_pos_right hd).mp hup
    exact_mod_cast hnum_pos.le
  have hnat : u.num.natAbs ^ 3 = 34992 * u.den ^ 3 := by
    zify
    rw [abs_of_nonneg ha_nonneg]
    exact hz
  have h2a3 : 2 ∣ u.num.natAbs ^ 3 := ⟨17496 * u.den ^ 3, by linarith⟩
  have h2a : 2 ∣ u.num.natAbs := Nat.prime_two.dvd_of_dvd_pow h2a3
  rcases h2a with ⟨m, hm⟩
  have hm3 : m ^ 3 = 2 * (2187 * u.den ^ 3) := by
    rw [hm] at hnat
    linarith
  have h2m3 : 2 ∣ m ^ 3 := ⟨2187 * u.den ^ 3, hm3⟩
  have h2m : 2 ∣ m := Nat.prime_two.dvd_of_dvd_pow h2m3
  rcases h2m with ⟨k, hk⟩
  have hk3 : 2187 * u.den ^ 3 = 2 * (2 * k ^ 3) := by
    rw [hk] at hm3
    linarith
  have h2mul : 2 ∣ 2187 * u.den ^ 3 := ⟨2 * k ^ 3, hk3⟩
  have h2b3 : 2 ∣ u.den ^ 3 := (Nat.prime_two.dvd_mul.mp h2mul).resolve_left (by decide)
  have h2b : 2 ∣ u.den := Nat.prime_two.dvd_of_dvd_pow h2b3
  have h2gcd : 2 ∣ Nat.gcd u.num.natAbs u.den :=
    Nat.dvd_gcd ⟨2 * k, by rw [hm, hk]⟩ h2b
  rw [u.reduced] at h2gcd
  omega

lemma W_nonsingular {u v : ℚ} (h : W.Equation u v) : W.Nonsingular u v := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨h, Or.inl ?_⟩
  simp only [W]
  have hu := W_u_pos h
  nlinarith

def mkPt (u v : ℚ) (h : v ^ 2 = u ^ 3 - 34992) : W.Point :=
  Point.some u v (W_nonsingular ((W_eq_iff u v).mpr h))

def P : W.Point := mkPt 36 108 (by norm_num)

lemma P_def : P = Point.some 36 108 (W_nonsingular ((W_eq_iff 36 108).mpr (by norm_num))) := rfl

lemma W_add_some {u₁ v₁ u₂ v₂ : ℚ} {h₁ : W.Nonsingular u₁ v₁} {h₂ : W.Nonsingular u₂ v₂}
    (hxy : ¬(u₁ = u₂ ∧ v₁ = -v₂)) :
    Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ =
      Point.some (W.addX u₁ u₂ (W.slope u₁ u₂ v₁ v₂))
        (W.addY u₁ u₂ v₁ (W.slope u₁ u₂ v₁ v₂))
        (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (by rw [W_negY]; exact hxy)) := by
  exact Point.add_some (by rw [W_negY]; exact hxy)

lemma two_smul_P : (2 : ℕ) • P = mkPt 252 (-3996) (by norm_num) := by
  rw [two_nsmul, P_def, mkPt]
  have h := W_add_some (u₁ := 36) (v₁ := 108) (u₂ := 36) (v₂ := 108)
    (h₁ := W_nonsingular ((W_eq_iff 36 108).mpr (by norm_num)))
    (h₂ := W_nonsingular ((W_eq_iff 36 108).mpr (by norm_num)))
    (by norm_num)
  rw [h, Point.some.injEq]
  constructor
  · simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope, W, WeierstrassCurve.Affine.negY]
    norm_num
  · simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope, W, WeierstrassCurve.Affine.negY]
    norm_num

lemma four_smul_P : (4 : ℕ) • P = mkPt (87948 / 1369) (-24299892 / 50653) (by norm_num) := by
  have h4 : (4 : ℕ) • P = (2 : ℕ) • P + (2 : ℕ) • P := by
    rw [show (4 : ℕ) = 2 + 2 by rfl, add_nsmul]
  rw [h4, two_smul_P, mkPt, mkPt]
  have h := W_add_some (u₁ := 252) (v₁ := -3996) (u₂ := 252) (v₂ := -3996)
    (h₁ := W_nonsingular ((W_eq_iff 252 (-3996)).mpr (by norm_num)))
    (h₂ := W_nonsingular ((W_eq_iff 252 (-3996)).mpr (by norm_num)))
    (by norm_num)
  rw [h, Point.some.injEq]
  constructor
  · simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope, W, WeierstrassCurve.Affine.negY]
    norm_num
  · simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope, W, WeierstrassCurve.Affine.negY]
    norm_num

/- ### 37-adic formal group -/

def is37Int (q : ℚ) : Prop := ¬ (37 : ℕ) ∣ q.den

def div37Pow (r : ℕ) (q : ℚ) : Prop := is37Int q ∧ ((37 : ℤ) ^ r) ∣ q.num

def is37Unit (q : ℚ) : Prop := is37Int q ∧ ¬ (37 : ℤ) ∣ q.num

lemma is37Int_of_int (m : ℤ) : is37Int (m : ℚ) := by
  unfold is37Int
  rw [Rat.den_intCast]
  decide

lemma is37Int_add {a b : ℚ} (ha : is37Int a) (hb : is37Int b) : is37Int (a + b) := by
  unfold is37Int at *
  intro hdiv
  have hden := Rat.add_den_dvd a b
  have hmul : (37 : ℕ) ∣ a.den * b.den := dvd_trans hdiv hden
  rcases (Nat.Prime.dvd_mul (by decide)).mp hmul with h1 | h2
  · exact ha h1
  · exact hb h2

lemma is37Int_neg {a : ℚ} (ha : is37Int a) : is37Int (-a) := by
  unfold is37Int at *
  simpa [Rat.neg_den] using ha

lemma is37Int_sub {a b : ℚ} (ha : is37Int a) (hb : is37Int b) : is37Int (a - b) := by
  rw [sub_eq_add_neg]
  exact is37Int_add ha (is37Int_neg hb)

lemma is37Int_mul {a b : ℚ} (ha : is37Int a) (hb : is37Int b) : is37Int (a * b) := by
  unfold is37Int at *
  intro hdiv
  have hden := Rat.mul_den_dvd a b
  have hmul : (37 : ℕ) ∣ a.den * b.den := dvd_trans hdiv hden
  rcases (Nat.Prime.dvd_mul (by decide)).mp hmul with h1 | h2
  · exact ha h1
  · exact hb h2

lemma div37Pow_zero_val (r : ℕ) : div37Pow r 0 := by
  refine ⟨?_, ?_⟩
  · unfold is37Int; norm_num
  · simp

lemma div37Pow_zero_exp {q : ℚ} (hq : is37Int q) : div37Pow 0 q :=
  ⟨hq, by simp⟩

lemma div37Pow_mono {r s : ℕ} (hrs : r ≤ s) {q : ℚ} (hq : div37Pow s q) : div37Pow r q :=
  ⟨hq.1, dvd_trans (pow_dvd_pow (37 : ℤ) hrs) hq.2⟩

lemma div37Pow_neg {r : ℕ} {q : ℚ} (hq : div37Pow r q) : div37Pow r (-q) :=
  ⟨is37Int_neg hq.1, by simpa [Rat.neg_num] using dvd_neg.mpr hq.2⟩

lemma rat_num_add_rel (a b : ℚ) :
    (a + b).num * ((a.den : ℤ) * (b.den : ℤ)) =
      (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)) * ((a + b).den : ℤ) := by
  have hd1 : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  have hd2 : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr b.den_nz
  have hd3 : ((a + b).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (a + b).den_nz
  have hq : ((a + b).num : ℚ) * ((a.den : ℚ) * (b.den : ℚ)) =
      ((a.num : ℚ) * (b.den : ℚ) + (b.num : ℚ) * (a.den : ℚ)) * ((a + b).den : ℚ) := by
    have hsum := congr_arg (· * ((a.den : ℚ) * (b.den : ℚ) * ((a + b).den : ℚ)))
      (show (a + b).num / ((a + b).den : ℚ) = a.num / (a.den : ℚ) + b.num / (b.den : ℚ) by
        simp [Rat.num_div_den])
    field_simp [hd1, hd2, hd3] at hsum ⊢
    linarith
  exact_mod_cast hq

lemma rat_num_mul_rel (a b : ℚ) :
    (a * b).num * ((a.den : ℤ) * (b.den : ℤ)) = (a.num * b.num) * ((a * b).den : ℤ) := by
  have hd1 : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  have hd2 : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr b.den_nz
  have hd3 : ((a * b).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (a * b).den_nz
  have hq : ((a * b).num : ℚ) * ((a.den : ℚ) * (b.den : ℚ)) =
      ((a.num : ℚ) * (b.num : ℚ)) * ((a * b).den : ℚ) := by
    have hmul := congr_arg (· * ((a.den : ℚ) * (b.den : ℚ) * ((a * b).den : ℚ)))
      (show (a * b).num / ((a * b).den : ℚ) = (a.num / (a.den : ℚ)) * (b.num / (b.den : ℚ)) by
        simp [Rat.num_div_den])
    field_simp [hd1, hd2, hd3] at hmul ⊢
    linarith
  exact_mod_cast hq

lemma isPrime_37_int : Prime (37 : ℤ) :=
  Int.prime_iff_natAbs_prime.mpr (by decide)

lemma not_dvd_pow_37_of_not_dvd {k : ℕ} (hk : ¬ (37 : ℕ) ∣ k) (r : ℕ) :
    IsCoprime ((37 : ℤ) ^ r) (k : ℤ) := by
  apply IsCoprime.pow_left
  refine isPrime_37_int.coprime_iff_not_dvd.mpr ?_
  intro h
  exact hk (Int.natCast_dvd_natCast.mp h)

lemma div37Pow_add {r : ℕ} {a b : ℚ} (ha : div37Pow r a) (hb : div37Pow r b) :
    div37Pow r (a + b) := by
  refine ⟨is37Int_add ha.1 hb.1, ?_⟩
  have hrel := rat_num_add_rel a b
  have hdvd : (37 : ℤ) ^ r ∣ (a + b).num * ((a.den : ℤ) * (b.den : ℤ)) := by
    rw [hrel]
    exact dvd_mul_of_dvd_left (dvd_add (dvd_mul_of_dvd_left ha.2 _) (dvd_mul_of_dvd_left hb.2 _)) _
  have hcop : IsCoprime ((37 : ℤ) ^ r) ((a.den : ℤ) * (b.den : ℤ)) := by
    apply IsCoprime.mul_right
    · exact not_dvd_pow_37_of_not_dvd ha.1 r
    · exact not_dvd_pow_37_of_not_dvd hb.1 r
  exact hcop.dvd_of_dvd_mul_right hdvd

lemma div37Pow_sub {r : ℕ} {a b : ℚ} (ha : div37Pow r a) (hb : div37Pow r b) :
    div37Pow r (a - b) := by
  rw [sub_eq_add_neg]
  exact div37Pow_add ha (div37Pow_neg hb)

lemma div37Pow_mul {r s : ℕ} {a b : ℚ} (ha : div37Pow r a) (hb : div37Pow s b) :
    div37Pow (r + s) (a * b) := by
  refine ⟨is37Int_mul ha.1 hb.1, ?_⟩
  have hrel := rat_num_mul_rel a b
  have hpow : (37 : ℤ) ^ (r + s) ∣ a.num * b.num := by
    rw [pow_add]
    exact mul_dvd_mul ha.2 hb.2
  have hdvd : (37 : ℤ) ^ (r + s) ∣ (a * b).num * ((a.den : ℤ) * (b.den : ℤ)) := by
    rw [hrel]
    exact dvd_mul_of_dvd_left hpow _
  have hcop : IsCoprime ((37 : ℤ) ^ (r + s)) ((a.den : ℤ) * (b.den : ℤ)) :=
    (not_dvd_pow_37_of_not_dvd ha.1 (r + s)).mul_right (not_dvd_pow_37_of_not_dvd hb.1 (r + s))
  exact hcop.dvd_of_dvd_mul_right hdvd

lemma div37Pow_mul_int {r : ℕ} {a : ℚ} (ha : div37Pow r a) (m : ℤ) : div37Pow r ((m : ℚ) * a) := by
  simpa using div37Pow_mul (div37Pow_zero_exp (is37Int_of_int m)) ha

lemma div37Pow_pow {r n : ℕ} {a : ℚ} (ha : div37Pow r a) : div37Pow (n * r) (a ^ n) := by
  induction n with
  | zero => simp; exact div37Pow_zero_exp (is37Int_of_int 1)
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact div37Pow_mul ih ha

lemma is37Unit_ne_zero {u : ℚ} (hu : is37Unit u) : u ≠ 0 := by
  intro h0
  apply hu.2
  rw [h0]
  simp

lemma rat_inv_mul_rel {u : ℚ} (hu0 : u ≠ 0) :
    u.num * u⁻¹.num = (u.den : ℤ) * (u⁻¹.den : ℤ) := by
  have hd1 : (u.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr u.den_nz
  have hd2 : (u⁻¹.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr u⁻¹.den_nz
  have hq : (u.num : ℚ) * u⁻¹.num = (u.den : ℚ) * u⁻¹.den := by
    calc (u.num : ℚ) * u⁻¹.num
        = ((u.num : ℚ) / u.den) * (u⁻¹.num / u⁻¹.den) * ((u.den : ℚ) * u⁻¹.den) := by
            field_simp [hd1, hd2]
      _ = u * u⁻¹ * ((u.den : ℚ) * u⁻¹.den) := by rw [Rat.num_div_den, Rat.num_div_den]
      _ = 1 * ((u.den : ℚ) * u⁻¹.den) := by rw [mul_inv_cancel₀ hu0]
      _ = (u.den : ℚ) * u⁻¹.den := one_mul _
  exact_mod_cast hq

lemma is37Unit_inv {u : ℚ} (hu : is37Unit u) : is37Unit u⁻¹ := by
  have hu0 : u ≠ 0 := is37Unit_ne_zero hu
  have hrel := rat_inv_mul_rel hu0
  have hnat : u.num.natAbs * u⁻¹.num.natAbs = u.den * u⁻¹.den := by
    zify
    rw [← abs_mul, hrel, abs_of_nonneg (by positivity)]
  have hden : ¬ (37 : ℕ) ∣ u⁻¹.den := by
    intro hdiv
    have hmul : 37 ∣ u.num.natAbs * u⁻¹.num.natAbs := by
      rw [hnat]
      exact dvd_mul_of_dvd_right hdiv _
    rcases (Nat.Prime.dvd_mul (by decide)).mp hmul with h1 | h2
    · exact hu.2 (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h1))
    · have hgcd : 37 ∣ Nat.gcd u⁻¹.num.natAbs u⁻¹.den := Nat.dvd_gcd h2 hdiv
      rw [u⁻¹.reduced] at hgcd
      omega
  have hnum : ¬ (37 : ℤ) ∣ u⁻¹.num := by
    intro hdiv
    have hdvd : (37 : ℤ) ∣ (u.den : ℤ) * (u⁻¹.den : ℤ) := by
      rw [← hrel]
      exact dvd_mul_of_dvd_right hdiv _
    rcases isPrime_37_int.dvd_or_dvd hdvd with h1 | h2
    · exact hu.1 (Int.natCast_dvd_natCast.mp h1)
    · exact hden (Int.natCast_dvd_natCast.mp h2)
  exact ⟨hden, hnum⟩

lemma div37Pow_div_unit {r : ℕ} {a u : ℚ} (ha : div37Pow r a) (hu : is37Unit u) :
    div37Pow r (a / u) := by
  rw [div_eq_mul_inv]
  simpa using div37Pow_mul ha (div37Pow_zero_exp (is37Unit_inv hu).1)

lemma is37Unit_one_sub {a : ℚ} (ha : div37Pow 1 a) : is37Unit (1 - a) := by
  refine ⟨is37Int_sub (is37Int_of_int 1) ha.1, ?_⟩
  intro hdiv
  have hsub : div37Pow 1 (1 - a) := ⟨is37Int_sub (is37Int_of_int 1) ha.1, by simpa using hdiv⟩
  have h1 : div37Pow 1 (1 : ℚ) := by
    simpa using div37Pow_add hsub ha
  have hdvd : (37 : ℤ) ∣ (1 : ℚ).num := by simpa using h1.2
  norm_num at hdvd

lemma is37Unit_one_add {a : ℚ} (ha : div37Pow 1 a) : is37Unit (1 + a) := by
  simpa [sub_neg_eq_add] using is37Unit_one_sub (div37Pow_neg ha)

noncomputable def zCoord : W.Point → ℚ
  | 0 => 0
  | Point.some u v _ => -u / v

def InFormalGroup (r : ℕ) : W.Point → Prop
  | 0 => True
  | Point.some u v _ => v ≠ 0 ∧ div37Pow r (-u / v) ∧ div37Pow (3 * r) (-1 / v)

lemma zCoord_zero : zCoord (0 : W.Point) = 0 := rfl

lemma zCoord_neg (Q : W.Point) : zCoord (-Q) = -zCoord Q := by
  rcases Q with (_ | ⟨u, v, h⟩)
  · rfl
  · simp only [Point.neg_some, W_negY, zCoord]
    ring

lemma inFormalGroup_neg {r : ℕ} {Q : W.Point} (hQ : InFormalGroup r Q) : InFormalGroup r (-Q) := by
  rcases Q with (_ | ⟨u, v, h⟩)
  · trivial
  · simp only [Point.neg_some, W_negY, InFormalGroup] at hQ ⊢
    refine ⟨neg_ne_zero.mpr hQ.1, ?_, ?_⟩
    · simpa [div_neg] using div37Pow_neg hQ.2.1
    · simpa [div_neg] using div37Pow_neg hQ.2.2

lemma inFormalGroup_upgrade {r : ℕ} {Q : W.Point} (h1 : InFormalGroup 1 Q)
    (hz : div37Pow r (zCoord Q)) : InFormalGroup r Q := by
  rcases Q with (_ | ⟨u, v, h⟩)
  · trivial
  · simp only [InFormalGroup] at h1 ⊢
    simp only [zCoord] at hz
    refine ⟨h1.1, hz, ?_⟩
    set z : ℚ := -u / v
    set w : ℚ := -1 / v
    have heq : v ^ 2 = u ^ 3 - 34992 := (W_eq_iff u v).mp h.1
    have hw_eq : w * (1 + 34992 * w ^ 2) = z ^ 3 := by
      have hv : v ≠ 0 := h1.1
      dsimp [z, w]
      field_simp [hv]
      linarith
    have hunit : is37Unit (1 + 34992 * w ^ 2) := by
      apply is37Unit_one_add
      have hw2 : div37Pow 6 (w ^ 2) := by simpa using div37Pow_pow (n := 2) h1.2.2
      exact div37Pow_mono (by omega) (div37Pow_mul_int hw2 34992)
    have hz3 : div37Pow (3 * r) (z ^ 3) := by simpa using div37Pow_pow (n := 3) hz
    have hdiv : div37Pow (3 * r) (z ^ 3 / (1 + 34992 * w ^ 2)) := div37Pow_div_unit hz3 hunit
    have hw_div : w = z ^ 3 / (1 + 34992 * w ^ 2) := by
      rw [eq_div_iff (is37Unit_ne_zero hunit)]
      exact hw_eq
    rw [hw_div]
    exact hdiv

lemma w_rel_of_eq {u v : ℚ} (h : W.Equation u v) (hv : v ≠ 0) :
    (-1 / v) = (-u / v) ^ 3 + (-34992 : ℚ) * (-1 / v) ^ 3 := by
  rw [W_eq_iff] at h
  field_simp [hv]
  linarith

lemma cubic_coeff_rel {B μ ν z₁ z₂ : ℚ} (hz : B * μ ^ 3 + 1 ≠ 0) :
    let w₁ := μ * z₁ + ν
    let w₂ := μ * z₂ + ν
    let z₃ := -z₁ - z₂ - 3 * B * μ ^ 2 * ν / (1 + B * μ ^ 3)
    let w₃ := μ * z₃ + ν
    z₁ ^ 3 + B * w₁ ^ 3 - w₁ = 0 →
    z₂ ^ 3 + B * w₂ ^ 3 - w₂ = 0 →
    μ * (1 - B * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) = z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2 →
    (1 + B * μ ^ 3) * w₁ * w₂ * w₃ = ν ^ 3 ∧
      (1 + B * μ ^ 3) * (w₁ * w₂ + w₁ * w₃ + w₂ * w₃) = 3 * ν ^ 2 - μ ^ 3 := by
  intro w₁ w₂ z₃ w₃ hw₁ hw₂ hμ
  let c₃ := 1 + B * μ ^ 3
  let c₂ := 3 * B * μ ^ 2 * ν
  let c₁ := 3 * B * μ * ν ^ 2 - μ
  let c₀ := B * ν ^ 3 - ν
  have h1B : 1 + B * μ ^ 3 ≠ 0 := fun h => hz (by linarith)
  have hc₂ : c₂ = -c₃ * (z₁ + z₂ + z₃) := by
    dsimp [c₂, c₃, z₃]
    field_simp [h1B]
    ring
  have hc₁ : c₁ = c₃ * (z₁ * z₂ + z₃ * (z₁ + z₂)) := by
    dsimp [c₁, c₃, z₃]
    field_simp [h1B]
    dsimp [w₁, w₂] at hμ
    linear_combination -hμ
  have hpoly1 : c₃ * z₁ ^ 3 + c₂ * z₁ ^ 2 + c₁ * z₁ + c₀ = 0 := by
    dsimp [c₃, c₂, c₁, c₀]
    dsimp [w₁] at hw₁
    linear_combination hw₁
  have hc₀ : c₀ = -c₃ * z₁ * z₂ * z₃ := by
    linear_combination hpoly1 - z₁ ^ 2 * hc₂ - z₁ * hc₁
  constructor
  · dsimp [w₁, w₂, w₃]
    change c₃ * (μ * z₁ + ν) * (μ * z₂ + ν) * (μ * z₃ + ν) = ν ^ 3
    linear_combination (norm := (dsimp [c₃, c₂, c₁, c₀]; ring))
      (μ ^ 3) * hc₀ - μ ^ 2 * ν * hc₁ + μ * ν ^ 2 * hc₂
  · dsimp [w₁, w₂, w₃]
    change c₃ * ((μ * z₁ + ν) * (μ * z₂ + ν) + (μ * z₁ + ν) * (μ * z₃ + ν) +
      (μ * z₂ + ν) * (μ * z₃ + ν)) = 3 * ν ^ 2 - μ ^ 3
    linear_combination (norm := (dsimp [c₃, c₂, c₁, c₀]; ring))
      -(μ ^ 2) * hc₁ + 2 * μ * ν * hc₂

private lemma div37Pow_step {r : ℕ} {z₁ z₂ corr μ ν z₃ w₃ u₃ v₃ : ℚ}
    (hz₁ : div37Pow r z₁) (hz₂ : div37Pow r z₂) (hc : div37Pow (7 * r) corr)
    (hμ : div37Pow (2 * r) μ) (hν : div37Pow (3 * r) ν) (hr : 1 ≤ r)
    (hz₃ : z₃ = -z₁ - z₂ - corr) (hw₃ : w₃ = μ * z₃ + ν)
    (hzu : -u₃ / v₃ = -z₃) (hwu : -1 / v₃ = -w₃) :
    div37Pow r (-u₃ / v₃) ∧ div37Pow (3 * r) (-1 / v₃) ∧ div37Pow (7 * r) (-u₃ / v₃ - (z₁ + z₂)) := by
  have hcr : div37Pow r corr := div37Pow_mono (by omega) hc
  have hz3d : div37Pow r z₃ := by rw [hz₃]; exact div37Pow_sub (div37Pow_sub (div37Pow_neg hz₁) hz₂) hcr
  have hμzd : div37Pow (3 * r) (μ * z₃) := by
    rw [show 3 * r = 2 * r + r by omega]
    exact div37Pow_mul hμ hz3d
  have hw3d : div37Pow (3 * r) w₃ := by rw [hw₃]; exact div37Pow_add hμzd hν
  refine ⟨by rw [hzu]; exact div37Pow_neg hz3d, by rw [hwu]; exact div37Pow_neg hw3d, ?_⟩
  rw [hzu, hz₃, show -(-z₁ - z₂ - corr) - (z₁ + z₂) = corr by ring]
  exact hc

lemma formalGroup_add {r : ℕ} (hr : 1 ≤ r) {Q₁ Q₂ : W.Point}
    (hQ₁ : InFormalGroup r Q₁) (hQ₂ : InFormalGroup r Q₂) :
    InFormalGroup r (Q₁ + Q₂) ∧ div37Pow (7 * r) (zCoord (Q₁ + Q₂) - (zCoord Q₁ + zCoord Q₂)) := by
  rcases Q₁ with (_ | ⟨u₁, v₁, h₁⟩)
  · simp only [← Point.zero_def, zero_add, zCoord_zero, sub_self]
    exact ⟨hQ₂, div37Pow_zero_val (7 * r)⟩
  rcases Q₂ with (_ | ⟨u₂, v₂, h₂⟩)
  · simp only [← Point.zero_def, add_zero, zCoord_zero, sub_self]
    exact ⟨hQ₁, div37Pow_zero_val (7 * r)⟩
  by_cases hxy : u₁ = u₂ ∧ v₁ = -v₂
  · have hsum : Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ = 0 := by
      apply Point.add_of_Y_eq hxy.1
      rw [W_negY, hxy.2]
    rw [hsum]
    refine ⟨trivial, ?_⟩
    have hz : zCoord (Point.some u₁ v₁ h₁) + zCoord (Point.some u₂ v₂ h₂) = 0 := by
      simp only [zCoord, hxy.1, hxy.2]
      ring
    rw [zCoord_zero, hz, sub_zero]
    exact div37Pow_zero_val (7 * r)
  · rw [W_add_some hxy]
    let L := W.slope u₁ u₂ v₁ v₂
    let u₃ := W.addX u₁ u₂ L
    let v₃ := W.addY u₁ u₂ v₁ L
    have h₃ : W.Nonsingular u₃ v₃ :=
      WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (by rw [W_negY]; exact hxy)
    have hv₁ : v₁ ≠ 0 := hQ₁.1
    have hv₂ : v₂ ≠ 0 := hQ₂.1
    have hv₃ : v₃ ≠ 0 := W_v_ne_zero h₃.1
    set B : ℚ := -34992
    set z₁ : ℚ := -u₁ / v₁
    set w₁ : ℚ := -1 / v₁
    set z₂ : ℚ := -u₂ / v₂
    set w₂ : ℚ := -1 / v₂
    have hw₁_ne : w₁ ≠ 0 := by dsimp [w₁]; exact div_ne_zero (by norm_num) hv₁
    have hw₂_ne : w₂ ≠ 0 := by dsimp [w₂]; exact div_ne_zero (by norm_num) hv₂
    have hw₁_eq : w₁ = z₁ ^ 3 + B * w₁ ^ 3 := w_rel_of_eq h₁.1 hv₁
    have hw₂_eq : w₂ = z₂ ^ 3 + B * w₂ ^ 3 := w_rel_of_eq h₂.1 hv₂
    have hz₁_div : div37Pow r z₁ := hQ₁.2.1
    have hw₁_div : div37Pow (3 * r) w₁ := hQ₁.2.2
    have hz₂_div : div37Pow r z₂ := hQ₂.2.1
    have hw₂_div : div37Pow (3 * r) w₂ := hQ₂.2.2
    have hw_sum_div : div37Pow (3 * r) (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2) := by
      have hw11 : div37Pow (3 * r) (w₁ ^ 2) := by
        have h6 : div37Pow (6 * r) (w₁ ^ 2) := by
          simpa [pow_two, show 3 * r + 3 * r = 6 * r by omega] using div37Pow_mul hw₁_div hw₁_div
        exact div37Pow_mono (by omega) h6
      have hw12 : div37Pow (3 * r) (w₁ * w₂) :=
        div37Pow_mono (by omega) (div37Pow_mul hw₁_div hw₂_div)
      have hw22 : div37Pow (3 * r) (w₂ ^ 2) := by
        have h6 : div37Pow (6 * r) (w₂ ^ 2) := by
          simpa [pow_two, show 3 * r + 3 * r = 6 * r by omega] using div37Pow_mul hw₂_div hw₂_div
        exact div37Pow_mono (by omega) h6
      exact div37Pow_add (div37Pow_add hw11 hw12) hw22
    have hden_μ_div1 : div37Pow 1 (B * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) :=
      div37Pow_mono (by omega) (div37Pow_mul_int hw_sum_div (-34992))
    have hden_μ_unit : is37Unit (1 - B * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) :=
      is37Unit_one_sub hden_μ_div1
    have hden_μ_ne : 1 - B * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2) ≠ 0 := is37Unit_ne_zero hden_μ_unit
    set μ : ℚ := (z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2) / (1 - B * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2))
    set ν : ℚ := w₁ - μ * z₁
    have hμ_num_div : div37Pow (2 * r) (z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2) := by
      have hz11 : div37Pow (2 * r) (z₁ ^ 2) :=
        by simpa [two_mul, pow_two] using div37Pow_mul hz₁_div hz₁_div
      have hz12 : div37Pow (2 * r) (z₁ * z₂) :=
        by simpa [two_mul] using div37Pow_mul hz₁_div hz₂_div
      have hz22 : div37Pow (2 * r) (z₂ ^ 2) :=
        by simpa [two_mul, pow_two] using div37Pow_mul hz₂_div hz₂_div
      exact div37Pow_add (div37Pow_add hz11 hz12) hz22
    have hμ_div : div37Pow (2 * r) μ := div37Pow_div_unit hμ_num_div hden_μ_unit
    have hν_div : div37Pow (3 * r) ν := by
      have hmz : div37Pow (3 * r) (μ * z₁) := by
        simpa [show 2 * r + r = 3 * r by omega] using div37Pow_mul hμ_div hz₁_div
      exact div37Pow_sub hw₁_div hmz
    have hμ_rel : μ * (1 - B * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) = z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2 := by
      dsimp [μ]
      exact div_mul_cancel₀ _ hden_μ_ne
    have hw_diff : w₁ - w₂ = μ * (z₁ - z₂) := by
      have hdiff1 : (w₁ - w₂) * (1 - B * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) =
          (z₁ - z₂) * (z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2) := by
        linear_combination hw₁_eq - hw₂_eq
      rw [← hμ_rel] at hdiff1
      exact mul_right_cancel₀ hden_μ_ne (by linear_combination hdiff1)
    have hw₂_line : w₂ = μ * z₂ + ν := by
      dsimp [ν]
      linarith
    have hw₁_line : w₁ = μ * z₁ + ν := by
      dsimp [ν]
      ring
    have hμ_ne : μ ≠ 0 := by
      intro h0
      have hzsum : z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2 = 0 := by
        rw [← hμ_rel, h0, zero_mul]
      have hz2 : z₂ = 0 := by
        by_contra h
        exact absurd (mul_self_pos.mpr h) (by nlinarith [sq_nonneg (2 * z₁ + z₂)])
      rw [hz2] at hzsum
      have hz1 : z₁ = 0 := by
        by_contra h
        exact absurd (mul_self_pos.mpr h) (by nlinarith)
      have hu1_pos := W_u_pos h₁.1
      have hnv : (-u₁) / v₁ = 0 := hz1
      have hu10 : u₁ = 0 := by
        rcases div_eq_zero_iff.mp hnv with hu | hv
        · linarith
        · exact absurd hv hv₁
      linarith
    have hν_ne : ν ≠ 0 := by
      by_cases hx : u₁ = u₂
      · have hy : v₁ ≠ -v₂ := fun h => hxy ⟨hx, h⟩
        have hv12 : v₁ = v₂ :=
          WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hx (by rw [W_negY]; exact hy)
        have hz12 : z₁ = z₂ := by dsimp [z₁, z₂]; rw [hx, hv12]
        have hw12 : w₁ = w₂ := by dsimp [w₁, w₂]; rw [hv12]
        intro hν0
        have hμ_tan : μ * (1 - 3 * B * w₁ ^ 2) = 3 * z₁ ^ 2 := by
          have hrel' := hμ_rel
          rw [← hz12, ← hw12] at hrel'
          linarith
        have hwz : w₁ = μ * z₁ := by linear_combination hw₁_line + hν0
        have hrel2 : 2 * w₁ = 0 := by
          have h1 : μ * z₁ * (1 - 3 * B * w₁ ^ 2) = 3 * z₁ ^ 3 := by
            linear_combination z₁ * hμ_tan
          rw [← hwz] at h1
          have h2 : z₁ ^ 3 = w₁ - B * w₁ ^ 3 := by linarith [hw₁_eq]
          rw [h2] at h1
          linear_combination -h1
        exact hw₁_ne (by linarith)
      · intro hν0
        have hzw : z₁ * w₂ - z₂ * w₁ = ν * (z₁ - z₂) := by
          linear_combination -(z₂ * hw₁_line) + z₁ * hw₂_line
        rw [hν0, zero_mul] at hzw
        apply hx
        dsimp [z₁, w₁, z₂, w₂] at hzw
        field_simp [hv₁, hv₂] at hzw
        linarith
    have hL_eq : L = μ / ν := by
      dsimp [L]
      by_cases hx : u₁ = u₂
      · have hy : v₁ ≠ W.negY u₂ v₂ := fun h => hxy ⟨hx, by rw [W_negY] at h; exact h⟩
        rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
        have hv12 : v₁ = v₂ := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁.1 h₂.1 hx hy
        have hz12 : z₁ = z₂ := by dsimp [z₁, z₂]; rw [hx, hv12]
        have hw12 : w₁ = w₂ := by dsimp [w₁, w₂]; rw [hv12]
        have hμ_tan : μ * (1 - 3 * B * w₁ ^ 2) = 3 * z₁ ^ 2 := by
          have hrel' := hμ_rel
          rw [← hz12, ← hw12] at hrel'
          linarith
        have hden_tan : ν * (1 - 3 * B * w₁ ^ 2) = -2 * w₁ := by
          have h1 : (w₁ - μ * z₁) * (1 - 3 * B * w₁ ^ 2) =
              w₁ * (1 - 3 * B * w₁ ^ 2) - 3 * z₁ ^ 3 := by
            linear_combination -z₁ * hμ_tan
          have h2 : z₁ ^ 3 = w₁ - B * w₁ ^ 3 := by linarith [hw₁_eq]
          dsimp [ν]
          rw [h2] at h1
          linear_combination h1
        have h13 : (1 : ℚ) - 3 * B * w₁ ^ 2 ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hden_tan
          exact hw₁_ne (by linarith)
        have hu1_val : u₁ = z₁ / w₁ := by dsimp [z₁, w₁]; field_simp [hv₁]
        have hv1_val : v₁ = -1 / w₁ := by dsimp [w₁]; field_simp [hv₁]
        calc (3 * u₁ ^ 2 + 2 * W.a₂ * u₁ + W.a₄ - W.a₁ * v₁) / (v₁ - W.negY u₁ v₁)
            = (3 * u₁ ^ 2) / (2 * v₁) := by
                rw [W_negY]
                simp only [W, mul_zero, zero_mul, add_zero, sub_zero]
                ring
          _ = (3 * (z₁ / w₁) ^ 2) / (2 * (-1 / w₁)) := by rw [hu1_val, hv1_val]
          _ = (-3 * z₁ ^ 2) / (2 * w₁) := by field_simp [hw₁_ne]
          _ = μ / ν := by
              rw [div_eq_div_iff (mul_ne_zero (by norm_num) hw₁_ne) hν_ne]
              have hzero : (1 - 3 * B * w₁ ^ 2) * (2 * w₁ * μ + 3 * z₁ ^ 2 * ν) = 0 := by
                linear_combination 2 * w₁ * hμ_tan + 3 * z₁ ^ 2 * hden_tan
              have hsum0 : 2 * w₁ * μ + 3 * z₁ ^ 2 * ν = 0 :=
                (mul_eq_zero.mp hzero).resolve_left h13
              linarith
      · rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
        have hzw : z₁ * w₂ - z₂ * w₁ = ν * (z₁ - z₂) := by
          linear_combination -(z₂ * hw₁_line) + z₁ * hw₂_line
        have hz12_ne : z₁ - z₂ ≠ 0 := by
          intro hz0
          have hw0 : w₁ - w₂ = 0 := by rw [hw_diff, hz0, mul_zero]
          apply hx
          dsimp [z₁, z₂, w₁, w₂] at hz0 hw0
          have hv12 : v₁ = v₂ := by
            field_simp [hv₁, hv₂] at hw0
            linarith
          rw [hv12] at hz0
          field_simp [hv₂] at hz0
          linarith
        have hnum_sec : v₁ - v₂ = (w₁ - w₂) / (w₁ * w₂) := by
          dsimp [w₁, w₂]; field_simp [hv₁, hv₂]; ring
        have hden_sec : u₁ - u₂ = (z₁ * w₂ - z₂ * w₁) / (w₁ * w₂) := by
          dsimp [z₁, z₂, w₁, w₂]; field_simp [hv₁, hv₂]
        rw [hnum_sec, hden_sec, div_div_div_cancel_right₀ (mul_ne_zero hw₁_ne hw₂_ne)]
        rw [hw_diff, hzw]
        field_simp [hν_ne, hz12_ne]
    have hBμ3_div1 : div37Pow 1 (B * μ ^ 3) := by
      have hμ3 : div37Pow (6 * r) (μ ^ 3) := by
        simpa [show 3 * (2 * r) = 6 * r by omega] using div37Pow_pow (n := 3) hμ_div
      exact div37Pow_mono (by omega) (div37Pow_mul_int hμ3 (-34992))
    have hden_z₃_unit : is37Unit (1 + B * μ ^ 3) := is37Unit_one_add hBμ3_div1
    have hden_z₃_ne : 1 + B * μ ^ 3 ≠ 0 := is37Unit_ne_zero hden_z₃_unit
    set corr : ℚ := 3 * B * μ ^ 2 * ν / (1 + B * μ ^ 3)
    have hcorr_div : div37Pow (7 * r) corr := by
      have hμ2 : div37Pow (4 * r) (μ ^ 2) := by
        simpa [show 2 * (2 * r) = 4 * r by omega] using div37Pow_pow (n := 2) hμ_div
      have hμ2ν : div37Pow (7 * r) (μ ^ 2 * ν) := by
        simpa [show 4 * r + 3 * r = 7 * r by omega] using div37Pow_mul hμ2 hν_div
      have hcorr_eq : corr = ((3 * (-34992) : ℤ) : ℚ) * (μ ^ 2 * ν) / (1 + B * μ ^ 3) := by
        dsimp [corr, B]
        ring
      rw [hcorr_eq]
      exact div37Pow_div_unit (div37Pow_mul_int hμ2ν (3 * (-34992))) hden_z₃_unit
    set z₃ : ℚ := -z₁ - z₂ - corr
    set w₃ : ℚ := μ * z₃ + ν
    have hcub := cubic_coeff_rel (B := B) (μ := μ) (ν := ν) (z₁ := z₁) (z₂ := z₂)
      (fun h => hden_z₃_ne (by linarith))
      (by rw [← hw₁_line]; linarith [hw₁_eq]) (by rw [← hw₂_line]; linarith [hw₂_eq])
      (by rw [← hw₁_line, ← hw₂_line]; exact hμ_rel)
    have hw₃_prod : (1 + B * μ ^ 3) * w₁ * w₂ * w₃ = ν ^ 3 := by
      simpa [← hw₁_line, ← hw₂_line] using hcub.1
    have hw₃_pair : (1 + B * μ ^ 3) * (w₁ * w₂ + w₁ * w₃ + w₂ * w₃) = 3 * ν ^ 2 - μ ^ 3 := by
      simpa [← hw₁_line, ← hw₂_line] using hcub.2
    have hw₃_ne : w₃ ≠ 0 := by
      intro hw30
      rw [hw30, mul_zero] at hw₃_prod
      exact (pow_ne_zero 3 hν_ne) hw₃_prod.symm
    have hu₃_eq : u₃ = z₃ / w₃ := by
      have hsum_zw : μ * (w₁ * w₂ * w₃) * (z₁ / w₁ + z₂ / w₂ + z₃ / w₃) +
          ν * (w₁ * w₂ + w₁ * w₃ + w₂ * w₃) = 3 * (w₁ * w₂ * w₃) := by
        have h3 : w₃ = μ * z₃ + ν := rfl
        have hpoly : μ * (z₁ * w₂ * w₃ + z₂ * w₁ * w₃ + z₃ * w₁ * w₂) +
            ν * (w₁ * w₂ + w₁ * w₃ + w₂ * w₃) = 3 * (w₁ * w₂ * w₃) := by
          linear_combination -(w₂ * w₃ * hw₁_line) - w₁ * w₃ * hw₂_line - w₁ * w₂ * h3
        have hrat : μ * (w₁ * w₂ * w₃) * (z₁ / w₁ + z₂ / w₂ + z₃ / w₃) =
            μ * (z₁ * w₂ * w₃ + z₂ * w₁ * w₃ + z₃ * w₁ * w₂) := by
          field_simp [hw₁_ne, hw₂_ne, hw₃_ne]
        linarith
      have hstep : ((1 + B * μ ^ 3) * w₁ * w₂ * w₃) * μ * (z₁ / w₁ + z₂ / w₂ + z₃ / w₃) +
          ν * ((1 + B * μ ^ 3) * (w₁ * w₂ + w₁ * w₃ + w₂ * w₃)) =
          3 * ((1 + B * μ ^ 3) * w₁ * w₂ * w₃) := by
        linear_combination (1 + B * μ ^ 3) * hsum_zw
      rw [hw₃_prod, hw₃_pair] at hstep
      have hν_cancel : ν ^ 3 * μ * (μ ^ 2 / ν ^ 2) = ν * μ ^ 3 := by
        field_simp [hν_ne]
      have hfin : ν ^ 3 * μ * (z₁ / w₁ + z₂ / w₂ + z₃ / w₃ - μ ^ 2 / ν ^ 2) = 0 := by
        rw [mul_sub, hν_cancel]
        linarith [hstep]
      have hdiv0 : z₁ / w₁ + z₂ / w₂ + z₃ / w₃ - μ ^ 2 / ν ^ 2 = 0 :=
        (mul_eq_zero.mp hfin).resolve_left (mul_ne_zero (pow_ne_zero 3 hν_ne) hμ_ne)
      have hu₁_val : u₁ = z₁ / w₁ := by dsimp [z₁, w₁]; field_simp [hv₁]
      have hu₂_val : u₂ = z₂ / w₂ := by dsimp [z₂, w₂]; field_simp [hv₂]
      dsimp [u₃, WeierstrassCurve.Affine.addX, W]
      rw [hL_eq, hu₁_val, hu₂_val]
      ring_nf at hdiv0 ⊢
      linarith
    have hv₃_eq : v₃ = 1 / w₃ := by
      change -(L * (u₃ - u₁) + v₁) - W.a₁ * u₃ - W.a₃ = 1 / w₃
      simp only [W, zero_mul, sub_zero]
      rw [hL_eq, hu₃_eq]
      have hu₁_val : u₁ = z₁ / w₁ := by dsimp [z₁, w₁]; field_simp [hv₁]
      have hv₁_val : v₁ = -1 / w₁ := by dsimp [w₁]; field_simp [hv₁]
      rw [hu₁_val, hv₁_val]
      have h3 : w₃ = μ * z₃ + ν := rfl
      field_simp [hν_ne, hw₁_ne, hw₃_ne]
      linear_combination w₁ * h3 - w₃ * hw₁_line
    have hz₃_val : -u₃ / v₃ = -z₃ := by
      rw [hu₃_eq, hv₃_eq]
      field_simp [hw₃_ne]
    have hw₃_val : -1 / v₃ = -w₃ := by
      rw [hv₃_eq]
      field_simp [hw₃_ne]
    have hstep_div := div37Pow_step hz₁_div hz₂_div hcorr_div hμ_div hν_div hr
      rfl rfl hz₃_val hw₃_val
    exact ⟨⟨hv₃, hstep_div.1, hstep_div.2.1⟩, hstep_div.2.2⟩

lemma formalGroup_nsmul {r : ℕ} (hr : 1 ≤ r) {R : W.Point} (hR : InFormalGroup r R) (k : ℕ) :
    InFormalGroup r (k • R) ∧ div37Pow (7 * r) (zCoord (k • R) - (k : ℚ) * zCoord R) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    exact ⟨trivial, div37Pow_zero_val (7 * r)⟩
  | succ k ih =>
    rw [succ_nsmul]
    have hadd := formalGroup_add hr ih.1 hR
    refine ⟨hadd.1, ?_⟩
    have hsplit : zCoord (k • R + R) - ((k + 1 : ℕ) : ℚ) * zCoord R =
        (zCoord (k • R + R) - (zCoord (k • R) + zCoord R)) + (zCoord (k • R) - (k : ℚ) * zCoord R) := by
      push_cast
      ring
    rw [hsplit]
    exact div37Pow_add hadd.2 ih.2

lemma four_smul_P_inFormalGroup : InFormalGroup 1 ((4 : ℕ) • P) ∧ zCoord ((4 : ℕ) • P) ≠ 0 := by
  rw [four_smul_P, mkPt]
  refine ⟨⟨by norm_num, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, by norm_num [zCoord]⟩
  · unfold is37Int; norm_num
  · norm_num
  · unfold is37Int; norm_num
  · norm_num

lemma exists_max_pow37 {q : ℚ} (hq : div37Pow 1 q) (hq0 : q ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ div37Pow r q ∧ ¬ div37Pow (r + 1) q := by
  have hnum0 : q.num ≠ 0 := Rat.num_ne_zero.mpr hq0
  have hle : ∀ k : ℕ, ((37 : ℤ) ^ k) ∣ q.num → k ≤ q.num.natAbs := by
    intro k hk
    have hnat : 37 ^ k ≤ q.num.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hnum0) (by
      rw [← Int.natCast_dvd]
      simpa using hk)
    have hkl : k < 37 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  let S := (Finset.Icc 1 q.num.natAbs).filter (fun k => ((37 : ℤ) ^ k) ∣ q.num)
  have h1 : 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hle 1 hq.2⟩, hq.2⟩
  have hne : S.Nonempty := ⟨1, h1⟩
  refine ⟨S.max' hne, ?_, ?_, ?_⟩
  · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (S.max'_mem hne)).1).1
  · exact ⟨hq.1, (Finset.mem_filter.mp (S.max'_mem hne)).2⟩
  · intro hnext
    set r := S.max' hne
    have hmem : r + 1 ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hle (r + 1) hnext.2⟩, hnext.2⟩
    have hle_max := S.le_max' (r + 1) hmem
    omega

lemma zCoord_eq_zero_iff_of_inFormalGroup {R : W.Point} (hR : InFormalGroup 1 R) :
    zCoord R = 0 ↔ R = 0 := by
  constructor
  · intro hz
    rcases R with (_ | ⟨u, v, h⟩)
    · rfl
    · have hu_pos := W_u_pos h.1
      have hv : v ≠ 0 := hR.1
      have hnv : -u / v = 0 := hz
      have hu0 : u = 0 := by
        rcases div_eq_zero_iff.mp hnv with hu | hv0
        · linarith
        · exact absurd hv0 hv
      linarith
  · rintro rfl
    rfl

lemma nsmul_P_ne_zero : ∀ m : ℕ, 0 < m → m • P ≠ 0 := by
  classical
  intro m hm hmp
  have hm4 : m • ((4 : ℕ) • P) = 0 := by
    rw [← mul_nsmul', mul_comm, mul_nsmul', hmp, nsmul_zero]
  have hex : ∃ n : ℕ, 0 < n ∧ n • ((4 : ℕ) • P) = 0 := ⟨m, hm, hm4⟩
  let n := Nat.find hex
  have hn_spec : 0 < n ∧ n • ((4 : ℕ) • P) = 0 := Nat.find_spec hex
  have hn_pos : 0 < n := hn_spec.1
  have hn_ne_one : n ≠ 1 := by
    intro hn1
    have h40 : (4 : ℕ) • P = 0 := by simpa [hn1] using hn_spec.2
    have hfg := four_smul_P_inFormalGroup
    rw [h40, zCoord_zero] at hfg
    exact hfg.2 rfl
  let q := n.minFac
  have hq_prime : q.Prime := Nat.minFac_prime hn_ne_one
  have hq_dvd : q ∣ n := Nat.minFac_dvd n
  let k := n / q
  have hkq : k * q = n := Nat.div_mul_cancel hq_dvd
  have hk_lt : k < n := Nat.div_lt_self hn_pos hq_prime.one_lt
  have hk_pos : 0 < k := Nat.div_pos (Nat.le_of_dvd hn_pos hq_dvd) hq_prime.pos
  let R := k • ((4 : ℕ) • P)
  have hR_ne : R ≠ 0 := by
    intro hR0
    exact Nat.find_min hex hk_lt ⟨hk_pos, hR0⟩
  have hR_fg1 : InFormalGroup 1 R := (formalGroup_nsmul le_rfl four_smul_P_inFormalGroup.1 k).1
  have hR_z_ne : zCoord R ≠ 0 := fun hz => hR_ne ((zCoord_eq_zero_iff_of_inFormalGroup hR_fg1).mp hz)
  have hR_z_div1 : div37Pow 1 (zCoord R) := by
    rcases R with (_ | ⟨u, v, h⟩)
    · exact absurd rfl hR_ne
    · exact hR_fg1.2.1
  rcases exists_max_pow37 hR_z_div1 hR_z_ne with ⟨r, hr1, hR_divr, hR_ndiv⟩
  have hR_fgr : InFormalGroup r R := inFormalGroup_upgrade hR_fg1 hR_divr
  have hqR0 : q • R = 0 := by
    dsimp [R]
    rw [← mul_nsmul', mul_comm q k, hkq, hn_spec.2]
  have hq_fg := formalGroup_nsmul hr1 hR_fgr q
  rw [hqR0, zCoord_zero, zero_sub] at hq_fg
  have hq_div7r : div37Pow (7 * r) ((q : ℚ) * zCoord R) := by
    simpa using div37Pow_neg hq_fg.2
  have h7r_dvd : ((37 : ℤ) ^ (7 * r)) ∣ ((q : ℤ) * (zCoord R).num) := by
    have hrel := rat_num_mul_rel (q : ℚ) (zCoord R)
    have hnum_q : ((q : ℚ)).num = (q : ℤ) := Rat.num_natCast q
    have hden_q : ((q : ℚ)).den = 1 := Rat.den_natCast q
    rw [hnum_q, hden_q, Nat.cast_one, one_mul] at hrel
    have hdvd : (37 : ℤ) ^ (7 * r) ∣ (q : ℤ) * (zCoord R).num * ((q : ℚ) * zCoord R).den := by
      rw [← hrel]
      exact dvd_mul_of_dvd_left hq_div7r.2 _
    have hcop : IsCoprime ((37 : ℤ) ^ (7 * r)) (((q : ℚ) * zCoord R).den : ℤ) :=
      not_dvd_pow_37_of_not_dvd hq_div7r.1 (7 * r)
    exact hcop.dvd_of_dvd_mul_right hdvd
  have h6r_not : ¬ ((37 : ℤ) ^ (r + 1)) ∣ (zCoord R).num := fun h => hR_ndiv ⟨hR_divr.1, h⟩
  have hq37 : (37 : ℤ) ∣ (q : ℤ) := by
    by_contra hnq
    have hcop_q : IsCoprime ((37 : ℤ) ^ (7 * r)) (q : ℤ) := by
      apply IsCoprime.pow_left
      exact isPrime_37_int.coprime_iff_not_dvd.mpr hnq
    have hz7r : ((37 : ℤ) ^ (7 * r)) ∣ (zCoord R).num := hcop_q.dvd_of_dvd_mul_left h7r_dvd
    exact h6r_not (dvd_trans (pow_dvd_pow (37 : ℤ) (by omega)) hz7r)
  have hq_eq37 : q = 37 := by
    have hq_dvd_nat : 37 ∣ q := Int.natCast_dvd_natCast.mp hq37
    exact ((hq_prime.eq_one_or_self_of_dvd 37 hq_dvd_nat).resolve_left (by decide)).symm
  rw [hq_eq37] at h7r_dvd
  have hmul_pow : (37 : ℤ) * ((37 : ℤ) ^ (7 * r - 1)) ∣ (37 : ℤ) * (zCoord R).num := by
    rwa [← pow_succ', show 7 * r - 1 + 1 = 7 * r by omega]
  have hnext : ((37 : ℤ) ^ (7 * r - 1)) ∣ (zCoord R).num :=
    Int.dvd_of_mul_dvd_mul_left (by norm_num) hmul_pow
  exact h6r_not (dvd_trans (pow_dvd_pow (37 : ℤ) (by omega)) hnext)

lemma nsmul_P_some (k : ℕ) (hk : 1 ≤ k) :
    ∃ u v h, k • P = Point.some u v h := by
  rcases hkp : k • P with (_ | ⟨u, v, h⟩)
  · exact absurd hkp (nsmul_P_ne_zero k hk)
  · exact ⟨u, v, h, rfl⟩

lemma xCoord_injective {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    {u₁ v₁ u₂ v₂ : ℚ} {h₁ : W.Nonsingular u₁ v₁} {h₂ : W.Nonsingular u₂ v₂}
    (hp₁ : k₁ • P = Point.some u₁ v₁ h₁) (hp₂ : k₂ • P = Point.some u₂ v₂ h₂)
    (hx : u₁ = u₂) : k₁ = k₂ := by
  have heq := (Point.X_eq_iff (h₁ := h₁) (h₂ := h₂)).mp hx
  rcases heq with hsame | hneg
  · have hzero : ((k₁ : ℤ) - (k₂ : ℤ)) • P = 0 := by
      rw [sub_zsmul, natCast_zsmul, natCast_zsmul, hp₁, hp₂, hsame]
      exact add_neg_cancel _
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpos : ((k₂ - k₁ : ℕ) • P) = 0 := by
        have := congr_arg Neg.neg hzero
        rw [neg_zero, ← neg_zsmul, show -((k₁ : ℤ) - (k₂ : ℤ)) = ((k₂ - k₁ : ℕ) : ℤ) by omega,
          natCast_zsmul] at this
        exact this
      exact nsmul_P_ne_zero (k₂ - k₁) (by omega) hpos
    · have hpos : ((k₁ - k₂ : ℕ) • P) = 0 := by
        rw [show ((k₁ : ℤ) - (k₂ : ℤ)) = ((k₁ - k₂ : ℕ) : ℤ) by omega, natCast_zsmul] at hzero
        exact hzero
      exact nsmul_P_ne_zero (k₁ - k₂) (by omega) hpos
  · have hsum : (k₁ + k₂) • P = 0 := by
      rw [add_nsmul, hp₁, hp₂, hneg, neg_add_cancel]
    exact absurd hsum (nsmul_P_ne_zero (k₁ + k₂) (by omega))

/- ### Part B: Quadratic height bound -/

def H : W.Point → ℕ
  | 0 => 1
  | Point.some u _ _ => max u.num.natAbs u.den

noncomputable def h (Q : W.Point) : ℝ :=
  Real.log (H Q : ℝ)

lemma H_pos (Q : W.Point) : 1 ≤ H Q := by
  rcases Q with (_ | ⟨u, v, _⟩)
  · simp [H]
  · simp only [H]
    exact le_trans (Nat.succ_le_of_lt u.pos) (le_max_right _ _)

lemma h_nonneg (Q : W.Point) : 0 ≤ h Q := by
  unfold h
  apply Real.log_nonneg
  have h1 : (1 : ℝ) ≤ (H Q : ℝ) := by exact_mod_cast H_pos Q
  exact h1

lemma abs_split_bound {x y M : ℤ} (hM : 0 ≤ M) (hsum : |x + y| ≤ M) (hprod : |x * y| ≤ M ^ 2) :
    |x| ≤ 2 * M ∧ |y| ≤ 2 * M := by
  have hdiff_sq : (x - y) ^ 2 ≤ (3 * M) ^ 2 := by
    have hs : (x + y) ^ 2 ≤ M ^ 2 := by nlinarith [abs_le.mp hsum]
    have hp : -(M ^ 2) ≤ x * y := (abs_le.mp hprod).1
    nlinarith
  have hdiff_abs : |x - y| ≤ 3 * M := by
    have := abs_le_of_sq_le_sq' hdiff_sq (by linarith)
    exact abs_le.mpr this
  have h1 : |x + y| ≤ M := hsum
  constructor <;>
  · cases abs_le.mp h1; cases abs_le.mp hdiff_abs
    rw [abs_le]
    constructor <;> linarith

lemma primitive_triple_dvd {a₁ b₁ a₂ b₂ S P_num D : ℤ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hc₁ : Nat.Coprime a₁.natAbs b₁.natAbs) (hc₂ : Nat.Coprime a₂.natAbs b₂.natAbs)
    (hS : b₁ * b₂ * S = D * (a₁ * b₂ + a₂ * b₁))
    (hP : b₁ * b₂ * P_num = D * (a₁ * a₂)) :
    b₁ * b₂ ∣ D := by
  have hS' : (b₁ * b₂).natAbs * S.natAbs = D.natAbs * (a₁ * b₂ + a₂ * b₁).natAbs := by
    zify
    rw [← abs_mul, ← abs_mul, hS]
  have hP' : (b₁ * b₂).natAbs * P_num.natAbs = D.natAbs * (a₁ * a₂).natAbs := by
    zify
    rw [← abs_mul, ← abs_mul, hP]
  have hcop : Nat.Coprime (b₁ * b₂).natAbs (Nat.gcd (a₁ * b₂ + a₂ * b₁).natAbs (a₁ * a₂).natAbs) := by
    apply Nat.coprime_of_dvd
    intro p hp hpb hpg
    have hpd12 : p ∣ b₁.natAbs * b₂.natAbs := by simpa [Int.natAbs_mul] using hpb
    have hpg1 : p ∣ (a₁ * b₂ + a₂ * b₁).natAbs := dvd_trans hpg (Nat.gcd_dvd_left _ _)
    have hpg2 : p ∣ (a₁ * a₂).natAbs := dvd_trans hpg (Nat.gcd_dvd_right _ _)
    have hp2' : p ∣ a₁.natAbs * a₂.natAbs := by simpa [Int.natAbs_mul] using hpg2
    have hpi : (p : ℤ) ∣ b₁ ∨ (p : ℤ) ∣ b₂ := by
      rcases hp.dvd_mul.mp hpd12 with h1 | h2
      · exact Or.inl (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h1))
      · exact Or.inr (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h2))
    have hpa12 : (p : ℤ) ∣ a₁ ∨ (p : ℤ) ∣ a₂ := by
      rcases hp.dvd_mul.mp hp2' with h1 | h2
      · exact Or.inl (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h1))
      · exact Or.inr (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h2))
    have hp_sum : (p : ℤ) ∣ a₁ * b₂ + a₂ * b₁ := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpg1)
    rcases hpi with hpb1 | hpb2
    · have hpna1 : ¬ (p : ℤ) ∣ a₁ := fun ha1 => by
        have hg : p ∣ Nat.gcd a₁.natAbs b₁.natAbs :=
          Nat.dvd_gcd (Int.natCast_dvd.mp ha1) (Int.natCast_dvd.mp hpb1)
        rw [hc₁] at hg; exact hp.not_dvd_one hg
      have hpa2 : (p : ℤ) ∣ a₂ := hpa12.resolve_left hpna1
      have hpna2 : ¬ (p : ℤ) ∣ b₂ := fun hb2 => by
        have hg : p ∣ Nat.gcd a₂.natAbs b₂.natAbs :=
          Nat.dvd_gcd (Int.natCast_dvd.mp hpa2) (Int.natCast_dvd.mp hb2)
        rw [hc₂] at hg; exact hp.not_dvd_one hg
      have hpa1b2 : (p : ℤ) ∣ a₁ * b₂ := (Int.dvd_add_left (dvd_mul_of_dvd_right hpb1 a₂)).mp hp_sum
      have hp_nat : p ∣ a₁.natAbs * b₂.natAbs := by
        rw [← Int.natAbs_mul]
        exact Int.ofNat_dvd_left.mp hpa1b2
      rcases hp.dvd_mul.mp hp_nat with h1 | h2
      · exact hpna1 (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h1))
      · exact hpna2 (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h2))
    · have hpna2 : ¬ (p : ℤ) ∣ a₂ := fun ha2 => by
        have hg : p ∣ Nat.gcd a₂.natAbs b₂.natAbs :=
          Nat.dvd_gcd (Int.natCast_dvd.mp ha2) (Int.natCast_dvd.mp hpb2)
        rw [hc₂] at hg; exact hp.not_dvd_one hg
      have hpa1 : (p : ℤ) ∣ a₁ := hpa12.resolve_right hpna2
      have hpna1 : ¬ (p : ℤ) ∣ b₁ := fun hb1 => by
        have hg : p ∣ Nat.gcd a₁.natAbs b₁.natAbs :=
          Nat.dvd_gcd (Int.natCast_dvd.mp hpa1) (Int.natCast_dvd.mp hb1)
        rw [hc₁] at hg; exact hp.not_dvd_one hg
      have hpa2b1 : (p : ℤ) ∣ a₂ * b₁ := (Int.dvd_add_right (dvd_mul_of_dvd_right hpb2 a₁)).mp hp_sum
      have hp_nat : p ∣ a₂.natAbs * b₁.natAbs := by
        rw [← Int.natAbs_mul]
        exact Int.ofNat_dvd_left.mp hpa2b1
      rcases hp.dvd_mul.mp hp_nat with h1 | h2
      · exact hpna2 (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h1))
      · exact hpna1 (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h2))
  have hdvd_nat : (b₁ * b₂).natAbs ∣ D.natAbs := by
    have h1 : (b₁ * b₂).natAbs ∣ D.natAbs * (a₁ * b₂ + a₂ * b₁).natAbs := ⟨S.natAbs, hS'.symm⟩
    have h2 : (b₁ * b₂).natAbs ∣ D.natAbs * (a₁ * a₂).natAbs := ⟨P_num.natAbs, hP'.symm⟩
    have hg : (b₁ * b₂).natAbs ∣ D.natAbs * Nat.gcd (a₁ * b₂ + a₂ * b₁).natAbs (a₁ * a₂).natAbs := by
      rw [← Nat.gcd_mul_left]
      exact Nat.dvd_gcd h1 h2
    exact hcop.dvd_of_dvd_mul_right hg
  have hd : ((b₁ * b₂).natAbs : ℤ) ∣ (D.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr hdvd_nat
  have hleft : ((b₁ * b₂).natAbs : ℤ) = b₁ * b₂ := Int.natAbs_of_nonneg (mul_pos hb₁ hb₂).le
  rw [hleft] at hd
  exact Int.dvd_natAbs.mp hd

private lemma addX_sum_prod_eq {u₁ v₁ u₂ v₂ : ℚ} (heq₁ : v₁ ^ 2 = u₁ ^ 3 - 34992)
    (heq₂ : v₂ ^ 2 = u₂ ^ 3 - 34992) (hx : u₁ ≠ u₂) :
    let uP := W.addX u₁ u₂ (W.slope u₁ u₂ v₁ v₂)
    let uM := W.addX u₁ u₂ (W.slope u₁ u₂ v₁ (-v₂))
    let a₁ : ℤ := u₁.num
    let b₁ : ℤ := u₁.den
    let a₂ : ℤ := u₂.num
    let b₂ : ℤ := u₂.den
    let D : ℤ := (a₂ * b₁ - a₁ * b₂) ^ 2
    let S : ℤ := 2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁) - 139968 * b₁ ^ 2 * b₂ ^ 2
    let P_num : ℤ := (a₁ * a₂) ^ 2 + 139968 * b₁ * b₂ * (a₁ * b₂ + a₂ * b₁)
    0 < D ∧ uP + uM = (S : ℚ) / D ∧ uP * uM = (P_num : ℚ) / D := by
  intro uP uM a₁ b₁ a₂ b₂ D S P_num
  have hb₁q : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr u₁.den_nz
  have hb₂q : (b₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr u₂.den_nz
  have hu₁_q : u₁ = (a₁ : ℚ) / b₁ := (u₁.num_div_den).symm
  have hu₂_q : u₂ = (a₂ : ℚ) / b₂ := (u₂.num_div_den).symm
  have hab : (a₂ : ℚ) * b₁ - a₁ * b₂ ≠ 0 := by
    intro h0
    apply hx
    rw [hu₁_q, hu₂_q]
    field_simp [hb₁q, hb₂q]
    linarith
  have hD_pos : 0 < D := by
    refine sq_pos_iff.mpr ?_
    intro h0
    apply hab
    exact_mod_cast h0
  refine ⟨hD_pos, ?_, ?_⟩
  · dsimp [uP, uM, WeierstrassCurve.Affine.addX, W]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, WeierstrassCurve.Affine.slope_of_X_ne hx]
    have hxu : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr hx
    have hr : (((v₁ - v₂) / (u₁ - u₂)) ^ 2 + 0 * ((v₁ - v₂) / (u₁ - u₂)) - 0 - u₁ - u₂) +
          (((v₁ - -v₂) / (u₁ - u₂)) ^ 2 + 0 * ((v₁ - -v₂) / (u₁ - u₂)) - 0 - u₁ - u₂) =
        (2 * u₁ * u₂ * (u₁ + u₂) - 139968) / (u₁ - u₂) ^ 2 := by
      field_simp [hxu]
      linear_combination (norm := ring) 2 * heq₁ + 2 * heq₂
    have hq2 : (2 * u₁ * u₂ * (u₁ + u₂) - 139968) / (u₁ - u₂) ^ 2 = (S : ℚ) / D := by
      rw [hu₁_q, hu₂_q]
      dsimp [S, D]
      push_cast
      field_simp [hb₁q, hb₂q, hab]
      ring
    linarith
  · dsimp [uP, uM, WeierstrassCurve.Affine.addX, W]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, WeierstrassCurve.Affine.slope_of_X_ne hx]
    have hxu : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr hx
    have hr : (((v₁ - v₂) / (u₁ - u₂)) ^ 2 + 0 * ((v₁ - v₂) / (u₁ - u₂)) - 0 - u₁ - u₂) *
          (((v₁ - -v₂) / (u₁ - u₂)) ^ 2 + 0 * ((v₁ - -v₂) / (u₁ - u₂)) - 0 - u₁ - u₂) =
        ((u₁ * u₂) ^ 2 + 139968 * (u₁ + u₂)) / (u₁ - u₂) ^ 2 := by
      field_simp [hxu]
      linear_combination (norm := ring)
        (v₁ ^ 2 - v₂ ^ 2 + u₁ ^ 3 - u₂ ^ 3) * (heq₁ - heq₂) -
        2 * (u₁ + u₂) * (u₁ - u₂) ^ 2 * (heq₁ + heq₂)
    have hq2 : ((u₁ * u₂) ^ 2 + 139968 * (u₁ + u₂)) / (u₁ - u₂) ^ 2 = (P_num : ℚ) / D := by
      rw [hu₁_q, hu₂_q]
      dsimp [P_num, D]
      push_cast
      field_simp [hb₁q, hb₂q, hab]
      ring
    linarith

private lemma height_parallelogram_int {a₁ b₁ a₂ b₂ aP bP aM bM : ℤ}
    (hb₁_pos : 0 < b₁) (hb₂_pos : 0 < b₂) (hbP_pos : 0 < bP) (hbM_pos : 0 < bM)
    (hcP : Nat.Coprime aP.natAbs bP.natAbs) (hcM : Nat.Coprime aM.natAbs bM.natAbs)
    (hD_pos : 0 < (a₂ * b₁ - a₁ * b₂) ^ 2)
    (hS_rel : bP * bM * (2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁) - 139968 * b₁ ^ 2 * b₂ ^ 2) =
      (a₂ * b₁ - a₁ * b₂) ^ 2 * (aP * bM + aM * bP))
    (hP_rel : bP * bM * ((a₁ * a₂) ^ 2 + 139968 * b₁ * b₂ * (a₁ * b₂ + a₂ * b₁)) =
      (a₂ * b₁ - a₁ * b₂) ^ 2 * (aP * aM)) :
    max |aP| bP * max |aM| bM ≤ 1000000 * (max |a₁| b₁) ^ 2 * (max |a₂| b₂) ^ 2 := by
  let D : ℤ := (a₂ * b₁ - a₁ * b₂) ^ 2
  let S : ℤ := 2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁) - 139968 * b₁ ^ 2 * b₂ ^ 2
  let P_num : ℤ := (a₁ * a₂) ^ 2 + 139968 * b₁ * b₂ * (a₁ * b₂ + a₂ * b₁)
  have hdvd : bP * bM ∣ D := primitive_triple_dvd hbP_pos hbM_pos hcP hcM hS_rel hP_rel
  rcases hdvd with ⟨k, hk⟩
  have hk_pos : 1 ≤ k := by
    have hbb_pos : 0 < bP * bM := mul_pos hbP_pos hbM_pos
    by_contra hk0
    have hk_le0 : k ≤ 0 := by omega
    have hD_le0 : D ≤ 0 := hk ▸ mul_nonpos_of_nonneg_of_nonpos hbb_pos.le hk_le0
    exact (hD_pos.not_ge hD_le0)
  have hS_eq : k * (aP * bM + aM * bP) = S := by
    have h1 : bP * bM * (k * (aP * bM + aM * bP)) = bP * bM * S := by
      calc bP * bM * (k * (aP * bM + aM * bP)) = (bP * bM * k) * (aP * bM + aM * bP) := by ring
        _ = D * (aP * bM + aM * bP) := by rw [← hk]
        _ = bP * bM * S := hS_rel.symm
    exact mul_left_cancel₀ (mul_pos hbP_pos hbM_pos).ne' h1
  have hP_eq : k * (aP * aM) = P_num := by
    have h1 : bP * bM * (k * (aP * aM)) = bP * bM * P_num := by
      calc bP * bM * (k * (aP * aM)) = (bP * bM * k) * (aP * aM) := by ring
        _ = D * (aP * aM) := by rw [← hk]
        _ = bP * bM * P_num := hP_rel.symm
    exact mul_left_cancel₀ (mul_pos hbP_pos hbM_pos).ne' h1
  let H₁ : ℤ := max |a₁| b₁
  let H₂ : ℤ := max |a₂| b₂
  have hH₁_nonneg : 0 ≤ H₁ := le_trans hb₁_pos.le (le_max_right _ _)
  have hH₂_nonneg : 0 ≤ H₂ := le_trans hb₂_pos.le (le_max_right _ _)
  have ha₁_le : |a₁| ≤ H₁ := le_max_left _ _
  have hb₁_le : b₁ ≤ H₁ := le_max_right _ _
  have ha₂_le : |a₂| ≤ H₂ := le_max_left _ _
  have hb₂_le : b₂ ≤ H₂ := le_max_right _ _
  let M : ℤ := 500000 * H₁ ^ 2 * H₂ ^ 2
  have hM_nonneg : 0 ≤ M := by positivity
  have hD_le : D ≤ M := by
    have h1 : |a₂ * b₁ - a₁ * b₂| ≤ 2 * H₁ * H₂ := by
      calc |a₂ * b₁ - a₁ * b₂| ≤ |a₂ * b₁| + |a₁ * b₂| := abs_sub _ _
        _ = |a₂| * |b₁| + |a₁| * |b₂| := by rw [abs_mul, abs_mul]
        _ = |a₂| * b₁ + |a₁| * b₂ := by rw [abs_of_pos hb₁_pos, abs_of_pos hb₂_pos]
        _ ≤ H₂ * H₁ + H₁ * H₂ := add_le_add (mul_le_mul ha₂_le hb₁_le (by positivity) hH₂_nonneg)
            (mul_le_mul ha₁_le hb₂_le (by positivity) hH₁_nonneg)
        _ = 2 * H₁ * H₂ := by ring
    have h2 : D ≤ (2 * H₁ * H₂) ^ 2 := by
      have h1sq : |a₂ * b₁ - a₁ * b₂| ^ 2 ≤ (2 * H₁ * H₂) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self (abs_nonneg _) h1
      rwa [sq_abs] at h1sq
    calc D ≤ 4 * (H₁ ^ 2 * H₂ ^ 2) := by convert h2 using 1; ring
      _ ≤ 500000 * (H₁ ^ 2 * H₂ ^ 2) := by gcongr; norm_num
      _ = M := by dsimp [M]; ring
  have hS_le : |S| ≤ M := by
    have hab : |a₁ * b₂ + a₂ * b₁| ≤ 2 * H₁ * H₂ := by
      calc |a₁ * b₂ + a₂ * b₁| ≤ |a₁ * b₂| + |a₂ * b₁| := abs_add_le _ _
        _ = |a₁| * b₂ + |a₂| * b₁ := by rw [abs_mul, abs_mul, abs_of_pos hb₁_pos, abs_of_pos hb₂_pos]
        _ ≤ H₁ * H₂ + H₂ * H₁ := add_le_add (mul_le_mul ha₁_le hb₂_le (by positivity) hH₁_nonneg)
            (mul_le_mul ha₂_le hb₁_le (by positivity) hH₂_nonneg)
        _ = 2 * H₁ * H₂ := by ring
    have h1 : |2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁)| ≤ 4 * H₁ ^ 2 * H₂ ^ 2 := by
      calc |2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁)|
          = 2 * |a₁| * |a₂| * |a₁ * b₂ + a₂ * b₁| := by
              rw [abs_mul, abs_mul, abs_mul, show |(2 : ℤ)| = 2 by decide]
        _ ≤ 2 * H₁ * H₂ * (2 * H₁ * H₂) := by gcongr
        _ = 4 * H₁ ^ 2 * H₂ ^ 2 := by ring
    have h2 : |139968 * b₁ ^ 2 * b₂ ^ 2| ≤ 139968 * H₁ ^ 2 * H₂ ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
      gcongr
    calc |S| = |2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁) - 139968 * b₁ ^ 2 * b₂ ^ 2| := rfl
      _ ≤ |2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁)| + |139968 * b₁ ^ 2 * b₂ ^ 2| := abs_sub _ _
      _ ≤ 4 * H₁ ^ 2 * H₂ ^ 2 + 139968 * H₁ ^ 2 * H₂ ^ 2 := add_le_add h1 h2
      _ = 139972 * (H₁ ^ 2 * H₂ ^ 2) := by ring
      _ ≤ 500000 * (H₁ ^ 2 * H₂ ^ 2) := by gcongr; norm_num
      _ = M := by dsimp [M]; ring
  have hP_le : |P_num| ≤ M := by
    have ha1s : a₁ ^ 2 ≤ H₁ ^ 2 := sq_le_sq.mpr (by rw [abs_of_nonneg hH₁_nonneg]; exact ha₁_le)
    have ha2s : a₂ ^ 2 ≤ H₂ ^ 2 := sq_le_sq.mpr (by rw [abs_of_nonneg hH₂_nonneg]; exact ha₂_le)
    have h1 : |(a₁ * a₂) ^ 2| ≤ H₁ ^ 2 * H₂ ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_mul ha1s ha2s (sq_nonneg _) (by positivity)
    have hab : |a₁ * b₂ + a₂ * b₁| ≤ 2 * H₁ * H₂ := by
      calc |a₁ * b₂ + a₂ * b₁| ≤ |a₁ * b₂| + |a₂ * b₁| := abs_add_le _ _
        _ = |a₁| * b₂ + |a₂| * b₁ := by rw [abs_mul, abs_mul, abs_of_pos hb₁_pos, abs_of_pos hb₂_pos]
        _ ≤ H₁ * H₂ + H₂ * H₁ := add_le_add (mul_le_mul ha₁_le hb₂_le (by positivity) hH₁_nonneg)
            (mul_le_mul ha₂_le hb₁_le (by positivity) hH₂_nonneg)
        _ = 2 * H₁ * H₂ := by ring
    have h2 : |139968 * b₁ * b₂ * (a₁ * b₂ + a₂ * b₁)| ≤ 279936 * H₁ ^ 2 * H₂ ^ 2 := by
      calc |139968 * b₁ * b₂ * (a₁ * b₂ + a₂ * b₁)|
          = 139968 * b₁ * b₂ * |a₁ * b₂ + a₂ * b₁| := by
              rw [abs_mul, abs_mul, abs_mul, show |(139968 : ℤ)| = 139968 by decide,
                abs_of_pos hb₁_pos, abs_of_pos hb₂_pos]
        _ ≤ 139968 * H₁ * H₂ * (2 * H₁ * H₂) := by gcongr
        _ = 279936 * H₁ ^ 2 * H₂ ^ 2 := by ring
    calc |P_num| ≤ |(a₁ * a₂) ^ 2| + |139968 * b₁ * b₂ * (a₁ * b₂ + a₂ * b₁)| := abs_add_le _ _
      _ ≤ H₁ ^ 2 * H₂ ^ 2 + 279936 * H₁ ^ 2 * H₂ ^ 2 := add_le_add h1 h2
      _ = 279937 * (H₁ ^ 2 * H₂ ^ 2) := by ring
      _ ≤ 500000 * (H₁ ^ 2 * H₂ ^ 2) := by gcongr; norm_num
      _ = M := by dsimp [M]; ring
  have hbb_le : bP * bM ≤ M := by
    have hle : bP * bM ≤ D := by
      calc bP * bM ≤ (bP * bM) * k := le_mul_of_one_le_right (mul_pos hbP_pos hbM_pos).le hk_pos
        _ = D := hk.symm
    exact le_trans hle hD_le
  have hsum_le : |aP * bM + aM * bP| ≤ M := by
    have hle : |aP * bM + aM * bP| ≤ |S| := by
      calc |aP * bM + aM * bP| ≤ k * |aP * bM + aM * bP| := le_mul_of_one_le_left (abs_nonneg _) hk_pos
        _ = |S| := by rw [← abs_of_pos (show 0 < k by omega), ← abs_mul, hS_eq]
    exact le_trans hle hS_le
  have hprod_le : |aP * aM| ≤ M := by
    have hle : |aP * aM| ≤ |P_num| := by
      calc |aP * aM| ≤ k * |aP * aM| := le_mul_of_one_le_left (abs_nonneg _) hk_pos
        _ = |P_num| := by rw [← abs_of_pos (show 0 < k by omega), ← abs_mul, hP_eq]
    exact le_trans hle hP_le
  have hxy_prod : |(aP * bM) * (aM * bP)| ≤ M ^ 2 := by
    calc |(aP * bM) * (aM * bP)| = |aP * aM| * (bP * bM) := by
            rw [show (aP * bM) * (aM * bP) = (aP * aM) * (bP * bM) by ring, abs_mul,
              abs_of_pos (mul_pos hbP_pos hbM_pos)]
      _ ≤ M * M := mul_le_mul hprod_le hbb_le (by positivity) hM_nonneg
      _ = M ^ 2 := (sq M).symm
  have hsplit := abs_split_bound hM_nonneg hsum_le hxy_prod
  have h11 : |aP| * |aM| ≤ 2 * M := by
    rw [← abs_mul]; exact le_trans hprod_le (le_mul_of_one_le_left hM_nonneg (by omega))
  have h12 : |aP| * bM ≤ 2 * M := by
    simpa [abs_mul, abs_of_pos hbM_pos] using hsplit.1
  have h21 : bP * |aM| ≤ 2 * M := by
    simpa [mul_comm, abs_mul, abs_of_pos hbP_pos] using hsplit.2
  have h22 : bP * bM ≤ 2 * M := le_trans hbb_le (le_mul_of_one_le_left hM_nonneg (by omega))
  have hmax_int : max |aP| bP * max |aM| bM ≤ 2 * M := by
    rcases le_total |aP| bP with hA | hA <;> rcases le_total |aM| bM with hB | hB <;>
      simp [hA, hB] <;> assumption
  calc max |aP| bP * max |aM| bM ≤ 2 * M := hmax_int
    _ = 1000000 * H₁ ^ 2 * H₂ ^ 2 := by dsimp [M]; ring

lemma height_parallelogram {u₁ v₁ u₂ v₂ : ℚ} {h₁ : W.Nonsingular u₁ v₁} {h₂ : W.Nonsingular u₂ v₂}
    (hx : u₁ ≠ u₂) :
    H (Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂) *
      H (Point.some u₁ v₁ h₁ - Point.some u₂ v₂ h₂) ≤
      1000000 * (H (Point.some u₁ v₁ h₁)) ^ 2 * (H (Point.some u₂ v₂ h₂)) ^ 2 := by
  have hxy_add : ¬(u₁ = u₂ ∧ v₁ = -v₂) := fun h => hx h.1
  have hxy_sub : ¬(u₁ = u₂ ∧ v₁ = -(-v₂)) := fun h => hx h.1
  have hneg₂ : W.Nonsingular u₂ (-v₂) := by
    have hn := (WeierstrassCurve.Affine.nonsingular_neg (W' := W) u₂ v₂).mpr h₂
    rwa [W_negY] at hn
  have hsub_eq : Point.some u₁ v₁ h₁ - Point.some u₂ v₂ h₂ =
      Point.some u₁ v₁ h₁ + Point.some u₂ (-v₂) hneg₂ := by
    rw [sub_eq_add_neg, Point.neg_some]
    congr 1
    simp [W]
  rw [W_add_some hxy_add, hsub_eq, W_add_some hxy_sub]
  let uP := W.addX u₁ u₂ (W.slope u₁ u₂ v₁ v₂)
  let uM := W.addX u₁ u₂ (W.slope u₁ u₂ v₁ (-v₂))
  change max uP.num.natAbs uP.den * max uM.num.natAbs uM.den ≤
      1000000 * (max u₁.num.natAbs u₁.den) ^ 2 * (max u₂.num.natAbs u₂.den) ^ 2
  have heq₁ : v₁ ^ 2 = u₁ ^ 3 - 34992 := (W_eq_iff u₁ v₁).mp h₁.1
  have heq₂ : v₂ ^ 2 = u₂ ^ 3 - 34992 := (W_eq_iff u₂ v₂).mp h₂.1
  have hsum_prod := addX_sum_prod_eq heq₁ heq₂ hx
  rcases hsum_prod with ⟨hD_pos, hu_sum, hu_prod⟩
  let a₁ : ℤ := u₁.num
  let b₁ : ℤ := u₁.den
  let a₂ : ℤ := u₂.num
  let b₂ : ℤ := u₂.den
  let aP : ℤ := uP.num
  let bP : ℤ := uP.den
  let aM : ℤ := uM.num
  let bM : ℤ := uM.den
  have hDq : (((a₂ * b₁ - a₁ * b₂) ^ 2 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hD_pos.ne'
  have hbPq : (bP : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr uP.den_nz
  have hbMq : (bM : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr uM.den_nz
  have huP_q : uP = (aP : ℚ) / bP := (uP.num_div_den).symm
  have huM_q : uM = (aM : ℚ) / bM := (uM.num_div_den).symm
  have hS_rel : bP * bM * (2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁) - 139968 * b₁ ^ 2 * b₂ ^ 2) =
      (a₂ * b₁ - a₁ * b₂) ^ 2 * (aP * bM + aM * bP) := by
    have hq : uP + uM = (2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁) - 139968 * b₁ ^ 2 * b₂ ^ 2 : ℤ) /
        ((a₂ * b₁ - a₁ * b₂) ^ 2 : ℤ) := hu_sum
    rw [huP_q, huM_q] at hq
    have hmul : (bP : ℚ) * bM * (2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁) - 139968 * b₁ ^ 2 * b₂ ^ 2) =
        ((a₂ * b₁ - a₁ * b₂) ^ 2 : ℤ) * (aP * bM + aM * bP) := by
      field_simp [hbPq, hbMq, hDq] at hq
      push_cast at hq ⊢
      linarith
    exact_mod_cast hmul
  have hP_rel : bP * bM * ((a₁ * a₂) ^ 2 + 139968 * b₁ * b₂ * (a₁ * b₂ + a₂ * b₁)) =
      (a₂ * b₁ - a₁ * b₂) ^ 2 * (aP * aM) := by
    have hq : uP * uM = ((a₁ * a₂) ^ 2 + 139968 * b₁ * b₂ * (a₁ * b₂ + a₂ * b₁) : ℤ) /
        ((a₂ * b₁ - a₁ * b₂) ^ 2 : ℤ) := hu_prod
    rw [huP_q, huM_q] at hq
    have hmul : (bP : ℚ) * bM * ((a₁ * a₂) ^ 2 + 139968 * b₁ * b₂ * (a₁ * b₂ + a₂ * b₁)) =
        ((a₂ * b₁ - a₁ * b₂) ^ 2 : ℤ) * (aP * aM) := by
      field_simp [hbPq, hbMq, hDq] at hq
      push_cast at hq ⊢
      linarith
    exact_mod_cast hmul
  have hint := height_parallelogram_int
    (Int.natCast_pos.mpr u₁.pos) (Int.natCast_pos.mpr u₂.pos)
    (Int.natCast_pos.mpr uP.pos) (Int.natCast_pos.mpr uM.pos)
    (by simpa [aP, bP] using uP.reduced) (by simpa [aM, bM] using uM.reduced)
    hD_pos hS_rel hP_rel
  have hcast : ((max uP.num.natAbs uP.den * max uM.num.natAbs uM.den : ℕ) : ℤ) =
      max |aP| bP * max |aM| bM := by
    push_cast; simp [aP, bP, aM, bM]
  have hcast_rhs : ((1000000 * (max u₁.num.natAbs u₁.den) ^ 2 * (max u₂.num.natAbs u₂.den) ^ 2 : ℕ) : ℤ) =
      1000000 * (max |a₁| b₁) ^ 2 * (max |a₂| b₂) ^ 2 := by
    push_cast; simp [a₁, b₁, a₂, b₂]
  have hint' : (max uP.num.natAbs uP.den * max uM.num.natAbs uM.den : ℤ) ≤
      1000000 * (max u₁.num.natAbs u₁.den) ^ 2 * (max u₂.num.natAbs u₂.den) ^ 2 := by
    rw [← hcast, ← hcast_rhs] at hint
    exact_mod_cast hint
  exact_mod_cast hint'

lemma h_parallelogram {u₁ v₁ u₂ v₂ : ℚ} {h₁ : W.Nonsingular u₁ v₁} {h₂ : W.Nonsingular u₂ v₂}
    (hx : u₁ ≠ u₂) :
    h (Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂) + h (Point.some u₁ v₁ h₁ - Point.some u₂ v₂ h₂) ≤
      2 * h (Point.some u₁ v₁ h₁) + 2 * h (Point.some u₂ v₂ h₂) + Real.log 1000000 := by
  have hp := @height_parallelogram u₁ v₁ u₂ v₂ h₁ h₂ hx
  have hH₁ : (0 : ℝ) < H (Point.some u₁ v₁ h₁) := by exact_mod_cast H_pos _
  have hH₂ : (0 : ℝ) < H (Point.some u₂ v₂ h₂) := by exact_mod_cast H_pos _
  have hHp : (0 : ℝ) < H (Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂) := by exact_mod_cast H_pos _
  have hHm : (0 : ℝ) < H (Point.some u₁ v₁ h₁ - Point.some u₂ v₂ h₂) := by exact_mod_cast H_pos _
  have hpR : (H (Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂) : ℝ) *
      H (Point.some u₁ v₁ h₁ - Point.some u₂ v₂ h₂) ≤
      1000000 * (H (Point.some u₁ v₁ h₁) : ℝ) ^ 2 * (H (Point.some u₂ v₂ h₂) : ℝ) ^ 2 := by
    exact_mod_cast hp
  have hlog := Real.log_le_log (mul_pos hHp hHm) hpR
  rw [Real.log_mul hHp.ne' hHm.ne', Real.log_mul (by positivity) (pow_ne_zero 2 hH₂.ne'),
    Real.log_mul (by norm_num) (pow_ne_zero 2 hH₁.ne'), Real.log_pow, Real.log_pow] at hlog
  dsimp [h]
  push_cast at hlog ⊢
  linarith

lemma hP_ns : W.Nonsingular 36 108 :=
  W_nonsingular ((W_eq_iff 36 108).mpr (by norm_num))

lemma h_nsmul_step (k : ℕ) (hk : 2 ≤ k) :
    h ((k + 1) • P) + h ((k - 1) • P) ≤ 2 * h (k • P) + 200 := by
  rcases nsmul_P_some k (by omega) with ⟨uk, vk, hk_ns, hkp⟩
  have hP_def : P = Point.some 36 108 hP_ns := rfl
  have hne36 : uk ≠ 36 := by
    intro heq
    have hk1 := xCoord_injective (by omega) le_rfl hkp hP_def heq
    omega
  have hp_eq := h_parallelogram (h₁ := hk_ns) (h₂ := hP_ns) hne36
  have hadd : Point.some uk vk hk_ns + Point.some 36 108 hP_ns = (k + 1) • P := by
    rw [← hkp, ← hP_def, add_nsmul, one_nsmul]
  have hsub : Point.some uk vk hk_ns - Point.some 36 108 hP_ns = (k - 1) • P := by
    symm
    apply eq_sub_of_add_eq
    rw [← hkp, ← hP_def, ← succ_nsmul, show k - 1 + 1 = k by omega]
  rw [hadd, hsub, ← hkp] at hp_eq
  have hP_val : h (Point.some 36 108 hP_ns) = Real.log 36 := by
    simp [h, H]
  rw [hP_val] at hp_eq
  have hlog36 : Real.log 36 ≤ 35 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 36)
    linarith
  have hlog10 : Real.log 10 ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    linarith
  have hlog1e6 : Real.log 1000000 ≤ 54 := by
    have hpow : (1000000 : ℝ) = (10 : ℝ) ^ (6 : ℕ) := by norm_num
    rw [hpow, Real.log_pow]
    push_cast
    linarith
  linarith

lemma h_nsmul_diff (k : ℕ) (hk : 1 ≤ k) :
    h ((k + 1) • P) - h (k • P) ≤ 200 * (k : ℝ) := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      have h1 : h ((1 : ℕ) • P) = Real.log 36 := by
        rw [one_nsmul, P_def]
        simp [h, H]
      have h2 : h ((2 : ℕ) • P) = Real.log 252 := by
        rw [two_smul_P, mkPt]
        simp [h, H]
      rw [h1, h2]
      have hdiff : Real.log 252 - Real.log 36 = Real.log 7 := by
        rw [← Real.log_div (by norm_num) (by norm_num)]
        norm_num
      have hlog7 : Real.log 7 ≤ 6 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7)
        linarith
      push_cast
      linarith
    | succ k =>
      have hk1 : 1 ≤ k + 1 := by omega
      have hk_ge2 : 2 ≤ k + 2 := by omega
      have hstep := h_nsmul_step (k + 2) hk_ge2
      have hsub1 : (k + 2 - 1) = k + 1 := by omega
      rw [hsub1] at hstep
      have ihk := ih hk1
      push_cast at hstep ihk ⊢
      linarith

lemma h_nsmul_le (k : ℕ) (hk : 1 ≤ k) : h (k • P) ≤ 100 * (k : ℝ) ^ 2 := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      have h1 : h ((1 : ℕ) • P) = Real.log 36 := by
        rw [one_nsmul, P_def]
        simp [h, H]
      rw [h1]
      have hlog36 : Real.log 36 ≤ 35 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 36)
        linarith
      push_cast
      linarith
    | succ k =>
      have hk1 : 1 ≤ k + 1 := by omega
      have ihk := ih hk1
      have hdiff := h_nsmul_diff (k + 1) hk1
      push_cast at ihk hdiff ⊢
      nlinarith

/- ### Part C: Positive-cube arc DAG (`|v| < 324`) -/

def isGood (Q : W.Point) : Prop :=
  ∃ u v h, Q = Point.some u v h ∧ |v| < 324

lemma add_P_coords {u v : ℚ} {hq : W.Nonsingular u v} (hu36 : u ≠ 36) :
    let u' := 36 * (u ^ 2 + 36 * u - 1944 - 6 * v) / (u - 36) ^ 2
    let v' := 108 * (u ^ 3 + 108 * u ^ 2 - 139968 - 36 * (u - 24) * v) / (u - 36) ^ 3
    ∃ h' : W.Nonsingular u' v', Point.some u v hq + P = Point.some u' v' h' := by
  intro u' v'
  have hP_def : P = Point.some 36 108 hP_ns := rfl
  have hxy : ¬(u = 36 ∧ v = -108) := fun h => hu36 h.1
  have heq : v ^ 2 = u ^ 3 - 34992 := (W_eq_iff u v).mp hq.1
  have hu36_ne : u - 36 ≠ 0 := sub_ne_zero.mpr hu36
  have hu_add : W.addX u 36 (W.slope u 36 v 108) = u' := by
    dsimp [u', WeierstrassCurve.Affine.addX, W]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hu36]
    field_simp [hu36_ne]
    linear_combination (norm := ring) heq
  have hv_add : W.addY u 36 v (W.slope u 36 v 108) = v' := by
    change -(W.slope u 36 v 108 * (W.addX u 36 (W.slope u 36 v 108) - u) + v) - W.a₁ * _ - W.a₃ = v'
    rw [hu_add, WeierstrassCurve.Affine.slope_of_X_ne hu36]
    simp only [W, zero_mul, sub_zero]
    dsimp [u', v']
    field_simp [hu36_ne]
    linear_combination (norm := ring) 216 * heq
  have hns' : W.Nonsingular u' v' := by
    rw [← hu_add, ← hv_add]
    exact WeierstrassCurve.Affine.nonsingular_add hq hP_ns (by rw [W_negY]; exact hxy)
  refine ⟨hns', ?_⟩
  rw [hP_def, W_add_some hxy]
  congr 1

lemma u_gt_51_of_abs_v_ge {u v : ℚ} (heq : v ^ 2 = u ^ 3 - 34992) (hu : 0 < u) (hv : 324 ≤ |v|) :
    51 < u := by
  have hv2 : 104976 ≤ v ^ 2 := by
    have h : (324 : ℚ) ^ 2 ≤ |v| ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self (by norm_num) hv
    rw [sq_abs] at h
    linarith
  have hu3 : 51 ^ 3 < u ^ 3 := by linarith
  by_contra hle
  push Not at hle
  have h1 : u ^ 3 ≤ 51 ^ 3 := by nlinarith [sq_nonneg u]
  linarith

lemma abs_v_lt_of_u_lt {u v : ℚ} (heq : v ^ 2 = u ^ 3 - 34992) (hu0 : 0 < u) (hu : u < 51) :
    |v| < 324 := by
  have hu3 : u ^ 3 < 51 ^ 3 := by nlinarith [sq_nonneg u]
  have hv2 : v ^ 2 < 324 ^ 2 := by linarith
  rw [← sq_abs] at hv2
  by_contra hge
  push Not at hge
  have h1 : (324 : ℚ) ^ 2 ≤ |v| ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (by norm_num) hge
  linarith

lemma abs_v_gt_12 {u v : ℚ} (heq : v ^ 2 = u ^ 3 - 34992) (hu : 36 < u) :
    12 * u - 324 < |v| := by
  have hdiff : v ^ 2 - (12 * u - 324) ^ 2 = (u - 36) * ((u - 54) ^ 2 + 972) := by
    linear_combination (norm := ring) heq
  have hpos : 0 < v ^ 2 - (12 * u - 324) ^ 2 := by
    rw [hdiff]
    have h1 : 0 < u - 36 := by linarith
    have h2 : 0 < (u - 54) ^ 2 + 972 := by nlinarith [sq_nonneg (u - 54)]
    exact mul_pos h1 h2
  rw [← sq_abs] at hpos
  by_contra hle
  push Not at hle
  have hb : 0 ≤ 12 * u - 324 := by linarith
  have hsq : |v| ^ 2 ≤ (12 * u - 324) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (abs_nonneg v) hle
  linarith

lemma abs_v_gt_14 {u v : ℚ} (heq : v ^ 2 = u ^ 3 - 34992) (hu : 108 ≤ u) :
    14 * u - 460 < |v| := by
  set t := u - 108
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hdiff : v ^ 2 - (14 * u - 460) ^ 2 = t ^ 3 + 128 * t ^ 2 + 5536 * t + 118016 := by
    dsimp [t]
    linear_combination (norm := ring) heq
  have hpos : 0 < v ^ 2 - (14 * u - 460) ^ 2 := by
    rw [hdiff]
    nlinarith [sq_nonneg t]
  rw [← sq_abs] at hpos
  by_contra hle
  push Not at hle
  have hsq : |v| ^ 2 ≤ (14 * u - 460) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (abs_nonneg v) hle
  linarith

lemma dag_U2 {u v : ℚ} {hq : W.Nonsingular u v} (hv : 324 ≤ v) (hu : 108 ≤ u) :
    isGood (Point.some u v hq + P) := by
  have hpos := W_u_pos hq.1
  have hu36 : u ≠ 36 := by linarith
  rcases add_P_coords (hq := hq) hu36 with ⟨h', hadd⟩
  set u' := 36 * (u ^ 2 + 36 * u - 1944 - 6 * v) / (u - 36) ^ 2
  set v' := 108 * (u ^ 3 + 108 * u ^ 2 - 139968 - 36 * (u - 24) * v) / (u - 36) ^ 3
  have heq := (W_eq_iff u v).mp hq.1
  have heq' := (W_eq_iff u' v').mp h'.1
  have hv_pos : 0 < v := by linarith
  have hv14 : 14 * u - 460 < v := by
    have := abs_v_gt_14 heq hu
    rwa [abs_of_pos hv_pos] at this
  have hu'lt : u' < 51 := by
    set t := u - 108
    have ht : 0 ≤ t := by dsimp [t]; linarith
    have hden_pos : 0 < (u - 36) ^ 2 := sq_pos_iff.mpr (sub_ne_zero.mpr hu36)
    have hnum : 36 * (u ^ 2 + 36 * u - 1944 - 6 * v) < 51 * (u - 36) ^ 2 := by
      have h1 : 36 * (u ^ 2 + 36 * u - 1944 - 6 * v) <
          36 * (u ^ 2 + 36 * u - 1944 - 6 * (14 * u - 460)) := by linarith
      have h2 : 51 * (u - 36) ^ 2 - 36 * (u ^ 2 + 36 * u - 1944 - 6 * (14 * u - 460)) =
          15 * t ^ 2 + 1296 * t + 1728 := by dsimp [t]; ring
      have h3 : 0 < 15 * t ^ 2 + 1296 * t + 1728 := by nlinarith [sq_nonneg t]
      linarith
    dsimp [u']
    rwa [div_lt_iff₀ hden_pos]
  have hu'pos := W_u_pos h'.1
  exact ⟨u', v', h', hadd, abs_v_lt_of_u_lt heq' hu'pos hu'lt⟩

lemma dag_L1 {u v : ℚ} {hq : W.Nonsingular u v} (hv : v ≤ -324) (hu : u ≤ 108) :
    ∃ u' v' h', Point.some u v hq + P = Point.some u' v' h' ∧ 324 ≤ v' ∧ 108 ≤ u' := by
  have heq := (W_eq_iff u v).mp hq.1
  have hu_pos := W_u_pos hq.1
  have hv_abs : 324 ≤ |v| := by rw [abs_of_neg (by linarith)]; linarith
  have hu51 : 51 < u := u_gt_51_of_abs_v_ge heq hu_pos hv_abs
  have hu36 : u ≠ 36 := by linarith
  rcases add_P_coords (hq := hq) hu36 with ⟨h', hadd⟩
  set u' := 36 * (u ^ 2 + 36 * u - 1944 - 6 * v) / (u - 36) ^ 2
  set v' := 108 * (u ^ 3 + 108 * u ^ 2 - 139968 - 36 * (u - 24) * v) / (u - 36) ^ 3
  have hv12 : 12 * u - 324 < -v := by
    have := abs_v_gt_12 heq (by linarith)
    rwa [abs_of_neg (by linarith)] at this
  have hden2 : 0 < (u - 36) ^ 2 := sq_pos_iff.mpr (sub_ne_zero.mpr hu36)
  have hden3 : 0 < (u - 36) ^ 3 := pow_pos (by linarith) 3
  have hu'ge : 108 ≤ u' := by
    have hnum : 108 * (u - 36) ^ 2 ≤ 36 * (u ^ 2 + 36 * u - 1944 - 6 * v) := by
      have h1 : 36 * (u ^ 2 + 36 * u - 1944 + 6 * (12 * u - 324)) <
          36 * (u ^ 2 + 36 * u - 1944 - 6 * v) := by linarith
      have h2 : 36 * (u ^ 2 + 36 * u - 1944 + 6 * (12 * u - 324)) - 108 * (u - 36) ^ 2 =
          72 * ((u - 36) * (126 - u) + 648) := by ring
      have h3 : 0 < (u - 36) * (126 - u) + 648 := by
        have hm : 0 ≤ (u - 36) * (126 - u) := mul_nonneg (by linarith) (by linarith)
        linarith
      linarith
    dsimp [u']
    rwa [le_div_iff₀ hden2]
  have hv'ge : 324 ≤ v' := by
    have hnum : 324 * (u - 36) ^ 3 ≤ 108 * (u ^ 3 + 108 * u ^ 2 - 139968 - 36 * (u - 24) * v) := by
      have h1 : 108 * (u ^ 3 + 108 * u ^ 2 - 139968 + 36 * (u - 24) * 324) ≤
          108 * (u ^ 3 + 108 * u ^ 2 - 139968 - 36 * (u - 24) * v) := by
        have hmul : 36 * (u - 24) * 324 ≤ -36 * (u - 24) * v := by nlinarith
        linarith
      have h2 : (u ^ 3 + 108 * u ^ 2 - 139968 + 36 * (u - 24) * 324) - 3 * (u - 36) ^ 3 =
          2 * u ^ 2 * (216 - u) - 279936 := by ring
      have hu2 : (51 : ℚ) ^ 2 ≤ u ^ 2 := by nlinarith
      have h216 : (108 : ℚ) ≤ 216 - u := by linarith
      have h3 : 279936 ≤ 2 * u ^ 2 * (216 - u) := by
        calc (279936 : ℚ) ≤ 2 * 51 ^ 2 * 108 := by norm_num
          _ ≤ 2 * u ^ 2 * (216 - u) := by gcongr
      linarith
    dsimp [v']
    rwa [le_div_iff₀ hden3]
  exact ⟨u', v', h', hadd, hv'ge, hu'ge⟩

lemma dag_U1 {u v : ℚ} {hq : W.Nonsingular u v} (hv : 324 ≤ v) (_hu : u < 108) :
    isGood (Point.some u v hq + P) ∨
      ∃ u' v' h', Point.some u v hq + P = Point.some u' v' h' ∧ v' ≤ -324 ∧ u' ≤ 108 := by
  have heq := (W_eq_iff u v).mp hq.1
  have hu_pos := W_u_pos hq.1
  have hv_abs : 324 ≤ |v| := by rw [abs_of_pos (by linarith)]; linarith
  have hu51 : 51 < u := u_gt_51_of_abs_v_ge heq hu_pos hv_abs
  have hu36 : u ≠ 36 := by linarith
  rcases add_P_coords (hq := hq) hu36 with ⟨h', hadd⟩
  set u' := 36 * (u ^ 2 + 36 * u - 1944 - 6 * v) / (u - 36) ^ 2
  set v' := 108 * (u ^ 3 + 108 * u ^ 2 - 139968 - 36 * (u - 24) * v) / (u - 36) ^ 3
  have hv12 : 12 * u - 324 < v := by
    have := abs_v_gt_12 heq (by linarith)
    rwa [abs_of_pos (by linarith)] at this
  have hden2 : 0 < (u - 36) ^ 2 := sq_pos_iff.mpr (sub_ne_zero.mpr hu36)
  have hden3 : 0 < (u - 36) ^ 3 := pow_pos (by linarith) 3
  have hu'le : u' ≤ 108 := by
    have hnum : 36 * (u ^ 2 + 36 * u - 1944 - 6 * v) ≤ 108 * (u - 36) ^ 2 := by
      rcases le_or_gt u 54 with hu54 | hu54
      · have h1 : 108 * (u - 36) ^ 2 - 36 * (u ^ 2 + 36 * u - 1944 - 6 * 324) =
            72 * ((54 - u) * (72 - u)) := by ring
        have h2 : 0 ≤ (54 - u) * (72 - u) := mul_nonneg (by linarith) (by linarith)
        linarith
      · have h1 : 108 * (u - 36) ^ 2 - 36 * (u ^ 2 + 36 * u - 1944 - 6 * (12 * u - 324)) =
            72 * ((u - 36) * (u - 54)) := by ring
        have h2 : 0 ≤ (u - 36) * (u - 54) := mul_nonneg (by linarith) (by linarith)
        linarith
    dsimp [u']
    rwa [div_le_iff₀ hden2]
  have hv'lt : v' < 324 := by
    set t := u - 51
    have ht : 0 ≤ t := by dsimp [t]; linarith
    have hnum : 108 * (u ^ 3 + 108 * u ^ 2 - 139968 - 36 * (u - 24) * v) < 324 * (u - 36) ^ 3 := by
      have hmul : 36 * (u - 24) * (12 * u - 324) < 36 * (u - 24) * v := by nlinarith
      have h2 : 3 * (u - 36) ^ 3 - (u ^ 3 + 108 * u ^ 2 - 139968 - 36 * (u - 24) * (12 * u - 324)) =
          2 * t ^ 3 + 306 * t ^ 2 + 5238 * t + 16470 := by dsimp [t]; ring
      have h3 : 0 < 2 * t ^ 3 + 306 * t ^ 2 + 5238 * t + 16470 := by nlinarith [sq_nonneg t]
      linarith
    dsimp [v']
    rwa [div_lt_iff₀ hden3]
  by_cases hgood : |v'| < 324
  · exact Or.inl ⟨u', v', h', hadd, hgood⟩
  · right
    have hv'le : v' ≤ -324 := by
      have habs : 324 ≤ |v'| := not_lt.mp hgood
      rcases le_or_gt 0 v' with h0 | h0
      · rw [abs_of_nonneg h0] at habs; linarith
      · rw [abs_of_neg h0] at habs; linarith
    exact ⟨u', v', h', hadd, hv'le, hu'le⟩

lemma dag_L2 {u v : ℚ} {hq : W.Nonsingular u v} (hv : v ≤ -324) (hu : 108 < u) :
    ∃ u' v' h', Point.some u v hq + P = Point.some u' v' h' ∧ 0 < v' := by
  have hu36 : u ≠ 36 := by linarith
  rcases add_P_coords (hq := hq) hu36 with ⟨h', hadd⟩
  set u' := 36 * (u ^ 2 + 36 * u - 1944 - 6 * v) / (u - 36) ^ 2
  set v' := 108 * (u ^ 3 + 108 * u ^ 2 - 139968 - 36 * (u - 24) * v) / (u - 36) ^ 3
  have hden3 : 0 < (u - 36) ^ 3 := pow_pos (by linarith) 3
  have hpos : 0 < v' := by
    dsimp [v']
    apply div_pos _ hden3
    have hu3 : (139968 : ℚ) < u ^ 3 := by nlinarith [sq_nonneg u]
    have hvu : 0 < -(36 * (u - 24) * v) := by nlinarith
    nlinarith [sq_nonneg u]
  exact ⟨u', v', h', hadd, hpos⟩

lemma exists_good_in_five (j : ℕ) :
    ∃ i ∈ Finset.Icc (5 * j + 1) (5 * j + 5), isGood (i • P) := by
  have hstep1 : ∀ (u v : ℚ) (hq : W.Nonsingular u v),
      isGood (Point.some u v hq) ∨ isGood (Point.some u v hq + P) ∨
        isGood (Point.some u v hq + 2 • P) ∨ isGood (Point.some u v hq + 3 • P) ∨
        isGood (Point.some u v hq + 4 • P) := by
    intro u v hq
    by_cases hg0 : |v| < 324
    · exact Or.inl ⟨u, v, hq, rfl, hg0⟩
    right
    have hv_abs : 324 ≤ |v| := not_lt.mp hg0
    rcases le_or_gt 324 v with hv_pos | hv_lt
    · rcases le_or_gt 108 u with hu_ge | hu_lt
      · exact Or.inl (dag_U2 hv_pos hu_ge)
      · rcases dag_U1 hv_pos hu_lt with hg1 | ⟨u₁, v₁, h₁, had₁, hv₁, hu₁⟩
        · exact Or.inl hg1
        · rcases dag_L1 hv₁ hu₁ with ⟨u₂, v₂, h₂, had₂, hv₂, hu₂⟩
          right; right; left
          have h3 : Point.some u v hq + 3 • P = Point.some u₂ v₂ h₂ + P := by
            rw [show (3 : ℕ) = 1 + 1 + 1 by rfl, add_nsmul, add_nsmul, one_nsmul, ← add_assoc,
              ← add_assoc, had₁, had₂]
          rw [h3]
          exact dag_U2 hv₂ hu₂
    · have hv_le : v ≤ -324 := by
        rcases lt_or_ge v 0 with hn | hp
        · rw [abs_of_neg hn] at hv_abs; linarith
        · rw [abs_of_nonneg hp] at hv_abs; linarith
      rcases le_or_gt u 108 with hu_le | hu_gt
      · rcases dag_L1 hv_le hu_le with ⟨u₁, v₁, h₁, had₁, hv₁, hu₁⟩
        right; left
        rw [show Point.some u v hq + 2 • P = Point.some u v hq + P + P by
          rw [two_nsmul, add_assoc], had₁]
        exact dag_U2 hv₁ hu₁
      · rcases dag_L2 hv_le hu_gt with ⟨u₁, v₁, h₁, had₁, hv₁_pos⟩
        by_cases hg1 : |v₁| < 324
        · exact Or.inl ⟨u₁, v₁, h₁, had₁, hg1⟩
        have hv₁_ge : 324 ≤ v₁ := by
          have := not_lt.mp hg1
          rwa [abs_of_pos hv₁_pos] at this
        rcases le_or_gt 108 u₁ with hu₁_ge | hu₁_lt
        · right; left
          rw [show Point.some u v hq + 2 • P = Point.some u v hq + P + P by
            rw [two_nsmul, add_assoc], had₁]
          exact dag_U2 hv₁_ge hu₁_ge
        · rcases dag_U1 hv₁_ge hu₁_lt with hg2 | ⟨u₂, v₂, h₂, had₂, hv₂, hu₂⟩
          · right; left
            rw [show Point.some u v hq + 2 • P = Point.some u v hq + P + P by
              rw [two_nsmul, add_assoc], had₁]
            exact hg2
          · rcases dag_L1 hv₂ hu₂ with ⟨u₃, v₃, h₃, had₃, hv₃, hu₃⟩
            right; right; right
            rw [show Point.some u v hq + 4 • P = Point.some u v hq + P + P + P + P by
              rw [show (4 : ℕ) = 1 + 1 + 1 + 1 by rfl]; simp only [add_nsmul, one_nsmul, add_assoc],
              had₁, had₂, had₃]
            exact dag_U2 hv₃ hu₃
  rcases nsmul_P_some (5 * j + 1) (by omega) with ⟨u₀, v₀, h₀, hq₀⟩
  rcases hstep1 u₀ v₀ h₀ with g0 | g1 | g2 | g3 | g4
  · exact ⟨5 * j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simpa [hq₀] using g0⟩
  · refine ⟨5 * j + 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa [show 5 * j + 2 = (5 * j + 1) + 1 by omega, add_nsmul, one_nsmul, hq₀] using g1
  · refine ⟨5 * j + 3, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa [show 5 * j + 3 = (5 * j + 1) + 2 by omega, add_nsmul, hq₀] using g2
  · refine ⟨5 * j + 4, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa [show 5 * j + 4 = (5 * j + 1) + 3 by omega, add_nsmul, hq₀] using g3
  · refine ⟨5 * j + 5, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa [show 5 * j + 5 = (5 * j + 1) + 4 by omega, add_nsmul, hq₀] using g4

lemma good_count_ge (K : ℕ) [DecidablePred (fun k : ℕ => isGood (k • P))] :
    K ≤ ((Finset.Icc 1 (5 * K)).filter (fun k => isGood (k • P))).card := by
  let f : ℕ → ℕ := fun j => Classical.choose (exists_good_in_five j)
  have hf_mem : ∀ j ∈ Finset.range K,
      f j ∈ (Finset.Icc 1 (5 * K)).filter (fun k => isGood (k • P)) := by
    intro j hj
    have hjK : j < K := Finset.mem_range.mp hj
    have hspec := Classical.choose_spec (exists_good_in_five j)
    have hicc := Finset.mem_Icc.mp hspec.1
    dsimp [f]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hspec.2⟩
  have hf_inj : ∀ j₁ ∈ Finset.range K, ∀ j₂ ∈ Finset.range K, f j₁ = f j₂ → j₁ = j₂ := by
    intro j₁ _ j₂ _ heq
    have hs₁ := Finset.mem_Icc.mp (Classical.choose_spec (exists_good_in_five j₁)).1
    have hs₂ := Finset.mem_Icc.mp (Classical.choose_spec (exists_good_in_five j₂)).1
    dsimp [f] at heq
    omega
  simpa using Finset.card_le_card_of_injOn f hf_mem (fun j₁ hj₁ j₂ hj₂ h => hf_inj j₁ hj₁ j₂ hj₂ h)

/- ### Part D: Cube representations and final `(log N)^(1/4)` bound -/

lemma W_den_cube_sq {u v : ℚ} (h : W.Equation u v) :
    u.den ^ 3 = v.den ^ 2 ∧
      let d := v.den / Nat.gcd v.den u.den
      1 ≤ d ∧ u.den = d ^ 2 ∧ v.den = d ^ 3 := by
  rw [W_eq_iff] at h
  have hu_pos := W_u_pos ((W_eq_iff u v).mpr h)
  have hbu_nz : (u.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr u.den_nz
  have hbv_nz : (v.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr v.den_nz
  have hq : ((v.num : ℚ) / v.den) ^ 2 = ((u.num : ℚ) / u.den) ^ 3 - 34992 := by
    rwa [v.num_div_den, u.num_div_den]
  have hz : v.num ^ 2 * (u.den : ℤ) ^ 3 = (v.den : ℤ) ^ 2 * (u.num ^ 3 - 34992 * (u.den : ℤ) ^ 3) := by
    have hm : (v.num : ℚ) ^ 2 * (u.den : ℚ) ^ 3 =
        (v.den : ℚ) ^ 2 * ((u.num : ℚ) ^ 3 - 34992 * (u.den : ℚ) ^ 3) := by
      field_simp [hbu_nz, hbv_nz] at hq ⊢
      linarith
    exact_mod_cast hm
  have hv_dvd : (v.den : ℤ) ^ 2 ∣ v.num ^ 2 * (u.den : ℤ) ^ 3 :=
    ⟨u.num ^ 3 - 34992 * (u.den : ℤ) ^ 3, hz⟩
  have hv_dvd_nat : v.den ^ 2 ∣ v.num.natAbs ^ 2 * u.den ^ 3 := by
    rw [← Int.natCast_dvd_natCast]
    push_cast
    simpa [Int.natAbs_sq] using hv_dvd
  have hcop_v : Nat.Coprime (v.den ^ 2) (v.num.natAbs ^ 2) := (v.reduced.symm).pow 2 2
  have hv_dvd_u : v.den ^ 2 ∣ u.den ^ 3 := hcop_v.dvd_of_dvd_mul_left hv_dvd_nat
  have hu_dvd : (u.den : ℤ) ^ 3 ∣ (v.den : ℤ) ^ 2 * u.num ^ 3 := by
    refine ⟨v.num ^ 2 + 34992 * (v.den : ℤ) ^ 2, ?_⟩
    linear_combination -hz
  have hu_dvd_nat : u.den ^ 3 ∣ u.num.natAbs ^ 3 * v.den ^ 2 := by
    rw [← Int.natCast_dvd_natCast]
    push_cast
    have ha_nonneg : 0 ≤ u.num := by
      have hd : (0 : ℚ) < u.den := Nat.cast_pos.mpr u.pos
      have hrat := u.num_div_den
      have hnum_pos : (0 : ℚ) < u.num := by
        rw [← hrat] at hu_pos
        exact (div_pos_iff_of_pos_right hd).mp hu_pos
      exact_mod_cast hnum_pos.le
    rw [abs_of_nonneg ha_nonneg, mul_comm]
    exact hu_dvd
  have hcop_u : Nat.Coprime (u.den ^ 3) (u.num.natAbs ^ 3) := (u.reduced.symm).pow 3 3
  have hu_dvd_v : u.den ^ 3 ∣ v.den ^ 2 := hcop_u.dvd_of_dvd_mul_left hu_dvd_nat
  have heq_pow : u.den ^ 3 = v.den ^ 2 := Nat.dvd_antisymm hu_dvd_v hv_dvd_u
  refine ⟨heq_pow, ?_⟩
  let g := Nat.gcd v.den u.den
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left u.den v.pos
  let d := v.den / g
  let b₁ := u.den / g
  have hd_mul : g * d = v.den := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hb₁_mul : g * b₁ = u.den := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hcop_db : Nat.Coprime d b₁ := Nat.coprime_div_gcd_div_gcd hg_pos
  have hpow_g : g ^ 2 * d ^ 2 = g ^ 3 * b₁ ^ 3 := by
    calc g ^ 2 * d ^ 2 = (g * d) ^ 2 := by ring
      _ = v.den ^ 2 := by rw [hd_mul]
      _ = u.den ^ 3 := heq_pow.symm
      _ = (g * b₁) ^ 3 := by rw [hb₁_mul]
      _ = g ^ 3 * b₁ ^ 3 := by ring
  have hd2_eq : d ^ 2 = g * b₁ ^ 3 := by
    have hg2_pos : 0 < g ^ 2 := pow_pos hg_pos 2
    have hmul : g ^ 2 * d ^ 2 = g ^ 2 * (g * b₁ ^ 3) := by linarith
    exact Nat.mul_left_cancel hg2_pos hmul
  have hb₁_dvd : b₁ ∣ d ^ 2 := ⟨g * b₁ ^ 2, by rw [hd2_eq]; ring⟩
  have hb₁_cop2 : Nat.Coprime b₁ (d ^ 2) := (hcop_db.symm).pow_right 2
  have hb₁_one : b₁ = 1 := by
    have hgcd := Nat.dvd_gcd (dvd_refl b₁) hb₁_dvd
    rw [hb₁_cop2] at hgcd
    exact Nat.eq_one_of_dvd_one hgcd
  have hgu : g = u.den := by rw [← hb₁_mul, hb₁_one, mul_one]
  have hg_d2 : g = d ^ 2 := by rw [hb₁_one, one_pow, mul_one] at hd2_eq; exact hd2_eq.symm
  have hud_d2 : u.den = d ^ 2 := hgu.symm.trans hg_d2
  have hd1 : 1 ≤ d := by
    by_contra hd0
    have hd_eq0 : d = 0 := Nat.lt_one_iff.mp (not_le.mp hd0)
    rw [hd_eq0, zero_pow (by norm_num)] at hud_d2
    exact u.den_nz hud_d2
  refine ⟨hd1, hud_d2, ?_⟩
  change v.den = d ^ 3
  rw [← hd_mul, hg_d2]
  ring

lemma good_cube_triple {k : ℕ} (_hk : 1 ≤ k) (hg : isGood (k • P)) :
    ∃ X Y Z : ℕ, 0 < X ∧ 0 < Y ∧ 6 ≤ Z ∧ X ^ 3 + Y ^ 3 = 9 * Z ^ 3 ∧
      Z ≤ 6 * (H (k • P)) ^ 2 ∧
      ∃ v h, k • P = Point.some (108 * (Z : ℚ) / ((X : ℚ) + Y)) v h := by
  rcases hg with ⟨u, v, hq, hkp, hv_lt⟩
  rcases W_den_cube_sq hq.1 with ⟨heq_pow, hd1, hud, hvd⟩
  set d := v.den / Nat.gcd v.den u.den
  have hd_pos : 0 < (d : ℤ) := Int.natCast_pos.mpr hd1
  have hu_pos := W_u_pos hq.1
  have ha_pos : 0 < u.num := by
    have hd_q : (0 : ℚ) < u.den := Nat.cast_pos.mpr u.pos
    have hnum_q : (0 : ℚ) < u.num := by
      rw [← u.num_div_den] at hu_pos
      exact (div_pos_iff_of_pos_right hd_q).mp hu_pos
    exact_mod_cast hnum_q
  have hv_abs_z : |v.num| < 324 * (d : ℤ) ^ 3 := by
    have hvd_q : (v.den : ℚ) = (d : ℚ) ^ 3 := by exact_mod_cast hvd
    have hq_lt : ((|v.num| : ℤ) : ℚ) / ((d : ℚ) ^ 3) < 324 := by
      calc ((|v.num| : ℤ) : ℚ) / ((d : ℚ) ^ 3) = |(v.num : ℚ)| / |(v.den : ℚ)| := by
              rw [Int.cast_abs, hvd_q, abs_of_pos (show (0 : ℚ) < (d : ℚ) ^ 3 by positivity)]
        _ = |(v.num : ℚ) / v.den| := (abs_div _ _).symm
        _ = |v| := by rw [v.num_div_den]
        _ < 324 := hv_lt
    have hd3_pos : (0 : ℚ) < (d : ℚ) ^ 3 := by positivity
    have hq2 : (|v.num| : ℚ) < 324 * (d : ℚ) ^ 3 := by
      have := (div_lt_iff₀ hd3_pos).mp hq_lt
      exact_mod_cast this
    exact_mod_cast hq2
  let X_z : ℤ := 324 * (d : ℤ) ^ 3 + v.num
  let Y_z : ℤ := 324 * (d : ℤ) ^ 3 - v.num
  have hXz_pos : 0 < X_z := by cases abs_lt.mp hv_abs_z; dsimp [X_z]; linarith
  have hYz_pos : 0 < Y_z := by cases abs_lt.mp hv_abs_z; dsimp [Y_z]; linarith
  let X := X_z.toNat
  let Y := Y_z.toNat
  let Z := 6 * u.num.natAbs * d
  have hX_cast : (X : ℤ) = X_z := Int.toNat_of_nonneg hXz_pos.le
  have hY_cast : (Y : ℤ) = Y_z := Int.toNat_of_nonneg hYz_pos.le
  have hX_pos : 0 < X := by omega
  have hY_pos : 0 < Y := by omega
  have ha_nat1 : 1 ≤ u.num.natAbs := by omega
  have hZ_ge : 6 ≤ Z := by dsimp [Z]; nlinarith
  have hv_sq_z : v.num ^ 2 = u.num ^ 3 - 34992 * (d : ℤ) ^ 6 := by
    have hweq := (W_eq_iff u v).mp hq.1
    have hq_u : u = (u.num : ℚ) / (d : ℚ) ^ 2 := by
      conv_lhs => rw [← u.num_div_den]
      rw [show (u.den : ℚ) = (d : ℚ) ^ 2 by exact_mod_cast hud]
    have hq_v : v = (v.num : ℚ) / (d : ℚ) ^ 3 := by
      conv_lhs => rw [← v.num_div_den]
      rw [show (v.den : ℚ) = (d : ℚ) ^ 3 by exact_mod_cast hvd]
    rw [hq_u, hq_v] at hweq
    have hd_q : (d : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne'
    have hqm : (v.num : ℚ) ^ 2 = (u.num : ℚ) ^ 3 - 34992 * (d : ℚ) ^ 6 := by
      field_simp [hd_q] at hweq
      linarith
    exact_mod_cast hqm
  have hcube : X ^ 3 + Y ^ 3 = 9 * Z ^ 3 := by
    zify
    rw [hX_cast, hY_cast]
    dsimp [X_z, Y_z, Z]
    push_cast
    rw [abs_of_nonneg ha_pos.le]
    linear_combination (norm := ring) 1944 * (d : ℤ) ^ 3 * hv_sq_z
  have hZ_le : Z ≤ 6 * (H (k • P)) ^ 2 := by
    have hH_val : H (k • P) = max u.num.natAbs u.den := by rw [hkp]; rfl
    rw [hH_val]
    have h1 : u.num.natAbs ≤ max u.num.natAbs u.den := le_max_left _ _
    have h2 : d ≤ max u.num.natAbs u.den := by
      calc d ≤ d ^ 2 := Nat.le_self_pow (by norm_num) d
        _ = u.den := hud.symm
        _ ≤ max u.num.natAbs u.den := le_max_right _ _
    dsimp [Z]
    calc 6 * u.num.natAbs * d ≤ 6 * max u.num.natAbs u.den * max u.num.natAbs u.den := by gcongr
      _ = 6 * (max u.num.natAbs u.den) ^ 2 := by ring
  have hu_recov : u = 108 * (Z : ℚ) / ((X : ℚ) + Y) := by
    have hXq : (X : ℚ) = 324 * (d : ℚ) ^ 3 + v.num := by exact_mod_cast hX_cast
    have hYq : (Y : ℚ) = 324 * (d : ℚ) ^ 3 - v.num := by exact_mod_cast hY_cast
    have hZq : (Z : ℚ) = 6 * u.num * d := by
      have : (Z : ℤ) = 6 * u.num * (d : ℤ) := by
        dsimp [Z]; push_cast; rw [abs_of_nonneg ha_pos.le]
      exact_mod_cast this
    have hud_q : (u.den : ℚ) = (d : ℚ) ^ 2 := by exact_mod_cast hud
    have hd_q : (d : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne'
    conv_lhs => rw [← u.num_div_den]
    rw [hud_q, hXq, hYq, hZq]
    field_simp [hd_q]
    ring
  have hkp' : ∃ v h, k • P = Point.some (108 * (Z : ℚ) / ((X : ℚ) + Y)) v h := by
    rw [← hu_recov]
    exact ⟨v, hq, hkp⟩
  exact ⟨X, Y, Z, hX_pos, hY_pos, hZ_ge, hcube, hZ_le, hkp'⟩

def cubesSet : Set ℕ := {n | ∃ k, k ^ 3 = n}

private lemma log_bound_arith (K L : ℝ) (hK : 2 ≤ K) (hL0 : 0 ≤ L)
    (hL : L ≤ 8 + 3 * ((5 * K) * (5 + 5000 * K ^ 2))) :
    L ^ ((1 : ℝ) / 4) ≤ 100000 * K := by
  have h1 : L ≤ 100000 * K ^ 3 := by nlinarith [sq_nonneg K]
  have hK34 : K ^ 3 ≤ K ^ 4 := by nlinarith [sq_nonneg K]
  have hpow4 : L ≤ (100000 * K) ^ (4 : ℕ) := by
    calc L ≤ 100000 * K ^ 3 := h1
      _ ≤ 100000 * K ^ 4 := by gcongr
      _ ≤ (100000 : ℝ) ^ 4 * K ^ 4 := by gcongr; norm_num
      _ = (100000 * K) ^ (4 : ℕ) := by ring
  have hrp := Real.rpow_le_rpow hL0 hpow4 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
  have h4id : ((100000 * K) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = 100000 * K := by
    rw [← Real.rpow_natCast (100000 * K) 4, ← Real.rpow_mul (by linarith)]
    norm_num
  linarith [hrp, h4id]

open scoped Classical in
lemma mahler_core :
    ∃ C > (0 : ℝ),
      ∃ᶠ (n : ℕ) in Filter.atTop,
        C * (Real.log n) ^ ((1 : ℝ) / 4) ≤
          (((Finset.HasAntidiagonal.antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ cubesSet ∧ p.2 ∈ cubesSet)).card : ℝ) := by
  refine ⟨(1 : ℝ) / 100000, by norm_num, Filter.frequently_atTop.mpr ?_⟩
  intro M
  let K := max (M + 2) 2
  have hK2 : 2 ≤ K := le_max_right _ _
  have hKM : M + 2 ≤ K := le_max_left _ _
  let S := (Finset.Icc 1 (5 * K)).filter (fun k => isGood (k • P))
  have hS_ge : K ≤ S.card := good_count_ge K
  have hS_le : S.card ≤ 5 * K := by
    calc S.card ≤ (Finset.Icc 1 (5 * K)).card := Finset.card_filter_le _ _
      _ = 5 * K := by simp
  let Xof : ℕ → ℕ := fun k =>
    if h : isGood (k • P) ∧ 1 ≤ k then Classical.choose (good_cube_triple h.2 h.1) else 1
  let Yof : ℕ → ℕ := fun k =>
    if h : isGood (k • P) ∧ 1 ≤ k then Classical.choose (Classical.choose_spec (good_cube_triple h.2 h.1)) else 1
  let Zof : ℕ → ℕ := fun k =>
    if h : isGood (k • P) ∧ 1 ≤ k then
      Classical.choose (Classical.choose_spec (Classical.choose_spec (good_cube_triple h.2 h.1)))
    else 6
  have hspec : ∀ k ∈ S,
      0 < Xof k ∧ 0 < Yof k ∧ 6 ≤ Zof k ∧ (Xof k) ^ 3 + (Yof k) ^ 3 = 9 * (Zof k) ^ 3 ∧
        Zof k ≤ 6 * (H (k • P)) ^ 2 ∧
        ∃ v h, k • P = Point.some (108 * (Zof k : ℚ) / ((Xof k : ℚ) + Yof k)) v h := by
    intro k hk
    have hk_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
    have hgood := (Finset.mem_filter.mp hk).2
    have hcond : isGood (k • P) ∧ 1 ≤ k := ⟨hgood, hk_icc.1⟩
    dsimp [Xof, Yof, Zof]
    rw [dif_pos hcond, dif_pos hcond, dif_pos hcond]
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (good_cube_triple hcond.2 hcond.1)))
  let D : ℕ := ∏ k ∈ S, Zof k
  let N : ℕ := 9 * D ^ 3
  have hZ_dvd : ∀ k ∈ S, Zof k ∣ D := fun k hk => Finset.dvd_prod_of_mem Zof hk
  have hD_ge : 6 ^ S.card ≤ D := by
    calc 6 ^ S.card = ∏ _k ∈ S, (6 : ℕ) := by simp
      _ ≤ ∏ k ∈ S, Zof k := Finset.prod_le_prod' (fun k hk => (hspec k hk).2.2.1)
  have h6K_gt : K ≤ 6 ^ K := by
    have hpow : ∀ m : ℕ, m ≤ 6 ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have h1 : 1 ≤ 6 ^ m := Nat.one_le_pow m 6 (by norm_num)
        calc m + 1 ≤ 6 ^ m + 1 := Nat.add_le_add_right ih 1
          _ ≤ 6 ^ m + 5 * 6 ^ m := Nat.add_le_add_left (by nlinarith) _
          _ = 6 ^ (m + 1) := by ring
    exact hpow K
  have hD_pos : 0 < D := lt_of_lt_of_le (Nat.pos_of_ne_zero (pow_ne_zero S.card (by norm_num))) hD_ge
  have hN_ge_M : M ≤ N := by
    have h1 : K ≤ D := le_trans h6K_gt (le_trans (Nat.pow_le_pow_right (by norm_num) hS_ge) hD_ge)
    have h2 : D ≤ D ^ 3 := Nat.le_self_pow (by norm_num) D
    have h3 : D ^ 3 ≤ N := by dsimp [N]; omega
    omega
  let phi : ℕ → ℕ × ℕ := fun k => ((Xof k * (D / Zof k)) ^ 3, (Yof k * (D / Zof k)) ^ 3)
  let T := (Finset.HasAntidiagonal.antidiagonal N).filter (fun p : ℕ × ℕ => p.1 ∈ cubesSet ∧ p.2 ∈ cubesSet)
  have hphi_mem : ∀ k ∈ S, phi k ∈ T := by
    intro k hk
    have hsk := hspec k hk
    have hdvd := hZ_dvd k hk
    have hsum : (Xof k * (D / Zof k)) ^ 3 + (Yof k * (D / Zof k)) ^ 3 = N := by
      calc (Xof k * (D / Zof k)) ^ 3 + (Yof k * (D / Zof k)) ^ 3
          = ((Xof k) ^ 3 + (Yof k) ^ 3) * (D / Zof k) ^ 3 := by ring
        _ = 9 * (Zof k) ^ 3 * (D / Zof k) ^ 3 := by rw [hsk.2.2.2.1]
        _ = 9 * (Zof k * (D / Zof k)) ^ 3 := by ring
        _ = 9 * D ^ 3 := by rw [Nat.mul_div_cancel' hdvd]
    exact Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr hsum,
      ⟨Xof k * (D / Zof k), rfl⟩, ⟨Yof k * (D / Zof k), rfl⟩⟩
  have hphi_inj : ∀ a ∈ S, ∀ b ∈ S, phi a = phi b → a = b := by
    intro a ha b hb heq
    have hsa := hspec a ha
    have hsb := hspec b hb
    have hfst : (Xof a * (D / Zof a)) ^ 3 = (Xof b * (D / Zof b)) ^ 3 := congr_arg Prod.fst heq
    have hsnd : (Yof a * (D / Zof a)) ^ 3 = (Yof b * (D / Zof b)) ^ 3 := congr_arg Prod.snd heq
    have hX : Xof a * (D / Zof a) = Xof b * (D / Zof b) := Nat.pow_left_injective (by norm_num) hfst
    have hY : Yof a * (D / Zof a) = Yof b * (D / Zof b) := Nat.pow_left_injective (by norm_num) hsnd
    have hXY : (Xof a + Yof a) * (D / Zof a) = (Xof b + Yof b) * (D / Zof b) := by linarith
    have hdvd_a := hZ_dvd a ha
    have hdvd_b := hZ_dvd b hb
    have hZ_eq : (Xof a + Yof a) * Zof b = (Xof b + Yof b) * Zof a := by
      have hmul : (Xof a + Yof a) * Zof b * D = (Xof b + Yof b) * Zof a * D := by
        calc (Xof a + Yof a) * Zof b * D
            = (Xof a + Yof a) * (Zof a * (D / Zof a)) * Zof b := by
                rw [Nat.mul_div_cancel' hdvd_a]; ring
          _ = ((Xof a + Yof a) * (D / Zof a)) * Zof a * Zof b := by ring
          _ = ((Xof b + Yof b) * (D / Zof b)) * Zof a * Zof b := by rw [hXY]
          _ = (Xof b + Yof b) * (Zof b * (D / Zof b)) * Zof a := by ring
          _ = (Xof b + Yof b) * Zof a * D := by rw [Nat.mul_div_cancel' hdvd_b]; ring
      exact Nat.mul_right_cancel hD_pos hmul
    have hu_eq : 108 * (Zof a : ℚ) / ((Xof a : ℚ) + Yof a) =
        108 * (Zof b : ℚ) / ((Xof b : ℚ) + Yof b) := by
      have hXa : (0 : ℚ) < (Xof a : ℚ) + Yof a := by exact_mod_cast Nat.add_pos_left hsa.1 (Yof a)
      have hXb : (0 : ℚ) < (Xof b : ℚ) + Yof b := by exact_mod_cast Nat.add_pos_left hsb.1 (Yof b)
      rw [div_eq_div_iff hXa.ne' hXb.ne']
      have hzq : ((Xof a : ℚ) + Yof a) * Zof b = ((Xof b : ℚ) + Yof b) * Zof a := by
        exact_mod_cast hZ_eq
      linarith
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    rcases hsa.2.2.2.2.2 with ⟨va, hna, hpa⟩
    rcases hsb.2.2.2.2.2 with ⟨vb, hnb, hpb⟩
    exact xCoord_injective ha1 hb1 hpa hpb hu_eq
  have hcard : K ≤ T.card := le_trans hS_ge (Finset.card_le_card_of_injOn phi hphi_mem hphi_inj)
  have hlogN_le : Real.log (N : ℝ) ≤ 8 + 3 * ((5 * (K : ℝ)) * (5 + 5000 * (K : ℝ) ^ 2)) := by
    have hD_posR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD_pos
    have hN_cast : (N : ℝ) = 9 * (D : ℝ) ^ 3 := by dsimp [N]; push_cast; ring
    have hZ_posR : ∀ k ∈ S, (0 : ℝ) < (Zof k : ℝ) := fun k hk => by
      have := (hspec k hk).2.2.1; exact_mod_cast (by omega : 0 < Zof k)
    have hD_cast : (D : ℝ) = ∏ k ∈ S, (Zof k : ℝ) := by dsimp [D]; push_cast; rfl
    have hlogD : Real.log (D : ℝ) = ∑ k ∈ S, Real.log (Zof k : ℝ) := by
      rw [hD_cast]
      exact Real.log_prod (fun k hk => (hZ_posR k hk).ne')
    have hlog_N : Real.log (N : ℝ) = Real.log 9 + 3 * ∑ k ∈ S, Real.log (Zof k : ℝ) := by
      rw [hN_cast, Real.log_mul (by norm_num) (pow_ne_zero 3 hD_posR.ne'), Real.log_pow, hlogD]
      push_cast; ring
    have hterm_le : ∀ k ∈ S, Real.log (Zof k : ℝ) ≤ 5 + 5000 * (K : ℝ) ^ 2 := by
      intro k hk
      have hZ := (hspec k hk).2.2.2.2.1
      have hZR : (Zof k : ℝ) ≤ 6 * (H (k • P) : ℝ) ^ 2 := by exact_mod_cast hZ
      have hH_pos : (0 : ℝ) < (H (k • P) : ℝ) := by exact_mod_cast H_pos _
      have hlogZ : Real.log (Zof k : ℝ) ≤ Real.log 6 + 2 * h (k • P) := by
        have h1 := Real.log_le_log (hZ_posR k hk) hZR
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hH_pos.ne'), Real.log_pow] at h1
        dsimp [h]; push_cast at h1; linarith
      have hk_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
      have hk_nsmul := h_nsmul_le k hk_icc.1
      have hk_le5K : (k : ℝ) ≤ 5 * (K : ℝ) := by exact_mod_cast hk_icc.2
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hk_sq : (k : ℝ) ^ 2 ≤ 25 * (K : ℝ) ^ 2 := by
        calc (k : ℝ) ^ 2 ≤ (5 * (K : ℝ)) ^ 2 :=
              by simpa [pow_two] using mul_self_le_mul_self hk_nonneg hk_le5K
          _ = 25 * (K : ℝ) ^ 2 := by ring
      have hlog6 : Real.log 6 ≤ 5 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
        linarith
      linarith
    have hsum_le : ∑ k ∈ S, Real.log (Zof k : ℝ) ≤ (5 * (K : ℝ)) * (5 + 5000 * (K : ℝ) ^ 2) := by
      calc ∑ k ∈ S, Real.log (Zof k : ℝ)
          ≤ ∑ _k ∈ S, (5 + 5000 * (K : ℝ) ^ 2) := Finset.sum_le_sum hterm_le
        _ = (S.card : ℝ) * (5 + 5000 * (K : ℝ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (5 * (K : ℝ)) * (5 + 5000 * (K : ℝ) ^ 2) := by
            gcongr
            exact_mod_cast hS_le
    have hlog9 : Real.log 9 ≤ 8 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
      linarith
    linarith
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    have hD3 : 1 ≤ D ^ 3 := Nat.one_le_pow 3 D hD_pos
    have hN1 : 1 ≤ N := by dsimp [N]; omega
    exact_mod_cast hN1
  have hN_rpow : (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4) ≤ 100000 * (K : ℝ) :=
    log_bound_arith (K : ℝ) (Real.log (N : ℝ)) (by exact_mod_cast hK2) hlogN_nonneg hlogN_le
  refine ⟨N, hN_ge_M, ?_⟩
  have hcardR : (K : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard
  linarith [hN_rpow, hcardR]

end Erdos829Mahler

theorem OMA.solution : type_of% @Erdos829.variants.mahler := by
  rcases Erdos829Mahler.mahler_core with ⟨C, hC, hfreq⟩
  refine ⟨C, hC, hfreq.mono ?_⟩
  intro n hn
  rw [AdditiveCombinatorics.sumRep_def]
  refine le_trans hn (Nat.cast_le.mpr (Finset.card_le_card (fun p hp => ?_)))
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, by simpa [Erdos829.cubes, Erdos829Mahler.cubesSet] using hp.2⟩
