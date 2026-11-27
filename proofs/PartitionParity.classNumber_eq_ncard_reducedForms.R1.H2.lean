import OMAReductions.R_PartitionParity_classNumber_eq_ncard_reducedForms_R1

/-!
Gauss reduction for primitive positive-definite binary quadratic forms.
-/

-- Step PartitionParity.classNumber_eq_ncard_reducedForms.R1.H2: hypothesis H2 of reduction PartitionParity.classNumber_eq_ncard_reducedForms.R1
-- Credit: @ItsNotTheGabs

namespace OMA_GaussReduction_H2

abbrev Form (D : ℕ) :=
  {f : ℤ × ℤ × ℤ // 0 < f.1 ∧ f.2.1 ^ 2 - 4 * f.1 * f.2.2 = -(D : ℤ) ∧
    Int.gcd (Int.gcd f.1 f.2.1) f.2.2 = 1}

abbrev Reduced (D : ℕ) :=
  {f : ℤ × ℤ × ℤ // PartitionParity.IsReducedForm D f.1 f.2.1 f.2.2}

def evaluate {D : ℕ} (f : Form D) (x y : ℤ) : ℤ :=
  f.val.1 * x ^ 2 + f.val.2.1 * x * y + f.val.2.2 * y ^ 2

def proper {D : ℕ} (f g : Form D) : Prop :=
  ∃ u v w z : ℤ, u * z - v * w = 1 ∧
    ∀ x y : ℤ, evaluate f x y = evaluate g (u * x + v * y) (w * x + z * y)

private lemma gcd_triple_eq_one_of_dvd {a b c a' b' c' : ℤ}
    (hg : Int.gcd (Int.gcd a b) c = 1)
    (h : ∀ d : ℤ, d ∣ a' → d ∣ b' → d ∣ c' → d ∣ a ∧ d ∣ b ∧ d ∣ c) :
    Int.gcd (Int.gcd a' b') c' = 1 := by
  set d : ℕ := Int.gcd (Int.gcd a' b') c'
  have hd_ab' : (d : ℤ) ∣ (Int.gcd a' b' : ℤ) := Int.gcd_dvd_left (Int.gcd a' b' : ℤ) c'
  have hd_c' : (d : ℤ) ∣ c' := Int.gcd_dvd_right (Int.gcd a' b' : ℤ) c'
  have hd_a' : (d : ℤ) ∣ a' := dvd_trans hd_ab' (Int.gcd_dvd_left a' b')
  have hd_b' : (d : ℤ) ∣ b' := dvd_trans hd_ab' (Int.gcd_dvd_right a' b')
  obtain ⟨hd_a, hd_b, hd_c⟩ := h (d : ℤ) hd_a' hd_b' hd_c'
  have hd_ab : (d : ℤ) ∣ (Int.gcd a b : ℤ) := Int.ofNat_dvd.mpr (Int.dvd_gcd hd_a hd_b)
  have hd_abc : d ∣ Int.gcd (Int.gcd a b) c := Int.dvd_gcd hd_ab hd_c
  rw [hg] at hd_abc
  exact Nat.dvd_one.mp hd_abc

private lemma form_c_pos {D : ℕ} (hD : 0 < D) (f : Form D) : 0 < f.val.2.2 := by
  have ha : 0 < f.val.1 := f.prop.1
  have hdisc : f.val.2.1 ^ 2 - 4 * f.val.1 * f.val.2.2 = -(D : ℤ) := f.prop.2.1
  have hD' : (0 : ℤ) < (D : ℤ) := Nat.cast_pos.mpr hD
  nlinarith only [ha, hdisc, hD', sq_nonneg f.val.2.1]

private lemma reduced_a_pos {D : ℕ} (hD : 0 < D) {a b c : ℤ}
    (hr : PartitionParity.IsReducedForm D a b c) : 0 < a := by
  obtain ⟨hdisc, hba, _, _, _⟩ := hr
  have ha0 : 0 ≤ a := le_trans (abs_nonneg b) hba
  have hD' : (0 : ℤ) < (D : ℤ) := Nat.cast_pos.mpr hD
  rcases ha0.eq_or_lt with rfl | hpos
  · have hb0 : b = 0 := abs_nonpos_iff.mp hba
    rw [hb0] at hdisc
    linarith
  · exact hpos

private lemma reduced_b_bounds {D : ℕ} (hD : 0 < D) {a b c : ℤ}
    (hr : PartitionParity.IsReducedForm D a b c) : -a < b ∧ b ≤ a := by
  have ha : 0 < a := reduced_a_pos hD hr
  obtain ⟨_, hba, _, _, htie⟩ := hr
  have hle := abs_le.mp hba
  refine ⟨?_, hle.2⟩
  rcases hle.1.eq_or_lt with hEq | hLt
  · have habs : |b| = a := by
      rw [abs_eq ha.le]
      right; linarith
    have hb0 : 0 ≤ b := htie (Or.inl habs)
    linarith
  · exact hLt

private def ofReduced {D : ℕ} (hD : 0 < D) (r : Reduced D) : Form D :=
  ⟨r.val, reduced_a_pos hD r.prop, r.prop.1, r.prop.2.2.2.1⟩

private def shiftForm {D : ℕ} (f : Form D) (k : ℤ) : Form D :=
  ⟨(f.val.1, f.val.2.1 + 2 * f.val.1 * k,
      f.val.2.2 + f.val.2.1 * k + f.val.1 * k ^ 2), by
    refine ⟨f.prop.1, ?_, ?_⟩
    · have hdisc := f.prop.2.1
      linarith [show (f.val.2.1 + 2 * f.val.1 * k) ^ 2 -
        4 * f.val.1 * (f.val.2.2 + f.val.2.1 * k + f.val.1 * k ^ 2) =
        f.val.2.1 ^ 2 - 4 * f.val.1 * f.val.2.2 by ring]
    · apply gcd_triple_eq_one_of_dvd f.prop.2.2
      intro d ha' hb' hc'
      have hb : d ∣ f.val.2.1 := by
        have : f.val.2.1 = (f.val.2.1 + 2 * f.val.1 * k) - 2 * f.val.1 * k := by ring
        rw [this]
        exact dvd_sub hb' (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ha' 2) k)
      have hc : d ∣ f.val.2.2 := by
        have : f.val.2.2 = (f.val.2.2 + f.val.2.1 * k + f.val.1 * k ^ 2) -
            f.val.2.1 * k - f.val.1 * k ^ 2 := by ring
        rw [this]
        exact dvd_sub (dvd_sub hc' (dvd_mul_of_dvd_left hb k))
          (dvd_mul_of_dvd_left ha' (k ^ 2))
      exact ⟨ha', hb, hc⟩⟩

private def swapForm {D : ℕ} (hD : 0 < D) (f : Form D) : Form D :=
  ⟨(f.val.2.2, -f.val.2.1, f.val.1), by
    refine ⟨form_c_pos hD f, ?_, ?_⟩
    · have hdisc := f.prop.2.1
      linarith [show (-f.val.2.1) ^ 2 - 4 * f.val.2.2 * f.val.1 =
        f.val.2.1 ^ 2 - 4 * f.val.1 * f.val.2.2 by ring]
    · apply gcd_triple_eq_one_of_dvd f.prop.2.2
      intro d hc' hnb' ha'
      exact ⟨ha', dvd_neg.mp hnb', hc'⟩⟩

private lemma proper_refl {D : ℕ} (f : Form D) : proper f f :=
  ⟨1, 0, 0, 1, by ring, fun x y => by simp [evaluate]⟩

private lemma proper_symm {D : ℕ} {f g : Form D} (h : proper f g) : proper g f := by
  obtain ⟨u, v, w, z, hdet, hev⟩ := h
  refine ⟨z, -v, -w, u, by linarith, fun x y => ?_⟩
  have h1 := hev (z * x + -v * y) (-w * x + u * y)
  have hx : u * (z * x + -v * y) + v * (-w * x + u * y) = x := by
    calc u * (z * x + -v * y) + v * (-w * x + u * y)
        = (u * z - v * w) * x := by ring
      _ = 1 * x := by rw [hdet]
      _ = x := one_mul x
  have hy : w * (z * x + -v * y) + z * (-w * x + u * y) = y := by
    calc w * (z * x + -v * y) + z * (-w * x + u * y)
        = (u * z - v * w) * y := by ring
      _ = 1 * y := by rw [hdet]
      _ = y := one_mul y
  rw [hx, hy] at h1
  exact h1.symm

private lemma proper_trans {D : ℕ} {f g h : Form D}
    (h1 : proper f g) (h2 : proper g h) : proper f h := by
  obtain ⟨u1, v1, w1, z1, hd1, he1⟩ := h1
  obtain ⟨u2, v2, w2, z2, hd2, he2⟩ := h2
  refine ⟨u2 * u1 + v2 * w1, u2 * v1 + v2 * z1, w2 * u1 + z2 * w1, w2 * v1 + z2 * z1, ?_, ?_⟩
  · calc (u2 * u1 + v2 * w1) * (w2 * v1 + z2 * z1) - (u2 * v1 + v2 * z1) * (w2 * u1 + z2 * w1)
        = (u2 * z2 - v2 * w2) * (u1 * z1 - v1 * w1) := by ring
      _ = 1 * 1 := by rw [hd1, hd2]
      _ = 1 := by ring
  · intro x y
    rw [he1 x y, he2 (u1 * x + v1 * y) (w1 * x + z1 * y)]
    congr 1 <;> ring

private lemma proper_shiftForm {D : ℕ} (f : Form D) (k : ℤ) :
    proper f (shiftForm f k) := by
  refine ⟨1, -k, 0, 1, by ring, fun x y => ?_⟩
  simp only [evaluate, shiftForm]
  ring

private lemma proper_swapForm {D : ℕ} (hD : 0 < D) (f : Form D) :
    proper f (swapForm hD f) := by
  refine ⟨0, 1, -1, 0, by ring, fun x y => ?_⟩
  simp only [evaluate, swapForm]
  ring

private lemma exists_shift_range (a b : ℤ) (ha : 0 < a) :
    ∃ k : ℤ, -a < b + 2 * a * k ∧ b + 2 * a * k ≤ a := by
  have h2a : 0 < 2 * a := by omega
  let q := (b + a - 1) / (2 * a)
  let r := (b + a - 1) % (2 * a)
  have hqr : r + 2 * a * q = b + a - 1 := Int.emod_add_mul_ediv (b + a - 1) (2 * a)
  have hr0 : 0 ≤ r := Int.emod_nonneg (b + a - 1) (by omega)
  have hrlt : r < 2 * a := Int.emod_lt_of_pos (b + a - 1) h2a
  have hval : b + 2 * a * (-q) = r - a + 1 := by linarith
  refine ⟨-q, ?_, ?_⟩ <;> linarith

private lemma exists_reduced {D : ℕ} (hD : 0 < D) (f : Form D) :
    ∃ r : Reduced D, proper f (ofReduced hD r) := by
  suffices h : ∀ n : ℕ, ∀ f : Form D, f.val.1.toNat = n →
      ∃ r : Reduced D, proper f (ofReduced hD r) from h f.val.1.toNat f rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hn
    obtain ⟨k, hblt, hble⟩ := exists_shift_range f.val.1 f.val.2.1 f.prop.1
    let f1 := shiftForm f k
    have hp1 : proper f f1 := proper_shiftForm f k
    have ha1 : f1.val.1 = f.val.1 := rfl
    have hb1_gt : -f1.val.1 < f1.val.2.1 := hblt
    have hb1_le : f1.val.2.1 ≤ f1.val.1 := hble
    have habs1 : |f1.val.2.1| ≤ f1.val.1 := abs_le.mpr ⟨by omega, hb1_le⟩
    by_cases hca : f1.val.2.2 < f1.val.1
    · let f2 := swapForm hD f1
      have hp2 : proper f1 f2 := proper_swapForm hD f1
      have hlt : f2.val.1.toNat < n := by
        have hcpos : 0 < f1.val.2.2 := form_c_pos hD f1
        have hapos : 0 < f.val.1 := f.prop.1
        change f1.val.2.2.toNat < n
        omega
      obtain ⟨r, hpr⟩ := ih f2.val.1.toNat hlt f2 rfl
      exact ⟨r, proper_trans (proper_trans hp1 hp2) hpr⟩
    · have hac : f1.val.1 ≤ f1.val.2.2 := by omega
      by_cases hneg : f1.val.1 = f1.val.2.2 ∧ f1.val.2.1 < 0
      · let f2 := swapForm hD f1
        have hp2 : proper f1 f2 := proper_swapForm hD f1
        have hr2 : PartitionParity.IsReducedForm D f2.val.1 f2.val.2.1 f2.val.2.2 := by
          refine ⟨f2.prop.2.1, ?_, ?_, f2.prop.2.2, ?_⟩
          · change |-f1.val.2.1| ≤ f1.val.2.2
            rw [abs_neg, ← hneg.1]
            exact habs1
          · change f1.val.2.2 ≤ f1.val.1
            omega
          · intro _
            change 0 ≤ -f1.val.2.1
            omega
        refine ⟨⟨f2.val, hr2⟩, ?_⟩
        exact proper_trans hp1 hp2
      · have hr1 : PartitionParity.IsReducedForm D f1.val.1 f1.val.2.1 f1.val.2.2 := by
          refine ⟨f1.prop.2.1, habs1, hac, f1.prop.2.2, ?_⟩
          intro hor
          rcases hor with habs_eq | hac_eq
          · have : f1.val.2.1 = f1.val.1 ∨ f1.val.2.1 = -f1.val.1 :=
              (abs_eq f1.prop.1.le).mp habs_eq
            omega
          · by_contra hlt0
            exact hneg ⟨hac_eq, by omega⟩
        exact ⟨⟨f1.val, hr1⟩, hp1⟩

private lemma coeff_relations {D : ℕ} {f g : Form D} {u v w z : ℤ}
    (hev : ∀ x y : ℤ, evaluate f x y = evaluate g (u * x + v * y) (w * x + z * y)) :
    f.val.1 = evaluate g u w ∧
    f.val.2.2 = evaluate g v z ∧
    f.val.2.1 = 2 * g.val.1 * u * v + g.val.2.1 * (u * z + v * w) + 2 * g.val.2.2 * w * z := by
  have h10 := hev 1 0
  have h01 := hev 0 1
  have h11 := hev 1 1
  simp only [evaluate] at h10 h01 h11 ⊢
  refine ⟨by linarith, by linarith, by linarith⟩

private lemma reduced_eval_identity (a b c x y : ℤ) :
    a * x ^ 2 + b * x * y + c * y ^ 2 - (a - |b| + c) =
      (a - |b|) * (x ^ 2 - 1) + (c - |b|) * (y ^ 2 - 1) +
      |b| * ((|x| - |y|) ^ 2 + |x| * |y| - 1) + (b * x * y + |b| * |x| * |y|) := by
  have hx : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hy : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  rw [hx, hy]
  ring

private lemma reduced_eval_ge_of_ne_zero {D : ℕ} {a b c x y : ℤ}
    (hr : PartitionParity.IsReducedForm D a b c) (hx : x ≠ 0) (hy : y ≠ 0) :
    a - |b| + c ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  have hab : |b| ≤ a := hr.2.1
  have hac : a ≤ c := hr.2.2.1
  have hcb : |b| ≤ c := le_trans hab hac
  have hx1 : 1 ≤ |x| := Int.one_le_abs hx
  have hy1 : 1 ≤ |y| := Int.one_le_abs hy
  have hx2 : 1 ≤ x ^ 2 := by nlinarith only [hx1, sq_abs x]
  have hy2 : 1 ≤ y ^ 2 := by nlinarith only [hy1, sq_abs y]
  have hxy : 1 ≤ |x| * |y| := by nlinarith only [hx1, hy1]
  have h4 : 0 ≤ b * x * y + |b| * |x| * |y| := by
    have hneg : -(b * x * y) ≤ |b * x * y| := neg_le_abs (b * x * y)
    have hmul : |b * x * y| = |b| * |x| * |y| := by
      rw [abs_mul, abs_mul]
    linarith
  have hid := reduced_eval_identity a b c x y
  have h1 : 0 ≤ (a - |b|) * (x ^ 2 - 1) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (c - |b|) * (y ^ 2 - 1) := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ |b| * ((|x| - |y|) ^ 2 + |x| * |y| - 1) :=
    mul_nonneg (abs_nonneg b) (by linarith [sq_nonneg (|x| - |y|), hxy])
  linarith

private lemma reduced_eval_ge_a {D : ℕ} (hD : 0 < D) (r : Reduced D) {x y : ℤ}
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    r.val.1 ≤ evaluate (ofReduced hD r) x y := by
  have ha : 0 < r.val.1 := reduced_a_pos hD r.prop
  have hab : |r.val.2.1| ≤ r.val.1 := r.prop.2.1
  have hac : r.val.1 ≤ r.val.2.2 := r.prop.2.2.1
  simp only [evaluate, ofReduced]
  by_cases hx : x = 0
  · subst hx
    have hy : y ≠ 0 := hxy.resolve_left (by simp)
    have hy1 : 1 ≤ |y| := Int.one_le_abs hy
    have hy2 : 1 ≤ y ^ 2 := by nlinarith only [hy1, sq_abs y]
    nlinarith only [ha, hac, hy2]
  · by_cases hy : y = 0
    · subst hy
      have hx1 : 1 ≤ |x| := Int.one_le_abs hx
      have hx2 : 1 ≤ x ^ 2 := by nlinarith only [hx1, sq_abs x]
      nlinarith only [ha, hx2]
    · have hge := reduced_eval_ge_of_ne_zero r.prop hx hy
      linarith

private lemma reduced_eq_of_proper {D : ℕ} (hD : 0 < D) (r1 r2 : Reduced D)
    (hp : proper (ofReduced hD r1) (ofReduced hD r2)) : r1 = r2 := by
  set a1 := r1.val.1
  set b1 := r1.val.2.1
  set c1 := r1.val.2.2
  set a2 := r2.val.1
  set b2 := r2.val.2.1
  set c2 := r2.val.2.2
  have ha1_pos : 0 < a1 := reduced_a_pos hD r1.prop
  have ha2_pos : 0 < a2 := reduced_a_pos hD r2.prop
  have hb1_bnd := reduced_b_bounds hD r1.prop
  have hb2_bnd := reduced_b_bounds hD r2.prop
  obtain ⟨u, v, w, z, hdet, hev⟩ := hp
  obtain ⟨heq_a, heq_c, heq_b⟩ := coeff_relations hev
  have huw_ne : u ≠ 0 ∨ w ≠ 0 := by
    by_contra h
    push Not at h
    rw [h.1, h.2] at hdet
    norm_num at hdet
  have ha2_le_a1 : a2 ≤ a1 := by
    have hle := reduced_eval_ge_a hD r2 huw_ne
    simpa [a1, a2, ofReduced] using hle.trans_eq heq_a.symm
  have ha1_le_a2 : a1 ≤ a2 := by
    obtain ⟨u', v', w', z', hdet', hev'⟩ := proper_symm ⟨u, v, w, z, hdet, hev⟩
    obtain ⟨heq_a', _, _⟩ := coeff_relations hev'
    have huw'_ne : u' ≠ 0 ∨ w' ≠ 0 := by
      by_contra h
      push Not at h
      rw [h.1, h.2] at hdet'
      norm_num at hdet'
    have hle := reduced_eval_ge_a hD r1 huw'_ne
    simpa [a1, a2, ofReduced] using hle.trans_eq heq_a'.symm
  have ha_eq : a1 = a2 := le_antisymm ha1_le_a2 ha2_le_a1
  have hb_eq : b1 = b2 := by
    by_cases hw : w = 0
    · rw [hw] at hdet heq_b
      have huz : u * z = 1 := by linarith
      have hb_rel : b1 = 2 * a2 * (u * v) + b2 := by
        have : b1 = 2 * a2 * u * v + b2 * (u * z + v * 0) + 2 * c2 * 0 * z := heq_b
        rw [huz] at this
        linarith
      have huv0 : u * v = 0 := by
        by_contra hne
        have hcases : 1 ≤ u * v ∨ u * v ≤ -1 := by omega
        rcases hcases with h1 | h1 <;>
          nlinarith only [ha_eq, ha2_pos, hb1_bnd.1, hb1_bnd.2, hb2_bnd.1, hb2_bnd.2, hb_rel, h1]
      rw [huv0] at hb_rel
      linarith
    · by_cases hu : u = 0
      · rw [hu] at hdet heq_a heq_b
        have hvw : v * w = -1 := by linarith
        have hw2 : w ^ 2 = 1 := by
          have hw_cases : w = 1 ∨ w = -1 := by
            have hd : w ∣ 1 := ⟨-v, by linarith⟩
            rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hd) with rfl | rfl <;> simp
          rcases hw_cases with rfl | rfl <;> norm_num
        have hv2 : v ^ 2 = 1 := by
          have hv_cases : v = 1 ∨ v = -1 := by
            have hd : v ∣ 1 := ⟨-w, by linarith⟩
            rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hd) with rfl | rfl <;> simp
          rcases hv_cases with rfl | rfl <;> norm_num
        have hc2_eq : c2 = a2 := by
          have h1 : a1 = a2 * 0 ^ 2 + b2 * 0 * w + c2 * w ^ 2 := heq_a
          rw [hw2] at h1
          linarith
        have hb2_nonneg : 0 ≤ b2 := r2.prop.2.2.2.2 (Or.inr hc2_eq.symm)
        have hb_rel : b1 + b2 = 2 * a2 * (w * z) := by
          have h1 : b1 = 2 * a2 * 0 * v + b2 * (0 * z + v * w) + 2 * c2 * w * z := heq_b
          rw [hvw, hc2_eq] at h1
          linarith
        have hwz_cases : w * z = 0 ∨ w * z = 1 := by
          have hge0 : 0 ≤ w * z := by
            by_contra hlt
            have hle : w * z ≤ -1 := by omega
            nlinarith only [ha_eq, ha2_pos, hb1_bnd.1, hb2_nonneg, hb_rel, hle]
          have hle1 : w * z ≤ 1 := by
            by_contra hgt
            have hge : 2 ≤ w * z := by omega
            nlinarith only [ha_eq, ha2_pos, hb1_bnd.2, hb2_bnd.2, hb_rel, hge]
          omega
        rcases hwz_cases with hwz0 | hwz1
        · have hz0 : z = 0 := (mul_eq_zero.mp hwz0).resolve_left hw
          have hc1_eq : c1 = a1 := by
            have h1 : c1 = a2 * v ^ 2 + b2 * v * z + c2 * z ^ 2 := heq_c
            rw [hz0, hv2] at h1
            linarith
          have hb1_nonneg : 0 ≤ b1 := r1.prop.2.2.2.2 (Or.inr hc1_eq.symm)
          rw [hwz0] at hb_rel
          linarith
        · rw [hwz1] at hb_rel
          linarith
      · have hab2 : |b2| ≤ a2 := r2.prop.2.1
        have hac2 : a2 ≤ c2 := r2.prop.2.2.1
        have hcb2 : |b2| ≤ c2 := le_trans hab2 hac2
        have hu1 : 1 ≤ |u| := Int.one_le_abs hu
        have hw1 : 1 ≤ |w| := Int.one_le_abs hw
        have hu2 : 1 ≤ u ^ 2 := by nlinarith only [hu1, sq_abs u]
        have hw2 : 1 ≤ w ^ 2 := by nlinarith only [hw1, sq_abs w]
        have huw1 : 1 ≤ |u| * |w| := by nlinarith only [hu1, hw1]
        have hT1 : 0 ≤ (a2 - |b2|) * (u ^ 2 - 1) := mul_nonneg (by linarith) (by linarith)
        have hT2 : 0 ≤ (c2 - |b2|) * (w ^ 2 - 1) := mul_nonneg (by linarith) (by linarith)
        have hT3 : 0 ≤ |b2| * ((|u| - |w|) ^ 2 + |u| * |w| - 1) :=
          mul_nonneg (abs_nonneg b2) (by linarith [sq_nonneg (|u| - |w|), huw1])
        have hT4 : 0 ≤ b2 * u * w + |b2| * |u| * |w| := by
          have hneg : -(b2 * u * w) ≤ |b2 * u * w| := neg_le_abs (b2 * u * w)
          have hmul : |b2 * u * w| = |b2| * |u| * |w| := by rw [abs_mul, abs_mul]
          linarith
        have hid := reduced_eval_identity a2 b2 c2 u w
        have heq_a' : a2 = a2 * u ^ 2 + b2 * u * w + c2 * w ^ 2 := by
          simpa [a1, a2, b2, c2, evaluate, ofReduced, ha_eq] using heq_a
        have hc2_eq : c2 = a2 := by linarith
        have habs_b2 : |b2| = a2 := by linarith
        have hb2_nonneg : 0 ≤ b2 := r2.prop.2.2.2.2 (Or.inr hc2_eq.symm)
        have hb2_eq : b2 = a2 := by
          rw [abs_of_nonneg hb2_nonneg] at habs_b2
          exact habs_b2
        have hT3_zero : |b2| * ((|u| - |w|) ^ 2 + |u| * |w| - 1) = 0 := by linarith
        have hT4_zero : b2 * u * w + |b2| * |u| * |w| = 0 := by linarith
        have huw_eq1 : (|u| - |w|) ^ 2 + |u| * |w| - 1 = 0 := by
          rw [habs_b2] at hT3_zero
          exact (mul_eq_zero.mp hT3_zero).resolve_left ha2_pos.ne'
        have huw_abs1 : |u| * |w| = 1 := by linarith [sq_nonneg (|u| - |w|), huw1, huw_eq1]
        have huw_neg1 : u * w = -1 := by
          have h1 : a2 * (u * w + 1) = 0 := by
            calc a2 * (u * w + 1) = a2 * u * w + a2 * (|u| * |w|) := by rw [huw_abs1]; ring
              _ = b2 * u * w + |b2| * |u| * |w| := by rw [habs_b2, hb2_eq]; ring
              _ = 0 := hT4_zero
          have h2 : u * w + 1 = 0 := (mul_eq_zero.mp h1).resolve_left ha2_pos.ne'
          linarith
        have hw_eq_neg_u : w = -u := by
          have hu_abs1 : |u| = 1 := by nlinarith only [hu1, hw1, huw_abs1]
          have : u = 1 ∨ u = -1 := by
            rcases abs_eq (show (0 : ℤ) ≤ 1 by norm_num) |>.mp hu_abs1 with rfl | rfl <;> simp
          rcases this with rfl | rfl <;> linarith
        have huz_uv : u * z + u * v = 1 := by
          rw [hw_eq_neg_u] at hdet
          linarith
        have hb1_rel : b1 = a2 * (2 * (u * v) - 1) := by
          have h1 : b1 = 2 * a2 * u * v + b2 * (u * z + v * w) + 2 * c2 * w * z := heq_b
          rw [hb2_eq, hc2_eq, hw_eq_neg_u] at h1
          have h2 : u * z = 1 - u * v := by linarith
          have h3 : b1 = a2 * (u * v - u * z) := by linarith
          rw [h2] at h3
          linarith
        have huv_eq1 : u * v = 1 := by
          have hgt : 0 < u * v := by
            by_contra hle
            have hle0 : u * v ≤ 0 := by omega
            nlinarith only [hb1_bnd.1, ha_eq, ha2_pos, hb1_rel, hle0]
          have hle : u * v ≤ 1 := by
            by_contra hgt1
            have hge2 : 2 ≤ u * v := by omega
            nlinarith only [hb1_bnd.2, ha_eq, ha2_pos, hb1_rel, hge2]
          omega
        rw [huv_eq1] at hb1_rel
        linarith
  have hc_eq : c1 = c2 := by
    have hd1 : b1 ^ 2 - 4 * a1 * c1 = -(D : ℤ) := r1.prop.1
    have hd2 : b2 ^ 2 - 4 * a2 * c2 = -(D : ℤ) := r2.prop.1
    rw [ha_eq, hb_eq] at hd1
    nlinarith only [ha2_pos, hd1, hd2]
  apply Subtype.ext
  exact Prod.ext ha_eq (Prod.ext hb_eq hc_eq)

end OMA_GaussReduction_H2

theorem OMA.solution : OMA.R_PartitionParity_classNumber_eq_ncard_reducedForms_R1.H2 := by
  intro D hD
  let reduceForm : OMA_GaussReduction_H2.Form D → OMA_GaussReduction_H2.Reduced D :=
    fun f => Classical.choose (OMA_GaussReduction_H2.exists_reduced hD f)
  have hreduce_spec : ∀ f, OMA_GaussReduction_H2.proper f
      (OMA_GaussReduction_H2.ofReduced hD (reduceForm f)) :=
    fun f => Classical.choose_spec (OMA_GaussReduction_H2.exists_reduced hD f)
  have hlift_ok : ∀ f g, OMA_GaussReduction_H2.proper f g → reduceForm f = reduceForm g := by
    intro f g hfg
    exact OMA_GaussReduction_H2.reduced_eq_of_proper hD (reduceForm f) (reduceForm g)
      (OMA_GaussReduction_H2.proper_trans (OMA_GaussReduction_H2.proper_symm (hreduce_spec f))
        (OMA_GaussReduction_H2.proper_trans hfg (hreduce_spec g)))
  refine ⟨{
    toFun := Quot.lift reduceForm hlift_ok
    invFun := fun r => Quot.mk _ (OMA_GaussReduction_H2.ofReduced hD r)
    left_inv := fun q => Quot.induction_on q fun f =>
      Quot.sound (OMA_GaussReduction_H2.proper_symm (hreduce_spec f))
    right_inv := fun r =>
      OMA_GaussReduction_H2.reduced_eq_of_proper hD
        (reduceForm (OMA_GaussReduction_H2.ofReduced hD r)) r
        (OMA_GaussReduction_H2.proper_symm (hreduce_spec (OMA_GaussReduction_H2.ofReduced hD r)))
  }⟩
