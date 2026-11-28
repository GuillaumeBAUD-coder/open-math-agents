import OMAStatements.S_mo_144090
import Mathlib

open Matrix
open OMA.S_mo_144090

namespace UpperBand

abbrev Index := Fin 6
abbrev Mat := Matrix Index Index (ZMod 2)

def Gap (k : ℕ) (A : Mat) : Prop :=
  ∀ i j, j.val < i.val + k → A i j = 0

lemma gap_zero (k : ℕ) : Gap k 0 := by
  intro i j hij
  rfl

lemma gap_add {k : ℕ} {A B : Mat} (ha : Gap k A) (hb : Gap k B) : Gap k (A + B) := by
  intro i j hj
  change A i j + B i j = 0
  rw [ha i j hj, hb i j hj, add_zero]

lemma gap_sub {k : ℕ} {A B : Mat} (ha : Gap k A) (hb : Gap k B) : Gap k (A - B) := by
  intro i j hj
  change A i j - B i j = 0
  rw [ha i j hj, hb i j hj, sub_self]

lemma gap_mono {k l : ℕ} {A : Mat} (h : k ≤ l) (ha : Gap l A) : Gap k A := by
  intro i j hj
  exact ha i j (by omega)

lemma gap_mul {k l : ℕ} {A B : Mat} (ha : Gap k A) (hb : Gap l B) : Gap (k + l) (A * B) := by
  intro i j hj
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro r _
  by_cases h : r.val < i.val + k
  · rw [ha i r h, zero_mul]
  · rw [hb r j (by omega), mul_zero]

lemma gap_pow {A : Mat} (ha : Gap 1 A) (k : ℕ) : Gap k (A ^ k) := by
  induction k with
  | zero =>
    intro i j h
    rw [pow_zero, Matrix.one_apply_ne (by intro e; subst j; omega)]
  | succ k ih => simpa [pow_succ] using gap_mul ih ha

lemma gap_zero_of_large {A : Mat} {k : ℕ} (hk : 6 ≤ k) (ha : Gap k A) : A = 0 := by
  ext i j
  have hj := j.isLt
  exact ha i j (by omega)

def band (A : Mat) : Mat :=
  Matrix.of fun i j => if j.val = i.val + 1 then A i j else 0

lemma band_zero : band (0 : Mat) = 0 := by
  ext i j
  simp [band]

lemma band_add (A B : Mat) : band (A + B) = band A + band B := by
  ext i j
  by_cases h : j.val = i.val + 1 <;> simp [band, h]

lemma band_of_gap_two {A : Mat} (hA : Gap 2 A) : band A = 0 := by
  ext i j
  change (if j.val = i.val + 1 then A i j else 0) = 0
  split
  · exact hA i j (by omega)
  · rfl

lemma band_gap (A : Mat) : Gap 1 (band A) := by
  intro i j hij
  change (if j.val = i.val + 1 then A i j else 0) = 0
  rw [if_neg (by omega)]

lemma band_remainder {A : Mat} (hA : Gap 1 A) : Gap 2 (A - band A) := by
  intro i j hij
  change A i j - (if j.val = i.val + 1 then A i j else 0) = 0
  split_ifs with h
  · exact sub_self _
  · rw [hA i j (by omega), sub_zero]

def first : Mat := Matrix.of fun i j =>
  if j.val = i.val + 1 ∧ i.val < 2 then 1 else 0

def second : Mat := Matrix.of fun i j =>
  if j.val = i.val + 1 then 1 else 0

def modelBand (a b : ZMod 2) : Mat := a • first + b • second

lemma modelBand_add (a b c d : ZMod 2) :
    modelBand a b + modelBand c d = modelBand (a + c) (b + d) := by
  simp only [modelBand, add_smul]
  abel

def eligible (g : Matˣ) : Prop :=
  Gap 1 ((g : Mat) - 1) ∧ ∃ a b, band ((g : Mat) - 1) = modelBand a b

def positive : Submonoid Matˣ where
  carrier := {g | eligible g}
  one_mem' := by
    change Gap 1 ((1 : Mat) - 1) ∧ ∃ a b, band ((1 : Mat) - 1) = modelBand a b
    rw [sub_self, band_zero]
    exact ⟨gap_zero 1, 0, 0, by simp [modelBand]⟩
  mul_mem' := by
    intro g h hg hh
    change eligible g at hg
    change eligible h at hh
    change eligible (g * h)
    let A : Mat := (g : Mat) - 1
    let B : Mat := (h : Mat) - 1
    have hAB : Gap 2 (A * B) := gap_mul hg.1 hh.1
    have he : ((g * h : Matˣ) : Mat) - 1 = A + B + A * B := by
      change (g : Mat) * (h : Mat) - 1 = _
      dsimp [A, B]
      noncomm_ring
    constructor
    · rw [he]
      exact gap_add (gap_add hg.1 hh.1) (gap_mono (by omega) hAB)
    · obtain ⟨a,b,hab⟩ := hg.2
      obtain ⟨c,d,hcd⟩ := hh.2
      refine ⟨a + c, b + d, ?_⟩
      rw [he, band_add, band_of_gap_two hAB, add_zero, band_add]
      change band ((g : Mat) - 1) + band ((h : Mat) - 1) = _
      rw [hab, hcd, modelBand_add]

lemma add_self_zero (A : Mat) : A + A = 0 := by
  ext i j
  change A i j + A i j = 0
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

lemma one_add_sq (A : Mat) : (1 + A) ^ 2 = 1 + A ^ 2 := by
  rw [pow_two, pow_two]
  calc
    _ = (1 : Mat) + (A + A) + A * A := by noncomm_ring
    _ = _ := by rw [add_self_zero, add_zero]

lemma pow_eight (A : Mat) (hA : Gap 1 A) : (1 + A) ^ 8 = 1 := by
  have hA8 : A ^ 8 = 0 := gap_zero_of_large (by omega) (gap_pow hA 8)
  rw [show (8 : ℕ) = (2 * 2) * 2 by decide, pow_mul, pow_mul,
    one_add_sq, one_add_sq, one_add_sq, ← pow_mul, ← pow_mul]
  rw [show (2 * 2 * 2 : ℕ) = 8 by decide, hA8, add_zero]

lemma unit_pow_eight (g : Matˣ) (hg : Gap 1 ((g : Mat) - 1)) : g ^ 8 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have h := pow_eight ((g : Mat) - 1) hg
  rwa [add_sub_cancel] at h

def allowed : Subgroup Matˣ where
  toSubmonoid := positive
  inv_mem' := by
    intro g hg
    change eligible g at hg
    have he : g ^ 7 * g = 1 := by rw [← pow_succ, unit_pow_eight g hg.1]
    have hInv : g⁻¹ = g ^ 7 := by
      calc
        _ = 1 * g⁻¹ := (one_mul _).symm
        _ = _ := by rw [← he, mul_assoc, mul_inv_cancel, mul_one]
    rw [hInv]
    exact positive.pow_mem hg 7

abbrev Gr := allowed

def matVal : Gr →* Mat := (Units.coeHom Mat).comp allowed.subtype

lemma matVal_injective : Function.Injective matVal := by
  intro a b h
  exact Subtype.ext (Units.ext h)

def resid (g : Gr) : Mat := matVal g - 1

lemma resid_gap (g : Gr) : Gap 1 (resid g) := g.property.1

lemma resid_band (g : Gr) : ∃ a b, band (resid g) = modelBand a b := g.property.2

lemma resid_mul (g h : Gr) : resid (g * h) = resid g + resid h + resid g * resid h := by
  simp only [resid, map_mul]
  noncomm_ring

lemma group_nilpotent : Group.IsNilpotent Gr := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply IsPGroup.isNilpotent (p := 2)
  intro g
  refine ⟨3, ?_⟩
  apply Subtype.ext
  exact unit_pow_eight g.val (resid_gap g)

lemma gap_mul_as {a b c : ℕ} {A B : Mat} (h : c ≤ a + b)
    (ha : Gap a A) (hb : Gap b B) : Gap c (A*B) :=
  gap_mono h (gap_mul ha hb)

lemma resid_eq_zero_iff {g : Gr} : resid g = 0 ↔ g = 1 := by
  constructor
  · intro h
    apply matVal_injective
    simpa [resid, sub_eq_zero] using h
  · rintro rfl
    simp [resid]

lemma resid_comm (g h : Gr) (n : ℕ) :
    resid (comm g h (n+1)) =
      matVal ((comm g h n)⁻¹ * h⁻¹) *
        (resid (comm g h n) * resid h - resid h * resid (comm g h n)) := by
  let c := comm g h n
  let w := c⁻¹ * h⁻¹
  have hw : matVal w * (matVal h * matVal c) = 1 := by
    rw [← map_mul, ← map_mul]
    simp [w, mul_assoc]
  calc
    _ = matVal w * (matVal c * matVal h) - 1 := by simp [resid, OMA.S_mo_144090.comm, w, c, mul_assoc, map_mul]
    _ = matVal w * (matVal c * matVal h - matVal h * matVal c) := by rw [mul_sub, hw]
    _ = _ := by
      change matVal w * _ = matVal w * _
      congr 1
      simp only [resid]
      noncomm_ring

lemma resid_comm_gap (g h : Gr) (n : ℕ) : Gap (n+1) (resid (comm g h n)) := by
  induction n with
  | zero => exact resid_gap g
  | succ n ih =>
    rw [resid_comm]
    let w := (comm g h n)⁻¹ * h⁻¹
    let Q := resid (comm g h n) * resid h - resid h * resid (comm g h n)
    have hQ : Gap (n+1+1) Q :=
      gap_sub (gap_mul ih (resid_gap h)) (gap_mul_as (by omega) (resid_gap h) ih)
    change Gap (n+1+1) (matVal w * Q)
    rw [show matVal w * Q = Q + resid w * Q by simp only [resid]; noncomm_ring]
    exact gap_add hQ (gap_mul_as (by omega) (resid_gap w) hQ)

def lieIter (X Y : Mat) : ℕ → Mat
  | 0 => X
  | n+1 => lieIter X Y n * Y - Y * lieIter X Y n

lemma lie_gap {X Y : Mat} (hX : Gap 1 X) (hY : Gap 1 Y) (n : ℕ) :
    Gap (n+1) (lieIter X Y n) := by
  induction n with
  | zero => exact hX
  | succ n ih =>
    exact gap_sub (gap_mul ih hY) (gap_mul_as (by omega) hY ih)

lemma approximation (g h : Gr) (n : ℕ) :
    Gap (n+2) (resid (comm g h n) - lieIter (band (resid g)) (band (resid h)) n) := by
  let Y := resid h
  let V := band Y
  let X := band (resid g)
  change Gap (n+2) (resid (comm g h n) - lieIter X V n)
  induction n with
  | zero => exact band_remainder (resid_gap g)
  | succ n ih =>
    let W := resid (comm g h n)
    let L := lieIter X V n
    let w := (comm g h n)⁻¹ * h⁻¹
    have hL : Gap (n+1) L := lie_gap (band_gap _) (band_gap _) n
    have hW : Gap (n+1) W := resid_comm_gap g h n
    have hV : Gap 1 V := band_gap _
    have hY : Gap 1 Y := resid_gap h
    have hyv : Gap 2 (Y-V) := band_remainder hY
    have hQ : Gap (n+2) (W*Y-Y*W) :=
      gap_sub (gap_mul_as (by omega) hW hY) (gap_mul_as (by omega) hY hW)
    rw [resid_comm]
    change Gap (n+1+2) (matVal w * (W*Y-Y*W) - (L*V-V*L))
    rw [show matVal w * (W*Y-Y*W) - (L*V-V*L) =
      resid w * (W*Y-Y*W) + ((W-L)*Y + L*(Y-V)) - ((Y-V)*W + V*(W-L)) by
        simp only [resid]
        noncomm_ring]
    exact gap_sub (gap_add (gap_mul_as (by omega) (resid_gap w) hQ)
      (gap_add (gap_mul_as (by omega) ih hY) (gap_mul_as (by omega) hL hyv)))
      (gap_add (gap_mul_as (by omega) hyv hW) (gap_mul_as (by omega) hV ih))

lemma fourth_exact (g h : Gr) :
    resid (comm g h 4) = lieIter (band (resid g)) (band (resid h)) 4 :=
  sub_eq_zero.mp (gap_zero_of_large (by omega) (approximation g h 4))

lemma fifth_zero (g h : Gr) : comm g h 5 = 1 :=
  resid_eq_zero_iff.mp (gap_zero_of_large (by omega) (resid_comm_gap g h 5))

lemma comm_square {R : Type} [Ring R] (htwo : ∀ r : R, r + r = 0) (X Y : R) :
    (X*Y-Y*X)*Y-Y*(X*Y-Y*X) = X*(Y*Y)-(Y*Y)*X := by
  calc
    _ = X*(Y*Y)+(Y*Y)*X - (Y*X*Y + Y*X*Y) := by noncomm_ring
    _ = _ := by
      have h : -((Y*Y)*X) = (Y*Y)*X := neg_eq_iff_add_eq_zero.mpr (htwo _)
      rw [htwo, sub_zero, sub_eq_add_neg, h]

lemma lie_twice (X Y : Mat) :
    (X*Y-Y*X)*Y-Y*(X*Y-Y*X) = X*(Y*Y)-(Y*Y)*X :=
  comm_square add_self_zero X Y

lemma lie_four (X Y : Mat) :
    lieIter X Y 4 = X*((Y*Y)*(Y*Y))-((Y*Y)*(Y*Y))*X := by
  change (((X*Y-Y*X)*Y-Y*(X*Y-Y*X))*Y-Y*((X*Y-Y*X)*Y-Y*(X*Y-Y*X)))*Y -
    Y*((((X*Y-Y*X)*Y-Y*(X*Y-Y*X))*Y-Y*((X*Y-Y*X)*Y-Y*(X*Y-Y*X)))) = _
  rw [lie_twice (X := X) (Y := Y), lie_twice, lie_twice]

lemma fourthModel (a b : ZMod 2) (ha : a ≠ 0) :
    (modelBand a b * modelBand a b) * (modelBand a b * modelBand a b) = 0 := by
  revert a b
  decide +kernel

def label (g : Gr) : ZMod 2 := resid g 0 1 - resid g 2 3

lemma label_one : label 1 = 0 := by simp [label, resid]

lemma label_mul (g h : Gr) : label (g*h) = label g + label h := by
  unfold label
  rw [resid_mul]
  have hg := gap_mul (resid_gap g) (resid_gap h)
  simp only [Matrix.add_apply, hg 0 1 (by decide), hg 2 3 (by decide), add_zero]
  abel

def small : Subgroup Gr where
  carrier := {g | label g = 0}
  one_mem' := label_one
  mul_mem' := by
    intro a b ha hb
    change label a = 0 at ha
    change label b = 0 at hb
    change label (a*b) = 0
    rw [label_mul, ha, hb, add_zero]
  inv_mem' := by
    intro a ha
    change label a = 0 at ha
    change label a⁻¹ = 0
    have he := label_mul a⁻¹ a
    rw [inv_mul_cancel, label_one, ha, add_zero] at he
    exact he.symm

lemma label_of_band {g : Gr} {a b : ZMod 2} (h : band (resid g) = modelBand a b) :
    label g = a := by
  have h₁ := congrArg (fun M : Mat => M 0 1) h
  have h₂ := congrArg (fun M : Mat => M 2 3) h
  have h₁' : resid g 0 1 = a + b := by simpa [band, modelBand, first, second] using h₁
  have h₂' : resid g 2 3 = b := by simpa [band, modelBand, first, second] using h₂
  rw [label, h₁', h₂', add_sub_cancel_right]

lemma outside_small_engel (h : Gr) (hh : h ∉ small) :
    h ∈ leftEngel Gr 4 := by
  obtain ⟨a,b,hab⟩ := resid_band h
  have ha : a ≠ 0 := by
    change label h ≠ 0 at hh
    rw [label_of_band hab] at hh
    exact hh
  intro g
  apply resid_eq_zero_iff.mp
  rw [fourth_exact, hab, lie_four, fourthModel a b ha, mul_zero, zero_mul, sub_zero]

def unitOf (A : Mat) (hA : Gap 1 A) : Matˣ :=
  ⟨1+A, (1+A)^7,
    by rw [← pow_succ', pow_eight A hA],
    by rw [← pow_succ, pow_eight A hA]⟩

def element (a b : ZMod 2) : Gr := by
  let A := modelBand a b
  have hA : Gap 1 A := by
    intro i j hij
    simp [A, modelBand, first, second, show j.val ≠ i.val+1 by omega]
  refine ⟨unitOf A hA, ?_⟩
  change Gap 1 ((1+A)-1) ∧ ∃ c d, band ((1+A)-1) = modelBand c d
  rw [add_comm (1 : Mat), add_sub_cancel_right]
  refine ⟨hA, a, b, ?_⟩
  ext i j
  by_cases he : j.val = i.val + 1 <;> simp [band, A, modelBand, first, second, he]

lemma element_band (a b : ZMod 2) : band (resid (element a b)) = modelBand a b := by
  change band ((1 + modelBand a b) - 1) = _
  rw [add_comm (1 : Mat), add_sub_cancel_right]
  ext i j
  by_cases he : j.val = i.val + 1 <;> simp [band, modelBand, first, second, he]

lemma witness_entry :
    (lieIter (modelBand 1 0) (modelBand 0 1) 4) 0 5 = 1 := by
  rw [lie_four]
  decide +kernel

lemma witness : comm (element 1 0) (element 0 1) 4 ≠ 1 := by
  intro h
  have hzero := resid_eq_zero_iff.mpr h
  rw [fourth_exact, element_band, element_band] at hzero
  have hz := congrArg (fun M : Mat => M 0 5) hzero
  rw [witness_entry] at hz
  exact one_ne_zero hz

lemma comm_one_later {g h : Gr} {n m : ℕ} (hnm : n ≤ m) (he : comm g h n = 1) :
    comm g h m = 1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero => exact he
  | succ k ih => simp [OMA.S_mo_144090.comm, ih]

end UpperBand

open UpperBand in
theorem OMA.disproof :
    ¬ (∀ (G : Type) [Group G] [Finite G] [Group.IsNilpotent G] (n : ℕ),
      0 < n → leftEngel G n = Set.univ →
      (∀ m : ℕ, 0 < m → m < n → leftEngel G m ≠ Set.univ) →
      Subgroup.closure (leftEngel G (n-1))ᶜ = ⊤) := by
  intro h
  let _ : Group.IsNilpotent Gr := group_nilpotent
  have hfifth : leftEngel Gr 5 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro k g
    exact fifth_zero g k
  have hminimal (m : ℕ) (_ : 0 < m) (hm : m < 5) : leftEngel Gr m ≠ Set.univ := by
    intro he
    have hw : element 0 1 ∈ leftEngel Gr m := he.symm ▸ Set.mem_univ _
    exact witness (comm_one_later (by omega) (hw (element 1 0)))
  have heq := h Gr 5 (by decide) hfifth hminimal
  have hsubset : (leftEngel Gr (5-1))ᶜ ⊆ small := by
    intro g hg
    by_contra hn
    exact hg (outside_small_engel g hn)
  have hcl := (Subgroup.closure_le small).2 hsubset
  rw [heq] at hcl
  have hgood : element 1 0 ∈ small := hcl (Subgroup.mem_top _)
  change label (element 1 0) = 0 at hgood
  rw [label_of_band (element_band 1 0)] at hgood
  exact one_ne_zero hgood