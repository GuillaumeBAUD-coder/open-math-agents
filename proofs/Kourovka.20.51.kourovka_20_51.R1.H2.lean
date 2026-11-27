import OMAReductions.R_Kourovka_20_51_kourovka_20_51_R1

/-! Count commuting pairs of affine maps over the field of q elements whose
slopes belong to a subgroup of order p. For two fixed slopes there are q
choices of commuting translations, except at slopes (1,1), where there are q². -/

namespace OMA.AffineCount

variable {K : Type} [Field K]

structure Aff (S : Subgroup Kˣ) where
  slope : S
  shift : K

variable {S : Subgroup Kˣ}

private lemma Aff.ext {a b : Aff S} (hs : a.slope = b.slope) (ht : a.shift = b.shift) :
    a = b := by cases a; cases b; congr

private def coords : Aff S ≃ S × K where
  toFun a := (a.slope,a.shift)
  invFun a := ⟨a.1,a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Group (Aff S) where
  one := ⟨1,0⟩
  mul a b := ⟨a.slope*b.slope, a.shift + (a.slope.val : K)*b.shift⟩
  inv a := ⟨a.slope⁻¹,-((a.slope.val : K)⁻¹*a.shift)⟩
  one_mul a := by
    apply Aff.ext (one_mul _)
    change 0 + (1 : K)*a.shift = _
    simp
  mul_one a := by
    apply Aff.ext (mul_one _)
    change a.shift + _ * 0 = _
    simp
  mul_assoc a b c := by
    apply Aff.ext
    · exact mul_assoc _ _ _
    · change a.shift + _ * b.shift + ((a.slope.val : K) * b.slope.val) * c.shift =
          a.shift + _ * (b.shift + _ * c.shift)
      ring
  inv_mul_cancel a := by
    apply Aff.ext
    · exact inv_mul_cancel _
    · change -((a.slope.val : K)⁻¹*a.shift) + ((a.slope.val⁻¹ : Kˣ) : K)*a.shift = 0
      simp [Units.val_inv_eq_inv_val]

private lemma comm {a b : Aff S} : Commute a b ↔
    (1 - (b.slope.val : K))*a.shift = (1 - (a.slope.val : K))*b.shift := by
  constructor
  · intro h
    have eq := congrArg Aff.shift h.eq
    change a.shift + _ * b.shift = b.shift + _ * a.shift at eq
    linear_combination eq
  · intro h
    apply Aff.ext
    · exact mul_comm _ _
    · change a.shift + _ * b.shift = b.shift + _ * a.shift
      linear_combination h

private abbrev Line (u v : K) := {z : K × K // u*z.1 = v*z.2}

private def bySlopes : {z : Aff S × Aff S // Commute z.1 z.2} ≃
    Σ s : S × S, Line (1-(s.2.val : K)) (1-(s.1.val : K)) where
  toFun z := ⟨(z.val.1.slope, z.val.2.slope), (z.val.1.shift, z.val.2.shift), comm.mp z.prop⟩
  invFun z := ⟨(⟨z.1.1,z.2.val.1⟩,⟨z.1.2,z.2.val.2⟩), comm.mpr z.2.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma lineCount [DecidableEq K] (u v : K) :
    Nat.card (Line u v) = if u=0 ∧ v=0 then Nat.card K * Nat.card K else Nat.card K := by
  classical
  by_cases hu : u = 0
  · subst u
    by_cases hv : v = 0
    · subst v
      simp only [and_self, if_true]
      rw [← Nat.card_prod]
      exact Nat.card_congr ⟨Subtype.val, fun z => ⟨z, by simp⟩, fun _ => rfl, fun _ => rfl⟩
    · simp only [hv, and_false, if_false]
      apply Nat.card_congr
      refine ⟨fun z => z.val.1, fun x => ⟨(x,0), by simp⟩, ?_, fun _ => rfl⟩
      rintro ⟨⟨x,y⟩,h⟩
      have hy : y = 0 := by simpa [hv] using h.symm
      subst y
      rfl
  · simp only [hu, false_and, if_false]
    apply Nat.card_congr
    refine ⟨fun z => z.val.2, fun y => ⟨(v*y/u,y), ?_⟩, ?_, fun _ => rfl⟩
    · dsimp; field_simp
    · rintro ⟨⟨x,y⟩,h⟩
      change u*x = v*y at h
      apply Subtype.ext
      exact Prod.ext ((div_eq_iff hu).mpr (by linear_combination -h)) rfl

private lemma slope_one (a : S) : 1-(a.val : K) = 0 ↔ a=1 := by
  rw [sub_eq_zero]
  constructor
  · intro h
    exact Subtype.ext (Units.ext h.symm)
  · rintro rfl
    rfl

private lemma count [Fintype K] [Fintype S] :
    Nat.card (ConjClasses (Aff S)) * (Nat.card S * Nat.card K) =
      (Nat.card S * Nat.card S) * Nat.card K + (Nat.card K-1)*Nat.card K := by
  classical
  have hG := Nat.card_congr (coords (S := S))
  rw [Nat.card_prod] at hG
  rw [← hG, ← card_comm_eq_card_conjClasses_mul_card, Nat.card_congr (bySlopes (S := S)), Nat.card_sigma]
  have each (s : S × S) : Nat.card (Line (1-(s.2.val : K)) (1-(s.1.val : K))) =
      Nat.card K + (if s=(1,1) then (Nat.card K-1)*Nat.card K else 0) := by
    rw [lineCount, slope_one, slope_one]
    by_cases h : s=(1,1)
    · subst s
      simp only [and_self, if_true]
      have hk : 0 < Nat.card K := Nat.card_pos
      rw [← Nat.succ_pred_eq_of_pos hk] at ⊢
      simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
      ring
    · have hn : ¬(s.2=1 ∧ s.1=1) := fun hs => h (Prod.ext hs.2 hs.1)
      simp [hn,h]
  simp_rw [each]
  simp [Finset.sum_add_distrib, Nat.card_eq_fintype_card, mul_assoc]

end OMA.AffineCount

open OMA.AffineCount

theorem OMA.solution : OMA.R_Kourovka_20_51_kourovka_20_51_R1.H2 := by
  intro p q hp op hq oq hd
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨S,hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := (ZMod q)ˣ) p (n := 1)
    (by simpa [Nat.card_eq_fintype_card, ZMod.card_units, Nat.totient_prime hq] using hd)
  rw [pow_one] at hS
  have hq' : Nat.card (ZMod q) = q := by simp [Nat.card_eq_fintype_card]
  have hG : Nat.card (Aff S) = p*q := by rw [Nat.card_congr coords, Nat.card_prod, hS, hq']
  let : Finite (Aff S) := Finite.of_equiv _ coords.symm
  have : Nontrivial S := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hS]; exact hp.one_lt)
  obtain ⟨a,ha⟩ := exists_ne (1 : S)
  refine ⟨Aff S, inferInstance, inferInstance, ?_, hG ▸ op.mul oq, ?_⟩
  · refine ⟨⟨a,0⟩,⟨1,1⟩,fun h => ha ?_⟩
    have he := congrArg Aff.shift h
    apply Subtype.ext
    apply Units.ext
    change 0 + (a.val : ZMod q)*1 = 1 + 1*0 at he
    simpa using he
  · have h := count (K := ZMod q) (S := S)
    rw [hS,hq'] at h
    have hq1 : p*((q-1)/p) = q-1 := Nat.mul_div_cancel' hd
    apply Nat.eq_of_mul_eq_mul_right (show 0 < p*q from Nat.mul_pos hp.pos hq.pos)
    rw [h]
    calc
      _ = (p*p + p*((q-1)/p))*q := by rw [hq1]; ring
      _ = _ := by ring
