import OMAReductions.R_Erdos1057_erdos_1057_variants_harman_lower_bound_R2
import Mathlib

namespace OMA.GreedyCover

open Finset

noncomputable def remaining {A : Type*} [Fintype A] (S : Finset ℕ)
    (f : ℕ → A → ℂ) (z : ℕ → ℂ) : Finset A := by
  classical
  exact univ.filter (fun a => ∀ i ∈ S, z i ≠ f i a)

private theorem remaining_insert {A : Type*} [Fintype A] (S : Finset ℕ)
    (f : ℕ → A → ℂ) (z : ℕ → ℂ) {i : ℕ} (hi : i ∉ S) (value : ℂ) :
    remaining (insert i S) f (Function.update z i value) =
      (remaining S f z).filter (fun a => f i a ≠ value) := by
  classical
  ext a
  simp only [remaining, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro j hj
      simpa [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using h j (Or.inr hj)
    · simpa [ne_comm] using h i (Or.inl rfl)
  · rintro ⟨h,ne⟩ j (rfl|hj)
    · simpa [ne_comm] using ne
    · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using h j hj

private theorem large_fiber {A : Type*} [Fintype A] (R : Finset A) (f : A → ℂ)
    (m : ℕ) (hsize : (univ.image f).card ≤ m) (nonzero : ∀ a, f a ≠ 0) :
    ∃ v : ℂ, v ≠ 0 ∧ R.card ≤ m * (R.filter (fun a => f a=v)).card := by
  classical
  by_cases hn : R.Nonempty
  · let valueCount : ℂ → ℕ := fun v => (R.filter (fun a => f a=v)).card
    obtain ⟨v,hv,maximum⟩ := Finset.exists_max_image (R.image f) valueCount (hn.image _)
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
    refine ⟨f a,nonzero _,?_⟩
    have hi : (R.image f).card ≤ m :=
      (Finset.card_le_card (Finset.image_subset_image (Finset.subset_univ R))).trans hsize
    calc
      R.card = ∑ v ∈ R.image f, valueCount v := Finset.card_eq_sum_card_image _ _
      _ ≤ ∑ _v ∈ R.image f, valueCount (f a) := Finset.sum_le_sum maximum
      _ = (R.image f).card * valueCount (f a) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hi
  · exact ⟨1,one_ne_zero,by simp [Finset.not_nonempty_iff_eq_empty.mp hn]⟩

private theorem shrink {A : Type*} [Fintype A] (R : Finset A) (f : A → ℂ)
    (m : ℕ) (hm : 0 < m) (hsize : (univ.image f).card ≤ m)
    (nonzero : ∀ a, f a ≠ 0) :
    ∃ v : ℂ, v ≠ 0 ∧
      ((R.filter (fun a => f a ≠ v)).card : ℝ) ≤ R.card * Real.exp (-(1/(m:ℝ))) := by
  classical
  obtain ⟨v,hv,hcard⟩ := large_fiber R f m hsize nonzero
  refine ⟨v,hv,?_⟩
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have count : ((R.filter (fun a => f a=v)).card : ℝ) +
      ((R.filter (fun a => f a ≠ v)).card : ℝ) = R.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := R) (fun a => f a=v)
  have hcard' : (R.card : ℝ) ≤ (m:ℝ) * (R.filter (fun a => f a=v)).card := by
    exact_mod_cast hcard
  have enough : (R.card : ℝ) / m ≤ (R.filter (fun a => f a=v)).card :=
    (div_le_iff₀ hm').mpr (by rw [mul_comm]; exact hcard')
  calc
    _ ≤ R.card - (R.card:ℝ)/m := by linarith
    _ = (R.card:ℝ)*(1-1/(m:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      have h := Real.add_one_le_exp (-(1/(m:ℝ)))
      linarith) (by positivity)

private theorem chosen_bound {A : Type*} [Fintype A] (S : Finset ℕ)
    (f : ℕ → A → ℂ) (m : ℕ) (hm : 0 < m)
    (range_bound : ∀ i, (univ.image (f i)).card ≤ m)
    (nonzero : ∀ i a, f i a ≠ 0) :
    ∃ z : ℕ → ℂ, (∀ i ∈ S, z i ≠ 0) ∧
      ((remaining S f z).card : ℝ) ≤ Fintype.card A * Real.exp (-(S.card/(m:ℝ))) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 1,by simp,by simp [remaining]⟩
  | insert i S hi ih =>
    obtain ⟨z,hz,hr⟩ := ih
    obtain ⟨v,hv,hshrink⟩ := shrink (remaining S f z) (f i) m hm (range_bound i) (nonzero i)
    refine ⟨Function.update z i v,?_ ,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hs
      · simpa using hv
      · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hs hi)] using hz j hs
    · rw [remaining_insert S f z hi, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      have exponent :
          -(((S.card:ℝ)+1)/m) = -(S.card/(m:ℝ)) + -(1/(m:ℝ)) := by ring
      rw [exponent, Real.exp_add, ← mul_assoc]
      exact hshrink.trans (mul_le_mul_of_nonneg_right hr (by positivity))

private theorem assign_remaining {A : Type*} [Fintype A] (R : Finset A) (U : Finset ℕ)
    (f : ℕ → A → ℂ) (nonzero : ∀ i a, f i a ≠ 0) (hsize : R.card ≤ U.card) :
    ∃ z : ℕ → ℂ, (∀ i ∈ U, z i ≠ 0) ∧ ∀ a ∈ R, ∃ i ∈ U, z i = f i a := by
  classical
  obtain ⟨e⟩ : Nonempty (R ↪ U) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using hsize)
  let z : ℕ → ℂ := fun i =>
    if h : ∃ a : R, (e a).val=i then f i (Classical.choose h).val else 1
  refine ⟨z,?_ ,?_⟩
  · intro i _
    dsimp [z]
    split
    · exact nonzero _ _
    · exact one_ne_zero
  · intro a ha
    let aa : R := ⟨a,ha⟩
    refine ⟨(e aa).val,(e aa).property,?_⟩
    have h : ∃ x : R, (e x).val = (e aa).val := ⟨aa,rfl⟩
    dsimp [z]
    rw [dif_pos h]
    have eq : Classical.choose h = aa :=
      e.injective (Subtype.ext (Classical.choose_spec h))
    rw [eq]

theorem cover {A : Type*} [Fintype A] (T : Finset ℕ)
    (f : ℕ → A → ℂ) (m : ℕ) (hm : 0 < m) (hmN : m ≤ Fintype.card A)
    (range_bound : ∀ i, (univ.image (f i)).card ≤ m)
    (nonzero : ∀ i a, f i a ≠ 0)
    (budget : (m:ℝ)*(1+Real.log (Fintype.card A/(m:ℝ))) ≤ T.card) :
    ∃ z : ℕ → ℂ, (∀ i ∈ T, z i ≠ 0) ∧ ∀ a : A, ∃ i ∈ T, z i = f i a := by
  classical
  let N : ℕ := Fintype.card A
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hNm : (m:ℝ) ≤ N := by exact_mod_cast hmN
  have hN : (0:ℝ) < N := hm'.trans_le hNm
  let r : ℝ := m*Real.log (N/(m:ℝ))
  have hr : 0 ≤ r := mul_nonneg hm'.le
    (Real.log_nonneg ((le_div_iff₀ hm').mpr (by simpa using hNm)))
  let k : ℕ := ⌊r⌋₊+1
  have hsum : (m:ℝ)+r ≤ T.card := by
    change (m:ℝ)*(1+Real.log (N/(m:ℝ))) ≤ T.card at budget
    dsimp [r]
    linarith
  have hf : (⌊r⌋₊:ℝ) ≤ r := Nat.floor_le hr
  have hused : m + ⌊r⌋₊ ≤ T.card := by
    exact_mod_cast (show (m:ℝ)+(⌊r⌋₊:ℝ) ≤ T.card by linarith)
  have hk : k ≤ T.card := by dsimp [k]; omega
  obtain ⟨S,hST,hS⟩ := Finset.exists_subset_card_eq hk
  obtain ⟨z,hz,hremain⟩ := chosen_bound S f m hm range_bound nonzero
  let R := remaining S f z
  let U := T \ S
  have hR' : (R.card:ℝ) < m := by
    have hk' : r < (k:ℝ) := by
      rw [show (k:ℝ)=(⌊r⌋₊:ℝ)+1 by simp [k]]
      exact Nat.lt_floor_add_one r
    have hexp : -((k:ℝ)/m) < -Real.log (N/(m:ℝ)) := by
      have hquot : Real.log (N/(m:ℝ)) < (k:ℝ)/m :=
        (lt_div_iff₀ hm').mpr (by simpa [r,mul_comm] using hk')
      linarith
    calc
      _ ≤ (N:ℝ)*Real.exp (-(k/(m:ℝ))) := by simpa [R,N,hS] using hremain
      _ < (N:ℝ)*Real.exp (-Real.log (N/(m:ℝ))) :=
        mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hexp) hN
      _ = _ := by rw [Real.exp_neg, Real.exp_log (div_pos hN hm')]; field_simp
  have hR : R.card < m := by exact_mod_cast hR'
  have hfree : R.card ≤ U.card := by
    dsimp [U]
    rw [Finset.card_sdiff_of_subset hST,hS]
    dsimp [k]
    omega
  obtain ⟨w,hw,hcover⟩ := assign_remaining R U f nonzero hfree
  refine ⟨fun i => if i∈S then z i else w i,?_ ,?_⟩
  · intro i hi
    by_cases hs : i∈S
    · simp [hs,hz i hs]
    · have hu : i∈U := Finset.mem_sdiff.mpr ⟨hi,hs⟩
      simp [hs,hw i hu]
  · intro a
    by_cases ha : a∈R
    · obtain ⟨i,hi,eq⟩ := hcover a ha
      have pair := Finset.mem_sdiff.mp hi
      exact ⟨i,pair.1,by simp [pair.2,eq]⟩
    · have h : ∃ i ∈ S, z i = f i a := by
        simpa [R,remaining,not_forall] using ha
      obtain ⟨i,hi,eq⟩ := h
      exact ⟨i,hST hi,by simp [hi,eq]⟩

end OMA.GreedyCover

namespace OMA.DavenportBound

open Finset

private theorem char_nonzero {G : Type*} [AddCommGroup G] (χ : AddChar G ℂ) (a : G) :
    χ a ≠ 0 := by
  intro h
  have one : χ a * χ (-a) = 1 := by rw [← χ.map_add_eq_mul, add_neg_cancel, χ.map_zero_eq_one]
  simp [h] at one

private theorem range_card {G : Type*} [CommGroup G] [Finite G] [Fintype (AddChar (Additive G) ℂ)]
    (m : ℕ) (hm : 0 < m) (g : G) (hg : g ^ m = 1) :
    (univ.image (fun χ : AddChar (Additive G) ℂ => χ (Additive.ofMul g))).card ≤ m := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  let : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite _
  let values := univ.image (fun χ : AddChar (Additive G) ℂ => χ (Additive.ofMul g))
  let into : values → rootsOfUnity m ℂ := fun z => by
    have hroot : z.val ^ m = 1 := by
      obtain ⟨χ,_,hz⟩ := Finset.mem_image.mp z.property
      rw [← hz, ← χ.map_nsmul_eq_pow, ← ofMul_pow, hg, ofMul_one,
        χ.map_zero_eq_one]
    have hzero : z.val ≠ 0 := by
      obtain ⟨χ,_,hz⟩ := Finset.mem_image.mp z.property
      exact hz ▸ char_nonzero χ (Additive.ofMul g)
    exact ⟨Units.mk0 _ hzero, (mem_rootsOfUnity' _ _).mpr hroot⟩
  have hinj : Function.Injective into := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun r : rootsOfUnity m ℂ => ((r.val : ℂˣ) : ℂ)) h
  calc
    values.card = Fintype.card values := (Fintype.card_coe _).symm
    _ ≤ Fintype.card (rootsOfUnity m ℂ) := Fintype.card_le_of_injective into hinj
    _ = Nat.card (rootsOfUnity m ℂ) := (Nat.card_eq_fintype_card).symm
    _ ≤ m := card_rootsOfUnity (k := m) ℂ

private theorem char_prod {G : Type*} [CommGroup G] (χ : AddChar (Additive G) ℂ)
    (I : Finset ℕ) (g : ℕ → G) :
    (∏ i ∈ I, χ (Additive.ofMul (g i))) = χ (Additive.ofMul (∏ i ∈ I, g i)) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, ofMul_mul, χ.map_add_eq_mul]

theorem bound (G : Type) [CommGroup G] [Finite G] (T : Finset ℕ) (g : ℕ → G)
    (budget : (Monoid.exponent G : ℝ) *
      (1 + Real.log ((Nat.card G : ℝ) / (Monoid.exponent G : ℝ))) ≤ T.card) :
    ∃ I ⊆ T, I.Nonempty ∧ ∏ i ∈ I, g i = 1 := by
  classical
  let : Fintype (Additive G) := Fintype.ofFinite _
  let A := AddChar (Additive G) ℂ
  let m := Monoid.exponent G
  have cardG : Fintype.card (Additive G) = Nat.card G :=
    (Nat.card_eq_fintype_card (α := Additive G)).symm.trans
      (Nat.card_congr Additive.toMul)
  have cardA : Fintype.card A = Nat.card G := AddChar.card_eq.trans cardG
  have hN : 0 < Nat.card G := Nat.card_pos
  have hm : 0 < m := Monoid.exponent_pos_of_exists (Nat.card G) hN
    (fun _ => pow_card_eq_one')
  have hmN : m ≤ Fintype.card A := by
    rw [cardA]
    exact Nat.le_of_dvd hN Group.exponent_dvd_nat_card
  let f : ℕ → A → ℂ := fun i χ => χ (Additive.ofMul (g i))
  obtain ⟨z,hz,hcover⟩ := OMA.GreedyCover.cover T f m hm hmN
    (fun i => range_card m hm (g i) (Monoid.pow_exponent_eq_one _))
    (fun i χ => char_nonzero χ _) (by rwa [cardA])
  by_contra hnone
  have vanishes (χ : A) : (∏ i ∈ T, (z i - f i χ)) = 0 := by
    obtain ⟨i,hi,hzi⟩ := hcover χ
    exact Finset.prod_eq_zero hi (sub_eq_zero.mpr hzi)
  have product_sum :
      (∑ χ : A, ∏ i ∈ T, (z i - f i χ)) =
        ∑ I ∈ T.powerset, ((-1 : ℂ) ^ I.card * ∏ i ∈ T \ I, z i) *
          (∑ χ : A, χ (Additive.ofMul (∏ i ∈ I, g i))) := by
    calc
      _ = ∑ χ : A, ∑ I ∈ T.powerset, ((-1 : ℂ)^I.card * ∏ i ∈ T \ I, z i) *
          χ (Additive.ofMul (∏ i ∈ I, g i)) := by
        apply Finset.sum_congr rfl
        intro χ _
        rw [Finset.prod_sub]
        apply Finset.sum_congr rfl
        intro I _
        rw [show (∏ i ∈ I, f i χ) = _ from char_prod χ I g]
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  have positive_term :
      (∑ I ∈ T.powerset, ((-1 : ℂ) ^ I.card * ∏ i ∈ T \ I, z i) *
        (∑ χ : A, χ (Additive.ofMul (∏ i ∈ I, g i)))) =
        (∏ i ∈ T, z i) * (Nat.card G : ℂ) := by
    rw [Finset.sum_eq_single ∅]
    · have orthogonality : (∑ χ : A, χ 0) = (Nat.card G : ℂ) := by
        simpa only [if_pos rfl, ite_true, cardG] using
          (AddChar.sum_apply_eq_ite (α := Additive G) 0)
      simp only [Finset.card_empty, pow_zero, Finset.sdiff_empty, Finset.prod_empty,
        ofMul_one, one_mul, orthogonality]
    · intro I hI hne
      have hp : (∏ i ∈ I, g i) ≠ 1 :=
        fun one => hnone ⟨I,Finset.mem_powerset.mp hI,Finset.nonempty_iff_ne_empty.mpr hne,one⟩
      have hchar : (∑ χ : A, χ (Additive.ofMul (∏ i ∈ I, g i))) = 0 :=
        AddChar.sum_apply_eq_zero_iff_ne_zero.2 (((ofMul_eq_zero (A := G)).not.mpr hp))
      rw [hchar, mul_zero]
    · simp
  rw [positive_term] at product_sum
  simp only [vanishes, Finset.sum_const_zero] at product_sum
  exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr hz) (Nat.cast_ne_zero.mpr hN.ne')) product_sum.symm

end OMA.DavenportBound

theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_harman_lower_bound_R2.H1 := OMA.DavenportBound.bound