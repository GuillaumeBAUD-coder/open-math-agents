import OMAReductions.R_Erdos470_erdos_470_variants_weird_pos_density_R1
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # A positive lower density of weird multiples of 70 -/
open Finset Filter Real
namespace Weird470
noncomputable section
private def excess (m : ℕ) : ℝ := ∑ d ∈ m.divisors.erase 1, (1:ℝ)/d

private lemma sum_div (m : ℕ) (hm : 0 < m) :
    (∑ d ∈ m.divisors, (d:ℝ)) = m*(1+excess m) := by
  have hx := Nat.sum_div_divisors m (fun d : ℕ => (d:ℝ))
  rw [← hx]
  have he : 1+excess m = ∑ d ∈ m.divisors, (1:ℝ)/d := by
    have h := sum_erase_add (s := m.divisors) (fun d : ℕ => (1:ℝ)/d) (Nat.one_mem_divisors.mpr hm.ne')
    simpa [excess,add_comm] using h
  rw [he,mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
  ring

private lemma eq_of_remainder (a r m : ℕ) (hm : 0 < m) (hr : r < m) (he : r+m*a=m*70) : a = 70 := by
  by_contra hh
  rcases lt_or_gt_of_ne hh with h | h
  · have h1 := Nat.mul_le_mul_left m (Nat.succ_le_of_lt h)
    nlinarith only [h1,hr,he]
  · have h1 := Nat.mul_le_mul_left m (Nat.succ_le_of_lt h)
    nlinarith only [h1,hm,he,Nat.zero_le r]

private lemma multiply {m : ℕ} (hm : 0 < m) (hc : m.Coprime 70) (hs : excess m < 1/144) :
    (m*70).Weird := by
  classical
  refine ⟨Nat.weird_seventy.1.mul_left hm.ne',?_⟩
  rintro ⟨_,U,hU,hUs⟩
  let L := (70:ℕ).divisors.image (m*·)
  let V := (70:ℕ).properDivisors.filter fun d => m*d ∈ U
  have hL : L ⊆ (m*70).divisors := by
    rintro _ h
    obtain ⟨d,hd,rfl⟩ := mem_image.mp h
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left _ (Nat.dvd_of_mem_divisors hd),by positivity⟩
  have h144 : ∑ d ∈ (70:ℕ).divisors, d = 144 := by decide
  have hsumL : ∑ d ∈ L, d = m*144 := by
    rw [← h144,mul_sum]
    exact sum_image (mul_right_injective₀ hm.ne').injOn
  have hcomp : (∑ d ∈ (m*70).divisors \ L, d) < m := by
    have h := sum_sdiff hL (f := id)
    simp only [id_eq,hsumL,hc.sum_divisors_mul,h144] at h
    have hh := sum_div m hm
    have hh' : ((∑ d ∈ m.divisors, d : ℕ):ℝ) = m*(1+excess m) := by simpa using hh
    have hr : ((∑ d ∈ (m*70).divisors \ L, d : ℕ):ℝ) + m*144 =
        ((∑ d ∈ m.divisors, d : ℕ):ℝ)*144 := by exact_mod_cast h
    rw [hh'] at hr
    apply (Nat.cast_lt (α:=ℝ)).mp
    linarith only [hr,mul_lt_mul_of_pos_left hs (by exact_mod_cast hm : (0:ℝ) < m)]
  have hV : V.image (m*·) = U ∩ L := by
    ext z
    constructor
    · intro h
      obtain ⟨d,hd,rfl⟩ := mem_image.mp h
      obtain ⟨hd,hu⟩ := mem_filter.mp hd
      exact mem_inter.mpr ⟨hu,mem_image.mpr ⟨d,Nat.properDivisors_subset_divisors hd,rfl⟩⟩
    · intro h
      obtain ⟨hu,hl⟩ := mem_inter.mp h
      obtain ⟨d,hd,rfl⟩ := mem_image.mp hl
      refine mem_image.mpr ⟨d,mem_filter.mpr ⟨Nat.mem_properDivisors.mpr ⟨Nat.dvd_of_mem_divisors hd,?_⟩,hu⟩,rfl⟩
      have hlt := (Nat.mem_properDivisors.mp (hU hu)).2
      exact Nat.lt_of_mul_lt_mul_left hlt
  have hsumV : ∑ d ∈ U ∩ L, d = m*∑ d ∈ V,d := by
    rw [← hV,mul_sum,sum_image (mul_right_injective₀ hm.ne').injOn]
  have hrest : ∑ d ∈ U \ L,d < m := by
    apply lt_of_le_of_lt _ hcomp
    apply sum_le_sum_of_subset
    intro d hd
    exact mem_sdiff.mpr ⟨Nat.properDivisors_subset_divisors (hU (mem_sdiff.mp hd).1),(mem_sdiff.mp hd).2⟩
  have hsum := sum_sdiff (inter_subset_left (s₁:=U) (s₂:=L)) (f:=id)
  simp only [id_eq,sdiff_inter_self_left,hsumV,hUs] at hsum
  have h70 : ∑ d ∈ V,d = 70 := eq_of_remainder _ _ _ hm hrest hsum
  exact Nat.weird_seventy.2 ⟨by decide,V,filter_subset _ _,h70⟩
private lemma ap_card (b B d T : ℕ) (hc : d.Coprime B) :
    ((range T).filter fun t => d ∣ B*t+b).card ≤ T/d+1 := by
  have h := Finset.card_le_card_of_injOn (s := (range T).filter fun t => d ∣ B*t+b)
      (t := range (T/d+1)) (fun t => t/d) (by
        intro t ht
        have ht' := mem_range.mp (mem_filter.mp ht).1
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt ht')))) (by
        intro u hu v hv he
        have hm := (Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp hu).2).trans
          (Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp hv).2).symm
        have hr : u % d = v % d := Nat.ModEq.cancel_left_of_coprime hc
          (Nat.ModEq.add_right_cancel' b hm)
        change u/d = v/d at he
        have h1 := Nat.div_add_mod u d
        have h2 := Nat.div_add_mod v d
        rw [he, hr] at h1
        omega)
  simpa using h



variable (P : ℕ)
private def progression (t : ℕ) := P*t+1
variable (Ppos : 0 < P) (Pdiv : ∀ {d : ℕ}, 0 < d → d ≤ 1000 → d ∣ P)

private lemma cop (t : ℕ) : (progression P t).Coprime P := by
  rw [progression,add_comm,Nat.coprime_comm,Nat.coprime_add_mul_left_right]
  simp

include Pdiv in
private lemma mean (T : ℕ) : (∑ t ∈ range T, excess (progression P t)) ≤
    (T:ℝ)/1000 + (1+log (P*T+1 : ℕ)) := by
  classical
  let U := P*T+1
  let D := Ioc 1000 U
  have h0 (t : ℕ) : 0 < progression P t := Nat.succ_pos _
  have hsum t (ht : t ∈ range T) : excess (progression P t) =
      ∑ d ∈ D, if d ∣ progression P t then (1:ℝ)/d else 0 := by
    rw [excess,← sum_filter]
    apply sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [mem_erase, Nat.mem_divisors,mem_filter,D,mem_Ioc]
    constructor
    · rintro ⟨hd1,hd,_⟩
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (h0 t)
      have hbig : 1000 < d := by
        by_contra! hs
        exact hd1 (Nat.eq_one_of_dvd_coprimes (cop P t) hd (Pdiv hd0 hs))
      have hdle := Nat.le_of_dvd (h0 t) hd
      have hh := Nat.mul_le_mul_left P (mem_range.mp ht).le
      exact ⟨⟨hbig,hdle.trans (Nat.succ_le_succ hh)⟩,hd⟩
    · rintro ⟨⟨h1000,_⟩,hd⟩
      exact ⟨by omega,hd,(h0 t).ne'⟩
  have hcount (d : ℕ) : ((range T).filter fun t => d ∣ progression P t).card ≤ T/d+1 := by
    by_cases hc : d.Coprime P
    · exact ap_card 1 P d T hc
    · have he : ((range T).filter fun t => d ∣ progression P t) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact hc ((cop P t).coprime_dvd_left (mem_filter.mp ht).2)
      simp [he]
  calc
    _ = ∑ d ∈ D, ∑ t ∈ range T, if d ∣ progression P t then (1:ℝ)/d else 0 := by
      rw [sum_comm]
      exact sum_congr rfl hsum
    _ ≤ ∑ d ∈ D, ((T:ℝ)*((d:ℝ)^2)⁻¹ + 1/d) := by
      apply sum_le_sum
      intro d hd
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      calc
        _ ≤ ((T/d+1 : ℕ):ℝ) * (1/d) := by gcongr; exact_mod_cast hcount d
        _ ≤ ((T:ℝ)/d+1) * (1/d) := by
          push_cast; gcongr; exact Nat.cast_div_le
        _ = _ := by ring
    _ ≤ _ := by
      rw [sum_add_distrib,← mul_sum]
      apply add_le_add
      · change _ ≤ (T:ℝ)/1000
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        by_cases h : 1000 ≤ U
        · have h1 := sum_Ioc_inv_sq_le_sub (α:=ℝ) (by decide : (1000:ℕ) ≠ 0) h
          norm_num at h1 ⊢
          linarith [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) U)]
        · have : D = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
          rw [this,sum_empty]; norm_num
      · calc
          _ ≤ ∑ d ∈ Icc 1 U, (1:ℝ)/d := sum_le_sum_of_subset_of_nonneg (by
            intro d hd; exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hd).1; omega,(mem_Ioc.mp hd).2⟩) (by intros; positivity)
          _ = (harmonic U : ℝ) := by simp [harmonic_eq_sum_Icc,one_div]
          _ ≤ _ := harmonic_le_one_add_log U

include Ppos Pdiv in
private lemma many : ∀ᶠ T : ℕ in atTop,
    T ≤ 2*((range T).filter (fun t => excess (progression P t) < 1/144)).card := by
  classical
  have ht : Tendsto (fun T : ℕ => (P:ℝ)*T+1) atTop atTop := by
    apply tendsto_atTop_mono (fun t => ?_) tendsto_natCast_atTop_atTop
    have hp : (1:ℝ) ≤ P := by exact_mod_cast Ppos
    nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α:=ℝ) t)]
  let δ : ℝ := 1/(10000*((P:ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [ht.eventually (isLittleO_log_id_atTop.bound hδ),eventually_ge_atTop 10000] with T hlog hT
  have hT' : (10000:ℝ) ≤ T := by exact_mod_cast hT
  have hP : (0:ℝ) ≤ P := Nat.cast_nonneg _
  have hpos : 0 ≤ log ((P:ℝ)*T+1) := log_nonneg (by nlinarith [mul_nonneg hP (Nat.cast_nonneg (α:=ℝ) T)])
  change ‖log ((P:ℝ)*T+1)‖ ≤ δ*‖(P:ℝ)*T+1‖ at hlog
  rw [Real.norm_of_nonneg hpos, Real.norm_of_nonneg (by positivity)] at hlog
  have hlog' : log ((P:ℝ)*T+1) ≤ (T:ℝ)/10000 := by
    apply hlog.trans
    dsimp [δ]
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  let bad := (range T).filter (fun t => ¬ excess (progression P t) < 1/144)
  have hmean := mean P Pdiv T
  push_cast at hmean
  have hb : (bad.card:ℝ)*(1/144) ≤ ∑ t ∈ range T, excess (progression P t) := calc
    _ = ∑ _ ∈ bad, (1/144:ℝ) := by simp
    _ ≤ ∑ t ∈ bad, excess (progression P t) := sum_le_sum (fun t h => le_of_not_gt (mem_filter.mp h).2)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; exact sum_nonneg (fun _ _ => by positivity))
  have hsmall : 2*bad.card ≤ T := by exact_mod_cast (show 2*(bad.card:ℝ) ≤ T by linarith)
  have hpart := card_filter_add_card_filter_not (s := range T) (fun t => excess (progression P t)<1/144)
  change _ + bad.card = _ at hpart
  rw [card_range] at hpart
  omega

include Ppos Pdiv in
private lemma density : ∃ c : ℝ, 0 < c ∧ ∀ᶠ b : ℕ in atTop,
    c ≤ {n : ℕ | n.Weird}.partialDensity Set.univ b := by
  classical
  let D := 140*P
  have hp := Ppos
  have hD : 0 < D := Nat.mul_pos (by decide) hp
  have hdt : Tendsto (fun b : ℕ => b/D) atTop atTop := Nat.tendsto_div_const_atTop hD.ne'
  refine ⟨1/(4*(D:ℝ)),by positivity,?_⟩
  filter_upwards [hdt.eventually (many P Ppos Pdiv),hdt.eventually_ge_atTop 1,eventually_ge_atTop 1] with b hb hT hb1
  let T := b/D
  let G := (range T).filter (fun t => excess (progression P t) < 1/144)
  change T ≤ 2*G.card at hb
  change 1 ≤ T at hT
  have hfits : T*D ≤ b := Nat.div_mul_le_self b D
  have hbT : b ≤ 2*T*D := by
    have hh : b < (T+1)*D := by simpa only [T,mul_comm] using Nat.lt_mul_div_succ b hD
    nlinarith [Nat.mul_le_mul_right D hT]
  let g (t : ℕ) := progression P t * 70
  have hinj : Function.Injective g := by
    intro t u he
    have h := Nat.eq_of_mul_eq_mul_right (by decide : 0 < 70) he
    apply Nat.eq_of_mul_eq_mul_left hp
    exact Nat.add_right_cancel (show P*t+1 = P*u+1 from h)
  have hsub : (G.image g : Set ℕ) ⊆ {n : ℕ | n.Weird} ∩ Set.Iio b := by
    intro n hn
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hn
    obtain ⟨ht0,he⟩ := mem_filter.mp ht
    have ht1 := mem_range.mp ht0
    have hc70 := (cop P t).coprime_dvd_right (Pdiv (by decide : 0 < 70) (by decide))
    have ht2 := Nat.mul_le_mul_left P (Nat.succ_le_of_lt ht1)
    refine ⟨multiply (Nat.succ_pos _) hc70 he,?_⟩
    change (P*t+1)*70 < b
    dsimp [D] at hfits
    nlinarith
  have hc : G.card ≤ ({n : ℕ | n.Weird} ∩ Set.Iio b).ncard := by
    have h := Set.ncard_le_ncard hsub ((Set.finite_Iio b).subset Set.inter_subset_right)
    rw [Set.ncard_coe_finset, card_image_of_injective _ hinj] at h
    exact h
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Set.ncard_Iio_nat]
  apply (le_div_iff₀ (by exact_mod_cast (show 0 < b by omega))).mpr
  rw [one_div,inv_mul_eq_div]
  apply (div_le_iff₀ (by positivity)).mpr
  have hh : b ≤ ({n : ℕ | n.Weird} ∩ Set.Iio b).ncard*(4*D) := by
    nlinarith [Nat.mul_le_mul_right D (hb.trans (Nat.mul_le_mul_left 2 hc))]
  exact_mod_cast hh

end
end Weird470

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1.H4 := Weird470.density (Nat.factorial 1000) (Nat.factorial_pos _) (fun hd h => Nat.dvd_factorial hd h)
