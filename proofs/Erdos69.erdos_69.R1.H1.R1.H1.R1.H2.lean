import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1_H1_R1
import Mathlib

/-! Credit: @marcusbuffett. Bounding each discriminant factor and then the number of factors gives a polynomial in the triple logarithm for the logarithm of the modulus. -/

namespace CubeScope69
open Finset Filter
open scoped Topology

private lemma finite_bounds (l : ℝ) (hl : 100 ≤ l) (K H : ℕ)
    (hC : (2:ℝ)^K ≤ l^2) (hK : (K:ℝ) ≤ l^2) (hH : (H:ℝ) ≤ l^2)
    (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ)
    (hp : ∀ E ∈ (range K).powerset, (p E:ℝ) ≤ Real.exp (l^3) ∧
      |s E| ≤ 8*(K:ℤ)^2*p E) :
    let C := (range K).powerset
    let S := C ×ˢ Ico (K+1) (K+H+1)
    let r (a : Finset ℕ × ℕ) : ℤ := (p a.1:ℤ)*a.2-s a.1
    let W := ∏ a ∈ S.offDiag, (r a.1-r a.2).natAbs
    W ≠ 0 →
      (((∏ E ∈ C, p E) * (∏ q ∈ W.primeFactors \ C.image p, q^W.factorization q) : ℕ):ℝ) ≤
        Real.exp (4*l^11) ∧
      (∀ E ∈ C, |(s E:ℝ)| ≤ Real.exp (4*l^11)) ∧
      ∀ a ∈ S, |(r a:ℝ)| ≤ Real.exp (4*l^11) := by
  classical
  intro C S r W hW
  have hl0 : 0 ≤ l := by linarith
  have grow {i j : ℕ} (hij : i ≤ j) : l^i ≤ l^j := pow_le_pow_right₀ (by linarith) hij
  have hP := Real.pow_div_factorial_le_exp (l^3) (pow_nonneg hl0 3) 2
  norm_num at hP
  have hl4 : 100*l^4 ≤ l^6 := by
    have hl2 : 100 ≤ l^2 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hl2 (pow_nonneg hl0 4)]
  have hlocal : 2*l^2+8*l^4 ≤ Real.exp (l^3) := by
    nlinarith only [hP,hl4,grow (i:=2) (j:=4) (by decide),pow_nonneg hl0 4]
  have h2P : 2 ≤ Real.exp (l^3) := by
    nlinarith [Real.add_one_le_exp (l^3),grow (i:=1) (j:=3) (by decide)]
  have hK2 : (K:ℝ)^2 ≤ l^4 := by
    calc
      _ ≤ (l^2)^2 := pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
      _ = _ := by ring
  have hss (E) (he : E ∈ C) : |(s E:ℝ)| ≤ (8*l^4)*Real.exp (l^3) := by
    have orig : |(s E:ℝ)| ≤ 8*(K:ℝ)^2*(p E:ℝ) := by exact_mod_cast (hp E he).2
    exact orig.trans (mul_le_mul (by linarith : 8*(K:ℝ)^2 ≤ 8*l^4) (hp E he).1
      (Nat.cast_nonneg _) (by positivity))
  have hr (a) (ha : a ∈ S) : |(r a:ℝ)| ≤ Real.exp (2*l^3) := by
    obtain ⟨he,hh⟩ := mem_product.mp ha
    have hval : (a.2:ℝ) ≤ 2*l^2 := by
      have ha' : a.2 ≤ K+H := by have := (mem_Ico.mp hh).2; omega
      have h' : (a.2:ℝ) ≤ K+(H:ℝ) := by exact_mod_cast ha'
      linarith
    have hv := mul_le_mul hval (hp a.1 he).1 (Nat.cast_nonneg _) (by positivity)
    change |(((p a.1:ℤ)*(a.2:ℤ)-s a.1:ℤ):ℝ)| ≤ _
    push_cast
    calc
      _ ≤ |(p a.1:ℝ)*a.2| + |(s a.1:ℝ)| := abs_sub _ _
      _ ≤ (2*l^2+8*l^4)*Real.exp (l^3) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ (p a.1:ℝ)*a.2)]
        nlinarith only [hv,hss a.1 he]
      _ ≤ Real.exp (l^3)*Real.exp (l^3) :=
        mul_le_mul_of_nonneg_right hlocal (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hc : (C.card:ℝ) ≤ l^2 := by simpa [C] using hC
  have hS : (S.card:ℝ) ≤ l^4 := by
    have z : S.card = C.card * H := by simp [S]
    rw [z,Nat.cast_mul]
    calc
      _ ≤ l^2*l^2 := mul_le_mul hc hH (Nat.cast_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hoff : (S.offDiag.card:ℝ) ≤ l^8 := by
    have hsub : S.offDiag ⊆ S ×ˢ S := fun a ha =>
      mem_product.mpr ⟨(mem_offDiag.mp ha).1,(mem_offDiag.mp ha).2.1⟩
    have h' : S.offDiag.card ≤ S.card*S.card := by simpa using card_le_card hsub
    have hh : (S.offDiag.card:ℝ) ≤ (S.card:ℝ)*S.card := by exact_mod_cast h'
    calc
      _ ≤ _ := hh
      _ ≤ l^4*l^4 := mul_le_mul hS hS (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hWle : (W:ℝ) ≤ Real.exp (3*l^11) := by
    dsimp only [W]
    push_cast
    calc
      _ ≤ ∏ _ ∈ S.offDiag, Real.exp (3*l^3) := by
        apply Finset.prod_le_prod
        · intros; positivity
        · intro a ha
          obtain ⟨h1,h2,_⟩ := mem_offDiag.mp ha
          have h' : |(r a.1:ℝ)-(r a.2:ℝ)| ≤ Real.exp (2*l^3)+Real.exp (2*l^3) :=
            (abs_sub _ _).trans (add_le_add (hr _ h1) (hr _ h2))
          have he : Real.exp (3*l^3) = Real.exp (l^3)*Real.exp (2*l^3) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [he]
          have := mul_le_mul_of_nonneg_right h2P (Real.exp_pos (2*l^3)).le
          simp only [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub] 
          linarith
      _ = Real.exp ((S.offDiag.card:ℝ)*(3*l^3)) := by simp [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith only [mul_le_mul_of_nonneg_right hoff (show 0 ≤ 3*l^3 by positivity)])
  have hPle : ((∏ E ∈ C, p E : ℕ):ℝ) ≤ Real.exp (l^11) := by
    push_cast
    calc
      _ ≤ ∏ _ ∈ C, Real.exp (l^3) := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun E he => (hp E he).1)
      _ = Real.exp ((C.card:ℝ)*l^3) := by simp [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith only [mul_le_mul_of_nonneg_right hc (pow_nonneg hl0 3),grow (i:=5) (j:=11) (by decide)])
  have hD : (∏ q ∈ W.primeFactors \ C.image p, q ^ W.factorization q) ≤ W := by
    apply Nat.le_of_dvd (Nat.pos_of_ne_zero hW)
    conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hW]
    exact prod_dvd_prod_of_subset _ _ _ sdiff_subset
  have hex : Real.exp (2*l^3) ≤ Real.exp (4*l^11) := Real.exp_le_exp.mpr (by
    nlinarith [grow (i:=3) (j:=11) (by decide),pow_nonneg hl0 11])
  refine ⟨?_,?_,fun a ha => (hr a ha).trans hex⟩
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (l^11) * Real.exp (3*l^11) := mul_le_mul hPle
        (le_trans (by exact_mod_cast hD) hWle) (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · intro E he
    apply (hss E he).trans
    apply le_trans _ hex
    rw [show 2*l^3 = l^3+l^3 by ring,Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    linarith [sq_nonneg l]


theorem envelope : ∀ η : ℝ, 0 < η → ∀ᶠ x : ℕ in atTop,
    let l := Real.log (Real.log (Real.log x))
    let B := Real.exp (Real.sqrt (Real.log (Real.log x)))
    let K := ⌊2 * Real.log l / Real.log 2⌋₊
    let H := ⌊l^2⌋₊
    let C := (range K).powerset
    ∀ (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ),
      (∀ E ∈ C, (p E:ℝ) ≤ Real.exp (l^3) ∧ |s E| ≤ 8*(K:ℤ)^2*p E) →
      let W := (∏ a ∈ ((range K).powerset ×ˢ Ico (K+1) (K+H+1)).offDiag, (((p a.1.1:ℤ)*(a.1.2:ℤ)-s a.1.1)-((p a.2.1:ℤ)*(a.2.2:ℤ)-s a.2.1)).natAbs)
      W ≠ 0 → 1/2^K ≤ η ∧
      (((∏ E ∈ C, p E) * (∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ) : ℕ):ℝ) ≤ B ∧
      (∀ E ∈ C, |(s E:ℝ)| ≤ B) ∧
      ∀ a ∈ ((range K).powerset ×ˢ Ico (K+1) (K+H+1)), |(((p a.1:ℤ)*(a.2:ℤ)-s a.1:ℤ):ℝ)| ≤ B := by
  classical
  intro η hη
  let L (x : ℕ) := Real.log (Real.log (Real.log x))
  have hll : Tendsto (fun x : ℕ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have ht : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hll
  filter_upwards [ht.eventually_ge_atTop 100,ht.eventually_ge_atTop (4/η),
    ht.eventually_ge_atTop (4*2^12*(Nat.factorial 12:ℝ)),hll.eventually_gt_atTop 0]
    with x hl hηl hbig hloglog
  let l := L x
  let K := ⌊2*Real.log l / Real.log 2⌋₊
  let H := ⌊l^2⌋₊
  change 100 ≤ l at hl
  change 4/η ≤ l at hηl
  change 4*2^12*(Nat.factorial 12:ℝ) ≤ l at hbig
  have lpos : 0<l := by linarith
  have log2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have logl := Real.log_nonneg (by linarith : 1≤l)
  have floorK : (K:ℝ) ≤ 2*Real.log l / Real.log 2 := Nat.floor_le (by positivity)
  have floorK' : 2*Real.log l / Real.log 2 < (K:ℝ)+1 := Nat.lt_floor_add_one _
  have eq : Real.exp (2*Real.log l) = l^2 := by
    rw [show 2*Real.log l=Real.log l+Real.log l by ring,Real.exp_add,Real.exp_log lpos]; ring
  have eqK : Real.exp ((K:ℝ)*Real.log 2) = (2:ℝ)^K := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have hC : (2:ℝ)^K ≤ l^2 := by
    rw [←eqK,←eq,Real.exp_le_exp]
    exact (le_div_iff₀ log2).mp floorK
  have hC' : l^2 < (2:ℝ)^K*2 := by
    have h := Real.exp_lt_exp.mpr ((div_lt_iff₀ log2).mp floorK')
    rwa [add_mul,one_mul,Real.exp_add,eq,eqK,Real.exp_log (by norm_num : (0:ℝ)<2)] at h
  have hK : (K:ℝ) ≤ l^2 :=
    le_trans (by exact_mod_cast K.lt_two_pow_self.le) hC
  have hH : (H:ℝ) ≤ l^2 := Nat.floor_le (sq_nonneg _)
  have hηK : 1/(2:ℝ)^K ≤ η := by
    apply (div_le_iff₀ (by positivity)).2
    have ηl := (div_le_iff₀ hη).mp hηl
    have lsq : l ≤ l^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (lsq.trans hC'.le) hη.le]
  have hge : 4*l^11 ≤ Real.sqrt (Real.log (Real.log x)) := by
    have hb := mul_le_mul_of_nonneg_right hbig (pow_nonneg lpos.le 11)
    have he := Real.pow_div_factorial_le_exp (l/2) (show 0≤l/2 by linarith) 12
    have e : Real.exp (l/2) = Real.sqrt (Real.log (Real.log x)) := by
      rw [Real.exp_half,show l = Real.log (Real.log (Real.log x)) by rfl,Real.exp_log hloglog]
    rw [←e]
    apply le_trans _ he
    apply (le_div_iff₀ (by positivity)).2
    rw [div_pow]
    apply (le_div_iff₀ (by norm_num : 0 < (2:ℝ)^12)).2
    nlinarith only [hb]
  dsimp only
  intro p s hp hW
  obtain ⟨bound,sb,rb⟩ := finite_bounds l hl K H hC hK hH p s hp hW
  exact ⟨hηK,bound.trans (Real.exp_le_exp.mpr hge),
    fun E he => (sb E he).trans (Real.exp_le_exp.mpr hge),
    fun a ha => (rb a ha).trans (Real.exp_le_exp.mpr hge)⟩

end CubeScope69

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1_H1_R1.H2 := CubeScope69.envelope
