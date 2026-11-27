import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1
import Mathlib

/-! Credit: @marcusbuffett. The second moment splits into a finite variance bound
for distinct residue classes and a numerical estimate for the reciprocal prime sum.
The cube weights, separations and progression modulus are handled explicitly below. -/

namespace OMA.R_Erdos69_erdos_69_R1_H1_R1_H3_R1
open Finset Filter
open scoped Classical
open OMA.R_Erdos69_erdos_69_R1_H1_R1 (geom_one geom_two sign_sum)

/-- Finite variance estimate. Different primes impose independent congruences up to
a bounded rounding error. At a single prime the distinct shifts are disjoint. -/
def H1 : Prop :=
  ∀ (L U Q b : ℕ) (S : Finset (Finset ℕ × ℕ)) (P : Finset ℕ)
    (r : Finset ℕ × ℕ → ℤ) (w : Finset ℕ × ℕ → ℝ),
    0 < Q → (∀ p ∈ P, p.Prime ∧ ¬p ∣ Q) →
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ p ∈ P, ¬(p:ℤ) ∣ r i-r j) →
    (∑ i ∈ S, w i) = 0 →
    let N := (Icc L U).filter (fun n => n%Q=b%Q)
    ∑ n ∈ N, (∑ i ∈ S, w i * ((P.filter fun (p : ℕ) => (p:ℤ) ∣ (n:ℤ)+r i).card:ℝ))^2 ≤
      (N.card:ℝ)*(∑ i ∈ S, (w i)^2)*(∑ p ∈ P, (1:ℝ)/p) +
      4*((P.card:ℝ)*(∑ i ∈ S, |w i|))^2

/-- The reciprocal prime sum and the two-prime rounding error fit the specified
error budget, uniformly in the residue class and in the upper endpoint. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ x : ℕ in atTop,
    let l := Real.log (Real.log (Real.log x))
    let K := ⌊2*Real.log l / Real.log 2⌋₊
    let D := Real.exp (4*l^11)
    let R := (x:ℝ)^(1/Real.log (Real.log x)^2)
    100 ≤ l ∧ 0 < K ∧ (2:ℝ)^K ≤ l^2 ∧ 2*D < R ∧ D < (x/2:ℕ) ∧
    ∀ y : ℝ, y ≤ (x:ℝ)^(1/50:ℝ) → ∀ Q b : ℕ, 0 < Q → (Q:ℝ) ≤ D →
      let N := (Icc (x/2) x).filter fun n => n%Q=b%Q
      let P : Finset ℕ := (range (⌊y⌋₊+1)).filter fun (p : ℕ) => p.Prime ∧ R < p ∧ (p:ℝ) ≤ y
      (N.card:ℝ)*(1/(3*2^K))*(∑ p ∈ P, (1:ℝ)/p) + 4*(P.card:ℝ)^2 ≤ η*N.card


lemma finite_bounds (l : ℝ) (hl : 100 ≤ l) (K H : ℕ)
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



lemma weights (K H : ℕ) (hk : 0<K) :
    let S := (range K).powerset ×ˢ Ico (K+1) (K+H+1)
    let w (a : Finset ℕ × ℕ) := (-1:ℝ)^a.1.card/2^a.2
    (∑ i ∈ S, w i) = 0 ∧ (∑ i ∈ S, |w i|) ≤ 1 ∧
      (∑ i ∈ S, (w i)^2) ≤ 1/(3*2^K) := by
  classical
  dsimp only
  simp only [sum_product]
  constructor
  · rw [sum_comm]
    apply sum_eq_zero
    intro h _
    rw [← sum_div,sign_sum K hk,zero_div]
  constructor
  · rw [sum_comm]
    simp only [abs_div,abs_pow,abs_neg,abs_one,one_pow,abs_of_pos (by norm_num : (0:ℝ)<2)]
    simp only [sum_const,card_powerset,card_range,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_one_div]
    rw [geom_one]
    linarith [show (0:ℝ) ≤ 1/2^H by positivity]
  · rw [sum_comm]
    simp only [div_pow,← pow_mul,show ∀ c : ℕ, (-1:ℝ)^(c*2)=1 by
      intro c; rw [mul_comm,pow_mul]; norm_num]
    simp only [sum_const,card_powerset,card_range,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_one_div]
    simp_rw [pow_mul (2:ℝ) _ 2]
    rw [geom_two]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [show (0:ℝ) ≤ 1/(2^H:ℝ)^2 by positivity]

set_option maxHeartbeats 1200000 in
theorem main : H1 → H2 → OMA.R_Erdos69_erdos_69_R1_H1_R1.H3 := by
  classical
  intro variance numeric η hη
  apply eventually_atTop.mp
  filter_upwards [numeric η hη] with x hx
  let l := Real.log (Real.log (Real.log x))
  let D := Real.exp (4*l^11)
  let R := (x:ℝ) ^ (1/Real.log (Real.log x)^2)
  intro y hy K H Q b p s
  dsimp only
  intro hK hH hs hi hW hQ _
  obtain ⟨hl,hKpos,hC,hDR,hDx,small⟩ := hx
  rw [← hK] at hKpos hC small
  let C := (range K).powerset
  let S := C ×ˢ Ico (K+1) (K+H+1)
  let N := (Icc (x/2) x).filter fun n => n%Q=b%Q
  let P : Finset ℕ := (range (⌊y⌋₊+1)).filter fun (q : ℕ) => q.Prime ∧ R < q ∧ (q:ℝ) ≤ y
  let r (a : Finset ℕ × ℕ) : ℤ := (p a.1:ℤ)*a.2 - s a.1
  let w (a : Finset ℕ × ℕ) := (-1:ℝ)^a.1.card/2^a.2
  have hQp : 0 < Q := by
    rw [hQ]
    exact Nat.mul_pos (prod_pos fun E he => (hs E he).1.pos)
      (prod_pos fun q hq => pow_pos (Nat.pos_of_mem_primeFactors (mem_sdiff.mp hq).1) _)
  have hKsmall : (K:ℝ) ≤ l^2 := le_trans (by exact_mod_cast K.lt_two_pow_self.le) hC
  obtain ⟨hQD,_,hshift⟩ := finite_bounds l hl K H hC hKsmall
    (show (H:ℝ) ≤ l^2 from hH ▸ Nat.floor_le (sq_nonneg l))
    p s (fun E he => ⟨(hs E he).2.2.1,(hs E he).2.2.2.1⟩) hW
  rw [← hQ] at hQD
  have locQ (q : ℕ) (hq : q ∈ P) : q.Prime ∧ ¬q ∣ Q := by
    obtain ⟨hp,hr,_⟩ := (mem_filter.mp hq).2
    refine ⟨hp,fun hd => ?_⟩
    have hle : (q:ℝ) ≤ Q := by exact_mod_cast Nat.le_of_dvd hQp hd
    have := Real.exp_pos (4*l^11)
    change 2*D < R at hDR
    change (Q:ℝ) ≤ D at hQD
    dsimp only [D] at *
    linarith
  have locDiff (i) (hiS : i ∈ S) (j) (hjS : j ∈ S) (hne : i≠j) (q : ℕ) (hq : q ∈ P) :
      ¬(q:ℤ) ∣ r i-r j := by
    have hne' : (r i-r j).natAbs ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hW) (i,j) (mem_offDiag.mpr ⟨hiS,hjS,hne⟩)
    intro hd
    have hle : (q:ℝ) ≤ (r i-r j).natAbs := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hne') (Int.natCast_dvd.mp hd)
    rw [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub] at hle
    have hu := (abs_sub (r i:ℝ) (r j:ℝ)).trans (add_le_add (hshift i hiS) (hshift j hjS))
    change |(r i:ℝ)-(r j:ℝ)| ≤ D+D at hu
    change 2*D < R at hDR
    have hR := (mem_filter.mp hq).2.2.1
    linarith
  have count (n) (hn : n ∈ N) (i) (hiS : i ∈ S) :
      ((n:ℤ)+r i).natAbs.primeFactors.filter (fun q : ℕ => R < q ∧ (q:ℝ) ≤ y) =
      P.filter fun (q : ℕ) => (q:ℤ) ∣ (n:ℤ)+r i := by
    have hn' : ((x/2:ℕ):ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).1
    have hr : |(r i:ℝ)| ≤ D := hshift i hiS
    have hpos : 0 < (n:ℝ)+(r i:ℝ) := by
      change D < ((x/2:ℕ):ℝ) at hDx
      linarith [neg_abs_le (r i:ℝ)]
    have hne : ((n:ℤ)+r i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr
      (show (n:ℤ)+r i ≠ 0 by exact_mod_cast hpos.ne')
    ext q
    simp only [P,mem_filter,mem_range,Nat.mem_primeFactors,Int.natCast_dvd]
    constructor
    · rintro ⟨⟨hq,hd,_⟩,hR,hyq⟩
      exact ⟨⟨Nat.lt_succ_of_le (Nat.le_floor hyq),hq,hR,hyq⟩,hd⟩
    · rintro ⟨⟨_,hq,hR,hyq⟩,hd⟩
      exact ⟨⟨hq,hd,hne⟩,hR,hyq⟩
  obtain ⟨hz,hw,hw2⟩ := weights K H hKpos
  have hv := variance (x/2) x Q b S P r w hQp locQ locDiff hz
  have hm := small y hy Q b hQp hQD
  calc
    _ = ∑ n ∈ N, (∑ i ∈ S, w i * ((P.filter fun (q : ℕ) => (q:ℤ) ∣ (n:ℤ)+r i).card:ℝ))^2 := by
      apply sum_congr rfl
      intro n hn
      congr 1
      apply sum_congr rfl
      intro i hiS
      change w i * (((((n:ℤ)+r i).natAbs.primeFactors.filter _).card:ℕ):ℝ) = _
      rw [count n hn i hiS]
    _ ≤ _ := hv
    _ ≤ (N.card:ℝ)*(1/(3*2^K))*(∑ q ∈ P, (1:ℝ)/q) + 4*(P.card:ℝ)^2 := by
      apply add_le_add
      · gcongr
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by positivity)
        simpa using (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg P.card))
    _ ≤ _ := hm

end OMA.R_Erdos69_erdos_69_R1_H1_R1_H3_R1
