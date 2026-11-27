import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1
import Mathlib

/-! The full second-moment bound combines the finite covariance estimate with the Mertens-window estimate.

Credit: @marcusbuffett. The second moment splits into a finite variance bound
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

section

/-! Credit: @marcusbuffett. Count one or two congruences over an interval by complete periods, then sum covariances. The zero-sum weights cancel each pair of distinct primes. -/

namespace FiniteSieve69
open Finset
open scoped Classical

private def blockPrefix (n m r : ℕ) := (range n).filter fun i => i%m=r

private lemma full_blocks (k m r : ℕ) (hm : 0 < m) (hr : r < m) :
    (blockPrefix (k*m) m r).card = k := by
  have eq : blockPrefix (k*m) m r = (range k).image (fun t => t*m+r) := by
    ext i
    simp only [blockPrefix,mem_filter,mem_range,mem_image]
    constructor
    · rintro ⟨hi,he⟩
      exact ⟨i/m,(Nat.div_lt_iff_lt_mul hm).2 hi, by
        rw [←he,Nat.mul_comm]; exact Nat.div_add_mod i m⟩
    · rintro ⟨t,ht,rfl⟩
      constructor
      · calc
          _ < t*m+m := Nat.add_lt_add_left hr _
          _ = (t+1)*m := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ ht
      · simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
  rw [eq,card_image_of_injective,card_range]
  intro u v he
  exact Nat.eq_of_mul_eq_mul_right hm (Nat.add_right_cancel he)

private lemma prefix_error (n m r : ℕ) (hm : 0 < m) (hr : r < m) :
    |((blockPrefix n m r).card:ℝ)-(n:ℝ)/m| ≤ 1 := by
  have mono {a b : ℕ} (h : a ≤ b) : blockPrefix a m r ⊆ blockPrefix b m r :=
    filter_subset_filter _ (range_mono h)
  have l := card_le_card (mono (Nat.div_mul_le_self n m))
  have u := card_le_card (mono (a:=n) (b:=(n/m+1)*m) (by
    exact ((Nat.div_lt_iff_lt_mul hm).1 (Nat.lt_succ_self (n/m))).le))
  rw [full_blocks _ _ _ hm hr] at l u
  have l' : ((n/m:ℕ):ℝ) ≤ (blockPrefix n m r).card := by exact_mod_cast l
  have u' : ((blockPrefix n m r).card:ℝ) ≤ (n/m:ℕ)+1 := by exact_mod_cast u
  have dl : ((n/m:ℕ):ℝ)*(m:ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n m
  have du : (n:ℝ) < (((n/m:ℕ):ℝ)+1)*m := by
    exact_mod_cast ((Nat.div_lt_iff_lt_mul hm).1 (Nat.lt_succ_self (n/m)))
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have lo := (le_div_iff₀ mp).2 dl
  have up := (div_lt_iff₀ mp).2 du
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private def interval (L U m r : ℕ) := (Icc L U).filter fun i => i%m=r%m

private lemma interval_error (L U m r : ℕ) (hm : 0 < m) :
    |((interval L U m r).card:ℝ)-((U+1-L:ℕ):ℝ)/m| ≤ 2 := by
  by_cases h : L ≤ U+1
  · have hsub : blockPrefix L m (r%m) ⊆ blockPrefix (U+1) m (r%m) :=
      filter_subset_filter _ (range_mono h)
    have e : interval L U m r = blockPrefix (U+1) m (r%m) \ blockPrefix L m (r%m) := by
      ext i
      simp only [interval,blockPrefix,mem_sdiff,mem_filter,mem_Icc,mem_range]
      omega
    rw [e,card_sdiff_of_subset hsub,Nat.cast_sub (card_le_card hsub),Nat.cast_sub h,Nat.cast_add_one]
    have h1 := abs_le.mp (prefix_error (U+1) m (r%m) hm (Nat.mod_lt _ hm))
    have h2 := abs_le.mp (prefix_error L m (r%m) hm (Nat.mod_lt _ hm))
    push_cast at h1
    rw [sub_div]
    exact abs_le.mpr ⟨by linarith [h1.1,h2.2],by linarith [h1.2,h2.1]⟩
  · have h' : U<L := by omega
    simp [interval,Finset.Icc_eq_empty_of_lt h',Nat.sub_eq_zero_of_le (by omega : U+1≤L)]

private lemma class_error (L U Q b m r : ℕ) (hQ : 0<Q) (hm : 0 < m) (co : Q.Coprime m) :
    |(((interval L U Q b).filter (fun i => i%m=r%m)).card:ℝ) -
      ((interval L U Q b).card:ℝ)/m| ≤ 4 := by
  let c := Nat.chineseRemainder co b r
  have e : (interval L U Q b).filter (fun i => i%m=r%m) = interval L U (Q*m) c.val := by
    ext i
    simp only [interval,mem_filter,mem_Icc]
    change ((_ ∧ i ≡ b [MOD Q]) ∧ i ≡ r [MOD m]) ↔ _ ∧ i ≡ c.val [MOD Q*m]
    rw [← Nat.modEq_and_modEq_iff_modEq_mul co]
    constructor
    · rintro ⟨⟨a,hb⟩,hr⟩
      exact ⟨a,hb.trans c.prop.1.symm,hr.trans c.prop.2.symm⟩
    · rintro ⟨a,hb,hr⟩
      exact ⟨⟨a,hb.trans c.prop.1⟩,hr.trans c.prop.2⟩
  rw [e]
  have h1 := interval_error L U (Q*m) c.val (Nat.mul_pos hQ hm)
  have h2 := interval_error L U Q b hQ
  have m1 : 1≤(m:ℝ) := by exact_mod_cast hm
  have h2' : |(((interval L U Q b).card:ℝ)-((U+1-L:ℕ):ℝ)/Q)/m| ≤ 2 := by
    rw [abs_div,abs_of_pos (by positivity : (0:ℝ) < m)]
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  rw [sub_div,div_div] at h2'
  rw [Nat.cast_mul] at h1
  obtain ⟨h1l,h1u⟩ := abs_le.mp h1
  obtain ⟨h2l,h2u⟩ := abs_le.mp h2'
  exact abs_le.mpr ⟨by linarith,by linarith⟩


private def residue (q : ℕ) (z : ℤ) := ((-z : ℤ) : ZMod q).val

private lemma residue_iff {q n : ℕ} (hq : q ≠ 0) (z : ℤ) :
    (q:ℤ) ∣ (n:ℤ)+z ↔ n ≡ residue q z [MOD q] := by
  letI : NeZero q := ⟨hq⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.natCast_eq_natCast_iff]
  simp [residue,ZMod.natCast_zmod_val,eq_neg_iff_add_eq_zero]

private lemma pair_error (L U Q b : ℕ) (hQ : 0<Q) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpQ : ¬p ∣ Q) (hqQ : ¬q ∣ Q)
    (u v : ℤ) (distinct : p=q → u≠v → ¬(p:ℤ) ∣ u-v) :
    let N := interval L U Q b
    let S := N.filter fun (n : ℕ) => (p:ℤ) ∣ (n:ℤ)+u ∧ (q:ℤ) ∣ (n:ℤ)+v
    |(S.card:ℝ)-N.card*(if p=q then (if u=v then 1/(p:ℝ) else 0)
       else 1/((p:ℝ)*q))| ≤ 4 := by
  intro N S
  by_cases e : p=q
  · subst q
    rw [if_pos rfl]
    by_cases f : u=v
    · subst v
      rw [if_pos rfl]
      have he : S = N.filter (fun n => n%p=(residue p u)%p) := by
        ext n
        simp only [S,mem_filter,and_self,residue_iff hp.ne_zero]
        rfl
      rw [he,mul_one_div]
      exact class_error L U Q b p (residue p u) hQ hp.pos (hp.coprime_iff_not_dvd.mpr hpQ).symm
    · have he : S = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨hu,hv⟩ := (mem_filter.mp hn).2
        have d := Int.dvd_sub hu hv
        rw [show (n:ℤ)+u-((n:ℤ)+v)=u-v by ring] at d
        exact distinct rfl f d
      simp [he,f]
  · rw [if_neg e]
    have co := (Nat.coprime_primes hp hq).mpr e
    let c := Nat.chineseRemainder co (residue p u) (residue q v)
    have he : S = N.filter (fun n => n%(p*q)=c.val%(p*q)) := by
      ext n
      simp only [S,mem_filter,residue_iff hp.ne_zero,residue_iff hq.ne_zero]
      change _ ∧ _ ↔ _ ∧ n ≡ c.val [MOD p*q]
      rw [← Nat.modEq_and_modEq_iff_modEq_mul co]
      exact and_congr_right fun _ => ⟨fun h => ⟨h.1.trans c.prop.1.symm,h.2.trans c.prop.2.symm⟩,
        fun h => ⟨h.1.trans c.prop.1,h.2.trans c.prop.2⟩⟩
    rw [he,mul_one_div]
    have H := class_error L U Q b (p*q) c.val hQ (Nat.mul_pos hp.pos hq.pos)
      ((hp.coprime_iff_not_dvd.mpr hpQ).symm.mul_right (hq.coprime_iff_not_dvd.mpr hqQ).symm)
    simpa using H



private lemma moments {α : Type} [DecidableEq α] (A : Finset α) (N : Finset ℕ)
    (c : α → ℝ) (g : α → ℕ → Prop) [∀ a,DecidablePred (g a)] :
    ∑ n ∈ N, (∑ a ∈ A, if g a n then c a else 0)^2 =
      ∑ a ∈ A, ∑ b ∈ A, (c a*c b) * ((N.filter fun n => g a n ∧ g b n).card:ℝ) := by
  classical
  calc
    _ = ∑ n ∈ N, ∑ a ∈ A, ∑ b ∈ A,
          (if g a n then c a else 0)*(if g b n then c b else 0) := by
      simp only [pow_two,sum_mul,mul_sum]
      simp only [mul_comm]
    _ = ∑ a ∈ A, ∑ b ∈ A, ∑ n ∈ N,
          (if g a n then c a else 0)*(if g b n then c b else 0) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      calc
        _ = ∑ n ∈ N, if g a n ∧ g b n then c a*c b else 0 := by
          apply sum_congr rfl
          intro n _
          by_cases ha : g a n <;> by_cases hb : g b n <;> simp [ha,hb]
        _ = _ := by rw [← sum_filter]; simp [mul_comm]

private noncomputable def mean {α : Type} [DecidableEq α] (a b : ℕ × α) : ℝ :=
  if a.1=b.1 then (if a.2=b.2 then 1/(a.1:ℝ) else 0) else 1/((a.1:ℝ)*b.1)

private lemma mean_sum {α : Type} [DecidableEq α] (S : Finset α) (P : Finset ℕ) (w : α → ℝ)
    (hz : ∑ i ∈ S, w i = 0) :
    ∑ a ∈ P ×ˢ S, ∑ b ∈ P ×ˢ S, w a.2*w b.2 * mean a b =
       (∑ i ∈ S, (w i)^2)*(∑ p ∈ P, (1:ℝ)/p) := by
  classical
  simp only [sum_product]
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  rw [sum_eq_single p]
  · apply Eq.trans _ (sum_mul ..).symm
    apply sum_congr rfl
    intro i hi
    rw [sum_eq_single i]
    · simp [mean,pow_two]
    · intro j hj hji
      simp [mean,Ne.symm hji]
    · exact fun h => (h hi).elim
  · intro q hq hqp
    apply sum_eq_zero
    intro i hi
    simp only [mean,if_neg hqp.symm]
    calc
      _ = (w i*(1/((p:ℝ)*q)))*∑ j ∈ S, w j := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ = 0 := by rw [hz,mul_zero]
  · exact fun h => (h hp).elim

theorem variance (L U Q b : ℕ) (S : Finset (Finset ℕ × ℕ)) (P : Finset ℕ)
    (r : Finset ℕ × ℕ → ℤ) (w : Finset ℕ × ℕ → ℝ)
    (hQ : 0<Q) (hP : ∀ p ∈ P, p.Prime ∧ ¬p ∣ Q)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ p ∈ P, ¬(p:ℤ) ∣ r i-r j)
    (hz : ∑ i ∈ S, w i = 0) :
    let N := (Icc L U).filter (fun n => n%Q=b%Q)
    ∑ n ∈ N, (∑ i ∈ S, w i * ((P.filter fun (p:ℕ) => (p:ℤ) ∣ (n:ℤ)+r i).card:ℝ))^2 ≤
      (N.card:ℝ)*(∑ i ∈ S, (w i)^2)*(∑ p ∈ P, (1:ℝ)/p) +
      4*((P.card:ℝ)*(∑ i ∈ S, |w i|))^2 := by
  classical
  intro N
  let A := P ×ˢ S
  let g (a : ℕ × (Finset ℕ × ℕ)) (n : ℕ) := (a.1:ℤ) ∣ (n:ℤ)+r a.2
  let c (a : ℕ × (Finset ℕ × ℕ)) := w a.2
  have e (n : ℕ) :
      ∑ i ∈ S, w i * ((P.filter fun (p:ℕ) => (p:ℤ) ∣ (n:ℤ)+r i).card:ℝ) =
        ∑ a ∈ A, if g a n then c a else 0 := by
    rw [show A = P ×ˢ S by rfl,sum_product,sum_comm]
    apply sum_congr rfl
    intro i _
    dsimp only [g,c]
    rw [←sum_filter]
    simp [mul_comm]
  let cnt (a b : ℕ × (Finset ℕ × ℕ)) : ℝ := (N.filter fun n => g a n ∧ g b n).card
  have point (a) (ha : a ∈ A) (v) (hv : v ∈ A) :
      (c a*c v)*cnt a v ≤ (N.card:ℝ)*(c a*c v*mean a v)+4*(|c a| * |c v|) := by
    obtain ⟨pa,si⟩ := mem_product.mp ha
    obtain ⟨pv,sj⟩ := mem_product.mp hv
    have hne : r a.2 = r v.2 ↔ a.2 = v.2 := by
      constructor
      · intro he
        by_contra ij
        exact hd a.2 si v.2 sj ij a.1 pa (by rw [he,sub_self]; exact dvd_zero _)
      · exact congrArg r
    have hh := pair_error L U Q b hQ a.1 v.1 (hP _ pa).1 (hP _ pv).1 (hP _ pa).2 (hP _ pv).2
      (r a.2) (r v.2) (fun _ hne' => hd a.2 si v.2 sj (fun h => hne' (congrArg r h)) a.1 pa)
    have h' : |cnt a v-N.card*mean a v| ≤ 4 := by
      simpa [cnt,g,N,interval,mean,hne] using hh
    have hle := (le_abs_self ((c a*c v)*(cnt a v-N.card*mean a v))).trans
      ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left h' (abs_nonneg _)))
    rw [abs_mul] at hle
    linarith only [hle]
  calc
    _ = ∑ a ∈ A, ∑ v ∈ A, (c a*c v)*cnt a v := by
      simp_rw [e]
      exact moments A N c g
    _ ≤ ∑ a ∈ A, ∑ v ∈ A, ((N.card:ℝ)*(c a*c v*mean a v)+4*(|c a| * |c v|)) :=
      sum_le_sum fun a ha => sum_le_sum (point a ha)
    _ = (N.card:ℝ)*(∑ a ∈ A, ∑ v ∈ A, c a*c v*mean a v)+
        4*(∑ a ∈ A, |c a|)^2 := by
      simp only [sum_add_distrib,←mul_sum,pow_two,sum_mul]
    _ = _ := by
      rw [show (∑ a ∈ A, ∑ v ∈ A, c a*c v*mean a v) = _ from mean_sum S P w hz]
      simp [A,c,sum_product,mul_assoc]


end FiniteSieve69

end

section

/-! # Prime reciprocal mass and rounding error in the second moment

Mertens' theorem bounds the reciprocal sum on the specified moving interval
by twice the triple logarithm plus a constant. The progression contains at
least one eighth of the square root of x many integers. This absorbs the
two-prime rounding term of order x to the power 1/25.

The elementary Mertens estimates through mertensG_step are from
@senamakel's merged Erdős 962 proof, commit
d757b84b7870c7b80a9e62d5e93a293328aee0d4.
The real-variable form adapts @marcusbuffett's Erdős 377 proof. -/

section

open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp


/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

/-- Partial sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring


end OMALib.Mertens
end

section
open Filter Finset Real Asymptotics
open scoped Topology BigOperators
open OMALib.Mertens
namespace Mass377
noncomputable abbrev S (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1:ℝ)/p
lemma Cpos : 0 ≤ mertens1Const := by
  exact (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)
lemma Gdiff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
    |mertensG n - mertensG m| ≤ (mertens1Const+1)*(1/log m-1/log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    calc |mertensG (n+1)-mertensG m| =
        |(mertensG (n+1)-mertensG n)+(mertensG n-mertensG m)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
      _ = _ := by ring
lemma logTop : Tendsto (fun n : ℕ => log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma natMertens : ∃ b : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE n, (1:ℝ)/p) -
    log (log n)) atTop (𝓝 b) := by
  have hC : CauchySeq mertensG := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => (mertens1Const+1)/log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logTop
    obtain ⟨m,hm,he⟩ := ((eventually_ge_atTop 2).and (hlim.eventually_lt_const hε)).exists
    refine ⟨m,fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply (Gdiff m n hm hn).trans_lt
    have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hp : 0≤(mertens1Const+1)*(1/log n) := mul_nonneg (by linarith [Cpos]) (by positivity [log_pos hn'])
    rw [mul_sub,←div_eq_mul_one_div]
    linarith
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hC
  let R (n : ℕ) := ((∑ p ∈ Nat.primesLE n, log p / p)-log n)/log n
  have hR : Tendsto R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (show Tendsto (fun n : ℕ => mertens1Const/log n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop logTop)
    filter_upwards [logTop.eventually_gt_atTop 0] with n hn
    dsimp only [R]
    rw [Real.norm_eq_abs, abs_div,abs_of_pos hn]
    exact div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat n) hn.le
  refine ⟨b,?_⟩
  simpa [R,mertensG] using hb.add hR
lemma realMertens : ∃ b : ℝ, Tendsto (fun x : ℝ => S x-log (log x)) atTop (𝓝 b) := by
  obtain ⟨b,hb⟩ := natMertens
  have he := (isEquivalent_nat_floor (R:=ℝ)).log tendsto_id
  have hz := tendsto_log_atTop.eventually_ne_atTop 0
  have ht := ((isEquivalent_iff_tendsto_one hz).1 he).log (by norm_num)
  have hfloor : Tendsto (fun x : ℝ => log (⌊x⌋₊:ℝ)) atTop atTop := logTop.comp tendsto_nat_floor_atTop
  have hdiff : Tendsto (fun x : ℝ => log (log (⌊x⌋₊:ℝ)) - log (log x)) atTop (𝓝 0) := by
    rw [Real.log_one] at ht
    apply ht.congr'
    filter_upwards [hz,hfloor.eventually_ne_atTop 0] with x hx hf
    exact log_div hf hx
  refine ⟨b,?_⟩
  have h := (hb.comp tendsto_nat_floor_atTop).add hdiff
  simpa [S,Function.comp_def,sub_add_sub_cancel] using h
end Mass377
end

section
open Filter Finset Real
namespace Numeric69
lemma prog_card (x Q b : ℕ) (hx : 256 ≤ x) (hQ : 0 < Q) (hQr : (Q:ℝ) ≤ √(x:ℝ)) :
    √(x:ℝ) ≤ 8 * (((Icc (x/2) x).filter fun n => n%Q=b%Q).card:ℝ) := by
  let u := x.sqrt
  have hQn : Q ≤ u := by
    change Q ≤ x.sqrt
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt]
    exact Nat.le_floor hQr
  have hu : 16 ≤ u := by
    exact Nat.le_sqrt.mpr hx
  let f (i : ℕ) := x/2/Q*Q + (i+1)*Q + b%Q
  have hi : Function.Injective f := by
    intro i j h
    dsimp [f] at h
    have he : (i+1)*Q=(j+1)*Q := by omega
    have := Nat.eq_of_mul_eq_mul_right hQ he
    omega
  have him : (range (u/4)).image f ⊆ (Icc (x/2) x).filter fun n => n%Q=b%Q := by
    rintro _ hi'
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hi'
    have hir := mem_range.mp hi
    have hdiv := Nat.div_mul_le_self (x/2) Q
    have hmod := Nat.mod_add_div (x/2) Q
    rw [Nat.mul_comm Q] at hmod
    have hm := Nat.mod_lt (x/2) hQ
    have hb := Nat.mod_lt b hQ
    have hsu := Nat.sqrt_le x
    change u*u ≤ x at hsu
    have hsum : (i+2)*Q ≤ x/2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0<2)).2
      calc
        (i+2)*Q*2 = (2*(i+2))*Q := by ring
        _ ≤ u*u := Nat.mul_le_mul (by omega) hQn
        _ ≤ x := hsu
    have hbase : Q ≤ (i+1)*Q := by exact Nat.le_mul_of_pos_left Q (by omega)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩,?_⟩
    · dsimp [f]; omega
    · dsimp [f]; rw [show i+2=i+1+1 by omega, Nat.add_mul, one_mul] at hsum; omega
    · simp [f,Nat.add_mod]
  have hcard := card_le_card him
  rw [card_image_of_injective _ hi,card_range] at hcard
  have hf := Nat.lt_floor_add_one (√(x:ℝ))
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt] at hf
  change √(x:ℝ) < (u:ℝ)+1 at hf
  have hbound : u+1 ≤ 8 * (((Icc (x/2) x).filter fun n => n%Q=b%Q).card) := by omega
  exact hf.le.trans (by exact_mod_cast hbound)
lemma floor_power (l : ℝ) (hl : 100 ≤ l) :
    let K := ⌊2*log l/log 2⌋₊
    0 < K ∧ (2:ℝ)^K ≤ l^2 ∧ l^2 ≤ 2*(2:ℝ)^K := by
  let t := 2*log l/log 2
  let K := ⌊t⌋₊
  have hl0 : 0 < l := by linarith
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ hlog).2
    have := log_le_log (by norm_num : (0:ℝ)<2) (show 2≤l by linarith)
    linarith
  have heq : (2:ℝ)^t=l^2 := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hh : log 2 * t = 2*log l := by dsimp [t]; field_simp
    rw [hh, show 2 * log l = log (l^2) by simp [Real.log_pow], Real.exp_log (by positivity)]
  have h1 : (K:ℝ) ≤ t := Nat.floor_le (by linarith)
  have h2 : t ≤ (K:ℝ)+1 := (Nat.lt_floor_add_one t).le
  have hK : 1 ≤ K := Nat.le_floor (by simpa using ht)
  refine ⟨hK, ?_, ?_⟩
  · calc (2:ℝ)^K = 2^(K:ℝ) := (Real.rpow_natCast ..).symm
         _ ≤ 2^t := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
         _ = _ := heq
  · calc l^2 = (2:ℝ)^t := heq.symm
         _ ≤ 2^((K:ℝ)+1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
         _ = _ := by rw [Real.rpow_add (by norm_num),Real.rpow_natCast,Real.rpow_one]; ring
end Numeric69
end

section
open Filter Real
namespace Numeric69
lemma growth (A : ℝ) : ∀ᶠ x : ℕ in atTop,
    let w := log (log x)
    let l := log w
    let D := exp (4*l^11)
    let R := (x:ℝ)^(1/w^2)
    256 ≤ x ∧ A ≤ l ∧ 100 ≤ l ∧ 2*D < R ∧ D < √(x:ℝ) ∧ D < (x/2:ℕ) ∧
      A ≤ R ∧ R ≤ x ∧ log (log R) = w - 2*l := by
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hwtop := tendsto_log_atTop.comp hlog
  have hltop := tendsto_log_atTop.comp hwtop
  have he := (tendsto_exp_div_pow_atTop 13).comp hwtop
  filter_upwards [eventually_ge_atTop 256,hlog.eventually_ge_atTop 1,hwtop.eventually_ge_atTop 2,
    hltop.eventually_ge_atTop (max A 100),he.eventually_ge_atTop 16] with x hx hxlog hw0 hl0 hexp
  let w := log (log (x:ℝ))
  let l := log w
  let R := (x:ℝ)^(1/w^2)
  have hxR : 1 < (x:ℝ) := by exact_mod_cast (show 1<x by omega)
  change 1 ≤ log (x:ℝ) at hxlog
  change 2 ≤ w at hw0
  change max A 100 ≤ l at hl0
  change 16 ≤ exp w / w^13 at hexp
  have hw : 0 < w := by linarith
  have hA := (le_max_left A 100).trans hl0
  have hl := (le_max_right A 100).trans hl0
  have hlw : l ≤ w := (log_le_sub_one_of_pos hw).trans (by linarith)
  have hwp : 16*w^13 ≤ log (x:ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0<w^13)).mp hexp
    simpa [w,Real.exp_log (by linarith : 0<log (x:ℝ))] using hh
  have h11 := pow_le_pow_left₀ (show 0 ≤ l by linarith) hlw 11
  have h13 : w^11 ≤ w^13 := pow_le_pow_right₀ (by linarith) (by decide)
  have hl11 : l ≤ l^11 := le_self_pow₀ (by linarith) (by decide)
  have hlogR : log R = log (x:ℝ) / w^2 := by dsimp [R]; rw [log_rpow (by linarith)]; ring
  have hratio : 16*w^11 ≤ log R := by
    rw [hlogR,le_div_iff₀ (by positivity)]
    calc 16 * w^11 * w^2 = 16*w^13 := by ring
         _ ≤ _ := hwp
  have hlR : 0 < log R := by linarith [show 0 < w^11 by positivity]
  have hR0 : 0 < R := rpow_pos_of_pos (by linarith) _
  have heR : 2*exp (4*l^11) < R := by
    rw [← exp_log (by norm_num : (0:ℝ)<2), ← exp_add, ← exp_log hR0]
    apply exp_lt_exp.mpr
    nlinarith only [hratio,h11,hl11,hl,log_two_lt_d9]
  have hD : exp (4*l^11) < √(x:ℝ) := by
    rw [← exp_log (Real.sqrt_pos.2 (by linarith : 0<(x:ℝ))), log_sqrt (by positivity)]
    apply exp_lt_exp.mpr
    linarith only [h11,h13,hwp,hl11,hl]
  have hs : √(x:ℝ) < (x/2:ℕ) := by
    have hs16 : 16 ≤ √(x:ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).2 (by
      have h : (256:ℝ)≤ x := by exact_mod_cast hx
      norm_num; linarith)
    have hdiv : (x:ℝ) ≤ 2*((x/2:ℕ):ℝ)+1 := by exact_mod_cast (show x≤2*(x/2)+1 by omega)
    nlinarith [sq_sqrt (by positivity : (0:ℝ) ≤ x),sq_nonneg (√(x:ℝ)-8)]
  refine ⟨hx,hA,hl,heR,hD,hD.trans hs,?_,?_,?_⟩
  · have := add_one_le_exp (log R)
    rw [exp_log hR0] at this
    linarith only [this,hratio,hl11,h11,hA,hl]
  · calc R ≤ (x:ℝ)^(1:ℝ) := rpow_le_rpow_of_exponent_le hxR.le
          ((div_le_one (by positivity)).2 (by nlinarith [sq_nonneg (w-2)]))
         _ = _ := rpow_one _
  · change log (log R) = w - 2*l
    rw [hlogR,log_div (by linarith) (by positivity),log_pow]; norm_num [w,l]
end Numeric69
end

section
open Real Filter Finset
open scoped Topology
namespace Numeric69
lemma prime_mass (C x R y : ℝ) (hR : R ≤ x) (hy : y ≤ x)
    (hC1 : |Mass377.S x - log (log x) - C| < 1) (hC2 : |Mass377.S R - log (log R) - C| < 1) :
    let P := (range (⌊y⌋₊+1)).filter fun p : ℕ => p.Prime ∧ R < p ∧ (p:ℝ) ≤ y
    (∑ p ∈ P,(1:ℝ)/p) ≤ log (log x) - log (log R) + 2 := by
  intro P
  have hsub : Nat.primesLE ⌊R⌋₊ ⊆ Nat.primesLE ⌊x⌋₊ :=
    fun p hp => Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.floor_mono hR),
      (Nat.mem_primesLE.mp hp).2⟩
  have hP : P ⊆ Nat.primesLE ⌊x⌋₊ \ Nat.primesLE ⌊R⌋₊ := by
    intro p hp
    obtain ⟨hprime, hpR, hpy⟩ := (mem_filter.mp hp).2
    refine mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor (hpy.trans hy),hprime⟩,?_⟩
    intro h
    have hpos : 0 < p := hprime.pos
    have hh := (Nat.mem_primesLE.mp h).1
    have := (Nat.le_floor_iff' hpos.ne').mp hh
    linarith
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (1:ℝ)/p) hP (by intros; positivity)
  have he := Finset.sum_sdiff hsub (f := fun p : ℕ => (1:ℝ)/p)
  change _ + Mass377.S R = Mass377.S x at he
  linarith only [hsum,he,(abs_lt.mp hC1).2,(abs_lt.mp hC2).1]

theorem numeric_bound :
  ∀ η : ℝ, 0 < η → ∀ᶠ x : ℕ in atTop,
    let l := log (log (log x))
    let K := ⌊2*log l/log 2⌋₊
    let D := exp (4*l^11)
    let R := (x:ℝ)^(1/log (log x)^2)
    100 ≤ l ∧ 0 < K ∧ (2:ℝ)^K ≤ l^2 ∧ 2*D < R ∧ D < (x/2:ℕ) ∧
    ∀ y : ℝ, y ≤ (x:ℝ)^(1/50:ℝ) → ∀ Q b : ℕ, 0 < Q → (Q:ℝ) ≤ D →
      let N := (Icc (x/2) x).filter fun n => n%Q=b%Q
      let P := (range (⌊y⌋₊+1)).filter fun p : ℕ => p.Prime ∧ R < p ∧ (p:ℝ) ≤ y
      (N.card:ℝ)*(1/(3*2^K))*(∑ p ∈ P, (1:ℝ)/p) + 4*(P.card:ℝ)^2 ≤ η*N.card := by
  intro η hη
  obtain ⟨C,hC⟩ := Mass377.realMertens
  obtain ⟨M,hM⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hC 1 (by norm_num))
  have ht := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<23/50)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (256/η)
  filter_upwards [growth (max M (8/η)),ht] with x hg hscale
  obtain ⟨hx,hlM,hl,hdR,hds,hdi,hRM,hRx,hRlog⟩ := hg
  let l := log (log (log (x:ℝ)))
  let K := ⌊2*log l/log 2⌋₊
  let R := (x:ℝ)^(1/log (log x)^2)
  let z := (x:ℝ)^(1/50:ℝ)
  change 100 ≤ l at hl
  change max M (8/η) ≤ l at hlM
  change max M (8/η) ≤ R at hRM
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast (show 1≤x by omega)
  have hx0 : (0:ℝ) < x := by linarith
  have hz1 : 1 ≤ z := Real.one_le_rpow hx1 (by norm_num)
  have hzx : z ≤ x := by
    calc z ≤ (x:ℝ)^(1:ℝ) := rpow_le_rpow_of_exponent_le hx1 (by norm_num)
         _ = _ := rpow_one _
  obtain ⟨hK,hK2,hKlo⟩ := floor_power l hl
  refine ⟨hl,hK,hK2,hdR,hdi,?_⟩
  intro y hy Q b hQ hQD N P
  have hprog := prog_card x Q b hx hQ (hQD.trans hds.le)
  change √(x:ℝ) ≤ 8*(N.card:ℝ) at hprog
  have hbound (t : ℝ) (ht : M ≤ t) : |Mass377.S t - log (log t) - C| < 1 := by
    simpa only [Real.dist_eq] using hM t ht
  have hmr : M ≤ R := (le_max_left _ _).trans hRM
  have hsum := prime_mass C (x:ℝ) R y hRx (hy.trans hzx)
    (hbound _ (hmr.trans hRx)) (hbound _ hmr)
  change (∑ p ∈ P,(1:ℝ)/p) ≤ log (log x) - log (log R) + 2 at hsum
  rw [hRlog] at hsum
  have hlin : 8 ≤ η*l := by
    have := (div_le_iff₀ hη).mp ((le_max_right M (8/η)).trans hlM)
    linarith
  have hsmall : (∑ p ∈ P,(1:ℝ)/p) ≤ (η/2)*(3*(2:ℝ)^K) := by
    have h1 : 2*l+2 ≤ 4*l := by linarith
    have h2 := mul_le_mul_of_nonneg_right hlin (show 0 ≤ l by linarith)
    have h3 := mul_le_mul_of_nonneg_left hKlo hη.le
    change _ ≤ log (log x) - (log (log x) - 2*l) + 2 at hsum
    nlinarith only [hsum,h1,h2,h3,hη,mul_nonneg hη.le (show 0≤(2:ℝ)^K by positivity),hl]
  have hmain : (N.card:ℝ)*(1/(3*2^K))*(∑ p ∈ P,(1:ℝ)/p) ≤ (N.card:ℝ)*(η/2) := by
    have hd : 0 < 3*(2:ℝ)^K := by positivity
    calc
      _ = (N.card:ℝ) * ((∑ p ∈ P,(1:ℝ)/p) / (3*(2:ℝ)^K)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((div_le_iff₀ hd).2 hsmall) (by positivity)
  have hc : (P.card : ℝ) ≤ 2*z := by
    have hf := Finset.card_filter_le (range (⌊y⌋₊+1)) (fun p : ℕ => p.Prime ∧ R<p ∧ (p:ℝ)≤y)
    change P.card ≤ _ at hf
    rw [card_range] at hf
    have hc' : P.card ≤ ⌊z⌋₊+1 := hf.trans (Nat.add_le_add_right (Nat.floor_mono (show y ≤ z from hy)) 1)
    have hc'' : (P.card : ℝ) ≤ (⌊z⌋₊:ℝ)+1 := by exact_mod_cast hc'
    linarith [Nat.floor_le (show 0≤z by positivity)]
  have hpows : z^2 * (x:ℝ)^(23/50 : ℝ) = √(x:ℝ) := by
    dsimp [z]
    rw [← rpow_natCast,← rpow_mul hx0.le,← rpow_add hx0,Real.sqrt_eq_rpow]
    norm_num
  change 256/η ≤ (x:ℝ)^(23/50 : ℝ) at hscale
  have hm := mul_le_mul_of_nonneg_left ((div_le_iff₀ hη).mp hscale) (sq_nonneg z)
  have hlarge : 256*z^2 ≤ η*√(x:ℝ) := by
    rw [← hpows]
    linarith only [hm]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (P.card:ℝ)) hc 2
  have hηn := mul_le_mul_of_nonneg_left hprog hη.le
  nlinarith only [hmain,hlarge,hsq,hηn]
end Numeric69
end

end

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1.H3 :=
  OMA.R_Erdos69_erdos_69_R1_H1_R1_H3_R1.main FiniteSieve69.variance Numeric69.numeric_bound
