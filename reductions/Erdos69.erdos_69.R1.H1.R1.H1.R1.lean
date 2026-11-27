import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1

/-! Credit: @marcusbuffett. Separate the Hilbert cube construction in the primes
from the numerical size estimates. The simultaneous congruences are solved here. -/

namespace OMA.R_Erdos69_erdos_69_R1_H1_R1_H1_R1
open Finset Filter

/-- The prime Hilbert cube at its own scale, with no collisions at the near shifts. -/
def H1 : Prop :=
  ∀ᶠ l : ℝ in atTop,
    let K := ⌊2 * Real.log l / Real.log 2⌋₊
    let H := ⌊l^2⌋₊
    ∃ (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ),
    (∀ E ∈ (range K).powerset, (p E).Prime ∧ Real.exp (l^3) ≤ 8*p E ∧
      (p E:ℝ) ≤ Real.exp (l^3) ∧ |s E| ≤ 8*(K:ℤ)^2*p E ∧
      ∀ k < K, (p (symmDiff E {k}):ℤ) * ((k+1:ℕ):ℤ) - s (symmDiff E {k}) = (p E:ℤ) * ((k+1:ℕ):ℤ) - s E) ∧
    Set.InjOn p ((range K).powerset) ∧ (∏ a ∈ ((range K).powerset ×ˢ Ico (K+1) (K+H+1)).offDiag, (((p a.1.1:ℤ)*(a.1.2:ℤ)-s a.1.1)-((p a.2.1:ℤ)*(a.2.2:ℤ)-s a.2.1)).natAbs) ≠ 0

/-- The products of prime powers and pairwise differences fit below the outer
scale, using only individual upper bounds. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ x : ℕ in atTop,
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
      ∀ a ∈ ((range K).powerset ×ˢ Ico (K+1) (K+H+1)), |(((p a.1:ℤ)*(a.2:ℤ)-s a.1:ℤ):ℝ)| ≤ B

lemma progression (C : Finset (Finset ℕ)) (p : Finset ℕ → ℕ) (s : Finset ℕ → ℤ)
    (hprime : ∀ E ∈ C, (p E).Prime) (hinj : Set.InjOn p C) (W : ℕ) :
    ∃ b : ℕ, (∀ E ∈ C, (b:ℤ) ≡ s E [ZMOD p E]) ∧ (∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ) ∣ b := by
  classical
  let v (E : Finset ℕ) := ((s E : ℤ) : ZMod (p E)).val
  let cr := Nat.chineseRemainderOfFinset v p C (fun E hE => (hprime E hE).ne_zero)
    (fun E hE F hF hne => (Nat.coprime_primes (hprime E hE) (hprime F hF)).mpr
      (fun he => hne (hinj hE hF he)))
  let P := ∏ E ∈ C, p E
  let D := (∏ ℓ ∈ W.primeFactors \ C.image p, ℓ ^ W.factorization ℓ)
  have hc : P.Coprime D := by
    apply Nat.coprime_prod_left_iff.mpr
    intro E hE
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    obtain ⟨hW,hn⟩ := mem_sdiff.mp hq
    apply Nat.Coprime.pow_right
    apply (Nat.coprime_primes (hprime E hE) (Nat.prime_of_mem_primeFactors hW)).mpr
    intro he
    exact hn (mem_image.mpr ⟨E,hE,he⟩)
  let out := Nat.chineseRemainder hc cr.val 0
  refine ⟨out.val,?_,Nat.modEq_zero_iff_dvd.mp out.prop.2⟩
  intro E hE
  have he := (out.prop.1.of_dvd (dvd_prod_of_mem p hE)).trans (cr.prop E hE)
  letI : NeZero (p E) := ⟨(hprime E hE).ne_zero⟩
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  rw [Int.cast_natCast]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr he).trans (ZMod.natCast_zmod_val _)

theorem main : H1 → H2 → OMA.R_Erdos69_erdos_69_R1_H1_R1.H1 := by
  intro cubes small η hη
  have hscale : Tendsto (fun x : ℕ => Real.log (Real.log (Real.log x))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))))
  apply eventually_atTop.mp
  filter_upwards [hscale.eventually cubes,small η hη] with x hcube hsmall
  let l := Real.log (Real.log (Real.log x))
  let K := ⌊2 * Real.log l / Real.log 2⌋₊
  let H := ⌊l^2⌋₊
  obtain ⟨p,s,hs,hi,hW⟩ := hcube
  obtain ⟨b,hb,hd⟩ := progression ((range K).powerset) p s (fun E he => (hs E he).1) hi
    ((∏ a ∈ ((range K).powerset ×ˢ Ico (K+1) (K+H+1)).offDiag, (((p a.1.1:ℤ)*(a.1.2:ℤ)-s a.1.1)-((p a.2.1:ℤ)*(a.2.2:ℤ)-s a.2.1)).natAbs))
  obtain ⟨hl,hQ,hS,hR⟩ := hsmall p s (fun E he => ⟨(hs E he).2.2.1,(hs E he).2.2.2.1⟩) hW
  refine ⟨K,H,_,b,p,s,rfl,rfl,?_,hi,hW,rfl,hd,hl,hQ,hS,hR⟩
  intro E he
  obtain ⟨hp,hlo,hup,habs,hflip⟩ := hs E he
  exact ⟨hp,hlo,hup,habs,hb E he,hflip⟩

end OMA.R_Erdos69_erdos_69_R1_H1_R1_H1_R1
