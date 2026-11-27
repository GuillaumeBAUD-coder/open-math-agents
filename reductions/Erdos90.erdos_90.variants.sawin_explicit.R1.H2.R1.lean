import OMAReductions.R_Erdos90_erdos_90_variants_sawin_explicit_R1
import Mathlib

/-! Sawin gives explicit prime sets, exponents and radius in the proof of Theorem 1
(arXiv:2605.20579). His Lemma 12 for those fixed primes gives the tower in H1.
The scalar comparison H2 contains only two fixed integers, obtained by taking the
fourth power of the product of primes and the eighth power of the product of
multiplicities. The identification of those integers and of the local parameters
is checked below. -/
namespace OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H2_R1
open Finset NumberField

/-- The concrete CM tower from Sawin's Lemma 12 for the auxiliary quadratic
field of discriminant 4 times the product of the odd primes up to 43. -/
def H1 : Prop :=
  let S : Finset ℕ := {2,3,5,7,11,13,17,19,23,29,47,71,79,97,101,107,109,139,151,163,167,179}
  let e (p : ℕ) : ℕ := if p ≤ 29 then 2 else 1
  ∀ N : ℕ, ∃ (F K : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
      (_ : IsTotallyReal F) (_ : Field K) (_ : CharZero K) (_ : NumberField K)
      (_ : IsTotallyComplex K) (_ : Algebra F K) (_ : Algebra.IsQuadraticExtension F K),
    N ≤ Module.finrank ℚ F ∧
    |(NumberField.discr K : ℝ)| / |(NumberField.discr F : ℝ)| ≤
      (Real.sqrt 26165522663340060) ^ (Module.finrank ℚ F) ∧
    ∀ p ∈ S, ∀ 𝔭 ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F),
      𝔭.ramificationIdx ℤ = e p ∧ 𝔭.inertiaDeg ℤ ≤ 2 ∧ Nat.card (𝔭.primesOver (𝓞 K)) = 2

/-- The explicit scalar comparison. Its two sides are approximately 48.52751 and
48.53323, respectively. -/
def H2 : Prop :=
  (144 * (15366930839640910407280821544568342760939116621460511799368640691024952414942895895674487917919190453067074013839821044685981817225847752755432866840801104952946378971003813637609053179555854971429716544369570035272611087657978405847032106632812497009078453661958168488757383118555915563176123245641339520488302511643015980605017267388801042321225063767021503823501125249521809325896257913477135701039141274572751456580509666911459268400451518726144000000000000000000000 : ℝ) ^ (4:ℝ)⁻¹ + 1) ^ (0.014114:ℝ) <
    (1 - 1 / 72) * Real.sqrt (2 * Real.pi / Real.exp 1) *
      (4028003754363836120804840523694080 : ℝ) ^ (8:ℝ)⁻¹ /
      ((Real.sqrt 26165522663340060) ^ (1/4:ℝ) * Real.sqrt (Real.log (Real.sqrt 26165522663340060)))

set_option maxRecDepth 8000 in
theorem main : H1 → H2 → OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1.H2 := by
  intro tower numeric
  let S : Finset ℕ := {2,3,5,7,11,13,17,19,23,29,47,71,79,97,101,107,109,139,151,163,167,179}
  let e (p : ℕ) : ℕ := if p ≤ 29 then 2 else 1
  let j (p : ℕ) : ℕ := if p ≤ 29 then 1 else 2
  let k : ℕ → ℕ := fun p => if p = 2 then 50 else if p = 3 then 31 else if p = 5 then 21 else if p = 7 then 17 else if p = 11 then 14 else if p = 13 then 13 else if p = 17 then 12 else if p = 19 then 11 else if p = 23 then 10 else if p = 29 then 10 else if p = 47 then 8 else if p = 71 then 7 else if p = 79 then 7 else if p = 97 then 7 else if p = 101 then 7 else if p = 107 then 7 else if p = 109 then 7 else 6
  have hS : ∀ p ∈ S, p.Prime ∧ 1 ≤ e p ∧ 1 ≤ (2:ℕ) ∧ 1 ≤ k p := by
    decide +kernel
  refine ⟨S,e,fun _ => 2,k,Real.sqrt 26165522663340060,72,?_,by norm_num,hS,?_,tower⟩
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  let A := ∏ p ∈ S, (p:ℝ)^((k p:ℝ)/(2*(e p:ℝ)))
  let B := ∏ p ∈ S, ((k p:ℝ)+1)^((1:ℝ)/(2*(e p:ℝ)*2))
  have ha (p : ℕ) : ((k p:ℝ)/(2*(e p:ℝ)))*4 = (k p * j p : ℕ) := by
    by_cases hp : p ≤ 29 <;> simp [e,j,hp] <;> ring
  have hb (p : ℕ) : ((1:ℝ)/(2*(e p:ℝ)*2))*8 = (j p:ℝ) := by
    by_cases hp : p ≤ 29 <;> norm_num [e,j,hp]
  have hUA : (∏ p ∈ S, p^(k p*j p)) = 15366930839640910407280821544568342760939116621460511799368640691024952414942895895674487917919190453067074013839821044685981817225847752755432866840801104952946378971003813637609053179555854971429716544369570035272611087657978405847032106632812497009078453661958168488757383118555915563176123245641339520488302511643015980605017267388801042321225063767021503823501125249521809325896257913477135701039141274572751456580509666911459268400451518726144000000000000000000000 := by decide +kernel
  have hVB : (∏ p ∈ S, (k p+1)^(j p)) = 4028003754363836120804840523694080 := by decide +kernel
  have hA : A^4 = (15366930839640910407280821544568342760939116621460511799368640691024952414942895895674487917919190453067074013839821044685981817225847752755432866840801104952946378971003813637609053179555854971429716544369570035272611087657978405847032106632812497009078453661958168488757383118555915563176123245641339520488302511643015980605017267388801042321225063767021503823501125249521809325896257913477135701039141274572751456580509666911459268400451518726144000000000000000000000:ℝ) := by
    calc
      A^4 = ∏ p ∈ S, (p:ℝ)^(k p*j p) := by
        dsimp only [A]
        rw [← Finset.prod_pow]
        apply prod_congr rfl
        intro p _
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),show ((4:ℕ):ℝ)=4 by norm_num,
          ha,Real.rpow_natCast]
      _ = _ := by exact_mod_cast hUA
  have hB : B^8 = (4028003754363836120804840523694080:ℝ) := by
    calc
      B^8 = ∏ p ∈ S, ((k p:ℝ)+1)^(j p) := by
        dsimp only [B]
        rw [← Finset.prod_pow]
        apply prod_congr rfl
        intro p _
        rw [← Real.rpow_mul_natCast (by positivity),show ((8:ℕ):ℝ)=8 by norm_num,
          hb,Real.rpow_natCast]
      _ = _ := by exact_mod_cast hVB
  have hA0 : 0 ≤ A := prod_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hB0 : 0 ≤ B := prod_nonneg fun p _ => Real.rpow_nonneg (by positivity) _
  change (2 * 72 * A + 1) ^ (0.014114:ℝ) < (1-1/72)*Real.sqrt (2*Real.pi/Real.exp 1)*B /
    ((Real.sqrt 26165522663340060) ^ (1/4:ℝ) * Real.sqrt (Real.log (Real.sqrt 26165522663340060)))
  unfold H2 at numeric
  have hAr : (15366930839640910407280821544568342760939116621460511799368640691024952414942895895674487917919190453067074013839821044685981817225847752755432866840801104952946378971003813637609053179555854971429716544369570035272611087657978405847032106632812497009078453661958168488757383118555915563176123245641339520488302511643015980605017267388801042321225063767021503823501125249521809325896257913477135701039141274572751456580509666911459268400451518726144000000000000000000000:ℝ)^(4:ℝ)⁻¹ = A := by
    rw [← hA]; exact Real.pow_rpow_inv_natCast hA0 (n:=4) (by decide)
  have hBr : (4028003754363836120804840523694080:ℝ)^(8:ℝ)⁻¹ = B := by
    rw [← hB]; exact Real.pow_rpow_inv_natCast hB0 (n:=8) (by decide)
  rw [hAr,hBr] at numeric
  rw [show (2:ℝ)*72=144 by norm_num]
  exact numeric

end OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H2_R1
