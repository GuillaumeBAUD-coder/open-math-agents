import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1
import Mathlib


-- Reduction Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H1.R1.H4.R1 of step Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H1.R1.H4
-- Credit: @carterleffen

-- Reduction Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H1.R1.H4.R1 of step Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H1.R1.H4
-- Credit: @carterleffen

/-! # Boundary, renewal, and prime-sum limits for the reference polynomial -/

open Filter Finset MeasureTheory Set Real
open scoped Classical Topology ENNReal
namespace OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1_H4_R1

def H1 : Prop :=
  let d (c u : ℝ) := Nat.rec (motive := fun _ => ℝ → ℝ) (fun _ => 1)
    (fun _ g v => 1+c*∫ t in (1:ℝ)..max 1 v, g (t-1)/max 1 t) ⌈u⌉₊ u
  let A := 2*exp eulerMascheroniConstant
  let f (s : ℝ) := if s ≤ 2 then 0 else A*(d 1 (s-1)-d (-1) (s-1))/(2*s)
  let F (s : ℝ) := A*(d 1 (s-1)+d (-1) (s-1))/(2*s)
  let C := (∫ y in Set.Ioi (1:ℝ), (y^2-1)*(1-f (y+1))) -
    ∫ y in Set.Ioi (0:ℝ), y^2*(1-F (y+1))
  C = (8:ℝ)/3

def H2 : Prop :=
∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (P : ℕ → Measure ℝ),
    P 0 = Measure.dirac 0 → (∀ n, P (n+1) = (P n).conv μ) →
    (∀ a r : ℝ, μ {x : ℝ | ∃ k : ℤ, x = a + k*r} ≠ 1) →
    MemLp id 2 μ → 0 < (∫ x, x ∂μ) →
    (∫⁻ x, ENNReal.ofReal (exp (-(1*x))) ∂μ) < 1 →
    ((∀ H : ℝ → ℝ, Continuous H →
      (∑' k : ℤ, ⨆ x ∈ Set.Icc (k:ℝ) (k+1), ‖H x‖ₑ) ≠ ∞ →
      Tendsto (fun y : ℝ => ∑' n : ℕ, ∫ s, H (y-s) ∂P n)
        atTop (𝓝 ((∫ x, H x)/(∫ x, x ∂μ)))) ∧
     ∀ ell : ℝ, ∃ C : ℝ, ∀ y, Measure.sum P (Set.Icc y (y+ell)) ≤ ENNReal.ofReal C)

def H3 : Prop :=
  let d (c u : ℝ) := Nat.rec (motive := fun _ => ℝ → ℝ) (fun _ => 1)
    (fun _ g v => 1+c*∫ t in (1:ℝ)..max 1 v, g (t-1)/max 1 t) ⌈u⌉₊ u
  let A := 2*exp eulerMascheroniConstant
  let f (s : ℝ) := if s ≤ 2 then 0 else A*(d 1 (s-1)-d (-1) (s-1))/(2*s)
  let F (s : ℝ) := A*(d 1 (s-1)+d (-1) (s-1))/(2*s)
  let U (i : Bool) (r b : ℝ) := if i then max 1 (min (min 2 b) ((r-2)/2)) else max 1 (min 2 b)
  let K (v : Bool → ℝ → ℝ → ℝ) (i : Bool) (r b : ℝ) :=
    ∫ x in (1:ℝ)..U i r b, v (!i) (r-x) x/max 1 x
  let h (i : Bool) (r : ℝ) := (∑ n ∈ range (⌈max r 0⌉₊+3),
    (-1:ℝ)^n*(K^[n] (fun _ _ _ => 1)) i r 2) - (if i then F (r/2) else f (r/2))/2
  let J := (∫ r in Set.Ioi (4:ℝ), r*(r/2-2)*h false r) -
    ∫ r in Set.Ioi (2:ℝ), (r^2/2-2*r+2)*h true r
  let E (l : ℝ → ℝ) (v : Bool → ℝ → ℝ) (z : ℝ) :=
    let L := log z
    let Y := ⌊z^2/L^2⌋₊
    let w := L/(log L)^2
    let P := (Finset.Icc (⌊l w⌋₊+1) ⌊z⌋₊).filter Nat.Prime
    let e (p : ℕ) := log p/log w
    let G (s : Finset ℕ) := log ((Y:ℝ)/(∏ p ∈ s, (p:ℝ)))/log w+2-1/100
    let T := P.powerset.filter fun s => ∀ p ∈ s, let t := s.filter fun q => p ≤ q
      Even t.card → max (2*e p) (e p+2) ≤
        log ((Y:ℝ)/(∏ q ∈ t,(q:ℝ)))/log w+2-1/100
    (L/log w)^2*∑ s ∈ T, (-1:ℝ)^s.card/(∏ p ∈ s, (p:ℝ))*v (decide (Odd s.card)) (G s)
  (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (P : ℕ → Measure ℝ),
    P 0 = Measure.dirac 0 → (∀ n, P (n+1) = (P n).conv μ) →
    (∀ a r : ℝ, μ {x : ℝ | ∃ k : ℤ, x = a + k*r} ≠ 1) →
    MemLp id 2 μ → 0 < (∫ x, x ∂μ) →
    (∫⁻ x, ENNReal.ofReal (exp (-(1*x))) ∂μ) < 1 →
    ((∀ H : ℝ → ℝ, Continuous H →
      (∑' k : ℤ, ⨆ x ∈ Set.Icc (k:ℝ) (k+1), ‖H x‖ₑ) ≠ ∞ →
      Tendsto (fun y : ℝ => ∑' n : ℕ, ∫ s, H (y-s) ∂P n)
        atTop (𝓝 ((∫ x, H x)/(∫ x, x ∂μ)))) ∧
     ∀ ell : ℝ, ∃ C : ℝ, ∀ y, Measure.sum P (Set.Icc y (y+ell)) ≤ ENNReal.ofReal C)) → ∃ M : ℝ, 0 < M ∧ M ≤ 8 ∧
    Tendsto (E (·^2) h) atTop (𝓝 (exp eulerMascheroniConstant*(J/M)))

def H4 : Prop :=
  let d (c u : ℝ) := Nat.rec (motive := fun _ => ℝ → ℝ) (fun _ => 1)
    (fun _ g v => 1+c*∫ t in (1:ℝ)..max 1 v, g (t-1)/max 1 t) ⌈u⌉₊ u
  let A := 2*exp eulerMascheroniConstant
  let f (s : ℝ) := if s ≤ 2 then 0 else A*(d 1 (s-1)-d (-1) (s-1))/(2*s)
  let F (s : ℝ) := A*(d 1 (s-1)+d (-1) (s-1))/(2*s)
  let U (i : Bool) (r b : ℝ) := if i then max 1 (min (min 2 b) ((r-2)/2)) else max 1 (min 2 b)
  let K (v : Bool → ℝ → ℝ → ℝ) (i : Bool) (r b : ℝ) :=
    ∫ x in (1:ℝ)..U i r b, v (!i) (r-x) x/max 1 x
  let h (i : Bool) (r : ℝ) := (∑ n ∈ range (⌈max r 0⌉₊+3),
    (-1:ℝ)^n*(K^[n] (fun _ _ _ => 1)) i r 2) - (if i then F (r/2) else f (r/2))/2
  let J := (∫ r in Set.Ioi (4:ℝ), r*(r/2-2)*h false r) -
    ∫ r in Set.Ioi (2:ℝ), (r^2/2-2*r+2)*h true r
  let E (l : ℝ → ℝ) (v : Bool → ℝ → ℝ) (z : ℝ) :=
    let L := log z
    let Y := ⌊z^2/L^2⌋₊
    let w := L/(log L)^2
    let P := (Finset.Icc (⌊l w⌋₊+1) ⌊z⌋₊).filter Nat.Prime
    let e (p : ℕ) := log p/log w
    let G (s : Finset ℕ) := log ((Y:ℝ)/(∏ p ∈ s, (p:ℝ)))/log w+2-1/100
    let T := P.powerset.filter fun s => ∀ p ∈ s, let t := s.filter fun q => p ≤ q
      Even t.card → max (2*e p) (e p+2) ≤
        log ((Y:ℝ)/(∏ q ∈ t,(q:ℝ)))/log w+2-1/100
    (L/log w)^2*∑ s ∈ T, (-1:ℝ)^s.card/(∏ p ∈ s, (p:ℝ))*v (decide (Odd s.card)) (G s)
  let C := (∫ y in Set.Ioi (1:ℝ), (y^2-1)*(1-f (y+1))) -
    ∫ y in Set.Ioi (0:ℝ), y^2*(1-F (y+1))
  let g (i : Bool) (r b : ℝ) := if i then (U true r b)⁻¹-(U false r b)⁻¹ else 0
  let a (n : ℕ) := (∫ y in Set.Ioi (1:ℝ), 2*(y^2-1)*(K^[n] g) false (2*y+2) 2) +
    ∫ y in Set.Ioi (0:ℝ), 2*y^2*(K^[n] g) true (2*y+2) 2
  J = 2*(C-∑' n, a n) ∧ Tendsto (fun z => E id (fun _ _ => 1) z-E (·^2) h z)
    atTop (𝓝 (exp eulerMascheroniConstant*(-(1:ℝ)/100)))

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1.H4 := by
  intro hb hr hc hd
  let d (c u : ℝ) := Nat.rec (motive := fun _ => ℝ → ℝ) (fun _ => 1)
    (fun _ g v => 1+c*∫ t in (1:ℝ)..max 1 v, g (t-1)/max 1 t) ⌈u⌉₊ u
  let A := 2*exp eulerMascheroniConstant
  let f (s : ℝ) := if s ≤ 2 then 0 else A*(d 1 (s-1)-d (-1) (s-1))/(2*s)
  let F (s : ℝ) := A*(d 1 (s-1)+d (-1) (s-1))/(2*s)
  let U (i : Bool) (r b : ℝ) := if i then max 1 (min (min 2 b) ((r-2)/2)) else max 1 (min 2 b)
  let K (v : Bool → ℝ → ℝ → ℝ) (i : Bool) (r b : ℝ) :=
    ∫ x in (1:ℝ)..U i r b, v (!i) (r-x) x/max 1 x
  let h (i : Bool) (r : ℝ) := (∑ n ∈ range (⌈max r 0⌉₊+3),
    (-1:ℝ)^n*(K^[n] (fun _ _ _ => 1)) i r 2) - (if i then F (r/2) else f (r/2))/2
  let J := (∫ r in Set.Ioi (4:ℝ), r*(r/2-2)*h false r) -
    ∫ r in Set.Ioi (2:ℝ), (r^2/2-2*r+2)*h true r
  let E (l : ℝ → ℝ) (v : Bool → ℝ → ℝ) (z : ℝ) :=
    let L := log z
    let Y := ⌊z^2/L^2⌋₊
    let w := L/(log L)^2
    let P := (Finset.Icc (⌊l w⌋₊+1) ⌊z⌋₊).filter Nat.Prime
    let e (p : ℕ) := log p/log w
    let G (s : Finset ℕ) := log ((Y:ℝ)/(∏ p ∈ s, (p:ℝ)))/log w+2-1/100
    let T := P.powerset.filter fun s => ∀ p ∈ s, let t := s.filter fun q => p ≤ q
      Even t.card → max (2*e p) (e p+2) ≤
        log ((Y:ℝ)/(∏ q ∈ t,(q:ℝ)))/log w+2-1/100
    (L/log w)^2*∑ s ∈ T, (-1:ℝ)^s.card/(∏ p ∈ s, (p:ℝ))*v (decide (Odd s.card)) (G s)
  let C := (∫ y in Set.Ioi (1:ℝ), (y^2-1)*(1-f (y+1))) -
    ∫ y in Set.Ioi (0:ℝ), y^2*(1-F (y+1))
  let g (i : Bool) (r b : ℝ) := if i then (U true r b)⁻¹-(U false r b)⁻¹ else 0
  let a (n : ℕ) := (∫ y in Set.Ioi (1:ℝ), 2*(y^2-1)*(K^[n] g) false (2*y+2) 2) +
    ∫ y in Set.Ioi (0:ℝ), 2*y^2*(K^[n] g) true (2*y+2) 2
  change C = (8:ℝ)/3 at hb
  obtain ⟨m, hm, h8, hlim⟩ := hc hr
  change Tendsto (E (·^2) h) atTop (𝓝 (exp eulerMascheroniConstant*(J/m))) at hlim
  obtain ⟨hj, hdiff⟩ := hd
  change J = 2*(C-∑' n, a n) at hj
  change Tendsto (fun z => E id (fun _ _ => 1) z-E (·^2) h z) atTop
    (𝓝 (exp eulerMascheroniConstant*(-(1:ℝ)/100))) at hdiff
  have hs := hdiff.add hlim
  simp only [sub_add_cancel] at hs
  rw [hj, hb, ← mul_add] at hs
  refine ⟨m, hm, h8, ?_⟩
  simpa only [E, a, g, K, U, id_eq, mul_one] using hs

end OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1_H4_R1
