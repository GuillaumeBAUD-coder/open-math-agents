import FormalConjectures.Wikipedia.Kaplansky

/-!
# Counterexample to Kaplansky's Unit Conjecture over `ℂ`

We prove `Kaplansky.UnitConjecture.counterexamples.ii`: the complex group algebra
`MonoidAlgebra ℂ PromislowGroup` contains a non-trivial unit, formalizing Gardam's
explicit 21-term unit (arXiv:2312.05240).
-/

namespace KaplanskyUnitComplex

open Kaplansky

noncomputable section

/- ### Relations in `PromislowGroup` -/

private abbrev P := PromislowGroup

private def gA : P := PresentedGroup.of (0 : Fin 2)
private def gB : P := PresentedGroup.of (1 : Fin 2)
private def gX : P := gA * gA
private def gY : P := gB * gB
private def gAB : P := gA * gB
private def gZ : P := gAB * gAB

private lemma rel_b_a2 : gB⁻¹ * gA * gA * gB * gA * gA = 1 := by
  let fa := FreeGroup.of (0 : Fin 2)
  let fb := FreeGroup.of (1 : Fin 2)
  have hmem : fb⁻¹ * fa * fa * fb * fa * fa ∈
      ({fb⁻¹ * fa * fa * fb * fa * fa, fa⁻¹ * fb * fb * fa * fb * fb} : Set (FreeGroup (Fin 2))) :=
    Set.mem_insert _ _
  have h := PresentedGroup.one_of_mem hmem
  simpa [gA, gB, fa, fb, PresentedGroup.of, map_mul, map_inv] using h

private lemma rel_a_b2 : gA⁻¹ * gB * gB * gA * gB * gB = 1 := by
  let fa := FreeGroup.of (0 : Fin 2)
  let fb := FreeGroup.of (1 : Fin 2)
  have hmem : fa⁻¹ * fb * fb * fa * fb * fb ∈
      ({fb⁻¹ * fa * fa * fb * fa * fa, fa⁻¹ * fb * fb * fa * fb * fb} : Set (FreeGroup (Fin 2))) :=
    Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have h := PresentedGroup.one_of_mem hmem
  simpa [gA, gB, fa, fb, PresentedGroup.of, map_mul, map_inv] using h

private lemma gB_mul_gX : gB * gX = gX⁻¹ * gB := by
  have h : gB⁻¹ * gX * gB * gX = 1 := by simpa [gX, mul_assoc] using rel_b_a2
  calc gB * gX = gX⁻¹ * (gB * (gB⁻¹ * gX * gB * gX)) := by group
    _ = gX⁻¹ * (gB * 1) := by rw [h]
    _ = gX⁻¹ * gB := by group

private lemma gB_mul_gX_inv : gB * gX⁻¹ = gX * gB := by
  calc gB * gX⁻¹ = gX * (gX⁻¹ * gB) * gX⁻¹ := by group
    _ = gX * (gB * gX) * gX⁻¹ := by rw [← gB_mul_gX]
    _ = gX * gB := by group

private lemma gA_mul_gY : gA * gY = gY⁻¹ * gA := by
  have h : gA⁻¹ * gY * gA * gY = 1 := by simpa [gY, mul_assoc] using rel_a_b2
  calc gA * gY = gY⁻¹ * (gA * (gA⁻¹ * gY * gA * gY)) := by group
    _ = gY⁻¹ * (gA * 1) := by rw [h]
    _ = gY⁻¹ * gA := by group

private lemma gA_mul_gY_inv : gA * gY⁻¹ = gY * gA := by
  calc gA * gY⁻¹ = gY * (gY⁻¹ * gA) * gY⁻¹ := by group
    _ = gY * (gA * gY) * gY⁻¹ := by rw [← gA_mul_gY]
    _ = gY * gA := by group

private lemma gA_mul_gX : gA * gX = gX * gA := by simp only [gX, mul_assoc]

private lemma gA_mul_gX_inv : gA * gX⁻¹ = gX⁻¹ * gA := by
  calc gA * gX⁻¹ = gX⁻¹ * (gX * gA) * gX⁻¹ := by group
    _ = gX⁻¹ * (gA * gX) * gX⁻¹ := by rw [← gA_mul_gX]
    _ = gX⁻¹ * gA := by group

private lemma gB_mul_gY : gB * gY = gY * gB := by simp only [gY, mul_assoc]

private lemma gB_mul_gY_inv : gB * gY⁻¹ = gY⁻¹ * gB := by
  calc gB * gY⁻¹ = gY⁻¹ * (gY * gB) * gY⁻¹ := by group
    _ = gY⁻¹ * (gB * gY) * gY⁻¹ := by rw [← gB_mul_gY]
    _ = gY⁻¹ * gB := by group

private lemma gX_mul_gY : gX * gY = gY * gX := by
  calc gX * gY = gA * (gA * gY) := by simp only [gX, mul_assoc]
    _ = gA * (gY⁻¹ * gA) := by rw [gA_mul_gY]
    _ = (gA * gY⁻¹) * gA := by simp only [mul_assoc]
    _ = (gY * gA) * gA := by rw [gA_mul_gY_inv]
    _ = gY * gX := by simp only [gX, mul_assoc]

private lemma gA_mul_gZ : gA * gZ = gZ⁻¹ * gA := by
  have hprod : (gA * gZ * gA⁻¹) * gZ = 1 := by
    calc gA * gZ * gA⁻¹ * gZ
        = gX * gB * (gA * gY) * gA * gB := by simp only [gZ, gAB, gX, gY, mul_assoc]; group
      _ = gX * gB * (gY⁻¹ * gA) * gA * gB := by rw [gA_mul_gY]
      _ = gX * (gB * gY⁻¹) * gX * gB := by simp only [gX, mul_assoc]
      _ = gX * (gY⁻¹ * gB) * gX * gB := by rw [gB_mul_gY_inv]
      _ = gX * gY⁻¹ * (gB * gX) * gB := by simp only [mul_assoc]
      _ = gX * gY⁻¹ * (gX⁻¹ * gB) * gB := by rw [gB_mul_gX]
      _ = gX * gY⁻¹ * gX⁻¹ * gY := by simp only [gY, mul_assoc]
      _ = gX * gY⁻¹ * gX⁻¹ * (gX * gY * gX⁻¹) := by rw [gX_mul_gY]; group
      _ = 1 := by group
  calc gA * gZ = (gA * gZ * gA⁻¹ * gZ) * gZ⁻¹ * gA := by group
    _ = 1 * gZ⁻¹ * gA := by rw [hprod]
    _ = gZ⁻¹ * gA := by group

private lemma gB_mul_gZ : gB * gZ = gZ⁻¹ * gB := by
  have hprod : (gB * gZ * gB⁻¹) * gZ = 1 := by
    calc gB * gZ * gB⁻¹ * gZ
        = gB * gA * (gB * gX) * gB * gA * gB := by simp only [gZ, gAB, gX, mul_assoc]; group
      _ = gB * gA * (gX⁻¹ * gB) * gB * gA * gB := by rw [gB_mul_gX]
      _ = gB * (gA * gX⁻¹) * gY * gA * gB := by simp only [gY, mul_assoc]
      _ = gB * (gX⁻¹ * gA) * gY * gA * gB := by rw [gA_mul_gX_inv]
      _ = gB * gX⁻¹ * (gA * gY) * gA * gB := by simp only [mul_assoc]
      _ = gB * gX⁻¹ * (gY⁻¹ * gA) * gA * gB := by rw [gA_mul_gY]
      _ = (gB * gX⁻¹) * gY⁻¹ * gX * gB := by simp only [gX, mul_assoc]
      _ = (gX * gB) * gY⁻¹ * gX * gB := by rw [gB_mul_gX_inv]
      _ = gX * (gB * gY⁻¹) * gX * gB := by simp only [mul_assoc]
      _ = gX * (gY⁻¹ * gB) * gX * gB := by rw [gB_mul_gY_inv]
      _ = gX * gY⁻¹ * (gB * gX) * gB := by simp only [mul_assoc]
      _ = gX * gY⁻¹ * (gX⁻¹ * gB) * gB := by rw [gB_mul_gX]
      _ = gX * gY⁻¹ * gX⁻¹ * gY := by simp only [gY, mul_assoc]
      _ = gX * gY⁻¹ * gX⁻¹ * (gX * gY * gX⁻¹) := by rw [gX_mul_gY]; group
      _ = 1 := by group
  calc gB * gZ = (gB * gZ * gB⁻¹ * gZ) * gZ⁻¹ * gB := by group
    _ = 1 * gZ⁻¹ * gB := by rw [hprod]
    _ = gZ⁻¹ * gB := by group

private lemma gA_mul_gZ_inv : gA * gZ⁻¹ = gZ * gA := by
  calc gA * gZ⁻¹ = gZ * (gZ⁻¹ * gA) * gZ⁻¹ := by group
    _ = gZ * (gA * gZ) * gZ⁻¹ := by rw [← gA_mul_gZ]
    _ = gZ * gA := by group

private lemma gB_mul_gZ_inv : gB * gZ⁻¹ = gZ * gB := by
  calc gB * gZ⁻¹ = gZ * (gZ⁻¹ * gB) * gZ⁻¹ := by group
    _ = gZ * (gB * gZ) * gZ⁻¹ := by rw [← gB_mul_gZ]
    _ = gZ * gB := by group

private lemma gX_mul_gZ : gX * gZ = gZ * gX := by
  calc gX * gZ = gA * (gA * gZ) := by simp only [gX, mul_assoc]
    _ = gA * (gZ⁻¹ * gA) := by rw [gA_mul_gZ]
    _ = (gA * gZ⁻¹) * gA := by simp only [mul_assoc]
    _ = (gZ * gA) * gA := by rw [gA_mul_gZ_inv]
    _ = gZ * gX := by simp only [gX, mul_assoc]

private lemma gY_mul_gZ : gY * gZ = gZ * gY := by
  calc gY * gZ = gB * (gB * gZ) := by simp only [gY, mul_assoc]
    _ = gB * (gZ⁻¹ * gB) := by rw [gB_mul_gZ]
    _ = (gB * gZ⁻¹) * gB := by simp only [mul_assoc]
    _ = (gZ * gB) * gB := by rw [gB_mul_gZ_inv]
    _ = gZ * gY := by simp only [gY, mul_assoc]

private lemma gB_mul_gA : gB * gA = gX⁻¹ * gY * gZ⁻¹ * gAB := by
  have h1 : gA⁻¹ = gX⁻¹ * gA := by simp only [gX]; group
  have h2 : gB⁻¹ = gY⁻¹ * gB := by simp only [gY]; group
  have hzy : gZ⁻¹ * gY = gY * gZ⁻¹ := by
    calc gZ⁻¹ * gY = gZ⁻¹ * (gY * gZ) * gZ⁻¹ := by group
      _ = gZ⁻¹ * (gZ * gY) * gZ⁻¹ := by rw [gY_mul_gZ]
      _ = gY * gZ⁻¹ := by group
  calc gB * gA = gA⁻¹ * gZ * gB⁻¹ := by simp only [gZ, gAB, mul_assoc]; group
    _ = gX⁻¹ * (gA * gZ) * (gY⁻¹ * gB) := by rw [h1, h2]; simp only [mul_assoc]
    _ = gX⁻¹ * (gZ⁻¹ * gA) * (gY⁻¹ * gB) := by rw [gA_mul_gZ]
    _ = gX⁻¹ * gZ⁻¹ * (gA * gY⁻¹) * gB := by simp only [mul_assoc]
    _ = gX⁻¹ * gZ⁻¹ * (gY * gA) * gB := by rw [gA_mul_gY_inv]
    _ = gX⁻¹ * (gZ⁻¹ * gY) * gAB := by simp only [gAB, mul_assoc]
    _ = gX⁻¹ * (gY * gZ⁻¹) * gAB := by rw [hzy]
    _ = gX⁻¹ * gY * gZ⁻¹ * gAB := by simp only [mul_assoc]

private lemma gA_mul_gAB : gA * gAB = gX * gB := by simp only [gAB, gX, mul_assoc]

private lemma gB_mul_gAB : gB * gAB = gX⁻¹ * gZ⁻¹ * gA := by
  have h : gZ⁻¹ * gY⁻¹ = gY⁻¹ * gZ⁻¹ := by
    calc gZ⁻¹ * gY⁻¹ = (gY * gZ)⁻¹ := by group
      _ = (gZ * gY)⁻¹ := by rw [gY_mul_gZ]
      _ = gY⁻¹ * gZ⁻¹ := by group
  calc gB * gAB = (gB * gA) * gB := by simp only [gAB, mul_assoc]
    _ = (gX⁻¹ * gY * gZ⁻¹ * gAB) * gB := by rw [gB_mul_gA]
    _ = gX⁻¹ * gY * gZ⁻¹ * (gA * gY) := by simp only [gAB, gY, mul_assoc]
    _ = gX⁻¹ * gY * gZ⁻¹ * (gY⁻¹ * gA) := by rw [gA_mul_gY]
    _ = gX⁻¹ * gY * (gZ⁻¹ * gY⁻¹) * gA := by simp only [mul_assoc]
    _ = gX⁻¹ * gY * (gY⁻¹ * gZ⁻¹) * gA := by rw [h]
    _ = gX⁻¹ * gZ⁻¹ * gA := by group

private lemma gAB_mul_gA : gAB * gA = gY⁻¹ * gZ * gB := by
  have h : gY⁻¹ * gX = gX * gY⁻¹ := by
    calc gY⁻¹ * gX = gY⁻¹ * (gX * gY) * gY⁻¹ := by group
      _ = gY⁻¹ * (gY * gX) * gY⁻¹ := by rw [gX_mul_gY]
      _ = gX * gY⁻¹ := by group
  calc gAB * gA = gA * (gB * gA) := by simp only [gAB, mul_assoc]
    _ = gA * (gX⁻¹ * gY * gZ⁻¹ * gAB) := by rw [gB_mul_gA]
    _ = (gA * gX⁻¹) * gY * gZ⁻¹ * gAB := by simp only [mul_assoc]
    _ = (gX⁻¹ * gA) * gY * gZ⁻¹ * gAB := by rw [gA_mul_gX_inv]
    _ = gX⁻¹ * (gA * gY) * gZ⁻¹ * gAB := by simp only [mul_assoc]
    _ = gX⁻¹ * (gY⁻¹ * gA) * gZ⁻¹ * gAB := by rw [gA_mul_gY]
    _ = gX⁻¹ * gY⁻¹ * (gA * gZ⁻¹) * gAB := by simp only [mul_assoc]
    _ = gX⁻¹ * gY⁻¹ * (gZ * gA) * gAB := by rw [gA_mul_gZ_inv]
    _ = gX⁻¹ * gY⁻¹ * gZ * (gA * gAB) := by simp only [mul_assoc]
    _ = gX⁻¹ * gY⁻¹ * gZ * (gX * gB) := by rw [gA_mul_gAB]
    _ = gX⁻¹ * gY⁻¹ * (gZ * gX) * gB := by simp only [mul_assoc]
    _ = gX⁻¹ * gY⁻¹ * (gX * gZ) * gB := by rw [gX_mul_gZ]
    _ = gX⁻¹ * (gY⁻¹ * gX) * gZ * gB := by simp only [mul_assoc]
    _ = gX⁻¹ * (gX * gY⁻¹) * gZ * gB := by rw [h]
    _ = gY⁻¹ * gZ * gB := by group

private lemma gAB_mul_gB : gAB * gB = gY⁻¹ * gA := by
  calc gAB * gB = gA * gY := by simp only [gAB, gY, mul_assoc]
    _ = gY⁻¹ * gA := gA_mul_gY

private lemma gAB_mul_gAB : gAB * gAB = gZ := rfl

private lemma conj_zpow_eq {g u : P} (h : g * u = u * g) (k : ℤ) :
    g * u ^ k = u ^ k * g := by
  have hc : Commute g u := h
  exact hc.zpow_right k

private lemma conj_zpow_inv {g u : P} (h : g * u = u⁻¹ * g) (k : ℤ) :
    g * u ^ k = u ^ (-k) * g := by
  have hconj : g * u * g⁻¹ = u⁻¹ := by rw [h]; group
  have hpow : g * u ^ k * g⁻¹ = u ^ (-k) := by
    calc g * u ^ k * g⁻¹ = (g * u * g⁻¹) ^ k := conj_zpow.symm
      _ = (u⁻¹) ^ k := by rw [hconj]
      _ = u ^ (-k) := by simp [zpow_neg]
  calc g * u ^ k = (g * u ^ k * g⁻¹) * g := by group
    _ = u ^ (-k) * g := by rw [hpow]

/- ### Free abelian subgroup `N = ℤ³` and group algebra `ℂ[P]` -/

private abbrev N := Multiplicative (ℤ × ℤ × ℤ)

private def mkN (i j k : ℤ) : N := Multiplicative.ofAdd (i, j, k)

private lemma mkN_mul (i₁ j₁ k₁ i₂ j₂ k₂ : ℤ) :
    mkN i₁ j₁ k₁ * mkN i₂ j₂ k₂ = mkN (i₁ + i₂) (j₁ + j₂) (k₁ + k₂) := rfl

private lemma mkN_one : mkN 0 0 0 = 1 := rfl

private def ι : N →* P where
  toFun n := let v := Multiplicative.toAdd n; gX ^ v.1 * gY ^ v.2.1 * gZ ^ v.2.2
  map_one' := by simp
  map_mul' n₁ n₂ := by
    rcases n₁ with ⟨i₁, j₁, k₁⟩; rcases n₂ with ⟨i₂, j₂, k₂⟩
    change gX ^ (i₁ + i₂) * gY ^ (j₁ + j₂) * gZ ^ (k₁ + k₂) =
      (gX ^ i₁ * gY ^ j₁ * gZ ^ k₁) * (gX ^ i₂ * gY ^ j₂ * gZ ^ k₂)
    have hxy : ∀ a b : ℤ, gY ^ b * gX ^ a = gX ^ a * gY ^ b := fun a b =>
      (Commute.zpow_zpow (gX_mul_gY.symm) b a)
    have hxz : ∀ a c : ℤ, gZ ^ c * gX ^ a = gX ^ a * gZ ^ c := fun a c =>
      (Commute.zpow_zpow (gX_mul_gZ.symm) c a)
    have hyz : ∀ b c : ℤ, gZ ^ c * gY ^ b = gY ^ b * gZ ^ c := fun b c =>
      (Commute.zpow_zpow (gY_mul_gZ.symm) c b)
    rw [zpow_add, zpow_add, zpow_add]
    calc gX ^ i₁ * gX ^ i₂ * (gY ^ j₁ * gY ^ j₂) * (gZ ^ k₁ * gZ ^ k₂)
        = gX ^ i₁ * (gX ^ i₂ * gY ^ j₁) * gY ^ j₂ * gZ ^ k₁ * gZ ^ k₂ := by simp only [mul_assoc]
      _ = gX ^ i₁ * (gY ^ j₁ * gX ^ i₂) * gY ^ j₂ * gZ ^ k₁ * gZ ^ k₂ := by rw [← hxy i₂ j₁]
      _ = gX ^ i₁ * gY ^ j₁ * gX ^ i₂ * (gY ^ j₂ * gZ ^ k₁) * gZ ^ k₂ := by simp only [mul_assoc]
      _ = gX ^ i₁ * gY ^ j₁ * gX ^ i₂ * (gZ ^ k₁ * gY ^ j₂) * gZ ^ k₂ := by rw [← hyz j₂ k₁]
      _ = gX ^ i₁ * gY ^ j₁ * (gX ^ i₂ * gZ ^ k₁) * gY ^ j₂ * gZ ^ k₂ := by simp only [mul_assoc]
      _ = gX ^ i₁ * gY ^ j₁ * (gZ ^ k₁ * gX ^ i₂) * gY ^ j₂ * gZ ^ k₂ := by rw [← hxz i₂ k₁]
      _ = (gX ^ i₁ * gY ^ j₁ * gZ ^ k₁) * (gX ^ i₂ * gY ^ j₂ * gZ ^ k₂) := by simp only [mul_assoc]

private def flipA : N →* N where
  toFun n := let v := Multiplicative.toAdd n; mkN v.1 (-v.2.1) (-v.2.2)
  map_one' := rfl
  map_mul' n₁ n₂ := by
    rcases n₁ with ⟨i₁, j₁, k₁⟩; rcases n₂ with ⟨i₂, j₂, k₂⟩
    change mkN (i₁ + i₂) (-(j₁ + j₂)) (-(k₁ + k₂)) = mkN (i₁ + i₂) (-j₁ + -j₂) (-k₁ + -k₂)
    congr 1; ring; ring

private def flipB : N →* N where
  toFun n := let v := Multiplicative.toAdd n; mkN (-v.1) v.2.1 (-v.2.2)
  map_one' := rfl
  map_mul' n₁ n₂ := by
    rcases n₁ with ⟨i₁, j₁, k₁⟩; rcases n₂ with ⟨i₂, j₂, k₂⟩
    change mkN (-(i₁ + i₂)) (j₁ + j₂) (-(k₁ + k₂)) = mkN (-i₁ + -i₂) (j₁ + j₂) (-k₁ + -k₂)
    congr 1; ring; ring

private def flipC : N →* N where
  toFun n := let v := Multiplicative.toAdd n; mkN (-v.1) (-v.2.1) v.2.2
  map_one' := rfl
  map_mul' n₁ n₂ := by
    rcases n₁ with ⟨i₁, j₁, k₁⟩; rcases n₂ with ⟨i₂, j₂, k₂⟩
    change mkN (-(i₁ + i₂)) (-(j₁ + j₂)) (k₁ + k₂) = mkN (-i₁ + -i₂) (-j₁ + -j₂) (k₁ + k₂)
    congr 1; ring; ring

private lemma gA_mul_ι (n : N) : gA * ι n = ι (flipA n) * gA := by
  rcases n with ⟨i, j, k⟩
  change gA * (gX ^ i * gY ^ j * gZ ^ k) = gX ^ i * gY ^ (-j) * gZ ^ (-k) * gA
  calc gA * (gX ^ i * gY ^ j * gZ ^ k)
      = (gA * gX ^ i) * gY ^ j * gZ ^ k := by simp only [mul_assoc]
    _ = (gX ^ i * gA) * gY ^ j * gZ ^ k := by rw [conj_zpow_eq gA_mul_gX i]
    _ = gX ^ i * (gA * gY ^ j) * gZ ^ k := by simp only [mul_assoc]
    _ = gX ^ i * (gY ^ (-j) * gA) * gZ ^ k := by rw [conj_zpow_inv gA_mul_gY j]
    _ = gX ^ i * gY ^ (-j) * (gA * gZ ^ k) := by simp only [mul_assoc]
    _ = gX ^ i * gY ^ (-j) * (gZ ^ (-k) * gA) := by rw [conj_zpow_inv gA_mul_gZ k]
    _ = gX ^ i * gY ^ (-j) * gZ ^ (-k) * gA := by simp only [mul_assoc]

private lemma gB_mul_ι (n : N) : gB * ι n = ι (flipB n) * gB := by
  rcases n with ⟨i, j, k⟩
  change gB * (gX ^ i * gY ^ j * gZ ^ k) = gX ^ (-i) * gY ^ j * gZ ^ (-k) * gB
  calc gB * (gX ^ i * gY ^ j * gZ ^ k)
      = (gB * gX ^ i) * gY ^ j * gZ ^ k := by simp only [mul_assoc]
    _ = (gX ^ (-i) * gB) * gY ^ j * gZ ^ k := by rw [conj_zpow_inv gB_mul_gX i]
    _ = gX ^ (-i) * (gB * gY ^ j) * gZ ^ k := by simp only [mul_assoc]
    _ = gX ^ (-i) * (gY ^ j * gB) * gZ ^ k := by rw [conj_zpow_eq gB_mul_gY j]
    _ = gX ^ (-i) * gY ^ j * (gB * gZ ^ k) := by simp only [mul_assoc]
    _ = gX ^ (-i) * gY ^ j * (gZ ^ (-k) * gB) := by rw [conj_zpow_inv gB_mul_gZ k]
    _ = gX ^ (-i) * gY ^ j * gZ ^ (-k) * gB := by simp only [mul_assoc]

private lemma gAB_mul_ι (n : N) : gAB * ι n = ι (flipC n) * gAB := by
  rcases n with ⟨i, j, k⟩
  have hflip : flipA (flipB (mkN i j k)) = flipC (mkN i j k) := by
    change mkN (-i) (-j) (-(-k)) = mkN (-i) (-j) k; simp
  calc gAB * ι (mkN i j k) = gA * (gB * ι (mkN i j k)) := by simp only [gAB, mul_assoc]
    _ = gA * (ι (flipB (mkN i j k)) * gB) := by rw [gB_mul_ι]
    _ = (gA * ι (flipB (mkN i j k))) * gB := by simp only [mul_assoc]
    _ = (ι (flipA (flipB (mkN i j k))) * gA) * gB := by rw [gA_mul_ι]
    _ = ι (flipC (mkN i j k)) * gAB := by rw [hflip]; simp only [gAB, mul_assoc]

private abbrev R := MonoidAlgebra ℂ N
private abbrev A := MonoidAlgebra ℂ P

private def embed : R →+* A := MonoidAlgebra.mapDomainRingHom ℂ ι
private def σA : R →+* R := MonoidAlgebra.mapDomainRingHom ℂ flipA
private def σB : R →+* R := MonoidAlgebra.mapDomainRingHom ℂ flipB
private def σC : R →+* R := MonoidAlgebra.mapDomainRingHom ℂ flipC

private def eA : A := MonoidAlgebra.single gA 1
private def eB : A := MonoidAlgebra.single gB 1
private def eAB : A := MonoidAlgebra.single gAB 1

private def rX : R := MonoidAlgebra.single (mkN 1 0 0) 1
private def rXi : R := MonoidAlgebra.single (mkN (-1) 0 0) 1
private def rY : R := MonoidAlgebra.single (mkN 0 1 0) 1
private def rYi : R := MonoidAlgebra.single (mkN 0 (-1) 0) 1
private def rZ : R := MonoidAlgebra.single (mkN 0 0 1) 1
private def rZi : R := MonoidAlgebra.single (mkN 0 0 (-1)) 1

private lemma rX_mul_rXi : rX * rXi = 1 := by
  simp [rX, rXi, MonoidAlgebra.single_mul_single, mkN_mul, mkN_one, MonoidAlgebra.one_def]

private lemma rY_mul_rYi : rY * rYi = 1 := by
  simp [rY, rYi, MonoidAlgebra.single_mul_single, mkN_mul, mkN_one, MonoidAlgebra.one_def]

private lemma rZ_mul_rZi : rZ * rZi = 1 := by
  simp [rZ, rZi, MonoidAlgebra.single_mul_single, mkN_mul, mkN_one, MonoidAlgebra.one_def]

private lemma embed_single (n : N) (c : ℂ) :
    embed (MonoidAlgebra.single n c) = MonoidAlgebra.single (ι n) c := by simp [embed]

private lemma σA_single (n : N) (c : ℂ) :
    σA (MonoidAlgebra.single n c) = MonoidAlgebra.single (flipA n) c := by simp [σA]

private lemma σB_single (n : N) (c : ℂ) :
    σB (MonoidAlgebra.single n c) = MonoidAlgebra.single (flipB n) c := by simp [σB]

private lemma σC_single (n : N) (c : ℂ) :
    σC (MonoidAlgebra.single n c) = MonoidAlgebra.single (flipC n) c := by simp [σC]

private lemma eA_mul_embed (f : R) : eA * embed f = embed (σA f) * eA := by
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂; simp only [map_add, mul_add, add_mul, h₁, h₂]
  · intro n c
    rw [embed_single, σA_single, embed_single]
    simp only [eA, MonoidAlgebra.single_mul_single, one_mul, mul_one, gA_mul_ι]

private lemma eB_mul_embed (f : R) : eB * embed f = embed (σB f) * eB := by
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂; simp only [map_add, mul_add, add_mul, h₁, h₂]
  · intro n c
    rw [embed_single, σB_single, embed_single]
    simp only [eB, MonoidAlgebra.single_mul_single, one_mul, mul_one, gB_mul_ι]

private lemma eAB_mul_embed (f : R) : eAB * embed f = embed (σC f) * eAB := by
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂; simp only [map_add, mul_add, add_mul, h₁, h₂]
  · intro n c
    rw [embed_single, σC_single, embed_single]
    simp only [eAB, MonoidAlgebra.single_mul_single, one_mul, mul_one, gAB_mul_ι]

private lemma eA_mul_eA : eA * eA = embed rX := by
  rw [rX, embed_single]; simp only [eA, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]; simp [gX]

private lemma eA_mul_eB : eA * eB = eAB := by
  simp [eA, eB, eAB, MonoidAlgebra.single_mul_single, gAB]

private lemma eA_mul_eAB : eA * eAB = embed rX * eB := by
  rw [rX, embed_single]; simp only [eA, eB, eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gA_mul_gAB]

private lemma eB_mul_eA : eB * eA = embed (rXi * rY * rZi) * eAB := by
  have h1 : rXi * rY * rZi = MonoidAlgebra.single (mkN (-1) 1 (-1)) 1 := by
    simp [rXi, rY, rZi, MonoidAlgebra.single_mul_single, mkN_mul]
  rw [h1, embed_single]; simp only [eA, eB, eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gB_mul_gA]

private lemma eB_mul_eB : eB * eB = embed rY := by
  rw [rY, embed_single]; simp only [eB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]; simp [gY]

private lemma eB_mul_eAB : eB * eAB = embed (rXi * rZi) * eA := by
  have h1 : rXi * rZi = MonoidAlgebra.single (mkN (-1) 0 (-1)) 1 := by
    simp [rXi, rZi, MonoidAlgebra.single_mul_single, mkN_mul]
  rw [h1, embed_single]; simp only [eA, eB, eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gB_mul_gAB]

private lemma eAB_mul_eA : eAB * eA = embed (rYi * rZ) * eB := by
  have h1 : rYi * rZ = MonoidAlgebra.single (mkN 0 (-1) 1) 1 := by
    simp [rYi, rZ, MonoidAlgebra.single_mul_single, mkN_mul]
  rw [h1, embed_single]; simp only [eA, eB, eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gAB_mul_gA]

private lemma eAB_mul_eB : eAB * eB = embed rYi * eA := by
  rw [rYi, embed_single]; simp only [eA, eB, eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gAB_mul_gB]

private lemma eAB_mul_eAB : eAB * eAB = embed rZ := by
  rw [rZ, embed_single]; simp only [eAB, MonoidAlgebra.single_mul_single, one_mul, ι, mkN]
  simp [gAB_mul_gAB]

private def quad (p1 q1 r1 s1 : R) : A :=
  embed p1 + embed q1 * eA + embed r1 * eB + embed s1 * eAB

private lemma quad_one : quad 1 0 0 0 = 1 := by simp [quad]

private lemma quad_mul (p1 q1 r1 s1 p2 q2 r2 s2 : R) :
    quad p1 q1 r1 s1 * quad p2 q2 r2 s2 =
      quad
        (p1 * p2 + q1 * σA q2 * rX + r1 * σB r2 * rY + s1 * σC s2 * rZ)
        (p1 * q2 + q1 * σA p2 + r1 * σB s2 * (rXi * rZi) + s1 * σC r2 * rYi)
        (p1 * r2 + q1 * σA s2 * rX + r1 * σB p2 + s1 * σC q2 * (rYi * rZ))
        (p1 * s2 + q1 * σA r2 + r1 * σB q2 * (rXi * rY * rZi) + s1 * σC p2) := by
  unfold quad
  simp only [mul_add, add_mul]
  have hA1 : ∀ f g : R, embed f * eA * embed g = embed (f * σA g) * eA := by
    intro f g; rw [mul_assoc, eA_mul_embed, ← mul_assoc, ← map_mul]
  have hA2 : ∀ f g : R, embed f * eA * (embed g * eA) = embed (f * σA g * rX) := by
    intro f g; rw [← mul_assoc, hA1, mul_assoc, eA_mul_eA, ← map_mul]
  have hA3 : ∀ f g : R, embed f * eA * (embed g * eB) = embed (f * σA g) * eAB := by
    intro f g; rw [← mul_assoc, hA1, mul_assoc, eA_mul_eB]
  have hA4 : ∀ f g : R, embed f * eA * (embed g * eAB) = embed (f * σA g * rX) * eB := by
    intro f g; rw [← mul_assoc, hA1, mul_assoc, eA_mul_eAB, ← mul_assoc, ← map_mul]
  have hB1 : ∀ f g : R, embed f * eB * embed g = embed (f * σB g) * eB := by
    intro f g; rw [mul_assoc, eB_mul_embed, ← mul_assoc, ← map_mul]
  have hB2 : ∀ f g : R, embed f * eB * (embed g * eA) = embed (f * σB g * (rXi * rY * rZi)) * eAB := by
    intro f g; rw [← mul_assoc, hB1, mul_assoc, eB_mul_eA, ← mul_assoc, ← map_mul]
  have hB3 : ∀ f g : R, embed f * eB * (embed g * eB) = embed (f * σB g * rY) := by
    intro f g; rw [← mul_assoc, hB1, mul_assoc, eB_mul_eB, ← map_mul]
  have hB4 : ∀ f g : R, embed f * eB * (embed g * eAB) = embed (f * σB g * (rXi * rZi)) * eA := by
    intro f g; rw [← mul_assoc, hB1, mul_assoc, eB_mul_eAB, ← mul_assoc, ← map_mul]
  have hC1 : ∀ f g : R, embed f * eAB * embed g = embed (f * σC g) * eAB := by
    intro f g; rw [mul_assoc, eAB_mul_embed, ← mul_assoc, ← map_mul]
  have hC2 : ∀ f g : R, embed f * eAB * (embed g * eA) = embed (f * σC g * (rYi * rZ)) * eB := by
    intro f g; rw [← mul_assoc, hC1, mul_assoc, eAB_mul_eA, ← mul_assoc, ← map_mul]
  have hC3 : ∀ f g : R, embed f * eAB * (embed g * eB) = embed (f * σC g * rYi) * eA := by
    intro f g; rw [← mul_assoc, hC1, mul_assoc, eAB_mul_eB, ← mul_assoc, ← map_mul]
  have hC4 : ∀ f g : R, embed f * eAB * (embed g * eAB) = embed (f * σC g * rZ) := by
    intro f g; rw [← mul_assoc, hC1, mul_assoc, eAB_mul_eAB, ← map_mul]
  simp only [hA1, hA2, hA3, hA4, hB1, hB2, hB3, hB4, hC1, hC2, hC3, hC4,
    ← mul_assoc, ← map_mul, map_add, add_mul]
  abel

/- ### Gardam's complex unit and inverse -/

private def cScalar (c : ℂ) : R := MonoidAlgebra.single (1 : N) c

private lemma cScalar_mul (c₁ c₂ : ℂ) : cScalar c₁ * cScalar c₂ = cScalar (c₁ * c₂) := by
  simp [cScalar, MonoidAlgebra.single_mul_single]

private lemma cScalar_one : cScalar 1 = 1 := by simp [cScalar, MonoidAlgebra.one_def]

private lemma cScalar_neg (c : ℂ) : cScalar (-c) = -cScalar c := by simp [cScalar]

private lemma σA_cScalar (c : ℂ) : σA (cScalar c) = cScalar c := by
  rw [cScalar, σA_single]; rfl

private lemma σB_cScalar (c : ℂ) : σB (cScalar c) = cScalar c := by
  rw [cScalar, σB_single]; rfl

private lemma σC_cScalar (c : ℂ) : σC (cScalar c) = cScalar c := by
  rw [cScalar, σC_single]; rfl

@[local simp] private lemma σA_rX : σA rX = rX := by simp [σA_single, rX, flipA, mkN]
@[local simp] private lemma σA_rXi : σA rXi = rXi := by simp [σA_single, rXi, flipA, mkN]
@[local simp] private lemma σA_rY : σA rY = rYi := by simp [σA_single, rY, rYi, flipA, mkN]
@[local simp] private lemma σA_rYi : σA rYi = rY := by simp [σA_single, rY, rYi, flipA, mkN]
@[local simp] private lemma σA_rZ : σA rZ = rZi := by simp [σA_single, rZ, rZi, flipA, mkN]
@[local simp] private lemma σA_rZi : σA rZi = rZ := by simp [σA_single, rZ, rZi, flipA, mkN]

@[local simp] private lemma σB_rX : σB rX = rXi := by simp [σB_single, rX, rXi, flipB, mkN]
@[local simp] private lemma σB_rXi : σB rXi = rX := by simp [σB_single, rX, rXi, flipB, mkN]
@[local simp] private lemma σB_rY : σB rY = rY := by simp [σB_single, rY, flipB, mkN]
@[local simp] private lemma σB_rYi : σB rYi = rYi := by simp [σB_single, rYi, flipB, mkN]
@[local simp] private lemma σB_rZ : σB rZ = rZi := by simp [σB_single, rZ, rZi, flipB, mkN]
@[local simp] private lemma σB_rZi : σB rZi = rZ := by simp [σB_single, rZ, rZi, flipB, mkN]

@[local simp] private lemma σC_rX : σC rX = rXi := by simp [σC_single, rX, rXi, flipC, mkN]
@[local simp] private lemma σC_rXi : σC rXi = rX := by simp [σC_single, rX, rXi, flipC, mkN]
@[local simp] private lemma σC_rY : σC rY = rYi := by simp [σC_single, rY, rYi, flipC, mkN]
@[local simp] private lemma σC_rYi : σC rYi = rY := by simp [σC_single, rY, rYi, flipC, mkN]
@[local simp] private lemma σC_rZ : σC rZ = rZ := by simp [σC_single, rZ, flipC, mkN]
@[local simp] private lemma σC_rZi : σC rZi = rZi := by simp [σC_single, rZi, flipC, mkN]

private def wC : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)
private def wiC : ℂ := (1 - Complex.I) / (Real.sqrt 2 : ℂ)

private lemma sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

private lemma sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := sqrt2_sq
  rw [h] at this
  norm_num at this

private lemma wC_mul_wiC : wC * wiC = 1 := by
  unfold wC wiC
  field_simp [sqrt2_ne]
  rw [sqrt2_sq]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma wC_mul_wC : wC * wC = Complex.I := by
  unfold wC
  field_simp [sqrt2_ne]
  rw [sqrt2_sq]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma wiC_mul_wiC : wiC * wiC = -Complex.I := by
  unfold wiC
  field_simp [sqrt2_ne]
  rw [sqrt2_sq]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma wiC_eq : wiC = -Complex.I * wC := by
  unfold wC wiC
  field_simp [sqrt2_ne]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma wC_eq : wC = Complex.I * wiC := by
  unfold wC wiC
  field_simp [sqrt2_ne]
  ring_nf
  rw [Complex.I_sq]
  ring

private def cI : R := cScalar Complex.I
private def cw : R := cScalar wC
private def cwi : R := cScalar wiC

@[local simp] private lemma σA_cI : σA cI = cI := σA_cScalar _
@[local simp] private lemma σB_cI : σB cI = cI := σB_cScalar _
@[local simp] private lemma σC_cI : σC cI = cI := σC_cScalar _
@[local simp] private lemma σA_cw : σA cw = cw := σA_cScalar _
@[local simp] private lemma σB_cw : σB cw = cw := σB_cScalar _
@[local simp] private lemma σC_cw : σC cw = cw := σC_cScalar _
@[local simp] private lemma σA_cwi : σA cwi = cwi := σA_cScalar _
@[local simp] private lemma σB_cwi : σB cwi = cwi := σB_cScalar _
@[local simp] private lemma σC_cwi : σC cwi = cwi := σC_cScalar _

private lemma cI_sq : cI * cI = -1 := by
  rw [cI, cScalar_mul, Complex.I_mul_I, cScalar_neg, cScalar_one]

private lemma cw_mul_cwi : cw * cwi = 1 := by
  rw [cw, cwi, cScalar_mul, wC_mul_wiC, cScalar_one]

private lemma cw_mul_cw : cw * cw = cI := by
  rw [cw, cI, cScalar_mul, wC_mul_wC]

private lemma cwi_mul_cwi : cwi * cwi = -cI := by
  rw [cwi, cI, cScalar_mul, wiC_mul_wiC, cScalar_neg]

private lemma cwi_eq : cwi = -cI * cw := by
  rw [cwi, cI, cw, ← cScalar_neg, cScalar_mul, ← wiC_eq]

private lemma cw_eq : cw = cI * cwi := by
  rw [cw, cI, cwi, cScalar_mul, ← wC_eq]

private def uP : R := 1 - cI * rX + cI * rY + rX * rY - (1 + cI * rX - cI * rY + rX * rY) * rZi
private def uQ : R := rXi * rYi - cI * rX + cI * rYi * rZ - rZ
private def uR : R := 1 + cI * rX - cI * rYi * rZ - rX * rY * rZ
private def uS : R := 1 + cI * (rX - rXi - rY + rYi) * rZi

private def vP : R := cI * rXi + 1 + rXi * rYi - cI * rYi - (-cI * rXi + 1 + rXi * rYi + cI * rYi) * rZ
private def vQ : R := cI * rXi * rXi * rYi - 1 + rXi * rYi * rZ - cI * rXi * rZ
private def vR : R := -cI * rYi - rX * rYi + rYi * rYi * rZ + cI * rX * rZ
private def vS : R := rZi + cI * (rX - rXi + rYi - rY)

private def unitU : A := quad uP (cw * uQ) (cwi * uR) uS
private def unitV : A := quad vP (cw * vQ) (cwi * vR) vS

/- ### Verification of `unitU * unitV = 1` and `unitV * unitU = 1` -/

private lemma uv_1 :
    uP * vP + (cw * uQ) * σA (cw * vQ) * rX + (cwi * uR) * σB (cwi * vR) * rY + uS * σC vS * rZ = 1 := by
  have hx := rX_mul_rXi; have hy := rY_mul_rYi; have hz := rZ_mul_rZi
  have hi := cI_sq; have hww := cw_mul_cw; have hwii := cwi_mul_cwi
  simp [uP, uQ, uR, uS, vP, vQ, vR, vS]; grind

private lemma uv_2 :
    uP * (cw * vQ) + (cw * uQ) * σA vP + (cwi * uR) * σB vS * (rXi * rZi) + uS * σC (cwi * vR) * rYi = 0 := by
  have hx := rX_mul_rXi; have hy := rY_mul_rYi; have hz := rZ_mul_rZi
  have hi := cI_sq; have hwi := cwi_eq
  simp [uP, uQ, uR, uS, vP, vQ, vR, vS]; grind

private lemma uv_3 :
    uP * (cwi * vR) + (cw * uQ) * σA vS * rX + (cwi * uR) * σB vP + uS * σC (cw * vQ) * (rYi * rZ) = 0 := by
  have hx := rX_mul_rXi; have hy := rY_mul_rYi; have hz := rZ_mul_rZi
  have hi := cI_sq; have hw := cw_eq
  simp [uP, uQ, uR, uS, vP, vQ, vR, vS]; grind

private lemma uv_4 :
    uP * vS + (cw * uQ) * σA (cwi * vR) + (cwi * uR) * σB (cw * vQ) * (rXi * rY * rZi) + uS * σC vP = 0 := by
  have hx := rX_mul_rXi; have hy := rY_mul_rYi; have hz := rZ_mul_rZi
  have hi := cI_sq; have hwwi := cw_mul_cwi
  simp [uP, uQ, uR, uS, vP, vQ, vR, vS]; grind

private lemma vu_1 :
    vP * uP + (cw * vQ) * σA (cw * uQ) * rX + (cwi * vR) * σB (cwi * uR) * rY + vS * σC uS * rZ = 1 := by
  have hx := rX_mul_rXi; have hy := rY_mul_rYi; have hz := rZ_mul_rZi
  have hi := cI_sq; have hww := cw_mul_cw; have hwii := cwi_mul_cwi
  simp [uP, uQ, uR, uS, vP, vQ, vR, vS]; grind

private lemma vu_2 :
    vP * (cw * uQ) + (cw * vQ) * σA uP + (cwi * vR) * σB uS * (rXi * rZi) + vS * σC (cwi * uR) * rYi = 0 := by
  have hx := rX_mul_rXi; have hy := rY_mul_rYi; have hz := rZ_mul_rZi
  have hi := cI_sq; have hwi := cwi_eq
  simp [uP, uQ, uR, uS, vP, vQ, vR, vS]; grind

private lemma vu_3 :
    vP * (cwi * uR) + (cw * vQ) * σA uS * rX + (cwi * vR) * σB uP + vS * σC (cw * uQ) * (rYi * rZ) = 0 := by
  have hx := rX_mul_rXi; have hy := rY_mul_rYi; have hz := rZ_mul_rZi
  have hi := cI_sq; have hw := cw_eq
  simp [uP, uQ, uR, uS, vP, vQ, vR, vS]; grind

private lemma vu_4 :
    vP * uS + (cw * vQ) * σA (cwi * uR) + (cwi * vR) * σB (cw * uQ) * (rXi * rY * rZi) + vS * σC uP = 0 := by
  have hx := rX_mul_rXi; have hy := rY_mul_rYi; have hz := rZ_mul_rZi
  have hi := cI_sq; have hwwi := cw_mul_cwi
  simp [uP, uQ, uR, uS, vP, vQ, vR, vS]; grind

private lemma unitU_mul_unitV : unitU * unitV = 1 := by
  rw [unitU, unitV, quad_mul, uv_1, uv_2, uv_3, uv_4, quad_one]

private lemma unitV_mul_unitU : unitV * unitU = 1 := by
  rw [unitU, unitV, quad_mul, vu_1, vu_2, vu_3, vu_4, quad_one]

/- ### Non-triviality via the crystallographic action on `ℤ³` -/

private def actA : Equiv.Perm (ℤ × ℤ × ℤ) where
  toFun v := (v.1 + 1, -v.2.1, -v.2.2)
  invFun v := (v.1 - 1, -v.2.1, -v.2.2)
  left_inv v := by rcases v with ⟨x, y, z⟩; simp
  right_inv v := by rcases v with ⟨x, y, z⟩; simp

private def actB : Equiv.Perm (ℤ × ℤ × ℤ) where
  toFun v := (-v.1, v.2.1 + 1, 1 - v.2.2)
  invFun v := (-v.1, v.2.1 - 1, 1 - v.2.2)
  left_inv v := by rcases v with ⟨x, y, z⟩; simp
  right_inv v := by rcases v with ⟨x, y, z⟩; simp

private def φ : P →* Equiv.Perm (ℤ × ℤ × ℤ) :=
  PresentedGroup.toGroup (f := fun i : Fin 2 => if i = 0 then actA else actB) (by
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      ext ⟨x, y, z⟩ <;> (simp [actA, actB, show (1 : Fin 2) ≠ 0 by decide]; try omega)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      ext ⟨x, y, z⟩ <;> (simp [actA, actB, show (1 : Fin 2) ≠ 0 by decide]; try omega))

private lemma φ_gA : φ gA = actA := by
  simp [φ, gA, PresentedGroup.toGroup.of]

private lemma φ_gB : φ gB = actB := by
  simp [φ, gB, PresentedGroup.toGroup.of]

private lemma φ_gX_apply (v : ℤ × ℤ × ℤ) : φ gX v = (v.1 + 2, v.2.1, v.2.2) := by
  rcases v with ⟨x, y, z⟩
  simp [gX, map_mul, φ_gA, actA]
  omega

private lemma φ_gY_apply (v : ℤ × ℤ × ℤ) : φ gY v = (v.1, v.2.1 + 2, v.2.2) := by
  rcases v with ⟨x, y, z⟩
  simp [gY, map_mul, φ_gB, actB]
  omega

private lemma φ_gAB_apply (v : ℤ × ℤ × ℤ) : φ gAB v = (1 - v.1, -1 - v.2.1, v.2.2 - 1) := by
  rcases v with ⟨x, y, z⟩
  simp [gAB, map_mul, φ_gA, φ_gB, actA, actB]
  omega

private lemma φ_gZ_apply (v : ℤ × ℤ × ℤ) : φ gZ v = (v.1, v.2.1, v.2.2 - 2) := by
  rcases v with ⟨x, y, z⟩
  simp [gZ, map_mul, φ_gAB_apply]
  omega

private lemma perm_apply_inv (f : Equiv.Perm (ℤ × ℤ × ℤ)) (w : ℤ × ℤ × ℤ) : f (f⁻¹ w) = w := by
  change (f * f⁻¹) w = w
  rw [mul_inv_cancel]; rfl

private lemma φ_gX_zpow (k : ℤ) (v : ℤ × ℤ × ℤ) :
    (φ gX ^ k) v = (v.1 + 2 * k, v.2.1, v.2.2) := by
  induction k using Int.induction_on generalizing v with
  | zero => rcases v with ⟨x, y, z⟩; simp
  | succ n ih =>
    have h1 : (φ gX ^ ((n : ℤ) + 1)) v = φ gX ((φ gX ^ (n : ℤ)) v) := by
      rw [add_comm, zpow_one_add]; rfl
    rw [h1, ih, φ_gX_apply]
    exact Prod.ext (by dsimp; omega) (Prod.ext rfl rfl)
  | pred n ih =>
    have hinv : ∀ w : ℤ × ℤ × ℤ, (φ gX)⁻¹ w = (w.1 - 2, w.2.1, w.2.2) := by
      intro w; apply (φ gX).injective
      rw [perm_apply_inv, φ_gX_apply]; rcases w with ⟨x, y, z⟩
      exact Prod.ext (by dsimp; omega) (Prod.ext rfl rfl)
    have h1 : (φ gX ^ (-(n : ℤ) - 1)) v = (φ gX)⁻¹ ((φ gX ^ (-(n : ℤ))) v) := by
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one]; rfl
    rw [h1, ih, hinv]
    exact Prod.ext (by dsimp; omega) (Prod.ext rfl rfl)

private lemma φ_gY_zpow (k : ℤ) (v : ℤ × ℤ × ℤ) :
    (φ gY ^ k) v = (v.1, v.2.1 + 2 * k, v.2.2) := by
  induction k using Int.induction_on generalizing v with
  | zero => rcases v with ⟨x, y, z⟩; simp
  | succ n ih =>
    have h1 : (φ gY ^ ((n : ℤ) + 1)) v = φ gY ((φ gY ^ (n : ℤ)) v) := by
      rw [add_comm, zpow_one_add]; rfl
    rw [h1, ih, φ_gY_apply]
    exact Prod.ext rfl (Prod.ext (by dsimp; omega) rfl)
  | pred n ih =>
    have hinv : ∀ w : ℤ × ℤ × ℤ, (φ gY)⁻¹ w = (w.1, w.2.1 - 2, w.2.2) := by
      intro w; apply (φ gY).injective
      rw [perm_apply_inv, φ_gY_apply]; rcases w with ⟨x, y, z⟩
      exact Prod.ext rfl (Prod.ext (by dsimp; omega) rfl)
    have h1 : (φ gY ^ (-(n : ℤ) - 1)) v = (φ gY)⁻¹ ((φ gY ^ (-(n : ℤ))) v) := by
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one]; rfl
    rw [h1, ih, hinv]
    exact Prod.ext rfl (Prod.ext (by dsimp; omega) rfl)

private lemma φ_gZ_zpow (k : ℤ) (v : ℤ × ℤ × ℤ) :
    (φ gZ ^ k) v = (v.1, v.2.1, v.2.2 - 2 * k) := by
  induction k using Int.induction_on generalizing v with
  | zero => rcases v with ⟨x, y, z⟩; simp
  | succ n ih =>
    have h1 : (φ gZ ^ ((n : ℤ) + 1)) v = φ gZ ((φ gZ ^ (n : ℤ)) v) := by
      rw [add_comm, zpow_one_add]; rfl
    rw [h1, ih, φ_gZ_apply]
    exact Prod.ext rfl (Prod.ext rfl (by dsimp; omega))
  | pred n ih =>
    have hinv : ∀ w : ℤ × ℤ × ℤ, (φ gZ)⁻¹ w = (w.1, w.2.1, w.2.2 + 2) := by
      intro w; apply (φ gZ).injective
      rw [perm_apply_inv, φ_gZ_apply]; rcases w with ⟨x, y, z⟩
      exact Prod.ext rfl (Prod.ext rfl (by dsimp; omega))
    have h1 : (φ gZ ^ (-(n : ℤ) - 1)) v = (φ gZ)⁻¹ ((φ gZ ^ (-(n : ℤ))) v) := by
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one]; rfl
    rw [h1, ih, hinv]
    exact Prod.ext rfl (Prod.ext rfl (by dsimp; omega))

private lemma φ_ι_apply (i j k : ℤ) (v : ℤ × ℤ × ℤ) :
    φ (ι (mkN i j k)) v = (v.1 + 2 * i, v.2.1 + 2 * j, v.2.2 - 2 * k) := by
  change (φ (gX ^ i * gY ^ j * gZ ^ k)) v = _
  simp only [map_mul, map_zpow, Equiv.Perm.mul_apply, φ_gX_zpow, φ_gY_zpow, φ_gZ_zpow]

private lemma φ_ι_injective : Function.Injective (fun n : N => φ (ι n)) := by
  rintro ⟨i₁, j₁, k₁⟩ ⟨i₂, j₂, k₂⟩ h
  have h0 := congr_arg (fun f : Equiv.Perm (ℤ × ℤ × ℤ) => f (0, 0, 0)) h
  change φ (ι (mkN i₁ j₁ k₁)) (0, 0, 0) = φ (ι (mkN i₂ j₂ k₂)) (0, 0, 0) at h0
  rw [φ_ι_apply, φ_ι_apply] at h0
  simp only [Prod.mk.injEq] at h0
  change mkN i₁ j₁ k₁ = mkN i₂ j₂ k₂
  congr 1 <;> omega

private def linear_diff (f : Equiv.Perm (ℤ × ℤ × ℤ)) : ℤ × ℤ × ℤ :=
  let a := f (1, 1, 1); let b := f (0, 0, 0)
  (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)

private lemma diff_φ_ι (n : N) : linear_diff (φ (ι n)) = (1, 1, 1) := by
  rcases n with ⟨i, j, k⟩
  change linear_diff (φ (ι (mkN i j k))) = (1, 1, 1)
  simp only [linear_diff, φ_ι_apply]
  exact Prod.ext (by dsimp; omega) (Prod.ext (by dsimp; omega) (by dsimp; omega))

private lemma diff_φ_ι_gA (n : N) : linear_diff (φ (ι n * gA)) = (1, -1, -1) := by
  rcases n with ⟨i, j, k⟩
  change linear_diff (φ (ι (mkN i j k) * gA)) = (1, -1, -1)
  simp [linear_diff, map_mul, φ_gA, actA, φ_ι_apply]

private lemma diff_φ_ι_gB (n : N) : linear_diff (φ (ι n * gB)) = (-1, 1, -1) := by
  rcases n with ⟨i, j, k⟩
  change linear_diff (φ (ι (mkN i j k) * gB)) = (-1, 1, -1)
  simp [linear_diff, map_mul, φ_gB, actB, φ_ι_apply]; omega

private lemma diff_φ_ι_gAB (n : N) : linear_diff (φ (ι n * gAB)) = (-1, -1, 1) := by
  rcases n with ⟨i, j, k⟩
  change linear_diff (φ (ι (mkN i j k) * gAB)) = (-1, -1, 1)
  simp [linear_diff, map_mul, φ_gAB_apply, φ_ι_apply]; omega

private lemma mapDomain_φ_vanish (f : R) (g : P) (M : Equiv.Perm (ℤ × ℤ × ℤ))
    (hne : ∀ n : N, φ (ι n * g) ≠ M) :
    (MonoidAlgebra.mapDomainRingHom ℂ φ (embed f * MonoidAlgebra.single g 1)).coeff M = 0 := by
  classical
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂
    simp only [map_add, add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, h₁, h₂, add_zero]
  · intro n c
    rw [embed_single, MonoidAlgebra.single_mul_single, mul_one]
    simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (hne n)]

private lemma mapDomain_φ_embed_mul_eAB (f : R) (n₀ : N) :
    (MonoidAlgebra.mapDomainRingHom ℂ φ (embed f * eAB)).coeff (φ (ι n₀ * gAB)) = f.coeff n₀ := by
  classical
  have hinj : Function.Injective (fun n : N => φ (ι n * gAB)) := by
    intro n₁ n₂ h
    simp only [map_mul] at h
    exact φ_ι_injective (mul_right_cancel h)
  refine MonoidAlgebra.induction_linear f ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂
    simp only [map_add, add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, h₁, h₂]
  · intro n c
    rw [embed_single, eAB, MonoidAlgebra.single_mul_single, mul_one]
    simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, hinj.eq_iff]

private lemma uS_expanded :
    uS = MonoidAlgebra.single (mkN 0 0 0) 1 +
         MonoidAlgebra.single (mkN 1 0 (-1)) Complex.I +
         MonoidAlgebra.single (mkN (-1) 0 (-1)) (-Complex.I) +
         MonoidAlgebra.single (mkN 0 1 (-1)) (-Complex.I) +
         MonoidAlgebra.single (mkN 0 (-1) (-1)) Complex.I := by
  unfold uS cI cScalar rX rXi rY rYi rZi
  have h1 : (1 : R) = MonoidAlgebra.single (mkN 0 0 0) 1 := by simp [mkN_one, MonoidAlgebra.one_def]
  rw [h1]
  simp only [mul_add, mul_sub, add_mul, sub_mul, MonoidAlgebra.single_mul_single,
    mkN_mul, one_mul, mul_one]
  norm_num
  abel

private lemma uS_coeff_0 : uS.coeff (mkN 0 0 0) = 1 := by
  rw [uS_expanded]
  simp [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, mkN]

private lemma uS_coeff_1 : uS.coeff (mkN 1 0 (-1)) = Complex.I := by
  rw [uS_expanded]
  simp [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single, mkN]

private lemma unitU_not_trivial : ¬ IsTrivialUnit unitU := by
  classical
  rintro ⟨k, g, hg⟩
  let Ψ := MonoidAlgebra.mapDomainRingHom ℂ φ
  have hΨ_eval : ∀ n₀ : N, (Ψ unitU).coeff (φ (ι n₀ * gAB)) = uS.coeff n₀ := by
    intro n₀
    have hM := diff_φ_ι_gAB n₀
    have hP0 : (Ψ (embed uP)).coeff (φ (ι n₀ * gAB)) = 0 := by
      have h := mapDomain_φ_vanish uP 1 (φ (ι n₀ * gAB)) fun n heq => by
        rw [mul_one] at heq
        have h1 := diff_φ_ι n
        rw [heq, hM] at h1
        norm_num at h1
      rw [← MonoidAlgebra.one_def, mul_one] at h
      exact h
    have hQ0 : (Ψ (embed (cw * uQ) * eA)).coeff (φ (ι n₀ * gAB)) = 0 :=
      mapDomain_φ_vanish (cw * uQ) gA (φ (ι n₀ * gAB)) fun n heq => by
        have h1 := diff_φ_ι_gA n; rw [heq, hM] at h1; norm_num at h1
    have hR0 : (Ψ (embed (cwi * uR) * eB)).coeff (φ (ι n₀ * gAB)) = 0 :=
      mapDomain_φ_vanish (cwi * uR) gB (φ (ι n₀ * gAB)) fun n heq => by
        have h1 := diff_φ_ι_gB n; rw [heq, hM] at h1; norm_num at h1
    have hS := mapDomain_φ_embed_mul_eAB uS n₀
    simp only [unitU, quad, Ψ, map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [hP0, hQ0, hR0, hS]
    ring
  have h1 : (Ψ unitU).coeff (φ (ι (mkN 0 0 0) * gAB)) = 1 := by
    rw [hΨ_eval, uS_coeff_0]
  have h2 : (Ψ unitU).coeff (φ (ι (mkN 1 0 (-1)) * gAB)) = Complex.I := by
    rw [hΨ_eval, uS_coeff_1]
  have htriv : Ψ unitU = MonoidAlgebra.single (φ g) (k : ℂ) := by
    rw [hg]; simp [Ψ]
  rw [htriv, MonoidAlgebra.coeff_single, Finsupp.single_apply] at h1 h2
  have heq1 : φ g = φ (ι (mkN 0 0 0) * gAB) := by
    by_contra hne
    rw [if_neg hne] at h1
    exact zero_ne_one h1
  have heq2 : φ g = φ (ι (mkN 1 0 (-1)) * gAB) := by
    by_contra hne
    rw [if_neg hne] at h2
    exact Complex.I_ne_zero h2.symm
  have hsame : φ (ι (mkN 0 0 0) * gAB) = φ (ι (mkN 1 0 (-1)) * gAB) := heq1.symm.trans heq2
  simp only [map_mul] at hsame
  have hn_eq : mkN 0 0 0 = mkN 1 0 (-1) := φ_ι_injective (mul_right_cancel hsame)
  have hadd := congr_arg Multiplicative.toAdd hn_eq
  simp [mkN] at hadd

end

end KaplanskyUnitComplex

open Kaplansky KaplanskyUnitComplex

theorem OMA.solution : type_of% @Kaplansky.UnitConjecture.counterexamples.ii :=
  ⟨⟨unitU, unitV, unitU_mul_unitV, unitV_mul_unitU⟩, unitU_not_trivial⟩
