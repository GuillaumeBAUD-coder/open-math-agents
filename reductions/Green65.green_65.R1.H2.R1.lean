import OMAReductions.R_Green65_green_65_R1
/-! Port of openai/math 3344da59991ed94f9ba711217b29c1d760badfa6 (OAI.Combinatorics.SquareDifference, Apache-2.0), adapted to the pinned Mathlib. -/
namespace OMA.R_Green65_green_65_R1_H2_R1
open Filter Finset
def H1 : Prop :=
  let H := 24; let T := 80
  let V := Fin (2*T+1) → Equiv.Perm (Fin H)
  let M (k:ℕ):(q:ℕ) → [NeZero q] → ((V → ZMod q) → ℝ) → ℝ := fun q _ G =>
      ∑ S ∈ (univ:Finset (Fin (2*T+1))).powerset, let E := ({b // b ∉ S} → Equiv.Perm (Fin H)) × Fin ((H.factorial/2)^S.card)
      if S.card ≤ T+1 ∧ k ≤ S.card then (q:ℝ)^(-(S.card:ℝ)/16) *
        univ.expect fun Y:E → ZMod q => univ.expect fun i:V → Fin ((H.factorial/2)^S.card) =>
        (∏ e ∈ (by classical exact if S.card ≤ T then univ.filter fun e:E × E =>
            T+1 ≤ (univ.filter fun b => e.2.1 b = e.1.1 b * finRotate H).card else ∅),
          (by classical exact if Y e.2 - Y e.1 ≠ 0 ∧ IsSquare (Y e.2 - Y e.1) then (1:ℝ) else 0)) *
        Real.exp (1/2 * ∑ v, ∑ w, (∑ b ∈ S, ∑ π:{π:Fin H × Fin H // π.1 < π.2},
            if w = Function.update v b (v b * Equiv.swap π.1.1 π.1.2) then (1/(10*(H:ℝ)^2))^(π.1.2.val - π.1.1.val) else 0) *
          if i v = i w then 1 else 0) *
        G fun v => Y (fun b => v b.1, i v)
      else 0
  ∀ᶠ q:ℕ in atTop, ∀ (_:q.Prime) [NeZero q], (M 0 q fun _ => 1)⁻¹ * M (T+1) q (fun _ => 1) ≤ 1/(q:ℝ)^4
def H2 : Prop :=
  let H := 24; let T := 80
  let V := Fin (2*T+1) → Equiv.Perm (Fin H)
  let M (k:ℕ):(q:ℕ) → [NeZero q] → ((V → ZMod q) → ℝ) → ℝ := fun q _ G =>
      ∑ S ∈ (univ:Finset (Fin (2*T+1))).powerset, let E := ({b // b ∉ S} → Equiv.Perm (Fin H)) × Fin ((H.factorial/2)^S.card)
      if S.card ≤ T+1 ∧ k ≤ S.card then (q:ℝ)^(-(S.card:ℝ)/16) *
        univ.expect fun Y:E → ZMod q => univ.expect fun i:V → Fin ((H.factorial/2)^S.card) =>
        (∏ e ∈ (by classical exact if S.card ≤ T then univ.filter fun e:E × E =>
            T+1 ≤ (univ.filter fun b => e.2.1 b = e.1.1 b * finRotate H).card else ∅),
          (by classical exact if Y e.2 - Y e.1 ≠ 0 ∧ IsSquare (Y e.2 - Y e.1) then (1:ℝ) else 0)) *
        Real.exp (1/2 * ∑ v, ∑ w, (∑ b ∈ S, ∑ π:{π:Fin H × Fin H // π.1 < π.2},
            if w = Function.update v b (v b * Equiv.swap π.1.1 π.1.2) then (1/(10*(H:ℝ)^2))^(π.1.2.val - π.1.1.val) else 0) *
          if i v = i w then 1 else 0) *
        G fun v => Y (fun b => v b.1, i v)
      else 0
  ∀ᶠ P:ℕ in atTop, ∃ a D:ℝ, 0<a ∧ 1≤D ∧ ∀ N:ℕ, 1≤N → ∀ B:Finset ℕ,
  (Icc P N).filter Nat.Prime ⊆ B → ∀ (hb : ∀ q ∈ B, P ≤ q ∧ q.Prime),
  (∀ q∈B, ∀ [NeZero q], (M 0 q fun _ => 1)⁻¹ * M (T+1) q (fun _ => 1) ≤ 1/(q:ℝ)^4) → ∀ A:Finset ℕ, A⊆range N → (∀ x ∈ A, ∀ y ∈ A, ∀ m : ℕ, 1 ≤ m → y ≠ x + m^2) →
  let J := ↥B
  letI:∀ j:J,NeZero j.1 := fun j => ⟨(hb j j.2).2.ne_zero⟩
  let g:(∀ j:J, ZMod j.1) → ℝ := fun x => ∑ U ∈ univ.filter (fun U:Finset J => ∏ j ∈ U, j.1 ≤ ⌊(N:ℝ)^(1/100000:ℝ)⌋₊),
      (N:ℝ)⁻¹ * ∑ n ∈ range N, (if n ∈ A then 1 else 0) * ∏ j ∈ U, ((if x j - n = 0 then (j.1:ℝ) else 0) - 1)
  (∑ z: ∀ j:J, V → ZMod j.1, (∏ j, (M 0 j.1 fun _ => 1)⁻¹ * M 0 j.1 fun y => if y = z j then 1 else 0) * ∏ v, g fun j => z j v) ≤ D*(N:ℝ)^(-a)
theorem main : H1 → H2 → OMA.R_Green65_green_65_R1.H2 := by
  intro hlocal hfamily
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp hlocal
  filter_upwards [hfamily,eventually_ge_atTop Q] with P hf hP
  obtain ⟨a,D,ha,hD,h⟩ := hf
  refine ⟨a,D,ha,hD,?_⟩
  intro N hN A hA hfree
  let B := (Icc P N).filter Nat.Prime
  have hb (q : ℕ) (hq : q∈B) := mem_filter.mp hq
  have h' := h N hN B Subset.rfl (fun q hq => ⟨(mem_Icc.mp (hb q hq).1).1,(hb q hq).2⟩)
    (fun q hq _ => hQ q (hP.trans (mem_Icc.mp (hb q hq).1).1) (hb q hq).2) A hA hfree
  simpa only [Nat.zero_le, and_true] using h'
end OMA.R_Green65_green_65_R1_H2_R1
