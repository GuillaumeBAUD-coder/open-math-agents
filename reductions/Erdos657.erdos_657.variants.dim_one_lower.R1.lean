import FormalConjectures.ErdosProblems.«657»
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

/-! Dumitrescu's logarithmic gain from Ruzsa modelling and quantitative Roth.
The model only has to preserve three-term progressions in the reverse direction.
For comparison, @Genbox's qualitative solution in project PR 1630 uses
triangle removal rather than a quantitative bound for integer progressions. -/

namespace OMA.R_Erdos657_erdos_657_variants_dim_one_lower_R1
open Finset Filter
open scoped Pointwise Classical

/-- Ruzsa modelling on the real line, with polynomial dependence on difference doubling. -/
def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (K : ℝ), 1 ≤ K → 0 < A.card →
    ((A - A).card : ℝ) ≤ K * A.card →
    ∃ (N : ℕ) (B : Finset ℕ) (g : ℕ → ℝ), B ⊆ range N ∧ A.card ≤ 4 * B.card ∧
      (N : ℝ) ≤ C * K ^ 8 * A.card ∧ Set.MapsTo g (B : Set ℕ) (A : Set ℝ) ∧
      Set.InjOn g (B : Set ℕ) ∧
      ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, a + c = b + b → g a + g c = g b + g b

/-- A finite quantitative Roth bound. The factor four in the logarithm also covers small intervals. -/
def H2 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : Finset ℕ), B ⊆ range N →
    ThreeAPFree (B : Set ℕ) → (B.card : ℝ) * Real.log (4 * (N : ℝ)) ≤ C * N

private theorem diffs (A : Finset ℝ) :
    (A - A).card ≤ 2 * (distinctDistances A + 1) := by
  classical
  let D := insert 0 (distanceSet A)
  let signed : Bool × ℝ → ℝ := fun v => if v.1 then v.2 else -v.2
  have hs : A - A ⊆ (univ ×ˢ D).image signed := by
    intro t ht
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_sub.mp ht
    have hab : |x-y| ∈ D := by
      by_cases he : x=y
      · simp [D,he]
      · apply mem_insert_of_mem
        exact mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hx,hy,he⟩,Real.dist_eq ..⟩
    rcases le_total y x with h|h
    · exact mem_image.mpr ⟨(true,|x-y|),mem_product.mpr ⟨mem_univ _,hab⟩,
        by simp [signed,abs_of_nonneg (sub_nonneg.mpr h)]⟩
    · exact mem_image.mpr ⟨(false,|x-y|),mem_product.mpr ⟨mem_univ _,hab⟩,
        by simp [signed,abs_of_nonpos (sub_nonpos.mpr h)]⟩
  calc
    _ ≤ _ := card_le_card hs
    _ ≤ (univ ×ˢ D : Finset (Bool × ℝ)).card := card_image_le
    _ = 2*D.card := by simp
    _ ≤ _ := Nat.mul_le_mul_left 2 (card_insert_le _ _)

private theorem no_progression {A : Finset ℝ} (h : (A : Set ℝ).IsIsoscelesFree) :
    ThreeAPFree (A : Set ℝ) := by
  intro a ha b hb c hc he
  by_contra hab
  have hac : a ≠ c := by intro e; apply hab; linarith
  have hbc : b ≠ c := by intro e; apply hab; linarith
  apply h ha hb hc hab hbc hac
  left
  rw [Real.dist_eq, Real.dist_eq, show a - b = b - c by linarith]

theorem main : H1 → H2 → type_of% @Erdos657.erdos_657.variants.dim_one_lower := by
  rintro ⟨C,hC,hmodel⟩ ⟨T,hT,hroth⟩
  let e : ℝ := 1 / 16
  have he : 0 < e := by norm_num [e]
  refine ⟨e,he,?_⟩
  have hg : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ e) atTop atTop :=
    (tendsto_rpow_atTop he).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hg.eventually_gt_atTop (1 + 4*T*C*3^8),eventually_ge_atTop 2] with n hn hn2
  intro A hA hiso
  let L := (Real.log (n : ℝ)) ^ e
  have hn' : 0 < (n : ℝ) := by positivity
  have hL : 1 ≤ L := by
    change 1 + 4*T*C*3^8 < L at hn
    linarith [show 0 < 4*T*C*3^8 by positivity]
  have hp : L ^ 16 = Real.log (n : ℝ) := by
    dsimp [L]
    rw [← Real.rpow_mul_natCast (Real.log_nonneg (x := (n : ℝ)) (by exact_mod_cast (show 1 ≤ n by omega)))]
    norm_num [e]
  by_contra! small
  have hD : ((A - A).card : ℝ) ≤ 3*L*A.card := by
    have hd : ((A - A).card : ℝ) ≤ 2 * ((distinctDistances A : ℝ) + 1) := by
      exact_mod_cast diffs A
    rw [hA]
    change (distinctDistances A : ℝ) < (n : ℝ)*L at small
    nlinarith [mul_le_mul_of_nonneg_left hL hn'.le, show (2:ℝ) ≤ n by exact_mod_cast hn2]
  obtain ⟨N,B,g,hsub,hcard,hsz,hm,hi,hap⟩ :=
    hmodel A (3*L) (by linarith) (by omega) hD
  have hb : ThreeAPFree (B : Set ℕ) := by
    intro a ha b hbb c hc habc
    exact hi ha hbb (no_progression hiso (hm ha) (hm hbb) (hm hc) (hap a ha b hbb c hc habc))
  rw [hA] at hsz hcard
  have hBN : B.card ≤ N := by simpa using card_le_card hsub
  have hlog : Real.log (n : ℝ) ≤ Real.log (4 * (N : ℝ)) :=
    Real.log_le_log hn' (by exact_mod_cast (show n ≤ 4*N by omega))
  have hsum : (n : ℝ)*Real.log n ≤ 4*T*C*(3*L)^8*n := calc
    _ ≤ (4*(B.card : ℝ))*Real.log (4*(N : ℝ)) :=
      mul_le_mul (by exact_mod_cast hcard) hlog (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) (by positivity)
    _ ≤ 4*(T*N) := by linarith [hroth N B hsub hb]
    _ ≤ 4*T*(C*(3*L)^8*n) := by nlinarith [mul_le_mul_of_nonneg_left hsz hT.le]
    _ = _ := by ring
  have hcancel : L^16 ≤ (4*T*C*3^8)*L^8 := by
    apply (le_of_mul_le_mul_right (a := (n : ℝ)) · hn')
    rw [hp]
    linarith only [show (n : ℝ)*Real.log n ≤ 4*T*C*(3*L)^8*n from hsum]
  have hpow : L ≤ L^8 := le_self_pow₀ hL (by decide)
  have h8 : 0 < L^8 := by positivity
  have hcoef : L^8 ≤ 4*T*C*3^8 := by
    apply (le_of_mul_le_mul_right (a := L^8) · h8)
    nlinarith only [hcancel, show L^8*L^8 = L^16 by ring]
  change 1 + 4*T*C*3^8 < L at hn
  linarith

end OMA.R_Erdos657_erdos_657_variants_dim_one_lower_R1
