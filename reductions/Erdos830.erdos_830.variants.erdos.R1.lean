import FormalConjectures.ErdosProblems.«830»

/-! The density-zero argument in Erdős, *On amicable numbers* (1955), pp. 109–111.
The three inputs concern all positive integers and can be proved independently. -/

namespace OMA.R_Erdos830_erdos_830_variants_erdos_R1

open scoped ArithmeticFunction.sigma Classical
open Finset Filter Erdos830 Asymptotics

/-- Every fixed positive integer divides the divisor sum almost everywhere (Erdős, Lemma 2). -/
def H1 : Prop := ∀ m : ℕ, 0 < m → ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
  (((Icc 1 N).filter (fun n => ¬ m ∣ σ 1 n)).card:ℝ) ≤ ε*N

/-- The contribution from divisors above B is small in density (Erdős, Lemma 3). -/
def H2 : Prop := ∀ η ε : ℝ, 0<η → 0<ε → ∃ B : ℕ, ∀ᶠ N : ℕ in atTop,
  (((Icc 1 N).filter (fun n => η ≤ ((σ 1 n : ℝ)/n) - (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d))).card:ℝ) ≤ ε*N

/-- Right continuity at 2 of the distribution of the abundancy ratio (Davenport). -/
def H3 : Prop := ∀ ε : ℝ, 0<ε → ∃ η : ℝ, 0<η ∧ ∀ᶠ N : ℕ in atTop,
  (((Icc 1 N).filter (fun n => 2 < ((σ 1 n : ℝ)/n) ∧ ((σ 1 n : ℝ)/n) ≤ 2+η)).card:ℝ) ≤ ε*N

lemma ratio_eq {n : ℕ} (hn : 0<n) : ((σ 1 n : ℝ)/n) = ∑ d ∈ n.divisors, (1:ℝ)/d := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [ArithmeticFunction.sigma_one_apply,Nat.cast_sum,← Nat.sum_div_divisors n (fun d => (d:ℝ)),Finset.sum_div]
  apply sum_congr rfl; intro d hd
  have hd' : (d:ℝ)≠0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd']
  field_simp

lemma compare {a b B : ℕ} (hb : 0<b) (ham : IsAmicable a b) (hfac : B.factorial ∣ σ 1 a) :
    (∑ d ∈ a.divisors.filter (· ≤ B), (1:ℝ)/d) ≤ (σ 1 b : ℝ)/b := by
  rw [ratio_eq hb]
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  intro d hd
  obtain ⟨hd,hB⟩ := mem_filter.mp hd
  have hda := Nat.dvd_of_mem_divisors hd
  have h := (Nat.dvd_factorial (Nat.pos_of_mem_divisors hd) hB).trans hfac
  rw [ham.left] at h
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_add_iff_right hda).mpr h,hb.ne'⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos830.erdos_830.variants.erdos := by
  intro h1 h2 h3
  let ratio (n : ℕ) : ℝ := (σ 1 n : ℝ)/n
  let partialRatio (B n : ℕ) : ℝ := ∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have hδ : 0 < ε/3 := by positivity
  obtain ⟨η,hη,hnear⟩ := h3 _ hδ
  obtain ⟨B,htail⟩ := h2 η _ hη hδ
  have hbad := h1 B.factorial (Nat.factorial_pos _) _ hδ
  filter_upwards [tendsto_nat_floor_atTop.eventually (hbad.and (htail.and hnear)),eventually_ge_atTop (0:ℝ)] with x hx hx0
  let N := ⌊x⌋₊
  let P := ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun q : ℕ × ℕ => q.1 ≤ q.2 ∧ IsAmicable q.1 q.2
  let E := (Icc 1 N).filter (fun n => ¬ B.factorial ∣ σ 1 n)
  let F := (Icc 1 N).filter (fun n => η ≤ ratio n - partialRatio B n)
  let G := (Icc 1 N).filter (fun n => 2 < ratio n ∧ ratio n ≤ 2+η)
  have maps : Set.MapsTo Prod.fst (P:Set (ℕ×ℕ)) (↑((E∪F)∪G):Set ℕ) := by
    rintro ⟨a,b⟩ hab
    obtain ⟨hm,hle,ham⟩ := mem_filter.mp hab
    obtain ⟨ha,hb⟩ := mem_product.mp hm
    by_cases hbad' : ¬ B.factorial ∣ σ 1 a
    · exact mem_union_left _ (mem_union_left _ (show a ∈ E by simpa only [E,mem_filter] using And.intro ha hbad'))
    by_cases hf : η ≤ ratio a - partialRatio B a
    · exact mem_union_left _ (mem_union_right _ (show a ∈ F by simpa only [F,mem_filter] using And.intro ha hf))
    apply mem_union_right _ (show a ∈ G from ?_)
    simp only [G,mem_filter]; refine ⟨ha,?_⟩
    have hapos := (mem_Icc.mp ha).1
    have hbpos := (mem_Icc.mp hb).1
    have hlt : a<b := lt_of_le_of_ne hle ham.ne
    have ha' : 0<(a:ℝ) := by exact_mod_cast hapos
    have hb' : 0<(b:ℝ) := by exact_mod_cast hbpos
    have hab' : (a:ℝ)<b := by exact_mod_cast hlt
    have hcmp : partialRatio B a ≤ ratio b := compare hbpos ham (not_not.mp hbad')
    have hupper : ratio b ≤ 2 := by
      dsimp only [ratio]
      rw [div_le_iff₀ hb',ham.right,Nat.cast_add]; linarith
    refine ⟨?_,by linarith [lt_of_not_ge hf]⟩
    dsimp only [ratio]
    rw [lt_div_iff₀ ha',ham.left,Nat.cast_add]; linarith
  have inj : Set.InjOn Prod.fst (P:Set (ℕ×ℕ)) := by
    rintro ⟨a,b⟩ hab ⟨a',b'⟩ hab' he
    change a=a' at he
    subst a'
    have h := (mem_filter.mp hab).2.2.left
    have h' := (mem_filter.mp hab').2.2.left
    exact Prod.ext rfl (Nat.add_left_cancel (h.symm.trans h'))
  have hbound := (card_le_card_of_injOn Prod.fst maps inj).trans (card_union_le _ _)
  have hnat : P.card ≤ E.card+F.card+G.card := hbound.trans (Nat.add_le_add_right (card_union_le _ _) _)
  rcases hx with ⟨he,hf,hg⟩
  change (E.card:ℝ) ≤ ε/3*N at he
  change (F.card:ℝ) ≤ ε/3*N at hf
  change (G.card:ℝ) ≤ ε/3*N at hg
  change ‖(P.card:ℝ)‖ ≤ ε*‖x‖
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg hx0]
  have hr : (P.card:ℝ) ≤ E.card+F.card+G.card := by exact_mod_cast hnat
  have hn : (N:ℝ)≤x := Nat.floor_le hx0
  nlinarith only [hr,he,hf,hg,mul_le_mul_of_nonneg_left hn hε.le]

end OMA.R_Erdos830_erdos_830_variants_erdos_R1
