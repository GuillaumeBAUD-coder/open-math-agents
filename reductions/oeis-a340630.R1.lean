import OMAStatements.S_oeis_a340630

/-!
# A340630 and the cost of the grid boundary

Credit: @connoranderson. Hugo van der Sanden gave the distinct-sums lower bound
and boundary argument in OEIS A340630. We use the four corner sums and rounding
modulo 10 to obtain the full bound without classifying nearby neighborhoods.
The remaining task is to construct grids at the lower bound in the two cases
for the permitted excess over the sum of the first n² nonnegative integers.
-/

namespace OMA.R_oeis_a340630_R1
open Finset OMA.S_oeis_a340630

private theorem distinct_lower (s : Finset ℕ) : s.card ^ 2 ≤ 2 * (∑ x ∈ s, x) + s.card := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hne : a ∉ s := fun h => (ha a h).false
    have hsub : s ⊆ range a := fun x hx => mem_range.mpr (ha x hx)
    have hcard := card_le_card hsub
    simp only [card_range] at hcard
    rw [sum_insert hne, card_insert_of_notMem hne]
    nlinarith

private theorem inj_lower {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (hf : Function.Injective f) : s.card ^ 2 ≤ 2 * (∑ x ∈ s, f x) + s.card := by
  have h := distinct_lower (s.image f)
  simpa only [card_image_of_injective _ hf, sum_image (fun _ _ _ _ h => hf h)] using h

private def direction {n : ℕ} (p q : Fin n × Fin n) : ℕ :=
  if q.1 < p.1 then 0 else if p.1 < q.1 then 1 else
  if q.2 < p.2 then 2 else if p.2 < q.2 then 3 else 4

private theorem dir_lt {n : ℕ} (p q : Fin n × Fin n) : direction p q < 5 := by
  unfold direction
  split_ifs <;> decide

private theorem dir_inj {n : ℕ} (p : Fin n × Fin n) :
    Set.InjOn (direction p) (vonNeumann n p) := by
  intro a ha b hb hab
  have ha := (Finset.mem_filter.mp (show a ∈ vonNeumann n p from ha)).2
  have hb := (Finset.mem_filter.mp (show b ∈ vonNeumann n p from hb)).2
  unfold Nat.dist at ha hb
  unfold direction at hab
  simp only [Fin.lt_def] at hab
  apply Prod.ext <;> apply Fin.ext <;> split_ifs at hab <;> omega

private theorem hood_size {n : ℕ} (p : Fin n × Fin n) : (vonNeumann n p).card ≤ 5 := by
  simpa using card_le_card_of_injOn (t := range 5) (direction p)
    (fun q _ => mem_range.mpr (dir_lt p q)) (dir_inj p)

private def corners (k : ℕ) : Finset (Fin (k+5) × Fin (k+5)) :=
  let ends : Finset (Fin (k+5)) := {0, Fin.last (k+4)}
  ends ×ˢ ends

private theorem corners_card (k : ℕ) : (corners k).card = 4 := by
  have h : (0 : Fin (k+5)) ≠ Fin.last (k+4) := by
    intro he
    have := congrArg Fin.val he
    simp at this
  simp [corners,h]

private theorem in_range {k : ℕ} {p q : Fin (k+5) × Fin (k+5)}
    (hq : q ∈ vonNeumann (k+5) p) :
    p.1.val - q.1.val + (q.1.val - p.1.val) +
      (p.2.val - q.2.val + (q.2.val - p.2.val)) ≤ 1 := by
  exact (Finset.mem_filter.mp hq).2

private theorem is_corner {k : ℕ} {q : Fin (k+5) × Fin (k+5)} (hq : q ∈ corners k) :
    (q.1.val = 0 ∨ q.1.val = k+4) ∧ (q.2.val = 0 ∨ q.2.val = k+4) := by
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hq
  simp only [mem_insert, mem_singleton] at hx hy
  constructor
  · exact hx.imp (congrArg Fin.val) (congrArg Fin.val)
  · exact hy.imp (congrArg Fin.val) (congrArg Fin.val)

private theorem corner_overlap {k : ℕ} (p : Fin (k+5) × Fin (k+5)) :
    ((vonNeumann (k+5) p) ∩ corners k).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha,ca⟩ := mem_inter.mp ha
  obtain ⟨hb,cb⟩ := mem_inter.mp hb
  have a₁ := in_range ha
  have b₁ := in_range hb
  obtain ⟨ac,ad⟩ := is_corner ca
  obtain ⟨bc,bd⟩ := is_corner cb
  apply Prod.ext <;> apply Fin.ext <;> omega

private theorem lost_direction {k : ℕ} (p : Fin (k+5) × Fin (k+5))
    (h : ((vonNeumann (k+5) p) ∩ corners k).Nonempty) :
    (vonNeumann (k+5) p).card ≤ 4 := by
  obtain ⟨q,hq⟩ := h
  obtain ⟨hq,hc⟩ := mem_inter.mp hq
  have hd := in_range hq
  obtain ⟨cx,cy⟩ := is_corner hc
  have px := p.1.isLt
  have py := p.2.isLt
  have boundary : p.1.val=0 ∨ p.1.val=k+4 ∨ p.2.val=0 ∨ p.2.val=k+4 := by omega
  obtain ⟨d,hlt,absent⟩ : ∃ d < 5, ∀ b, direction p b ≠ d := by
    rcases boundary with h|h|h|h
    · refine ⟨0,by decide,fun b => ?_⟩
      unfold direction
      simp only [Fin.lt_def]
      split_ifs <;> omega
    · refine ⟨1,by decide,fun b => ?_⟩
      have hb := b.1.isLt
      unfold direction
      simp only [Fin.lt_def]
      split_ifs <;> omega
    · refine ⟨2,by decide,fun b => ?_⟩
      unfold direction
      simp only [Fin.lt_def]
      split_ifs <;> omega
    · refine ⟨3,by decide,fun b => ?_⟩
      have hb := b.2.isLt
      unfold direction
      simp only [Fin.lt_def]
      split_ifs <;> omega
  have bound := card_le_card_of_injOn (t := (range 5).erase d) (direction p)
    (fun b _ => mem_erase.mpr ⟨absent b,mem_range.mpr (dir_lt p b)⟩) (dir_inj p)
  simpa [card_erase_of_mem (mem_range.mpr hlt)] using bound

private theorem multiplicity {k : ℕ} (p : Fin (k+5) × Fin (k+5)) :
    (vonNeumann (k+5) p).card + ((vonNeumann (k+5) p) ∩ corners k).card ≤ 5 := by
  by_cases h : ((vonNeumann (k+5) p) ∩ corners k).Nonempty
  · have := lost_direction p h
    have := corner_overlap p
    omega
  · simpa [not_nonempty_iff_eq_empty.mp h] using hood_size p

private theorem total_over {n : ℕ} (M : Fin n → Fin n → ℕ) (s : Finset (Fin n × Fin n)) :
    ∑ q ∈ s, neighborhoodSum M q = ∑ p, ((vonNeumann n p) ∩ s).card * M p.1 p.2 := by
  classical
  have loc (q : Fin n × Fin n) : neighborhoodSum M q =
      ∑ p : Fin n × Fin n, if q ∈ vonNeumann n p then M p.1 p.2 else 0 := by
    unfold neighborhoodSum vonNeumann
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    rw [Nat.dist_comm q.1.val p.1.val, Nat.dist_comm q.2.val p.2.val]
    simp only [mem_filter, mem_univ, true_and]
  simp_rw [loc]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [← sum_filter]
  have heq : s.filter (· ∈ vonNeumann n p) = vonNeumann n p ∩ s := by ext; simp [and_comm]
  simp [heq]

private theorem incidence {k : ℕ} (M : Fin (k+5) → Fin (k+5) → ℕ) :
    (∑ q, neighborhoodSum M q) + (∑ q ∈ corners k, neighborhoodSum M q) ≤ 5 * gridSum M := by
  rw [total_over, total_over]
  simp only [inter_univ, ← sum_add_distrib, ← Nat.add_mul]
  unfold gridSum
  rw [← sum_product', ← univ_product_univ, mul_sum]
  apply sum_le_sum
  intro p _
  exact Nat.mul_le_mul_right _ (multiplicity p)

private theorem round_up {n s : ℕ} (h : n ^ 4 + 12 ≤ 10*s+n^2) :
    n ^ 4 + 14 ≤ 10*s+n^2 := by
  have hc : (n^4+12)%10 ≠ (10*s+n^2)%10 ∧ (n^4+13)%10 ≠ (10*s+n^2)%10 := by
    rw [Nat.mul_add_mod_self_left, Nat.add_mod, Nat.add_mod (n^4) 13, Nat.pow_mod n 4 10,
      Nat.pow_mod n 2 10]
    have hlt := Nat.mod_lt n (by decide : 0<10)
    interval_cases n % 10 <;> decide
  omega

/-- Every valid grid of side at least five satisfies the conjectured sharp lower bound. -/
theorem grid_lower_bound {k : ℕ} (M : Fin (k+5) → Fin (k+5) → ℕ) (hv : IsValidGrid M) :
    Nat.ceil ((((k+5 : ℕ) : ℚ)^4 - ((k+5 : ℕ) : ℚ)^2 + 14) / 10) ≤ gridSum M := by
  have hall := inj_lower (univ : Finset (Fin (k+5) × Fin (k+5))) _ hv
  have hc := inj_lower (corners k) _ hv
  rw [corners_card] at hc
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin] at hall
  have hinc := incidence M
  have h : (k+5)^4 + 12 ≤ 10*gridSum M + (k+5)^2 := by
    nlinarith only [hall,hc,hinc]
  have hr := round_up h
  apply Nat.ceil_le.mpr
  rw [div_le_iff₀ (by decide : (0:ℚ)<10)]
  have hq : ((k+5 : ℕ) : ℚ)^4 + 14 ≤ 10*(gridSum M : ℚ) + ((k+5 : ℕ) : ℚ)^2 := by
    exact_mod_cast hr
  linarith

/-- The two side-length classes in which the optimal grid has nine units of
weight available beyond the minimum total of its distinct neighborhood sums. -/
def H1 : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n → n % 5 = 2 ∨ n % 5 = 3 →
    ∃ M : Fin n → Fin n → ℕ, IsValidGrid M ∧
      gridSum M ≤ Nat.ceil (((n : ℚ)^4 - (n : ℚ)^2 + 14) / 10)

/-- In the other three side-length classes the optimal grid has ten units available. -/
def H2 : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n → n % 5 ≠ 2 → n % 5 ≠ 3 →
    ∃ M : Fin n → Fin n → ℕ, IsValidGrid M ∧
      gridSum M ≤ Nat.ceil (((n : ℚ)^4 - (n : ℚ)^2 + 14) / 10)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a340630.main := by
  rintro ⟨n₁,h₁⟩ ⟨n₂,h₂⟩
  refine ⟨max 4 (max n₁ n₂), ?_⟩
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 5 := ⟨n-5, by omega⟩
  obtain ⟨M,hv,hm⟩ : ∃ M : Fin (k+5) → Fin (k+5) → ℕ, IsValidGrid M ∧
      gridSum M ≤ Nat.ceil ((((k+5 : ℕ) : ℚ)^4 - ((k+5 : ℕ) : ℚ)^2 + 14) / 10) := by
    by_cases hc : (k+5)%5=2 ∨ (k+5)%5=3
    · exact h₁ _ (by omega) hc
    · exact h₂ _ (by omega) (by tauto) (by tauto)
  let costs := {s : ℕ | ∃ G : Fin (k+5) → Fin (k+5) → ℕ, IsValidGrid G ∧ gridSum G = s}
  have hm' : gridSum M ∈ costs := ⟨M,hv,rfl⟩
  change sInf costs = _
  apply le_antisymm ((Nat.sInf_le hm').trans hm)
  obtain ⟨G,hg,he⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨_,hm'⟩)
  rw [←he]
  exact grid_lower_bound G hg

end OMA.R_oeis_a340630_R1
