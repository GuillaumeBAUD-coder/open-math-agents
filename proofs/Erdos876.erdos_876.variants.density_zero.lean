import FormalConjectures.ErdosProblems.«876»
open Finset Erdos876 Filter
namespace SubsetSumDensity

def part (F : Finset ℕ) (i : ℕ) := F.filter (· < i)
def shift (F : Finset ℕ) (i : ℕ) := ∑ x ∈ part F i, x

lemma shift_collision {A : Set ℕ} (h : IsSubsetSumFree A) {F : Finset ℕ} (hf : ↑F ⊆ A)
    {i j x y : ℕ} (hi : i ∈ F) (hij : i < j) (hx : x ∈ A) (hy : y ∈ A)
    (ht : ∀ a ∈ F, a < y) (he : shift F i + x = shift F j + y) : False := by
  classical
  let D := part F j \ part F i
  have hsub : part F i ⊆ part F j := fun a ha =>
    mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.trans hij⟩
  have hsum : (∑ a ∈ D, a) + shift F i = shift F j := sum_sdiff hsub
  have hiD : i ∈ D := by simp [D,part,hi,hij]
  have pos := (h i (hf hi)).1
  have hle : i ≤ ∑ a ∈ D, a := single_le_sum (f := id) (fun a _ => Nat.zero_le a) hiD
  have hyx : y < x := by omega
  have hD (a : ℕ) (ha : a ∈ D) : a ∈ F := (mem_filter.mp (mem_sdiff.mp ha).1).1
  have hny : y ∉ D := fun hm => (lt_irrefl y) (ht _ (hD _ hm))
  apply (h x hx).2
  refine ⟨insert y D, ?_, ?_⟩
  · intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact ⟨hy,hyx⟩
    · exact ⟨hf (hD a ha),(ht a (hD a ha)).trans hyx⟩
  · rw [sum_insert hny]
    omega

/-- Translates of the tail by the distinct prefix sums of F are disjoint. -/
lemma packing {A : Set ℕ} (h : IsSubsetSumFree A) {F T : Finset ℕ} (hf : ↑F ⊆ A)
    (ht : ↑T ⊆ A) (sep : ∀ y ∈ T, ∀ a ∈ F, a < y) {n : ℕ} (hn : ∀ y ∈ T, y < n) :
    F.card * T.card ≤ n + ∑ i ∈ F, i := by
  let f (p : ℕ × ℕ) := shift F p.1 + p.2
  have hinj : Set.InjOn f ↑(F ×ˢ T) := by
    rintro ⟨i,x⟩ hix ⟨j,y⟩ hjy he
    obtain ⟨hi,hx⟩ := mem_product.mp hix
    obtain ⟨hj,hy⟩ := mem_product.mp hjy
    change shift F i + x = shift F j + y at he
    rcases lt_trichotomy i j with hh | rfl | hh
    · exact (shift_collision h hf hi hh (ht hx) (ht hy) (sep y hy) he).elim
    · simp_all
    · exact (shift_collision h hf hj hh (ht hy) (ht hx) (sep x hx) he.symm).elim
  have hsub : (F ×ˢ T).image f ⊆ range (n + ∑ i ∈ F, i) := by
    rintro v hv
    obtain ⟨⟨i,y⟩,hp,rfl⟩ := mem_image.mp hv
    have hy := hn y (mem_product.mp hp).2
    have hh : shift F i ≤ ∑ a ∈ F, a := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by simp)
    exact mem_range.mpr (show shift F i + y < _ by omega)
  simpa [card_image_of_injOn hinj] using card_le_card hsub

lemma bound {A : Set ℕ} (h : IsSubsetSumFree A) (ha : A.Infinite) (k : ℕ) :
    ∃ C, ∀ n, k * (A ∩ Set.Iio n).ncard ≤ n+C := by
  classical
  obtain ⟨F,hF,hk⟩ := ha.exists_subset_card_eq k
  let L := (∑ a ∈ F, a)+1
  refine ⟨(∑ a ∈ F, a) + k*L, fun n => ?_⟩
  let U := (range n).filter (· ∈ A)
  let T := U \ range L
  have sep : ∀ y ∈ T, ∀ a ∈ F, a < y := by
    intro y hy a ha'
    have hle : a ≤ ∑ a ∈ F, a := single_le_sum (f := id) (fun a _ => Nat.zero_le a) ha'
    have hny := (mem_sdiff.mp hy).2
    simp only [mem_range] at hny
    dsimp [L] at hny
    omega
  have pack := packing h hF (T := T)
    (fun y hy => (mem_filter.mp (mem_sdiff.mp hy).1).2) sep
    (n := n) (fun y hy => mem_range.mp (mem_filter.mp (mem_sdiff.mp hy).1).1)
  rw [hk] at pack
  have hcard : U.card ≤ T.card + L := by
    have h1 := card_sdiff_add_card_inter U (range L)
    have h2 := card_le_card (inter_subset_right (s₁ := U) (s₂ := range L))
    simp only [card_range] at h2
    dsimp [T]; omega
  have hU : (U : Set ℕ) = A ∩ Set.Iio n := by ext y; simp [U,and_comm]
  rw [← hU, Set.ncard_coe_finset]
  calc
    k*U.card ≤ k*(T.card+L) := Nat.mul_le_mul_left _ hcard
    _ ≤ _ := by rw [Nat.mul_add]; omega
end SubsetSumDensity

theorem OMA.solution : type_of% @Erdos876.erdos_876.variants.density_zero := by
  intro A ha hs
  simp only [Set.HasDensity,Set.partialDensity,Set.inter_univ,Set.univ_inter, Set.ncard_Iio_nat]
  rw [Metric.tendsto_atTop]
  intro ε he
  obtain ⟨k,hk⟩ := exists_nat_gt (2/ε)
  have hk' : 2 < (k : ℝ)*ε := (div_lt_iff₀ he).mp hk
  obtain ⟨C,hC⟩ := SubsetSumDensity.bound hs ha k
  refine ⟨C+1, fun n hn => ?_⟩
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hle : k*(A ∩ Set.Iio n).ncard ≤ 2*n := (hC n).trans (by omega)
  have hle' : (k : ℝ)*(A ∩ Set.Iio n).ncard ≤ 2*(n : ℝ) := by exact_mod_cast hle
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hpos]
  have hh := mul_lt_mul_of_pos_right hk' hpos
  have kp : (0 : ℝ) < k := by by_contra! hh; nlinarith
  apply lt_of_mul_lt_mul_left (a := (k : ℝ)) _ kp.le
  nlinarith
