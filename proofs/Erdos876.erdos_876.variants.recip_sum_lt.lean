import FormalConjectures.ErdosProblems.«876»
/-! A packing bound for two dyadic blocks limits the number of blocks at each density. -/
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

def block (S : Finset ℕ) (j : ℕ) := S.filter (fun a => Nat.log 2 a = j)

lemma bounds {A : Set ℕ} (hs : IsSubsetSumFree A) {S : Finset ℕ} (hS : ↑S ⊆ A)
    {a j : ℕ} (ha : a ∈ block S j) : 2^j ≤ a ∧ a < 2^(j+1) := by
  obtain ⟨haS, rfl⟩ := mem_filter.mp ha
  exact ⟨Nat.pow_log_le_self _ (hs _ (hS haS)).1.ne', Nat.lt_pow_succ_log_self (by decide) _⟩

lemma block_card {A : Set ℕ} (hs : IsSubsetSumFree A) {S : Finset ℕ} (hS : ↑S ⊆ A) (j : ℕ) :
    (block S j).card ≤ 2^j := by
  have h : block S j ⊆ Ico (2^j) (2^(j+1)) := fun _ ha => mem_Ico.mpr (bounds hs hS ha)
  simpa [pow_succ,Nat.mul_two] using card_le_card h

lemma block_pack {A : Set ℕ} (hs : IsSubsetSumFree A) {S : Finset ℕ} (hS : ↑S ⊆ A)
    {i j : ℕ} (hij : i < j) :
    (block S i).card * (block S j).card ≤ 2*2^j + 2*(block S i).card * 2^i := by
  have sub (s : ℕ) : ↑(block S s) ⊆ A := fun _ ha => hS (mem_filter.mp ha).1
  have pack := packing hs (sub i) (sub j) (fun y hy a ha =>
    (bounds hs hS ha).2.trans_le ((Nat.pow_le_pow_right (by decide : 0 < 2) hij).trans
      (bounds hs hS hy).1)) (fun _ hy => (bounds hs hS hy).2)
  have sm := sum_le_sum (s := block S i) (fun a ha => (bounds hs hS ha).2.le)
  simp only [sum_const,smul_eq_mul] at sm
  simp only [pow_succ] at pack sm
  nlinarith only [pack,sm]

lemma bad_count (k : ℕ → ℕ)
    (pack : ∀ i j, i < j → k i * k j ≤ 2*2^j + 2*k i*2^i) (J : Finset ℕ) (t : ℕ) :
    (J.filter (fun j => 2^j ≤ 2^t*k j)).card ≤ 3*t+5 := by
  let B := J.filter (fun j => 2^j ≤ 2^t*k j)
  let U := B.filter (fun i => 2*t+2 ≤ i)
  by_cases hu : U.Nonempty
  · let i := U.min' hu
    obtain ⟨hib, hil⟩ := mem_filter.mp (show i ∈ U from min'_mem _ _)
    have hki := (mem_filter.mp hib).2
    have hsmall : 4*2^t ≤ k i := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 2) hil
      rw [show 2*t+2 = t+t+2 by omega, pow_add, pow_add] at h
      exact Nat.le_of_mul_le_mul_left (c := 2^t) (by nlinarith only [h,hki]) (by positivity)
    have sub : B ⊆ range (2*t+2) ∪ Ico i (i+t+3) := by
      intro j hj
      by_cases hcut : j < 2*t+2
      · exact mem_union_left _ (mem_range.mpr hcut)
      have hjU : j ∈ U := mem_filter.mpr ⟨hj,by omega⟩
      refine mem_union_right _ (mem_Ico.mpr ⟨min'_le _ _ hjU, ?_⟩)
      by_contra! hfar
      have hY : 8*2^i*2^t ≤ 2^j := by
        have h := Nat.pow_le_pow_right (by decide : 0 < 2) hfar
        rw [pow_add, pow_add] at h
        nlinarith only [h]
      have hkj := (mem_filter.mp hj).2
      have pp := pack i j (by omega)
      have hp : 0 < k i * 2^j := Nat.mul_pos (lt_of_lt_of_le (by positivity) hsmall) (by positivity)
      nlinarith only [Nat.mul_le_mul_left (k i) hkj, Nat.mul_le_mul_left (2^t) pp,
        Nat.mul_le_mul_right (2^j) hsmall, Nat.mul_le_mul_left (k i) hY,hp]
    have hc := (card_le_card sub).trans (card_union_le ..)
    simp only [card_range,Nat.card_Ico] at hc
    change B.card ≤ _
    omega
  · have sub : B ⊆ range (2*t+2) := by
      intro j hj
      apply mem_range.mpr
      by_contra! hn
      exact hu ⟨j,mem_filter.mpr ⟨hj,hn⟩⟩
    have hc := card_le_card sub
    simp only [card_range] at hc
    change B.card ≤ _
    omega

open scoped Classical
noncomputable def level (k : ℕ → ℕ) (j : ℕ) :=
  if h : ∃ t : ℕ, 2^j ≤ 2^t*k j then Nat.find h else 0

lemma level_spec (k : ℕ → ℕ) (j : ℕ) (hp : 0 < k j) :
    2^j ≤ 2^(level k j)*k j ∧ ∀ u < level k j, ¬2^j ≤ 2^u*k j := by
  have ex : ∃ t : ℕ, 2^j ≤ 2^t*k j := ⟨j, Nat.le_mul_of_pos_right _ hp⟩
  rw [level, dif_pos ex]
  exact ⟨Nat.find_spec ex,fun _ => Nat.find_min ex⟩

lemma density_le (k : ℕ → ℕ) (j : ℕ) (hp : 0 < k j) (hc : k j ≤ 2^j) :
    (k j : ℝ)/2^j ≤ 2*(1/2 : ℝ)^(level k j) := by
  have spec := level_spec k j hp
  cases h : level k j with
  | zero =>
    simp only [pow_zero,mul_one]
    apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^j)).2
    have hr : (k j : ℝ) ≤ 2^j := by exact_mod_cast hc
    linarith [show 0 ≤ (2:ℝ)^j by positivity]
  | succ u =>
    have hn : 2^u*k j < 2^j := lt_of_not_ge (spec.2 u (by omega))
    have hr : (2:ℝ)^u * k j ≤ 2^j := by exact_mod_cast hn.le
    rw [pow_succ,one_div_pow]
    field_simp
    nlinarith only [hr]

lemma majorant (t : ℕ) : (3*(t:ℝ)+5) * (2*(1/2 : ℝ)^t) ≤ 12*(3/4 : ℝ)^t := by
  have h : 3*(t:ℝ)+5 ≤ 6*(3/2 : ℝ)^t := by
    induction t with
    | zero => norm_num
    | succ t ih =>
      push_cast
      rw [pow_succ]
      linarith [one_le_pow₀ (n := t) (by norm_num : (1:ℝ) ≤ 3/2)]
  calc
    _ ≤ (6*(3/2 : ℝ)^t) * (2*(1/2 : ℝ)^t) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by rw [show (3/4 : ℝ) = 3/2*(1/2) by norm_num,mul_pow]; ring

lemma dyadic_sum (k : ℕ → ℕ) (J : Finset ℕ) (pos : ∀ j ∈ J, 0 < k j)
    (card : ∀ j, k j ≤ 2^j) (pack : ∀ i j, i < j → k i * k j ≤ 2*2^j + 2*k i*2^i) :
    ∑ j ∈ J, (k j : ℝ)/2^j ≤ 48 := by
  classical
  let D := J.image (level k)
  have hf (t : ℕ) : (J.filter (fun j => level k j = t)).card ≤ 3*t+5 := by
    refine (card_le_card (t := J.filter (fun j => 2^j ≤ 2^t*k j)) ?_).trans (bad_count k pack J t)
    intro j hj
    obtain ⟨hj,ht⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨hj, ht ▸ (level_spec k j (pos j hj)).1⟩
  calc
    _ = ∑ t ∈ D, ∑ j ∈ J with level k j = t, (k j : ℝ)/2^j :=
      (sum_fiberwise_of_maps_to (fun j => mem_image_of_mem (level k)) _).symm
    _ ≤ ∑ t ∈ D, 12*(3/4 : ℝ)^t := by
      apply sum_le_sum
      intro t _
      calc
        _ ≤ ∑ j ∈ J with level k j = t, 2*(1/2 : ℝ)^t := by
          apply sum_le_sum
          intro j hj
          obtain ⟨hj, ht⟩ := mem_filter.mp hj
          exact ht ▸ density_le k j (pos j hj) (card j)
        _ ≤ (3*(t:ℝ)+5) * (2*(1/2 : ℝ)^t) := by
          simp only [sum_const,nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hf t
        _ ≤ _ := majorant t
    _ ≤ 48 := by
      rw [← mul_sum]
      have hg := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4)
        (by norm_num : (3/4 : ℝ) < 1)).sum_le_tsum D (fun i _ => by positivity)
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hg
      linarith

lemma finite_bound {A : Set ℕ} (hs : IsSubsetSumFree A) (S : Finset ℕ) (hS : ↑S ⊆ A) :
    ∑ a ∈ S, (1:ℝ)/a ≤ 48 := by
  classical
  let J := S.image (Nat.log 2)
  let k := fun j => (block S j).card
  have hp : ∀ j ∈ J, 0 < k j := by
    intro j hj
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hj
    exact card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,rfl⟩⟩
  calc
    _ = ∑ j ∈ J, ∑ a ∈ block S j, (1:ℝ)/a :=
      (sum_fiberwise_of_maps_to (fun _ => mem_image_of_mem (Nat.log 2)) _).symm
    _ ≤ ∑ j ∈ J, (k j : ℝ)/2^j := by
      apply sum_le_sum
      intro j _
      calc
        _ ≤ ∑ a ∈ block S j, (1:ℝ)/2^j := by
          apply sum_le_sum
          intro a ha
          exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (bounds hs hS ha).1)
        _ = _ := by simp [k,div_eq_mul_inv]
    _ ≤ _ := dyadic_sum k J hp (block_card hs hS) (fun _ _ => block_pack hs hS)
end SubsetSumDensity

theorem OMA.solution : type_of% @Erdos876.erdos_876.variants.recip_sum_lt := by
  intro A _ hs
  let f := fun a : A => (1:ℝ)/(a:ℕ)
  have hn : 0 ≤ f := fun a => by dsimp [f]; positivity
  have hb (U : Finset A) : ∑ a ∈ U, f a ≤ 48 := by
    let e := Function.Embedding.subtype (· ∈ A)
    have hc : ↑(U.map e) ⊆ A := by
      intro x hx
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      exact a.property
    have hh := SubsetSumDensity.finite_bound hs _ hc
    rw [sum_map] at hh
    convert hh using 1
    apply sum_congr rfl
    intro a _
    rfl
  exact ⟨∑' a, f a, (Real.tsum_le_of_sum_le hn hb).trans_lt (by norm_num),
    (summable_of_sum_le hn hb).hasSum⟩
