import FormalConjectures.ErdosProblems.«876»
import Mathlib

/-! A finite certificate for Abbott's lower bound, from his construction with
A = {1,2,4,8} and t = 24 (Acta Arith. 48, 1987, 93–96). The upper bound
is separated into Levine and O'Sullivan's counting inequality (2.6) and
their reciprocal-sum bound for sequences satisfying that inequality. -/

namespace OMA.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1

open Erdos876 Finset

-- Levine–O'Sullivan, Theorem 2, with b the rank-k member of a finite prefix.
def H1 : Prop := ∀ A : Finset ℕ, IsSubsetSumFree (A : Set ℕ) → ∀ b ∈ A, ∀ x : ℕ,
  ((A.filter (· ≤ b)).card + 1) * (A.filter (· ≤ x)).card ≤
    x + ((A.filter (· ≤ b)).card + 1) * b

-- Numerical upper bound for their chi-sequences, in the finite-sum form.
def H2 : Prop := ∀ A : Finset ℕ, 0 ∉ A →
  (∀ b ∈ A, ∀ x : ℕ, ((A.filter (· ≤ b)).card + 1) * (A.filter (· ≤ x)).card ≤
    x + ((A.filter (· ≤ b)).card + 1) * b) →
  (∑ a ∈ A, (1 : ℝ) / a) ≤ 19999 / 5000

lemma bitCover (L : List ℕ) (U : Finset ℕ) (hU : ∀ u ∈ U, u ∈ L) :
    (L.foldr (fun x b : ℕ => b ||| (b <<< x)) 1).testBit (∑ u ∈ U, u) = true := by
  induction L generalizing U with
  | nil =>
    have he : U = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro u hu
      simpa using hU u hu
    simp [he]
  | cons x xs ih =>
    rw [List.foldr_cons,Nat.testBit_or,Bool.or_eq_true]
    by_cases hx : x ∈ U
    · right
      have he := ih (U.erase x) (fun u hu => (List.mem_cons.mp
        (hU u (mem_of_mem_erase hu))).resolve_left (ne_of_mem_erase hu))
      rw [← add_sum_erase U (fun u : ℕ => u) hx, Nat.testBit_shiftLeft]
      simpa using he
    · left
      exact ih U fun u hu => (List.mem_cons.mp (hU u hu)).resolve_left (fun e => hx (e ▸ hu))

private lemma certified (L : List ℕ) (hc : L.all (fun a => (0 < a) &&
    !(((L.filter (· < a)).foldr (fun x b : ℕ => b ||| (b <<< x)) 1).testBit a)) = true) :
    IsSubsetSumFree (L.toFinset : Set ℕ) := by
  intro a ha
  have good := List.all_eq_true.mp hc a (List.mem_toFinset.mp ha)
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at good
  refine ⟨good.1,?_⟩
  rintro ⟨U,hU,eq⟩
  have hit := bitCover (L.filter (· < a)) U (fun u hu => List.mem_filter.mpr
    ⟨List.mem_toFinset.mp (hU hu).1,decide_eq_true (hU hu).2⟩)
  rw [← eq,good.2] at hit
  contradiction

private lemma witness : ∃ F : Finset ℕ, IsSubsetSumFree (F : Set ℕ) ∧
    (2.064:ℝ) < ∑ a ∈ F, (1:ℝ)/a := by
  let L : List ℕ := [1, 2, 4, 8, 25, 49, 73, 97, 121, 145, 169, 193, 217, 241, 265, 289, 313, 337, 361, 385, 409, 433, 457, 481, 505, 529, 553, 577, 601, 625, 649, 673, 697, 721, 745, 769, 793, 817, 841, 865, 889, 913, 937, 961, 985, 1009, 1033, 1057, 1081, 1105, 1129, 1153, 1177, 1201, 1225, 1249, 1273, 1297, 1321, 36529, 36553, 36577, 36601, 36625, 36649, 36673, 36697, 36721, 36745, 36769, 36793, 36817]
  let F := L.toFinset
  have hs : IsSubsetSumFree (F : Set ℕ) := by
    apply certified L
    decide +kernel
  refine ⟨F,hs,?_⟩
  have cert : 206400000 < ∑ a ∈ F, 100000000 / a := by decide +kernel
  have hr : (206400000 : ℝ) < ∑ a ∈ F, ((100000000 / a : ℕ) : ℝ) := by exact_mod_cast cert
  have hsum : (∑ a ∈ F, ((100000000 / a : ℕ) : ℝ)) ≤ (∑ a ∈ F, (1:ℝ)/a) * 100000000 := by
    rw [Finset.sum_mul]
    apply sum_le_sum
    intro a ha
    have hap : (0:ℝ) < a := by exact_mod_cast (hs a ha).1
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hap]
    exact_mod_cast Nat.div_mul_le_self 100000000 a
  linarith

private lemma extendFree (F : Finset ℕ) (hf : IsSubsetSumFree (F : Set ℕ)) :
    ∃ A : Set ℕ, (F : Set ℕ) ⊆ A ∧ A.Infinite ∧ IsSubsetSumFree A := by
  classical
  let D := (∑ i ∈ F, i) + 1
  let t (k : ℕ) := D * 2^k
  have hD : 0 < D := Nat.succ_pos _
  have ht : StrictMono t := fun i j hij => Nat.mul_lt_mul_of_pos_left
    (Nat.pow_lt_pow_right (by decide : 1 < 2) hij) hD
  have hF (x : ℕ) (hx : x ∈ F) (k : ℕ) : x < t k := by
    have h₁ := single_le_sum (f := id) (fun i _ => Nat.zero_le i) hx
    have h₂ : D ≤ t k := by simpa [t] using Nat.mul_le_mul_left D (Nat.one_le_pow k 2 (by decide))
    dsimp only [id] at h₁
    dsimp [D] at h₂
    omega
  have hgeo (k : ℕ) : (∑ i ∈ F, i) + (∑ i ∈ range k, t i) + 1 = t k := by
    induction k with
    | zero => simp [t,D]
    | succ k ih =>
      rw [sum_range_succ]
      have hnext : t (k+1) = 2*t k := by dsimp [t]; rw [pow_succ]; ring
      omega
  refine ⟨(F : Set ℕ) ∪ Set.range t,Set.subset_union_left,(Set.infinite_range_of_injective ht.injective).mono
    Set.subset_union_right,?_⟩
  intro a ha
  rcases ha with ha | ⟨k,rfl⟩
  · refine ⟨(hf a ha).1, fun ⟨U,hU,he⟩ => (hf a ha).2 ⟨U,?_,he⟩⟩
    intro u hu
    rcases (hU hu).1 with h | ⟨k,rfl⟩
    · exact ⟨h,(hU hu).2⟩
    · have hlt : t k < a := (hU hu).2
      exact ((hF a ha k).not_gt hlt).elim
  · refine ⟨by dsimp [t]; positivity,?_⟩
    rintro ⟨U,hU,he⟩
    have hsub : U ⊆ F ∪ (range k).image t := by
      intro u hu
      rcases (hU hu).1 with h | ⟨j,rfl⟩
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_image.mpr ⟨j,mem_range.mpr (ht.lt_iff_lt.mp (hU hu).2),rfl⟩)
    have h₁ := Finset.sum_le_sum_of_subset (f := id) hsub
    have hdis : Disjoint F ((range k).image t) := by
      rw [Finset.disjoint_left]
      rintro u hu hm
      obtain ⟨j,_,rfl⟩ := mem_image.mp hm
      exact (hF _ hu j).false
    rw [Finset.sum_union hdis, Finset.sum_image (fun _ _ _ _ H => ht.injective H)] at h₁
    dsimp only [id] at h₁
    have := hgeo k
    omega

theorem main : H1 → H2 → type_of% @Erdos876.erdos_876.variants.recip_sum_bounds := by
  classical
  intro count numerical
  have bound (A : Set ℕ) (hf : IsSubsetSumFree A) (s : Finset A) :
      ∑ a ∈ s, (1:ℝ)/(a.val : ℕ) ≤ 19999/5000 := by
    let F := s.map (Function.Embedding.subtype _)
    have hsub : (F : Set ℕ) ⊆ A := by
      rintro x hx
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      exact a.property
    have hfree : IsSubsetSumFree (F : Set ℕ) := fun a ha =>
      ⟨(hf a (hsub ha)).1, fun hb => (hf a (hsub ha)).2 (subsetSums_mono
        (Set.inter_subset_inter_left _ hsub) hb)⟩
    have hb := numerical F (fun hz => (Nat.lt_irrefl 0) (hfree 0 hz).1) (count F hfree)
    simpa [F] using hb
  have high : ∀ v ∈ {s : ℝ | ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
      HasSum (fun a : A => (1:ℝ) / (a : ℕ)) s}, v ≤ 19999/5000 := by
    rintro v ⟨A,_,hf,hs⟩
    rw [← hs.tsum_eq]
    exact tsum_le_of_sum_le' (by norm_num) (bound A hf)
  obtain ⟨F,hF,hrec⟩ := witness
  obtain ⟨A,hFA,hi,hf⟩ := extendFree F hF
  have hs := summable_of_sum_le (f := fun a : A => (1:ℝ)/(a : ℕ)) (fun _ => by positivity) (bound A hf)
  have hmem : (∑' a : A, (1:ℝ)/(a:ℕ)) ∈ {s : ℝ | ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
      HasSum (fun a : A => (1:ℝ)/(a:ℕ)) s} := ⟨A,hi,hf,hs.hasSum⟩
  have hf' : (∑ a ∈ F, (1:ℝ)/a) ≤ ∑' a : A, (1:ℝ)/(a:ℕ) := by
    let e : F → A := fun a => ⟨a.val,hFA a.property⟩
    have hin : Function.Injective e := fun a b h => Subtype.ext (congrArg (fun u : A => u.val) h)
    have hle := hs.sum_le_tsum (univ.image e) (fun a _ => by positivity)
    rw [sum_image (fun _ _ _ _ h => hin h)] at hle
    change (∑ a ∈ F.attach, (1:ℝ)/(a.val:ℕ)) ≤ _ at hle
    rwa [Finset.sum_attach F (fun i : ℕ => (1:ℝ)/i)] at hle
  exact ⟨hrec.trans_le (hf'.trans (le_csSup ⟨_,high⟩ hmem)),
    (csSup_le ⟨_,hmem⟩ high).trans_lt (by norm_num)⟩

end OMA.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1
