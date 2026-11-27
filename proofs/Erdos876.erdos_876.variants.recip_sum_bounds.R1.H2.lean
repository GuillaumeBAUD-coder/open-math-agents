import OMAReductions.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1

/-!
Abbott’s lower bound for sum-free sequences (Acta Arith. 48, 1987). We use the initial blocks described by @minimumnz in the parent reduction. A bit-set verifies that the finite block is sum-free. A geometric tail extends it to an infinite set.
-/
namespace Abbott876
open Finset Erdos876
-- Read a decreasing list from right to left. Bit n records that n is a subset sum.
def scan : List ℕ → ℕ × Bool
  | [] => (1,true)
  | x :: xs =>
    let r := scan xs
    (r.1 ||| (r.1 <<< x), r.2 && !(r.1.testBit x) && decide (0 < x) && xs.all (· < x))

lemma bit_of_subset (l : List ℕ) (s : Finset ℕ) (hs : s ⊆ l.toFinset) :
    (scan l).1.testBit (∑ n∈s,n) = true := by
  induction l generalizing s with
  | nil => have := Finset.subset_empty.mp (by simpa using hs : s ⊆ ∅); subst s; decide
  | cons x xs ih =>
    change ((_ ||| (_ <<< x)):ℕ).testBit _ = true
    simp only [Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    by_cases hx : x ∈ s
    · right
      have he : s.erase x ⊆ xs.toFinset := by
        intro y hy
        have h := hs (mem_of_mem_erase hy)
        simpa [List.toFinset_cons,ne_of_mem_erase hy] using h
      have heq := sum_erase_add s (fun i : ℕ => i) hx
      have hv := ih _ he
      change (∑ i ∈ s.erase x,i)+x=∑ i∈s,i at heq
      rw [←heq,Nat.add_sub_cancel]
      exact ⟨by omega,hv⟩
    · left; apply ih
      intro y hy
      have hne : y ≠ x := fun e => hx (e ▸ hy)
      simpa [List.toFinset_cons,hne] using hs hy

lemma scan_free (l : List ℕ) (h : (scan l).2 = true) : IsSubsetSumFree (l.toFinset : Set ℕ) := by
  induction l with
  | nil => simp [IsSubsetSumFree]
  | cons x xs ih =>
    simp only [scan,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,List.all_eq_true] at h
    obtain ⟨⟨⟨hok,hbit⟩,hx0⟩,hlt⟩ := h
    have hfree := ih hok
    intro a ha
    change a∈(x::xs).toFinset at ha
    simp only [List.toFinset_cons,mem_insert] at ha
    have hale : a ≤ x := ha.elim (fun e => e.le) (fun h => (hlt a (List.mem_toFinset.mp h)).le)
    have transfer (t : Finset ℕ) (ht : (t:Set ℕ) ⊆ ((x::xs).toFinset:Set ℕ) ∩ Set.Iio a) :
        (t:Set ℕ) ⊆ (xs.toFinset:Set ℕ) ∩ Set.Iio a := by
      intro y hy
      obtain ⟨hy',hylt⟩ := ht hy
      have hne : y ≠ x := (hylt.trans_le hale).ne
      exact ⟨by simpa [List.toFinset_cons,hne] using hy',hylt⟩
    rcases ha with rfl|ha
    · refine ⟨hx0,?_⟩
      rintro ⟨t,ht,eq⟩
      have hb := bit_of_subset xs t (fun n hn => (transfer t ht hn).1)
      rw [←eq,hbit] at hb
      contradiction
    · refine ⟨(hfree a ha).1,?_⟩
      rintro ⟨t,ht,eq⟩
      exact (hfree a ha).2 ⟨t,transfer t ht,eq⟩

def values : List ℕ :=
  (((List.range 16).map (fun i => 36167+24*i)).reverse ++
   ((List.range 55).map (fun i => 25+24*i)).reverse ++ [8,4,2,1])
def S := values.toFinset
theorem freeS : IsSubsetSumFree (S : Set ℕ) := scan_free values (by decide +kernel)
theorem massS : (2.064:ℝ) < ∑ a∈S,1/(a:ℝ) := by
  have h : 206400000 < ∑ a∈S,100000000/a := by decide +kernel
  have hi : (206400000:ℝ) < ∑ a∈S,((100000000/a:ℕ):ℝ) := by exact_mod_cast h
  have hj := sum_le_sum (s:=S) (fun a _ => Nat.cast_div_le (α:=ℝ) (m:=100000000) (n:=a))
  push_cast at hj
  have he : (∑ a∈S,(100000000:ℝ)/a) = 100000000*(∑ a∈S,1/(a:ℝ)) := by
    rw [mul_sum]; apply sum_congr rfl; intro a _; ring
  rw [he] at hj
  linarith
end Abbott876

namespace Abbott876
open Erdos876 Finset
theorem extend (S : Finset ℕ) (hf : IsSubsetSumFree (S:Set ℕ)) {c : ℝ}
    (hm : c < ∑ a∈S,1/(a:ℝ)) :
    ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧ ∃ v : ℝ, c < v ∧ HasSum (fun a : A => (1:ℝ)/(a:ℕ)) v := by
  classical
  let T := (∑ a∈S,a)+1
  let g (n : ℕ) := T*2^n
  have hT : 0 < T := Nat.succ_pos _
  have hmon : StrictMono g := strictMono_nat_of_lt_succ fun n => by
    change T*2^n < T*2^(n+1)
    exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self n)) hT
  have hsmall (a : ℕ) (ha : a∈S) : a<T := by
    have h := single_le_sum (f:=fun i : ℕ => i) (fun i _ => Nat.zero_le i) ha
    dsimp [T]; omega
  have hTg (n : ℕ) : T ≤ g n := by simpa [g] using hmon.monotone (Nat.zero_le n)
  let f : S ⊕ ℕ → ℕ := Sum.elim (fun a => a.val) g
  have hinj : Function.Injective f := by
    rintro (a|n) (b|m) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · change a.val = g m at h
      exact False.elim ((hsmall a a.property).not_ge ((hTg m).trans_eq h.symm))
    · change g n = b.val at h
      exact False.elim ((hsmall b b.property).not_ge ((hTg n).trans_eq h))
    · exact congrArg Sum.inr (hmon.injective h)
  let A := Set.range f
  have ha (a : ℕ) : a∈A ↔ a∈S ∨ ∃ n, g n=a := by
    constructor
    · rintro ⟨(a|n),rfl⟩
      · exact Or.inl a.property
      · exact Or.inr ⟨n,rfl⟩
    · rintro (h|⟨n,rfl⟩)
      · exact ⟨Sum.inl ⟨a,h⟩,rfl⟩
      · exact ⟨Sum.inr n,rfl⟩
  have hInf : A.Infinite := (Set.infinite_range_of_injective hmon.injective).mono (by
    rintro _ ⟨n,rfl⟩; exact (ha _).mpr (Or.inr ⟨n,rfl⟩))
  have hgeom (n : ℕ) : (∑ i∈range n,g i)+T=g n := by
    induction n with
    | zero => simp [g]
    | succ n ih =>
      rw [sum_range_succ,show g (n+1)=g n+g n by dsimp [g]; ring]
      omega
  have hFree : IsSubsetSumFree A := by
    intro a haA
    rcases (ha a).mp haA with haS|⟨n,rfl⟩
    · refine ⟨(hf a haS).1,?_⟩
      rintro ⟨s,hs,e⟩
      apply (hf a haS).2
      refine ⟨s,?_,e⟩
      intro y hy
      obtain ⟨hyA,hylt⟩ := hs hy
      refine ⟨?_,hylt⟩
      rcases (ha y).mp hyA with h|⟨j,rfl⟩
      · exact h
      · exact False.elim (((hTg j).trans_lt (hylt.trans (hsmall a haS))).false)
    · refine ⟨hT.trans_le (hTg _),?_⟩
      rintro ⟨s,hs,e⟩
      have sub : s ⊆ S ∪ (range n).image g := by
        intro y hy
        obtain ⟨hm,hl⟩ := hs hy
        rcases (ha y).mp hm with h|⟨k,rfl⟩
        · exact mem_union_left _ h
        · exact mem_union_right _ (mem_image.mpr ⟨k,mem_range.mpr (hmon.lt_iff_lt.mp hl),rfl⟩)
      have dis : Disjoint S ((range n).image g) := by
        rw [disjoint_left]; intro x hx him
        obtain ⟨k,_,rfl⟩ := mem_image.mp him
        exact (hsmall _ hx).not_ge (hTg k)
      have bound := sum_le_sum_of_subset_of_nonneg (f:=fun i : ℕ => i) sub (fun _ _ _ => Nat.zero_le _)
      rw [sum_union dis,sum_image (hmon.injective.injOn)] at bound
      have hh := hgeom n
      dsimp [T] at hh
      omega
  let v := (∑ a∈S,1/(a:ℝ))
  have hsingle : HasSum ((fun n : ℕ => (1:ℝ)/n) ∘ f ∘ Sum.inl) v := by
    change HasSum (fun a : S => (1:ℝ)/(a:ℕ)) (∑ a∈S,1/(a:ℝ))
    rw [← sum_coe_sort S (fun a : ℕ => (1:ℝ)/a)]
    exact hasSum_fintype _
  have hseries : Summable (fun n : ℕ => (1:ℝ)/g n) := by
    apply (summable_geometric_two.mul_left (1/(T:ℝ))).congr
    intro n
    simp [g,one_div,mul_comm]
  let u := ∑' n : ℕ,(1:ℝ)/g n
  have htail : HasSum ((fun n : ℕ => (1:ℝ)/n) ∘ f ∘ Sum.inr) u := hseries.hasSum
  refine ⟨A,hInf,hFree,v+u,lt_of_lt_of_le hm (le_add_of_nonneg_right (tsum_nonneg fun _ => by positivity)),?_⟩
  exact hinj.hasSum_range_iff.mpr (HasSum.sum (f:=(fun n : ℕ => (1:ℝ)/n) ∘ f) hsingle htail)
end Abbott876

theorem OMA.solution : OMA.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1.H2 := Abbott876.extend Abbott876.S Abbott876.freeS Abbott876.massS
