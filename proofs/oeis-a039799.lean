import OMAStatements.S_oeis_a039799
import Mathlib

/-! # Maximum common restricted two-term sumset

Rob Pratt conjectured that the maximum in OEIS A039799 is 2n−11 for n≥14
on July 14, 2015. The upper bound checks his suggested restriction on the
first five eligible sums and reflects it at the other end. An explicit
two-coloring gives the matching lower bound.

Source: https://oeis.org/A039799 -/

open OMA.S_oeis_a039799

namespace PrattLower

/-- The first four colors are red, blue, blue, red; the interior has red at odd indices.
At the right end the colors are blue, blue, red, red in even size and red, blue, blue, red
in odd size. -/
private def red (n i : ℕ) : Prop :=
  i = 1 ∨ i = 4 ∨ (5 ≤ i ∧ i + 4 ≤ n ∧ i % 2 = 1) ∨ i = n ∨
  (n % 2 = 0 ∧ i + 1 = n) ∨ (n % 2 = 1 ∧ i + 3 = n)

private noncomputable def coloring (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter (red n)

private def covered (n k : ℕ) : Prop :=
  k ∈ pairSums (coloring n) ∩ pairSums (Finset.Icc 1 n \ coloring n)

private lemma sum_of_distinct {s : Finset ℕ} {x y k : ℕ} (hx : x ∈ s) (hy : y ∈ s)
    (hd : x ≠ y) (he : x+y=k) : k ∈ pairSums s := by
  rcases lt_or_gt_of_ne hd with h | h
  · exact Finset.mem_image.mpr ⟨(x,y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,h⟩,he⟩
  · exact Finset.mem_image.mpr ⟨(y,x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy,hx⟩,h⟩,
      (Nat.add_comm y x).trans he⟩

/-- The red pair is (u,k−u), and the blue pair is (v,k−v). -/
private lemma by_pairs (n k u v : ℕ)
    (h : 1 ≤ u ∧ u ≤ n ∧ u < k ∧ k ≤ n+u ∧ 2*u ≠ k ∧ red n u ∧ red n (k-u) ∧
          1 ≤ v ∧ v ≤ n ∧ v < k ∧ k ≤ n+v ∧ 2*v ≠ k ∧ ¬red n v ∧ ¬red n (k-v)) :
    covered n k := by
  classical
  rcases h with ⟨u1,un,uk,ukn,ud,ur,urr,v1,vn,vk,vkn,vd,vb,vbb⟩
  apply Finset.mem_inter.mpr
  constructor
  · apply sum_of_distinct (x := u) (y := k-u)
    · simpa [coloring] using And.intro (And.intro u1 un) ur
    · simpa [coloring] using And.intro (And.intro (show 1 ≤ k-u by omega) (show k-u ≤ n by omega)) urr
    · omega
    · omega
  · apply sum_of_distinct (x := v) (y := k-v)
    · simp [coloring, v1, vn, vb]
    · simp [coloring, show 1 ≤ k-v by omega, show k-v ≤ n by omega, vbb]
    · omega
    · omega

private lemma interior (n k : ℕ) (hn : 14 ≤ n) (hk : 8 ≤ k) (hkn : k+6 ≤ 2*n) :
    covered n k := by
  by_cases low : k+3 ≤ n
  · by_cases parity : k%2 = 0
    · apply by_pairs n k 1 2; unfold red; omega
    · apply by_pairs n k 4 3; unfold red; omega
  by_cases high : n+5 ≤ k
  · by_cases endCase : k+6 = 2*n
    · by_cases hnpar : n%2 = 0
      · apply by_pairs n k (n-1) (n-2); unfold red; omega
      · apply by_pairs n k n (n-1); unfold red; omega
    by_cases hnpar : n%2 = 0 <;> by_cases hkpar : k%2 = 0
    · apply by_pairs n k (n-1) (n-2); unfold red; omega
    · apply by_pairs n k n (n-3); unfold red; omega
    · apply by_pairs n k n (n-1); unfold red; omega
    · apply by_pairs n k (n-3) (n-2); unfold red; omega
  by_cases hnpar : n%2 = 0
  · have cases : k+2=n ∨ k+1=n ∨ k=n ∨ k=n+1 ∨ k=n+2 ∨ k=n+3 ∨ k=n+4 := by omega
    rcases cases with h | h | h | h | h | h | h
    · apply by_pairs n k 5 2; unfold red; omega
    · apply by_pairs n k 4 2; unfold red; omega
    · apply by_pairs n k 1 2; unfold red; omega
    · apply by_pairs n k 1 3; unfold red; omega
    · apply by_pairs n k 7 6; unfold red; omega
    · apply by_pairs n k 4 6; unfold red; omega
    · apply by_pairs n k 4 6; unfold red; omega
  · have cases : k+2=n ∨ k+1=n ∨ k=n ∨ k=n+1 ∨ k=n+2 ∨ k=n+3 ∨ k=n+4 := by omega
    rcases cases with h | h | h | h | h | h | h
    · apply by_pairs n k 1 3; unfold red; omega
    · apply by_pairs n k 5 6; unfold red; omega
    · apply by_pairs n k 4 2; unfold red; omega
    · apply by_pairs n k 1 2; unfold red; omega
    · apply by_pairs n k 5 3; unfold red; omega
    · apply by_pairs n k 7 8; unfold red; omega
    · apply by_pairs n k 4 6; unfold red; omega


private def edge (n : ℕ) : ℕ := if n%2=0 then 2*n-5 else 2*n-3

theorem bound (n : ℕ) (hn : 14 ≤ n) :
    ∃ s : Finset ℕ, s ⊆ Finset.Icc 1 n ∧
      2*n-11 ≤ (pairSums s ∩ pairSums (Finset.Icc 1 n \ s)).card := by
  classical
  refine ⟨coloring n, Finset.filter_subset _ _, ?_⟩
  let mid := Finset.Icc 8 (2*n-6)
  have hfront : covered n 5 := by apply by_pairs n 5 1 2; unfold red; omega
  have hback : covered n (edge n) := by
    unfold edge
    split_ifs with he
    · apply by_pairs n _ n (n-2); unfold red; omega
    · apply by_pairs n _ n (n-1); unfold red; omega
  have sub : insert 5 (insert (edge n) mid) ⊆
      pairSums (coloring n) ∩ pairSums (Finset.Icc 1 n \ coloring n) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with h | hk
    · exact h ▸ hfront
    rcases Finset.mem_insert.mp hk with h | hk
    · exact h ▸ hback
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hk
    exact interior n k hn hl (by omega)
  have hb : 2*n-6 < edge n := by unfold edge; split_ifs <;> omega
  have hbe : edge n ∉ mid := by simp [mid]; omega
  have hf : 5 ∉ insert (edge n) mid := by simp [mid]; omega
  have hcard := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem hbe] at hcard
  simp only [mid, Nat.card_Icc] at hcard
  omega

end PrattLower

namespace PrattUpper
open OMA.S_oeis_a039799

private def ground := Finset.Icc 1 8

/-- The sums up to nine depend only on the colors of the first eight elements. -/
private def fringe (S : Finset ℕ) :=
  (pairSums S ∩ pairSums (ground \ S)).filter (· ≤ 9)

private theorem fringe_cap {S : Finset ℕ} (h : S ⊆ ground) : (fringe S).card ≤ 3 := by
  have finite_check : ∀ A ∈ ground.powerset, (fringe A).card ≤ 3 := by decide +kernel
  exact finite_check S (Finset.mem_powerset.mpr h)

private lemma pair_iff {S : Finset ℕ} {x : ℕ} :
    x ∈ pairSums S ↔ ∃ a ∈ S, ∃ b ∈ S, a < b ∧ a+b=x := by
  simp only [pairSums, Finset.mem_image, Finset.mem_filter,
    Prod.exists]
  aesop

private lemma in_fringe {a b c d x : ℕ} (P : ℕ → Prop) [DecidablePred P]
    (ha : 0 < a) (hc : 0 < c) (hab : a<b) (hcd : c<d)
    (habx : a+b=x) (hcdx : c+d=x) (hx : x≤9)
    (pa : P a) (pb : P b) (pc : ¬P c) (pd : ¬P d) :
    x ∈ fringe (ground.filter P) := by
  have small {i : ℕ} (hl : 0 < i) (hu : i ≤ 8) : i ∈ ground :=
    Finset.mem_Icc.mpr ⟨hl,hu⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨pair_iff.mpr ?_,pair_iff.mpr ?_⟩,hx⟩
  · exact ⟨a, Finset.mem_filter.mpr ⟨small ha (by omega),pa⟩,
      b, Finset.mem_filter.mpr ⟨small (by omega) (by omega),pb⟩,hab,habx⟩
  · exact ⟨c, Finset.mem_sdiff.mpr ⟨small hc (by omega),fun h => pc (Finset.mem_filter.mp h).2⟩,
      d, Finset.mem_sdiff.mpr ⟨small (by omega) (by omega),fun h => pd (Finset.mem_filter.mp h).2⟩,
      hcd,hcdx⟩

/-- Pratt's low-end bound and reflection give the global extremal upper bound. -/
theorem bound (n : ℕ) (hn : 14 ≤ n) (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 n) :
    (pairSums s ∩ pairSums (Finset.Icc 1 n \ s)).card ≤ 2*n-11 := by
  let L := fringe (ground.filter (· ∈ s))
  let R := fringe (ground.filter (fun i => n+1-i ∈ s))
  let M := Finset.Icc 10 (2*n-8)
  let r (i : ℕ) := 2*n+2-i
  have sub : pairSums s ∩ pairSums (Finset.Icc 1 n \ s) ⊆ L ∪ M ∪ R.image r := by
    intro x hx
    obtain ⟨h1,h2⟩ := Finset.mem_inter.mp hx
    obtain ⟨a,ha,b,hb,hab,he⟩ := pair_iff.mp h1
    obtain ⟨c,hc,d,hd,hcd,hf⟩ := pair_iff.mp h2
    obtain ⟨hc,pc⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨hd,pd⟩ := Finset.mem_sdiff.mp hd
    have ba := Finset.mem_Icc.mp (hs ha)
    have bb := Finset.mem_Icc.mp (hs hb)
    have bc := Finset.mem_Icc.mp hc
    have bd := Finset.mem_Icc.mp hd
    simp only [Finset.mem_union]
    by_cases low : x ≤ 9
    · left; left
      exact in_fringe (· ∈ s) ba.1 bc.1 hab hcd he hf low ha hb pc pd
    by_cases mid : x ≤ 2*n-8
    · exact Or.inl (Or.inr (Finset.mem_Icc.mpr ⟨by omega,mid⟩))
    right
    refine Finset.mem_image.mpr ⟨r x, ?_, by dsimp [r]; omega⟩
    apply in_fringe (fun i => n+1-i ∈ s)
      (a := n+1-b) (b := n+1-a) (c := n+1-d) (d := n+1-c)
      (by omega) (by omega) (by omega) (by omega) (by dsimp [r]; omega)
      (by dsimp [r]; omega) (by dsimp [r]; omega)
    · simpa only [show n+1-(n+1-b)=b by omega] using hb
    · simpa only [show n+1-(n+1-a)=a by omega] using ha
    · simpa only [show n+1-(n+1-d)=d by omega] using pd
    · simpa only [show n+1-(n+1-c)=c by omega] using pc
  have lc : L.card ≤ 3 := fringe_cap (Finset.filter_subset _ _)
  have rc : (R.image r).card ≤ 3 := Finset.card_image_le.trans (fringe_cap (Finset.filter_subset _ _))
  have mc : M.card = 2*n-17 := by dsimp [M]; rw [Nat.card_Icc]; omega
  have h1 := Finset.card_le_card sub
  have h2 := Finset.card_union_le (L ∪ M) (R.image r)
  have h3 := Finset.card_union_le L M
  omega

end PrattUpper
open OMA.S_oeis_a039799

theorem OMA.solution : type_of% @OMA.S_oeis_a039799.main := by
  intro n hn
  obtain ⟨s, hs, hlow⟩ := PrattLower.bound n hn
  constructor
  · exact ⟨s, hs, (PrattUpper.bound n hn s hs).antisymm hlow⟩
  · rintro m ⟨t, ht, rfl⟩
    exact PrattUpper.bound n hn t ht
