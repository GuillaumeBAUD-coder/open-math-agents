import OMAReductions.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1

/-! # A finite counting proof of logarithmic Ramsey graphs -/
-- Credit: @steveDOTdigital
namespace OMA.RamseyCounting
open Finset Filter

-- A bit labels each finite vertex subset. Only labels on two-element subsets form edges.
private def graph {n : ℕ} (f : Finset (Fin n) → Bool) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ f {x,y} = true
  symm := ⟨fun x y h => ⟨h.1.symm, by simpa only [Finset.pair_comm y x] using h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

private noncomputable def pattern {α : Type*} [Fintype α] [DecidableEq α] (D : Finset α) (b : Bool) :
    Finset (α → Bool) := Fintype.piFinset fun x => if x ∈ Dᶜ then univ else {b}

private lemma pattern_card {α : Type*} [Fintype α] [DecidableEq α] (D : Finset α) (b : Bool) :
    (pattern D b).card = 2^(Fintype.card α - D.card) := by
  classical
  rw [pattern, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_univ, Fintype.card_bool, card_singleton]
  simpa [Finset.card_compl] using (Fintype.prod_ite_mem Dᶜ (fun _ => (2 : ℕ)))

private lemma homogeneous_pattern {n : ℕ} (f : Finset (Fin n) → Bool) (s : Finset (Fin n))
    (hom : (graph f).IsHomogeneous (s : Set (Fin n))) :
    ∃ b, f ∈ pattern (s.powersetCard 2) b := by
  classical
  have pair {a : Finset (Fin n)} (ha : a ∈ s.powersetCard 2) :
      ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ a = {x,y} := by
    obtain ⟨sub,hc⟩ := mem_powersetCard.mp ha
    obtain ⟨x,y,h,rfl⟩ := card_eq_two.mp hc
    exact ⟨x,sub (by simp),y,sub (by simp),h,rfl⟩
  rcases hom with cl | ind
  · refine ⟨true,?_⟩
    simp only [pattern,Fintype.mem_piFinset]
    intro a
    by_cases ha : a ∈ s.powersetCard 2
    · obtain ⟨x,hx,y,hy,ne,rfl⟩ := pair ha
      simpa [ha] using (cl hx hy ne).2
    · simp [ha]
  · refine ⟨false,?_⟩
    simp only [pattern,Fintype.mem_piFinset]
    intro a
    by_cases ha : a ∈ s.powersetCard 2
    · obtain ⟨x,hx,y,hy,ne,rfl⟩ := pair ha
      have h := ind (show x ∈ (s : Set _) from hx) (show y ∈ (s : Set _) from hy) ne
      have bit : f {x,y} = false := by
        cases hf : f {x,y} <;> first | rfl | exact False.elim (h ⟨ne,hf⟩)
      simpa [ha] using bit
    · simp [ha]

private lemma count_graph (n k : ℕ) (small : n.choose k * 2 < 2^(k.choose 2)) :
    ∃ G : SimpleGraph (Fin n), ∀ s : Finset (Fin n), G.IsHomogeneous s → s.card < k := by
  classical
  by_cases kn : k ≤ n
  · let subsets := (univ : Finset (Fin n)).powersetCard k
    let patterns := fun s : Finset (Fin n) =>
      (pattern (s.powersetCard 2) false) ∪ (pattern (s.powersetCard 2) true)
    let bad := subsets.biUnion patterns
    let N := Fintype.card (Finset (Fin n))
    have cap : k.choose 2 ≤ N := by
      obtain ⟨s,_,hs⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using kn)
      simpa [hs,N] using (s.powersetCard 2).card_le_univ
    have c1 (s : Finset (Fin n)) (hs : s ∈ subsets) : (patterns s).card ≤ 2*2^(N-k.choose 2) := by
      have size := (mem_powersetCard.mp hs).2
      simpa [patterns,pattern_card, Finset.card_powersetCard,size,N,two_mul] using
        (Finset.card_union_le (pattern (s.powersetCard 2) false) (pattern (s.powersetCard 2) true))
    have ub : bad.card ≤ n.choose k*2*2^(N-k.choose 2) := calc
      _ ≤ ∑ s ∈ subsets, (patterns s).card := card_biUnion_le
      _ ≤ ∑ _s ∈ subsets, 2*2^(N-k.choose 2) := sum_le_sum c1
      _ = _ := by simp [subsets, mul_assoc]
    have eq : 2^(k.choose 2) * 2^(N-k.choose 2) = 2^N := by
      rw [←pow_add,Nat.add_sub_of_le cap]
    have strict : bad.card < (univ : Finset (Finset (Fin n) → Bool)).card := by
      have bound := ub.trans_lt (Nat.mul_lt_mul_of_pos_right small (by positivity : 0 < 2^(N-k.choose 2)))
      rw [eq] at bound
      simpa [N] using bound
    obtain ⟨f,_,hf⟩ := exists_mem_notMem_of_card_lt_card strict
    refine ⟨graph f,?_⟩
    intro s hom
    by_contra! big
    obtain ⟨t,sub,ht⟩ := exists_subset_card_eq big
    have hom' : (graph f).IsHomogeneous (t : Set (Fin n)) :=
      SimpleGraph.IsHomogeneous.subset (G := graph f) (s := (s : Set (Fin n))) (t := (t : Set (Fin n)))
        (fun _ hx => sub hx) hom
    obtain ⟨b,hb⟩ := homogeneous_pattern f t hom'
    apply hf
    apply mem_biUnion.mpr
    refine ⟨t,mem_powersetCard.mpr ⟨subset_univ _,ht⟩,?_⟩
    cases b
    · exact mem_union_left _ hb
    · exact mem_union_right _ hb
  · refine ⟨⊥,fun s _ => ?_⟩
    have hs := s.card_le_univ
    simp only [Fintype.card_fin] at hs
    omega

-- Take k = 4 (floor(log₂ n) + 2); the number of bad patterns is strictly below the total.
private lemma count_bound (n : ℕ) :
    let k := 4*(n.log2+2)
    n.choose k * 2 < 2^(k.choose 2) := by
  let l := n.log2
  let k := 4*(l+2)
  change n.choose k * 2 < 2^(k.choose 2)
  have hn : n ≤ 2^(l+1) := by
    simpa [l,Nat.log2_eq_log_two] using (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have exp : (l+1)*k+1 < k.choose 2 := by
    rw [Nat.choose_two_right]
    have sub : k-1 = 4*l+7 := by dsimp [k]; omega
    rw [sub]
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    dsimp [k]
    nlinarith
  calc
    n.choose k * 2 ≤ n^k * 2 := Nat.mul_le_mul_right _ (Nat.choose_le_pow n k)
    _ ≤ (2^(l+1))^k * 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hn k)
    _ = 2^((l+1)*k+1) := by rw [← pow_mul,pow_succ 2 ((l+1)*k)]
    _ < _ := Nat.pow_lt_pow_right (by decide) exp

theorem logarithmic : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
    ∀ s : Set (Fin n), G.IsHomogeneous s → (s.ncard : ℝ) ≤ K * Real.log n := by
  classical
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 / Real.log 2 + 8,by positivity,?_⟩
  have logs : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [logs.eventually (eventually_ge_atTop 1)] with n hlog
  obtain ⟨G,hG⟩ := count_graph n (4*(n.log2+2)) (count_bound n)
  refine ⟨G,fun s hs => ?_⟩
  have hom : G.IsHomogeneous (s.toFinset : Set (Fin n)) := by simpa using hs
  have card := (hG s.toFinset hom).le
  have size : (s.ncard : ℝ) ≤ 4*((n.log2 : ℝ)+2) := by
    exact_mod_cast (by simpa only [Set.ncard_eq_toFinset_card' s] using card : s.ncard ≤ 4*(n.log2+2))
  have bound := Real.log2_le_logb n
  rw [Real.logb] at bound
  change 1 ≤ Real.log n at hlog
  calc
    _ ≤ 4 * (Real.log n / Real.log 2 + 2) := size.trans (by linarith)
    _ ≤ (4 / Real.log 2 + 8) * Real.log n := by
      rw [add_mul]
      have e : 4 * (Real.log n / Real.log 2) = (4 / Real.log 2) * Real.log n := by ring
      linarith

end OMA.RamseyCounting

theorem OMA.solution : OMA.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1.H1 := OMA.RamseyCounting.logarithmic
