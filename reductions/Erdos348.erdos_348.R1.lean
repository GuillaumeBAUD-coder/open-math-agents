import FormalConjectures.ErdosProblems.«348»

/-! # Which finite deletions destroy eventual subset-sum completeness?

This reduction follows Geneson's deletion classification (arXiv:2609.25107).
It proves the powers-of-two example and the exclusion for m ≥ 2 from a central-interval
theorem. For the exclusion it restores deleted occurrences, handles an eventually
constant sequence, proves a prefix-slack bound, and reindexes the surviving positive terms.
Credit: @JaviSoto. -/

namespace OMA.R_Erdos348_erdos_348_R1

open Finset Filter

/-- The shifted Fibonacci sequence tolerates each single deletion, but no larger deletion. -/
def H1 : Prop :=
  let a := fun i : ℕ => Nat.fib (i+1)
  ∀ n : ℕ, 1 < n → Monotone a ∧
    (∀ s : Finset ℕ, s.card = 1 → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) ∧
    ∀ t : Finset ℕ, t.card = n → ¬ IsAddCompleteNatSeq' (Function.updateFinset a t 0)

/-- Long prefixes of an unbounded complete sequence with divergent slack contain all central sums. -/
def H2 : Prop :=
  ∀ b : ℕ → ℕ, Monotone b → (∀ i, 0 < b i) → (∀ C, ∃ i, C ≤ b i) →
    IsAddCompleteNatSeq' b → (∀ C, ∀ᶠ k in atTop, b k + C ≤ ∑ i ∈ range k, b i) →
    ∃ T, ∀ᶠ k in atTop, ∀ u, T ≤ u → u + T ≤ ∑ i ∈ range k, b i →
      ∃ s : Finset ℕ, s ⊆ range k ∧ u = ∑ i ∈ s, b i

end OMA.R_Erdos348_erdos_348_R1

namespace OMA.Constructions348
open Finset Filter

private theorem prefix_covers (a : ℕ → ℕ)
    (h : ∀ k, a k ≤ (∑ i ∈ range k, a i) + 1) (k n : ℕ)
    (hn : n ≤ ∑ i ∈ range k, a i) :
    ∃ s : Finset ℕ, s ⊆ range k ∧ n = ∑ i ∈ s, a i := by
  induction k generalizing n with
  | zero =>
    exact ⟨∅, by simp, by simpa using hn⟩
  | succ k ih =>
    rw [sum_range_succ] at hn
    by_cases hs : n ≤ ∑ i ∈ range k, a i
    · obtain ⟨s, hsub, heq⟩ := ih n hs
      exact ⟨s, hsub.trans (range_mono (by omega)), heq⟩
    · have hk := h k
      obtain ⟨s, hsub, heq⟩ := ih (n - a k) (by omega)
      have hks : k ∉ s := fun hh => (by simpa using hsub hh : False)
      exact ⟨insert k s, insert_subset (by simp) (hsub.trans (range_mono (by omega))),
        by rw [sum_insert hks]; omega⟩

private theorem represented_survivors {a : ℕ → ℕ} {D : Finset ℕ} {v : ℕ}
    (hv : v ∈ subseqSums' (Function.updateFinset a D 0)) :
    ∃ S : Finset ℕ, Disjoint S D ∧ v = ∑ i ∈ S, a i := by
  obtain ⟨s, hs⟩ := hv
  refine ⟨s.filter (fun i => i ∉ D), ?_, ?_⟩
  · exact disjoint_left.mpr fun i hi => (mem_filter.mp hi).2
  · simpa [sum_filter, Function.updateFinset_def, ite_not] using hs

private theorem total_with_omitted {a : ℕ → ℕ} {s : Finset ℕ} {j k : ℕ}
    (hsub : s ⊆ range k) (hj : j < k) (hjs : j ∉ s) :
    (∑ i ∈ s, a i) + a j ≤ ∑ i ∈ range k, a i := by
  have hh : insert j s ⊆ range k := insert_subset (mem_range.mpr hj) hsub
  simpa [sum_insert hjs, Nat.add_comm] using sum_le_sum_of_subset (f := a) hh

private theorem prefix_for_sum {a : ℕ → ℕ} (ha : Monotone a) {s : Finset ℕ} {k : ℕ}
    (h : (∑ i ∈ s, a i) < a k) : s ⊆ range k := by
  intro i hi
  apply mem_range.mpr
  by_contra! hki
  exact (h.not_ge ((ha hki).trans (single_le_sum (fun j _ => Nat.zero_le (a j)) hi)))

private theorem binary_prefix (k : ℕ) : (∑ i ∈ range k, 2 ^ i : ℕ) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, pow_succ]; omega

theorem binary_witness (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ → ℕ, Monotone a ∧
      (∀ s : Finset ℕ, s.card = 0 → IsAddCompleteNatSeq' (Function.updateFinset a s 0)) ∧
      ∀ t : Finset ℕ, t.card = n → ¬ IsAddCompleteNatSeq' (Function.updateFinset a t 0) := by
  let a (i : ℕ) : ℕ := 2 ^ i
  have hmono : Monotone a := fun _ _ hij => Nat.pow_le_pow_right (by decide) hij
  refine ⟨a, hmono, ?_, ?_⟩
  · intro s hs
    have hs' : s = ∅ := card_eq_zero.mp hs
    subst s
    rw [Function.updateFinset_empty]
    apply Eventually.of_forall
    intro u
    have hsum := binary_prefix (u+1)
    have hpow := Nat.lt_two_pow_self (n := u+1)
    obtain ⟨S, _, hS⟩ := prefix_covers a (fun j => (binary_prefix j).symm.le)
      (u+1) u (by dsimp [a]; omega)
    exact ⟨S, hS⟩
  · intro t ht hc
    obtain ⟨j, hj⟩ := card_pos.mp (ht ▸ hn : 0 < t.card)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hc
    let k := N+j+1
    have hpow := Nat.lt_two_pow_self (n := k)
    have hbig : N ≤ a k - 1 := by dsimp [a, k] at *; omega
    obtain ⟨S, hdis, hS⟩ := represented_survivors (hN _ hbig)
    have hlt : (∑ i ∈ S, a i) < a k := by rw [← hS]; dsimp [a]; omega
    have hbound := total_with_omitted (a := a) (prefix_for_sum hmono hlt)
      (show j < k by dsimp [k]; omega) (fun h => disjoint_left.mp hdis h hj)
    have hsum := binary_prefix k
    have hpos : 0 < a j := Nat.pow_pos (by decide)
    change (∑ i ∈ range k, a i) + 1 = a k at hsum
    omega

end OMA.Constructions348

namespace OMA.Extend348
open Finset Filter

theorem reps_iff (a : ℕ → ℕ) (D : Finset ℕ) (v : ℕ) :
    v ∈ subseqSums' (Function.updateFinset a D 0) ↔
    ∃ S : Finset ℕ, Disjoint S D ∧ v = ∑ i ∈ S, a i := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.filter (fun i => i ∉ D), disjoint_left.mpr (fun i hi => (mem_filter.mp hi).2), ?_⟩
    simpa [sum_filter, Function.updateFinset_def, ite_not] using hs
  · rintro ⟨s, hd, hs⟩
    refine ⟨s, hs.trans (sum_congr rfl fun i hi => ?_)⟩
    simp [Function.updateFinset, disjoint_left.mp hd hi]

/-- Transfer an eventual representation after a pair deletion by changing only
the prefix. The translated sum has a representation after deleting D and j. -/
theorem extend_at (a : ℕ → ℕ) (D : Finset ℕ) (T k i j : ℕ)
    (hD : D ⊆ range k) (hi : i < k) (hj : k ≤ j)
    (hlarge : (∑ r ∈ D, a r) + 2*T ≤ a i) (hcentral : (∀ u : ℕ, T ≤ u → u + T ≤ ∑ r ∈ range k \ D, a r → ∃ s : Finset ℕ, s ⊆ range k \ D ∧ u = ∑ r ∈ s, a r))
    (hpair : IsAddCompleteNatSeq' (Function.updateFinset a {i,j} 0)) :
    IsAddCompleteNatSeq' (Function.updateFinset a (insert j D) 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpair
  apply eventually_atTop.mpr
  refine ⟨N+T, fun x hx => ?_⟩
  obtain ⟨s, hdis, hs⟩ := (reps_iff a {i,j} _).mp (hN (x-T) (by omega))
  let p := s ∩ range k
  let q := s \ range k
  have hp_sub : p ⊆ range k := inter_subset_right
  have hi_not : i ∉ p := fun h => disjoint_left.mp hdis (mem_inter.mp h).1 (by simp)
  have hp_bound : (∑ r ∈ p, a r) + a i ≤ ∑ r ∈ range k, a r := by
    have hsub := insert_subset (mem_range.mpr hi) hp_sub
    simpa [sum_insert hi_not, Nat.add_comm] using sum_le_sum_of_subset (f := a) hsub
  have hsplit := sum_sdiff (f := a) hD
  obtain ⟨p', hsub, hp'⟩ := hcentral ((∑ r ∈ p, a r)+T) (by omega) (by omega)
  have hsep : Disjoint p' q := disjoint_left.mpr fun r hr hrq =>
    (mem_sdiff.mp hrq).2 (mem_sdiff.mp (hsub hr)).1
  apply (reps_iff ..).mpr
  refine ⟨p' ∪ q, disjoint_left.mpr ?_, ?_⟩
  · intro r hr hbad
    rcases mem_union.mp hr with hp' | hq
    · obtain ⟨hrk, hrd⟩ := mem_sdiff.mp (hsub hp')
      rcases mem_insert.mp hbad with rfl | h
      · exact (Nat.not_lt.mpr hj) (mem_range.mp hrk)
      · exact hrd h
    · obtain ⟨hrs, hrk⟩ := mem_sdiff.mp hq
      rcases mem_insert.mp hbad with rfl | h
      · exact disjoint_left.mp hdis hrs (by simp)
      · exact hrk (hD h)
  · rw [sum_union hsep]
    have hsum : (∑ r ∈ p, a r) + (∑ r ∈ q, a r) = ∑ r ∈ s, a r :=
      sum_inter_add_sum_sdiff s (range k) a
    omega

/-- Every complete finite deletion of an unbounded sequence can be enlarged if
it has central intervals and every pair deletion preserves completeness. -/
theorem extend_complete (a : ℕ → ℕ) (ha : ∀ C, ∃ i, C ≤ a i) (D : Finset ℕ)
    (hc : ∃ T, ∀ᶠ k in atTop, (∀ u : ℕ, T ≤ u → u + T ≤ ∑ r ∈ range k \ D, a r → ∃ s : Finset ℕ, s ⊆ range k \ D ∧ u = ∑ r ∈ s, a r))
    (hpair : ∀ E : Finset ℕ, E.card = 2 →
      IsAddCompleteNatSeq' (Function.updateFinset a E 0)) :
    ∃ j ∉ D, IsAddCompleteNatSeq' (Function.updateFinset a (insert j D) 0) := by
  obtain ⟨T, hT⟩ := hc
  obtain ⟨K, hK⟩ := eventually_atTop.mp hT
  obtain ⟨i, hi⟩ := ha ((∑ r ∈ D, a r)+2*T)
  obtain ⟨d, hd⟩ := exists_nat_subset_range D
  let k := max (max K d) (i+1)
  have hdk : D ⊆ range k := hd.trans (range_mono (by dsimp [k]; omega))
  have hik : i < k := by dsimp [k]; omega
  exact ⟨k, fun hk => (lt_irrefl _ (mem_range.mp (hdk hk))),
    extend_at a D T k i k hdk hik le_rfl hi (hK k (by dsimp [k]; omega))
      (hpair {i,k} (by simp [hik.ne]))⟩

theorem complete_restore {a : ℕ → ℕ} {D E : Finset ℕ} (hDE : D ⊆ E)
    (h : IsAddCompleteNatSeq' (Function.updateFinset a E 0)) :
    IsAddCompleteNatSeq' (Function.updateFinset a D 0) :=
  h.mono fun v hv => by
    obtain ⟨s, hs, heq⟩ := (reps_iff ..).mp hv
    exact (reps_iff ..).mpr ⟨s, hs.mono_right hDE, heq⟩

theorem complete_of_card_le {a : ℕ → ℕ} {m : ℕ}
    (hm : ∀ E : Finset ℕ, E.card = m → IsAddCompleteNatSeq' (Function.updateFinset a E 0))
    {D : Finset ℕ} (hD : D.card ≤ m) :
    IsAddCompleteNatSeq' (Function.updateFinset a D 0) := by
  obtain ⟨E, hDE, hE⟩ := Infinite.exists_superset_card_eq D m hD
  exact complete_restore hDE (hm E hE)

/-- Geneson, Lemma 3 in original-index coordinates: zeros and deletions need
not be reindexed. The natural-number inequality expresses divergent slack. -/
theorem slack_of_singletons (a : ℕ → ℕ) (hm : Monotone a)
    (ha : ∀ C, ∃ i, C ≤ a i)
    (hsingle : ∀ i : ℕ, IsAddCompleteNatSeq' (Function.updateFinset a {i} 0))
    (D : Finset ℕ) (C : ℕ) :
    ∀ᶠ k in atTop, a k + C ≤ ∑ r ∈ range k \ D, a r := by
  obtain ⟨i, hi⟩ := ha (C + (∑ r ∈ D, a r) + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsingle i)
  obtain ⟨l, hl⟩ := ha N
  let b := max l (i+1)
  have hNb := hl.trans (hm (show l ≤ b by dsimp [b]; omega))
  obtain ⟨d, hd⟩ := exists_nat_subset_range D
  refine eventually_atTop.mpr ⟨max d (b+1), fun k hk => ?_⟩
  have hD : D ⊆ range k := hd.trans (range_mono (by omega))
  have hiK : i ∈ range k := mem_range.mpr (by dsimp [b] at *; omega)
  let P := range k \ {i}
  have hbP : b ∈ P := mem_sdiff.mpr ⟨mem_range.mpr (by omega), by dsimp [b]; simp; omega⟩
  have hNS := hNb.trans (single_le_sum (f := a) (fun r _ => Nat.zero_le _) hbP)
  obtain ⟨s, hs, hsum⟩ := (reps_iff ..).mp (hN ((∑ r ∈ P, a r)+1) (by omega))
  have hnext : a k ≤ (∑ r ∈ P, a r)+1 := by
    by_contra! hsmall
    have hsub : s ⊆ P := by
      intro r hr
      have hbound := single_le_sum (f := a) (fun r _ => Nat.zero_le _) hr
      refine mem_sdiff.mpr ⟨mem_range.mpr ?_, fun h => disjoint_left.mp hs hr h⟩
      by_contra! hkr
      have := hm hkr
      omega
    have := sum_le_sum_of_subset (f := a) hsub
    omega
  have hsplit₁ := sum_sdiff (f := a) (singleton_subset_iff.mpr hiK)
  change (∑ r ∈ P, a r) + _ = _ at hsplit₁
  rw [sum_singleton] at hsplit₁
  have hsplit₂ := sum_sdiff (f := a) hD
  omega

private theorem bounded_deletion (a : ℕ → ℕ) (hm : Monotone a) (hb : BddAbove (Set.range a))
    (hc : IsAddCompleteNatSeq' a) (n : ℕ) :
    ∃ D : Finset ℕ, D.card = n ∧ IsAddCompleteNatSeq' (Function.updateFinset a D 0) := by
  obtain ⟨k, hk⟩ := Nat.sSup_mem (Set.range_nonempty a) hb
  have hconst (i : ℕ) (hi : k ≤ i) : a i = a k :=
    le_antisymm (hk ▸ le_csSup hb (Set.mem_range_self i)) (hm hi)
  let f : ℕ ↪ ℕ := ⟨fun i => if i < k then i else i+n, by
    intro p q heq
    dsimp only at heq
    split_ifs at heq <;> omega⟩
  have hval (i : ℕ) : a (f i) = a i := by
    change a (if i < k then i else i+n) = a i
    split_ifs with h
    · rfl
    · exact (hconst _ (by omega)).trans (hconst _ (by omega)).symm
  refine ⟨Ico k (k+n), by simp, hc.mono (fun x hx => ?_)⟩
  obtain ⟨s, heq⟩ := hx
  apply (reps_iff ..).mpr
  refine ⟨s.map f, disjoint_left.mpr ?_, ?_⟩
  · intro r hr hrD
    obtain ⟨i, _, rfl⟩ := mem_map.mp hr
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hrD
    change k ≤ (if i < k then i else i+n) at hlo
    change (if i < k then i else i+n) < k+n at hhi
    split_ifs at hlo hhi <;> omega
  · simpa [sum_map, hval] using heq

theorem exclusion_of_central (a : ℕ → ℕ) (hm : Monotone a) (m n : ℕ) (hm2 : 2 ≤ m)
    (hcomplete : ∀ E : Finset ℕ, E.card = m → IsAddCompleteNatSeq' (Function.updateFinset a E 0))
    (hcentral : (∀ C, ∃ i, C ≤ a i) → ∀ D : Finset ℕ,
      IsAddCompleteNatSeq' (Function.updateFinset a D 0) →
      (∀ C, ∀ᶠ k in atTop, a k + C ≤ ∑ r ∈ range k \ D, a r) →
      ∃ T, ∀ᶠ k in atTop, (∀ u : ℕ, T ≤ u → u + T ≤ ∑ r ∈ range k \ D, a r → ∃ s : Finset ℕ, s ⊆ range k \ D ∧ u = ∑ r ∈ s, a r)) :
    ∃ D : Finset ℕ, D.card = n ∧ IsAddCompleteNatSeq' (Function.updateFinset a D 0) := by
  have hzero : IsAddCompleteNatSeq' (Function.updateFinset a ∅ 0) :=
    complete_of_card_le hcomplete (by simp)
  by_cases hu : ∀ C, ∃ i, C ≤ a i
  · induction n with
    | zero => exact ⟨∅, by simp, hzero⟩
    | succ n ih =>
      obtain ⟨D, hcard, hD⟩ := ih
      have hs (i : ℕ) : IsAddCompleteNatSeq' (Function.updateFinset a {i} 0) :=
        complete_of_card_le hcomplete (by simp; omega)
      obtain ⟨j, hj, hnew⟩ := extend_complete a hu D
        (hcentral hu D hD (slack_of_singletons a hm hu hs D)) fun E hE =>
          complete_of_card_le hcomplete (by omega)
      exact ⟨insert j D, by simp [hj, hcard], hnew⟩
  · push Not at hu
    obtain ⟨C, hC⟩ := hu
    have hbounded : BddAbove (Set.range a) := by
      refine ⟨C, ?_⟩
      rintro v ⟨i, rfl⟩
      exact (hC i).le
    exact bounded_deletion a hm hbounded (by simpa using hzero) n

end OMA.Extend348

namespace OMA.Extend348
open Finset Filter

theorem central_after_deletion (main : OMA.R_Erdos348_erdos_348_R1.H2) (a : ℕ → ℕ) (hm : Monotone a)
    (hu : ∀ C, ∃ i, C ≤ a i) (D : Finset ℕ)
    (hc : IsAddCompleteNatSeq' (Function.updateFinset a D 0))
    (hslack : ∀ C, ∀ᶠ k in atTop, a k + C ≤ ∑ r ∈ range k \ D, a r) :
    ∃ T, ∀ᶠ k in atTop, (∀ u : ℕ, T ≤ u → u + T ≤ ∑ r ∈ range k \ D, a r → ∃ s : Finset ℕ, s ⊆ range k \ D ∧ u = ∑ r ∈ s, a r) := by
  classical
  let P (i : ℕ) := i ∉ D ∧ 0 < a i
  obtain ⟨K, hK⟩ := exists_nat_subset_range D
  obtain ⟨p, hp⟩ := hu 1
  have htail : ∀ i ≥ max K p, P i := by
    intro i hi
    exact ⟨fun hiD => (by have := mem_range.mp (hK hiD); omega),
      hp.trans (hm (by omega))⟩
  have hinf : (Set.ofPred P).Infinite := (Set.Ici_infinite (max K p)).mono fun i hi => htail i hi
  let f : ℕ ↪ ℕ := ⟨Nat.nth P, Nat.nth_injective hinf⟩
  let b (i : ℕ) := a (f i)
  have hf (i : ℕ) : P (f i) := Nat.nth_mem_of_infinite hinf i
  have hstrict : StrictMono f := Nat.nth_strictMono hinf
  have hfcount {i : ℕ} (hi : P i) : f (Nat.count P i) = i := Nat.nth_count hi
  have hmap (k : ℕ) : (range (Nat.count P k)).map f =
      (range k \ D).filter (fun r => 0 < a r) := by
    ext r
    constructor
    · intro hr
      obtain ⟨l, hl, rfl⟩ := mem_map.mp hr
      have hlt : f l < k := (Nat.lt_nth_iff_count_lt hinf).mp (mem_range.mp hl)
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_range.mpr hlt, (hf l).1⟩, (hf l).2⟩
    · intro hr
      obtain ⟨hr, hpos⟩ := mem_filter.mp hr
      obtain ⟨hr, hD⟩ := mem_sdiff.mp hr
      have he := hfcount ⟨hD, hpos⟩
      apply Finset.mem_map.mpr
      exact ⟨Nat.count P r, mem_range.mpr ((Nat.lt_nth_iff_count_lt hinf).mpr
        (by change f _ < k; rw [he]; exact mem_range.mp hr)), he⟩
  have htrim (S : Finset ℕ) : (∑ i ∈ S.filter (fun r => 0 < a r), a i) = ∑ i ∈ S, a i := by
    apply sum_subset (filter_subset _ _)
    intro i hi hn
    simpa [hi] using hn
  have hsum (k : ℕ) : (∑ i ∈ range (Nat.count P k), b i) = ∑ r ∈ range k \ D, a r := by
    calc
      _ = ∑ r ∈ (range (Nat.count P k)).map f, a r := by simp [sum_map, b]
      _ = _ := (congrArg (fun s : Finset ℕ => ∑ i ∈ s, a i) (hmap k)).trans (htrim _)
  have hcomp : IsAddCompleteNatSeq' b := hc.mono fun x hx => by
    obtain ⟨S, hD, hS⟩ := (reps_iff ..).mp hx
    let A := S.filter (fun i => 0 < a i)
    have hP {r : ℕ} (hr : r ∈ A) : P r :=
      ⟨disjoint_left.mp hD (mem_filter.mp hr).1, (mem_filter.mp hr).2⟩
    refine ⟨A.image (Nat.count P), ?_⟩
    rw [sum_image (fun i hi j hj hij => by
      have := congrArg f hij
      simpa [hfcount (hP hi), hfcount (hP hj)] using this)]
    exact (hS.trans (htrim _).symm).trans (sum_congr rfl fun i hi => by
      change a i = a (f (Nat.count P i))
      rw [hfcount (hP hi)])
  have hbs (C : ℕ) : ∀ᶠ k in atTop, b k + C ≤ ∑ i ∈ range k, b i := by
    obtain ⟨K, hK⟩ := eventually_atTop.mp (hslack C)
    apply eventually_atTop.mpr
    refine ⟨K, fun k hk => ?_⟩
    have he := hsum (f k)
    rw [show Nat.count P (f k) = k from Nat.count_nth_of_infinite hinf k] at he
    exact he.symm ▸ hK (f k) (hk.trans (hstrict.id_le k))
  have hbu (C : ℕ) : ∃ i, C ≤ b i := by
    obtain ⟨i, hi⟩ := hu C
    exact ⟨i, hi.trans (hm (hstrict.id_le i))⟩
  obtain ⟨T, hT⟩ := main b (hm.comp hstrict.monotone) (fun i => (hf i).2) hbu hcomp hbs
  obtain ⟨L, hL⟩ := eventually_atTop.mp hT
  refine ⟨T, eventually_atTop.mpr ⟨f L, fun k hk => ?_⟩⟩
  intro u huT hbudget
  have hLk : L ≤ Nat.count P k := by
    have := Nat.count_monotone P hk
    rwa [show Nat.count P (f L) = L from Nat.count_nth_of_infinite hinf L] at this
  obtain ⟨s, hs, heq⟩ := hL _ hLk u huT (by rw [hsum]; exact hbudget)
  have hs' : s.map f ⊆ (range (Nat.count P k)).map f := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hr
    exact mem_map_of_mem f (hs hi)
  rw [hmap k] at hs'
  exact ⟨s.map f, hs'.trans (filter_subset _ _), by simpa [sum_map, b] using heq⟩

end OMA.Extend348

namespace OMA.R_Erdos348_erdos_348_R1

open OMA.Extend348

theorem main : H1 → H2 → type_of% @Erdos348.erdos_348 := by
  intro hFib hinterval
  ext ⟨m,n⟩
  constructor
  · rintro ⟨m', n', hmn, a, hm, hgood, hbad, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    refine ⟨hmn, ?_⟩
    by_contra! hlarge
    obtain ⟨D, hcard, hD⟩ := exclusion_of_central a hm m' n' (by omega) hgood
      (central_after_deletion hinterval a hm)
    exact hbad D hcard hD
  · rintro ⟨hmn, hsmall⟩
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · obtain ⟨a, hm, hgood, hbad⟩ := OMA.Constructions348.binary_witness n hmn
      exact ⟨0, n, hmn, a, hm, hgood, hbad, rfl⟩
    · obtain ⟨hm, hgood, hbad⟩ := hFib n hmn
      exact ⟨1, n, hmn, fun i => Nat.fib (i+1), hm, hgood, hbad, rfl⟩

end OMA.R_Erdos348_erdos_348_R1
