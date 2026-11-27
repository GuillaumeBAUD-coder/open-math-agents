import FormalConjectures.ErdosProblems.«337»

-- Problem: Erdős Problem 337 — h fold
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/337.lean:77 (declaration Erdos337.erdos_337.variants.h_fold)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Construction (in the spirit of Ruzsa-Turjanyi). Let g = h + 1.
-- * B: numbers whose binary digits all sit in one residue class of positions mod g. Every n is a
--   sum of g elements of B (split its binary digits by position mod g), and B has at most
--   g 2^t elements below 2^(g t), so B has density zero.
-- * Chunks I_k = (N_k - L_k, N_k] with N_k = 2^(g t_k), L_k = N_k / 2^k, t_k = (4gh)^(k+1).
-- A = B together with all chunks is a basis of order g of density zero. At N = N_k, any h-fold sum
-- that is at most N_k either uses a chunk-k element (so lies in I_k: at most L_k values) or uses
-- only elements below N_k - L_k, of which there are at most 2g 2^(t_k); their h-fold sums number
-- at most (2g 2^(t_k))^h <= L_k. So |hA ∩ [1,N_k]| <= 2 L_k <= 2 |A ∩ [1,N_k]|.

open Filter Set Asymptotics
open scoped Pointwise

namespace OMA337
def E (g r : ℕ) (S : Finset ℕ) : ℕ := ∑ i ∈ S, 2 ^ (g * i + r)

def B (g : ℕ) : Set ℕ := {x | ∃ r < g, ∃ S : Finset ℕ, x = E g r S}

lemma part_eq (g r : ℕ) (hr : r < g) (T : Finset ℕ) :
    E g r ((T.filter (fun i => i % g = r)).image (· / g)) =
      ∑ i ∈ T.filter (fun i => i % g = r), 2 ^ i := by
  unfold E
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter] at hi
    congr 1
    have := Nat.div_add_mod i g
    omega
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hj
    have h1 := Nat.div_add_mod i g
    have h2 := Nat.div_add_mod j g
    simp only at hij
    rw [← h1, ← h2, hij, hi.2, hj.2]

lemma decomp (g : ℕ) (hg : 0 < g) (n : ℕ) :
    ∃ f : Fin g → ℕ, (∀ r, f r ∈ B g) ∧ ∑ r, f r = n := by
  classical
  set T := n.bitIndices.toFinset
  refine ⟨fun r => E g r ((T.filter (fun i => i % g = (r : ℕ))).image (· / g)), ?_, ?_⟩
  · intro r
    exact ⟨r, r.2, _, rfl⟩
  · simp only
    rw [Fin.sum_univ_eq_sum_range (fun r => E g r ((T.filter (fun i => i % g = r)).image (· / g)))]
    rw [Finset.sum_congr rfl (fun r hr => part_eq g r (Finset.mem_range.mp hr) T)]
    rw [Finset.sum_fiberwise_of_maps_to (g := fun i => i % g) (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i hg))]
    exact Finset.sum_toFinset_bitIndices_two_pow n

lemma E_lt (g r t : ℕ) (S : Finset ℕ) (h : E g r S < 2 ^ (g * t)) : S ⊆ Finset.range t := by
  intro i hi
  have : 2 ^ (g * i + r) ≤ E g r S := Finset.single_le_sum (f := fun i => 2 ^ (g * i + r))
    (fun _ _ => Nat.zero_le _) hi
  have h2 : g * i + r < g * t := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt this h)
  rw [Finset.mem_range]
  by_contra hc
  push Not at hc
  have : g * t ≤ g * i := Nat.mul_le_mul_left g hc
  omega

noncomputable def Bfin (g t : ℕ) : Finset ℕ :=
  (Finset.range g).biUnion fun r => (Finset.range t).powerset.image (E g r)

lemma Bfin_card (g t : ℕ) : (Bfin g t).card ≤ g * 2 ^ t := by
  unfold Bfin
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ r ∈ Finset.range g, ((Finset.range t).powerset.image (E g r)).card
      ≤ ∑ r ∈ Finset.range g, 2 ^ t := by
        apply Finset.sum_le_sum; intro r _
        exact (Finset.card_image_le).trans (by simp)
    _ = g * 2 ^ t := by simp

lemma B_sub (g t x : ℕ) (hx : x ∈ B g) (hlt : x < 2 ^ (g * t)) : x ∈ Bfin g t := by
  obtain ⟨r, hr, S, rfl⟩ := hx
  unfold Bfin
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_powerset]
  exact ⟨r, hr, S, E_lt g r t S hlt, rfl⟩


section
variable (h : ℕ)

def gg : ℕ := h + 1
def CC : ℕ := 4 * gg h * h
def tt (k : ℕ) : ℕ := CC h ^ (k + 1)
def NN (k : ℕ) : ℕ := 2 ^ (gg h * tt h k)
def LL (k : ℕ) : ℕ := 2 ^ (gg h * tt h k - k)
def II (k : ℕ) : Finset ℕ := Finset.Ioc (NN h k - LL h k) (NN h k)
def AA : Set ℕ := B (gg h) ∪ {x | ∃ k, x ∈ II h k}

variable {h}

lemma CC_ge (hh : 2 ≤ h) : 2 * gg h * h + 1 ≤ CC h ∧ gg h + 1 ≤ CC h ∧ 2 ≤ CC h := by
  unfold CC gg; refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma tt_pos (hh : 2 ≤ h) (k : ℕ) : 1 ≤ tt h k := Nat.one_le_pow _ _ (by have := CC_ge hh; omega)

lemma tt_rec (hh : 2 ≤ h) (k : ℕ) : gg h * tt h k + 1 ≤ tt h (k + 1) := by
  have h1 := CC_ge hh
  have h2 := tt_pos hh k
  have : tt h (k + 1) = CC h * tt h k := by unfold tt; ring
  rw [this]; nlinarith

lemma tt_big (hh : 2 ≤ h) (k : ℕ) : 2 * gg h * h + k ≤ tt h k := by
  have h1 := CC_ge hh
  have h3 : k + 1 ≤ CC h ^ k := by
    have := Nat.lt_pow_self (n := k) (show 1 < CC h by omega)
    omega
  have : tt h k = CC h * CC h ^ k := by unfold tt; ring
  rw [this]; nlinarith

lemma tt_mono (hh : 2 ≤ h) {k j : ℕ} (hkj : k ≤ j) : tt h k ≤ tt h j := by
  unfold tt; exact Nat.pow_le_pow_right (by have := CC_ge hh; omega) (by omega)

lemma gg_ge (hh : 2 ≤ h) : 3 ≤ gg h := by unfold gg; omega

lemma k_le (hh : 2 ≤ h) (k : ℕ) : k + 1 ≤ gg h * tt h k := by
  have := tt_big hh k; have := gg_ge hh; nlinarith

lemma LL_mul (hh : 2 ≤ h) (k : ℕ) : LL h k * 2 ^ k = NN h k := by
  unfold LL NN; rw [← pow_add]; congr 1; have := k_le hh k; omega

lemma LL_pos (k : ℕ) : 1 ≤ LL h k := Nat.one_le_two_pow

lemma LL_half (hh : 2 ≤ h) (k : ℕ) (hk : 1 ≤ k) : 2 * LL h k ≤ NN h k := by
  rw [← LL_mul hh k]
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  nlinarith [LL_pos (h := h) k]

lemma NN_mono (hh : 2 ≤ h) {k j : ℕ} (hkj : k ≤ j) : NN h k ≤ NN h j := by
  unfold NN; exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (tt_mono hh hkj))

-- elements of later chunks are larger than NN k
lemma later (hh : 2 ≤ h) {k j x : ℕ} (hkj : k < j) (hx : x ∈ II h j) : NN h k < x := by
  unfold II at hx
  rw [Finset.mem_Ioc] at hx
  have h1 := LL_half hh j (by omega)
  have h2 : 2 * NN h k + 1 ≤ NN h j := by
    have e1 := tt_rec hh k
    have e2 := tt_mono hh (show k + 1 ≤ j by omega)
    have e3 : gg h * tt h k + 2 ≤ gg h * tt h j := by
      have := gg_ge hh; have := tt_pos hh k; nlinarith
    unfold NN
    calc 2 * 2 ^ (gg h * tt h k) + 1 ≤ 2 * 2 ^ (gg h * tt h k) + 2 * 2 ^ (gg h * tt h k) := by
          have := Nat.one_le_two_pow (n := gg h * tt h k); omega
      _ = 2 ^ (gg h * tt h k + 1) * 2 := by ring
      _ ≤ 2 ^ (gg h * tt h j) := by
          rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma basis (hh : 2 ≤ h) : (AA h).IsAsymptoticAddBasis := by
  refine ⟨gg h, ?_⟩
  refine Filter.Eventually.of_forall fun n => ?_
  obtain ⟨f, hf, hs⟩ := decomp (gg h) (by have := gg_ge hh; omega) n
  rw [Set.mem_nsmul]
  refine ⟨fun r => ⟨f r, Or.inl (hf r)⟩, ?_⟩
  simp only [List.sum_ofFn]
  exact hs

end

section
variable {h : ℕ}

lemma II_sub (k : ℕ) : (II h k : Set ℕ) ⊆ AA h ∩ Icc 1 (NN h k) := by
  intro x hx
  refine ⟨Or.inr ⟨k, hx⟩, ?_⟩
  simp only [II, Finset.coe_Ioc, Set.mem_Ioc] at hx
  exact ⟨by omega, hx.2⟩

lemma lower (k : ℕ) : LL h k ≤ (AA h ∩ Icc 1 (NN h k)).ncard := by
  have hc : (II h k).card = LL h k := by
    unfold II; rw [Nat.card_Ioc]
    have : LL h k ≤ NN h k := by
      unfold LL NN; exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    omega
  rw [← hc, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (II_sub k) ((Set.finite_Icc _ _).subset Set.inter_subset_right)

noncomputable def DD (h j : ℕ) : Finset ℕ := Bfin (gg h) (tt h (j + 1)) ∪ Finset.range (NN h j + 1)

lemma DD_card (hh : 2 ≤ h) (j : ℕ) : (DD h j).card ^ h ≤ LL h (j + 1) := by
  have c1 : (DD h j).card ≤ gg h * 2 ^ tt h (j + 1) + (NN h j + 1) :=
    (Finset.card_union_le _ _).trans (by
      have := Bfin_card (gg h) (tt h (j + 1)); simp only [Finset.card_range]; omega)
  have c2 : NN h j + 1 ≤ 2 ^ tt h (j + 1) := by
    unfold NN
    calc 2 ^ (gg h * tt h j) + 1 ≤ 2 ^ (gg h * tt h j) * 2 := by
          have := Nat.one_le_two_pow (n := gg h * tt h j); omega
      _ = 2 ^ (gg h * tt h j + 1) := by ring
      _ ≤ 2 ^ tt h (j + 1) := Nat.pow_le_pow_right (by norm_num) (tt_rec hh j)
  have c3 : (DD h j).card ≤ 2 * gg h * 2 ^ tt h (j + 1) := by have := gg_ge hh; nlinarith
  have c4 : 2 * gg h ≤ 2 ^ (2 * gg h) := (Nat.lt_two_pow_self).le
  set t := tt h (j + 1)
  have c5 : 2 * gg h * h + (j + 1) ≤ t := tt_big hh (j + 1)
  calc (DD h j).card ^ h ≤ (2 * gg h * 2 ^ t) ^ h := Nat.pow_le_pow_left c3 h
    _ = (2 * gg h) ^ h * 2 ^ (t * h) := by rw [mul_pow, ← pow_mul]
    _ ≤ (2 ^ (2 * gg h)) ^ h * 2 ^ (t * h) := by
        apply Nat.mul_le_mul_right; exact Nat.pow_le_pow_left c4 h
    _ = 2 ^ (2 * gg h * h + t * h) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (gg h * t - (j + 1)) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : gg h * t = t * h + t := by unfold gg; ring
        omega
    _ = LL h (j + 1) := rfl

lemma upper (hh : 2 ≤ h) (j : ℕ) :
    ((h • AA h) ∩ Icc 1 (NN h (j + 1))).ncard ≤ 2 * LL h (j + 1) := by
  classical
  set k := j + 1 with hk_def
  have hsub : (h • AA h) ∩ Icc 1 (NN h k) ⊆ ↑(II h k ∪ h • DD h j) := by
    rintro x ⟨hx, hx1⟩
    rw [Set.mem_nsmul] at hx
    obtain ⟨f, rfl⟩ := hx
    have hle : ∀ i, (f i : ℕ) ≤ (List.ofFn fun i => (f i : ℕ)).sum := fun i =>
      List.le_sum_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    by_cases hbig : ∃ i, NN h k - LL h k < (f i : ℕ)
    · left
      obtain ⟨i, hi⟩ := hbig
      simp only [II, Finset.mem_Ioc]
      exact ⟨lt_of_lt_of_le hi (hle i), hx1.2⟩
    · right
      push Not at hbig
      rw [Finset.mem_nsmul]
      have hmem : ∀ i, (f i : ℕ) ∈ DD h j := by
        intro i
        have hi := hbig i
        have hA := (f i).2
        have hL := LL_pos (h := h) k
        have hNk : LL h k ≤ NN h k := by
          unfold LL NN; exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
        rcases hA with hB | ⟨m, hm⟩
        · apply Finset.mem_union_left
          exact B_sub _ _ _ hB (show (f i : ℕ) < NN h k by omega)
        · apply Finset.mem_union_right
          rw [Finset.mem_range]
          rcases lt_trichotomy m k with hmk | hmk | hmk
          · have : (f i : ℕ) ≤ NN h m := by
              simp only [II, Finset.mem_Ioc] at hm; exact hm.2
            have := NN_mono hh (show m ≤ j by omega)
            omega
          · subst hmk
            simp only [II, Finset.mem_Ioc] at hm; omega
          · have := later hh hmk hm
            omega
      exact ⟨fun i => ⟨f i, hmem i⟩, rfl⟩
  calc ((h • AA h) ∩ Icc 1 (NN h k)).ncard ≤ (II h k ∪ h • DD h j).card := by
        rw [← Set.ncard_coe_finset]; exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ (II h k).card + (h • DD h j).card := Finset.card_union_le _ _
    _ ≤ LL h k + (DD h j).card ^ h := by
        apply add_le_add
        · have : LL h k ≤ NN h k := by
            unfold LL NN; exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
          unfold II; rw [Nat.card_Ioc]; omega
        · exact Finset.card_nsmul_le
    _ ≤ 2 * LL h k := by have := DD_card hh j; rw [hk_def]; omega

end

section
variable {h : ℕ}

lemma NN_ge (hh : 2 ≤ h) (k : ℕ) : k < NN h k := by
  unfold NN
  calc k < 2 ^ k := Nat.lt_two_pow_self
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by have := k_le hh k; omega)

lemma chunk_card (hh : 2 ≤ h) (N k : ℕ) (hk : 1 ≤ k) :
    (((II h k).filter (· ≤ N)).card : ℝ) ≤ 2 * N * (1 / 2) ^ k := by
  by_cases hne : ((II h k).filter (· ≤ N)).Nonempty
  · obtain ⟨x, hx⟩ := hne
    simp only [II, Finset.mem_filter, Finset.mem_Ioc] at hx
    have h1 := LL_half hh k hk
    have h2 := LL_mul hh k
    have h3 : LL h k * 2 ^ k ≤ 2 * N := by omega
    have hc : ((II h k).filter (· ≤ N)).card ≤ LL h k := by
      refine (Finset.card_filter_le _ _).trans ?_
      unfold II; rw [Nat.card_Ioc]; omega
    have h3' : (LL h k : ℝ) * 2 ^ k ≤ 2 * N := by exact_mod_cast h3
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    calc (((II h k).filter (· ≤ N)).card : ℝ) ≤ LL h k := by exact_mod_cast hc
      _ ≤ 2 * N / 2 ^ k := by rw [le_div_iff₀ hp]; exact h3'
      _ = 2 * N * (1 / 2) ^ k := by rw [one_div, inv_pow, div_eq_mul_inv]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

lemma geom_tail (K M : ℕ) : ∑ k ∈ Finset.Ico K M, ((1 : ℝ) / 2) ^ k ≤ 2 * (1 / 2) ^ K := by
  rcases le_or_gt K M with hKM | hKM
  · rw [Finset.sum_Ico_eq_sum_range]
    simp_rw [pow_add]
    rw [← Finset.mul_sum]
    have := sum_geometric_two_le (M - K)
    have hp : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
    nlinarith
  · rw [Finset.Ico_eq_empty (by omega)]; simp

lemma density_bound (hh : 2 ≤ h) (K N : ℕ) (hK : 1 ≤ K) :
    ((AA h ∩ Icc 1 N).ncard : ℝ) ≤
      gg h * 2 ^ (Nat.log 2 N / gg h + 1) + (NN h K + 1) + 4 * N * (1 / 2) ^ K := by
  classical
  set s := Nat.log 2 N / gg h + 1
  let F : Finset ℕ := Bfin (gg h) s ∪ Finset.range (NN h K + 1) ∪
    (Finset.Ico K (2 * N + 1)).biUnion (fun k => (II h k).filter (· ≤ N))
  have hsub : AA h ∩ Icc 1 N ⊆ ↑F := by
    rintro x ⟨hA, hx⟩
    rw [Set.mem_Icc] at hx
    simp only [F, Finset.coe_union, Finset.coe_biUnion, Set.mem_union, Finset.mem_coe,
      Set.mem_iUnion, Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    rcases hA with hB | ⟨k, hk⟩
    · left; left
      apply B_sub _ _ _ hB
      have e1 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
      have e2 : Nat.log 2 N + 1 ≤ gg h * s := by
        have := Nat.div_add_mod (Nat.log 2 N) (gg h)
        have := Nat.mod_lt (Nat.log 2 N) (show 0 < gg h by have := gg_ge hh; omega)
        simp only [s]; rw [mul_add]; omega
      calc x ≤ N := hx.2
        _ < 2 ^ (Nat.log 2 N + 1) := e1
        _ ≤ 2 ^ (gg h * s) := Nat.pow_le_pow_right (by norm_num) e2
    · by_cases hkK : k < K
      · left; right
        have : x ≤ NN h k := by simp only [II, Finset.mem_Ioc] at hk; exact hk.2
        have := NN_mono hh hkK.le
        omega
      · right
        refine ⟨k, ⟨by omega, ?_⟩, hk, hx.2⟩
        have h1 := LL_half hh k (by omega)
        have h2 := NN_ge hh k
        simp only [II, Finset.mem_Ioc] at hk
        omega
  have hF : ((AA h ∩ Icc 1 N).ncard : ℝ) ≤ F.card := by
    rw [← Set.ncard_coe_finset F]; exact_mod_cast Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  refine hF.trans ?_
  have c1 : (F.card : ℝ) ≤ (Bfin (gg h) s).card + (NN h K + 1) +
      ∑ k ∈ Finset.Ico K (2 * N + 1), (((II h k).filter (· ≤ N)).card : ℝ) := by
    have a1 := Finset.card_union_le (Bfin (gg h) s ∪ Finset.range (NN h K + 1))
      ((Finset.Ico K (2 * N + 1)).biUnion (fun k => (II h k).filter (· ≤ N)))
    have a2 := Finset.card_union_le (Bfin (gg h) s) (Finset.range (NN h K + 1))
    have a3 := Finset.card_biUnion_le (s := Finset.Ico K (2 * N + 1))
      (t := fun k => (II h k).filter (· ≤ N))
    rw [Finset.card_range] at a2
    have : (F.card : ℕ) ≤ (Bfin (gg h) s).card + (NN h K + 1) +
        ∑ k ∈ Finset.Ico K (2 * N + 1), ((II h k).filter (· ≤ N)).card := by
      simp only [F]; omega
    exact_mod_cast this
  have c2 : ((Bfin (gg h) s).card : ℝ) ≤ gg h * 2 ^ s := by exact_mod_cast Bfin_card _ _
  have c3 : ∑ k ∈ Finset.Ico K (2 * N + 1), (((II h k).filter (· ≤ N)).card : ℝ) ≤
      4 * N * (1 / 2) ^ K := by
    calc _ ≤ ∑ k ∈ Finset.Ico K (2 * N + 1), 2 * (N : ℝ) * (1 / 2) ^ k := by
          apply Finset.sum_le_sum; intro k hk
          rw [Finset.mem_Ico] at hk
          exact chunk_card hh N k (by omega)
      _ = 2 * N * ∑ k ∈ Finset.Ico K (2 * N + 1), ((1 : ℝ) / 2) ^ k := by rw [Finset.mul_sum]
      _ ≤ 2 * N * (2 * (1 / 2) ^ K) := by
          apply mul_le_mul_of_nonneg_left (geom_tail _ _); positivity
      _ = 4 * N * (1 / 2) ^ K := by ring
  linarith

end

section
variable {h : ℕ}

lemma littleO (hh : 2 ≤ h) :
    (fun N : ℕ ↦ ((AA h ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hg3 := gg_ge hh
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 12 by positivity)
    (show (1 : ℝ) / 2 < 1 by norm_num)
  set K := n0 + 1
  have hK : ((1 : ℝ) / 2) ^ K ≤ ε / 12 := by
    have : ((1 : ℝ) / 2) ^ K ≤ (1 / 2) ^ n0 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  set M := ⌈6 * (gg h : ℝ) / ε⌉₊
  filter_upwards [eventually_ge_atTop (2 ^ (gg h * M)),
    eventually_ge_atTop ⌈3 * ((NN h K : ℝ) + 1) / ε⌉₊, eventually_ge_atTop 1] with N hN1 hN2 hN3
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN3
  have hd := density_bound hh K N (by omega)
  set a := Nat.log 2 N / gg h
  have hlog : gg h * M ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hN1
  have haM : M ≤ a := by
    rw [Nat.le_div_iff_mul_le (by omega)]; linarith [mul_comm (gg h) M]
  have hm_ge : (M : ℝ) + 1 ≤ 2 ^ a := by
    have : M + 1 ≤ 2 ^ a := by
      have := Nat.lt_two_pow_self (n := a); omega
    exact_mod_cast this
  have hmM : 6 * (gg h : ℝ) / ε ≤ 2 ^ a := by
    have := Nat.le_ceil (6 * (gg h : ℝ) / ε); linarith
  have hm2 : ((2 : ℝ) ^ a) ^ 2 ≤ N := by
    have e1 : a * gg h ≤ Nat.log 2 N := Nat.div_mul_le_self _ _
    have e2 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
    have e3 : (2 ^ a) ^ 2 ≤ N := by
      calc (2 ^ a) ^ 2 = 2 ^ (a * 2) := by rw [pow_mul]
        _ ≤ 2 ^ (a * gg h) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
        _ ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right (by norm_num) e1
        _ ≤ N := e2
    exact_mod_cast e3
  have hB : (gg h : ℝ) * 2 ^ (a + 1) ≤ ε * N / 3 := by
    have hm0 : (0 : ℝ) < 2 ^ a := by positivity
    have : (6 * (gg h : ℝ)) ≤ ε * 2 ^ a := by
      rw [div_le_iff₀ hε] at hmM; linarith
    rw [pow_succ]
    nlinarith
  have hC : (NN h K : ℝ) + 1 ≤ ε * N / 3 := by
    have := Nat.le_ceil (3 * ((NN h K : ℝ) + 1) / ε)
    have h2 : 3 * ((NN h K : ℝ) + 1) / ε ≤ N := le_trans this (by exact_mod_cast hN2)
    rw [div_le_iff₀ hε] at h2; linarith
  have hD : 4 * (N : ℝ) * (1 / 2) ^ K ≤ ε * N / 3 := by nlinarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  linarith

lemma not_tendsto (hh : 2 ≤ h) :
    ¬ Tendsto (fun N : ℕ ↦ ((h • AA h ∩ Icc 1 N).ncard : ℝ) / ((AA h ∩ Icc 1 N).ncard : ℝ))
      atTop atTop := by
  intro ht
  obtain ⟨N0, hN0⟩ := (ht.eventually_gt_atTop 2).exists_forall_of_atTop
  have hge : N0 ≤ NN h (N0 + 1) := by have := NN_ge hh (N0 + 1); omega
  have h1 := hN0 _ hge
  have up := upper hh N0
  have lo := lower (h := h) (N0 + 1)
  have hL := LL_pos (h := h) (N0 + 1)
  have up' : ((h • AA h ∩ Icc 1 (NN h (N0 + 1))).ncard : ℝ) ≤ 2 * LL h (N0 + 1) := by
    exact_mod_cast up
  have lo' : (LL h (N0 + 1) : ℝ) ≤ (AA h ∩ Icc 1 (NN h (N0 + 1))).ncard := by exact_mod_cast lo
  have hL' : (1 : ℝ) ≤ LL h (N0 + 1) := by exact_mod_cast hL
  have hpos : (0 : ℝ) < (AA h ∩ Icc 1 (NN h (N0 + 1))).ncard := by linarith
  rw [lt_div_iff₀ hpos] at h1
  linarith

theorem main : ∀ h : ℕ, 2 ≤ h →
    ∃ A : Set ℕ, A.IsAsymptoticAddBasis ∧
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) ∧
      ¬ Tendsto (fun N : ℕ ↦
          ((h • A ∩ Icc 1 N).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop :=
  fun _ hh => ⟨_, basis hh, littleO hh, not_tendsto hh⟩

end
end OMA337

theorem OMA.solution : type_of% @Erdos337.erdos_337.variants.h_fold := OMA337.main
