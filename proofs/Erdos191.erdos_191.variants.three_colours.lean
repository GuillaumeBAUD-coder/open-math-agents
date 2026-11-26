import FormalConjectures.ErdosProblems.«191»

/-! Three colors suffice to keep all monochromatic logarithmic weights bounded. -/

open Finset

namespace OMA

lemma smallMonochromaticSubsets (A : Type*) [Fintype A] (L : ℕ)
    (hA : Fintype.card A ≤ 2 ^ L) :
    ∃ c : Finset A → Bool, ∀ X : Finset A,
      (∃ b, ∀ e ∈ X.powersetCard 2, c e = b) → X.card < 2 * L + 3 := by
  classical
  let k := 2 * L + 3
  by_cases hk : k ≤ Fintype.card A
  swap
  · exact ⟨fun _ => false, fun X _ => (card_le_univ X).trans_lt (lt_of_not_ge hk)⟩
  let bad (b : Bool) (X : Finset A) : Finset (Finset A → Bool) :=
    univ.filter fun c => ∀ e ∈ X.powersetCard 2, c e = b
  let N := Fintype.card (Finset A)
  have hbad (b : Bool) (X : Finset A) (hX : X.card = k) :
      (bad b X).card ≤ 2 ^ (N - k.choose 2) := by
    let W := (X.powersetCard 2)ᶜ
    let f : (bad b X) ↪ (W → Bool) :=
      ⟨fun c e => c.val e.val, by
        intro c d h
        apply Subtype.ext
        funext e
        by_cases he : e ∈ X.powersetCard 2
        · exact ((Finset.mem_filter.mp c.property).2 e he).trans
            (((Finset.mem_filter.mp d.property).2 e he).symm)
        · exact congrFun h ⟨e, Finset.mem_compl.mpr he⟩⟩
    have hcard := Fintype.card_le_of_embedding f
    simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool,
      W, Finset.card_compl, Finset.card_powersetCard, hX, N] using hcard
  let configurations := (univ : Finset Bool) ×ˢ (univ : Finset A).powersetCard k
  let badColorings := configurations.biUnion fun i => bad i.1 i.2
  have hbadColorings : badColorings.card ≤ configurations.card * 2 ^ (N - k.choose 2) := by
    refine Finset.card_biUnion_le_card_mul _ _ _ fun i hi => ?_
    exact hbad _ _ (Finset.mem_powersetCard.mp (Finset.mem_product.mp hi).2).2
  have hix : configurations.card ≤ 2 ^ (L * k + 1) := by
    simp only [configurations, Finset.card_product, Finset.card_univ, Fintype.card_bool, Finset.card_powersetCard]
    calc
      _ ≤ 2 * (Fintype.card A) ^ k := Nat.mul_le_mul_left 2 (Nat.choose_le_pow _ _)
      _ ≤ 2 * (2 ^ L) ^ k := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hA _)
      _ = _ := by rw [← pow_mul, pow_succ, mul_comm]
  have hchoose : k.choose 2 = k * (L + 1) := by
    rw [Nat.choose_two_right, show k - 1 = (L + 1) * 2 by dsimp [k]; omega, ← Nat.mul_assoc]
    simp
  have hstrict : L * k + 1 < k.choose 2 := by
    rw [hchoose, show k * (L + 1) = L * k + k by ring]
    have : 1 < k := by dsimp [k]; omega
    omega
  have hn : k.choose 2 ≤ N := by
    obtain ⟨X, _, hX⟩ := Finset.exists_subset_card_eq
      (show k ≤ (univ : Finset A).card by simpa using hk)
    rw [← hX, ← Finset.card_powersetCard]
    exact Finset.card_le_univ _
  have hsmall : badColorings.card < (univ : Finset (Finset A → Bool)).card := by
    calc
      _ ≤ configurations.card * 2 ^ (N - k.choose 2) := hbadColorings
      _ ≤ 2 ^ (L * k + 1) * 2 ^ (N - k.choose 2) := Nat.mul_le_mul_right _ hix
      _ = 2 ^ (L * k + 1 + (N - k.choose 2)) := (pow_add _ _ _).symm
      _ < 2 ^ N := Nat.pow_lt_pow_right (by decide) (by omega)
      _ = _ := by simp [N]
  have hx : ∃ c : Finset A → Bool, c ∉ badColorings := by
    by_contra! h
    exact hsmall.not_ge (Finset.card_le_card (fun x _ => h x))
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, fun X hX => ?_⟩
  by_contra! hXlarge
  obtain ⟨Y, hYX, hY⟩ := Finset.exists_subset_card_eq hXlarge
  obtain ⟨b, hb⟩ := hX
  apply hc
  refine Finset.mem_biUnion.mpr ⟨(b, Y), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨mem_univ _, Finset.mem_powersetCard.mpr ⟨subset_univ _, hY⟩⟩
  · refine Finset.mem_filter.mpr ⟨mem_univ _, fun e he => hb e ?_⟩
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp he
    exact Finset.mem_powersetCard.mpr ⟨hsub.trans hYX, hcard⟩

def weightedBlockStart (j : ℕ) : ℕ := 2 ^ (2 ^ j)
def weightedBlock (x : ℕ) : ℕ := Nat.log 2 (Nat.log 2 x)

lemma weightedBlockStart_pos (j : ℕ) : 0 < weightedBlockStart j := by
  unfold weightedBlockStart
  positivity

lemma weightedBlock_bounds {x : ℕ} (hx : 2 ≤ x) :
    weightedBlockStart (weightedBlock x) ≤ x ∧ x < weightedBlockStart (weightedBlock x + 1) := by
  have hl : 0 < Nat.log 2 x := Nat.log_pos (by decide) hx
  unfold weightedBlockStart weightedBlock
  constructor
  · exact (Nat.pow_le_pow_right (by decide : (0 : ℕ) < 2)
      (Nat.pow_log_le_self 2 hl.ne')).trans (Nat.pow_log_le_self 2 (by omega))
  · refine (Nat.lt_pow_succ_log_self (by decide : (1 : ℕ) < 2) x).trans_le ?_
    apply Nat.pow_le_pow_right (by decide : (0 : ℕ) < 2)
    have h := Nat.lt_pow_succ_log_self (by decide : (1 : ℕ) < 2) (Nat.log 2 x)
    exact Nat.succ_le_of_lt h

lemma weightedBlock_weight {j x : ℕ} (hx : weightedBlockStart j ≤ x) :
    1 / Real.log (x : ℝ) ≤ 1 / ((2 : ℝ) ^ j * Real.log 2) := by
  have hp : 0 < (weightedBlockStart j : ℝ) := by exact_mod_cast weightedBlockStart_pos j
  have hle : (weightedBlockStart j : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlog := Real.log_le_log hp hle
  simp only [weightedBlockStart, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog
  exact one_div_le_one_div_of_le (mul_pos (by positivity) (Real.log_pos (by norm_num))) hlog

lemma weightedBlock_weight_geometric (j : ℕ) :
    1 / ((2 : ℝ) ^ j * Real.log 2) = (1 / Real.log 2) * (1 / 2 : ℝ) ^ j := by
  calc
    _ = (1 / Real.log 2) * (1 / (2 : ℝ) ^ j) := (one_div_mul_one_div_rev (Real.log 2) ((2 : ℝ) ^ j)).symm
    _ = _ := by simp [one_div, inv_pow]

lemma weightedBlock_sum_across {A : Type*} (X : Finset A) (v j : A → ℕ)
    (hj : Set.InjOn j (X : Set A))
    (hbound : ∀ x ∈ X, weightedBlockStart (j x) ≤ v x) :
    (∑ x ∈ X, 1 / Real.log (v x : ℝ)) ≤ 2 / Real.log 2 := by
  let a : ℝ := 1 / 2
  have ha : ‖a‖ < 1 := by norm_num [a, Real.norm_eq_abs]
  have hs : Summable (fun i : ℕ => a ^ i) := summable_geometric_of_norm_lt_one ha
  have ht : (∑' i : ℕ, a ^ i) = 2 := by
    rw [tsum_geometric_of_norm_lt_one ha]
    norm_num [a]
  have hpartial : (∑ i ∈ X.image j, a ^ i) ≤ ∑' i : ℕ, a ^ i :=
    hs.sum_le_tsum (X.image j) (fun i _ => by positivity)
  rw [ht] at hpartial
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ ∑ x ∈ X, (1 / Real.log 2) * a ^ (j x) := by
      refine Finset.sum_le_sum fun x hx => ?_
      exact (weightedBlock_weight (hbound x hx)).trans_eq (weightedBlock_weight_geometric _)
    _ = (1 / Real.log 2) * ∑ i ∈ X.image j, a ^ i := by
      rw [Finset.mul_sum, Finset.sum_image (fun x hx y hy h => hj hx hy h)]
    _ ≤ (1 / Real.log 2) * 2 := mul_le_mul_of_nonneg_left hpartial (by positivity)
    _ = _ := by ring

lemma weightedBlock_sum_within {A : Type*} (X : Finset A) (v : A → ℕ) (j : ℕ)
    (hbound : ∀ x ∈ X, weightedBlockStart j ≤ v x)
    (hcard : X.card < 2 * 2 ^ (j + 1) + 3) :
    (∑ x ∈ X, 1 / Real.log (v x : ℝ)) ≤ 7 / Real.log 2 := by
  have hpow : 1 ≤ (2 : ℕ) ^ j := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ] at hcard
  have hsize : X.card ≤ 7 * (2 : ℕ) ^ j := by omega
  have hsizeR : (X.card : ℝ) ≤ 7 * (2 : ℝ) ^ j := by exact_mod_cast hsize
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ ∑ _x ∈ X, 1 / ((2 : ℝ) ^ j * Real.log 2) :=
      Finset.sum_le_sum fun x hx => weightedBlock_weight (hbound x hx)
    _ = (X.card : ℝ) * (1 / ((2 : ℝ) ^ j * Real.log 2)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (7 * (2 : ℝ) ^ j) * (1 / ((2 : ℝ) ^ j * Real.log 2)) :=
      mul_le_mul_of_nonneg_right hsizeR (by positivity)
    _ = _ := by field_simp [hlog.ne', pow_ne_zero j (by norm_num : (2 : ℝ) ≠ 0)]

end OMA

theorem OMA.solution : type_of% @Erdos191.erdos_191.variants.three_colours := by
  classical
  refine ⟨8 / Real.log 2, fun n => ?_⟩
  let A := ↥(Finset.Icc 2 n)
  let j (x : A) := OMA.weightedBlock (x : ℕ)
  have hbounds (x : A) :
      OMA.weightedBlockStart (j x) ≤ (x : ℕ) ∧ (x : ℕ) < OMA.weightedBlockStart (j x + 1) :=
    OMA.weightedBlock_bounds (Finset.mem_Icc.mp x.property).1
  have localExists (b : ℕ) := OMA.smallMonochromaticSubsets
    (Fin (OMA.weightedBlockStart (b + 1))) (2 ^ (b + 1)) (by rw [Fintype.card_fin, OMA.weightedBlockStart])
  let localColor (b : ℕ) := (localExists b).choose
  have localSmall (b : ℕ) := (localExists b).choose_spec
  let index (b : ℕ) (x : A) : Fin (OMA.weightedBlockStart (b + 1)) :=
    ⟨(x : ℕ) % _, Nat.mod_lt _ (OMA.weightedBlockStart_pos _)⟩
  have index_val (b : ℕ) (x : A) (h : j x = b) : (index b x).val = (x : ℕ) := by
    have hlt := (hbounds x).2
    rw [h] at hlt
    exact Nat.mod_eq_of_lt hlt
  let col (x y : A) : Fin 3 :=
    if j x = j y then
      if localColor (j x) {index (j x) x, index (j x) y} then 1 else 0
    else 2
  have sym (x y : A) : col x y = col y x := by
    by_cases h : j x = j y
    · unfold col
      rw [if_pos h, if_pos h.symm, h,
        Finset.pair_comm (index (j y) x) (index (j y) y)]
    · simp [col, h, Ne.symm h]
  refine ⟨Sym2.lift ⟨col, sym⟩, ?_⟩
  intro X hMono
  obtain ⟨i, hi⟩ := hMono
  have mono (x y : A) (hx : x ∈ X) (hy : y ∈ X) (hne : x ≠ y) :
      col x y = i := hi x hx y hy hne
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hc : i = 2
  · have inj : Set.InjOn j (X : Set A) := by
      intro x hx y hy hxy
      by_contra hne
      have hm := mono x y hx hy hne
      rw [hc] at hm
      by_cases hb : localColor (j x) {index (j x) x, index (j x) y} = true <;>
        simp [col, hxy, hb] at hm
    exact (OMA.weightedBlock_sum_across X (fun x => (x : ℕ)) j inj (fun x _ => (hbounds x).1)).trans_lt
      (div_lt_div_of_pos_right (by norm_num) hlog)
  · by_cases hX : X.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.mp hX, Finset.sum_empty]
      positivity
    obtain ⟨x₀, hx₀⟩ := hX
    let b := j x₀
    have same (x : A) (hx : x ∈ X) : j x = b := by
      by_cases h : x = x₀
      · simp [b, h]
      · by_contra hn
        have hne : j x ≠ j x₀ := hn
        have hcol : col x x₀ = 2 := by simp [col, hne]
        exact hc ((mono x x₀ hx hx₀ h).symm.trans hcol)
    have inj : Set.InjOn (index b) (X : Set A) := by
      intro x hx y hy h
      apply Subtype.ext
      have hv := congrArg Fin.val h
      rw [index_val b x (same x hx), index_val b y (same y hy)] at hv
      exact hv
    let Y := X.image (index b)
    have hYcard : Y.card = X.card := Finset.card_image_of_injOn inj
    have hi₀₁ : i = 0 ∨ i = 1 := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (hc rfl).elim
    have hbit (x y : A) (hx : x ∈ X) (hy : y ∈ X) (hne : x ≠ y) :
        localColor b {index b x, index b y} = decide (i = 1) := by
      have hxj := same x hx
      have hyj := same y hy
      have hxy := hxj.trans hyj.symm
      have hh : (if localColor b {index b x, index b y} then (1 : Fin 3) else 0) = i := by
        have hm := mono x y hx hy hne
        unfold col at hm
        rw [if_pos hxy, hxj] at hm
        exact hm
      rcases hi₀₁ with hi₀ | hi₁
      · cases hb : localColor b {index b x, index b y} <;> simp [hb, hi₀] at hh ⊢
      · cases hb : localColor b {index b x, index b y} <;> simp [hb, hi₁] at hh ⊢
    have hMonoY : ∃ t, ∀ e ∈ Y.powersetCard 2, localColor b e = t := by
      refine ⟨decide (i = 1), ?_⟩
      intro e he
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp he
      obtain ⟨a, a', haa, rfl⟩ := Finset.card_eq_two.mp hcard
      have ha : a ∈ X.image (index b) := hsub (by simp)
      have ha' : a' ∈ X.image (index b) := hsub (by simp)
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha'
      exact hbit x y hx hy (fun h => haa (congrArg (index b) h))
    have hSize : X.card < 2 * 2 ^ (b + 1) + 3 := by
      rw [← hYcard]
      exact localSmall b Y hMonoY
    have hlower (x : A) (hx : x ∈ X) : OMA.weightedBlockStart b ≤ (x : ℕ) := by
      simpa only [same x hx] using (hbounds x).1
    exact (OMA.weightedBlock_sum_within X (fun x => (x : ℕ)) b hlower hSize).trans_lt
      (div_lt_div_of_pos_right (by norm_num) hlog)