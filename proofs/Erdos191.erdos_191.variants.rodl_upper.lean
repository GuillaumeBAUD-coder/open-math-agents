import FormalConjectures.ErdosProblems.«191»

/-!
# Rödl's weighted Ramsey upper bound

Divide the integers into blocks between successive double powers of two.
Use a Ramsey lower - bound colouring within each block and a second such
colouring on the block indices. A monochromatic set has bounded weight in
each block. The number of blocks it meets is logarithmic in the total block count.
The within - block estimate also appears in Ian Qvist’s three - colour proof (#211).
See Vojtěch Rödl, On homogeneous sets of positive integers (2003),
https://doi.org/10.1016/S0097-3165(03)00026-8.
-/

namespace OMA.Rodl

open Finset Filter

private def Mono {V : Type*} [DecidableEq V] (c : Finset V → Bool)
    (S : Finset V) (b : Bool) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c {x, y} = b

private theorem mono_edge {V : Type*} [DecidableEq V] {c : Finset V → Bool}
    {S E : Finset V} {b : Bool} (h : Mono c S b) (he : E ∈ S.powersetCard 2) :
    c E = b := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp he
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hcard
  exact h x (hsub (by simp)) y (hsub (by simp)) hxy

private theorem ramsey_coloring (V : Type*) [Fintype V] [DecidableEq V] (L : ℕ)
    (hV : Fintype.card V ≤ 2 ^ L) :
    ∃ c : Finset V → Bool, ∀ S b, Mono c S b → S.card < 2 * L + 3 := by
  classical
  let k := 2 * L + 3
  let config := (univ : Finset V).powersetCard k
  let N := Fintype.card (Finset V)
  by_contra! h
  have hex (c : Finset V → Bool) : ∃ (Y : config) (b : Bool), Mono c Y.val b := by
    obtain ⟨X, b, hm, hX⟩ := h c
    obtain ⟨Y, hYX, hY⟩ := exists_subset_card_eq hX
    exact ⟨⟨Y, mem_powersetCard.mpr ⟨subset_univ _, hY⟩⟩, b,
      fun x hx y hy hxy => hm x (hYX hx) y (hYX hy) hxy⟩
  let selected (c : Finset V → Bool) : config := (hex c).choose
  let bit (c : Finset V → Bool) : Bool := (hex c).choose_spec.choose
  let Free (Y : config) := ↥((Y.val.powersetCard 2)ᶜ : Finset (Finset V))
  let code (c : Finset V → Bool) : (Σ Y : config, Bool × (Free Y → Bool)) :=
    ⟨selected c, bit c, fun e => c e.val⟩
  have hcode : Function.Injective code := by
    intro c d hcd
    have hY : selected c = selected d := congrArg Sigma.fst hcd
    have hb : bit c = bit d := congrArg (fun s => s.2.1) hcd
    funext e
    by_cases he : e ∈ (selected c).val.powersetCard 2
    · have hf : e ∈ (selected d).val.powersetCard 2 := by rwa [← hY]
      exact (mono_edge (hex c).choose_spec.choose_spec he).trans
        (hb.trans (mono_edge (hex d).choose_spec.choose_spec hf).symm)
    · have he' : e ∈ ((selected c).val.powersetCard 2)ᶜ := mem_compl.mpr he
      have hf' : e ∈ ((selected d).val.powersetCard 2)ᶜ := by rwa [← hY]
      have hv := congrArg (fun s : (Σ Y : config, Bool × (Free Y → Bool)) =>
        if he : e ∈ (s.1.val.powersetCard 2)ᶜ then s.2.2 ⟨e, he⟩ else false) hcd
      simpa [code, he', hf'] using hv
  have hCardFree (Y : config) : Fintype.card (Free Y) = N - k.choose 2 := by
    have hY := (mem_powersetCard.mp Y.property).2
    simp only [Free, Fintype.card_coe, card_compl, card_powersetCard, hY, N]
  have hSize := Fintype.card_le_of_injective code hcode
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_sigma, Fintype.card_prod,
    hCardFree, sum_const, card_univ, nsmul_eq_mul] at hSize
  have hConfig : Fintype.card config ≤ 2 ^ (L * k) := by
    calc
      _ = (Fintype.card V).choose k := by simp [config]
      _ ≤ (Fintype.card V) ^ k := Nat.choose_le_pow _ _
      _ ≤ (2 ^ L) ^ k := Nat.pow_le_pow_left hV _
      _ = _ := (pow_mul _ _ _).symm
  have hkN : k.choose 2 ≤ N := by
    let Y := selected (fun _ => false)
    have hY := (mem_powersetCard.mp Y.property).2
    have hc := card_le_univ (Y.val.powersetCard 2)
    simpa [card_powersetCard, hY, N] using hc
  have hPairs : k.choose 2 = k * (L + 1) := by
    rw [Nat.choose_two_right, show k - 1 = (L + 1) * 2 by dsimp [k]; omega, ← Nat.mul_assoc]
    simp
  have hExp : L * k + 1 + (N - k.choose 2) < N := by
    have hk : 1 < k := by dsimp [k]; omega
    have hlt : L * k + 1 < k.choose 2 := by
      rw [hPairs, show k * (L + 1) = L * k + k by ring]
      omega
    omega
  have hlt : Fintype.card config * (2 * 2 ^ (N - k.choose 2)) < 2 ^ N := by
    calc
      _ ≤ 2 ^ (L * k) * (2 * 2 ^ (N - k.choose 2)) :=
        Nat.mul_le_mul_right _ hConfig
      _ = 2 ^ (L * k + 1 + (N - k.choose 2)) := by
        rw [pow_add, pow_succ]
        ring
      _ < _ := Nat.pow_lt_pow_right (by norm_num) hExp
  exact hlt.not_ge hSize

private def cutoff (j : ℕ) : ℕ := 2 ^ (2 ^ j)
private def block (x : ℕ) : ℕ := Nat.log 2 (Nat.log 2 x)

private theorem cutoff_pos (j : ℕ) : 0 < cutoff j := by
  unfold cutoff
  positivity

private theorem block_bounds {x : ℕ} (hx : 2 ≤ x) :
    cutoff (block x) ≤ x ∧ x < cutoff (block x + 1) := by
  have hlog : 0 < Nat.log 2 x := Nat.log_pos (by decide) hx
  have hbase : (0 : ℕ) < 2 := by decide
  constructor
  · apply le_trans _ (Nat.pow_log_le_self 2 (by omega : x ≠ 0))
    exact Nat.pow_le_pow_right hbase (Nat.pow_log_le_self 2 hlog.ne')
  · apply lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) x)
    apply Nat.pow_le_pow_right hbase
    exact Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (Nat.log 2 x)

private theorem weight_bound {j x : ℕ} (hx : cutoff j ≤ x) :
    1 / Real.log (x : ℝ) ≤ 1 / ((2 : ℝ) ^ j * Real.log 2) := by
  have hpositive : 0 < (cutoff j : ℝ) := by exact_mod_cast cutoff_pos j
  have hle : (cutoff j : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hh := Real.log_le_log hpositive hle
  simp only [cutoff, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hh
  exact one_div_le_one_div_of_le (mul_pos (by positivity) (Real.log_pos (by norm_num))) hh

private theorem log2_bound {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hp : ((2 : ℕ) ^ Nat.log 2 n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  have h := Real.log_le_log (by positivity) hp
  simp only [Nat.cast_ofNat, Real.log_pow] at h
  have hh : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n))]

private theorem block_count_bound {n : ℕ}
    (hn : 2 ≤ n) (h₂ : 2 ≤ Real.log (Real.log (n : ℝ)))
    (h₃ : 1 ≤ Real.log (Real.log (Real.log (n : ℝ)))) :
    (2 * ((Nat.log 2 (block n + 1) : ℝ) + 1) + 3) ≤
      17 * Real.log (Real.log (Real.log (n : ℝ))) := by
  have hn0 : 0 < n := by omega
  have hnlog : 0 < Nat.log 2 n := Nat.log_pos (by decide) hn
  have hlog : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hloglog := Real.log_le_log (by exact_mod_cast hnlog) (log2_bound hn0)
  rw [Real.log_mul (by norm_num) hlogn.ne'] at hloglog
  have hblocks := log2_bound hnlog
  change (block n : ℝ) ≤ _ at hblocks
  have hnum : ((block n + 1 : ℕ) : ℝ) ≤ 4 * Real.log (Real.log (n : ℝ)) := by
    push_cast
    linarith
  have hlogBlocks := Real.log_le_log (by positivity) hnum
  rw [Real.log_mul (by norm_num) (by linarith : Real.log (Real.log (n : ℝ)) ≠ 0)] at hlogBlocks
  have hlogFour : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlast := log2_bound (by omega : 0 < block n + 1)
  linarith

private theorem mono_image {A V : Type*} [DecidableEq V] {S : Finset A}
    {c : Finset V → Bool} {f : A → V} {b : Bool}
    (h : ∀ x ∈ S, ∀ y ∈ S, f x ≠ f y → c {f x, f y} = b) :
    Mono c (S.image f) b := by
  intro p hp q hq hpq
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hq
  exact h x hx y hy hpq

private theorem fiber_weight {A : Type*} (S : Finset A) (x : A → ℕ) (j : ℕ)
    (hStart : ∀ a ∈ S, cutoff j ≤ x a)
    (hCount : S.card < 2 * 2 ^ (j + 1) + 3) :
    (∑ a ∈ S, 1 / Real.log (x a : ℝ)) ≤ 7 / Real.log 2 := by
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ] at hCount
  have hn : S.card ≤ 7 * 2 ^ j := by omega
  have hr : (S.card : ℝ) ≤ 7 * (2 : ℝ) ^ j := by exact_mod_cast hn
  calc
    _ ≤ ∑ _a ∈ S, 1 / ((2 : ℝ) ^ j * Real.log 2) :=
      sum_le_sum fun a ha => weight_bound (hStart a ha)
    _ = (S.card : ℝ) * (1 / ((2 : ℝ) ^ j * Real.log 2)) := by simp [nsmul_eq_mul]
    _ ≤ (7 * (2 : ℝ) ^ j) * (1 / ((2 : ℝ) ^ j * Real.log 2)) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := by field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0), (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

set_option maxHeartbeats 600000 in
private theorem weighted_ramsey (n : ℕ)
    (hn : 2 ≤ n) (h₂ : 2 ≤ Real.log (Real.log (n : ℝ)))
    (h₃ : 1 ≤ Real.log (Real.log (Real.log (n : ℝ)))) :
    ∃ G : SimpleGraph (↥(Finset.Icc 2 n)), ∀ X : Finset (↥(Finset.Icc 2 n)),
      G.IsClique X ∨ G.IsIndepSet X →
      (∑ x ∈ X, 1 / Real.log (x : ℕ)) ≤
        (7 / Real.log 2 * 17) * Real.log (Real.log (Real.log (n : ℝ))) := by
  classical
  let A := ↥(Finset.Icc 2 n)
  let J := Fin (block n + 1)
  let j (x : A) : J := ⟨block (x : ℕ), Nat.lt_succ_of_le
    (Nat.log_mono_right (Nat.log_mono_right (mem_Icc.mp x.property).2))⟩
  have hx (x : A) : cutoff (j x).val ≤ (x : ℕ) ∧ (x : ℕ) < cutoff ((j x).val + 1) :=
    block_bounds (mem_Icc.mp x.property).1
  let L := Nat.log 2 (block n + 1) + 1
  have hJ : Fintype.card J ≤ 2 ^ L := by
    rw [Fintype.card_fin]
    exact (Nat.lt_pow_succ_log_self (by decide) (block n + 1)).le
  obtain ⟨outer, hOuter⟩ := ramsey_coloring J L hJ
  let V (i : J) := Fin (cutoff (i.val + 1))
  have inner_exists (i : J) := ramsey_coloring (V i) (2 ^ (i.val + 1)) (by
    change Fintype.card (Fin (cutoff (i.val + 1))) ≤ _
    rw [Fintype.card_fin, cutoff])
  let inner (i : J) := (inner_exists i).choose
  have hInner (i : J) := (inner_exists i).choose_spec
  let index (i : J) (x : A) : V i :=
    ⟨(x : ℕ) % cutoff (i.val + 1), Nat.mod_lt _ (cutoff_pos _)⟩
  have hIndex (i : J) (x : A) (h : j x = i) : (index i x).val = (x : ℕ) := by
    have hlt := (hx x).2
    rw [h] at hlt
    exact Nat.mod_eq_of_lt hlt
  let color (x y : A) : Bool :=
    if j x = j y then inner (j x) {index (j x) x, index (j x) y}
    else outer {j x, j y}
  have hSym (x y : A) : color x y = color y x := by
    by_cases h : j x = j y
    · simp only [color, if_pos h, if_pos h.symm]
      rw [h, pair_comm]
    · simp [color, h, Ne.symm h, pair_comm]
  let G : SimpleGraph A := {
    Adj := fun x y => x ≠ y ∧ color x y = true
    symm := ⟨fun x y h => ⟨h.1.symm, (hSym y x).trans h.2⟩⟩
    loopless := ⟨fun x h => h.1 rfl⟩ }
  refine ⟨G, fun X hX => ?_⟩
  have hMono : ∃ b : Bool, ∀ x ∈ X, ∀ y ∈ X, x ≠ y → color x y = b := by
    rcases hX with hc | hi
    · exact ⟨true, fun x hx y hy hxy => (hc hx hy hxy).2⟩
    · refine ⟨false, fun x hx y hy hxy => ?_⟩
      have h := hi hx hy hxy
      cases hb : color x y
      · rfl
      · exact (h ⟨hxy, hb⟩).elim
  obtain ⟨b, hb⟩ := hMono
  let Y := X.image j
  have hOutMono : Mono outer Y b := by
    apply mono_image
    intro x hx y hy hxy
    have h := hb x hx y hy (fun he => hxy (congrArg j he))
    simpa [color, hxy] using h
  have hY : Y.card < 2 * L + 3 := hOuter Y b hOutMono
  let S (i : J) := X.filter (fun x => j x = i)
  let weight (x : A) := 1 / Real.log (x : ℕ)
  have hS (i : J) : (∑ x ∈ S i, weight x) ≤ 7 / Real.log 2 := by
    have hmono : Mono (inner i) ((S i).image (index i)) b := by
      apply mono_image
      intro x hx y hy hxy
      obtain ⟨hxX, hxj⟩ := mem_filter.mp hx
      obtain ⟨hyX, hyj⟩ := mem_filter.mp hy
      have h := hb x hxX y hyX (fun he => hxy (congrArg (index i) he))
      unfold color at h
      rw [if_pos (hxj.trans hyj.symm), hxj] at h
      exact h
    have hinj : Set.InjOn (index i) (S i : Set A) := by
      intro x hx y hy he
      have hv := congrArg Fin.val he
      rw [hIndex i x (mem_filter.mp hx).2, hIndex i y (mem_filter.mp hy).2] at hv
      exact Subtype.ext hv
    have hc := hInner i ((S i).image (index i)) b hmono
    rw [card_image_of_injOn hinj] at hc
    apply fiber_weight (S i) (fun x => (x : ℕ)) i.val _ hc
    intro x hxS
    have h := (hx x).1
    rw [(mem_filter.mp hxS).2] at h
    exact h
  have hYreal : (Y.card : ℝ) ≤ 17 * Real.log (Real.log (Real.log (n : ℝ))) := by
    have haux : (Y.card : ℝ) ≤ 2 * (L : ℝ) + 3 := by exact_mod_cast hY.le
    refine haux.trans ?_
    simpa [L] using block_count_bound hn h₂ h₃
  have hmaps : ∀ x ∈ X, j x ∈ Y := fun x hx => mem_image_of_mem j hx
  calc
    _ = ∑ i ∈ Y, ∑ x ∈ S i, weight x :=
      (Finset.sum_fiberwise_of_maps_to hmaps weight).symm
    _ ≤ ∑ _i ∈ Y, 7 / Real.log 2 := sum_le_sum fun i _ => hS i
    _ = (Y.card : ℝ) * (7 / Real.log 2) := by simp [nsmul_eq_mul]
    _ ≤ (17 * Real.log (Real.log (Real.log (n : ℝ)))) * (7 / Real.log 2) :=
      mul_le_mul_of_nonneg_right hYreal (by positivity)
    _ = _ := by ring

theorem solution : type_of% @Erdos191.erdos_191.variants.rodl_upper := by
  refine ⟨7 / Real.log 2 * 17, ?_⟩
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hNat
  have h₂ := Real.tendsto_log_atTop.comp hlog
  have h₃ := Real.tendsto_log_atTop.comp h₂
  filter_upwards [eventually_ge_atTop (2 : ℕ), h₂ (eventually_ge_atTop (2 : ℝ)),
    h₃ (eventually_ge_atTop (1 : ℝ))] with n hn h₂n h₃n
  exact weighted_ramsey n hn h₂n h₃n

end OMA.Rodl

theorem OMA.solution : type_of% @Erdos191.erdos_191.variants.rodl_upper :=
  OMA.Rodl.solution
