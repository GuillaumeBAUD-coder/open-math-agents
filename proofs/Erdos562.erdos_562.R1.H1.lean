import OMAReductions.R_Erdos562_erdos_562_R1

/-!
# Proof of `Erdos562.erdos_562.R1.H1`

Erdős–Rado (1952) hypergraph Ramsey upper bound: for every `r ≥ 3`,
`Real.log^[r - 1] (Combinatorics.hypergraphRamsey r n : ℝ) = O(n)` as `n → ∞`.
-/

-- Step Erdos562.erdos_562.R1.H1: hypothesis H1 of reduction Erdos562.erdos_562.R1
-- Credit: @LiJiaHua1024

namespace OMA.Erdos562H1

open Finset Filter Asymptotics

/-- Asymmetric Ramsey property: every 2-coloring of `r`-subsets of any `N`-element set
contains either a `false`-monochromatic `a`-subset or a `true`-monochromatic `b`-subset. -/
private def IsRamsey (r a b N : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (U : Finset V), N ≤ U.card →
    ∀ (c : Finset V → Bool),
      (∃ S ⊆ U, S.card = a ∧ ∀ e ⊆ S, e.card = r → c e = false) ∨
      (∃ S ⊆ U, S.card = b ∧ ∀ e ⊆ S, e.card = r → c e = true)

private lemma isRamsey_mono {r a b N₁ N₂ : ℕ} (h : IsRamsey r a b N₁) (hle : N₁ ≤ N₂) :
    IsRamsey r a b N₂ :=
  fun U hU c => h U (hle.trans hU) c

/-- Base case `r = 1` (pigeonhole). -/
private lemma isRamsey_one (a b : ℕ) : IsRamsey 1 a b (a + b) := by
  intro V _ U hU c
  let U0 := U.filter fun v => c {v} = false
  let U1 := U.filter fun v => c {v} = true
  have hsum : U0.card + U1.card = U.card := by
    have hdisj : Disjoint U0 U1 := Finset.disjoint_filter.mpr fun _ _ h0 h1 => by simp_all
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1; ext v; simp only [U0, U1, mem_union, mem_filter]
    cases hc : c {v} <;> simp
  by_cases ha : a ≤ U0.card
  · obtain ⟨S, hSU0, hScard⟩ := Finset.exists_subset_card_eq ha
    left; refine ⟨S, hSU0.trans (filter_subset _ _), hScard, fun e heS hecard => ?_⟩
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hecard
    exact (mem_filter.mp (hSU0 (heS (mem_singleton_self v)))).2
  · have hb : b ≤ U1.card := by omega
    obtain ⟨S, hSU1, hScard⟩ := Finset.exists_subset_card_eq hb
    right; refine ⟨S, hSU1.trans (filter_subset _ _), hScard, fun e heS hecard => ?_⟩
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hecard
    exact (mem_filter.mp (hSU1 (heS (mem_singleton_self v)))).2

/-- Pigeonhole on fibers of a function `f : W → β` into a `Fintype β`. -/
private lemma exists_large_fiber {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [Nonempty β]
    (W : Finset V) (f : V → β) (B : ℕ) (hW : Fintype.card β * B ≤ W.card) :
    ∃ y : β, B ≤ (W.filter fun w => f w = y).card := by
  by_contra hno
  push Not at hno
  have hlt : ∀ y : β, (W.filter fun w => f w = y).card + 1 ≤ B := fun y => hno y
  have hsum : ∑ y : β, (W.filter fun w => f w = y).card = W.card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext w; simp
    · intro y₁ _ y₂ _ hne
      exact Finset.disjoint_filter.mpr fun _ _ h1 h2 => hne (h1.symm.trans h2)
  have hpos : 0 < Fintype.card β := Fintype.card_pos
  have hstrict : ∑ y : β, (W.filter fun w => f w = y).card < ∑ _y : β, B :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hpos))
      (fun y _ => hno y)
  rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hstrict
  omega

/-- Erdős–Rado stepping-up lemma: `IsRamsey r a b M` implies
`IsRamsey (r + 1) (a + 1) (b + 1) (2 ^ (M * (M ^ (r - 1) + 1)))`. -/
private lemma isRamsey_step {r a b M : ℕ} (hr : 1 ≤ r) (_hM : 1 ≤ M) (hR : IsRamsey r a b M) :
    IsRamsey (r + 1) (a + 1) (b + 1) (2 ^ (M * (M ^ (r - 1) + 1))) := by
  intro V _ U hU c
  let D : ℕ := M ^ (r - 1) + 1
  -- Build a chain of `k` distinct vertices `v_0, ..., v_{k-1}` and nested sets `W_k`
  -- such that for every `i < k` and every `(r - 1)`-subset `f` of `{v_0, ..., v_{i-1}}`,
  -- `c (insert w (insert v_i f))` is constant over all `w ∈ W_{i+1}` (hence over `{v_{i+1}, ..., v_{k-1}} ∪ W_k`).
  have hchain : ∀ k ≤ M, ∃ (vs : Fin k → V) (W : Finset V),
      Function.Injective vs ∧
      (∀ i, vs i ∈ U) ∧
      W ⊆ U ∧
      (∀ i, vs i ∉ W) ∧
      2 ^ ((M - k) * D) ≤ W.card ∧
      ∀ (i : Fin k) (e : Finset V),
        e ⊆ (Finset.univ.filter fun j : Fin k => j.val ≤ i.val).image vs →
        e.card = r → vs i ∈ e →
        ∃ col : Bool,
          (∀ j : Fin k, i.val < j.val → c (insert (vs j) e) = col) ∧
          (∀ w ∈ W, c (insert w e) = col) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Fin.elim0, U, fun i => Fin.elim0 i, fun i => Fin.elim0 i, Subset.rfl,
        fun i => Fin.elim0 i, by simpa [D] using hU, fun i => Fin.elim0 i⟩
    | succ k ih =>
      intro hkM
      obtain ⟨vs, W, hinj, hvsU, hWU, hdisj, hWcard, hconst⟩ := ih (by omega)
      have hWpos : 0 < W.card := lt_of_lt_of_le (Nat.two_pow_pos _) hWcard
      obtain ⟨vk, hvkW⟩ := Finset.card_pos.mp hWpos
      let P : Finset V := Finset.univ.image vs
      let F : Finset (Finset V) := P.powersetCard (r - 1)
      -- Signature of w ∈ W.erase vk is its colors on (insert w (insert vk f)) for f ∈ F
      let sig : V → (↥F → Bool) := fun w f => c (insert w (insert vk f.1))
      have hFcard : F.card ≤ M ^ (r - 1) := by
        have hPcard : P.card = k := by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        rw [Finset.card_powersetCard, hPcard]
        calc k.choose (r - 1)
            = k.descFactorial (r - 1) / (r - 1).factorial := Nat.choose_eq_descFactorial_div_factorial k (r - 1)
          _ ≤ k.descFactorial (r - 1) := Nat.div_le_self _ _
          _ ≤ k ^ (r - 1) := Nat.descFactorial_le_pow k (r - 1)
          _ ≤ M ^ (r - 1) := Nat.pow_le_pow_left (by omega) (r - 1)
      have hcard_sig : Fintype.card (↥F → Bool) ≤ 2 ^ (M ^ (r - 1)) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
        exact Nat.pow_le_pow_right (by norm_num) hFcard
      let B := 2 ^ ((M - (k + 1)) * D)
      have hBpos : 1 ≤ B := Nat.one_le_two_pow
      have hpow_split : 2 ^ ((M - k) * D) = 2 * (2 ^ (M ^ (r - 1)) * B) := by
        have hexp : (M - k) * D = 1 + M ^ (r - 1) + (M - (k + 1)) * D := by
          have : M - k = (M - (k + 1)) + 1 := by omega
          rw [this]; dsimp [D]; ring
        rw [hexp, pow_add, pow_add, pow_one, mul_assoc]
      have hWer : Fintype.card (↥F → Bool) * B ≤ (W.erase vk).card := by
        rw [Finset.card_erase_of_mem hvkW]
        have h1 : Fintype.card (↥F → Bool) * B ≤ 2 ^ (M ^ (r - 1)) * B :=
          Nat.mul_le_mul_right B hcard_sig
        have h2 : 1 ≤ 2 ^ (M ^ (r - 1)) * B := Nat.mul_pos (Nat.two_pow_pos _) hBpos
        omega
      obtain ⟨σ₀, hσ₀⟩ := exists_large_fiber (W.erase vk) sig B hWer
      let W' := (W.erase vk).filter fun w => sig w = σ₀
      let vs' : Fin (k + 1) → V := Fin.snoc vs vk
      have hvs'_inj : Function.Injective vs' := by
        intro i j
        refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro _; rfl
        · intro hij; simp only [vs', Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact absurd (hij ▸ hvkW) (hdisj j')
        · intro hij; simp only [vs', Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact absurd (hij.symm ▸ hvkW) (hdisj i')
        · intro hij; simp only [vs', Fin.snoc_castSucc] at hij
          exact congrArg Fin.castSucc (hinj hij)
      have hvs'_U : ∀ i : Fin (k + 1), vs' i ∈ U := by
        intro i; refine Fin.lastCases ?_ (fun i' => ?_) i
        · simpa [vs'] using hWU hvkW
        · simpa [vs'] using hvsU i'
      have hW'_sub_W : W' ⊆ W := (filter_subset _ _).trans (erase_subset _ _)
      have hW'_disj : ∀ i : Fin (k + 1), vs' i ∉ W' := by
        intro i
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · intro hmem; simp only [vs', Fin.snoc_last] at hmem
          exact (mem_erase.mp (mem_filter.mp hmem).1).1 rfl
        · intro hmem; simp only [vs', Fin.snoc_castSucc] at hmem
          exact hdisj i' (hW'_sub_W hmem)
      refine ⟨vs', W', hvs'_inj, hvs'_U, hW'_sub_W.trans hWU, hW'_disj, hσ₀, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · -- i = last k: e contains vk, so e.erase vk ∈ F
        intro e hesub hecard hvi
        simp only [vs', Fin.snoc_last] at hvi
        have hf_sub : e.erase vk ⊆ P := by
          intro x hx
          obtain ⟨hxv, hxe⟩ := mem_erase.mp hx
          obtain ⟨j, _, rfl⟩ := mem_image.mp (hesub hxe)
          revert hxv
          refine Fin.lastCases ?_ (fun j' => ?_) j
          · intro hxv; simp only [vs', Fin.snoc_last] at hxv; exact absurd rfl hxv
          · intro _; exact mem_image.mpr ⟨j', mem_univ _, by simp [vs']⟩
        have hf_card : (e.erase vk).card = r - 1 := by rw [card_erase_of_mem hvi, hecard]
        have hf_mem : e.erase vk ∈ F := mem_powersetCard.mpr ⟨hf_sub, hf_card⟩
        refine ⟨σ₀ ⟨e.erase vk, hf_mem⟩, fun j hj => ?_, fun w hw => ?_⟩
        · have := j.isLt; simp at hj; omega
        · have hsw := congrFun (mem_filter.mp hw).2 ⟨e.erase vk, hf_mem⟩
          dsimp only [sig] at hsw
          rwa [insert_erase hvi] at hsw
      · -- i = castSucc i': e ⊆ {vs 0, ..., vs i'}, reuse hconst i'
        intro e hesub hecard hvi
        simp only [vs', Fin.snoc_castSucc] at hvi
        have hesub' : e ⊆ (Finset.univ.filter fun j : Fin k => j.val ≤ i'.val).image vs := by
          intro x hx
          obtain ⟨j, hj, rfl⟩ := mem_image.mp (hesub hx)
          rw [mem_filter] at hj
          revert hj
          refine Fin.lastCases ?_ (fun j' => ?_) j
          · intro hj; exfalso; have := i'.isLt; simp at hj; omega
          · intro hj
            refine mem_image.mpr ⟨j', mem_filter.mpr ⟨mem_univ _, by simpa using hj.2⟩, by simp [vs']⟩
        obtain ⟨col, hcol_j, hcol_W⟩ := hconst i' e hesub' hecard hvi
        refine ⟨col, fun j => ?_, fun w hw => hcol_W w (hW'_sub_W hw)⟩
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro _; simp only [vs', Fin.snoc_last]; exact hcol_W vk hvkW
        · intro hj; simp only [vs', Fin.snoc_castSucc]; exact hcol_j j' (by simpa using hj)
  obtain ⟨vs, W, hinj, hvsU, hWU, hdisj, hWcard, hconst⟩ := hchain M le_rfl
  have hWpos : 0 < W.card := by
    simp only [Nat.sub_self, zero_mul, pow_zero] at hWcard; omega
  obtain ⟨wstar, hwstarW⟩ := Finset.card_pos.mp hWpos
  let P : Finset V := Finset.univ.image vs
  have hPcard : P.card = M := by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hwstar_notP : wstar ∉ P := by
    intro h; obtain ⟨i, _, hi⟩ := mem_image.mp h; exact hdisj i (hi ▸ hwstarW)
  -- Induced r-coloring on P
  let c' : Finset V → Bool := fun e => c (insert wstar e)
  -- Key property: for ANY (r + 1)-subset f ⊆ insert wstar P, there is an r-subset e ⊆ f.erase wstar (⊆ P) with c f = c' e
  have hkey : ∀ S ⊆ P, ∀ (col : Bool),
      (∀ e ⊆ S, e.card = r → c' e = col) →
      ∀ f ⊆ insert wstar S, f.card = r + 1 → c f = col := by
    intro S hSP col hScol f hfsub hfcard
    by_cases hw : wstar ∈ f
    · have hesub : f.erase wstar ⊆ S := by
        intro x hx
        have ⟨hne, hxf⟩ := mem_erase.mp hx
        exact (mem_insert.mp (hfsub hxf)).resolve_left hne
      have hecard : (f.erase wstar).card = r := by rw [card_erase_of_mem hw, hfcard]; omega
      have := hScol (f.erase wstar) hesub hecard
      dsimp only [c'] at this
      rwa [insert_erase hw] at this
    · have hfS : f ⊆ S := fun x hx => (mem_insert.mp (hfsub hx)).resolve_left (fun h => hw (h ▸ hx))
      -- Every element of f is vs j for some j : Fin M; take the maximum j!
      let J : Finset (Fin M) := Finset.univ.filter fun j => vs j ∈ f
      have hJcard : J.card = r + 1 := by
        have himg : J.image vs = f := by
          ext x; simp only [J, mem_image, mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨j, hj, rfl⟩; exact hj
          · intro hxf; obtain ⟨j, _, rfl⟩ := mem_image.mp (hSP (hfS hxf)); exact ⟨j, hxf, rfl⟩
        rw [← Finset.card_image_of_injective J hinj, himg, hfcard]
      have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
      let jmax := J.max' hJne
      have hjmax_f : vs jmax ∈ f := (mem_filter.mp (Finset.max'_mem J hJne)).2
      let e := f.erase (vs jmax)
      have hecard : e.card = r := by rw [card_erase_of_mem hjmax_f, hfcard]; omega
      have heS : e ⊆ S := (erase_subset _ _).trans hfS
      -- Let imax be the max index in e
      let Je : Finset (Fin M) := Finset.univ.filter fun j => vs j ∈ e
      have hJecard : Je.card = r := by
        have himg : Je.image vs = e := by
          ext x; simp only [Je, mem_image, mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨j, hj, rfl⟩; exact hj
          · intro hxe; obtain ⟨j, _, rfl⟩ := mem_image.mp (hSP (heS hxe)); exact ⟨j, hxe, rfl⟩
        rw [← Finset.card_image_of_injective Je hinj, himg, hecard]
      have hJene : Je.Nonempty := Finset.card_pos.mp (by omega)
      let imax := Je.max' hJene
      have himax_e : vs imax ∈ e := (mem_filter.mp (Finset.max'_mem Je hJene)).2
      have himax_lt : imax.val < jmax.val := by
        have hmemJ : imax ∈ J := mem_filter.mpr ⟨mem_univ _, (erase_subset _ _ himax_e)⟩
        have hle : imax ≤ jmax := Finset.le_max' J imax hmemJ
        have hne : imax ≠ jmax := fun h => (mem_erase.mp himax_e).1 (congrArg vs h)
        exact lt_of_le_of_ne hle (fun h => hne (Fin.ext h))
      have he_le : e ⊆ (Finset.univ.filter fun j : Fin M => j.val ≤ imax.val).image vs := by
        intro x hxe
        obtain ⟨j, _, rfl⟩ := mem_image.mp (hSP (heS hxe))
        have hjJe : j ∈ Je := mem_filter.mpr ⟨mem_univ _, hxe⟩
        exact mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, Finset.le_max' Je j hjJe⟩, rfl⟩
      obtain ⟨col₀, hcol_j, hcol_W⟩ := hconst imax e he_le hecard himax_e
      have h1 : c f = col₀ := by rw [← insert_erase hjmax_f]; exact hcol_j jmax himax_lt
      have h2 : c' e = col₀ := hcol_W wstar hwstarW
      rw [h1, ← h2]
      exact hScol e heS hecard
  -- Apply IsRamsey r a b M to (P, c')
  have hPM : M ≤ P.card := hPcard.ge
  rcases hR P hPM c' with ⟨S, hSP, hScard, hScol⟩ | ⟨S, hSP, hScard, hScol⟩
  · left
    have hw_notS : wstar ∉ S := fun h => hwstar_notP (hSP h)
    refine ⟨insert wstar S, insert_subset (hWU hwstarW) (hSP.trans (by
      intro x hx; obtain ⟨i, _, rfl⟩ := mem_image.mp hx; exact hvsU i)),
      by rw [card_insert_of_notMem hw_notS, hScard], hkey S hSP false hScol⟩
  · right
    have hw_notS : wstar ∉ S := fun h => hwstar_notP (hSP h)
    refine ⟨insert wstar S, insert_subset (hWU hwstarW) (hSP.trans (by
      intro x hx; obtain ⟨i, _, rfl⟩ := mem_image.mp hx; exact hvsU i)),
      by rw [card_insert_of_notMem hw_notS, hScard], hkey S hSP true hScol⟩

/-- Real exponential tower: `tower 0 x = x`, `tower (k + 1) x = exp (tower k x)`. -/
private noncomputable def tower : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.exp (tower k x)

private lemma tower_ge_one (k : ℕ) {x : ℝ} (hx : 1 ≤ x) : 1 ≤ tower k x := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    dsimp only [tower]
    exact Real.one_le_exp (by linarith)

private lemma tower_mono (k : ℕ) {x y : ℝ} (hxy : x ≤ y) : tower k x ≤ tower k y := by
  induction k with
  | zero => exact hxy
  | succ k ih => exact Real.exp_le_exp.mpr ih

private lemma tower_mul_add_le (k : ℕ) {c x : ℝ} (hc : 1 ≤ c) (hx : 1 ≤ x) :
    c * tower k x + 1 ≤ tower k (2 * c * x) := by
  induction k with
  | zero =>
    dsimp only [tower]
    nlinarith
  | succ k ih =>
    dsimp only [tower]
    have h1 : 1 ≤ tower k x := tower_ge_one k hx
    have h2 : 1 ≤ Real.exp (tower k x) := Real.one_le_exp (by linarith)
    have h3 : c * Real.exp (tower k x) + 1 ≤ (c + 1) * Real.exp (tower k x) := by nlinarith
    have h4 : c + 1 ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
    have h5 : (c + 1) * Real.exp (tower k x) ≤ Real.exp (c + tower k x) := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
    have h6 : c + tower k x ≤ c * tower k x + 1 := by nlinarith
    exact h3.trans (h5.trans (Real.exp_le_exp.mpr (h6.trans ih)))

private lemma log_iter_tower (k : ℕ) (x : ℝ) : Real.log^[k] (tower k x) = x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, tower, Real.log_exp]
    exact ih x

private lemma log_iter_mono (k : ℕ) {x y : ℝ} (hx : tower k 1 ≤ x) (hxy : x ≤ y) :
    1 ≤ Real.log^[k] x ∧ Real.log^[k] x ≤ Real.log^[k] y := by
  induction k generalizing x y with
  | zero =>
    simpa [tower] using ⟨hx, hxy⟩
  | succ k ih =>
    have hx_pos : 0 < x := lt_of_lt_of_le (by have := tower_ge_one (k + 1) le_rfl; linarith) hx
    have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
    have hlog_ge : tower k 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx_pos]; exact hx
    have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log hx_pos hxy
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih hlog_ge hlog_le

/-- Explicit tower upper bound on `IsRamsey r n n`: for every `r ≥ 1`, there exists `C ≥ 1`
such that for all `n ≥ 1`, there is `N` with `IsRamsey r n n N` and `(N : ℝ) ≤ tower (r - 1) (C * n)`. -/
private lemma exists_ramsey_tower :
    ∀ r : ℕ, 1 ≤ r → ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ N : ℕ, IsRamsey r n n N ∧ (N : ℝ) ≤ tower (r - 1) (C * (n : ℝ)) := by
  intro r
  induction r with
  | zero => intro h; omega
  | succ r ih =>
    intro _
    rcases eq_or_lt_of_le (Nat.zero_le r) with rfl | hrpos
    · -- r = 0, so r + 1 = 1
      refine ⟨2, by norm_num, fun n _ => ⟨n + n, isRamsey_one n n, ?_⟩⟩
      simp only [Nat.sub_self, tower]; push_cast; linarith
    · -- r ≥ 1
      obtain ⟨C, hC1, hC⟩ := ih hrpos
      -- Choose C' := 2 * (r + 1) * C (for r = 1, 2 * 2 * C = 4 * C, etc.)
      refine ⟨4 * (r : ℝ) * C, by have : (1 : ℝ) ≤ (r : ℝ) := (by exact_mod_cast (Nat.succ_le_of_lt hrpos)); nlinarith, fun n hn => ?_⟩
      rcases eq_or_lt_of_le hn with rfl | hn2
      · -- n = 1: IsRamsey (r + 1) 1 1 1 holds trivially!
        refine ⟨1, ?_, ?_⟩
        · intro V _ U hU _
          obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
          left; refine ⟨{v}, singleton_subset_iff.mpr hv, card_singleton v, fun e he hec => ?_⟩
          have := card_le_card he; rw [card_singleton, hec] at this; omega
        · have : (1 : ℝ) ≤ 4 * (r : ℝ) * C * 1 := by
            have : (1 : ℝ) ≤ (r : ℝ) := (by exact_mod_cast (Nat.succ_le_of_lt hrpos)); nlinarith
          simpa using tower_ge_one r this
      · -- n ≥ 2: apply IH to n - 1 ≥ 1
        obtain ⟨M, hMR, hMt⟩ := hC (n - 1) (by omega)
        let M' := max M 1
        have hM'R : IsRamsey r (n - 1) (n - 1) M' := isRamsey_mono hMR (le_max_left _ _)
        have hM'1 : 1 ≤ M' := le_max_right _ _
        have hstep : IsRamsey (r + 1) (n - 1 + 1) (n - 1 + 1) (2 ^ (M' * (M' ^ (r - 1) + 1))) := isRamsey_step hrpos hM'1 hM'R
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hstep
        refine ⟨2 ^ (M' * (M' ^ (r - 1) + 1)), hstep, ?_⟩
        -- Bound 2 ^ (M' * (M' ^ (r - 1) + 1)) ≤ tower r (4 * r * C * n)
        have hM'r : (M' : ℝ) ≤ tower (r - 1) (C * (n : ℝ)) := by
          have hCn : (1 : ℝ) ≤ C * (n : ℝ) := by
            have : (1 : ℝ) ≤ (n : ℝ) := (by exact_mod_cast hn); nlinarith
          have hle1 : (1 : ℝ) ≤ tower (r - 1) (C * (n : ℝ)) := tower_ge_one (r - 1) hCn
          have hleM : (M : ℝ) ≤ tower (r - 1) (C * (n : ℝ)) :=
            hMt.trans (tower_mono (r - 1) (by
              have : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
              nlinarith))
          dsimp only [M']; rw [Nat.cast_max, Nat.cast_one]; exact max_le hleM hle1
        have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have hpow_exp : ((2 ^ (M' * (M' ^ (r - 1) + 1)) : ℕ) : ℝ) ≤
            Real.exp ((M' : ℝ) * ((M' : ℝ) ^ (r - 1) + 1)) := by
          have h1 : ((2 ^ (M' * (M' ^ (r - 1) + 1)) : ℕ) : ℝ) = (2 : ℝ) ^ (M' * (M' ^ (r - 1) + 1)) := by
            push_cast; rfl
          rw [h1]
          calc (2 : ℝ) ^ (M' * (M' ^ (r - 1) + 1))
              ≤ (Real.exp 1) ^ (M' * (M' ^ (r - 1) + 1)) := pow_le_pow_left₀ (by norm_num) h2e _
            _ = Real.exp ((M' * (M' ^ (r - 1) + 1) : ℕ) * (1 : ℝ)) := by rw [← Real.exp_nat_mul]
            _ = Real.exp ((M' : ℝ) * ((M' : ℝ) ^ (r - 1) + 1)) := by push_cast; ring_nf
        have hM'ge1 : (1 : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hM'1
        have hinner : (M' : ℝ) * ((M' : ℝ) ^ (r - 1) + 1) ≤ 2 * (M' : ℝ) ^ r := by
          have h1 : (1 : ℝ) ≤ (M' : ℝ) ^ (r - 1) := one_le_pow₀ hM'ge1
          have h2 : (M' : ℝ) * (M' : ℝ) ^ (r - 1) = (M' : ℝ) ^ r := by
            rw [← pow_succ', Nat.sub_add_cancel hrpos]
          nlinarith
        have hgoal_exp : 2 * (M' : ℝ) ^ r ≤ tower (r - 1) (4 * (r : ℝ) * C * (n : ℝ)) := by
          rcases eq_or_lt_of_le (Nat.succ_le_of_lt hrpos) with rfl | hr2
          · -- r = 1: 2 * M'^1 ≤ 2 * (C * n) ≤ 4 * 1 * C * n
            simp only [Nat.sub_self, pow_one, tower, Nat.cast_one] at hM'r ⊢
            have : (0 : ℝ) ≤ C * (n : ℝ) := by positivity
            linarith
          · -- r ≥ 2: r - 1 = (r - 2) + 1, so tower (r - 1) y = exp (tower (r - 2) y)
            have hr1 : r - 1 = (r - 2) + 1 := by omega
            rw [hr1] at hM'r ⊢
            dsimp only [tower] at hM'r ⊢
            have hpow : (M' : ℝ) ^ r ≤ Real.exp ((r : ℝ) * tower (r - 2) (C * (n : ℝ))) := by
              calc (M' : ℝ) ^ r ≤ (Real.exp (tower (r - 2) (C * (n : ℝ)))) ^ r :=
                    pow_le_pow_left₀ (by linarith) hM'r r
                _ = Real.exp ((r : ℝ) * tower (r - 2) (C * (n : ℝ))) := by rw [← Real.exp_nat_mul]
            have hmul2 : 2 * (M' : ℝ) ^ r ≤ Real.exp ((r : ℝ) * tower (r - 2) (C * (n : ℝ)) + 1) := by
              rw [Real.exp_add]
              calc 2 * (M' : ℝ) ^ r ≤ Real.exp 1 * Real.exp ((r : ℝ) * tower (r - 2) (C * (n : ℝ))) :=
                    mul_le_mul h2e hpow (by positivity) (Real.exp_nonneg _)
                _ = Real.exp ((r : ℝ) * tower (r - 2) (C * (n : ℝ))) * Real.exp 1 := mul_comm _ _
            have hCn : (1 : ℝ) ≤ C * (n : ℝ) := by
              have : (1 : ℝ) ≤ (n : ℝ) := (by exact_mod_cast hn); nlinarith
            have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hrpos)
            have ht := tower_mul_add_le (r - 2) hr_ge1 hCn
            have hle_arg : 2 * (r : ℝ) * (C * (n : ℝ)) ≤ 4 * (r : ℝ) * C * (n : ℝ) := by nlinarith
            exact hmul2.trans (Real.exp_le_exp.mpr (ht.trans (tower_mono (r - 2) hle_arg)))
        have hfinal : Real.exp ((M' : ℝ) * ((M' : ℝ) ^ (r - 1) + 1)) ≤
            tower r (4 * (r : ℝ) * C * (n : ℝ)) := by
          have hr_eq : r = (r - 1) + 1 := by omega
          conv_rhs => arg 1; rw [hr_eq]
          dsimp only [tower]
          exact Real.exp_le_exp.mpr (hinner.trans hgoal_exp)
        have hsub : r + 1 - 1 = r := Nat.add_sub_cancel r 1
        rw [hsub]
        exact hpow_exp.trans hfinal

end OMA.Erdos562H1

theorem OMA.solution : OMA.R_Erdos562_erdos_562_R1.H1 := by
  open Filter Asymptotics OMA.Erdos562H1 in
  intro r hr
  obtain ⟨C, hC1, hC⟩ := exists_ramsey_tower r (by omega)
  let K : ℕ := Nat.ceil (tower (r - 1) 1)
  let B : ℝ := (Finset.range (K + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩
    (fun m => |Real.log^[r - 1] (m : ℝ)|)
  rw [Asymptotics.isBigO_iff]
  refine ⟨max C B, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨N, hNR, hNt⟩ := hC n hn
  have hram_le : Combinatorics.hypergraphRamsey r n ≤ N := by
    apply Nat.sInf_le
    intro c
    rcases hNR Finset.univ (by simp) c with ⟨S, _, hSc, hS⟩ | ⟨S, _, hSc, hS⟩
    · exact ⟨S, hSc, false, hS⟩
    · exact ⟨S, hSc, true, hS⟩
  have hram_r : (Combinatorics.hypergraphRamsey r n : ℝ) ≤ tower (r - 1) (C * (n : ℝ)) :=
    (by exact_mod_cast hram_le : (Combinatorics.hypergraphRamsey r n : ℝ) ≤ (N : ℝ)).trans hNt
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  by_cases hbig : tower (r - 1) 1 ≤ (Combinatorics.hypergraphRamsey r n : ℝ)
  · have ⟨hge1, hle⟩ := log_iter_mono (r - 1) hbig hram_r
    rw [log_iter_tower] at hle
    rw [abs_of_nonneg (by linarith)]
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_left C B) (Nat.cast_nonneg n))
  · have hltK : Combinatorics.hypergraphRamsey r n < K + 1 := by
      have h1 : (Combinatorics.hypergraphRamsey r n : ℝ) < tower (r - 1) 1 := not_le.mp hbig
      have h2 : tower (r - 1) 1 ≤ (K : ℝ) := Nat.le_ceil _
      have h3 : (Combinatorics.hypergraphRamsey r n : ℝ) < (K : ℝ) := lt_of_lt_of_le h1 h2
      have h4 : Combinatorics.hypergraphRamsey r n < K := by exact_mod_cast h3
      omega
    have hleB : |Real.log^[r - 1] (Combinatorics.hypergraphRamsey r n : ℝ)| ≤ B :=
      Finset.le_sup' (f := fun m : ℕ => |Real.log^[r - 1] (m : ℝ)|) (Finset.mem_range.mpr hltK)
    have hBnn : 0 ≤ B := (abs_nonneg _).trans hleB
    calc |Real.log^[r - 1] (Combinatorics.hypergraphRamsey r n : ℝ)|
        ≤ B := hleB
      _ ≤ B * (n : ℝ) := le_mul_of_one_le_right hBnn hn1
      _ ≤ max C B * (n : ℝ) := mul_le_mul_of_nonneg_right (le_max_right C B) (Nat.cast_nonneg n)
