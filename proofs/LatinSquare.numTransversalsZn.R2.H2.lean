import OMAReductions.R_LatinSquare_numTransversalsZn_R2
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Factorial.BigOperators

-- The finite entropy estimate is taken from @amp2600's accepted proof of
-- LatinSquare.maxTransversalsBound, lefttosolve2/open-math-agents PR 7985.
-- The product comparison for odd cyclic orders follows below that estimate.
namespace CyclicTransversalBound
open Finset Real

noncomputable def availableMean (n j : ℕ) : ℝ := 1 + (↑(j * (j - 1)) : ℝ) / ((n : ℝ) - 2)

noncomputable def ratio (n : ℕ) : ℝ :=
  ∏ j ∈ range n, availableMean n j / (j + 1 : ℝ)

lemma mean_pos (n j : ℕ) (hn : 3 ≤ n) : 0 < availableMean n j := by
  unfold availableMean
  have hlt : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have h : (0 : ℝ) < (n : ℝ) - 2 := sub_pos.mpr hlt
  positivity

lemma ratio_mul_factorial (n : ℕ) :
    ratio n * n.factorial = ∏ j ∈ range n, availableMean n j := by
  unfold ratio
  have h : ∏ j ∈ range n, (j + 1 : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  rw [Finset.prod_div_distrib, h, div_mul_cancel₀ _ (by positivity)]

open Finset

abbrev Transversal {n : ℕ} (L : LatinSquare n) :=
  {σ : Fin n → Fin n // IsTransversal L σ}

def choices {n : ℕ} (L : LatinSquare n) (σ : Fin n → Fin n)
    (S : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  univ.filter fun c => ∀ j ∈ S, c ≠ σ j ∧ L.mat i c ≠ L.mat j (σ j)

lemma choices_congr {n : ℕ} (L : LatinSquare n) {σ τ : Fin n → Fin n}
    {S : Finset (Fin n)} (h : ∀ j ∈ S, σ j = τ j) (i : Fin n) :
    choices L σ S i = choices L τ S i := by
  ext c
  simp only [choices, mem_filter, mem_univ, true_and]
  constructor <;> intro hc j hj
  · rw [← h j hj]
    exact hc j hj
  · rw [h j hj]
    exact hc j hj

lemma transversal_choice {n : ℕ} {L : LatinSquare n}
    (σ : Transversal L) {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    σ.val i ∈ choices L σ.val S i := by
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  intro j hj
  have hji : i ≠ j := fun e => hi (e ▸ hj)
  exact ⟨σ.property.1.ne hji, σ.property.2.ne hji⟩

noncomputable def prefixWeight {n : ℕ} (L : LatinSquare n)
    (σ : Fin n → Fin n) (S : Finset (Fin n)) : List (Fin n) → ℝ
  | [] => 1
  | i :: rest => ((choices L σ S i).card : ℝ)⁻¹ * prefixWeight L σ (insert i S) rest

def completions {n : ℕ} (L : LatinSquare n) (σ : Fin n → Fin n)
    (S : Finset (Fin n)) : Finset (Transversal L) :=
  univ.filter fun τ => ∀ j ∈ S, τ.val j = σ j

lemma mem_completions {n : ℕ} {L : LatinSquare n} {σ : Fin n → Fin n}
    {S : Finset (Fin n)} {τ : Transversal L} :
    τ ∈ completions L σ S ↔ ∀ j ∈ S, τ.val j = σ j := by
  simp [completions]

lemma mass_le_one {n : ℕ} (L : LatinSquare n) (rows : List (Fin n))
    (S : Finset (Fin n)) (σ : Fin n → Fin n) (hrows : rows.Nodup)
    (hdisj : ∀ j ∈ rows, j ∉ S) (hcover : ∀ j, j ∈ S ∨ j ∈ rows) :
    ∑ τ ∈ completions L σ S, prefixWeight L τ.val S rows ≤ 1 := by
  induction rows generalizing S σ with
  | nil =>
    simp only [prefixWeight, sum_const, nsmul_eq_mul, mul_one, Nat.cast_le_one]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply Subtype.ext
    funext j
    have hj : j ∈ S := (hcover j).resolve_right (by simp)
    exact (mem_completions.mp ha j hj).trans (mem_completions.mp hb j hj).symm
  | cons i rows ih =>
    have hi : i ∉ S := hdisj _ (by simp)
    let C := choices L σ S i
    let G := completions L σ S
    have hmap : ∀ τ ∈ G, τ.val i ∈ C := by
      intro τ hτ
      dsimp [C]
      rw [← choices_congr L (mem_completions.mp hτ)]
      exact transversal_choice τ hi
    calc
      _ = ∑ c ∈ C, ∑ τ ∈ G.filter (fun τ => τ.val i = c), prefixWeight L τ.val S (i :: rows) :=
        (Finset.sum_fiberwise_of_maps_to hmap (fun τ => prefixWeight L τ.val S (i :: rows))).symm
      _ ≤ ∑ c ∈ C, ((C.card : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro c hc
        let σ' : Fin n → Fin n := Function.update σ i c
        have hf : G.filter (fun τ => τ.val i = c) = completions L σ' (insert i S) := by
          ext τ
          simp only [G, mem_filter, mem_completions, mem_insert]
          constructor
          · rintro ⟨hτ, hiτ⟩ j (rfl | hj)
            · simpa [σ'] using hiτ
            · have hji : j ≠ i := fun e => hi (e ▸ hj)
              simpa [σ', Function.update_of_ne hji] using hτ j hj
          · intro hτ
            refine ⟨fun j hj => ?_, ?_⟩
            · have hji : j ≠ i := fun e => hi (e ▸ hj)
              simpa [σ', Function.update_of_ne hji] using hτ j (Or.inr hj)
            · simpa [σ'] using hτ i (Or.inl rfl)
        have hw : ∀ τ ∈ G.filter (fun τ => τ.val i = c),
            prefixWeight L τ.val S (i :: rows) =
              (C.card : ℝ)⁻¹ * prefixWeight L τ.val (insert i S) rows := by
          intro τ hτ
          rw [prefixWeight, choices_congr L (mem_completions.mp (mem_filter.mp hτ).1)]
        rw [Finset.sum_congr rfl hw, ← Finset.mul_sum, hf]
        refine mul_le_of_le_one_right (by positivity) (ih _ _ (List.nodup_cons.mp hrows).2 ?_ ?_)
        · intro j hj
          simp only [mem_insert, not_or]
          exact ⟨fun e => (List.nodup_cons.mp hrows).1 (e ▸ hj), hdisj _ (by simp [hj])⟩
        · intro j
          rcases hcover j with hj | hj
          · exact Or.inl (mem_insert_of_mem hj)
          · rcases List.mem_cons.mp hj with rfl | hh
            · exact Or.inl (mem_insert_self _ _)
            · exact Or.inr hh
      _ ≤ 1 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        by_cases hc : (C.card : ℝ) = 0
        · simp [hc]
        · simp [mul_inv_cancel₀ hc]


lemma avg_log_le {A : Type} (s : Finset A) (z : A → ℝ) (y : ℝ)
    (hy : 0 < y) (hz : ∀ a ∈ s, 0 < z a)
    (h : ∑ a ∈ s, z a ≤ (s.card : ℝ) * y) :
    ∑ a ∈ s, Real.log (z a) ≤ (s.card : ℝ) * Real.log y := by
  have hone (a) (ha : a ∈ s) :
      Real.log (z a) ≤ Real.log y + z a / y - 1 := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (hz a ha) hy)
    rw [Real.log_div (hz a ha).ne' hy.ne'] at hh
    linarith
  calc
    _ ≤ ∑ a ∈ s, (Real.log y + z a / y - 1) :=
      sum_le_sum hone
    _ ≤ _ := by
      rw [sum_sub_distrib, sum_add_distrib, ← Finset.sum_div, sum_const, sum_const,
        nsmul_eq_mul, nsmul_eq_mul]
      have hY := (div_le_iff₀ hy).mpr h
      linarith

lemma prefixWeight_pos {n : ℕ} (L : LatinSquare n) (σ : Transversal L)
    (S : Finset (Fin n)) (rows : List (Fin n))
    (hrows : rows.Nodup) (hdisj : ∀ j ∈ rows, j ∉ S) :
    0 < prefixWeight L σ.val S rows := by
  induction rows generalizing S with
  | nil => simp [prefixWeight]
  | cons i rows ih =>
    have hi : i ∉ S := hdisj i (by simp)
    have hp : (0 : ℝ) < (choices L σ.val S i).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨σ.val i, transversal_choice σ hi⟩
    rw [prefixWeight]
    refine mul_pos (inv_pos.mpr hp) (ih _ (List.nodup_cons.mp hrows).2 ?_)
    intro j hj
    simp only [mem_insert, not_or]
    exact ⟨fun e => (List.nodup_cons.mp hrows).1 (e ▸ hj), hdisj _ (by simp [hj])⟩

lemma logPrefixWeight {n : ℕ} (L : LatinSquare n) (σ : Transversal L)
    (S : Finset (Fin n)) (rows : List (Fin n))
    (hrows : rows.Nodup) (hdisj : ∀ j ∈ rows, j ∉ S) :
    Real.log (prefixWeight L σ.val S rows) =
      -∑ i : Fin rows.length, Real.log
        ((choices L σ.val (S ∪ (rows.take i).toFinset) rows[i]).card : ℝ) := by
  induction rows generalizing S with
  | nil => simp [prefixWeight]
  | cons i rows ih =>
    have hi : i ∉ S := hdisj i (by simp)
    have hp : (0 : ℝ) < (choices L σ.val S i).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨σ.val i, transversal_choice σ hi⟩
    have hnew : ∀ j ∈ rows, j ∉ insert i S := by
      intro j hj
      simp only [mem_insert, not_or]
      exact ⟨fun e => (List.nodup_cons.mp hrows).1 (e ▸ hj), hdisj _ (by simp [hj])⟩
    have hrest := prefixWeight_pos L σ (insert i S) rows (List.nodup_cons.mp hrows).2 hnew
    rw [prefixWeight, Real.log_mul (inv_ne_zero hp.ne') hrest.ne', Real.log_inv,
      ih _ (List.nodup_cons.mp hrows).2 hnew]
    let f (k : Fin (rows.length+1)) : ℝ :=
      Real.log ((choices L σ.val (S ∪ ((i::rows).take k.val).toFinset) (i::rows)[k]).card : ℝ)
    change _ = -(∑ j, f j)
    rw [Fin.sum_univ_succ]
    have hs (T : Finset (Fin n)) : S ∪ insert i T = insert i S ∪ T := by
      ext j
      simp only [mem_union,mem_insert]
      tauto
    simp [f, List.take_succ_cons, hs, add_comm]

lemma completions_empty {n : ℕ} (L : LatinSquare n) (σ : Fin n → Fin n) :
    completions L σ ∅ = univ := by ext τ; simp [mem_completions]

lemma fixed_order_card {n : ℕ} (L : LatinSquare n) (rows : List (Fin n))
    (hrows : rows.Nodup) (hcover : ∀ i, i ∈ rows) :
    let N := Fintype.card (Transversal L)
    (N : ℝ) * Real.log N ≤
      ∑ σ : Transversal L, ∑ i : Fin rows.length,
        Real.log ((choices L σ.val (rows.take i).toFinset rows[i]).card : ℝ) := by
  classical
  let N := Fintype.card (Transversal L)
  change (N : ℝ) * Real.log N ≤ _
  by_cases hn : N = 0
  · have he : IsEmpty (Transversal L) := Fintype.card_eq_zero_iff.mp hn
    simp [hn]
  have hpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  let f (σ : Transversal L) : ℝ := prefixWeight L σ.val ∅ rows
  have hm : ∑ σ, f σ ≤ 1 := by
    simpa [f, completions_empty L id] using
      mass_le_one L rows ∅ id hrows (by simp) (by simpa using hcover)
  have hr := avg_log_le (univ : Finset (Transversal L)) f ((N : ℝ)⁻¹)
        (inv_pos.mpr hpos) (fun σ _ => prefixWeight_pos L σ ∅ rows hrows (by simp))
        (by simpa [N, mul_inv_cancel₀ hpos.ne'] using hm)
  simp only [card_univ, ← show N = Fintype.card (Transversal L) from rfl, Real.log_inv,
    mul_neg, f] at hr
  simp only [logPrefixWeight L _ ∅ rows hrows (by simp), empty_union, sum_neg_distrib] at hr
  linarith

section Counting

open Equiv

lemma relabel_three {A : Type} [DecidableEq A] {a b c u v w : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∃ f : Perm A, f a = u ∧ f b = v ∧ f c = w := by
  let g := swap a u
  have ha : g a = u := swap_apply_left _ _
  let h := swap (g b) v
  have hb : h (g b) = v := swap_apply_left _ _
  have hu : h u = u := swap_apply_of_ne_of_ne
    (by simpa [ha] using g.injective.ne hab) huv
  let j := swap (h (g c)) w
  have hc : j (h (g c)) = w := swap_apply_left _ _
  have hu' : j u = u := swap_apply_of_ne_of_ne
    (by simpa [ha,hu] using (g.trans h).injective.ne hac) huw
  have hv' : j v = v := swap_apply_of_ne_of_ne
    (by simpa [hb] using (g.trans h).injective.ne hbc) hvw
  refine ⟨(g.trans h).trans j, ?_, ?_, hc⟩
  · change j (h (g a)) = u
    rw [ha,hu,hu']
  · change j (h (g b)) = v
    rw [hb,hv']

def afterRows {n : ℕ} (e : Perm (Fin n)) (k : Fin n) : Finset (Fin n) :=
  (Ioi k).map e.toEmbedding

lemma mem_afterRows {n : ℕ} (e : Perm (Fin n)) (k i : Fin n) :
    i ∈ afterRows e k ↔ k < e.symm i := by
  constructor
  · intro h
    obtain ⟨x,hx,rfl⟩ := mem_map.mp h
    simpa using hx
  · intro h
    exact mem_map.mpr ⟨e.symm i, mem_Ioi.mpr h, e.apply_symm_apply _⟩

def mark {n : ℕ} (k : Fin n) (e : Perm (Fin n)) (i j l : Fin n) : ℕ :=
  if e k = i ∧ j ∈ afterRows e k ∧ l ∈ afterRows e k then 1 else 0

lemma mark_sum_eq {n : ℕ} (k : Fin n) {a b c u v w : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (∑ e : Perm (Fin n), mark k e a b c) = ∑ e : Perm (Fin n), mark k e u v w := by
  obtain ⟨f,ha,hb,hc⟩ := relabel_three hab hac hbc huv huw hvw
  let F : Perm (Fin n) ≃ Perm (Fin n) :=
    { toFun := fun e => e.trans f
      invFun := fun e => e.trans f.symm
      left_inv := fun e => by ext x; simp
      right_inv := fun e => by ext x; simp }
  rw [← F.sum_comp (fun e => mark k e u v w)]
  apply sum_congr rfl
  intro e _
  rw [← ha, ← hb, ← hc]
  simp only [mark, mem_afterRows, F, Equiv.coe_fn_mk, Equiv.trans_apply,
    Equiv.symm_trans_apply, Equiv.symm_apply_apply, f.injective.eq_iff]

lemma mark_sum_fixed {n : ℕ} (e : Perm (Fin n)) (k : Fin n) :
    (∑ i : Fin n, ∑ pair ∈ ((univ : Finset (Fin n)).erase i).offDiag,
      mark k e i pair.1 pair.2) = (n - 1 - k.val) * (n - 1 - k.val - 1) := by
  let P := afterRows e k
  have hPi : e k ∉ P := by simp [P, mem_afterRows]
  rw [Finset.sum_eq_single (e k)]
  · have hed :
        (((univ : Finset (Fin n)).erase (e k)).offDiag).filter
            (fun pair => pair.1 ∈ P ∧ pair.2 ∈ P) = P.offDiag := by
      ext pair
      simp only [mem_filter, mem_offDiag, mem_erase, mem_univ, and_true]
      constructor
      · rintro ⟨⟨_, _, hd⟩,h₁,h₂⟩
        exact ⟨h₁,h₂,hd⟩
      · rintro ⟨h₁,h₂,hd⟩
        have hn (j : Fin n) (hj : j ∈ P) : j ≠ e k := fun h => hPi (h ▸ hj)
        exact ⟨⟨hn _ h₁, hn _ h₂, hd⟩, h₁, h₂⟩
    simp only [mark, true_and, P] at *
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, hed, offDiag_card]
    rw [afterRows, card_map, Fin.card_Ioi]
    let a := n - 1 - k.val
    change a * a - a = a * (a - 1)
    rw [Nat.mul_sub_left_distrib a a 1, mul_one]
  · intro j _ hj
    simp [mark, Ne.symm hj]
  · simp

lemma sum_flip {A B : Type} [Fintype A] [Fintype B] (s : A → Finset B)
    (f : A → B → (C → ℕ)) [Fintype C] :
    (∑ c : C, ∑ a : A, ∑ b ∈ s a, f a b c) =
      ∑ a : A, ∑ b ∈ s a, ∑ c : C, f a b c := by
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  exact sum_comm

lemma mark_eq_after {n : ℕ} (e : Perm (Fin n)) (k j l : Fin n) :
    mark k e (e k) j l = if j ∈ afterRows e k ∧ l ∈ afterRows e k then 1 else 0 := by
  simp [mark]

lemma mark_sum_identity {n : ℕ} (hn : 3 ≤ n) (k : Fin n)
    (u : Fin n → Fin n → Fin n) [NeZero n]
    (f g : Fin n → Fin n → Fin n)
    (h : ∀ i c, c ≠ u i i → i ≠ f i c ∧ i ≠ g i c ∧ f i c ≠ g i c) :
    (∑ e : Perm (Fin n), ∑ c ∈ (univ : Finset (Fin n)).erase (u (e k) (e k)),
      mark k e (e k) (f (e k) c) (g (e k) c)) * (n - 2) =
      Fintype.card (Perm (Fin n)) * ((n - 1 - k.val) * (n - 1 - k.val - 1)) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  let H := ∑ e : Perm (Fin n), mark k e a b c
  have hconst {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
      (∑ e : Perm (Fin n), mark k e i j l) = H := by
    exact mark_sum_eq k hij hil hjl (by simp [a,b]) (by simp [a,c]) (by simp [b,c])
  have hn1 : 1 ≤ n := by omega
  have hcard (i : Fin n) : ((univ : Finset (Fin n)).erase i).offDiag.card =
      (n - 1) * (n - 2) := by
    rw [offDiag_card, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have he : n - 2 = n - 1 - 1 := by omega
    rw [he, Nat.mul_sub_left_distrib (n - 1) (n - 1) 1, mul_one]
  have hfull :
      (∑ e : Perm (Fin n), ∑ i : Fin n, ∑ pair ∈ ((univ : Finset (Fin n)).erase i).offDiag,
        mark k e i pair.1 pair.2) = n * ((n-1) * (n-2) * H) := by
    rw [sum_flip]
    calc
      _ = ∑ i : Fin n, ∑ pair ∈ ((univ : Finset (Fin n)).erase i).offDiag, H := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro pair hp
        have ⟨ha, hb, hh⟩ := mem_offDiag.mp hp
        exact hconst (mem_erase.mp ha).1.symm (mem_erase.mp hb).1.symm hh
      _ = _ := by simp [hcard, nsmul_eq_mul]
  have hmain := hfull
  simp only [mark_sum_fixed, sum_const, card_univ, nsmul_eq_mul] at hmain
  have hsub :
      (∑ e : Perm (Fin n), ∑ c ∈ (univ : Finset (Fin n)).erase (u (e k) (e k)),
        mark k e (e k) (f (e k) c) (g (e k) c)) = n * ((n - 1) * H) := by
    have he (e : Perm (Fin n)) :
        (∑ c ∈ (univ : Finset (Fin n)).erase (u (e k) (e k)),
          mark k e (e k) (f (e k) c) (g (e k) c)) =
          ∑ i : Fin n, ∑ c ∈ (univ : Finset (Fin n)).erase (u i i),
            mark k e i (f i c) (g i c) := by
      symm
      refine sum_eq_single (e k) ?_ (by simp)
      intro i _ hi
      simp [mark, ne_comm.mp hi]
    simp only [he]
    rw [sum_flip]
    calc
      _ = ∑ i : Fin n, ∑ c ∈ (univ : Finset (Fin n)).erase (u i i), H := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro c hc
        obtain ⟨h₁,h₂,h₃⟩ := h i c (mem_erase.mp hc).1
        exact hconst h₁ h₂ h₃
      _ = _ := by simp [nsmul_eq_mul, card_erase_of_mem (mem_univ _)]
  rw [hsub]
  have hm : Fintype.card (Perm (Fin n)) * ((n - 1 - k.val) * (n - 1 - k.val - 1)) =
      n * ((n-1) * (n-2) * H) := by exact_mod_cast hmain
  rw [hm]
  ring

noncomputable def colPermT {n : ℕ} (L : LatinSquare n) (t : Transversal L) : Perm (Fin n) :=
  Equiv.ofBijective t.val t.property.1.bijective_of_finite

noncomputable def symbolPermT {n : ℕ} (L : LatinSquare n) (t : Transversal L) : Perm (Fin n) :=
  Equiv.ofBijective (fun i => L.mat i (t.val i)) t.property.2.bijective_of_finite

noncomputable def colBlocker {n : ℕ} {L : LatinSquare n} (t : Transversal L) (c : Fin n) :=
  (colPermT L t).symm c

noncomputable def symbolBlocker {n : ℕ} {L : LatinSquare n} (t : Transversal L) (i c : Fin n) :=
  (symbolPermT L t).symm (L.mat i c)

lemma blocker_column {n : ℕ} {L : LatinSquare n} (t : Transversal L) (c : Fin n) :
    t.val (colBlocker t c) = c := (colPermT L t).apply_symm_apply c

lemma blocker_symbol {n : ℕ} {L : LatinSquare n} (t : Transversal L) (i c : Fin n) :
    L.mat (symbolBlocker t i c) (t.val (symbolBlocker t i c)) = L.mat i c :=
  (symbolPermT L t).apply_symm_apply _

lemma blockers_distinct {n : ℕ} {L : LatinSquare n} (t : Transversal L) (i c : Fin n)
    (hc : c ≠ t.val i) :
    i ≠ colBlocker t c ∧ i ≠ symbolBlocker t i c ∧
      colBlocker t c ≠ symbolBlocker t i c := by
  have h₁ := blocker_column t c
  have h₂ := blocker_symbol t i c
  have a : i ≠ colBlocker t c := by
    intro h
    rw [← h] at h₁
    exact hc h₁.symm
  have b : i ≠ symbolBlocker t i c := by
    intro h
    rw [← h] at h₂
    exact hc (L.row_injective i h₂).symm
  refine ⟨a,b,?_⟩
  intro h
  rw [← h,h₁] at h₂
  have he : colBlocker t c = i := L.col_injective c h₂
  exact a he.symm

def beforeRows {n : ℕ} (e : Perm (Fin n)) (k : Fin n) : Finset (Fin n) :=
  (Iio k).map e.toEmbedding

lemma mem_beforeRows {n : ℕ} (e : Perm (Fin n)) (k i : Fin n) :
    i ∈ beforeRows e k ↔ e.symm i < k := by
  constructor
  · intro h
    obtain ⟨x,hx,rfl⟩ := mem_map.mp h
    simpa using hx
  · intro h
    exact mem_map.mpr ⟨e.symm i, mem_Iio.mpr h, e.apply_symm_apply _⟩

lemma mem_choices_iff_blockers {n : ℕ} {L : LatinSquare n} (t : Transversal L)
    (e : Perm (Fin n)) (k : Fin n) (c : Fin n) (hc : c ≠ t.val (e k)) :
    c ∈ choices L t.val (beforeRows e k) (e k) ↔
      colBlocker t c ∈ afterRows e k ∧ symbolBlocker t (e k) c ∈ afterRows e k := by
  obtain ⟨h₁,h₂,_⟩ := blockers_distinct t (e k) c hc
  have h₁' : e.symm (colBlocker t c) ≠ k := by
    intro h
    have he := congrArg e h
    simp at he
    exact h₁ he.symm
  have h₂' : e.symm (symbolBlocker t (e k) c) ≠ k := by
    intro h
    have he := congrArg e h
    simp at he
    exact h₂ he.symm
  simp only [mem_afterRows]
  constructor
  · intro h
    obtain ⟨_,hh⟩ := mem_filter.mp h
    refine ⟨lt_of_le_of_ne (le_of_not_gt ?_) h₁'.symm,
      lt_of_le_of_ne (le_of_not_gt ?_) h₂'.symm⟩
    · intro hj
      exact (hh _ ((mem_beforeRows e k _).mpr hj)).1 (blocker_column t c).symm
    · intro hj
      exact (hh _ ((mem_beforeRows e k _).mpr hj)).2 (blocker_symbol t (e k) c).symm
  · rintro ⟨hcol,hsym⟩
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro j hj
    have hj' := (mem_beforeRows e k j).mp hj
    refine ⟨?_,?_⟩
    · intro h
      have h' : colBlocker t c = j := t.property.1 ((blocker_column t c).trans h)
      rw [h'] at hcol
      exact lt_asymm hcol hj'
    · intro h
      have h' : symbolBlocker t (e k) c = j :=
        t.property.2 ((blocker_symbol t (e k) c).trans h)
      rw [h'] at hsym
      exact lt_asymm hsym hj'

lemma choice_card_mark {n : ℕ} {L : LatinSquare n} (t : Transversal L)
    (e : Perm (Fin n)) (k : Fin n) :
    (choices L t.val (beforeRows e k) (e k)).card =
      1 + ∑ c ∈ (univ : Finset (Fin n)).erase (t.val (e k)),
        mark k e (e k) (colBlocker t c) (symbolBlocker t (e k) c) := by
  have hi : e k ∉ beforeRows e k := by simp [mem_beforeRows]
  have hc : t.val (e k) ∈ choices L t.val (beforeRows e k) (e k) := transversal_choice t hi
  have he :
      ((univ : Finset (Fin n)).erase (t.val (e k))).filter
        (fun c => colBlocker t c ∈ afterRows e k ∧ symbolBlocker t (e k) c ∈ afterRows e k) =
      (choices L t.val (beforeRows e k) (e k)).erase (t.val (e k)) := by
    ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true]
    exact and_congr_right (fun h => (mem_choices_iff_blockers t e k c h).symm)
  simp only [mark_eq_after]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, he, card_erase_of_mem hc]
  have hp := card_pos.mpr ⟨_,hc⟩
  change (choices L t.val (beforeRows e k) (e k)).card =
    1 + ((choices L t.val (beforeRows e k) (e k)).card - 1)
  omega

lemma mean_count {n : ℕ} {L : LatinSquare n} (t : Transversal L)
    (hn : 3 ≤ n) (k : Fin n) :
    (∑ e : Perm (Fin n), ((choices L t.val (beforeRows e k) (e k)).card : ℝ)) =
      (Fintype.card (Perm (Fin n)) : ℝ) *
        (1 + (↑((n - 1 - k.val) * (n - 1 - k.val - 1)) : ℝ) / ((n : ℝ) - 2)) := by
  letI : NeZero n := ⟨by omega⟩
  simp only [choice_card_mark t, Nat.cast_add, Nat.cast_one, sum_add_distrib,
    sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.cast_sum]
  have ident := mark_sum_identity hn k (fun i _ => t.val i)
    (fun _ c => colBlocker t c) (symbolBlocker t)
    (blockers_distinct t)
  have hp := (Nat.cast_inj (R := ℝ)).mpr ident
  push_cast [Nat.cast_sub (show 2 ≤ n by omega)] at hp
  have hpos : (0 : ℝ) < (n : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast (show 2 < n by omega))
  apply (mul_right_cancel₀ hpos.ne')
  rw [add_mul, mul_assoc, add_mul]
  rw [hp, div_mul_cancel₀ _ hpos.ne', one_mul]
  push_cast
  ring

end Counting

open Finset

lemma beforeRows_ofFn {n : ℕ} (e : Equiv.Perm (Fin n)) (k : Fin n) :
    (List.ofFn e |>.take k.val).toFinset = beforeRows e k := by
  ext i
  simp only [List.mem_toFinset, List.mem_take_iff_getElem, List.length_ofFn,
    List.getElem_ofFn, mem_beforeRows]
  constructor
  · rintro ⟨b,hb,hab⟩
    have hv := congrArg e.symm hab
    simp only [Equiv.symm_apply_apply] at hv
    have hb' := (lt_min_iff.mp hb).1
    rw [← hv]
    exact hb'
  · intro hi
    exact ⟨(e.symm i).val, lt_min_iff.mpr ⟨hi,(e.symm i).isLt⟩, e.apply_symm_apply i⟩

lemma log_weight_permutation {n : ℕ} (L : LatinSquare n) (e : Equiv.Perm (Fin n)) :
    let N := Fintype.card (Transversal L)
    (N : ℝ) * Real.log N ≤
      ∑ t : Transversal L, ∑ k : Fin n,
        Real.log ((choices L t.val (beforeRows e k) (e k)).card : ℝ) := by
  have h := fixed_order_card L (List.ofFn e) (List.nodup_ofFn.mpr e.injective)
    (fun i => List.mem_ofFn.mpr ⟨e.symm i,e.apply_symm_apply i⟩)
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro t _
  apply Fintype.sum_equiv (finCongr (List.length_ofFn (f := e)))
  intro k
  let j : Fin n := finCongr (List.length_ofFn (f := e)) k
  have hg : (List.ofFn e)[k] = e j := by
    change (List.ofFn e)[k.val]'k.isLt = e j
    simp [j]
    apply Fin.ext
    rfl
  have hb : ((List.ofFn e).take k.val).toFinset = beforeRows e j :=
    beforeRows_ofFn e j
  rw [hg, hb]

lemma average_log_choices {n : ℕ} {L : LatinSquare n}
    (hn : 3 ≤ n) (t : Transversal L) (k : Fin n) :
    (∑ e : Equiv.Perm (Fin n), Real.log ((choices L t.val (beforeRows e k) (e k)).card : ℝ)) ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
        Real.log (availableMean n (n-1-k.val)) := by
  apply avg_log_le
  · exact mean_pos _ _ hn
  · intro e _
    have hi : e k ∉ beforeRows e k := by simp [mem_beforeRows]
    exact_mod_cast Finset.card_pos.mpr ⟨t.val (e k),transversal_choice t hi⟩
  · simpa [availableMean] using (mean_count t hn k).le

lemma per_square_mean_product {n : ℕ} (hn : 3 ≤ n) (L : LatinSquare n) :
    (numTransversals L : ℝ) ≤ ∏ j ∈ range n, availableMean n j := by
  classical
  let N := Fintype.card (Transversal L)
  let P := Fintype.card (Equiv.Perm (Fin n))
  let f (t : Transversal L) (k : Fin n) (e : Equiv.Perm (Fin n)) : ℝ :=
    Real.log ((choices L t.val (beforeRows e k) (e k)).card : ℝ)
  let g (k : Fin n) : ℝ := Real.log (availableMean n (n-1-k.val))
  change (N : ℝ) ≤ _
  have hall := Finset.prod_pos (s := range n) (f := availableMean n)
    (fun j _ => mean_pos _ _ hn)
  by_cases hN : N = 0
  · simp [hN,hall.le]
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hP : (0 : ℝ) < P := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Equiv.Perm (Fin n))))
  have hu : (P : ℝ) * ((N : ℝ) * Real.log N) ≤ (P : ℝ) * ((N : ℝ) * ∑ k, g k) := by
    calc
      _ = ∑ _e : Equiv.Perm (Fin n), (N : ℝ) * Real.log N := by
        simp [P,nsmul_eq_mul]
      _ ≤ ∑ e : Equiv.Perm (Fin n), ∑ t : Transversal L, ∑ k : Fin n, f t k e :=
        sum_le_sum fun e _ => log_weight_permutation L e
      _ = ∑ t : Transversal L, ∑ k : Fin n, ∑ e : Equiv.Perm (Fin n), f t k e := by
        rw [sum_comm]
        apply sum_congr rfl
        intro t _
        exact sum_comm
      _ ≤ ∑ t : Transversal L, ∑ k : Fin n, (P : ℝ) * g k :=
        sum_le_sum fun t _ => sum_le_sum fun k _ => average_log_choices hn t k
      _ = _ := by simp [← Finset.mul_sum, nsmul_eq_mul, N, mul_assoc, mul_comm, mul_left_comm]
  have hh := (mul_le_mul_iff_right₀ hN').mp ((mul_le_mul_iff_right₀ hP).mp hu)
  apply (Real.log_le_log_iff hN' hall).mp
  rw [Real.log_prod (fun j _ => (mean_pos _ _ hn).ne')]
  refine hh.trans_eq ?_
  let g' (k : Fin n) : ℝ := Real.log (availableMean n k.val)
  calc
    _ = ∑ k : Fin n, g' (Fin.revPerm k) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp [g,g']
      congr 2
      rw [show ((Fin.revPerm k : Fin n) : ℕ) = n - (k.val + 1) from rfl]
      omega
    _ = ∑ k : Fin n, g' k := Equiv.sum_comp Fin.revPerm g'
    _ = _ := Fin.sum_univ_eq_sum_range (fun j => Real.log (availableMean n j)) n

lemma odd_ratio (k : ℕ) (hk : 1 ≤ k) :
    ratio (2*k+1) ≤ (3/4 : ℝ)^k := by
  let n := 2*k+1
  let f (j : ℕ) := availableMean n j / ((j : ℝ)+1)
  have hn : 3 ≤ n := by dsimp [n]; omega
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ)-2 := by linarith
  have nonneg (j : ℕ) : 0 ≤ f j := div_nonneg (mean_pos n j hn).le (by positivity)
  have small (j : ℕ) (hj : 1 ≤ j) (hm : 2*j ≤ n) : f j ≤ 3/4 := by
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hm' : (2 : ℝ)*j ≤ n := by exact_mod_cast hm
    have ha : (j : ℝ)*(j-1) / (n-2) ≤ j/2 := (div_le_iff₀ hd).mpr (by
      nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) by positivity) (sub_nonneg.mpr hm')])
    dsimp only [f,availableMean]
    rw [Nat.cast_mul,Nat.cast_sub hj,Nat.cast_one]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have large (j : ℕ) (hj : 1 ≤ j) (hm : j < n) : f j ≤ 1 := by
    have hm' : (j : ℝ)+1 ≤ n := by exact_mod_cast (show j+1 ≤ n by omega)
    have ha : (j : ℝ)*(j-1) / (n-2) ≤ j := (div_le_iff₀ hd).mpr (by
      nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) by positivity) (show 0 ≤ (n : ℝ)-j-1 by linarith)])
    dsimp only [f,availableMean]
    rw [Nat.cast_mul,Nat.cast_sub hj,Nat.cast_one]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have first : (∏ j ∈ range k, f (j+1)) ≤ (3/4 : ℝ)^k := by
    calc
      _ ≤ ∏ _j ∈ range k, (3/4 : ℝ) := prod_le_prod (fun j _ ↦ nonneg _) (by
        intro j hj
        have h := mem_range.mp hj
        exact small _ (by omega) (by dsimp [n]; omega))
      _ = _ := by simp only [prod_const, card_range]
  have second : (∏ j ∈ range k, f (k+j+1)) ≤ 1 := by
    calc
      _ ≤ ∏ _j ∈ range k, (1 : ℝ) := prod_le_prod (fun j _ ↦ nonneg _) (by
        intro j hj
        have h := mem_range.mp hj
        exact large _ (by omega) (by dsimp [n]; omega))
      _ = _ := by simp
  have hzero : f 0 = 1 := by simp [f,availableMean]
  change (∏ j ∈ range (2*k+1), f j) ≤ _
  rw [prod_range_succ', hzero, mul_one, two_mul, prod_range_add]
  calc
    _ ≤ (3/4 : ℝ)^k * 1 := mul_le_mul first second
      (prod_nonneg fun j _ ↦ nonneg _) (by positivity)
    _ = _ := mul_one _

lemma cyclic_upper (k : ℕ) (hk : 1 ≤ k) :
    (LatinSquare.z (2*k+1) : ℝ) ≤ (3/4 : ℝ)^k * (2*k+1).factorial := by
  have hmean : (LatinSquare.z (2*k+1) : ℝ) ≤ ∏ j ∈ range (2*k+1), availableMean (2*k+1) j := by
    unfold LatinSquare.z
    exact per_square_mean_product (by omega) _
  rw [← ratio_mul_factorial] at hmean
  exact hmean.trans (mul_le_mul_of_nonneg_right (odd_ratio k hk) (by positivity))

end CyclicTransversalBound

theorem OMA.solution : OMA.R_LatinSquare_numTransversalsZn_R2.H2 :=
  CyclicTransversalBound.cyclic_upper
