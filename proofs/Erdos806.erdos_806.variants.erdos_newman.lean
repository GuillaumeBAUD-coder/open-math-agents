import FormalConjectures.ErdosProblems.«806»

/-! Shorter proof of `Erdos806.erdos_806.variants.erdos_newman`. -/

open Finset Filter Real
open scoped Pointwise

private def rep {n : ℕ} (x : ZMod n) : ℕ := if x.val = 0 then n else x.val

private lemma rep_cast {n : ℕ} [NeZero n] (x : ZMod n) : (rep x : ZMod n) = x := by
  unfold rep; split
  · rename_i h; simpa [h] using ZMod.natCast_zmod_val x
  · exact ZMod.natCast_zmod_val x

private lemma exists_uncovered {n m l : ℕ} [NeZero n]
    (hcount : n ^ l * (l ^ 2) ^ m < (n - m) ^ m) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 n ∧ A.card = m ∧
      ∀ B : Finset ℤ, A.map Nat.castEmbedding ⊆ B + B → l < B.card := by
  classical
  let U := Fin m ↪ ZMod n; let V := Fin l → ZMod n
  let sums (b : V) : Finset (ZMod n) := univ.image fun p : Fin l × Fin l => b p.1 + b p.2
  let bad (b : V) : Finset U := univ.filter fun a => ∀ i, a i ∈ sums b
  have hb (b : V) : (bad b).card ≤ (l ^ 2) ^ m := by
    let f (a : bad b) (i : Fin m) : sums b := ⟨a.1 i, (mem_filter.mp a.2).2 i⟩
    have hf : Function.Injective f := fun _ _ h => Subtype.ext (by ext i; exact congrArg Subtype.val (congrFun h i))
    have h := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] at h
    exact h.trans (Nat.pow_le_pow_left (card_image_le.trans (by simp [pow_two])) _)
  have hcov : ((univ : Finset V).biUnion bad).card ≤ n ^ l * (l ^ 2) ^ m :=
    card_biUnion_le.trans <| (sum_le_sum fun b _ => hb b).trans_eq (by simp [V, ZMod.card])
  have hu : (n - m) ^ m ≤ (univ : Finset U).card := by
    simp only [card_univ, U, Fintype.card_embedding_eq, Fintype.card_fin, ZMod.card,
      Nat.descFactorial_eq_prod_range]
    exact (by simp : (n - m) ^ m = ∏ _ ∈ range m, (n - m)) ▸
      prod_le_prod' fun _ hi => Nat.sub_le_sub_left (mem_range.mp hi).le n
  obtain ⟨a, -, ha⟩ := exists_mem_notMem_of_card_lt_card (hcov.trans_lt (hcount.trans_le hu))
  let A := univ.image fun i : Fin m => rep (a i)
  have hrinj : Function.Injective (@rep n) := fun _ _ h => by
    simpa only [rep_cast] using congrArg (fun x : ℕ => (x : ZMod n)) h
  refine ⟨A, fun q hq => ?_, by
    change (univ.image fun i : Fin m => rep (a i)).card = m
    rw [card_image_of_injective _ (show Function.Injective (fun i => rep (a i)) from hrinj.comp a.injective)]
    simp, fun B hB => ?_⟩
  · obtain ⟨i, -, rfl⟩ := mem_image.mp hq
    refine mem_Icc.mpr ?_; unfold rep; split
    · exact ⟨Nat.one_le_iff_ne_zero.mpr (NeZero.ne _), le_rfl⟩
    · have := (a i).val_lt; omega
  · by_contra! hsm
    let W := B.image fun x : ℤ => (x : ZMod n)
    have hW : W.card ≤ l := card_image_le.trans hsm
    let b (i : Fin l) : ZMod n := if h : i.1 < W.card then (W.equivFin.symm ⟨i.1, h⟩).1 else 0
    have hb' : (↑W : Set (ZMod n)) ⊆ Set.range b := fun w hw =>
      let j := W.equivFin ⟨w, hw⟩
      ⟨⟨j.1, j.2.trans_le hW⟩, by simp [b, j.2, j]⟩
    refine ha (mem_biUnion.mpr ⟨b, mem_univ _, mem_filter.mpr ⟨mem_univ _, fun i => ?_⟩⟩)
    have hj : (rep (a i) : ℤ) ∈ B + B :=
      hB (Finset.mem_map.mpr ⟨_, mem_image.mpr ⟨i, mem_univ _, rfl⟩, rfl⟩)
    obtain ⟨u, hu, v, hv, he⟩ := mem_add.mp hj
    obtain ⟨j, hj⟩ := hb' (mem_image.mpr ⟨u, hu, rfl⟩)
    obtain ⟨k, hk⟩ := hb' (mem_image.mpr ⟨v, hv, rfl⟩)
    exact mem_image.mpr ⟨(j, k), mem_univ _, by rw [hj, hk, ← Int.cast_add, he, Int.cast_natCast, rep_cast]⟩

theorem OMA.solution : type_of% @Erdos806.erdos_806.variants.erdos_newman := by
  refine ⟨1 / 32, by norm_num, ?_⟩
  have hT : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (4 : ℕ), hT.eventually (eventually_ge_atTop (2 : ℝ))]
    with n hn ht
  let : NeZero n := ⟨by omega⟩
  let s := √(n : ℝ); let t := log (n : ℝ); let L := log t
  let x := (1 / 32 : ℝ) * L / t * s; let m := ⌊s⌋₊; let l := ⌊x⌋₊
  change 2 ≤ t at ht
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ht0 : 0 < t := by linarith
  have hL : 0 < L := log_pos (by linarith)
  have hs : 2 ≤ s := (le_sqrt (by norm_num) hn0.le).mpr (by norm_num; exact_mod_cast hn)
  have hs0 : 0 < s := by linarith
  have hm : (m : ℝ) ≤ s := Nat.floor_le hs0.le
  have hmlo : s / 2 ≤ m := by have : s < (m : ℝ) + 1 := Nat.lt_floor_add_one s; linarith
  have hm0 : 0 < m := by exact_mod_cast (by linarith : (0 : ℝ) < m)
  have hl : (l : ℝ) ≤ x := Nat.floor_le (by dsimp [x]; positivity)
  have hlt : (l : ℝ) * t ≤ L * s / 32 := by
    rw [show L * s / 32 = x * t by dsimp [x]; field_simp [ht0.ne']]
    exact mul_le_mul_of_nonneg_right hl ht0.le
  have hsq : s ^ 2 = n := sq_sqrt hn0.le
  have hhalf : s ≤ (n : ℝ) / 2 := by nlinarith only [hsq, mul_nonneg hs0.le (sub_nonneg.mpr hs)]
  have hmn : m ≤ n := by exact_mod_cast (by linarith : (m : ℝ) ≤ n)
  have hdiff : (n : ℝ) / 2 ≤ ((n - m : ℕ) : ℝ) := by rw [Nat.cast_sub hmn]; linarith
  have hcount : n ^ l * (l ^ 2) ^ m < (n - m) ^ m := by
    by_cases hl0 : l = 0
    · have hpos : 0 < n - m := by exact_mod_cast (by linarith : (0 : ℝ) < ((n - m : ℕ) : ℝ))
      simpa [hl0, zero_pow hm0.ne'] using pow_pos hpos m
    · have hlpos : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl0
      have hlog : L ≤ 2 * √t := by
        have h := log_le_sub_one_of_pos (sqrt_pos.mpr ht0); rw [log_sqrt ht0.le] at h; linarith
      have hxs : x ≤ 2 * √t * s / (32 * t) := by
        calc x = L * (s / (32 * t)) := by dsimp [x]; ring
          _ ≤ 2 * √t * (s / (32 * t)) := mul_le_mul_of_nonneg_right hlog (div_nonneg hs0.le (by positivity))
          _ = _ := by ring
      have hsqle : (l : ℝ) ^ 2 ≤ (n : ℝ) / (2 * t) := calc
        _ ≤ (2 * √t * s / (32 * t)) ^ 2 := pow_le_pow_left₀ hlpos.le (hl.trans hxs) 2
        _ = (n : ℝ) / (256 * t) := by
            rw [div_pow, mul_pow, mul_pow, sq_sqrt ht0.le, hsq]; field_simp [ht0.ne']; ring
        _ ≤ _ := div_le_div_of_nonneg_left hn0.le (by positivity) (by nlinarith)
      have hlogs : log ((l : ℝ) ^ 2) ≤ t - log 2 - L := by
        refine ((log_le_log_iff (by positivity) (by positivity)).mpr hsqle).trans_eq ?_
        rw [log_div hn0.ne' (by positivity), log_mul (by norm_num) ht0.ne']
        change log (n : ℝ) - (log 2 + log t) = log (n : ℝ) - log 2 - log t; ring
      have hsmall : (n : ℝ) ^ l * ((l : ℝ) ^ 2) ^ m < ((n : ℝ) / 2) ^ m := by
        refine (log_lt_log_iff (by positivity) (by positivity)).mp ?_
        rw [log_mul (by positivity) (by positivity), log_pow (n : ℝ) l, log_pow ((l : ℝ) ^ 2) m,
          log_pow ((n : ℝ) / 2) m, log_div hn0.ne' (by norm_num)]
        change (l : ℝ) * t + (m : ℝ) * log ((l : ℝ) ^ 2) < (m : ℝ) * (t - log 2)
        nlinarith only [hlt, mul_le_mul_of_nonneg_left hlogs (Nat.cast_nonneg m),
          mul_le_mul_of_nonneg_right hmlo hL.le, mul_pos hL hs0]
      exact_mod_cast hsmall.trans_le (pow_le_pow_left₀ (by positivity) hdiff m)
  obtain ⟨A, ha, hac, hB⟩ := exists_uncovered hcount
  exact ⟨A, ha, by rw [hac]; linarith, hac ▸ hm, fun B hc =>
    (Nat.lt_floor_add_one x).le.trans (by exact_mod_cast Nat.succ_le_of_lt (hB B hc))⟩
