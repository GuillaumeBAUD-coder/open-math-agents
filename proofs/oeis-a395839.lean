import OMAStatements.S_oeis_a395839
import Mathlib.Tactic

-- Problem: A395839: G.f. 10*C(x)^2 - C(x), where C(x) = 1 + x*C(x)^2 is the g.f. of the Catalan numbers (A000108).
-- Upstream: statements/oeis-a395839.lean (declaration OMA.S_oeis_a395839.main)
-- Credit: @Dolcruz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A395839

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

lemma zmod2_neg (x : ZMod 2) : -x = x := by
  fin_cases x <;> rfl

lemma zmod3_pow_three (x : ZMod 3) : x ^ 3 = x := by
  fin_cases x <;> rfl

lemma zmod3_three_mul (x : ZMod 3) : x + x + x = 0 := by
  fin_cases x <;> rfl

lemma antidiag_sq_zmod2 (f : ℕ → ZMod 2) (n : ℕ) :
    (∑ p ∈ Finset.antidiagonal n, f p.1 * f p.2) =
      if Even n then f (n / 2) else 0 := by
  let S := Finset.antidiagonal n
  let Slt := S.filter (fun p => p.1 < p.2)
  let Sgt := S.filter (fun p => p.2 < p.1)
  let Seq := S.filter (fun p => p.1 = p.2)
  have hpart : S = Slt ∪ (Sgt ∪ Seq) := by
    ext p
    simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr (Or.inr ⟨hp, h⟩)
      · exact Or.inr (Or.inl ⟨hp, h⟩)
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hd1 : Disjoint Slt (Sgt ∪ Seq) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter] at hp1 hp2
    omega
  have hd2 : Disjoint Sgt Seq := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Sgt, Seq, Finset.mem_filter] at hp1 hp2
    omega
  have hswap : (∑ p ∈ Slt, f p.1 * f p.2) = ∑ p ∈ Sgt, f p.1 * f p.2 := by
    refine Finset.sum_bij (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Slt, Sgt, S, Finset.mem_filter, Finset.mem_antidiagonal, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      omega
    · intro p _ q _ h
      exact Prod.swap_injective h
    · intro q hq
      refine ⟨q.swap, ?_, Prod.swap_swap q⟩
      simp only [Slt, Sgt, S, Finset.mem_filter, Finset.mem_antidiagonal, Prod.fst_swap,
        Prod.snd_swap] at hq ⊢
      omega
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap, mul_comm]
  change ∑ p ∈ S, f p.1 * f p.2 = _
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2, hswap, ← add_assoc,
    zmod2_add_self, zero_add]
  by_cases hev : Even n
  · rw [if_pos hev]
    rcases hev with ⟨m, rfl⟩
    have hSeq : Seq = {(m, m)} := by
      ext p
      simp only [Seq, S, Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton,
        Prod.ext_iff]
      omega
    have hdiv : (m + m) / 2 = m := by omega
    rw [hSeq, Finset.sum_singleton, zmod2_mul_self, hdiv]
  · rw [if_neg hev]
    have hSeq : Seq = ∅ := by
      ext p
      simp only [Seq, S, Finset.mem_filter, Finset.mem_antidiagonal, Finset.notMem_empty,
        iff_false, not_and]
      intro hsum heq
      exact hev ⟨p.1, by omega⟩
    rw [hSeq, Finset.sum_empty]

lemma catalan_mod2_iff (n : ℕ) :
    (catalan n : ZMod 2) = 1 ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp only [catalan_zero, Nat.cast_one, true_iff]
      exact ⟨0, by norm_num⟩
    | succ m =>
      have hrec : (catalan (m + 1) : ZMod 2) =
          ∑ p ∈ Finset.antidiagonal m, (catalan p.1 : ZMod 2) * (catalan p.2 : ZMod 2) := by
        rw [catalan_succ']
        push_cast
        rfl
      rw [hrec, antidiag_sq_zmod2 (fun k => (catalan k : ZMod 2)) m]
      by_cases hev : Even m
      · rw [if_pos hev]
        rcases hev with ⟨j, rfl⟩
        have hdiv : (j + j) / 2 = j := by omega
        rw [hdiv, ih j (by omega)]
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k + 1, by rw [pow_succ']; omega⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k =>
            rw [pow_succ'] at hk
            exact ⟨k, by omega⟩
      · rw [if_neg hev]
        constructor
        · intro h01
          exact False.elim ((by decide : (0 : ZMod 2) ≠ 1) h01)
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k =>
            rw [pow_succ'] at hk
            exact False.elim (hev ⟨2 ^ k - 1, by
              have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
              omega⟩)

lemma triple_sum_zmod3 (f : ℕ → ZMod 3) (m : ℕ) :
    (∑ p ∈ Finset.antidiagonal m,
      (∑ q ∈ Finset.antidiagonal p.1, f q.1 * f q.2) * f p.2) =
    if 3 ∣ m then f (m / 3) else 0 := by
  let R := Finset.range (m + 1)
  let T := (R ×ˢ (R ×ˢ R)).filter (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = m)
  have hsum_eq :
      (∑ p ∈ Finset.antidiagonal m,
        (∑ q ∈ Finset.antidiagonal p.1, f q.1 * f q.2) * f p.2) =
      ∑ t ∈ T, f t.1 * f t.2.1 * f t.2.2 := by
    have h1 :
        (∑ p ∈ Finset.antidiagonal m,
          (∑ q ∈ Finset.antidiagonal p.1, f q.1 * f q.2) * f p.2) =
        ∑ p ∈ Finset.antidiagonal m,
          ∑ q ∈ Finset.antidiagonal p.1, f q.1 * f q.2 * f p.2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_mul]
    rw [h1, Finset.sum_sigma']
    refine Finset.sum_bij (fun x _ => (x.2.1, x.2.2, x.1.2)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx
      simp only [T, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro x hx y hy hxy
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hx hy
      simp only [Prod.mk.injEq] at hxy
      cases x with | mk p1 q1 =>
      cases y with | mk p2 q2 =>
      cases p1 with | mk a1 c1 =>
      cases q1 with | mk x1 y1 =>
      cases p2 with | mk a2 c2 =>
      cases q2 with | mk x2 y2 =>
      simp only at hx hy hxy
      have ha : a1 = a2 := by omega
      subst ha
      have : x1 = x2 ∧ y1 = y2 ∧ c1 = c2 := ⟨hxy.1, hxy.2.1, hxy.2.2⟩
      rcases this with ⟨rfl, rfl, rfl⟩
      rfl
    · intro t ht
      simp only [T, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
      refine ⟨⟨(t.1 + t.2.1, t.2.2), (t.1, t.2.1)⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal]
      exact ⟨ht.2, trivial⟩
    · intro x _
      rfl
  rw [hsum_eq]
  let σ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun t => (t.2.1, t.2.2, t.1)
  let B := m + 1
  let key : ℕ × ℕ × ℕ → ℕ := fun t => t.1 * B ^ 2 + t.2.1 * B + t.2.2
  have hB : 0 < B := Nat.succ_pos m
  have hkey_inj : ∀ t1 ∈ T, ∀ t2 ∈ T, key t1 = key t2 → t1 = t2 := by
    intro t1 ht1 t2 ht2 hkeq
    simp only [T, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht1 ht2
    have hc1 : t1.2.2 < B := ht1.1.2.2
    have hc2 : t2.2.2 < B := ht2.1.2.2
    have hb1 : t1.2.1 < B := ht1.1.2.1
    have hb2 : t2.2.1 < B := ht2.1.2.1
    have hmod : key t1 % B = key t2 % B := congrArg (· % B) hkeq
    have hk1m : key t1 % B = t1.2.2 := by
      dsimp only [key]
      have : t1.1 * B ^ 2 + t1.2.1 * B + t1.2.2 = t1.2.2 + (t1.1 * B + t1.2.1) * B := by ring
      rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1]
    have hk2m : key t2 % B = t2.2.2 := by
      dsimp only [key]
      have : t2.1 * B ^ 2 + t2.2.1 * B + t2.2.2 = t2.2.2 + (t2.1 * B + t2.2.1) * B := by ring
      rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc2]
    have hceq : t1.2.2 = t2.2.2 := by omega
    have hdiv : key t1 / B = key t2 / B := congrArg (· / B) hkeq
    have hk1d : key t1 / B = t1.1 * B + t1.2.1 := by
      dsimp only [key]
      have : t1.1 * B ^ 2 + t1.2.1 * B + t1.2.2 = t1.2.2 + (t1.1 * B + t1.2.1) * B := by ring
      rw [this, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hc1, zero_add]
    have hk2d : key t2 / B = t2.1 * B + t2.2.1 := by
      dsimp only [key]
      have : t2.1 * B ^ 2 + t2.2.1 * B + t2.2.2 = t2.2.2 + (t2.1 * B + t2.2.1) * B := by ring
      rw [this, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hc2, zero_add]
    have hab : t1.1 * B + t1.2.1 = t2.1 * B + t2.2.1 := by omega
    have hbmod : (t1.1 * B + t1.2.1) % B = (t2.1 * B + t2.2.1) % B := congrArg (· % B) hab
    rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2] at hbmod
    have haeq : t1.1 = t2.1 := by
      have : t1.1 * B = t2.1 * B := by omega
      exact Nat.eq_of_mul_eq_mul_right hB this
    ext <;> assumption
  have hσ_mem : ∀ t ∈ T, σ t ∈ T := by
    intro t ht
    simp only [T, R, σ, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht ⊢
    omega
  have hσ_inj : Function.Injective σ := by
    intro a b h
    simp only [σ, Prod.mk.injEq] at h
    ext
    · exact h.2.2
    · exact h.1
    · exact h.2.1
  have hσ3 : ∀ t, σ (σ (σ t)) = t := fun t => by simp [σ]
  let Tfix := T.filter (fun t => t.1 = t.2.1 ∧ t.2.1 = t.2.2)
  let Tnf := T.filter (fun t => ¬ (t.1 = t.2.1 ∧ t.2.1 = t.2.2))
  have hsplit : T = Tfix ∪ Tnf := by
    ext t
    simp only [Tfix, Tnf, Finset.mem_union, Finset.mem_filter]
    tauto
  have hdisj_fix : Disjoint Tfix Tnf := by
    rw [Finset.disjoint_left]
    intro t h1 h2
    simp only [Tfix, Tnf, Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  rw [hsplit, Finset.sum_union hdisj_fix]
  have hnf_zero : ∑ t ∈ Tnf, f t.1 * f t.2.1 * f t.2.2 = 0 := by
    let A := Tnf.filter (fun t => key t < key (σ t) ∧ key t < key (σ (σ t)))
    have hA_sub : A ⊆ Tnf := Finset.filter_subset _ _
    have hnf_part : Tnf = A ∪ (A.image σ ∪ A.image (σ ∘ σ)) := by
      ext t
      constructor
      · intro ht
        have htT : t ∈ T := (Finset.mem_filter.mp ht).1
        have hnotfix : ¬ (t.1 = t.2.1 ∧ t.2.1 = t.2.2) := (Finset.mem_filter.mp ht).2
        have hne1 : t ≠ σ t := by
          intro heq
          simp only [σ, Prod.ext_iff] at heq
          exact hnotfix ⟨heq.1, heq.2.1⟩
        have hne2 : t ≠ σ (σ t) := by
          intro heq
          simp only [σ, Prod.ext_iff] at heq
          exact hnotfix ⟨heq.2.1.symm, heq.2.2.symm⟩
        have hne12 : σ t ≠ σ (σ t) := fun h => hne1 (hσ_inj h)
        have hk01 : key t ≠ key (σ t) := fun h => hne1 (hkey_inj t htT (σ t) (hσ_mem t htT) h)
        have hk02 : key t ≠ key (σ (σ t)) := fun h =>
          hne2 (hkey_inj t htT (σ (σ t)) (hσ_mem _ (hσ_mem t htT)) h)
        have hk12 : key (σ t) ≠ key (σ (σ t)) := fun h =>
          hne12 (hkey_inj (σ t) (hσ_mem t htT) (σ (σ t)) (hσ_mem _ (hσ_mem t htT)) h)
        have hσnf : ∀ u ∈ Tnf, σ u ∈ Tnf := by
          intro u hu
          simp only [Tnf, Finset.mem_filter] at hu ⊢
          refine ⟨hσ_mem u hu.1, ?_⟩
          intro hfix
          simp only [σ] at hfix
          exact hu.2 ⟨hfix.2.symm.trans hfix.1.symm, hfix.1⟩
        simp only [Finset.mem_union, Finset.mem_image, Function.comp_apply]
        by_cases c1 : key t < key (σ t) ∧ key t < key (σ (σ t))
        · exact Or.inl (Finset.mem_filter.mpr ⟨ht, c1⟩)
        · by_cases c2 : key (σ (σ t)) < key t ∧ key (σ (σ t)) < key (σ t)
          · refine Or.inr (Or.inl ⟨σ (σ t), ?_, hσ3 t⟩)
            refine Finset.mem_filter.mpr ⟨hσnf _ (hσnf t ht), ?_⟩
            rw [hσ3 t]
            exact ⟨c2.1, c2.2⟩
          · refine Or.inr (Or.inr ⟨σ t, ?_, hσ3 t⟩)
            refine Finset.mem_filter.mpr ⟨hσnf t ht, ?_⟩
            rw [hσ3 t]
            omega
      · intro hu
        have hσnf : ∀ u ∈ Tnf, σ u ∈ Tnf := by
          intro u hu
          simp only [Tnf, Finset.mem_filter] at hu ⊢
          refine ⟨hσ_mem u hu.1, ?_⟩
          intro hfix
          simp only [σ] at hfix
          exact hu.2 ⟨hfix.2.symm.trans hfix.1.symm, hfix.1⟩
        simp only [Finset.mem_union, Finset.mem_image, Function.comp_apply] at hu
        rcases hu with hA | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
        · exact hA_sub hA
        · exact hσnf u (hA_sub hu)
        · exact hσnf _ (hσnf u (hA_sub hu))
    have hdA1 : Disjoint A (A.image σ ∪ A.image (σ ∘ σ)) := by
      rw [Finset.disjoint_left]
      intro t ht hu
      have htA := (Finset.mem_filter.mp ht).2
      simp only [Finset.mem_union, Finset.mem_image, Function.comp_apply] at hu
      rcases hu with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · have huA := (Finset.mem_filter.mp hu).2
        rw [hσ3 u] at htA
        omega
      · have huA := (Finset.mem_filter.mp hu).2
        rw [hσ3 u] at htA
        omega
    have hdA2 : Disjoint (A.image σ) (A.image (σ ∘ σ)) := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      rcases Finset.mem_image.mp h1 with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨v, hv, hvu⟩
      have huA := (Finset.mem_filter.mp hu).2
      have hvA := (Finset.mem_filter.mp hv).2
      have heq : u = σ v := (hσ_inj hvu).symm
      rw [heq] at huA
      rw [hσ3 v] at huA
      omega
    have hval1 : ∑ t ∈ A.image σ, f t.1 * f t.2.1 * f t.2.2 =
        ∑ t ∈ A, f t.1 * f t.2.1 * f t.2.2 := by
      rw [Finset.sum_image (fun _ _ _ _ h => hσ_inj h)]
      apply Finset.sum_congr rfl
      intro t _
      simp only [σ]
      ring
    have hval2 : ∑ t ∈ A.image (σ ∘ σ), f t.1 * f t.2.1 * f t.2.2 =
        ∑ t ∈ A, f t.1 * f t.2.1 * f t.2.2 := by
      rw [Finset.sum_image (fun a _ b _ h => by
        simp only [Function.comp_apply] at h
        exact hσ_inj (hσ_inj h))]
      apply Finset.sum_congr rfl
      intro t _
      simp only [Function.comp_apply, σ]
      ring
    rw [hnf_part, Finset.sum_union hdA1, Finset.sum_union hdA2, hval1, hval2, ← add_assoc]
    exact zmod3_three_mul _
  rw [hnf_zero, add_zero]
  by_cases h3 : 3 ∣ m
  · rw [if_pos h3]
    rcases h3 with ⟨k, rfl⟩
    have hTfix : Tfix = {(k, k, k)} := by
      ext t
      simp only [Tfix, T, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_singleton, Prod.ext_iff]
      omega
    have hdiv : 3 * k / 3 = k := by omega
    rw [hTfix, Finset.sum_singleton, hdiv]
    calc f k * f k * f k = f k ^ 3 := by ring
      _ = f k := zmod3_pow_three (f k)
  · rw [if_neg h3]
    have hTfix : Tfix = ∅ := by
      ext t
      simp only [Tfix, T, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.notMem_empty, iff_false, not_and]
      rintro ⟨_, hsum⟩ heq1 heq2
      exact h3 ⟨t.1, by omega⟩
    rw [hTfix, Finset.sum_empty]

lemma catalanZ_eq :
    OMA.S_oeis_a395839.catalanZ ^ 2 * PowerSeries.X + 1 = OMA.S_oeis_a395839.catalanZ := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) PowerSeries.catalanSeries_sq_mul_X_add_one
  simpa [OMA.S_oeis_a395839.catalanZ] using h

lemma catalanZ_coeff (n : ℕ) : OMA.S_oeis_a395839.catalanZ.coeff n = (catalan n : ℤ) := by
  simp [OMA.S_oeis_a395839.catalanZ]

end OMA.A395839

theorem OMA.solution : type_of% @OMA.S_oeis_a395839.main := by
  constructor
  · intro n
    have hS2 : PowerSeries.map (Int.castRingHom (ZMod 2)) OMA.S_oeis_a395839.series =
        PowerSeries.map (Int.castRingHom (ZMod 2)) OMA.S_oeis_a395839.catalanZ := by
      dsimp only [OMA.S_oeis_a395839.series]
      rw [map_sub, map_mul, map_ofNat]
      have h10 : (10 : PowerSeries (ZMod 2)) = 0 := by
        rw [← map_ofNat PowerSeries.C, show (10 : ZMod 2) = 0 from rfl, map_zero]
      rw [h10, zero_mul, zero_sub]
      ext k
      simp only [map_neg]
      exact OMA.A395839.zmod2_neg _
    have hs : ((OMA.S_oeis_a395839.series.coeff n : ℤ) : ZMod 2) = (catalan n : ZMod 2) := by
      have h := congrArg (PowerSeries.coeff n) hS2
      simpa [OMA.A395839.catalanZ_coeff] using h
    rw [hs]
    exact OMA.A395839.catalan_mod2_iff n
  · let C3 : PowerSeries (ZMod 3) :=
      PowerSeries.map (Int.castRingHom (ZMod 3)) OMA.S_oeis_a395839.catalanZ
    have hC3_coeff : ∀ k, C3.coeff k = (catalan k : ZMod 3) := by
      intro k
      simp [C3, OMA.A395839.catalanZ_coeff]
    have hC3_eq : C3 ^ 2 * PowerSeries.X + 1 = C3 := by
      have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 3))) OMA.A395839.catalanZ_eq
      simpa [C3] using h
    have hS3 : PowerSeries.map (Int.castRingHom (ZMod 3)) OMA.S_oeis_a395839.series =
        C3 ^ 3 * PowerSeries.X := by
      have h1 : PowerSeries.map (Int.castRingHom (ZMod 3)) OMA.S_oeis_a395839.series =
          C3 ^ 2 - C3 := by
        dsimp only [OMA.S_oeis_a395839.series]
        rw [map_sub, map_mul, map_pow, map_ofNat]
        have h10 : (10 : PowerSeries (ZMod 3)) = 1 := by
          rw [← map_ofNat PowerSeries.C, show (10 : ZMod 3) = 1 from rfl, map_one]
        rw [h10, one_mul]
      rw [h1]
      have hsub : C3 - 1 = C3 ^ 2 * PowerSeries.X := by
        linear_combination -hC3_eq
      calc C3 ^ 2 - C3 = C3 * (C3 - 1) := by ring
        _ = C3 * (C3 ^ 2 * PowerSeries.X) := by rw [hsub]
        _ = C3 ^ 3 * PowerSeries.X := by ring
    have hcoeff_mod3 : ∀ m : ℕ, ((OMA.S_oeis_a395839.series.coeff m : ℤ) : ZMod 3) =
        (C3 ^ 3 * PowerSeries.X).coeff m := by
      intro m
      have h := congrArg (PowerSeries.coeff m) hS3
      simpa using h
    have hcube : ∀ m : ℕ, (C3 ^ 3).coeff m = if 3 ∣ m then (catalan (m / 3) : ZMod 3) else 0 := by
      intro m
      rw [pow_succ, sq, PowerSeries.coeff_mul]
      have h1 : (∑ p ∈ Finset.antidiagonal m, (C3 * C3).coeff p.1 * C3.coeff p.2) =
          ∑ p ∈ Finset.antidiagonal m,
            (∑ q ∈ Finset.antidiagonal p.1, (catalan q.1 : ZMod 3) * (catalan q.2 : ZMod 3)) *
              (catalan p.2 : ZMod 3) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [PowerSeries.coeff_mul, hC3_coeff]
        congr 1
        apply Finset.sum_congr rfl
        intro q _
        rw [hC3_coeff, hC3_coeff]
      rw [h1]
      exact OMA.A395839.triple_sum_zmod3 (fun k => (catalan k : ZMod 3)) m
    intro n
    refine ⟨?_, ?_, ?_⟩
    · rw [hcoeff_mod3 (3 * n + 1), PowerSeries.coeff_succ_mul_X, hcube (3 * n)]
      have h3 : 3 ∣ 3 * n := ⟨n, rfl⟩
      rw [if_pos h3, show 3 * n / 3 = n by omega]
    · cases n with
      | zero =>
        rw [mul_zero, hcoeff_mod3 0, PowerSeries.coeff_zero_mul_X]
      | succ k =>
        have heq : 3 * (k + 1) = (3 * k + 2) + 1 := by omega
        rw [heq, hcoeff_mod3, PowerSeries.coeff_succ_mul_X, hcube (3 * k + 2)]
        have hnd : ¬ 3 ∣ 3 * k + 2 := by omega
        rw [if_neg hnd]
    · rw [show 3 * n + 2 = (3 * n + 1) + 1 by omega, hcoeff_mod3, PowerSeries.coeff_succ_mul_X,
        hcube (3 * n + 1)]
      have hnd : ¬ 3 ∣ 3 * n + 1 := by omega
      rw [if_neg hnd]
