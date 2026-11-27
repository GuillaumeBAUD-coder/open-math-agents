import OMAReductions.R_Erdos20_erdos_20_R1
import Mathlib.Data.Fintype.BigOperators

/-!
# Color-coding lemma for Erdős Problem 20 (step R1.H1)

Averaging over all `n`-colorings of the finite union of the family `F` shows that some
coloring makes at least a `n! / n^n` fraction of the `n`-element sets rainbow.
-/

-- Problem: Erdős Problem 20 — reduction step R1.H1
-- Credit: @Ronandt (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped BigOperators Classical

namespace OMA.Erdos20H1

noncomputable def swap0 {k : ℕ} (j x : Fin (k + 1)) : Fin (k + 1) :=
  if x = 0 then j else if x = j then 0 else x

lemma swap0_zero {k : ℕ} (j : Fin (k + 1)) : swap0 j 0 = j := by
  simp [swap0]

lemma swap0_self {k : ℕ} (j : Fin (k + 1)) : swap0 j j = 0 := by
  by_cases hj : j = 0
  · subst hj; simp [swap0]
  · simp [swap0, hj]

lemma swap0_invol {k : ℕ} (j x : Fin (k + 1)) : swap0 j (swap0 j x) = x := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [swap0_zero, swap0_self]
  · by_cases hxj : x = j
    · subst hxj
      rw [swap0_self, swap0_zero]
    · simp [swap0, hx0, hxj]

lemma swap0_bijective {k : ℕ} (j : Fin (k + 1)) : Function.Bijective (swap0 j) :=
  ⟨fun x y h => by simpa [swap0_invol] using congrArg (swap0 j) h,
   fun y => ⟨swap0 j y, swap0_invol j y⟩⟩

noncomputable def lift0 {k : ℕ} (g : Fin k → Fin k) (x : Fin (k + 1)) : Fin (k + 1) :=
  if hx : x.val = 0 then 0 else (g ⟨x.val - 1, by omega⟩).succ

lemma lift0_zero {k : ℕ} (g : Fin k → Fin k) : lift0 g 0 = 0 := by
  simp [lift0]

lemma lift0_succ {k : ℕ} (g : Fin k → Fin k) (i : Fin k) :
    lift0 g i.succ = (g i).succ := by
  unfold lift0
  rw [dif_neg (by simp : i.succ.val ≠ 0)]
  congr 1
  apply Fin.ext
  simp

lemma lift0_bijective {k : ℕ} {g : Fin k → Fin k} (hg : Function.Bijective g) :
    Function.Bijective (lift0 g) := by
  constructor
  · intro x y hxy
    by_cases hx : x.val = 0 <;> by_cases hy : y.val = 0
    · exact Fin.ext (by omega)
    · unfold lift0 at hxy
      rw [dif_pos hx, dif_neg hy] at hxy
      exact absurd (congrArg Fin.val hxy) (by simp)
    · unfold lift0 at hxy
      rw [dif_neg hx, dif_pos hy] at hxy
      exact absurd (congrArg Fin.val hxy) (by simp)
    · unfold lift0 at hxy
      rw [dif_neg hx, dif_neg hy] at hxy
      have hval : (g ⟨x.val - 1, by omega⟩).val = (g ⟨y.val - 1, by omega⟩).val := by
        have h := congrArg Fin.val hxy
        simp only [Fin.val_succ] at h
        omega
      have hg' : g ⟨x.val - 1, by omega⟩ = g ⟨y.val - 1, by omega⟩ := Fin.ext hval
      have heq := hg.1 hg'
      have heqval : x.val - 1 = y.val - 1 := congrArg Fin.val heq
      exact Fin.ext (by omega)
  · intro y
    by_cases hy : y.val = 0
    · refine ⟨0, ?_⟩
      rw [lift0_zero]
      exact Fin.ext (by simp; omega)
    · obtain ⟨i, hi⟩ := hg.2 ⟨y.val - 1, by omega⟩
      refine ⟨i.succ, ?_⟩
      rw [lift0_succ, hi]
      exact Fin.ext (by simp; omega)

noncomputable def drop0 {k : ℕ} (f : Fin (k + 1) → Fin (k + 1)) (i : Fin k) : Fin k :=
  ⟨(swap0 (f 0) (f i.succ)).val - 1, by
    have hi := i.isLt
    have hlt := (swap0 (f 0) (f i.succ)).isLt
    omega⟩

lemma swap0_f_succ_ne_zero {k : ℕ} {f : Fin (k + 1) → Fin (k + 1)}
    (hf : Function.Bijective f) (i : Fin k) :
    swap0 (f 0) (f i.succ) ≠ 0 := by
  intro h
  have h1 := congrArg (swap0 (f 0)) h
  rw [swap0_invol, swap0_zero] at h1
  have h2 := hf.1 h1
  exact absurd (congrArg Fin.val h2) (by simp)

lemma drop0_succ {k : ℕ} {f : Fin (k + 1) → Fin (k + 1)}
    (hf : Function.Bijective f) (i : Fin k) :
    (drop0 f i).succ = swap0 (f 0) (f i.succ) := by
  have hne : (swap0 (f 0) (f i.succ)).val ≠ 0 := by
    intro hv
    exact swap0_f_succ_ne_zero hf i (Fin.ext (by simpa using hv))
  apply Fin.ext
  change ((swap0 (f 0) (f i.succ)).val - 1) + 1 = (swap0 (f 0) (f i.succ)).val
  omega

lemma drop0_bijective {k : ℕ} {f : Fin (k + 1) → Fin (k + 1)}
    (hf : Function.Bijective f) : Function.Bijective (drop0 f) := by
  constructor
  · intro i₁ i₂ h
    have hsucc : (drop0 f i₁).succ = (drop0 f i₂).succ := congrArg Fin.succ h
    rw [drop0_succ hf, drop0_succ hf] at hsucc
    have hfsucc : f i₁.succ = f i₂.succ := (swap0_bijective (f 0)).1 hsucc
    have hisucc : i₁.succ = i₂.succ := hf.1 hfsucc
    have hval := congrArg Fin.val hisucc
    simp only [Fin.val_succ] at hval
    exact Fin.ext (by omega)
  · intro y
    have hcomp : Function.Bijective (fun x => swap0 (f 0) (f x)) :=
      (swap0_bijective (f 0)).comp hf
    obtain ⟨x, hx⟩ := hcomp.2 y.succ
    dsimp only at hx
    have hx0 : x.val ≠ 0 := by
      intro hv
      have hxzero : x = 0 := Fin.ext (by simpa using hv)
      rw [hxzero, swap0_self] at hx
      exact absurd (congrArg Fin.val hx) (by simp)
    let i : Fin k := ⟨x.val - 1, by have := x.isLt; omega⟩
    have hisucc : i.succ = x := Fin.ext (by simp [i]; omega)
    refine ⟨i, ?_⟩
    have hs : (drop0 f i).succ = y.succ := by
      rw [drop0_succ hf, hisucc, hx]
    have hval := congrArg Fin.val hs
    simp only [Fin.val_succ] at hval
    exact Fin.ext (by omega)

noncomputable def bijectiveFinSuccEquiv (k : ℕ) :
    {f : Fin (k + 1) → Fin (k + 1) // Function.Bijective f} ≃
      Fin (k + 1) × {g : Fin k → Fin k // Function.Bijective g} where
  toFun p := (p.1 0, ⟨drop0 p.1, drop0_bijective p.2⟩)
  invFun q :=
    ⟨fun x => swap0 q.1 (lift0 q.2.1 x),
      (swap0_bijective q.1).comp (lift0_bijective q.2.2)⟩
  left_inv p := by
    apply Subtype.ext
    funext x
    dsimp only
    by_cases hx : x.val = 0
    · have hx0 : x = 0 := Fin.ext (by simpa using hx)
      rw [hx0, lift0_zero, swap0_zero]
    · let i : Fin k := ⟨x.val - 1, by have := x.isLt; omega⟩
      have hisucc : i.succ = x := Fin.ext (by simp [i]; omega)
      rw [← hisucc, lift0_succ, drop0_succ p.2, swap0_invol]
  right_inv q := by
    apply Prod.ext
    · dsimp
      rw [lift0_zero, swap0_zero]
    · apply Subtype.ext
      funext i
      apply Fin.ext
      change (swap0 (swap0 q.1 (lift0 q.2.1 0)) (swap0 q.1 (lift0 q.2.1 i.succ))).val - 1 =
        (q.2.1 i).val
      rw [lift0_zero, swap0_zero, swap0_invol, lift0_succ]
      simp

lemma card_bijective_fin : ∀ k : ℕ,
    Fintype.card {f : Fin k → Fin k // Function.Bijective f} = k.factorial
  | 0 => by
      let e : {f : Fin 0 → Fin 0 // Function.Bijective f} ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => ⟨Fin.elim0, ⟨fun x => Fin.elim0 x, fun y => Fin.elim0 y⟩⟩
          left_inv := fun ⟨f, _⟩ => by
            apply Subtype.ext
            funext x
            exact Fin.elim0 x
          right_inv := fun u => by cases u; rfl }
      rw [Fintype.card_congr e]
      simp
  | k + 1 => by
      rw [Fintype.card_congr (bijectiveFinSuccEquiv k), Fintype.card_prod,
        Fintype.card_fin, card_bijective_fin k, Nat.factorial_succ]

noncomputable def extC {α : Type} {n : ℕ} (hn : 0 < n) (U : Finset α)
    (f : U → Fin n) (x : α) : Fin n :=
  if hx : x ∈ U then f ⟨x, hx⟩ else ⟨0, hn⟩

noncomputable def coloringSplitEquiv {α : Type} {n : ℕ} (hn : 0 < n)
    (U A : Finset α) (hAU : A ⊆ U) (hAcard : A.card = n) :
    {f : U → Fin n // Function.Bijective (fun x : A => extC hn U f x)} ≃
      {g : Fin n → Fin n // Function.Bijective g} × ((U \ A : Finset α) → Fin n) :=
  let eA : A ≃ Fin n := A.equivFin.trans (finCongr hAcard)
  { toFun := fun ⟨f, hf⟩ =>
      (⟨fun i => extC hn U f (eA.symm i), hf.comp eA.symm.bijective⟩,
       fun x => f ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩)
    invFun := fun ⟨⟨g, hg⟩, h⟩ =>
      ⟨fun u => if hu : u.1 ∈ A then g (eA ⟨u.1, hu⟩) else h ⟨u.1, Finset.mem_sdiff.mpr ⟨u.2, hu⟩⟩,
       by
         have heq : (fun x : A =>
             extC hn U
               (fun u => if hu : u.1 ∈ A then g (eA ⟨u.1, hu⟩)
                 else h ⟨u.1, Finset.mem_sdiff.mpr ⟨u.2, hu⟩⟩)
               x) = fun x : A => g (eA x) := by
           funext x
           unfold extC
           rw [dif_pos (hAU x.2)]
           dsimp only
           rw [dif_pos x.2]
         rw [heq]
         exact hg.comp eA.bijective⟩
    left_inv := fun ⟨f, _⟩ => by
      apply Subtype.ext
      funext u
      dsimp
      by_cases hu : u.1 ∈ A
      · rw [dif_pos hu]
        unfold extC
        rw [dif_pos (hAU (eA.symm (eA ⟨u.1, hu⟩)).2)]
        congr 1
        apply Subtype.ext
        simp only [Equiv.symm_apply_apply]
      · rw [dif_neg hu]
    right_inv := fun ⟨⟨g, _⟩, h⟩ => by
      apply Prod.ext
      · apply Subtype.ext
        funext i
        dsimp
        unfold extC
        rw [dif_pos (hAU (eA.symm i).2)]
        dsimp only
        rw [dif_pos (eA.symm i).2]
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
      · funext x
        have hxA : x.1 ∉ A := (Finset.mem_sdiff.mp x.2).2
        dsimp
        rw [dif_neg hxA] }

end OMA.Erdos20H1

open OMA.Erdos20H1

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 := by
  intro α n hn F hF
  by_cases hFempty : F = ∅
  · refine ⟨fun _ => ⟨0, hn⟩, ∅, Finset.empty_subset F, by simp, by simp [hFempty]⟩
  have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
  let U : Finset α := F.biUnion id
  have hAU : ∀ A ∈ F, A ⊆ U := fun A hA => Finset.subset_biUnion_of_mem id hA
  have hnU : n ≤ U.card := by
    obtain ⟨A₀, hA₀⟩ := hFne
    rw [← hF A₀ hA₀]
    exact Finset.card_le_card (hAU A₀ hA₀)
  let good (f : U → Fin n) : Finset (Finset α) :=
    F.filter (fun A => Function.Bijective (fun x : A => extC hn U f x))
  have hcount (A : Finset α) (hA : A ∈ F) :
      (Finset.univ.filter (fun f : U → Fin n =>
        Function.Bijective (fun x : A => extC hn U f x))).card =
      n.factorial * n ^ (U.card - n) := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr (coloringSplitEquiv hn U A (hAU A hA) (hF A hA))]
    rw [Fintype.card_prod, card_bijective_fin n, Fintype.card_fun,
      Fintype.card_coe, Fintype.card_fin, Finset.card_sdiff_of_subset (hAU A hA), hF A hA]
  have hsum :
      ∑ f : U → Fin n, (good f).card = F.card * (n.factorial * n ^ (U.card - n)) := by
    calc
      ∑ f : U → Fin n, (good f).card
        = ∑ f : U → Fin n, ∑ A ∈ F,
            if Function.Bijective (fun x : A => extC hn U f x) then 1 else 0 := by
            refine Finset.sum_congr rfl fun f _ => ?_
            exact Finset.card_filter _ _
      _ = ∑ A ∈ F, ∑ f : U → Fin n,
            if Function.Bijective (fun x : A => extC hn U f x) then 1 else 0 :=
            Finset.sum_comm
      _ = ∑ A ∈ F, (Finset.univ.filter (fun f : U → Fin n =>
            Function.Bijective (fun x : A => extC hn U f x))).card := by
            refine Finset.sum_congr rfl fun A _ => ?_
            exact (Finset.card_filter _ _).symm
      _ = ∑ _A ∈ F, (n.factorial * n ^ (U.card - n)) :=
            Finset.sum_congr rfl fun A hA => hcount A hA
      _ = F.card * (n.factorial * n ^ (U.card - n)) := by
            rw [Finset.sum_const, smul_eq_mul]
  by_contra hnone
  have hlt : ∀ f : U → Fin n, (good f).card * n ^ n < F.card * n.factorial := by
    intro f
    by_contra hle
    exact hnone ⟨extC hn U f, good f, Finset.filter_subset _ F,
      fun A hA => (Finset.mem_filter.mp hA).2, Nat.le_of_not_lt hle⟩
  have hne_univ : (Finset.univ : Finset (U → Fin n)).Nonempty :=
    ⟨fun _ => ⟨0, hn⟩, Finset.mem_univ _⟩
  have hsum_lt :
      ∑ f : U → Fin n, (good f).card * n ^ n <
        ∑ _f : U → Fin n, F.card * n.factorial :=
    Finset.sum_lt_sum_of_nonempty hne_univ (fun f _ => hlt f)
  have hLHS :
      ∑ f : U → Fin n, (good f).card * n ^ n = F.card * n.factorial * n ^ U.card := by
    rw [← Finset.sum_mul, hsum]
    have hpow : n ^ (U.card - n) * n ^ n = n ^ U.card := by
      rw [← pow_add, Nat.sub_add_cancel hnU]
    calc
      F.card * (n.factorial * n ^ (U.card - n)) * n ^ n
        = F.card * n.factorial * (n ^ (U.card - n) * n ^ n) := by ring
      _ = F.card * n.factorial * n ^ U.card := by rw [hpow]
  have hRHS :
      ∑ _f : U → Fin n, F.card * n.factorial = F.card * n.factorial * n ^ U.card := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe,
      Fintype.card_fin, smul_eq_mul, mul_comm]
  rw [hLHS, hRHS] at hsum_lt
  exact lt_irrefl _ hsum_lt
