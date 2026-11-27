import OMAReductions.R_Erdos535_erdos_535_R2
import Mathlib

/-! The tensor comparison and a width-preserving equality test reduce the
fixed-petal sunflower bound to two spectral statements. -/

/-
The comparison and sign test follow OpenAI's An exponential bound for sunflowers
(November 24, 2026), Sections 2 and 3, and the corresponding Lean modules
Rules, Comparison and Copy. The coefficient proofs here use finite functions over
the complex numbers and are checked with the project's pinned imports.
-/

/-
Ported from OpenAI math, commit 3344da59991ed94f9ba711217b29c1d760badfa6.
The source modules are Basic, ColorCount, Rounding and Transfer in
lean/OAI/Combinatorics/Sunflower. Changes inline the dependency modules, retain
the coloring and embedding arguments and pin the resulting statement to H2.
Licensed under the Apache License, Version 2.0, reproduced below.
-/

/- # Sunflowers in set families and in word families -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {ι I α β : Type*}

/-- Every entry of the tuple has the same value. This includes the empty tuple. -/
private def IsConstant (f : ι → β) : Prop :=
  ∀ i j, f i = f j

/-- One coordinate of a sunflower has either a common symbol or pairwise distinct symbols. -/
private def Admissible (f : ι → β) : Prop :=
  IsConstant f ∨ Function.Injective f

/-- Each coordinate of the tuple of words is admissible. -/
private def WordAdmissible (w : ι → I → β) : Prop :=
  ∀ c, Admissible (fun i => w i c)

/-- Every admissible ordered tuple of words in the family repeats one word. -/
private def WordFree (r : ℕ) (W : Finset (I → β)) : Prop :=
  ∀ w : Fin r → I → β, (∀ i, w i ∈ W) → WordAdmissible w → IsConstant w

theorem WordAdmissible.isConstant_of_repeat {w : ι → I → β} (h : WordAdmissible w)
    {i j : ι} (hne : i ≠ j) (hw : w i = w j) : IsConstant w := by
  intro a b
  funext c
  rcases h c with hc | hc
  · exact hc a b
  · exact (hne (hc (congrFun hw c))).elim

theorem WordAdmissible.injective_of_not_isConstant {w : ι → I → β}
    (h : WordAdmissible w) (hn : ¬ IsConstant w) : Function.Injective w := by
  intro i j heq
  by_contra hne
  exact hn (h.isConstant_of_repeat hne heq)

/-- A family contains a subfamily of size `r` whose distinct members intersect in one
fixed core. The core can be empty. -/
private def HasSunflower [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K

theorem hasSunflower_of_indexed [DecidableEq α] {r : ℕ} {F : Finset (Finset α)}
    {w : Fin r → Finset α} (hmem : ∀ i, w i ∈ F) (hinj : Function.Injective w)
    {K : Finset α} (hcore : ∀ i j, i ≠ j → w i ∩ w j = K) : HasSunflower r F := by
  let e : Fin r ↪ Finset α := ⟨w, hinj⟩
  refine ⟨Finset.univ.map e, ?_, by simp, K, ?_⟩
  · intro A hA
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hA
    exact hmem i
  · intro A hA B hB hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hB
    exact hcore i j (fun heq => hne (congrArg e heq))

end Sunflower
end Combinatorics
end OAI

/- # Counting rainbow members of uniform set families -/

open Finset

namespace OAI
namespace Combinatorics
namespace Sunflower

private noncomputable def extendColor {α : Type*} {k : ℕ} (hk : 0 < k)
    (U : Finset α) (f : U → Fin k) (x : α) : Fin k := by
  classical
  exact if h : x ∈ U then f ⟨x, h⟩ else ⟨0, hk⟩

/-- Fixing a bijection on a member of the family leaves all colors on its complement free. -/
private theorem card_good_colors {α : Type*} [DecidableEq α] {k : ℕ} (hk : 0 < k)
    (A U : Finset α) (hAU : A ⊆ U) (hA : A.card = k) :
    k.factorial * k ^ U.card ≤
      (univ.filter (fun f : U → Fin k =>
        Function.Bijective (fun x : A => extendColor hk U f x))).card * k ^ k := by
  classical
  let Good := fun f : U → Fin k => Function.Bijective (fun x : A => extendColor hk U f x)
  let join : (A ≃ Fin k) × ((U \ A : Finset α) → Fin k) → (U → Fin k) :=
    fun p u => if h : u.val ∈ A then p.1 ⟨u, h⟩
      else p.2 ⟨u, mem_sdiff.mpr ⟨u.property, h⟩⟩
  have hjoin (p) : Good (join p) := by
    change Function.Bijective (fun x : A => extendColor hk U (join p) x)
    convert p.1.bijective using 1
    funext x
    simp [extendColor, join, x.property, hAU x.property]
  have hinj : Function.Injective join := by
    intro p q h
    apply Prod.ext
    · apply Equiv.ext
      intro x
      have he := congrFun h (⟨x, hAU x.property⟩ : U)
      simpa [join, x.property] using he
    · funext x
      obtain ⟨hxU, hxA⟩ := mem_sdiff.mp x.property
      have he := congrFun h (⟨x, hxU⟩ : U)
      simpa [join, hxA] using he
  have hcount := Fintype.card_le_of_injective
    (fun p => (⟨join p, hjoin p⟩ : {f // Good f})) (fun _ _ h => hinj (congrArg Subtype.val h))
  have e : A ≃ Fin k := Fintype.equivFinOfCardEq (by simpa using hA)
  rw [Fintype.card_prod, Fintype.card_equiv e, Fintype.card_fun] at hcount
  simp only [Fintype.card_coe, hA, Fintype.card_fin] at hcount
  rw [Fintype.card_of_subtype (univ.filter Good) (by simp)] at hcount
  have hsum : (U \ A).card + k = U.card := hA ▸ card_sdiff_add_card_eq_card hAU
  calc
    k.factorial * k ^ U.card =
        (k.factorial * k ^ (U \ A).card) * k ^ k := by rw [← hsum, pow_add, mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ hcount

/-- Some coloring retains at least the fraction `k! / k^k` of a finite uniform family. -/
theorem exists_rainbow_subfamily {α : Type*} {k : ℕ} (hk : 0 < k)
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = k) :
    ∃ (c : α → Fin k) (G : Finset (Finset α)), G ⊆ F ∧
      (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧
      F.card * k.factorial ≤ G.card * k ^ k := by
  classical
  let U : Finset α := F.biUnion id
  let Good := fun (c : U → Fin k) (A : Finset α) =>
    Function.Bijective (fun x : A => extendColor hk U c x)
  let _ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨c, _, hc⟩ := (univ : Finset (U → Fin k)).exists_max_image
    (fun c => (F.filter (Good c)).card) univ_nonempty
  refine ⟨extendColor hk U c, F.filter (Good c), filter_subset _ _, ?_, ?_⟩
  · exact fun _ hA => (mem_filter.mp hA).2
  · have hcount (A) (hA : A ∈ F) := card_good_colors hk A U
        (subset_biUnion_of_mem id hA) (hF A hA)
    have hswap :
        ∑ A ∈ F, (univ.filter (fun c => Good c A)).card =
          ∑ f : U → Fin k, (F.filter (Good f)).card := by
      simp only [card_filter]
      rw [sum_comm]
    have allColors : Fintype.card (U → Fin k) = k ^ U.card := by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    have htotal :
        F.card * (k.factorial * k ^ U.card) ≤
          (k ^ U.card * (F.filter (Good c)).card) * k ^ k := calc
      _ = ∑ _A ∈ F, k.factorial * k ^ U.card := by simp
      _ ≤ ∑ A ∈ F, (univ.filter (fun c => Good c A)).card * k ^ k :=
        sum_le_sum hcount
      _ = (∑ f : U → Fin k, (F.filter (Good f)).card) * k ^ k := by rw [← sum_mul, hswap]
      _ ≤ (∑ _f : U → Fin k, (F.filter (Good c)).card) * k ^ k :=
        Nat.mul_le_mul_right _ (sum_le_sum hc)
      _ = _ := by simp [allColors]
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < k ^ U.card from Nat.pow_pos hk)
    · simpa only [mul_left_comm, mul_assoc, mul_comm] using htotal

end Sunflower
end Combinatorics
end OAI

/- # Exponential bounds for coloring and word comparisons -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- A uniformly random coloring with `k` colors is rainbow on a fixed `k`-set
with probability at least `3⁻ᵏ`. -/
theorem pow_self_le_three_pow_mul_factorial (k : ℕ) :
    k ^ k ≤ 3 ^ k * k.factorial := by
  have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hExp : Real.exp k ≤ (3 : ℝ) ^ k := by
    calc
      Real.exp k = (Real.exp 1) ^ k := by simp
      _ ≤ 3 ^ k := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have h := (div_le_iff₀ hk).mp ((Real.pow_div_factorial_le_exp k (Nat.cast_nonneg k) k).trans hExp)
  exact_mod_cast h

end Sunflower
end Combinatorics
end OAI

/- # Transferring word bounds to uniform set families -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- Ordering each rainbow member by color gives a word. A finite alphabet suffices
even when the ground type is infinite. -/
private theorem rainbow_encoding {α : Type*} [DecidableEq α] {k : ℕ}
    (G : Finset (Finset α)) (c : α → Fin k)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x)) :
    ∃ (n : ℕ) (encode : G → Fin k → Fin n) (decode : Fin n → α),
      Function.Injective decode ∧
      ∀ (A : G) (x : α), x ∈ (A : Finset α) ↔ decode (encode A (c x)) = x := by
  classical
  let U := G.biUnion id
  let e (A : G) : (A : Finset α) ≃ Fin k := Equiv.ofBijective _ (hc A A.property)
  let point (A : G) (j : Fin k) : U :=
    ⟨(e A).symm j, Finset.mem_biUnion.mpr ⟨A, A.property, ((e A).symm j).property⟩⟩
  let encode (A : G) (j : Fin k) := U.equivFin (point A j)
  let decode (u : Fin U.card) : α := U.equivFin.symm u
  have hdecode (A : G) (j : Fin k) :
      decode (encode A j) = ((e A).symm j).val := by
    simp [decode, encode, point]
  refine ⟨U.card, encode, decode, Subtype.val_injective.comp U.equivFin.symm.injective, ?_⟩
  intro A x
  rw [hdecode]
  constructor
  · intro hx
    have he : (e A) ⟨x, hx⟩ = c x := rfl
    rw [← he, Equiv.symm_apply_apply]
  · intro hx
    exact hx ▸ ((e A).symm (c x)).property

/-- A rainbow subfamily of a sunflower-free family embeds as an equally large
sunflower-free family of words over one finite alphabet. -/
theorem exists_word_family_of_rainbow {α : Type*} [DecidableEq α] {k r : ℕ}
    {G F : Finset (Finset α)} (hGF : G ⊆ F) (c : α → Fin k)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x))
    (hfree : ¬ HasSunflower r F) :
    ∃ (n : ℕ) (W : Finset (Fin k → Fin n)), W.card = G.card ∧ WordFree r W := by
  classical
  obtain ⟨n, encode, decode, hd, hmem⟩ := rainbow_encoding G c hc
  have hinj : Function.Injective encode := by
    intro A B hab
    apply Subtype.ext
    ext x
    rw [hmem, hmem, hab]
  let W := Finset.univ.image encode
  refine ⟨n, W, ?_, ?_⟩
  · simp [W, Finset.card_image_of_injective _ hinj]
  intro w hw hadm
  by_contra hnc
  have hwi := hadm.injective_of_not_isConstant hnc
  have hlift (i : Fin r) : ∃ A : G, encode A = w i := by
    obtain ⟨A, _, ha⟩ := Finset.mem_image.mp (hw i)
    exact ⟨A, ha⟩
  choose A hA using hlift
  have hAinj : Function.Injective (fun i => (A i : Finset α)) := by
    intro i j hij
    apply hwi
    rw [← hA i, ← hA j, Subtype.ext hij]
  have hAmem (i : Fin r) (x : α) :
      x ∈ (A i : Finset α) ↔ decode (w i (c x)) = x := by rw [← hA, hmem]
  let K := (G.biUnion id).filter fun x => ∀ i, x ∈ (A i : Finset α)
  apply hfree
  apply hasSunflower_of_indexed (K := K) (fun i => hGF (A i).property) hAinj
  intro i j hij
  ext x
  constructor
  · intro hx
    obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨A i, (A i).property, hi⟩, ?_⟩
    have heq : w i (c x) = w j (c x) :=
      hd (((hAmem i x).mp hi).trans ((hAmem j x).mp hj).symm)
    rcases hadm (c x) with hall | hdistinct
    · intro t
      exact (hAmem t x).mpr ((congrArg decode (hall t i)).trans ((hAmem i x).mp hi))
    · exact (hij (hdistinct heq)).elim
  · intro hx
    have hAll := (Finset.mem_filter.mp hx).2
    exact Finset.mem_inter.mpr ⟨hAll i, hAll j⟩

end Sunflower
end Combinatorics
end OAI

open OAI.Combinatorics.Sunflower

private theorem rainbow_transfer (r k : ℕ) (hk : 0 < k)
    (F : Finset (Finset ℕ)) (hUniform : ∀ A ∈ F, A.card = k)
    (hFree : ¬ HasSunflower r F) :
    ∃ (m : ℕ) (W : Finset (Fin k → Fin m)), F.card ≤ 3 ^ k * W.card ∧ WordFree r W := by
  obtain ⟨c, G, hGF, hc, hCount⟩ := exists_rainbow_subfamily hk F hUniform
  obtain ⟨m, W, hCard, hW⟩ := exists_word_family_of_rainbow hGF c hc
    (show ¬ HasSunflower r F from hFree)
  refine ⟨m, W, ?_, hW⟩
  apply Nat.le_of_mul_le_mul_right (c := k.factorial) _ (Nat.factorial_pos k)
  calc
    F.card * k.factorial ≤ G.card * k ^ k := hCount
    _ ≤ G.card * (3 ^ k * k.factorial) :=
      Nat.mul_le_mul_left _ (pow_self_le_three_pow_mul_factorial k)
    _ = (3 ^ k * W.card) * k.factorial := by rw [hCard]; ac_rfl


/- Coefficient identities for simultaneous controlled tensor restrictions. -/

noncomputable section
open scoped BigOperators Classical
open Finset

namespace OMA.R_Erdos535_erdos_535_R2_H1_R1

private abbrev Tensor (S A : Type) := (S → A) → ℂ

private def restrict [Fintype S] [DecidableEq S] [Fintype A] (T : Tensor S A)
    (M : ∀ _ : S, B → A → ℂ) : Tensor S B :=
  fun y => ∑ x, T x * ∏ s, M s (y s) (x s)

private def paired (T : Tensor S A) (U : Tensor S B) : Tensor S (A × B) :=
  fun x => T (fun s => (x s).1) * U (fun s => (x s).2)

private def product [Fintype J] {A : J → Type} (T : ∀ j, Tensor S (A j)) :
    Tensor S (∀ j, A j) :=
  fun x => ∏ j, T j (fun s => x s j)

private def grouped {G : Type} (g : S → G) (A : Type) : Tensor S A := by
  exact fun x => if ∀ s t, g s = g t → x s = x t then 1 else 0

private def diagonal (S A : Type) : Tensor S A :=
  grouped (fun _ : S => ()) A

private def mask [DecidableEq S] (P : Finset S) (A : Type) : Tensor S (Option A) := by
  exact fun x =>
    if ∃ a : A, ∀ s, x s = if s ∈ P then some a else none then 1 else 0

private def fiber [Fintype S] [DecidableEq G] (g : S → G) (i : G) : Finset S :=
  univ.filter (fun s => g s = i)

/-- Sum of tensors placed in their separate local blocks. -/
private def directSum [Fintype S] [DecidableEq S] [Fintype A] [Fintype B]
    (T : Tensor S A) (U : Tensor S B) : Tensor S (A ⊕ B) :=
  restrict T (fun _ y x => if Sum.inl x = y then 1 else 0) +
  restrict U (fun _ y x => if Sum.inr x = y then 1 else 0)

private structure Price (S : Type) [Fintype S] [DecidableEq S] where
  value : ∀ {A : Type} [Fintype A], Tensor S A → ℝ
  width : Finset S → ℝ
  restriction : ∀ {A B : Type} [Fintype A] [Fintype B]
    (T : Tensor S A) (M : S → B → A → ℂ),
      restrict T M ≠ 0 → value (restrict T M) ≤ value T
  pair : ∀ {A B : Type} [Fintype A] [Fintype B] (T : Tensor S A) (U : Tensor S B),
      T ≠ 0 → U ≠ 0 → value (paired T U) = value T + value U
  prod : ∀ {J : Type} [Fintype J] [DecidableEq J] {A : J → Type} [∀ j, Fintype (A j)]
    (T : ∀ j, Tensor S (A j)), (∀ j, T j ≠ 0) → value (product T) = ∑ j, value (T j)
  sum : ∀ {A B : Type} [Fintype A] [Fintype B] (T : Tensor S A) (U : Tensor S B),
    T ≠ 0 → U ≠ 0 →
      Real.exp (value (directSum T U)) = Real.exp (value T) + Real.exp (value U)
  full : ∀ {A : Type} [Fintype A] [Nonempty A],
    value (diagonal S A) = Real.log (Fintype.card A)
  groups : ∀ {A G : Type} [Fintype A] [Nonempty A] [Fintype G] [DecidableEq G]
    (g : S → G), Function.Surjective g →
      value (grouped g A) = (∑ i, width (fiber g i)) * Real.log (Fintype.card A)
  masks : ∀ {A : Type} [Fintype A] [Nonempty A] (P : Finset S), P.Nonempty →
    value (mask P A) = width P * Real.log (Fintype.card A)

private theorem grouped_const (g : S → G) (a : A) : grouped g A (fun _ => a) = 1 := by
  simp [grouped]

private theorem grouped_ne_zero (g : S → G) [Nonempty A] : grouped g A ≠ 0 := by
  intro h
  have := congrFun h (fun _ => Classical.choice (inferInstance : Nonempty A))
  simp [grouped_const] at this

private theorem product_ne_zero [Fintype J] {A : J → Type}
    (T : ∀ j, Tensor S (A j)) (h : ∀ j, T j ≠ 0) : product T ≠ 0 := by
  have hex (j) : ∃ x, T j x ≠ 0 := by
    by_contra! hn
    exact h j (funext hn)
  choose x hx using hex
  intro hn
  have hz : (∏ j, T j (x j)) = 0 := congrFun hn (fun s j => x j s)
  exact (Finset.prod_ne_zero_iff.mpr (fun j _ => hx j)) hz

private theorem paired_ne_zero (T : Tensor S A) (U : Tensor S B)
    (hT : T ≠ 0) (hU : U ≠ 0) : paired T U ≠ 0 := by
  have hexT : ∃ x, T x ≠ 0 := by
    by_contra! hn
    exact hT (funext hn)
  have hexU : ∃ x, U x ≠ 0 := by
    by_contra! hn
    exact hU (funext hn)
  obtain ⟨a, ha⟩ := hexT
  obtain ⟨b, hb⟩ := hexU
  intro hn
  exact mul_ne_zero ha hb (congrFun hn (fun s => (a s, b s)))

private def controlled [DecidableEq A] [Fintype J] {B C : J → Type}
    (M : ∀ j, S → A → C j → B j → ℂ)
    (s : S) (y : A × (∀ j, C j)) (x : A × (∀ j, B j)) : ℂ :=
  if x.1 = y.1 then ∏ j, M j s y.1 (y.2 j) (x.2 j) else 0

private theorem restrict_controlled [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    {B C : J → Type} [∀ j, Fintype (B j)]
    (T : Tensor S A) (U : ∀ j, Tensor S (B j))
    (M : ∀ j, S → A → C j → B j → ℂ) (y : S → A × (∀ j, C j)) :
    restrict (paired T (product U)) (controlled M) y =
      T (fun s => (y s).1) *
        ∏ j, restrict (U j) (fun s => M j s (y s).1) (fun s => (y s).2 j) := by
  let e : (S → A × (∀ j, B j)) ≃ (S → A) × (∀ j, S → B j) :=
    { toFun := fun x => (fun s => (x s).1, fun j s => (x s).2 j)
      invFun := fun x s => (x.1 s, fun j => x.2 j s)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold restrict paired product
  rw [← Fintype.sum_equiv e.symm _ _ (fun _ => rfl), Fintype.sum_prod_type]
  have localProd (a : S → A) (b : ∀ j, S → B j) :
      (∏ s, controlled M s (y s) (e.symm (a, b) s)) =
        if a = (fun s => (y s).1) then
          ∏ j, ∏ s, M j s (y s).1 ((y s).2 j) (b j s) else 0 := by
    split_ifs with h
    · subst a
      simpa [controlled, e] using
        (Finset.prod_comm (f := fun s j => M j s (y s).1 ((y s).2 j) (b j s)))
    · obtain ⟨s, hs⟩ : ∃ s, a s ≠ (y s).1 := by simpa [funext_iff] using h
      exact Finset.prod_eq_zero (mem_univ s) (by simp [controlled, e, hs])
  change (∑ a : S → A, ∑ b : (∀ j, S → B j),
      (T a * ∏ j, U j (b j)) * ∏ s, controlled M s (y s) (e.symm (a, b) s)) = _
  simp only [localProd, mul_ite, mul_zero]
  rw [Fintype.sum_eq_single (fun s => (y s).1)]
  · simp only [if_true]
    simp_rw [mul_assoc, ← Finset.prod_mul_distrib]
    rw [← Finset.mul_sum, Fintype.prod_sum]
  · intro a ha
    simp [ha]

private structure Device (S A : Type) where
  In : Type
  Out : Type
  inFinite : Fintype In
  outFinite : Fintype Out
  input : Tensor S In
  output : Tensor S Out
  input_ne : input ≠ 0
  output_ne : output ≠ 0
  matrix : S → A → Out → In → ℂ

private instance (D : Device S A) : Fintype D.In := D.inFinite
private instance (D : Device S A) : Fintype D.Out := D.outFinite

private def Device.cost [Fintype S] [DecidableEq S] (D : Device S A) (p : Price S) : ℝ :=
  p.value D.input - p.value D.output

private def Device.apply [Fintype S] [DecidableEq S] (D : Device S A) (control : S → A) : Tensor S D.Out :=
  restrict D.input (fun s => D.matrix s (control s))

private structure Rule (G : Type) where
  left : G
  right : G
  target : G
  deriving DecidableEq, Fintype

private def Rule.holds (q : Rule G) (a : G → A) : Prop :=
  a q.left = a q.right → a q.left = a q.target

private def Device.tests [Fintype S] [DecidableEq S] (D : Device S A) (g : S → G) (q : Rule G) : Prop :=
  (∀ a, D.apply (fun _ => a) = D.output) ∧
  ∀ a : G → A, ¬ q.holds a → D.apply (a ∘ g) = 0

private theorem price_comparison
    [Fintype S] [DecidableEq S] [Nonempty S] {r k m : ℕ}
    (p : Price S) (g : S → Fin r) (hg : Function.Surjective g)
    (rules : Finset (Rule (Fin r)))
    (forces : ∀ a : Fin r → Fin m, (∀ q ∈ rules, q.holds a) →
      OAI.Combinatorics.Sunflower.Admissible a)
    (W : Finset (Fin k → Fin m)) (hne : W.Nonempty)
    (hfree : OAI.Combinatorics.Sunflower.WordFree r W)
    (cost : rules → ℝ) (D : rules → Device S (Fin m))
    (hcost : ∀ q, (D q).cost p ≤ cost q)
    (hD : ∀ q, (D q).tests g q) :
    (1 - ∑ i, p.width (fiber g i)) * Real.log W.card ≤ k * ∑ q, cost q := by
  let : Nonempty W := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let J := Fin k × rules
  let M (j : J) (s : S) (a : W) := (D j.2).matrix s (a.val j.1)
  let I (j : J) := (D j.2).input
  let O (j : J) := (D j.2).output
  let C := paired (diagonal S W) (product O)
  have hC : C ≠ 0 :=
    paired_ne_zero _ _ (grouped_ne_zero _) (product_ne_zero _ fun j => (D j.2).output_ne)
  have hRestrict : restrict (paired (grouped g W) (product I)) (controlled M) = C := by
    funext y
    refine (restrict_controlled (J := J) (grouped g W) I M y).trans ?_
    let word (s : S) := (y s).1
    change grouped g W word * _ = C y
    by_cases hdiag : ∀ s t, word s = word t
    · let s₀ := Classical.choice (inferInstance : Nonempty S)
      have hw : word = fun _ => word s₀ := funext fun s => hdiag s s₀
      have hEval (j : J) :
          restrict (I j) (fun s => M j s (word s)) (fun s => (y s).2 j) =
            O j (fun s => (y s).2 j) := by
        rw [hw]
        exact congrFun ((hD j.2).1 ((word s₀).val j.1)) _
      have hGrouped : grouped g W word = 1 :=
        if_pos (fun s t _ => hdiag s t)
      have hDiagonal : diagonal S W word = 1 :=
        if_pos (fun s t _ => hdiag s t)
      change _ = diagonal S W word * ∏ j, O j (fun s => (y s).2 j)
      rw [hGrouped, hDiagonal]
      exact congrArg (fun z : ℂ => 1 * z) (Finset.prod_congr rfl (fun j _ => hEval j))
    · have hz : diagonal S W word = 0 :=
        if_neg (fun h => hdiag (fun s t => h s t rfl))
      change _ = diagonal S W word * _
      rw [hz, zero_mul]
      by_cases hgroup : ∀ s t, g s = g t → word s = word t
      · let rep := Function.surjInv hg
        have hrep (i) : g (rep i) = i := Function.rightInverse_surjInv hg i
        let words (i : Fin r) := word (rep i)
        have hw (s) : word s = words (g s) := hgroup s (rep (g s)) (hrep (g s)).symm
        have hbad : ∃ j : J, ¬ (j.2 : Rule (Fin r)).holds (fun i => (words i).val j.1) := by
          by_contra! hall
          apply hdiag
          have hconst := hfree (fun i => (words i).val) (fun i => (words i).property)
            (fun c => forces _ fun q hq => hall (c, ⟨q, hq⟩))
          intro s t
          rw [hw s, hw t]
          exact Subtype.ext (hconst (g s) (g t))
        obtain ⟨j, hj⟩ := hbad
        have hZero :
            restrict (I j) (fun s => M j s (word s)) (fun s => (y s).2 j) = 0 := by
          simp_rw [hw]
          exact congrFun ((hD j.2).2 _ hj) _
        rw [Finset.prod_eq_zero (mem_univ j) hZero, mul_zero]
      · have hz' : grouped g W word = 0 := if_neg hgroup
        rw [hz', zero_mul]
  have hInput : product I ≠ 0 := product_ne_zero _ fun j => (D j.2).input_ne
  have hOutput : product O ≠ 0 := product_ne_zero _ fun j => (D j.2).output_ne
  have h := p.restriction (paired (grouped g W) (product I)) (controlled M)
    (hRestrict ▸ hC)
  rw [hRestrict, show C = paired (diagonal S W) (product O) from rfl,
    p.pair (diagonal S W) (product O) (grouped_ne_zero _) hOutput, p.full, p.prod (J := J) O (fun j => (D j.2).output_ne),
    p.pair (grouped g W) (product I) (grouped_ne_zero _) hInput, p.groups g hg,
    p.prod (J := J) I (fun j => (D j.2).input_ne), Fintype.card_coe] at h
  have hsum : (∑ j : J, (D j.2).cost p) ≤ k * ∑ q, cost q := calc
    _ ≤ ∑ j : J, cost j.2 := Finset.sum_le_sum fun j _ => hcost j.2
    _ = _ := by
      change (∑ j : Fin k × rules, cost j.2) = _
      rw [Fintype.sum_prod_type]
      simp
  unfold Device.cost at hsum
  dsimp only [I, O] at h
  rw [Finset.sum_sub_distrib] at hsum
  linarith only [h, hsum]

private theorem exp_bound {ρ L : ℝ} (hρ : 0 < ρ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ k n : ℕ, ρ * Real.log n ≤ k * L → n ≤ D ^ k := by
  obtain ⟨D, hD⟩ := exists_nat_gt (Real.exp (L / ρ) + 1)
  have hD₁ : 1 ≤ D := by
    have hd : (0 : ℝ) < D := by linarith [Real.exp_pos (L / ρ)]
    exact_mod_cast Nat.succ_le_of_lt (show 0 < D by exact_mod_cast hd)
  refine ⟨D, hD₁, fun k n h => ?_⟩
  by_cases hn : n = 0
  · simp [hn]
  have hlog : Real.log n ≤ k * (L / ρ) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hρ).2 (by simpa [mul_comm] using h)
  have hnexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hn), Real.exp_nat_mul] at hnexp
  have hle : Real.exp (L / ρ) ≤ (D : ℝ) := by linarith
  exact_mod_cast hnexp.trans (pow_le_pow_left₀ (Real.exp_pos _).le hle k)

/-- A local equality test on two disjoint sets of sites. Each set of sites is
promised one common control, and each local operation only reads its own control. -/
private def Device.equalityOn [Fintype S] [DecidableEq S] (D : Device S A) (P T : Finset S) : Prop :=
  ∀ (c : S → A) x y, (∀ s ∈ P, c s = x) → (∀ s ∈ T, c s = y) →
    D.apply c = (if x = y then D.output else 0)

private def boundedEquality [Fintype S] [DecidableEq S] (p : Price S) (P T : Finset S) : Prop :=
  ∃ B : ℝ, ∀ m : ℕ, ∃ D : Device S (Fin m), D.cost p ≤ B ∧ D.equalityOn P T

/- The sign-average test below is adapted from OpenAI math's Copy.lean.
   The input diagonal shares one independent sign per possible control.
   It yields the equality indicator and returns the other signs to the sources. -/

private def masked [DecidableEq S] (P : Finset S) (a : A) (s : S) : Option A :=
  if s ∈ P then some a else none

private theorem masked_injective [DecidableEq S] {P : Finset S} (hP : P.Nonempty) :
    Function.Injective (masked P (A := A)) := by
  intro a b h
  obtain ⟨s, hs⟩ := hP
  simpa [masked, hs] using congrFun h s

private theorem mask_ne_zero [DecidableEq S] (P : Finset S) [Nonempty A] :
    mask P A ≠ 0 := by
  let a := Classical.choice (inferInstance : Nonempty A)
  intro h
  have h1 : mask P A (masked P a) = 1 :=
    if_pos ⟨a, fun _ => rfl⟩
  have hz := congrFun h (masked P a)
  rw [h1] at hz
  exact one_ne_zero hz

private theorem restrict_mask [Fintype S] [DecidableEq S] [Fintype A]
    (P : Finset S) (hP : P.Nonempty) (M : S → B → Option A → ℂ) (y : S → B) :
    restrict (mask P A) M y = ∑ a : A, ∏ s, M s (y s) (masked P a s) := by
  let f (x : S → Option A) := mask P A x * ∏ s, M s (y s) (x s)
  change (∑ x, f x) = _
  calc
    (∑ x, f x) = ∑ x ∈ univ.image (masked P), f x := by
      symm
      apply Finset.sum_subset (subset_univ _)
      intro x _ hx
      have h : ¬ ∃ a : A, ∀ s, x s = if s ∈ P then some a else none := by
        rintro ⟨a, ha⟩
        exact hx (Finset.mem_image.mpr ⟨a, mem_univ a, (funext ha).symm⟩)
      exact (congrArg (fun u : ℂ => u * ∏ s, M s (y s) (x s)) (if_neg h)).trans (zero_mul _)
    _ = ∑ a : A, f (masked P a) :=
      Finset.sum_image (fun a _ b _ hab => masked_injective hP hab)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      have h : mask P A (masked P a) = 1 := if_pos ⟨a, fun _ => rfl⟩
      simp only [f, h, one_mul]

private def sign (b : Bool) : ℂ := if b then -1 else 1

private theorem sign_average {n : ℕ} (x y : Fin (n + 1)) (v : Fin n → Bool) :
    (∑ b : Bool, sign b / 2 * sign (x.insertNth (α := fun _ => Bool) b v y)) =
      if x = y then 1 else 0 := by
  cases y using x.succAboveCases with
  | x => norm_num [Fintype.sum_bool, sign]
  | p j =>
    simp only [Fin.insertNth_apply_succAbove, Fin.ne_succAbove, ite_false, Fintype.sum_bool]
    cases v j <;> norm_num [sign]

private def flatMatrix [DecidableEq S] {n : ℕ} (P : Finset S) (a z : S) (s : S)
    (i : Fin (n + 1)) (o : Option (Fin n → Bool)) (t : Option (Fin (n + 1) → Bool)) : ℂ :=
  let bits := t.getD (fun _ => false)
  (if o = masked P (i.removeNth (α := fun _ => Bool) bits) s then 1 else 0) *
    (if s = a then sign (bits i) / 2 else 1) *
    (if s = z then sign (bits i) else 1)

private theorem flatMatrix_product [Fintype S] [DecidableEq S] {n : ℕ}
    {P : Finset S} {a z : S} (ha : a ∈ P) (hz : z ∉ P)
    (c : S → Fin (n + 1)) (x y : Fin (n + 1))
    (hx : ∀ s ∈ P, c s = x) (hy : c z = y)
    (o : S → Option (Fin n → Bool)) (bits : Fin (n + 1) → Bool) :
    (∏ s, flatMatrix P a z s (c s) (o s) (masked (insert z P) bits s)) =
      (if o = masked P (x.removeNth (α := fun _ => Bool) bits) then 1 else 0) *
        (sign (bits x) / 2 * sign (bits y)) := by
  have hlocal (s : S) :
      flatMatrix P a z s (c s) (o s) (masked (insert z P) bits s) =
        (if o s = masked P (x.removeNth (α := fun _ => Bool) bits) s then 1 else 0) *
          (if s = a then sign (bits x) / 2 else 1) *
          (if s = z then sign (bits y) else 1) := by
    by_cases h : s ∈ P
    · have hne : s ≠ z := fun eq => hz (eq ▸ h)
      simp [flatMatrix, masked, h, hne, hx s h]
    · have hne : s ≠ a := fun eq => h (eq ▸ ha)
      by_cases hs : s = z
      · subst s
        simp [flatMatrix, masked, hz, hne, hy]
      · simp [flatMatrix, masked, h, hne, hs]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [Fintype.prod_boole]
  simp only [← funext_iff, Finset.prod_ite_eq', mem_univ, if_true, mul_assoc]

private theorem flat_apply [Fintype S] [DecidableEq S] {n : ℕ}
    {P : Finset S} {a z : S} (ha : a ∈ P) (hz : z ∉ P)
    (c : S → Fin (n + 1)) (x y : Fin (n + 1)) (hx : ∀ s ∈ P, c s = x)
    (hy : c z = y) :
    restrict (mask (insert z P) (Fin (n + 1) → Bool)) (fun s => flatMatrix P a z s (c s)) =
      if x = y then mask P (Fin n → Bool) else 0 := by
  funext o
  rw [restrict_mask _ (Finset.insert_nonempty ..)]
  let f (v : Fin (n + 1) → Bool) : ℂ :=
    (if o = masked P (x.removeNth (α := fun _ => Bool) v) then 1 else 0) *
      (sign (v x) / 2 * sign (v y))
  have hprod : (∑ v : Fin (n + 1) → Bool,
      ∏ s, flatMatrix P a z s (c s) (o s) (masked (insert z P) v s)) =
      ∑ v, f v := Finset.sum_congr rfl (fun v _ => flatMatrix_product ha hz c x y hx hy o v)
  rw [hprod]
  let e : (Bool × (Fin n → Bool)) ≃ (Fin (n + 1) → Bool) := x.insertNthEquiv (fun _ => Bool)
  have hsum : (∑ v : Fin (n + 1) → Bool, f v) =
      ∑ v : Fin n → Bool, ∑ b : Bool, f (x.insertNth b v) := by
    rw [← Fintype.sum_equiv e (fun bv => f (e bv)) f (fun _ => rfl), Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hsum]
  unfold f
  simp only [Fin.removeNth_insertNth, Fin.insertNth_apply_same, ← Finset.mul_sum, sign_average]
  split_ifs with he
  · simp only [mul_one]
    by_cases h : ∃ v : Fin n → Bool, o = masked P v
    · obtain ⟨v, hv⟩ := h
      have hh : ∀ j : Fin n → Bool, o = masked P j ↔ j = v := by
        intro j
        rw [hv]
        exact ⟨fun eq => (masked_injective ⟨a, ha⟩ eq).symm, fun eq => by rw [eq]⟩
      simp only [hh, Finset.sum_ite_eq', mem_univ, if_true]
      exact (show mask P (Fin n → Bool) o = 1 from if_pos ⟨v, congrFun hv⟩).symm
    · have hh : ∀ v : Fin n → Bool, ¬ o = masked P v := fun v hv => h ⟨v, hv⟩
      simp only [hh, if_false, Finset.sum_const_zero]
      exact (show mask P (Fin n → Bool) o = 0 from if_neg
        (fun ⟨v, hv⟩ => h ⟨v, funext hv⟩)).symm
  · simp

private theorem bounded_flat [Fintype S] [DecidableEq S] (p : Price S)
    (P : Finset S) (z : S) (hP : P.Nonempty) (hz : z ∉ P)
    (hw : p.width (insert z P) = p.width P) : boundedEquality p P {z} := by
  obtain ⟨a, ha⟩ := hP
  refine ⟨max 0 (p.width P * Real.log 2), fun m => ?_⟩
  cases m with
  | zero =>
    let D : Device S (Fin 0) :=
      ⟨Option Unit, Option Unit, inferInstance, inferInstance, mask P Unit, mask P Unit,
        mask_ne_zero P, mask_ne_zero P, fun _ x => x.elim0⟩
    refine ⟨D, ?_, fun _ x => x.elim0⟩
    exact (sub_self (p.value (mask P Unit))).le.trans (le_max_left _ _)
  | succ n =>
    let D : Device S (Fin (n + 1)) :=
      ⟨Option (Fin (n + 1) → Bool), Option (Fin n → Bool), inferInstance, inferInstance,
        mask (insert z P) _, mask P _, mask_ne_zero _, mask_ne_zero _,
        flatMatrix P a z⟩
    refine ⟨D, ?_, ?_⟩
    · have hcost : D.cost p = p.width P * Real.log 2 := by
        change p.value (mask (insert z P) (Fin (n + 1) → Bool)) -
          p.value (mask P (Fin n → Bool)) = _
        rw [p.masks _ (Finset.insert_nonempty ..), p.masks _ ⟨a, ha⟩, hw]
        simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
          Nat.cast_ofNat, Real.log_pow, Nat.cast_succ]
        ring
      exact hcost.le.trans (le_max_right _ _)
    · intro c x y hx hy
      have he := flat_apply ha hz c x y hx (hy z (Finset.mem_singleton_self z))
      by_cases h : x = y
      · exact (he.trans (if_pos h)).trans (if_pos h).symm
      · exact (he.trans (if_neg h)).trans (if_neg h).symm

private theorem uniform_tests {s r : ℕ} (p : Price (Fin s)) (g : Fin s → Fin r)
    (q : Rule (Fin r)) (P T : Finset (Fin s))
    (hP : ∀ z ∈ P, g z = q.left ∨ g z = q.right)
    (hT : ∀ z ∈ T, g z = q.target)
    (he : boundedEquality p P T) :
    ∃ B : ℝ, ∀ m, ∃ D : Device (Fin s) (Fin m), D.cost p ≤ B ∧ D.tests g q := by
  obtain ⟨B, hB⟩ := he
  refine ⟨B, fun m => ?_⟩
  obtain ⟨D, hD, heq⟩ := hB m
  refine ⟨D, hD, ?_, ?_⟩
  · intro a
    exact (heq (fun _ => a) a a (fun _ _ => rfl) (fun _ _ => rfl)).trans (if_pos rfl)
  · intro a ha
    have hv : a q.left = a q.right ∧ a q.left ≠ a q.target := Classical.not_imp.mp ha
    have hp z (hz : z ∈ P) : (a ∘ g) z = a q.left := by
      rcases hP z hz with h | h <;> simp [h, ← hv.1]
    have ht z (hz : z ∈ T) : (a ∘ g) z = a q.target := by simp [hT z hz]
    simpa only [if_neg hv.2] using heq (a ∘ g) _ _ hp ht

/-- The two anchors together constrain every other group. Each anchor with a
third group constrains the other anchor, and each pair of other groups
constrains the first anchor. -/
private inductive AnchorRule {r : ℕ} (A B : Fin r) : Rule (Fin r) → Prop
  | together (i : Fin r) (hiA : i ≠ A) (hiB : i ≠ B) : AnchorRule A B ⟨A, B, i⟩
  | left (i : Fin r) (hiA : i ≠ A) (hiB : i ≠ B) : AnchorRule A B ⟨A, i, B⟩
  | right (i : Fin r) (hiA : i ≠ A) (hiB : i ≠ B) : AnchorRule A B ⟨B, i, A⟩
  | pair (i j : Fin r) (hiA : i ≠ A) (hiB : i ≠ B) (hjA : j ≠ A) (hjB : j ≠ B)
      (hij : i < j) : AnchorRule A B ⟨i, j, A⟩

private def anchorRules {r : ℕ} (A B : Fin r) : Finset (Rule (Fin r)) :=
  univ.filter (AnchorRule A B)

private theorem anchorRules_forces {r : ℕ} {A B : Fin r} (a : Fin r → X)
    (rules : ∀ q ∈ anchorRules A B, q.holds a) : Admissible a := by
  have test {q : Rule (Fin r)} (hq : AnchorRule A B q) : q.holds a :=
    rules q (Finset.mem_filter.mpr ⟨mem_univ _, hq⟩)
  by_cases hAB : a A = a B
  · left
    have h (i : Fin r) : a A = a i := by
      by_cases hiA : i = A
      · rw [hiA]
      by_cases hiB : i = B
      · exact hiB ▸ hAB
      exact test (.together i hiA hiB) hAB
    exact fun i j => (h i).symm.trans (h j)
  · right
    have hLeft (i : Fin r) (hi : i ≠ A) : a A ≠ a i := by
      intro eq
      by_cases hiB : i = B
      · exact hAB (hiB ▸ eq)
      exact hAB (test (.left i hi hiB) eq)
    have hRight (i : Fin r) (hi : i ≠ B) : a B ≠ a i := by
      intro eq
      by_cases hiA : i = A
      · exact hAB (hiA ▸ eq.symm)
      exact hAB (test (.right i hiA hi) eq).symm
    intro i j he
    by_contra hij
    by_cases hiA : i = A
    · subst i
      exact hLeft j (fun h => hij h.symm) he
    by_cases hjA : j = A
    · subst j
      exact hLeft i hij he.symm
    by_cases hiB : i = B
    · subst i
      exact hRight j (fun h => hij h.symm) he
    by_cases hjB : j = B
    · subst j
      exact hRight i hij he.symm
    rcases lt_or_gt_of_ne hij with h | h
    · exact hLeft i hiA (test (.pair i j hiA hiB hjA hjB h) he).symm
    · exact hLeft j hjA (test (.pair j i hjA hjB hiA hiB h) he.symm).symm

/-- The finite placement is fixed before the alphabet and word length.
The two alternatives are the positive-gap and width-preserving-copy configurations. -/
def H1 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ s : ℕ, 0 < s ∧
    ∃ (p : Price (Fin s)) (g : Fin s → Fin r) (A B : Fin r),
      Function.Surjective g ∧ A ≠ B ∧ 0 < 1 - ∑ i, p.width (fiber g i) ∧
        ∀ q ∈ anchorRules A B, ∃ P T : Finset (Fin s),
          P.Nonempty ∧ T.Nonempty ∧ Disjoint P T ∧
          (∀ z ∈ P, g z = q.left ∨ g z = q.right) ∧
          (∀ z ∈ T, g z = q.target) ∧
          (0 < p.width P + p.width T - p.width (P ∪ T) ∨
            ∃ z, T = {z} ∧ p.width (insert z P) = p.width P)

/-- Positive diagonal gaps pay for equality checking over arbitrarily large alphabets. -/
def H2 : Prop :=
  ∀ (s : ℕ), 0 < s → ∀ (p : Price (Fin s)) (P T : Finset (Fin s)),
    P.Nonempty → T.Nonempty → Disjoint P T →
    0 < p.width P + p.width T - p.width (P ∪ T) → boundedEquality p P T

theorem main : H1 → H2 → OMA.R_Erdos535_erdos_535_R2.H1 := by
  intro layout gap r hr
  obtain ⟨s, hs, p, g, A, B, hg, _, hpos, hlayout⟩ := layout r hr
  let rules := anchorRules A B
  let : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  have htests (q : rules) :
      ∃ B : ℝ, ∀ m, ∃ D : Device (Fin s) (Fin m), D.cost p ≤ B ∧ D.tests g q := by
    obtain ⟨P, T, hP, hT, hPT, hL, hR, hgeom⟩ := hlayout q q.property
    apply uniform_tests p g q P T hL hR
    rcases hgeom with hgap | ⟨z, rfl, heq⟩
    · exact gap s hs p P T hP hT hPT hgap
    · exact bounded_flat p P z hP
        (fun hz => (Finset.disjoint_left.mp hPT) hz (Finset.mem_singleton_self z)) heq
  choose cost hcost using htests
  obtain ⟨D, hD, hbound⟩ := exp_bound (L := ∑ q, cost q) hpos
  have wordBound (k m : ℕ) (W : Finset (Fin k → Fin m)) (hfree : WordFree r W) :
      W.card ≤ D ^ k := by
    by_cases hne : W.Nonempty
    · choose devices hCosts hTests using fun q => hcost q m
      exact hbound k W.card
        (price_comparison p g hg rules (fun a => anchorRules_forces a) W hne hfree
          cost devices hCosts hTests)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  refine ⟨3 * D, by omega, fun k F hF hLarge => ?_⟩
  by_cases hk : k = 0
  · subst k
    have hSmall : F.card ≤ 1 := Finset.card_le_one.mpr fun A hA B hB =>
      (Finset.card_eq_zero.mp (hF A hA)).trans (Finset.card_eq_zero.mp (hF B hB)).symm
    simp only [pow_zero] at hLarge
    exact (hLarge.not_ge hSmall).elim
  · by_contra hFree
    obtain ⟨m, W, hSize, hWordFree⟩ :=
      rainbow_transfer r k (Nat.pos_of_ne_zero hk) F hF hFree
    apply hLarge.not_ge
    rw [mul_pow]
    exact hSize.trans (Nat.mul_le_mul_left _ (wordBound k m W hWordFree))

end OMA.R_Erdos535_erdos_535_R2_H1_R1
/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
