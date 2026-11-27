import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Perm

/-! Count colorings that are bijective on each member of the uniform family. -/

open Finset

namespace OMA.SunflowerTransfer

lemma rainbow (n : ℕ) (hn : 0 < n) (F : Finset (Finset ℕ)) (hF : ∀ A ∈ F, A.card = n) :
    ∃ (c : ℕ → Fin n) (G : Finset (Finset ℕ)), G ⊆ F ∧
      (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧
      F.card * n.factorial ≤ G.card * n ^ n := by
  classical
  let base : Fin n := ⟨0, hn⟩
  by_cases hne : F.Nonempty
  · let S := F.biUnion id
    let C := (S → Fin n)
    let extend (c : C) (x : ℕ) := if hx : x ∈ S then c ⟨x,hx⟩ else base
    let good (A : Finset ℕ) (c : C) := Function.Bijective (fun x : A => extend c x)
    let cols := (univ : Finset C)
    have hsub {A : Finset ℕ} (hA : A ∈ F) : A ⊆ S := fun x hx =>
      mem_biUnion.mpr ⟨A,hA,hx⟩
    have count (A : Finset ℕ) (hA : A ∈ F) :
        n.factorial * n^(S.card-n) ≤ (cols.bipartiteAbove good A).card := by
      let D := S \ A
      let assemble (u : (A ≃ Fin n) × (D → Fin n)) (x : S) :=
        if hx : x.val ∈ A then u.1 ⟨x,hx⟩ else u.2 ⟨x,mem_sdiff.mpr ⟨x.property,hx⟩⟩
      have onA (u : (A ≃ Fin n) × (D → Fin n)) (x : A) :
          extend (assemble u) x = u.1 x := by simp [extend,assemble,hsub hA x.property,x.property]
      let embed (u : (A ≃ Fin n) × (D → Fin n)) : ↥(cols.bipartiteAbove good A) :=
        ⟨assemble u, mem_filter.mpr ⟨mem_univ _, by
          change Function.Bijective (fun x : A => extend (assemble u) x)
          simpa only [onA] using u.1.bijective⟩⟩
      have hinj : Function.Injective embed := by
        intro u v huv
        have he : assemble u = assemble v := congrArg Subtype.val huv
        apply Prod.ext
        · apply Equiv.ext
          intro x
          exact (onA u x).symm.trans ((congrArg (fun c => extend c x) he).trans (onA v x))
        · funext x
          have hx := mem_sdiff.mp x.property
          simpa [assemble,hx.2] using congrFun he ⟨x,hx.1⟩
      have cardEq : A ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hF A hA)
      have hcard := Fintype.card_le_of_injective _ hinj
      rw [Fintype.card_coe] at hcard
      simpa only [Fintype.card_coe,Fintype.card_fin,Fintype.card_prod,Fintype.card_equiv cardEq,Fintype.card_fun,D,
        card_sdiff_of_subset (hsub hA),hF A hA] using hcard
    obtain ⟨c, hc, hmax⟩ := cols.exists_max_image (fun c => (F.bipartiteBelow good c).card)
      ⟨fun _ => base,mem_univ _⟩
    refine ⟨extend c, F.bipartiteBelow good c, filter_subset _ _, ?_, ?_⟩
    · intro A ha
      exact (mem_filter.mp ha).2
    · obtain ⟨A,hA⟩ := hne
      have hle : n ≤ S.card := hF A hA ▸ card_le_card (hsub hA)
      have h := card_nsmul_le_card_nsmul (r := good) count hmax
      have hp : n^S.card = n^(S.card-n) * n^n := by rw [← pow_add, Nat.sub_add_cancel hle]
      simp only [smul_eq_mul, cols, card_univ, C, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_coe, hp] at h
      exact Nat.le_of_mul_le_mul_right (by simpa only [mul_assoc,mul_comm,mul_left_comm] using h)
        (pow_pos hn (S.card-n))
  · refine ⟨fun _ => base, ∅, empty_subset _, by simp, ?_⟩
    simp [not_nonempty_iff_eq_empty.mp hne]

-- The factorial estimate and word encoding are from @kenanwienberg's reduction of Erdős 20.
lemma pow_self_le_three_pow_mul_factorial (n : ℕ) :
    n ^ n ≤ 3 ^ n * n.factorial := by
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hExp : Real.exp n ≤ (3 : ℝ) ^ n := by
    calc
      Real.exp n = (Real.exp 1) ^ n := by simp [← Real.exp_nat_mul]
      _ ≤ (3 : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have h := (div_le_iff₀ hn).mp
    ((Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n).trans hExp)
  exact_mod_cast h

lemma word_family_of_rainbow {α : Type} [DecidableEq α] {n r : ℕ}
    {G F : Finset (Finset α)} (hGF : G ⊆ F) (c : α → Fin n)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x))
    (hfree : ¬ ∃ S ⊆ F, S.card = r ∧ ∃ K : Finset α,
      ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K) :
    ∃ (m : ℕ) (W : Finset (Fin n → Fin m)),
      W.card = G.card ∧
      ∀ w : Fin r → Fin n → Fin m,
        (∀ i, w i ∈ W) →
        (∀ j : Fin n, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b := by
  classical
  let U : Finset α := G.biUnion id
  let e (A : G) : (A : Finset α) ≃ Fin n := Equiv.ofBijective _ (hc A A.property)
  let pt (A : G) (j : Fin n) : U :=
    ⟨(e A).symm j, Finset.mem_biUnion.mpr ⟨A, A.property, ((e A).symm j).property⟩⟩
  let encode (A : G) (j : Fin n) : Fin U.card := U.equivFin (pt A j)
  let decode (u : Fin U.card) : α := U.equivFin.symm u
  have hdec_inj : Function.Injective decode :=
    Subtype.val_injective.comp U.equivFin.symm.injective
  have hmem : ∀ (A : G) (x : α), x ∈ (A : Finset α) ↔ decode (encode A (c x)) = x := by
    intro A x
    have hdecode (j : Fin n) : decode (encode A j) = ((e A).symm j).val := by
      simp [decode, encode, pt]
    rw [hdecode]
    constructor
    · intro hx
      have he : (e A) ⟨x, hx⟩ = c x := rfl
      rw [← he, Equiv.symm_apply_apply]
    · intro hx
      exact hx ▸ ((e A).symm (c x)).property
  have henc_inj : Function.Injective encode := by
    intro A B hab
    apply Subtype.ext
    ext x
    rw [hmem, hmem, hab]
  let W : Finset (Fin n → Fin U.card) := Finset.univ.image encode
  refine ⟨U.card, W, ?_, ?_⟩
  · simp [W, Finset.card_image_of_injective _ henc_inj]
  · intro w hw hadm
    by_contra hnc
    push Not at hnc
    obtain ⟨a₀, b₀, hab₀⟩ := hnc
    have hwinj : Function.Injective w := by
      intro i j hij
      by_contra hne
      apply hab₀
      funext j₀
      rcases hadm j₀ with hconst | hinj
      · exact hconst a₀ b₀
      · exact (hne (hinj (congrFun hij j₀))).elim
    have hlift : ∀ i : Fin r, ∃ A : G, encode A = w i := by
      intro i
      obtain ⟨A, _, hA⟩ := Finset.mem_image.mp (hw i)
      exact ⟨A, hA⟩
    choose A hA using hlift
    have hAinj : Function.Injective (fun i : Fin r => (A i : Finset α)) := by
      intro i j hij
      apply hwinj
      rw [← hA i, ← hA j, Subtype.ext hij]
    have hAmem (i : Fin r) (x : α) :
        x ∈ (A i : Finset α) ↔ decode (w i (c x)) = x := by
      rw [← hA i, hmem]
    let K : Finset α := U.filter fun x => ∀ i : Fin r, x ∈ (A i : Finset α)
    let emb : Fin r ↪ Finset α := ⟨fun i => (A i : Finset α), hAinj⟩
    apply hfree
    refine ⟨Finset.univ.map emb, ?_, by simp, K, ?_⟩
    · intro X hX
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hX
      exact hGF (A i).property
    · intro X hX Y hY hXY
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hX
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hY
      have hij : i ≠ j := fun h => hXY (congrArg emb h)
      ext x
      constructor
      · intro hx
        obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨A i, (A i).property, hi⟩, ?_⟩
        have heq : w i (c x) = w j (c x) :=
          hdec_inj (((hAmem i x).mp hi).trans ((hAmem j x).mp hj).symm)
        rcases hadm (c x) with hconst | hinj
        · intro t
          exact (hAmem t x).mpr ((congrArg decode (hconst t i)).trans ((hAmem i x).mp hi))
        · exact (hij (hinj heq)).elim
      · intro hx
        have hall := (Finset.mem_filter.mp hx).2
        exact Finset.mem_inter.mpr ⟨hall i, hall j⟩

end OMA.SunflowerTransfer

open OMA.SunflowerTransfer

theorem OMA.solution : OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1.H2 := by
  intro r k hk F hF hfree
  obtain ⟨c, G, hGF, hc, hsize⟩ := rainbow k hk F hF
  obtain ⟨m, W, hcard, hword⟩ := word_family_of_rainbow hGF c hc hfree
  refine ⟨m, W, ?_, hword⟩
  rw [hcard]
  apply Nat.le_of_mul_le_mul_right _ k.factorial_pos
  calc
    F.card * k.factorial ≤ G.card * k ^ k := hsize
    _ ≤ G.card * (3 ^ k * k.factorial) :=
      Nat.mul_le_mul_left _ (pow_self_le_three_pow_mul_factorial k)
    _ = 3 ^ k * G.card * k.factorial := by ring
